# -*- coding: utf-8 -*-
"""
AIGC 创作站 · 生视频插件（youzan666.vip AIGC 网关）

对接《API 接入文档 · AIGC 创作站》中的两种视频协议：
  GET  {base}/v1/models                    拉取当前可用模型列表（动态，勿写死模型 ID）
  POST {base}/v1/videos/generations        提交纯文生视频任务
  GET  {base}/v1/videos/{taskId}           轮询纯文生视频任务
  POST {base}/api/v1/services/aigc/video-generation/video-synthesis
                                             提交带参考素材的 DashScope 请求
  GET  {base}/api/v1/tasks/{taskId}         轮询带参考素材的任务

支持：
- 文生视频 / 图生视频（自动按参考图判断，也可手动指定）
- 参考图：http(s) URL 直接透传；本地图片转为接口支持的 Base64 数据 URL
- 参考图 / 音频 / 视频统一进入官方 input.media 数组，按槽位顺序绑定
- 动态模型列表（不写死模型 ID，UI 内可一键刷新）
- 429 / 502 / 503 / 504 指数退避重试
- 产物为 mp4，落盘前校验视频容器
"""

import base64
import hashlib
import json
import os
import re
import shutil
import sys
import tempfile
import threading
import time
import uuid
import mimetypes
import zipfile
from datetime import datetime
from pathlib import Path
from urllib.parse import urlparse

import requests

sys.path.append(os.path.dirname(os.path.dirname(__file__)))
from plugin_utils import load_plugin_config

_PLUGIN_FILE = __file__
_PLUGIN_ID = "video_plugin_youzan_aigc"
_PLUGIN_VERSION = "1.2.1"
_DEFAULT_UPDATE_MANIFEST_URL = (
    "https://cdn.jsdelivr.net/gh/609335334-rgb/"
    "youzan-aigc-plugin-updates@main/manifest.json"
)
_DEFAULT_UPDATE_MANIFEST_URLS = (
    _DEFAULT_UPDATE_MANIFEST_URL,
    "https://raw.githubusercontent.com/609335334-rgb/"
    "youzan-aigc-plugin-updates/main/manifest.json",
)

_DEFAULT_BASE_URL = "https://youzan666.vip"
_MODELS_PATH = "/v1/models"
_VIDEO_GENERATIONS_PATH = "/v1/videos/generations"
_VIDEO_STATUS_PATH = "/v1/videos/{task_id}"
_DASHSCOPE_VIDEO_GENERATIONS_PATH = (
    "/api/v1/services/aigc/video-generation/video-synthesis"
)
_DASHSCOPE_VIDEO_STATUS_PATH = "/api/v1/tasks/{task_id}"
_TASKS_PATH = "/api/tasks"
_USER_ME_PATH = "/api/user/me"

_DEFAULT_RESOLUTIONS = ["480p", "720p", "1080p"]
_DEFAULT_RATIOS = ["16:9", "9:16", "1:1", "4:3", "3:4", "adaptive"]
_DEFAULT_DURATION = "5"

# Wan3.0 官方时长支持范围：无视频输入时 [2, 30] 秒整数（实测 1 秒必 400 WAN3_PARAMETER_INVALID，2 秒可生成）
MIN_DURATION = 2
MAX_DURATION = 30

MODE_AUTO = "自动（按参考图判断）"
MODE_TEXT_TO_VIDEO = "文生视频"
MODE_IMAGE_TO_VIDEO = "图生视频"

# 参考图传参方式（文档只定义了单数 reference_image，但网关以实测契约为准，
# 模型本身支持多参考图时可通过数组/逗号分隔尝试传多张）
REF_MODE_SINGLE = "single"   # reference_image = "url1"（只传第 1 张）
REF_MODE_ARRAY = "array"     # reference_image = ["url1","url2"]（数组，需网关支持）
REF_MODE_COMMA = "comma"     # reference_image = "url1,url2"（逗号分隔，需网关支持）
REFERENCE_MODES = [REF_MODE_SINGLE, REF_MODE_ARRAY, REF_MODE_COMMA]

MAX_IMAGE_REFS = 10
MAX_AUDIO_REFS = 5  # 官方万相3.0：参考音频最多 5 段、单段 [1,15] 秒、总时长 ≤15 秒
MAX_AUDIO_TOTAL_SECONDS = 15
MAX_VIDEO_TOTAL_SECONDS = 15  # 官方万相3.0：参考视频最多 5 段、单段与总时长均 ≤15 秒
MIN_MEDIA_SECONDS = 1
MIN_POLL_INTERVAL = 10
MAX_POLL_INTERVAL = 60  # 触发网关 IP 限流（约 20 次/分钟）时把轮询间隔放大到此值
MAX_PROMPT_CHARS = 19000  # 网关上限（上游万相3.0 为 20000 字符，超限返回 WAN3_API_PROMPT_INVALID）

# 提交响应丢失后的找回策略：网关先受理任务、再回写任务历史，实测存在上百秒延迟，
# 因此按「5 秒探测一次、最长 5 分钟」的窗口持续找回，命中后继续轮询同一任务 ID。
RECOVERY_DEADLINE_SECONDS = 300
RECOVERY_INTERVAL_SECONDS = 5
RECOVERY_MAX_INTERVAL_SECONDS = 30  # 探测间隔逐步放大（5→10→20→30s），避免触发 IP 限流

# 网关 /api/tasks 列表把 prompt 截断到 500 字符（仅用于展示），
# 所以「按 prompt 找回任务」只能比对公共前缀，且前缀不能太短以免误配。
HISTORY_PROMPT_MIN_PREFIX = 60

# 参考素材不复用：每次生成都由网关重新导入本分镜素材，不向网关传 conversationId，
# 避免跨分镜复用素材会话导致串素材（文档 §7.6 的素材会话复用已停用）。

# ---- 素材导入排队（官方/网关：素材导入并发每账号 2 个、全局 4，超限 429 WAN3_API_IMPORT_BUSY）----
# 该状态代表任务未被网关受理、不扣积分：插件在本机做同样宽度的排队（同时只提交 2 个带素材的
# 分镜），拿到名额前一直等待；拿不到时再按网关 429 退避重试，避免多分镜同时提交直接报错。
IMPORT_CONCURRENCY = 2
# 排队 + 退避重试的总时长上限；超过后才按错误提示交给用户处理。
SUBMIT_QUEUE_DEADLINE_SECONDS = 600

# 视频容器魔数（用于下载后校验）
_WEBM_MAGIC = b"\x1a\x45\xdf\xa3"
_MP4_BOX = b"ftyp"

# 429 / 502 / 503 / 504 属于可退避重试的错误（504 = openresty 网关转发超时，重试通常可恢复）
_RETRYABLE_STATUS_CODES = {429, 502, 503, 504}

_default_params = {
    "api_key": "",
    "base_url": _DEFAULT_BASE_URL,
    "model": "",
    "generation_mode": MODE_AUTO,
    "resolution": "720p",
    "ratio": "16:9",
    "duration": _DEFAULT_DURATION,
    "reference_image_url": "",
    "reference_image_mode": REF_MODE_ARRAY,
    "enable_audio_reference": False,
    "auto_storyboard_audio": True,
    "audio_reference_url": "",
    "timeout": 900,
    "poll_interval": MIN_POLL_INTERVAL,
    "max_poll_attempts": 300,
    "update_manifest_url": _DEFAULT_UPDATE_MANIFEST_URL,
}


# ---------------------------------------------------------------- 基础工具

def _parse_version(version_text):
    parts = []
    for segment in str(version_text or "").strip().split("."):
        match = re.match(r"^(\d+)", segment)
        parts.append(int(match.group(1)) if match else 0)
    return tuple(parts or [0])


def _is_newer_version(remote_version, local_version):
    remote = list(_parse_version(remote_version))
    local = list(_parse_version(local_version))
    length = max(len(remote), len(local))
    remote.extend([0] * (length - len(remote)))
    local.extend([0] * (length - len(local)))
    return tuple(remote) > tuple(local)


def _compute_sha256(file_path):
    hasher = hashlib.sha256()
    with open(file_path, "rb") as file_obj:
        for chunk in iter(lambda: file_obj.read(8192), b""):
            hasher.update(chunk)
    return hasher.hexdigest().lower()


def _read_package_version(main_path):
    """读取更新包内 main.py 的 _PLUGIN_VERSION，安装前用于校验包与更新清单是否一致。"""
    try:
        text = Path(main_path).read_text(encoding="utf-8", errors="replace")
    except Exception:
        return ""
    match = re.search(r'_PLUGIN_VERSION\s*=\s*["\']([^"\']+)["\']', text)
    return match.group(1).strip() if match else ""


def _check_update_available():
    params = get_params()
    configured_url = str(
        params.get("update_manifest_url") or _DEFAULT_UPDATE_MANIFEST_URL
    ).strip()
    candidates = []
    for candidate in (configured_url, *_DEFAULT_UPDATE_MANIFEST_URLS):
        if candidate and candidate not in candidates:
            candidates.append(candidate)

    best_manifest_url = ""
    best_remote = None
    errors = []
    for manifest_url in candidates:
        try:
            response = requests.get(manifest_url, timeout=30)
            if response.status_code != 200:
                raise Exception(f"HTTP {response.status_code}")
            manifest = response.json()
            plugins = manifest.get("plugins") if isinstance(manifest, dict) else None
            if not isinstance(plugins, list):
                raise Exception("manifest.json 格式错误：缺少 plugins")
            remote = next(
                (
                    item
                    for item in plugins
                    if isinstance(item, dict) and item.get("plugin_id") == _PLUGIN_ID
                ),
                None,
            )
            if not remote:
                raise Exception(f"清单中未找到插件: {_PLUGIN_ID}")
            remote_version = str(remote.get("version") or "").strip()
            if not remote_version:
                raise Exception("更新项缺少 version")
        except Exception as exc:
            errors.append(f"{manifest_url}: {exc}")
            continue
        if best_remote is None or _is_newer_version(
            remote_version, best_remote.get("version")
        ):
            best_manifest_url = manifest_url
            best_remote = remote

    if best_remote is None:
        return {"ok": False, "error": "拉取更新清单失败: " + " | ".join(errors)}
    remote_version = str(best_remote.get("version") or "").strip()
    if not _is_newer_version(remote_version, _PLUGIN_VERSION):
        return {
            "ok": True,
            "has_update": False,
            "message": f"当前已是最新版（本地 {_PLUGIN_VERSION}，远端 {remote_version}）",
            "manifest_url": best_manifest_url,
        }
    return {
        "ok": True,
        "has_update": True,
        "local_version": _PLUGIN_VERSION,
        "remote_version": remote_version,
        "changelog": str(best_remote.get("changelog") or "无"),
        "download_url": str(best_remote.get("download_url") or "").strip(),
        "sha256": str(best_remote.get("sha256") or "").strip().lower(),
        "manifest_url": best_manifest_url,
    }


def _safe_extract_zip(archive, destination):
    root = Path(destination).resolve()
    for member in archive.infolist():
        target = (root / member.filename).resolve()
        if target != root and root not in target.parents:
            raise Exception("更新包包含非法路径")
    archive.extractall(root)


def _find_update_root(package_path, work_dir):
    package_path = Path(package_path)
    if package_path.suffix.lower() == ".py":
        return package_path.parent, package_path
    if package_path.suffix.lower() != ".zip":
        raise Exception("更新包仅支持 .py 或 .zip")
    extract_dir = Path(work_dir) / "extract"
    extract_dir.mkdir()
    with zipfile.ZipFile(package_path, "r") as archive:
        _safe_extract_zip(archive, extract_dir)
    candidates = [extract_dir, extract_dir / _PLUGIN_ID]
    candidates.extend(item.parent for item in extract_dir.rglob("main.py"))
    for candidate in candidates:
        if (candidate / "main.py").is_file():
            return candidate, candidate / "main.py"
    raise Exception("更新包中未找到 main.py")


def _execute_update(download_url, expected_sha256="", expected_version=""):
    if not download_url.startswith(("http://", "https://")):
        return {"ok": False, "error": "download_url 必须是 http(s) 地址"}
    work_dir = Path(tempfile.mkdtemp(prefix=f"{_PLUGIN_ID}_update_"))
    try:
        filename = Path(urlparse(download_url).path).name or "plugin_update.zip"
        package_path = work_dir / filename
        with requests.get(download_url, timeout=120, stream=True) as response:
            if response.status_code != 200:
                raise Exception(f"下载失败: HTTP {response.status_code}")
            with open(package_path, "wb") as file_obj:
                for chunk in response.iter_content(chunk_size=8192):
                    if chunk:
                        file_obj.write(chunk)
        if expected_sha256 and _compute_sha256(package_path) != expected_sha256:
            raise Exception("SHA-256 校验失败，已取消安装")

        source_dir, source_main = _find_update_root(package_path, work_dir)
        package_version = _read_package_version(source_main)
        if not package_version:
            raise Exception("更新包内 main.py 缺少版本号，已取消安装")
        if expected_version and package_version != expected_version:
            raise Exception(
                f"更新包版本与更新清单不一致（清单 {expected_version} / 包内 {package_version}），已取消安装"
            )
        if not _is_newer_version(package_version, _PLUGIN_VERSION):
            raise Exception(
                f"更新包版本异常（包内 {package_version} 不高于当前 {_PLUGIN_VERSION}），已取消安装"
            )

        target_dir = Path(_PLUGIN_FILE).parent
        backup = target_dir / f"main.py.bak.{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        shutil.copy2(_PLUGIN_FILE, backup)
        restore_dir = work_dir / "restore"
        restore_dir.mkdir()
        restore_items = []
        try:
            shutil.copy2(source_main, _PLUGIN_FILE)
            if package_path.suffix.lower() == ".zip":
                for item in source_dir.iterdir():
                    if item.name == "main.py":
                        continue
                    destination = target_dir / item.name
                    if destination.exists():
                        saved = restore_dir / item.name
                        if destination.is_dir():
                            shutil.copytree(destination, saved)
                        else:
                            shutil.copy2(destination, saved)
                        restore_items.append((destination, saved, destination.is_dir()))
                    if item.is_dir():
                        if destination.exists():
                            shutil.rmtree(destination)
                        shutil.copytree(item, destination)
                    else:
                        shutil.copy2(item, destination)
        except Exception:
            shutil.copy2(backup, _PLUGIN_FILE)
            for destination, saved, was_dir in reversed(restore_items):
                try:
                    if destination.exists():
                        if destination.is_dir():
                            shutil.rmtree(destination)
                        else:
                            destination.unlink()
                    if was_dir:
                        shutil.copytree(saved, destination)
                    else:
                        shutil.copy2(saved, destination)
                except Exception as restore_error:
                    print(f"[WARN] 回滚 {destination.name} 失败: {restore_error}")
            raise
        return {
            "ok": True,
            "message": (
                f"插件已更新到 {package_version}，已备份为 {backup.name}。请重启字字动画后生效。"
            ),
        }
    except Exception as exc:
        return {"ok": False, "error": str(exc)}
    finally:
        shutil.rmtree(work_dir, ignore_errors=True)

def _normalize_base_url(url):
    """统一为站点根地址（去掉末尾 /、/v1 与 /api/v1）。"""
    text = str(url or "").strip() or _DEFAULT_BASE_URL
    text = text.rstrip("/")
    for suffix in ("/api/v1", "/v1"):
        if text.endswith(suffix):
            text = text[: -len(suffix)].rstrip("/")
            break
    return text


def _api_url(base_url, path):
    return f"{_normalize_base_url(base_url)}{path}"


def _extract_api_error(response):
    """把网关错误响应转成可读文本：直接显示 API 返回的原文（JSON/HTML 原样，不截断不改写）。"""
    text = (response.text or "").strip()
    if not text:
        return f"HTTP {response.status_code}"
    return f"HTTP {response.status_code} - {text}"

# 网关错误码 → 可操作中文提示（对照《AIGC 中转 API 调用文档》§6）
_API_ERROR_HINTS = {
    "WAN3_API_AUTH_REQUIRED": "API Key 无效或已过期，请在插件设置里重新填写中转 Key",
    "WAN3_API_PERMISSION_DENIED": "当前 Key 没有该模型的权限，请联系网关管理员开通",
    "WAN3_API_PROMPT_INVALID": "提示词为空或超过 19000 字符，请精简分镜提示词后重试",
    "WAN3_API_MODEL_INVALID": "网关不支持该模型名，请在设置里点「刷新」重新选择模型",
    "WAN3_API_IMPORT_BUSY": "参考素材导入并发超限（每账号 2 个），稍等几秒再生成",
    "WAN3_API_MEDIA_URL_INVALID": "素材 URL 格式非法，请填写公网 http/https 直链",
    "WAN3_API_MEDIA_URL_FORBIDDEN": "素材 URL 指向内网/本机或非标准端口，网关只接受公网地址",
    "WAN3_API_MEDIA_DNS_FAILED": "素材域名解析失败，请检查链接是否可公网访问",
    "WAN3_API_MEDIA_DOWNLOAD_FAILED": "网关下载素材失败（404 或不可访问），请确认链接有效",
    "WAN3_API_MEDIA_FORMAT_INVALID": "素材真实格式与声明不符，请改用 JPG/PNG/WEBP/BMP",
    "WAN3_API_MEDIA_FLATTEN_FAILED": "图片透明通道处理失败，请自行转成不带透明通道的 JPG",
    "WAN3_API_REFERENCE_LIMIT": "参考素材数量超限（图 ≤10、视频 ≤5、音频 ≤5、合计 ≤20）",
    "WAN3_API_MEDIA_TIMEOUT": "网关处理参考素材超时（单次上限 90 秒）：可减少同时生成的分镜数量、改用公网直链素材或精简参考图",
    "WAN3_API_BODY_INVALID": "请求体结构错误（多为素材字段写法不对），请检查参考素材设置",
    "WAN3_API_MEDIA_REDIRECT": "素材 URL 重定向到不允许的地址，请改用可直连的公网直链",
    "WAN3_API_MEDIA_TOO_LARGE": "素材体积超限（图片 ≤20MB / 音频 ≤15MB），请先压缩后再提交",
    "WAN3_API_MEDIA_DATA_INVALID": "Base64 素材数据无效，请重试或改用公网直链素材",
    "WAN3_API_MEDIA_INVALID": "media 素材数组结构非法（最多 20 条且每条必须带 url）",
    "WAN3_API_REFERENCE_MODE": "参考图模式取值非法，请在插件设置里改回默认参考图模式",
    "WAN3_API_CONVERSATION_INVALID": "素材会话 ID 无效或不属于当前 Key，插件不再复用素材会话，请重新提交本次生成",
    "WAN3_API_MENTIONS_INVALID": "提示词里的素材引用无效（如写了「图片3」但只传了 2 张图），请核对提示词与参考素材序号",
    "WAN3_API_MEDIA_DISK_LOW": "网关磁盘空间不足（507），请稍后重试或联系网关管理员",
    "WAN3_API_REQUEST_FAILED": "网关转发上游失败（502），稍后重试即可",
    "WAN3_API_REFERENCE_INVALID": "使用了网关不认的素材字段（url/link/filePath），请用插件的参考素材设置传入",
    "EXTERNAL_MEDIA_URL_INSECURE": "图片 URL 必须是 HTTPS，请改用 https 直链",
    "EXTERNAL_MEDIA_URL_BLOCKED": "图片 URL 指向本机/内网/保留地址，请换公网地址",
    "EXTERNAL_MEDIA_URL_TOO_LONG": "图片 URL 超过 2048 字符，请改用短链",
    "WAN3_CLIENT_MEDIA_FORBIDDEN": "使用了网关已停用的素材字段，请用插件的参考素材设置传入",
    "WAN3_ASSET_INVALID": "素材未通过网关服务端校验，请更换素材后重试",
    "TOKEN_QUOTA_EXCEEDED": "该 Key 的 Token 额度已用完，请充值或换 Key",
    "DATAINSPECTIONFAILED": "提示词触发内容安全审核，请改写提示词后重试（积分会自动退回）",
    "POINTS_NOT_ENOUGH": "积分不足，请先充值",
    "PERMISSION_DENIED": "当前 Key 没有该模型/厂商权限，请联系网关管理员开通",
    "AUTH_ERROR": "API Key 无效或已过期，请在插件设置里重新填写中转 Key",
    "UPSTREAM_ERROR": "上游调用失败（502），稍后重试即可",
    "SERVICE_UNAVAILABLE": "上游暂不可用（503），稍后重试即可",
    "BILLING_ERROR": "网关计费不可用（503），请联系网关管理员",
}


def _describe_api_error(error_text):
    """在网关原文后面补一条可操作提示；未命中已知错误码时原样返回。"""
    text = str(error_text or "")
    upper = text.upper()
    for code, hint in _API_ERROR_HINTS.items():
        if code in upper:
            if hint in text:
                return text
            return f"{text}\n提示：{hint}"
    return text


def _normalize_prompt_text(text):
    """统一换行符与首尾空白，避免历史记录里的换行差异导致匹配失败。"""
    normalized = str(text or "").replace("\r\n", "\n").replace("\r", "\n")
    return normalized.strip()


def _prompt_matches_history(stored_prompt, sent_prompt):
    """
    判断任务历史里的 prompt 是否为本次提交的 prompt。

    网关 /api/tasks 列表把 prompt 截断到 500 字符用于展示，长提示词不可能与提交内容
    完全相等；只要一方是另一方的完整前缀、且前缀长度足够，即视为同一个任务。
    """
    stored = _normalize_prompt_text(stored_prompt)
    sent = _normalize_prompt_text(sent_prompt)
    if not stored or not sent:
        return False
    if stored == sent:
        return True
    shorter, longer = (stored, sent) if len(stored) < len(sent) else (sent, stored)
    return len(shorter) >= HISTORY_PROMPT_MIN_PREFIX and longer.startswith(shorter)


def _task_created_at_ms(task):
    try:
        return int(task.get("createdAt"))
    except (TypeError, ValueError, AttributeError):
        return None


def _fetch_recent_tasks(base_url, api_key, earliest_created_at, max_pages=4, page_size=50):
    """
    按时间倒序分页拉取近期任务，遇到早于 earliest_created_at 的记录即停止翻页。

    历史列表按 createdAt 倒序返回，找回刚提交的任务通常一次请求就能命中，
    比固定翻 5 页更快，也不会因为翻页过慢而错过任务。
    """
    history_url = _api_url(base_url, _TASKS_PATH)
    collected = []
    for page in range(1, max_pages + 1):
        response = requests.get(
            history_url,
            headers={"Authorization": f"Bearer {api_key}"},
            params={"page": page, "pageSize": page_size},
            timeout=30,
        )
        if response.status_code != 200:
            raise RuntimeError(_extract_api_error(response))

        data = response.json()
        tasks = [task for task in (data.get("tasks") or []) if isinstance(task, dict)]
        if not tasks:
            break
        collected.extend(tasks)

        created_values = [
            value for value in (_task_created_at_ms(task) for task in tasks) if value is not None
        ]
        if created_values and min(created_values) <= earliest_created_at:
            break
        if not data.get("hasMore"):
            break
    return collected


def _recover_submitted_task_id(
    base_url,
    api_key,
    payload,
    submitted_at_ms,
    poll_interval=MIN_POLL_INTERVAL,
    deadline_seconds=RECOVERY_DEADLINE_SECONDS,
):
    """
    提交响应丢失后（读超时 / 504 / 非 JSON），从任务历史中找回本次请求的任务 ID。

    网关是先受理任务、再回写任务历史的，响应超时并不代表任务没创建（积分也照扣）。
    按 prompt + 模型 + 时间窗口找回任务 ID 后继续轮询，宿主软件才能拿到视频，
    用户也不会因为看不到任务而重跑、重复扣积分。此函数绝不重复提交。
    """
    expected_prompt = str(payload.get("prompt") or "")
    expected_model = str(payload.get("model") or "")
    if not expected_prompt or not expected_model:
        return None

    earliest_created_at = submitted_at_ms - 2 * 60 * 1000
    interval = max(3, min(int(poll_interval or RECOVERY_INTERVAL_SECONDS), RECOVERY_INTERVAL_SECONDS))
    deadline = time.time() + max(interval * 2, int(deadline_seconds))
    last_error = None
    attempt = 0

    while True:
        attempt += 1
        try:
            candidates = []
            for task in _fetch_recent_tasks(base_url, api_key, earliest_created_at):
                if not task.get("id") or str(task.get("type") or "").lower() != "video":
                    continue
                task_model = str(task.get("model") or task.get("modelName") or "")
                if task_model != expected_model:
                    continue
                if not _prompt_matches_history(task.get("prompt"), expected_prompt):
                    continue
                created_at = _task_created_at_ms(task)
                if created_at is None or created_at < earliest_created_at:
                    continue
                candidates.append((created_at, str(task["id"]), str(task.get("status") or "unknown")))
            last_error = None

            if candidates:
                # 优先取提交开始后创建且时间最近的任务，避免误认更早的同提示词任务。
                candidates.sort(
                    key=lambda item: (
                        0 if item[0] >= submitted_at_ms else 1,
                        abs(item[0] - submitted_at_ms),
                    )
                )
                created_at, task_id, status = candidates[0]
                delta_seconds = (created_at - submitted_at_ms) / 1000
                print(
                    f"[提交恢复] 已从任务历史找回任务 ID: {task_id} "
                    f"（状态: {status}，创建时间偏移: {delta_seconds:+.1f}s，第 {attempt} 次探测命中）"
                )
                return task_id
        except (requests.exceptions.RequestException, ValueError, TypeError, RuntimeError) as exc:
            last_error = str(exc)

        if time.time() >= deadline:
            break

        print(
            f"[提交恢复] 暂未找到匹配任务，{interval}s 后继续查询 "
            f"（第 {attempt} 次: {last_error or '任务记录尚未同步'}）"
        )
        time.sleep(interval)
        interval = min(interval * 2, RECOVERY_MAX_INTERVAL_SECONDS)

    print(f"[提交恢复] 未能找回任务 ID（已探测 {attempt} 次）: {last_error or '没有匹配的近期任务'}")
    return None


# 上游对参考素材做安全校验时的典型错误关键词
_REFERENCE_REJECTION_KEYWORDS = ("引用素材", "参考图", "安全校验", "素材未通过", "image check", "safety")

# 参考图转 JPEG 时的合成底色（PNG 透明通道会合成到该颜色上）
_REFERENCE_JPEG_BACKGROUND = (255, 255, 255)


def _build_submit_error(response):
    """把提交失败转成 PLUGIN_ERROR；参考素材被拒时附上排查提示。"""
    error_text = _extract_api_error(response)
    if response.status_code == 400 and any(keyword in error_text for keyword in _REFERENCE_REJECTION_KEYWORDS):
        error_text += (
            "（排查提示：多为参考图内容或尺寸触发上游安全校验。"
            "可先换一张干净的图试生成，或改用文生视频确认模型可用；"
            "插件已自动对参考图做转 JPEG / 限尺寸预处理）"
        )
    return f"PLUGIN_ERROR:::{_describe_api_error(error_text)}"


# ---------------------------------------------------------------- 素材导入排队

_IMPORT_SEMAPHORE = threading.BoundedSemaphore(IMPORT_CONCURRENCY)


def _is_submit_busy(response):
    """
    判断提交是否属于「未被网关受理、可安全退避重试」的繁忙场景：
    素材导入并发超限（429 / WAN3_API_IMPORT_BUSY）、视频并发或账号/IP 限流（429）。
    """
    if getattr(response, "status_code", None) == 429:
        return True
    try:
        text = str(getattr(response, "text", "") or "").upper()
    except Exception:
        return False
    return "WAN3_API_IMPORT_BUSY" in text


def _submit_busy_reason(response):
    """把 429 / 繁忙响应细分出可读原因（网关文档 §6）。"""
    text = str(getattr(response, "text", "") or "")
    upper = text.upper()
    if "WAN3_API_IMPORT_BUSY" in upper:
        return f"参考素材导入并发超限（每账号 {IMPORT_CONCURRENCY} 个）"
    if "TOKEN_QUOTA_EXCEEDED" in upper:
        return "Key 的 Token 额度已用完"
    if "CONCURRENCY" in upper or "并发" in text:
        return "视频生成并发超限"
    if getattr(response, "status_code", None) == 429:
        return "网关限流（约 20 次/分钟、500 次/天/单 IP）"
    return "网关繁忙"


def _acquire_import_slot(deadline, cb=None):
    """
    本地素材导入排队：最多 IMPORT_CONCURRENCY 个带素材的分镜同时提交，与网关
    「参考素材导入并发（每账号 2 个）」保持一致，避免同批分镜同时提交时互相挤爆报错。

    排队期间打印进度并回报宿主；超过 deadline 仍未拿到名额时返回 False
    （改为直接提交，由网关 429 退避重试兜底）。
    """
    if _IMPORT_SEMAPHORE.acquire(blocking=False):
        return True
    started = time.time()
    while time.time() < deadline:
        if _IMPORT_SEMAPHORE.acquire(timeout=1):
            elapsed = int(time.time() - started)
            if elapsed:
                print(f"[排队] 已获得素材导入名额（本次等待 {elapsed}s）")
            return True
        elapsed = int(time.time() - started)
        if elapsed and elapsed % 5 == 0:
            print(
                f"[排队] 素材导入并发已满（{IMPORT_CONCURRENCY}/{IMPORT_CONCURRENCY}），"
                f"继续排队…（已等待 {elapsed}s）"
            )
            if cb:
                cb(f"排队中（等待素材导入 {elapsed}s）")
    print(f"[排队] 等待素材导入名额超时（{int(time.time() - started)}s），改为直接提交")
    return False


# ---------------------------------------------------------------- 参数

def get_params():
    params = _default_params.copy()
    params.update(load_plugin_config(_PLUGIN_FILE))
    params["base_url"] = _normalize_base_url(params.get("base_url", _DEFAULT_BASE_URL))
    return params


def get_info():
    return {
        "name": "AIGC创作站·生视频",
        "description": "通过 youzan666.vip AIGC 网关调用视频模型生成视频，支持文生视频 / 图生视频 / 多模态参考素材稳定绑定。",
        "version": _PLUGIN_VERSION,
        "author": "youzan-aigc",
        "images_per_batch": 1,
    }


# ---------------------------------------------------------------- 模型列表

def _list_models():
    params = get_params()
    api_key = (params.get("api_key") or "").strip()
    if not api_key:
        return {"ok": False, "error": "请先在插件设置中填写 API Key"}
    try:
        response = requests.get(
            _api_url(params.get("base_url", _DEFAULT_BASE_URL), _MODELS_PATH),
            headers={"Authorization": f"Bearer {api_key}"},
            timeout=30,
        )
    except requests.exceptions.RequestException as exc:
        return {"ok": False, "error": f"请求失败: {exc}"}

    if response.status_code != 200:
        return {"ok": False, "error": _extract_api_error(response)}

    try:
        payload = response.json()
    except ValueError:
        return {"ok": False, "error": "响应不是合法 JSON"}

    models = []
    for item in payload.get("data", []) or []:
        if isinstance(item, dict) and item.get("id"):
            models.append(str(item["id"]))
    models = sorted(set(models))
    if not models:
        return {"ok": False, "error": "网关未返回任何模型，请确认 Key 权限后重试"}
    return {"ok": True, "models": models, "count": len(models)}


def _fetch_points(api_key, base_url):
    """查询当前 API Key 的剩余积分。"""
    response = requests.get(
        _api_url(base_url, _USER_ME_PATH),
        headers={"Authorization": f"Bearer {api_key}"},
        timeout=30,
    )
    if response.status_code != 200:
        raise Exception(_extract_api_error(response))
    try:
        data = response.json()
    except ValueError:
        raise Exception("积分接口返回不是合法 JSON")
    if not isinstance(data, dict) or "points" not in data:
        raise Exception("积分接口未返回 points 字段")
    return data.get("points")


def handle_action(action, data=None):
    if action == "list_models":
        return _list_models()
    if action == "check_update":
        return _check_update_available()
    if action == "do_update":
        data = data or {}
        return _execute_update(
            data.get("download_url", ""),
            data.get("sha256", ""),
            data.get("remote_version", ""),
        )
    if action == "check_points":
        params = get_params()
        api_key = (params.get("api_key") or "").strip()
        if not api_key:
            return {"ok": False, "error": "请先在插件设置中填写 API Key"}
        try:
            points = _fetch_points(api_key, params.get("base_url", _DEFAULT_BASE_URL))
        except Exception as exc:
            return {"ok": False, "error": str(exc).replace("PLUGIN_ERROR:::", "")}
        return {"ok": True, "points": points, "message": f"剩余积分：{points}"}
    if action == "audio_upload":
        return _handle_audio_upload(data)
    return {"ok": False, "error": f"未知动作: {action}"}


# ---------------------------------------------------------------- 参考图

def _normalize_reference_images(reference_images):
    if not reference_images:
        return {}
    # 宿主通常传 0 基 {0: 路径, 1: ...}；跨 JSON 边界后键可能变成字符串，
    # 两种形态都统一包进「参考图片MAP」，避免 "10" 被当成普通字段丢掉。
    if isinstance(reference_images, dict):
        if "参考图片MAP" in reference_images:
            return dict(reference_images)
        keys = list(reference_images.keys())
        if keys and all(str(key).strip().lstrip("-").isdigit() for key in keys):
            return {"参考图片MAP": dict(reference_images)}
    return dict(reference_images)


_AUDIO_EXTS = (".mp3", ".wav", ".aac", ".ogg", ".flac", ".m4a", ".opus", ".wma")


def _is_audio_file(path):
    """粗判 path 是否音频：URL 看扩展名，本地文件看扩展名或文件头魔数。"""
    text = str(path or "").strip()
    if not text:
        return False
    if text.startswith(("http://", "https://")):
        clean = text.split("?")[0].split("#")[0].lower()
        return clean.endswith(_AUDIO_EXTS)
    if not os.path.exists(text):
        return False
    if text.lower().endswith(_AUDIO_EXTS):
        return True
    try:
        with open(text, "rb") as f:
            head = f.read(16)
        if head.startswith(b"RIFF") and len(head) >= 12 and head[8:12] == b"WAVE":
            return True
        return head.startswith((b"ID3", b"OggS", b"fLaC", b"\x1aE\xdf\xa3"))
    except Exception:
        return False


def _extract_path_value(value):
    """参考项值可能是 str 路径，也可能是 {path, media_type} 结构，统一提取路径。"""
    if isinstance(value, dict):
        for key in ("path", "url", "uri", "file_path", "image_path", "audio_path"):
            text = str(value.get(key) or "").strip()
            if text:
                return text
        return ""
    return str(value or "").strip()


def _reference_transport_kind(value):
    """识别参考素材的传输形态，拒绝网关会重新分组的不透明素材 ID。"""
    text = _extract_path_value(value)
    lower = text.lower()
    if lower.startswith("https://"):
        return "https_url"
    if lower.startswith("http://"):
        return "http_url"
    if lower.startswith("data:image/"):
        return "data_url"
    if text and os.path.exists(text):
        return "local_file"
    if text:
        return "asset_id"
    return "empty"


def _reference_identity(value):
    """生成不改变槽位的去重键；只用于检测重复，不用于压缩素材数组。"""
    text = _extract_path_value(value)
    if not text:
        return ""
    lower = text.lower()
    if lower.startswith(("http://", "https://")):
        parsed = urlparse(text)
        return "url:" + "|".join((
            parsed.scheme.lower(),
            parsed.netloc.lower(),
            parsed.path,
            parsed.query,
            parsed.fragment,
        ))
    if lower.startswith("data:"):
        return "data:" + hashlib.sha256(text.encode("utf-8")).hexdigest()
    if os.path.exists(text):
        return "file:" + os.path.abspath(text).lower()
    return "raw:" + text


def _build_reference_slot_plan(image_sources, audio_sources):
    """
    在任何上传/预处理开始前冻结本次请求的槽位计划。

    平台可能并行导入素材，也可能把素材 ID 与 URL 分组；插件不能等处理完成后
    再靠完成顺序推断编号。因此这里只允许可验证的 URL、本地文件或图片 data URL，
    并拒绝同一媒体类型内的重复来源，避免服务端去重后造成槽位前移。
    """
    plan = {"images": [], "audios": []}
    for key, label, sources in (
        ("images", "图片", image_sources or []),
        ("audios", "音频", audio_sources or []),
    ):
        seen = {}
        for slot, source in enumerate(sources, start=1):
            path = _extract_path_value(source)
            if not path:
                raise Exception(
                    f"PLUGIN_ERROR:::{label}{slot}没有可用路径，"
                    "为避免平台并行导入后槽位前移已停止提交"
                )
            transport = _reference_transport_kind(path)
            if transport == "asset_id":
                raise Exception(
                    f"PLUGIN_ERROR:::{label}{slot}使用了不透明素材 ID（{path}）；"
                    "当前接口可能把素材 ID 与 URL 重新分组，为避免引用错位请先转换为 HTTPS 公网 URL"
                )
            if transport == "http_url":
                raise Exception(
                    f"PLUGIN_ERROR:::{label}{slot}使用了不安全的 HTTP URL（{path}）；"
                    "请改用 HTTPS 公网直链"
                )
            identity = _reference_identity(path)
            if identity in seen:
                previous = seen[identity]
                raise Exception(
                    f"PLUGIN_ERROR:::{label}{slot}与{label}{previous}使用了相同素材来源；"
                    "平台去重后会改变槽位编号，请为每个引用提供唯一素材或删掉重复引用"
                )
            seen[identity] = slot
            plan[key].append({
                "slot": slot,
                "source": path,
                "transport": transport,
                "identity": identity,
            })
    return plan


def _log_reference_slot_plan(plan):
    """输出冻结后的源素材槽位，便于和最终上传 URL 逐项核对。"""
    for key, label in (("images", "图片"), ("audios", "音频")):
        for item in plan.get(key, []):
            print(
                f"[素材计划] {label}{item['slot']} <- {_preview_media(item['source'])}"
                f" ({item['transport']})"
            )


def _validate_reference_slot_plan(plan, payload):
    """确保处理完成后没有新增、丢失或前移任何已冻结的素材槽位。"""
    expected = {
        "images": _payload_slot_count(payload.get("reference_image")),
        "audios": _payload_slot_count(payload.get("reference_audio")),
    }
    actual = {
        "images": len(plan.get("images", [])),
        "audios": len(plan.get("audios", [])),
    }
    mismatches = []
    for key, label in (("images", "图片"), ("audios", "音频")):
        if expected[key] != actual[key]:
            mismatches.append(
                f"{label}计划 {actual[key]} 个、最终请求 {expected[key]} 个"
            )
    if mismatches:
        raise Exception(
            "PLUGIN_ERROR:::素材槽位在处理过程中发生变化："
            + "；".join(mismatches)
            + "。为避免平台重排后引用错位已停止提交"
        )


def _ordered_indexed_values(value, label):
    """读取数组或 0 基 MAP，并拒绝会造成槽位前移的稀疏索引。"""
    if value is None:
        return []
    if isinstance(value, (list, tuple)):
        return list(value)
    if not isinstance(value, dict):
        return [value] if value else []

    if label == "image" and "参考图片MAP" in value:
        value = value.get("参考图片MAP") or {}
    if not isinstance(value, dict):
        return _ordered_indexed_values(value, label)
    if not value:
        return []

    keys = list(value.keys())
    numeric_keys = []
    for key in keys:
        text = str(key).strip()
        if not text.lstrip("-").isdigit():
            numeric_keys = []
            break
        numeric_keys.append(int(text))
    if numeric_keys:
        ordered = sorted(zip(numeric_keys, keys), key=lambda pair: pair[0])
        expected = list(range(len(ordered)))
        actual = [index for index, _ in ordered]
        if actual != expected:
            raise Exception(
                f"PLUGIN_ERROR:::参考{label}槽位不连续（收到 {actual}，期望从 0 连续编号），"
                "为避免提示词引用错位，已停止提交"
            )
        return [value[key] for _, key in ordered]

    # 兼容旧插件传入的命名 MAP；只有明确数字键时才做槽位连续性校验。
    return [value[key] for key in keys]


def _reference_media_kind(value):
    """推断参考项类型；优先使用宿主 media_type，再用 MIME/扩展名兜底。"""
    media_type = ""
    if isinstance(value, dict):
        media_type = " ".join(
            str(value.get(key) or "").strip().lower()
            for key in ("media_type", "type", "mime_type", "kind")
        )
    path = _extract_path_value(value)
    media_text = f"{media_type} {path.lower()}"
    if "audio" in media_type or "音频" in media_type or _is_audio_file(path):
        return "audio"
    if "video" in media_type or "视频" in media_type:
        return "video"
    if "image" in media_type or "图片" in media_type or "图像" in media_type:
        return "image"
    clean = path.split("?", 1)[0].split("#", 1)[0].lower()
    if clean.startswith("data:image/") or clean.endswith((
        ".png", ".jpg", ".jpeg", ".webp", ".bmp", ".gif", ".tif", ".tiff"
    )):
        return "image"
    if clean.endswith(_VIDEO_EXTS):
        return "video"
    if clean.endswith(_AUDIO_EXTS):
        return "audio"
    if "image/" in media_text:
        return "image"
    return ""


def _ordered_reference_items(context, media_kind):
    """从宿主的 reference_items 取得指定类型，返回 None 表示没有可用结构化列表。"""
    items = context.get("reference_items")
    if not isinstance(items, list) or not items:
        return None
    selected = []
    for item in items:
        if not isinstance(item, dict):
            continue
        path = _extract_path_value(item)
        if not path:
            continue
        kind = _reference_media_kind(item)
        # 旧宿主偶尔省略 media_type；未知且不是音频/视频时按图片处理。
        if not kind and media_kind == "image":
            kind = "image"
        if kind == media_kind:
            selected.append(item)
    return selected or None


def _reference_values(context, media_kind):
    """按 reference_items -> 独立 MAP 的优先级读取单一媒体类型，绝不混并去重。"""
    structured = _ordered_reference_items(context, media_kind)
    if structured is not None:
        return structured
    key = {
        "image": "reference_images",
        "audio": "reference_audios",
        "video": "reference_videos",
    }[media_kind]
    source = context.get(key)
    if media_kind == "image":
        source = _normalize_reference_images(source)
    return _ordered_indexed_values(source, media_kind)


def _preview_media(value, limit=96):
    """日志里只显示素材值的前若干字符，避免把整段 base64 参考图写进宿主日志。"""
    if isinstance(value, (list, tuple)):
        return [_preview_media(item, limit) for item in value]
    text = str(value or "")
    if len(text) <= limit:
        return text
    return f"{text[:limit]}…（共 {len(text)} 字符）"


def _log_media_sources(context):
    """诊断日志：确认宿主把分镜素材放进了哪些 context 键（文件名摘要）。"""
    def _brief(v):
        if isinstance(v, dict):
            return {str(k): _brief(x) for k, x in list(v.items())[:6]}
        if isinstance(v, (list, tuple)):
            return [_brief(x) for x in v[:6]]
        text = str(v or "").strip()
        if os.path.exists(text):
            return os.path.basename(text)
        return text[:80]
    print(f"[素材诊断] reference_images={_brief(context.get('reference_images'))}")
    print(f"[素材诊断] reference_audios={_brief(context.get('reference_audios'))}")
    print(f"[素材诊断] reference_items={_brief(context.get('reference_items'))}")
    print(f"[素材诊断] audio_path={_preview_media(context.get('audio_path'))}")


def _collect_image_references(context, max_count=MAX_IMAGE_REFS):
    """
    收集普通参考图。

    关键约束：Wan3.0 的提示词引用是按数组位置绑定的，因此这里不去重、
    不跳过中间失败项，也不把 reference_items 与 reference_images 交叉拼接。
    首尾帧需走各自的官方字段，因此不混入 reference_image。
    """
    values = _reference_values(context, "image")
    if len(values) > max_count:
        print(
            f"[WARN] 参考图共 {len(values)} 张，Wan3.0 最多提交 {max_count} 张；"
            f"只保留槽位 1-{max_count}，提示词若引用更高编号将被提交前拦截"
        )
        values = values[:max_count]

    paths = []
    for index, value in enumerate(values, start=1):
        path = _extract_path_value(value)
        if not path:
            raise Exception(f"PLUGIN_ERROR:::图片{index}没有可用路径，为避免引用错位已停止提交")
        kind = _reference_media_kind(value)
        if kind == "audio":
            raise Exception(
                f"PLUGIN_ERROR:::图片{index}实际是音频（{path}），"
                "宿主素材类型与图片槽位不一致，为避免引用错位已停止提交"
            )
        if kind == "video":
            raise Exception(
                f"PLUGIN_ERROR:::图片{index}实际是视频（{path}），"
                "宿主素材类型与图片槽位不一致，为避免引用错位已停止提交"
            )
        paths.append(path)
    return paths


_VIDEO_EXTS = (".mp4", ".mov", ".webm", ".mkv", ".avi", ".m4v")


def _upload_media_to_uguu(file_path, timeout=60, retry_count=3):
    """上传本地音频/视频到 Uguu，返回临时公网直链。图片不走此链路。"""
    if not os.path.isfile(file_path):
        raise Exception(f"PLUGIN_ERROR:::媒体文件不存在: {file_path}")
    mime_type = mimetypes.guess_type(file_path)[0] or "application/octet-stream"
    last_error = None
    retry_count = max(1, int(retry_count))
    for attempt in range(1, retry_count + 1):
        try:
            with open(file_path, "rb") as file_obj:
                response = requests.post(
                    "https://uguu.se/upload",
                    files={"files[]": (os.path.basename(file_path), file_obj, mime_type)},
                    timeout=timeout,
                )
            if response.status_code == 200:
                data = response.json() or {}
                files = data.get("files") or []
                url = files[0].get("url") if files and isinstance(files[0], dict) else None
                if url:
                    print(f"[媒体] 已上传 Uguu: {file_path} -> {url}")
                    return url
                last_error = "返回中缺少文件 URL"
            else:
                last_error = f"HTTP {response.status_code}: {response.text[:200]}"
        except (requests.exceptions.RequestException, ValueError) as exc:
            last_error = str(exc)
        if attempt < retry_count:
            time.sleep(min(2 ** attempt, 10))
    raise Exception(f"PLUGIN_ERROR:::媒体上传 Uguu 失败: {last_error}")


def _handle_audio_upload(data):
    """UI 选择本地音频后上传 Uguu，返回临时公网 URL。"""
    data = data or {}
    name = str(data.get("name") or "audio.mp3").strip()
    b64_text = str(data.get("base64") or "").strip()
    if not b64_text:
        return {"ok": False, "error": "未收到音频内容"}
    try:
        audio_bytes = base64.b64decode(b64_text, validate=False)
        if not audio_bytes:
            return {"ok": False, "error": "音频内容为空"}
        ext = os.path.splitext(name)[1].lower() or ".mp3"
        temp_dir = tempfile.mkdtemp(prefix="zz_audio_")
        file_path = os.path.join(temp_dir, "audio" + ext)
        with open(file_path, "wb") as file_obj:
            file_obj.write(audio_bytes)
        url = _upload_media_to_uguu(file_path)
        return {"ok": True, "url": url, "name": name, "size": len(audio_bytes)}
    except Exception as exc:
        return {"ok": False, "error": str(exc).replace("PLUGIN_ERROR:::", "")}


def _collect_video_references(context, max_count=5, timeout=60):
    """收集参考视频 URL；本地视频自动上传 Uguu。"""
    paths = []
    seen = set()

    def add(value):
        if isinstance(value, dict):
            media_type = str(value.get("media_type") or "").lower()
            if media_type and "video" not in media_type:
                return
        path = _extract_path_value(value)
        if not path or len(paths) >= max_count or path in seen:
            return
        if path.startswith(("http://", "https://")):
            seen.add(path)
            paths.append(path)
        elif os.path.exists(path) or path.lower().split("?")[0].endswith(_VIDEO_EXTS):
            url = _upload_media_to_uguu(path, timeout=timeout)
            seen.add(url)
            paths.append(url)

    refs = context.get("reference_videos") or {}
    if isinstance(refs, dict):
        for key in sorted(refs.keys(), key=lambda item: str(item)):
            add(refs[key])
    elif isinstance(refs, (list, tuple)):
        for value in refs:
            add(value)
    for item in context.get("reference_items") or []:
        add(item)
    return paths


def _flatten_to_rgb(image, background=None):
    """
    把任意模式的 PIL 图片安全拍平成 JPEG 可用的图像。

    直接 convert("RGB") 有两个坑：透明通道被丢掉但不与背景合成（透明区变黑），
    16bit / I 模式超过 255 的数值被截断（中高调整片过曝成纯白）。
    这里先把高位深归一化到 8bit，再把 alpha 合成到实底。
    """
    from PIL import Image

    if image.mode in ("I", "I;16", "I;16B", "I;16L"):
        image = image.point(lambda value: value * (255.0 / 65535.0)).convert("L")
    elif image.mode == "F":
        image = image.point(lambda value: min(max(value, 0.0), 1.0) * 255).convert("L")
    if image.mode == "P" and "transparency" in image.info:
        image = image.convert("RGBA")
    if image.mode in ("RGBA", "LA", "PA"):
        rgba = image.convert("RGBA")
        base_color = _REFERENCE_JPEG_BACKGROUND if background is None else background
        flattened = Image.new("RGB", image.size, base_color)
        flattened.paste(rgba, mask=rgba.getchannel("A"))
        return flattened
    if image.mode in ("RGB", "L"):
        return image
    return image.convert("RGB")


def _convert_image_to_jpeg(image, max_side=2048, quality=92, max_bytes=8 * 1024 * 1024):
    """把已打开的 PIL 图片统一转成 JPEG bytes：拍平、限最长边、压体积。"""
    import io
    from PIL import Image

    image = _flatten_to_rgb(image)
    width, height = image.size
    longest = max(width, height)
    if longest > max_side:
        scale = max_side / float(longest)
        image = image.resize(
            (max(1, int(width * scale)), max(1, int(height * scale))),
            Image.LANCZOS,
        )
    buffer = io.BytesIO()
    image.save(buffer, "JPEG", quality=quality)
    if buffer.tell() > max_bytes:
        for lower_quality in range(quality - 10, 39, -10):
            buffer = io.BytesIO()
            image.save(buffer, "JPEG", quality=lower_quality)
            if buffer.tell() <= max_bytes:
                break
    return buffer.getvalue()


def _preprocess_reference_image(image_path, max_side=2048, quality=92, max_bytes=8 * 1024 * 1024):
    """
    参考图预处理：统一转 JPEG、限最长边、压体积，返回临时 .jpg 路径。

    PNG 也走这条路：透明通道合成到白底、16bit 归一化到 8bit、动图只取第 1 帧，
    避免 convert("RGB") 造成的透明区变黑 / 高位深过曝。
    处理失败时返回原路径（由调用方决定是否放行）。
    """
    try:
        from PIL import Image

        image = Image.open(image_path)
        source_format = (image.format or "").upper()
        frame_count = getattr(image, "n_frames", 1)
        if frame_count > 1:
            image.seek(0)
        image.load()
        jpeg_bytes = _convert_image_to_jpeg(image, max_side=max_side, quality=quality, max_bytes=max_bytes)
        temp_path = f"{image_path}_preprocessed.jpg"
        with open(temp_path, "wb") as file_obj:
            file_obj.write(jpeg_bytes)
        notes = [f"源格式 {source_format}"] if source_format else []
        if image.mode in ("RGBA", "LA", "PA") or (image.mode == "P" and "transparency" in image.info):
            notes.append("透明通道已合成白底")
        if frame_count > 1:
            notes.append(f"动图仅取第 1 帧（共 {frame_count} 帧）")
        suffix = "，" + "，".join(notes) if notes else ""
        print(
            f"[参考图] 已预处理: {image_path} -> {temp_path}"
            f"（最长边 {max(image.size)}px, {len(jpeg_bytes) // 1024}KB{suffix}）"
        )
        return temp_path
    except Exception as exc:
        print(f"[参考图] 预处理失败: {exc}")
        return image_path


def _resolve_reference_image_url(image_path):
    """
    将参考图转换为文档支持的值：公网 URL 原样透传；本地图片预处理后转
    data:image/jpeg;base64，避免上传到第三方公共图床。

    PNG（含透明底 / 16bit / 动图）统一由 _preprocess_reference_image 安全转换，
    不要求用户手动先转 JPG。
    """
    if not image_path:
        return None
    text = str(image_path)
    if text.startswith(("http://", "https://", "data:image/")):
        return text
    if not os.path.exists(text):
        print(f"[参考图] 文件不存在: {text}")
        return None
    upload_path = _preprocess_reference_image(text)
    if upload_path == text:
        raise Exception(
            "PLUGIN_ERROR:::参考图预处理失败（图片格式不支持或文件损坏），"
            "请将图片转为 JPG 后重试，或在高级设置的「参考图 URL」中填写 JPG 直链"
        )
    try:
        with open(upload_path, "rb") as file_obj:
            encoded = base64.b64encode(file_obj.read()).decode("ascii")
        return f"data:image/jpeg;base64,{encoded}"
    finally:
        if os.path.exists(upload_path):
            try:
                os.remove(upload_path)
            except OSError:
                pass


# ---------------------------------------------------------------- 视频校验

def _looks_like_video(content):
    head = content[:64]
    if head.startswith(b"{"):
        return False
    if _MP4_BOX in head:
        return True
    if head.startswith(_WEBM_MAGIC):
        return True
    return False


def _extract_task_id(data):
    """兼容 OpenAI 与 DashScope 两种提交响应的任务 ID。"""
    if not isinstance(data, dict):
        return None
    for key in ("taskId", "task_id", "id"):
        value = data.get(key)
        if value:
            return str(value)
    for key in ("output", "data", "result"):
        nested = data.get(key)
        if isinstance(nested, dict):
            value = _extract_task_id(nested)
            if value:
                return value
    return None


def _extract_task_status(data):
    """兼容 OpenAI status 与 DashScope output.task_status。"""
    if not isinstance(data, dict):
        return "unknown"
    for key in ("status", "task_status", "taskStatus"):
        value = data.get(key)
        if value:
            return str(value).strip().lower()
    for key in ("output", "data", "result"):
        nested = data.get(key)
        if isinstance(nested, dict):
            value = _extract_task_status(nested)
            if value != "unknown":
                return value
    return "unknown"


def _extract_video_url_candidates(data):
    """
    兼容网关不同版本的结果包装，按优先级返回候选直链：
    上游直链（url）优先、网关备份副本（backupUrl）兜底，前者失效时可自动回退。
    """
    if not isinstance(data, dict):
        return []

    candidates = []

    def add(value):
        if not isinstance(value, str):
            return
        text = value.strip()
        if not text or not text.startswith(("http://", "https://")):
            return
        if text not in candidates:
            candidates.append(text)

    for key in ("url", "directUrl", "direct_url", "video_url", "videoUrl", "download_url", "downloadUrl"):
        add(data.get(key))
    for key in ("backupUrl", "backup_url", "backupURL"):
        add(data.get(key))
    for key in ("result", "data", "output", "video"):
        nested = data.get(key)
        if isinstance(nested, dict):
            for url in _extract_video_url_candidates(nested):
                add(url)
        elif isinstance(nested, list):
            for item in nested:
                for url in _extract_video_url_candidates(item):
                    add(url)
    return candidates


def _extract_video_url(data):
    """兼容旧调用：返回优先级最高的视频直链。"""
    candidates = _extract_video_url_candidates(data)
    return candidates[0] if candidates else None


def _download_video_content(url, base_url, api_key, timeout, attempts=4):
    """下载直链内容；429/502/503/504 与网络异常按指数退避重试，最终失败时抛异常。"""
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                      "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
        "Accept": "*/*",
    }
    if str(url).startswith(base_url):
        headers["Authorization"] = f"Bearer {api_key}"

    last_error = "未知错误"
    for attempt in range(1, attempts + 1):
        if attempt > 1:
            time.sleep(2 ** attempt)
        try:
            response = requests.get(url, headers=headers, timeout=timeout)
        except requests.exceptions.RequestException as exc:
            last_error = f"网络异常: {exc}"
            print(f"[WARN] 视频下载网络异常: {exc}，稍后重试（{attempt}/{attempts}）")
            continue
        if response.status_code == 200:
            return response.content
        last_error = f"HTTP {response.status_code} - {response.text[:200]}"
        if response.status_code in _RETRYABLE_STATUS_CODES:
            print(f"[WARN] 视频下载返回 {response.status_code}，稍后重试（{attempt}/{attempts}）")
            continue
        break
    raise Exception(f"直链下载失败（最多尝试 {attempts} 次）: {last_error}")


def _extract_fail_reason(data):
    """直接返回网关失败响应的完整原文（JSON 原样，不截断不改写）。"""
    try:
        return json.dumps(data, ensure_ascii=False)
    except Exception:
        return str(data)


def _find_ffmpeg():
    """定位随软件附带的 ffmpeg；都找不到时返回 None（不阻断生成）。"""
    candidates = [
        r"E:\字字动画\resources\ffmpeg\bin\ffmpeg.exe",
        r"D:\字字动画\resources\ffmpeg\bin\ffmpeg.exe",
        "ffmpeg",
    ]
    for candidate in candidates:
        if os.path.sep in candidate:
            if os.path.exists(candidate):
                return candidate
        elif shutil.which(candidate):
            return candidate
    return None


def _probe_media_duration(file_path):
    """用 ffmpeg 探测本地音频/视频时长（秒，浮点）；失败返回 None（不阻断，仅告警）。"""
    import subprocess
    ffmpeg = _find_ffmpeg()
    if not ffmpeg or not file_path:
        return None
    try:
        proc = subprocess.run([ffmpeg, "-i", str(file_path)], capture_output=True, timeout=15)
    except Exception:
        return None
    # ffmpeg -i 不带输出参数时信息在 stderr
    text = (proc.stderr or b"").decode("utf-8", errors="ignore")
    match = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", text)
    if not match:
        return None
    hours, minutes, seconds = int(match.group(1)), int(match.group(2)), float(match.group(3))
    return hours * 3600 + minutes * 60 + seconds


def _trim_media_file(file_path, seconds, timeout=60):
    """
    用 ffmpeg 把本地音频截断到 seconds 秒，返回截断后的文件路径。

    参考音频只用前几秒即可（视频本身只有 N 秒），截断后即可满足官方「单段/总长 ≤15 秒」限制。
    截断失败时返回原路径（继续上传，不阻断生成）。
    """
    import subprocess
    ffmpeg = _find_ffmpeg()
    if not ffmpeg or not seconds or seconds <= 0:
        return file_path
    extension = (os.path.splitext(file_path)[1] or ".mp3").lower()
    codec_attempts = [["-c", "copy"]]
    if extension == ".mp3":
        codec_attempts.append(["-c:a", "libmp3lame", "-b:a", "128k"])
    elif extension == ".wav":
        codec_attempts.append(["-c:a", "pcm_s16le"])
    else:
        codec_attempts.append(["-c:a", "aac", "-b:a", "128k"])

    temp_dir = tempfile.mkdtemp(prefix="zz_audio_trim_")
    stem = os.path.splitext(os.path.basename(file_path))[0]
    for index, codec_args in enumerate(codec_attempts):
        output_path = os.path.join(temp_dir, f"{stem}_trim{index}{extension}")
        try:
            proc = subprocess.run(
                [ffmpeg, "-y", "-i", str(file_path), "-t", f"{float(seconds):.3f}",
                 "-vn", *codec_args, output_path],
                capture_output=True, timeout=timeout,
            )
        except Exception:
            continue
        if proc.returncode == 0 and os.path.exists(output_path) and os.path.getsize(output_path) > 0:
            print(
                f"[音频] 已截断到 {float(seconds):.1f}s: {os.path.basename(file_path)}"
                f" -> {os.path.getsize(output_path) // 1024}KB"
            )
            return output_path
    print(f"[WARN] 音频截断失败，改用原始文件（网关可能因超长报错）: {os.path.basename(file_path)}")
    return file_path


def _audio_keep_seconds(duration_seconds, used_seconds,
                        segment_limit=MAX_AUDIO_TOTAL_SECONDS,
                        max_total_seconds=MAX_AUDIO_TOTAL_SECONDS):
    """
    官方万相3.0 参考音频限制：单段 [1,15] 秒、总时长 ≤15 秒。

    返回该段音频应保留的秒数；返回 None 表示这段放不下
    （剩余额度不足 1 秒，或音频本身短于 1 秒）。
    """
    remaining = max_total_seconds - max(0.0, used_seconds or 0.0)
    if remaining < MIN_MEDIA_SECONDS:
        return None
    limit = min(segment_limit, remaining)
    if duration_seconds is None:
        return limit
    if duration_seconds < MIN_MEDIA_SECONDS:
        return None
    return min(duration_seconds, limit)


def _prepare_audio_references(sources, timeout=60, segment_limit=MAX_AUDIO_TOTAL_SECONDS,
                              max_total_seconds=MAX_AUDIO_TOTAL_SECONDS,
                              max_count=MAX_AUDIO_REFS):
    """
    按官方万相3.0 规则准备参考音频 URL：最多 5 段、单段 [1,15] 秒、总时长 ≤15 秒。

    · 本地音频先探测时长，超过可用额度（= min(15 秒, 本镜输出时长)）时用 ffmpeg 截断再上传；
    · 按顺序累计总时长，某段会突破总上限时截断到剩余额度；
      任何无法保留的槽位都直接报错，绝不让后续音频前移；
    · 公网 URL 音频无法探测/截断，原样保留（真超限由网关报错，插件会给出中文提示）。
    """
    urls = []
    used = 0.0
    for slot, source in enumerate(sources, start=1):
        text = str(source or "").strip()
        if not text:
            raise Exception(f"PLUGIN_ERROR:::音频{slot}没有可用路径，为避免引用错位已停止提交")
        if len(urls) >= max_count:
            raise Exception(
                f"PLUGIN_ERROR:::提示词/素材引用了至少音频{slot}，"
                f"但 Wan3.0 最多支持 {max_count} 段参考音频；为避免前移已停止提交"
            )
        if text.startswith(("http://", "https://")):
            # 公网 URL 无法可靠探测时长，但仍然必须占据自己的槽位；重复 URL
            # 也不能去重，否则音频 N 会被后一个素材顶上来。
            urls.append(text)
            continue
        if not os.path.exists(text):
            raise Exception(f"PLUGIN_ERROR:::音频参考 URL 非法或本地文件不存在: {text}")

        seconds = _probe_media_duration(text)
        keep = _audio_keep_seconds(seconds, used, segment_limit, max_total_seconds)
        name = os.path.basename(text)
        if keep is None:
            duration_text = f"{seconds:.1f}s" if seconds is not None else "未知"
            raise Exception(
                f"PLUGIN_ERROR:::音频{slot}（{name}）无法放入 Wan3.0 参考音频额度"
                f"（时长 {duration_text}，剩余不足 {MIN_MEDIA_SECONDS}s），"
                "为避免后续音频槽位前移已停止提交"
            )

        upload_path = text
        if seconds is not None and seconds > keep + 0.05:
            print(f"[音频] {name} 时长 {seconds:.1f}s 超过本次可用 {keep:.1f}s，自动截断后再上传")
            upload_path = _trim_media_file(text, keep, timeout=timeout)
        url = _upload_media_to_uguu(upload_path, timeout=timeout)
        if not url:
            raise Exception(f"PLUGIN_ERROR:::音频{slot}上传后没有返回 URL，为避免引用错位已停止提交")
        urls.append(url)
        used += keep if seconds is not None else 0.0

    if urls:
        print(
            f"[音频] 参考音频 {len(urls)} 段，已知本地音频合计 {used:.1f}s"
            f"（官方单段/总长上限 {max_total_seconds}s）"
        )
    return urls


def _collect_storyboard_audios(context):
    """
    宿主分镜参考音频：优先使用 reference_items 中的原始顺序；没有结构化列表时
    才回退到 reference_audios 的 0 基 MAP。绝不把多个来源去重拼接，否则会改变
    提示词的音频槽位。
    """
    values = _reference_values(context, "audio")
    paths = []
    for index, value in enumerate(values, start=1):
        path = _extract_path_value(value)
        if not path:
            raise Exception(f"PLUGIN_ERROR:::音频{index}没有可用路径，为避免引用错位已停止提交")
        kind = _reference_media_kind(value)
        if kind == "image":
            raise Exception(
                f"PLUGIN_ERROR:::音频{index}实际是图片（{path}），"
                "宿主素材类型与音频槽位不一致，为避免引用错位已停止提交"
            )
        if kind == "video":
            raise Exception(
                f"PLUGIN_ERROR:::音频{index}实际是视频（{path}），"
                "宿主素材类型与音频槽位不一致，为避免引用错位已停止提交"
            )
        paths.append(path)
    return paths


def _prompt_reference_slots(prompt):
    """提取提示词中明确出现的图片/音频槽位（槽位编号从 1 开始）。"""
    text = str(prompt or "")
    image_patterns = (
        r"<Picture\s*([1-9]\d*)\s*>",
        r"@?参考图\s*([1-9]\d*)",
        r"@?图片\s*([1-9]\d*)",
        r"(?<![\u4e00-\u9fffA-Za-z0-9])@?图\s*([1-9]\d*)",
    )
    audio_patterns = (
        r"<Audio\s*([1-9]\d*)\s*>",
        r"@?参考音频\s*([1-9]\d*)",
        r"@?音频\s*([1-9]\d*)",
    )

    def collect(patterns):
        slots = set()
        for pattern in patterns:
            slots.update(int(match.group(1)) for match in re.finditer(pattern, text, flags=re.IGNORECASE))
        return sorted(slots)

    return collect(image_patterns), collect(audio_patterns)


def _payload_slot_count(value):
    if isinstance(value, (list, tuple)):
        return len(value)
    return 1 if value not in (None, "") else 0


def _payload_slot_values(value):
    """把单值/数组平铺字段统一成保持原顺序的槽位数组。"""
    if isinstance(value, (list, tuple)):
        return list(value)
    if value in (None, ""):
        return []
    return [value]


def _prompt_reference_mentions(prompt, explicit_only=False):
    """按出现位置提取提示词中的图片/视频/音频槽位引用。

    ``explicit_only`` 只保留平台会按顺序解释的显式占位（``@图片N`` /
    ``<PictureN>`` 等）；普通的「图1是角色」只用于槽位存在性校验，
    不应被当成跨媒体排序指令。
    """
    text = str(prompt or "")
    if explicit_only:
        patterns = (
            ("image", re.compile(r"<Picture\s*([1-9]\d*)\s*>", re.IGNORECASE)),
            ("video", re.compile(r"<Video\s*([1-9]\d*)\s*>", re.IGNORECASE)),
            ("audio", re.compile(r"<Audio\s*([1-9]\d*)\s*>", re.IGNORECASE)),
            ("image", re.compile(r"@(?:参考图|图片|图)\s*([1-9]\d*)", re.IGNORECASE)),
            ("video", re.compile(r"@(?:参考视频|视频)\s*([1-9]\d*)", re.IGNORECASE)),
            ("audio", re.compile(r"@(?:参考音频|音频)\s*([1-9]\d*)", re.IGNORECASE)),
        )
    else:
        patterns = (
            ("image", re.compile(r"<Picture\s*([1-9]\d*)\s*>", re.IGNORECASE)),
            ("video", re.compile(r"<Video\s*([1-9]\d*)\s*>", re.IGNORECASE)),
            ("audio", re.compile(r"<Audio\s*([1-9]\d*)\s*>", re.IGNORECASE)),
            ("image", re.compile(r"@?(?:参考图|图片|图)\s*([1-9]\d*)", re.IGNORECASE)),
            ("video", re.compile(r"@?(?:参考视频|视频)\s*([1-9]\d*)", re.IGNORECASE)),
            ("audio", re.compile(r"@?(?:参考音频|音频)\s*([1-9]\d*)", re.IGNORECASE)),
        )
    matches = []
    for kind, pattern in patterns:
        for match in pattern.finditer(text):
            matches.append((match.start(), match.end(), kind, int(match.group(1))))

    # 「参考图1」同时可能被「图1」匹配；同一位置只保留最长的完整 token。
    matches.sort(key=lambda item: (item[0], -(item[1] - item[0]), item[2], item[3]))
    selected = []
    for item in matches:
        if any(item[0] < existing[1] and existing[0] < item[1] for existing in selected):
            continue
        selected.append(item)
    selected.sort(key=lambda item: item[0])
    return [(kind, slot) for _, _, kind, slot in selected]


def _validate_prompt_media_order(prompt):
    """
    兼容「图1 / 图片1 / 音频1」以及带 @ 的写法。

    提示词可能先描述图2再描述图1，编号本身仍然是明确绑定，不应因为
    自然语言描述顺序而拦截；真正需要校验的是编号是否存在对应槽位。
    """
    return _prompt_reference_mentions(prompt)


def _build_dashscope_media(payload, prompt=""):
    """
    从已校验的平铺素材字段构造官方 DashScope input.media 数组。

    同一类型仍严格按槽位 1、2、3 排列；只有 prompt 使用显式 ``@`` 或
    ``<PictureN>`` 一类占位时，才保留跨类型引用顺序。普通自然语言编号
    （如「图1是角色」）不会改变 media 顺序。
    """
    type_map = {
        "image": "reference_image",
        "video": "reference_video",
        "audio": "reference_audio",
    }
    groups = {}
    for kind in ("image", "video", "audio"):
        groups[kind] = []
        for slot, value in enumerate(
            _payload_slot_values(payload.get(f"reference_{kind}")), start=1
        ):
            text = str(value or "").strip()
            if not text:
                raise Exception(
                    f"PLUGIN_ERROR:::{kind}素材{slot}为空，无法建立稳定的 media 槽位"
                )
            groups[kind].append(
                {"type": type_map[kind], "url": text, "_slot": slot, "_kind": kind}
            )

    ordered_mentions = _prompt_reference_mentions(prompt, explicit_only=True)
    safe_kind = {}
    for kind in ("image", "video", "audio"):
        sequence = []
        for mention_kind, slot in ordered_mentions:
            if mention_kind == kind and slot not in sequence:
                sequence.append(slot)
        safe_kind[kind] = bool(
            sequence
            and sequence[0] == 1
            and sequence == list(range(1, max(sequence) + 1))
            and max(sequence) <= len(groups[kind])
        )

    media = []
    used = set()
    if ordered_mentions and any(safe_kind.values()):
        for kind, slot in ordered_mentions:
            if not safe_kind.get(kind):
                continue
            key = (kind, slot)
            if key in used:
                continue
            item = groups[kind][slot - 1]
            media.append(item)
            used.add(key)

    for kind in ("image", "video", "audio"):
        for item in groups[kind]:
            key = (kind, item["_slot"])
            if key not in used:
                media.append(item)

    # 首尾帧只有在没有普通参考素材时才会保留（上游规则已在调用方校验）。
    first_frame = str(payload.get("first_frame") or "").strip()
    last_frame = str(payload.get("last_frame") or "").strip()
    if first_frame:
        media.append({"type": "first_frame", "url": first_frame})
    if last_frame:
        media.append({"type": "last_frame", "url": last_frame})
    for item in media:
        item.pop("_slot", None)
        item.pop("_kind", None)
    return media


def _build_dashscope_request_body(payload, media):
    """构造网关文档 3.2 要求的 DashScope 风格请求体。"""
    input_payload = {"prompt": payload.get("prompt", "")}
    if media:
        input_payload["media"] = media
    parameters = {
        "duration": payload.get("duration"),
        "resolution": str(payload.get("resolution") or "720p").upper(),
        "ratio": payload.get("ratio"),
    }
    return {
        "model": payload.get("model"),
        "input": input_payload,
        "parameters": parameters,
    }


def _validate_dashscope_media(payload, media):
    """确保最终 media 数组与冻结后的各类型槽位逐项一致。"""
    expected = {
        "reference_image": _payload_slot_values(payload.get("reference_image")),
        "reference_video": _payload_slot_values(payload.get("reference_video")),
        "reference_audio": _payload_slot_values(payload.get("reference_audio")),
    }
    actual = {key: [] for key in expected}
    seen = set()
    for item in media:
        if not isinstance(item, dict):
            raise Exception("PLUGIN_ERROR:::最终 media 数组包含非法条目，已停止提交")
        item_type = str(item.get("type") or "").strip()
        url = str(item.get("url") or "").strip()
        if item_type in actual:
            actual[item_type].append(url)
        if not url:
            raise Exception("PLUGIN_ERROR:::最终 media 数组存在空 URL，已停止提交")
        identity = _reference_identity(url)
        if identity in seen:
            raise Exception(
                "PLUGIN_ERROR:::最终 media 数组存在重复素材 URL；"
                "平台去重会造成引用槽位前移，已停止提交"
            )
        seen.add(identity)

    mismatches = []
    for key in expected:
        if actual[key] != [str(value or "").strip() for value in expected[key]]:
            mismatches.append(
                f"{key}: 计划 {expected[key]} / media {actual[key]}"
            )
    if mismatches:
        raise Exception(
            "PLUGIN_ERROR:::最终 media 数组与素材槽位不一致："
            + "；".join(mismatches)
        )


def _validate_prompt_reference_slots(prompt, payload):
    """提交前核对提示词编号与最终 API 数组，阻止 WAN3_API_MENTIONS_INVALID。"""
    _validate_prompt_media_order(prompt)
    image_slots, audio_slots = _prompt_reference_slots(prompt)
    video_slots = sorted(
        slot for kind, slot in _prompt_reference_mentions(prompt) if kind == "video"
    )
    image_count = _payload_slot_count(payload.get("reference_image"))
    video_count = _payload_slot_count(payload.get("reference_video"))
    audio_count = _payload_slot_count(payload.get("reference_audio"))
    missing = []
    if image_slots and max(image_slots) > image_count:
        missing.append(f"图片{max(image_slots)}（当前只有 {image_count} 个参考图槽位）")
    if video_slots and max(video_slots) > video_count:
        missing.append(f"视频{max(video_slots)}（当前只有 {video_count} 个参考视频槽位）")
    if audio_slots and max(audio_slots) > audio_count:
        missing.append(f"音频{max(audio_slots)}（当前只有 {audio_count} 个参考音频槽位）")
    if missing:
        raise Exception(
            "PLUGIN_ERROR:::WAN3_API_MENTIONS_INVALID：提示词引用了不存在的素材槽位："
            + "、".join(missing)
            + "。请检查 reference_items / reference_images / reference_audios 的编号"
        )


def _log_reference_mapping(kind, sources, urls):
    """打印最终槽位映射，方便从宿主日志核对上传结果。"""
    label = "图片" if kind == "image" else "音频"
    for index, (source, url) in enumerate(zip(sources, urls), start=1):
        print(
            f"[素材映射] {label}{index} -> {_preview_media(_extract_path_value(source))}"
            f" -> {_preview_media(url)}"
        )


# ---------------------------------------------------------------- 主生成

def generate(context):
    """
    宿主入口：完整堆栈兜底。任何未预期异常都打印 traceback，
    并以 PLUGIN_ERROR 形式抛出，避免宿主把任务误判为「生成失败」。
    """
    try:
        return _generate_impl(context)
    except Exception as exc:
        import traceback
        traceback.print_exc()
        if str(exc).startswith("PLUGIN_ERROR:::"):
            raise
        raise Exception(f"PLUGIN_ERROR:::插件内部异常: {exc}") from exc


def _generate_impl(context):
    print("\n" + "=" * 60)
    print("[AIGC创作站 Plugin] 开始生成视频")
    print("=" * 60)

    prompt = (context.get("prompt") or "").strip()
    output_dir = context.get("project_path") or context.get("output_dir") or "."
    params = _default_params.copy()
    params.update(context.get("plugin_params") or get_params())
    cb = context.get("progress_callback")

    _log_media_sources(context)

    api_key = (params.get("api_key") or "").strip()
    if not api_key:
        raise Exception("PLUGIN_ERROR:::API Key 未设置，请在插件设置中配置")

    base_url = _normalize_base_url(params.get("base_url", _DEFAULT_BASE_URL))
    model = (params.get("model") or "").strip()
    if not model:
        raise Exception("PLUGIN_ERROR:::未选择视频模型，请在插件设置中选择模型（可点击「刷新」重新加载）")

    generation_mode = params.get("generation_mode", MODE_AUTO)
    resolution = (params.get("resolution") or "720p").strip().lower()
    ratio = (params.get("ratio") or "16:9").strip()
    timeout = int(params.get("timeout") or 900)
    poll_interval = max(MIN_POLL_INTERVAL, int(params.get("poll_interval") or MIN_POLL_INTERVAL))
    max_poll_attempts = int(params.get("max_poll_attempts") or 300)

    # 时长：优先取分镜时长，其次取插件设置
    # 官方万相3.0：无视频输入时 duration 取 [2, 30]（默认 5，-1 为智能时长）；
    # 有参考视频时「输入视频总时长 + 输出时长 ≤30」。超范围按边界取值并提示，避免提交被拒。
    scene_duration = context.get("scene_duration")
    try:
        duration = int(scene_duration) if scene_duration else int(params.get("duration") or _DEFAULT_DURATION)
    except (TypeError, ValueError):
        duration = int(_DEFAULT_DURATION)
    raw_duration = duration
    duration = max(MIN_DURATION, min(MAX_DURATION, duration))
    if duration != raw_duration:
        print(f"[时长] 分镜时长 {raw_duration}s 超出 Wan3.0 支持范围（{MIN_DURATION}-{MAX_DURATION}s），已调整为 {duration}s")

    # ---- 参考素材解析（首尾帧使用官方独立字段）----
    manual_ref_url = (params.get("reference_image_url") or "").strip()
    reference_image_mode = params.get("reference_image_mode", REF_MODE_SINGLE)
    if reference_image_mode not in REFERENCE_MODES:
        reference_image_mode = REF_MODE_SINGLE

    reference_paths = _collect_image_references(context)
    reference_videos = _collect_video_references(context, timeout=timeout)
    first_frame_path = context.get("first_frame_path")
    last_frame_path = context.get("end_frame_path") or context.get("last_frame_path")

    # 手动填了参考图 URL 时视为图生视频
    if manual_ref_url and not manual_ref_url.startswith(("http://", "https://", "data:image/")):
        print(f"[参考图] 手动填写的 URL 非法，忽略: {manual_ref_url}")
        manual_ref_url = ""

    mode = generation_mode
    if mode == MODE_AUTO:
        mode = MODE_IMAGE_TO_VIDEO if (manual_ref_url or reference_paths or first_frame_path or last_frame_path or reference_videos) else MODE_TEXT_TO_VIDEO
        print(f"自动判定模式: {mode}")

    print(f"提示词: {prompt}")
    print(f"模型: {model}")
    print(f"生成模式: {mode}")
    print(f"时长: {duration}s, 分辨率: {resolution}, 宽高比: {ratio}")
    print(f"API Key: {'已设置(' + str(len(api_key)) + '字符)' if api_key else '未设置'}")

    # ---- 在任何图片预处理 / 音频上传前冻结本次请求的槽位计划 ----
    # 图片和音频各自独立编号；prompt 后面无论以什么顺序出现，都只引用这里的槽位。
    audio_sources = []
    if params.get("auto_storyboard_audio", True):
        audio_sources = _collect_storyboard_audios(context)
    manual_text = (params.get("audio_reference_url") or "").strip()
    if params.get("enable_audio_reference"):
        if not manual_text:
            raise Exception("PLUGIN_ERROR:::已开启音频参考但未填写音频 URL")
        audio_sources.extend(
            part.strip() for part in re.split(r"[\n,;]+", manual_text) if part.strip()
        )

    image_plan_sources = []
    if mode == MODE_IMAGE_TO_VIDEO:
        image_plan_sources = [manual_ref_url] if manual_ref_url else reference_paths
    reference_plan = _build_reference_slot_plan(image_plan_sources, audio_sources)
    _log_reference_slot_plan(reference_plan)

    reference_image = None
    if mode == MODE_IMAGE_TO_VIDEO:
        if cb:
            cb("准备参考图")
        if manual_ref_url:
            if reference_paths:
                raise Exception(
                    "PLUGIN_ERROR:::同时检测到手动参考图 URL 和分镜参考图；"
                    "提示词编号只能对应一套素材，为避免引用错位请只保留一种来源"
                )
            print("模式: 图生视频（使用手动填写的参考图 URL）")
            reference_image = manual_ref_url
        else:
            print(f"模式: 参考素材生视频（普通参考图 {len(reference_paths)} 张）")
            reference_image_urls = []
            for index, ref_path in enumerate(reference_paths, start=1):
                resolved = _resolve_reference_image_url(ref_path)
                if not resolved:
                    raise Exception(
                        f"PLUGIN_ERROR:::图片{index}无法转换为 API 可用 URL（{ref_path}），"
                        "为避免后续图片槽位前移已停止提交"
                    )
                reference_image_urls.append(resolved)
            if reference_image_urls:
                # 只要提示词里可能引用多个编号，就必须使用数组；为保持单图/多图
                # 语义一致，这里对所有自动收集的参考图统一使用数组形式。
                if reference_image_mode != REF_MODE_ARRAY:
                    print(
                        f"[参考图] reference_image_mode={reference_image_mode} 会破坏槽位绑定，"
                        "已强制改为数组形式"
                    )
                reference_image = reference_image_urls
                _log_reference_mapping("image", reference_paths, reference_image_urls)
        print(f"参考图: {_preview_media(reference_image)}")
    else:
        print("模式: 文生视频")

    payload = {
        "model": model,
        "prompt": prompt,
        "duration": duration,
        "resolution": resolution,
        "ratio": ratio,
    }
    if reference_image is not None and reference_image != "":
        payload["reference_image"] = reference_image
    if first_frame_path:
        payload["first_frame"] = _resolve_reference_image_url(first_frame_path)
    if last_frame_path:
        payload["last_frame"] = _resolve_reference_image_url(last_frame_path)
    if reference_videos:
        payload["reference_video"] = reference_videos

    # ---- 音频参考（官方 Wan3.0 reference_audio：最多 5 段、单段 1-15 秒、总长 ≤15 秒、
    #       WAV/MP3、≤15MB；多说话人时多个 URL，prompt 用“音频1”“音频2”引用）----
    # audio_sources 已在上方冻结；这里仅按冻结顺序处理，不再重新收集素材。
    if audio_sources:
        # 单段可用额度 = min(官方 15 秒, 本镜输出时长)：视频只有 duration 秒，更长的参考音频没有意义
        audio_urls = _prepare_audio_references(
            audio_sources,
            timeout=params.get("timeout") or 60,
            segment_limit=min(MAX_AUDIO_TOTAL_SECONDS, duration),
        )
        if len(audio_urls) != len(audio_sources):
            raise Exception(
                "PLUGIN_ERROR:::参考音频处理后槽位数量发生变化，"
                "为避免提示词引用错位已停止提交"
            )
        if audio_urls:
            payload["reference_audio"] = audio_urls
            _log_reference_mapping("audio", audio_sources, audio_urls)
            print(f"音频参考(reference_audio): {audio_urls}")

    # ---- 官方万相3.0「素材组合」规则：first_frame / last_frame 与 reference_image /
    #      reference_video / reference_audio 互斥，混用会被上游拒绝（任务直接失败）。
    #      本插件以「参考图」为主流程、首尾帧很少用，因此两者同时出现时保留参考素材、
    #      丢弃首/尾帧，避免整条分镜因为组合非法而报错。----
    if (payload.get("first_frame") or payload.get("last_frame")) and any(
        payload.get(key) for key in ("reference_image", "reference_video", "reference_audio")
    ):
        dropped = [key for key in ("first_frame", "last_frame") if payload.pop(key, None)]
        print(
            "[WARN] 首帧/尾帧与参考素材互斥（官方万相3.0 规则），本插件以参考素材为主，"
            f"已忽略: {'、'.join(dropped)}（如需用首尾帧，请不要同时挂参考图/视频/音频）"
        )

    _validate_reference_slot_plan(reference_plan, payload)
    _validate_prompt_reference_slots(prompt, payload)

    # 有参考素材时改走官方 DashScope 兼容路径，并把所有素材收敛到一个
    # 明确的 input.media 数组；纯文生视频继续使用原来的 OpenAI 风格路径。
    media_items = _build_dashscope_media(payload, prompt)
    _validate_dashscope_media(payload, media_items)
    use_dashscope = bool(media_items)
    request_body = (
        _build_dashscope_request_body(payload, media_items)
        if use_dashscope
        else payload
    )

    if len(prompt) > MAX_PROMPT_CHARS:
        print(
            f"[WARN] 提示词 {len(prompt)} 字符超过网关上限 {MAX_PROMPT_CHARS}"
            "（上游万相3.0 为 20000 字符），网关会返回 WAN3_API_PROMPT_INVALID，请精简分镜提示词"
        )

    # 幂等键：网关支持 Idempotency-Key（1-128 位 ASCII），同一次生成的退避重试复用同一个值
    idempotency_key = "zz-" + uuid.uuid4().hex
    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
        "Idempotency-Key": idempotency_key,
    }
    if use_dashscope:
        # DashScope 兼容接口只支持异步提交，缺少此头会被当成同步调用拒绝。
        headers["X-DashScope-Async"] = "enable"
    endpoint = _api_url(
        base_url,
        _DASHSCOPE_VIDEO_GENERATIONS_PATH if use_dashscope else _VIDEO_GENERATIONS_PATH,
    )

    if cb:
        cb("提交任务")
    print(f"请求端点: {endpoint}")
    print(f"请求协议: {'DashScope input.media' if use_dashscope else 'OpenAI 兼容'}")
    print(f"请求体: {json.dumps(request_body, ensure_ascii=False)[:1200]}")

    # ---- 提交任务（受理后进入轮询，绝不重复提交，避免重复任务扣双倍积分；
    #       例外仅限网关明确「未受理、不扣积分」的繁忙场景：素材并发超限(429)----
    task_id = None
    submit_started_ms = int(time.time() * 1000)
    busy_retry = 0
    has_media = any(
        payload.get(key)
        for key in ("reference_image", "first_frame", "last_frame", "reference_video", "reference_audio")
    )
    queue_deadline = time.time() + SUBMIT_QUEUE_DEADLINE_SECONDS
    while True:
        # ---- 本地素材导入排队：同时只提交 IMPORT_CONCURRENCY 个带素材的分镜 ----
        held_slot = False
        if has_media:
            held_slot = _acquire_import_slot(queue_deadline, cb)
        try:
            response = requests.post(endpoint, headers=headers, json=request_body, timeout=timeout)
        except requests.exceptions.RequestException as exc:
            if held_slot:
                _IMPORT_SEMAPHORE.release()
            print(f"[WARN] 提交任务网络异常，开始从任务历史找回任务 ID: {exc}")
            task_id = _recover_submitted_task_id(
                base_url,
                api_key,
                payload,
                submit_started_ms,
                poll_interval=poll_interval,
            )
            if not task_id:
                raise Exception(
                    f"PLUGIN_ERROR:::提交任务网络异常: {exc}（已自动查询任务历史但未找到匹配任务。"
                    "请到「我的任务」确认任务状态，勿立即重复生成，以免重复扣积分）"
                ) from exc
            break

        if held_slot:
            _IMPORT_SEMAPHORE.release()

        # 网关繁忙/限流（429 等）：任务未被受理、不扣积分，可安全排队后重试
        if _is_submit_busy(response):
            if time.time() < queue_deadline:
                busy_retry += 1
                delay = min(2 ** min(busy_retry, 4) * 2, 30)
                print(
                    f"[WARN] {_submit_busy_reason(response)}，{delay}s 后重新提交"
                    f"（第 {busy_retry} 次，任务未受理、不扣积分）"
                )
                if cb:
                    cb("排队中")
                time.sleep(delay)
                continue
            print(
                f"[WARN] {_submit_busy_reason(response)}：排队已超过 "
                f"{SUBMIT_QUEUE_DEADLINE_SECONDS}s，不再等待"
            )

        break

    if not task_id:
        # 200/202 均视为提交成功（202 Accepted = 任务已受理）
        if response.status_code not in (200, 202):
            if response.status_code == 504:
                task_id = _recover_submitted_task_id(
                    base_url,
                    api_key,
                    payload,
                    submit_started_ms,
                    poll_interval=poll_interval,
                )
                if not task_id:
                    raise Exception(
                        "PLUGIN_ERROR:::提交网关超时（504），已自动查询任务历史但未找到匹配任务。"
                        "请到「我的任务」确认任务状态，勿立即重复生成，以免重复扣积分"
                    )
            else:
                raise Exception(_build_submit_error(response))

        if not task_id:
            try:
                result = response.json()
            except ValueError:
                task_id = _recover_submitted_task_id(
                    base_url,
                    api_key,
                    payload,
                    submit_started_ms,
                    poll_interval=poll_interval,
                )
                if not task_id:
                    raise Exception(
                        "PLUGIN_ERROR:::提交响应非 JSON，且未能从任务历史找回任务 ID。"
                        f"API 返回原文: {response.text}"
                    )
            if not task_id:
                task_id = _extract_task_id(result)
                if not task_id:
                    task_id = _recover_submitted_task_id(
                        base_url,
                        api_key,
                        payload,
                        submit_started_ms,
                        poll_interval=poll_interval,
                    )
                if not task_id:
                    raise Exception("PLUGIN_ERROR:::API 响应中缺少任务 ID，且任务历史中未找到匹配任务")
                cost = result.get("costPoints")
                remaining = result.get("remainingPoints")
                if cost is not None or remaining is not None:
                    print(f"预估消耗积分: {cost}，剩余积分: {remaining}")
    print(f"任务 ID: {task_id}")
    if cb:
        cb("排队中")

    # ---- 轮询任务状态 ----
    poll_url = _api_url(
        base_url,
        (
            _DASHSCOPE_VIDEO_STATUS_PATH
            if use_dashscope
            else _VIDEO_STATUS_PATH
        ).format(task_id=task_id),
    )
    attempts = 0
    video_urls = []
    last_poll_error = None
    failed_streak = 0
    poll_delay = poll_interval
    while attempts < max_poll_attempts:
        time.sleep(poll_delay)
        attempts += 1
        try:
            response = requests.get(
                poll_url,
                headers={"Authorization": f"Bearer {api_key}"},
                timeout=timeout,
            )
            if response.status_code != 200:
                last_poll_error = f"HTTP {response.status_code}: {response.text[:200]}"
                # 429 = 网关 IP 限流（约 20 次/分钟）：放大轮询间隔，避免雪上加霜
                if response.status_code == 429:
                    poll_delay = min(poll_delay * 2, MAX_POLL_INTERVAL)
                    print(f"[WARN] 轮询被网关限流（429），下次间隔放宽到 {poll_delay}s")
                print(f"状态查询失败，将继续轮询: {last_poll_error}")
                continue

            try:
                data = response.json()
            except ValueError:
                last_poll_error = f"状态查询返回非 JSON: {response.text[:200]}"
                print(f"{last_poll_error}，将继续轮询")
                continue
            poll_delay = poll_interval
            status = _extract_task_status(data)

            if status in {"success", "succeeded", "completed", "complete", "done"}:
                failed_streak = 0
                candidates = _extract_video_url_candidates(data)
                if not candidates:
                    last_poll_error = "网关报告成功但暂未返回视频链接"
                    print(f"{last_poll_error}，将继续轮询")
                    continue
                video_urls = candidates
                if len(video_urls) > 1:
                    print(f"视频生成成功: {video_urls[0]}（另有 {len(video_urls) - 1} 条备用直链可回退）")
                else:
                    print(f"视频生成成功: {video_urls[0]}")
                break

            if status in {"refunded", "refund", "refunded_failed"}:
                reason = _extract_fail_reason(data)
                print(f"[WARN] 任务已退款，生成失败: {reason}")
                raise Exception("PLUGIN_ERROR:::生成失败，已退款")

            if status in {"failed", "failure", "fail", "error"}:
                reason = _extract_fail_reason(data)
                raise Exception(f"PLUGIN_ERROR:::视频任务失败: {_describe_api_error(reason)}")

            failed_streak = 0

            mins, secs = divmod(attempts * poll_interval, 60)
            print(
                f"[{attempts}/{max_poll_attempts}] 状态: {status}，已等待 {int(mins):02d}:{int(secs):02d}",
                end="\r",
            )
            if cb:
                if status in {"processing", "running", "in_progress"}:
                    cb("生成中")
                elif status in {"pending", "queued", "submitted", "waiting"}:
                    cb("排队中")
        except requests.exceptions.RequestException as exc:
            last_poll_error = f"状态查询网络异常: {exc}"
            print(f"状态查询网络异常，将继续轮询: {exc}")
        except Exception as exc:
            if str(exc).startswith("PLUGIN_ERROR:::"):
                raise
            # 任务实际仍在网关侧生成：查询阶段的意外异常只记录，不中断、不误判失败
            last_poll_error = f"状态查询异常: {exc}"
            import traceback
            traceback.print_exc()
            print(f"状态查询异常，将继续轮询: {exc}")

    if not video_urls:
        error_suffix = f" 最近一次查询异常: {last_poll_error}。" if last_poll_error else ""
        raise Exception(
            f"PLUGIN_ERROR:::等待生成超时（已查询 {max_poll_attempts} 次），视频尚未完成。"
            f"{error_suffix}"
            "可在高级设置中增大「最长等待」后重试"
        )

    # ---- 下载并校验（主直链失败时回退到网关备份副本 backupUrl）----
    if cb:
        cb("下载中", 95)

    content = None
    download_errors = []
    for index, candidate in enumerate(video_urls, start=1):
        print(f"正在下载视频: {candidate}")
        try:
            content = _download_video_content(candidate, base_url, api_key, timeout)
            break
        except Exception as exc:
            download_errors.append(f"第 {index} 条直链 {exc}")
            if index < len(video_urls):
                print(f"[WARN] 下载失败，改用备用直链重试: {exc}")
            content = None

    if content is None:
        raise Exception("PLUGIN_ERROR:::下载视频失败: " + "；".join(download_errors))
    if not content or len(content) < 1024:
        raise Exception("PLUGIN_ERROR:::下载结果为空或文件过小，不是有效视频")
    if not _looks_like_video(content):
        raise Exception("PLUGIN_ERROR:::下载内容不是有效视频（网关可能返回了错误页），请重试")

    # ---- 按宿主规范命名并落盘 ----
    viewer_index = int(context.get("viewer_index", 0))
    unique_name = context.get("unique_name", "unknown")
    generation_round = int(context.get("generation_round", 0))
    positions = context.get("output_position") or [0]
    if isinstance(positions, list) and positions:
        position = positions[0]
    else:
        position = 0
    filename = f"{viewer_index:04d}_{unique_name}_{generation_round}_{position}.mp4"
    output_path = os.path.abspath(os.path.join(output_dir, filename))

    with open(output_path, "wb") as file_obj:
        file_obj.write(content)

    size_mb = len(content) / (1024 * 1024)
    print(f"视频已保存: {output_path}")
    print(f"文件大小: {size_mb:.2f} MB")
    print("=" * 60)

    if cb:
        cb("生成中", 100)
    return [output_path]
