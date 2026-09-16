# -*- coding: utf-8 -*-
"""
AIGC 创作站 · 生视频插件（youzan666.vip AIGC 网关）

对接 OpenAI 兼容协议（见《API 接入文档 · AIGC 创作站》）：
  GET  {base}/v1/models                    拉取当前可用模型列表（动态，勿写死模型 ID）
  POST {base}/v1/videos/generations        提交视频生成任务（立即返回任务 ID）
  GET  {base}/v1/videos/{taskId}           轮询任务状态 / 结果

支持：
- 文生视频 / 图生视频（自动按参考图判断，也可手动指定）
- 参考图：http(s) URL 直接透传；本地图片转为接口支持的 Base64 数据 URL
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
_PLUGIN_VERSION = "1.1.6"
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
    """统一为站点根地址（去掉末尾 / 与 /v1）。"""
    text = str(url or "").strip() or _DEFAULT_BASE_URL
    text = text.rstrip("/")
    if text.endswith("/v1"):
        text = text[:-3].rstrip("/")
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

# PNG 参考图统一拒绝：不做静默转码，直接让用户先转成 JPG
_PNG_REFERENCE_HINT = (
    "不支持 PNG 格式，请先转成 JPG 再提交"
    "（带透明通道的图请先合上白色或其他实底背景再转 JPG）；"
    "也可以在高级设置的「参考图 URL」中填写 JPG 公网直链。"
)


def _build_submit_error(response):
    """把提交失败转成 PLUGIN_ERROR；参考素材被拒时附上排查提示。"""
    error_text = _extract_api_error(response)
    if response.status_code == 400 and any(keyword in error_text for keyword in _REFERENCE_REJECTION_KEYWORDS):
        error_text += (
            "（排查提示：多为参考图内容或尺寸触发上游安全校验。"
            "可先换一张干净的图试生成，或改用文生视频确认模型可用；"
            "插件已对参考图做限尺寸预处理，但 PNG 需自行先转成 JPG）"
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
        "description": "通过 youzan666.vip AIGC 网关调用视频模型生成视频，支持文生视频 / 图生视频（参考图），模型列表动态刷新。",
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
    # 宿主传入的是 0 基 {0: 路径, 1: ...}，包一层便于统一读取
    if all(isinstance(key, int) for key in reference_images.keys()):
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
        return str(value.get("path") or "").strip()
    return str(value or "").strip()


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
    收集普通参考图（去重，上限 max_count）。首尾帧需走各自的官方字段，
    因此不混入 reference_image。
    """
    reference_images = _normalize_reference_images(context.get("reference_images", {}))
    paths = []
    seen = set()

    def add(path):
        if isinstance(path, dict):
            media_type = str(path.get("media_type") or "").lower()
            inner = str(path.get("path") or "").strip()
            if media_type and "audio" in media_type:
                print(f"[WARN] 跳过非图片参考: {inner or path}（音频走音频参考）")
                return
            path = inner
        path = _extract_path_value(path)
        if not path or len(paths) >= max_count:
            return
        if _is_audio_file(path):
            print(f"[WARN] 跳过疑似音频参考: {path}（音频走音频参考，不当作参考图上传）")
            return
        key = str(path)
        if key in seen:
            return
        seen.add(key)
        paths.append(path)

    ref_map = reference_images.get("参考图片MAP") or {}
    for index in sorted(ref_map.keys()):
        add(ref_map[index])
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


def _convert_image_to_jpeg(image, max_side=2048, quality=92, max_bytes=8 * 1024 * 1024):
    """把已打开的 PIL 图片统一转成 JPEG bytes：去 alpha、限最长边、压体积。"""
    import io
    from PIL import Image

    if image.mode not in ("RGB", "L"):
        image = image.convert("RGB")
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
    参考图预处理：非 PNG 图片统一转 JPEG、限最长边、压体积，返回临时 .jpg 路径。

    上游安全校验对参考图的格式 / 尺寸 / 体积较敏感，
    先规范化可排除「过大 / 非标准格式」导致的拒检。
    PNG 在进入本函数前就被 _resolve_reference_image_url 直接拒绝，此处不做静默转码。
    处理失败时返回原路径（由调用方决定是否放行）。
    """
    try:
        from PIL import Image

        image = Image.open(image_path)
        image.load()
        jpeg_bytes = _convert_image_to_jpeg(image, max_side=max_side, quality=quality, max_bytes=max_bytes)
        temp_path = f"{image_path}_preprocessed.jpg"
        with open(temp_path, "wb") as file_obj:
            file_obj.write(jpeg_bytes)
        print(f"[参考图] 已预处理: {image_path} -> {temp_path}（最长边 {max(image.size)}px, {len(jpeg_bytes) // 1024}KB）")
        return temp_path
    except Exception as exc:
        print(f"[参考图] 预处理失败: {exc}")
        return image_path


def _is_png_reference(image_path):
    """
    按真实文件内容判断是否 PNG，可识破把 .png 改名成 .jpg 的情况。
    无法识别格式时返回 False，交给后续预处理链路报错。
    """
    try:
        from PIL import Image

        with Image.open(image_path) as image:
            return (image.format or "").upper() == "PNG"
    except Exception:
        return False


def _resolve_reference_image_url(image_path):
    """
    将参考图转换为文档支持的值：公网 URL 原样透传；本地图片预处理后转
    data:image/jpeg;base64，避免上传到第三方公共图床。

    PNG 一律不处理、不转码，直接报错要求用户先转成 JPG。
    """
    if not image_path:
        return None
    text = str(image_path)
    if text.startswith(("http://", "https://")):
        return text
    if text.startswith("data:image/"):
        if "png" in text.split(",", 1)[0].lower():
            raise Exception(f"PLUGIN_ERROR:::参考图{_PNG_REFERENCE_HINT}")
        return text
    if not os.path.exists(text):
        print(f"[参考图] 文件不存在: {text}")
        return None
    if _is_png_reference(text):
        print(f"[参考图] 检测到 PNG 格式，已拒绝: {text}")
        raise Exception(
            f"PLUGIN_ERROR:::参考图「{os.path.basename(text)}」{_PNG_REFERENCE_HINT}"
        )
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
    · 按顺序累计总时长，某段会突破总上限时截断到剩余额度，剩余不足 1 秒才丢弃该段；
    · 公网 URL 音频无法探测/截断，原样保留（真超限由网关报错，插件会给出中文提示）。
    """
    urls = []
    used = 0.0
    for source in sources:
        text = str(source or "").strip()
        if not text or text in urls:
            continue
        if text.startswith(("http://", "https://")):
            if len(urls) < max_count:
                urls.append(text)
            continue
        if not os.path.exists(text):
            raise Exception(f"PLUGIN_ERROR:::音频参考 URL 非法或本地文件不存在: {text}")
        if len(urls) >= max_count:
            print(f"[WARN] 参考音频最多 {max_count} 段（官方限制），已忽略其余素材")
            break

        seconds = _probe_media_duration(text)
        keep = _audio_keep_seconds(seconds, used, segment_limit, max_total_seconds)
        name = os.path.basename(text)
        if keep is None:
            duration_text = f"{seconds:.1f}s" if seconds is not None else "未知"
            print(f"[WARN] 参考音频 {name} 已跳过（时长 {duration_text}，可用额度不足 {MIN_MEDIA_SECONDS}s）")
            continue

        upload_path = text
        if seconds is not None and seconds > keep + 0.05:
            print(f"[音频] {name} 时长 {seconds:.1f}s 超过本次可用 {keep:.1f}s，自动截断后再上传")
            upload_path = _trim_media_file(text, keep, timeout=timeout)
        url = _upload_media_to_uguu(upload_path, timeout=timeout)
        if url in urls:
            continue
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
    宿主分镜参考音频：context['reference_audios']（0 基 dict[int, str]，绝对路径）。
    字字动画「参考项·音频」就是从这里传给生成插件的（见 GENERATION_PLUGIN_DEV_GUIDE.md）。
    兜底：若宿主把音频混进了 reference_items / reference_images，也一并回收（去重）。
    """
    paths = []
    refs = context.get("reference_audios") or {}
    if isinstance(refs, dict):
        def _key(k):
            try:
                return int(k)
            except (TypeError, ValueError):
                return 0
        for _idx in sorted(refs.keys(), key=_key):
            text = str(refs[_idx] or "").strip()
            if text:
                paths.append(text)
    elif isinstance(refs, (list, tuple)):
        paths = [str(p or "").strip() for p in refs if str(p or "").strip()]

    # 兜底一：reference_items（list[dict]，含 media_type / path）
    items = context.get("reference_items") or []
    if isinstance(items, list):
        for item in items:
            if not isinstance(item, dict):
                continue
            media_type = str(item.get("media_type") or "").lower()
            item_path = _extract_path_value(item)
            if item_path and ("audio" in media_type or _is_audio_file(item_path)) \
                    and item_path not in paths:
                paths.append(item_path)

    # 兜底二：reference_images 里被宿主混放的音频（参考图链路已过滤，这里回收）
    img_refs = context.get("reference_images") or {}
    for _idx in (img_refs if isinstance(img_refs, dict) else {}):
        img_path = _extract_path_value(img_refs[_idx])
        if img_path and _is_audio_file(img_path) and img_path not in paths:
            paths.append(img_path)

    return paths


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

    reference_image = None
    if mode == MODE_IMAGE_TO_VIDEO:
        if cb:
            cb("准备参考图")
        if manual_ref_url:
            print("模式: 图生视频（使用手动填写的参考图 URL）")
            reference_image = manual_ref_url
        else:
            print(f"模式: 参考素材生视频（普通参考图 {len(reference_paths)} 张）")
            reference_image_urls = []
            for index, ref_path in enumerate(reference_paths, start=1):
                resolved = _resolve_reference_image_url(ref_path)
                if not resolved:
                    print(f"[参考图 {index}] 转 URL 失败，跳过: {ref_path}")
                    continue
                reference_image_urls.append(resolved)
            if reference_image_urls:
                if reference_image_mode == REF_MODE_ARRAY:
                    reference_image = reference_image_urls
                elif reference_image_mode == REF_MODE_COMMA:
                    reference_image = ",".join(reference_image_urls)
                else:
                    reference_image = reference_image_urls[0]
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
    # 来源一：分镜参考音频自动取用（宿主 context['reference_audios']，0 基独立编号；开关默认开）
    audio_sources = []
    if params.get("auto_storyboard_audio", True):
        audio_sources = _collect_storyboard_audios(context)
    # 来源二：设置页手动填写的公网音频 URL
    manual_text = (params.get("audio_reference_url") or "").strip()
    if params.get("enable_audio_reference"):
        if not manual_text:
            raise Exception("PLUGIN_ERROR:::已开启音频参考但未填写音频 URL")
        audio_sources.extend(re.split(r"[\n,;]+", manual_text))
    if audio_sources:
        # 单段可用额度 = min(官方 15 秒, 本镜输出时长)：视频只有 duration 秒，更长的参考音频没有意义
        audio_urls = _prepare_audio_references(
            audio_sources,
            timeout=params.get("timeout") or 60,
            segment_limit=min(MAX_AUDIO_TOTAL_SECONDS, duration),
        )
        if audio_urls:
            payload["reference_audio"] = audio_urls
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
    endpoint = _api_url(base_url, _VIDEO_GENERATIONS_PATH)

    if cb:
        cb("提交任务")
    print(f"请求端点: {endpoint}")
    print(f"请求体: {json.dumps(payload, ensure_ascii=False)[:500]}")

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
            response = requests.post(endpoint, headers=headers, json=payload, timeout=timeout)
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
                task_id = result.get("taskId") or result.get("id") or result.get("task_id")
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
    poll_url = _api_url(base_url, _VIDEO_STATUS_PATH.format(task_id=task_id))
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
            status = str(data.get("status") or "unknown").lower()

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
