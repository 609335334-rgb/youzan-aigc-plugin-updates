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
import time
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
_PLUGIN_VERSION = "1.1.0"

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
MAX_AUDIO_REFS = 5  # 官方 Wan3.0：参考音频最多 5 段、单段 1-15 秒、总长 ≤15 秒
MIN_POLL_INTERVAL = 10

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
    "update_manifest_url": "",
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


def _check_update_available():
    params = get_params()
    manifest_url = str(params.get("update_manifest_url") or "").strip()
    if not manifest_url:
        return {"ok": False, "error": "请先填写更新清单 URL"}
    try:
        response = requests.get(manifest_url, timeout=30)
        if response.status_code != 200:
            raise Exception(f"HTTP {response.status_code}")
        manifest = response.json()
    except Exception as exc:
        return {"ok": False, "error": f"拉取更新清单失败: {exc}"}

    plugins = manifest.get("plugins") if isinstance(manifest, dict) else None
    if not isinstance(plugins, list):
        return {"ok": False, "error": "manifest.json 格式错误：缺少 plugins"}
    remote = next((item for item in plugins if isinstance(item, dict) and item.get("plugin_id") == _PLUGIN_ID), None)
    if not remote:
        return {"ok": True, "has_update": False, "message": f"清单中未找到插件: {_PLUGIN_ID}"}
    remote_version = str(remote.get("version") or "").strip()
    if not remote_version:
        return {"ok": False, "error": "更新项缺少 version"}
    if not _is_newer_version(remote_version, _PLUGIN_VERSION):
        return {"ok": True, "has_update": False, "message": f"当前已是最新版（本地 {_PLUGIN_VERSION}，远端 {remote_version}）"}
    return {
        "ok": True,
        "has_update": True,
        "local_version": _PLUGIN_VERSION,
        "remote_version": remote_version,
        "changelog": str(remote.get("changelog") or "无"),
        "download_url": str(remote.get("download_url") or "").strip(),
        "sha256": str(remote.get("sha256") or "").strip().lower(),
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


def _execute_update(download_url, expected_sha256=""):
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
        target_dir = Path(_PLUGIN_FILE).parent
        backup = target_dir / f"main.py.bak.{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        shutil.copy2(_PLUGIN_FILE, backup)
        try:
            shutil.copy2(source_main, _PLUGIN_FILE)
            if package_path.suffix.lower() == ".zip":
                for item in source_dir.iterdir():
                    if item.name == "main.py":
                        continue
                    destination = target_dir / item.name
                    if item.is_dir():
                        if destination.exists():
                            shutil.rmtree(destination)
                        shutil.copytree(item, destination)
                    else:
                        shutil.copy2(item, destination)
        except Exception:
            shutil.copy2(backup, _PLUGIN_FILE)
            raise
        return {"ok": True, "message": f"插件已更新，已备份为 {backup.name}。请重启字字动画后生效。"}
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


def _recover_submitted_task_id(
    base_url,
    api_key,
    payload,
    submitted_at_ms,
    poll_interval=MIN_POLL_INTERVAL,
    max_attempts=12,
):
    """提交响应丢失后，从任务历史中找回本次请求的任务 ID；绝不重复提交。"""
    expected_prompt = str(payload.get("prompt") or "")
    expected_model = str(payload.get("model") or "")
    if not expected_prompt or not expected_model:
        return None

    history_url = _api_url(base_url, _TASKS_PATH)
    earliest_created_at = submitted_at_ms - 2 * 60 * 1000
    last_error = None

    for attempt in range(1, max_attempts + 1):
        candidates = []
        try:
            for page in range(1, 6):
                response = requests.get(
                    history_url,
                    headers={"Authorization": f"Bearer {api_key}"},
                    params={"page": page, "pageSize": 20},
                    timeout=30,
                )
                if response.status_code != 200:
                    last_error = _extract_api_error(response)
                    break

                data = response.json()
                tasks = data.get("tasks") or []
                for task in tasks:
                    if not isinstance(task, dict) or not task.get("id"):
                        continue
                    if str(task.get("type") or "").lower() != "video":
                        continue
                    task_model = str(task.get("model") or task.get("modelName") or "")
                    if task_model != expected_model or str(task.get("prompt") or "") != expected_prompt:
                        continue
                    try:
                        created_at = int(task.get("createdAt"))
                    except (TypeError, ValueError):
                        continue
                    if created_at < earliest_created_at:
                        continue
                    candidates.append((created_at, str(task["id"]), str(task.get("status") or "unknown")))

                if not data.get("hasMore"):
                    break

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
                    f"（状态: {status}，创建时间偏移: {delta_seconds:+.1f}s）"
                )
                return task_id
        except (requests.exceptions.RequestException, ValueError, TypeError) as exc:
            last_error = str(exc)

        if attempt < max_attempts:
            print(
                f"[提交恢复] 暂未找到匹配任务，将继续查询 "
                f"（{attempt}/{max_attempts}）: {last_error or '任务记录尚未同步'}"
            )
            time.sleep(max(MIN_POLL_INTERVAL, poll_interval))

    print(f"[提交恢复] 未能找回任务 ID: {last_error or '没有匹配的近期任务'}")
    return None


# 上游对参考素材做安全校验时的典型错误关键词
_REFERENCE_REJECTION_KEYWORDS = ("引用素材", "参考图", "安全校验", "素材未通过", "image check", "safety")


def _build_submit_error(response):
    """把提交失败转成 PLUGIN_ERROR；参考素材被拒时附上排查提示。"""
    error_text = _extract_api_error(response)
    if response.status_code == 400 and any(keyword in error_text for keyword in _REFERENCE_REJECTION_KEYWORDS):
        error_text += (
            "（排查提示：多为参考图内容或尺寸触发上游安全校验。"
            "可先换一张干净的图试生成，或改用文生视频确认模型可用；"
            "插件已自动对参考图做转 JPEG/限尺寸预处理）"
        )
    return f"PLUGIN_ERROR:::{error_text}"


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
        return _execute_update(data.get("download_url", ""), data.get("sha256", ""))
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
    print(f"[素材诊断] audio_path={context.get('audio_path')}")


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
    参考图预处理：统一转 JPEG、限最长边、压体积、去掉 alpha 通道，返回临时 .jpg 路径。

    上游安全校验对参考图的格式 / 尺寸 / 体积较敏感（部分模型不支持 PNG），
    先规范化可排除「PNG / 透明通道 / 过大 / 非标准格式」导致的拒检。
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


def _resolve_reference_image_url(image_path):
    """
    将参考图转换为文档支持的值：公网 URL 原样透传；本地图片预处理后转
    data:image/jpeg;base64，避免上传到第三方公共图床。
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


def _extract_video_url(data):
    """兼容网关不同版本的结果包装，提取视频直链。"""
    if not isinstance(data, dict):
        return None
    for key in ("url", "video_url", "videoUrl", "download_url", "downloadUrl"):
        value = data.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    for key in ("result", "data", "output", "video"):
        nested = data.get(key)
        if isinstance(nested, dict):
            url = _extract_video_url(nested)
            if url:
                return url
        elif isinstance(nested, list):
            for item in nested:
                url = _extract_video_url(item)
                if url:
                    return url
    return None


def _extract_fail_reason(data):
    """直接返回网关失败响应的完整原文（JSON 原样，不截断不改写）。"""
    try:
        return json.dumps(data, ensure_ascii=False)
    except Exception:
        return str(data)


def _probe_audio_duration(file_path):
    """用 ffmpeg 探测本地音频时长（秒，浮点）；失败返回 None（不阻断，仅告警）。"""
    import subprocess
    candidates = [
        r"E:\字字动画\resources\ffmpeg\bin\ffmpeg.exe",
        r"D:\字字动画\resources\ffmpeg\bin\ffmpeg.exe",
        "ffmpeg",
    ]
    for ff in candidates:
        try:
            proc = subprocess.run(
                [ff, "-i", file_path],
                capture_output=True, timeout=15,
            )
            # ffmpeg -i 不带输出参数时信息在 stderr
            text = (proc.stderr or b"").decode("utf-8", errors="ignore")
            import re
            m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", text)
            if m:
                h, mnt, sec = int(m.group(1)), int(m.group(2)), float(m.group(3))
                return h * 3600 + mnt * 60 + sec
        except Exception:
            continue
    return None


def _resolve_audio_reference_url(text, timeout=60):
    """公网音频 URL 原样透传；本地音频自动上传 Uguu。"""
    text = str(text or "").strip()
    if not text:
        return ""
    if text.startswith(("http://", "https://")):
        return text
    if os.path.exists(text):
        return _upload_media_to_uguu(text, timeout=timeout)
    raise Exception(f"PLUGIN_ERROR:::音频参考 URL 非法或本地文件不存在: {text}")


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
    # Wan3.0 官方支持范围 5-15 秒（实测 1 秒必 400 WAN3_PARAMETER_INVALID，2 秒可生成）；
    # 这里放宽为 2-15 秒并提示，超范围直接按边界取值，避免提交被网关拒。
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
        print(f"参考图: {reference_image}")
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
        audio_urls = []
        for chunk in audio_sources:
            chunk = str(chunk or "").strip()
            if not chunk:
                continue
            resolved = _resolve_audio_reference_url(chunk, timeout=params.get("timeout") or 60)
            if resolved and resolved not in audio_urls:
                audio_urls.append(resolved)
        if len(audio_urls) > MAX_AUDIO_REFS:
            print(f"[WARN] 音频参考最多 {MAX_AUDIO_REFS} 段（官方限制），已截断")
            audio_urls = audio_urls[:MAX_AUDIO_REFS]
        if audio_urls:
            payload["reference_audio"] = audio_urls
            print(f"音频参考(reference_audio): {audio_urls}")

    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
    }
    endpoint = _api_url(base_url, _VIDEO_GENERATIONS_PATH)

    if cb:
        cb("提交任务")
    print(f"请求端点: {endpoint}")
    print(f"请求体: {json.dumps(payload, ensure_ascii=False)[:500]}")

    # ---- 提交任务（只提交一次：受理后进入轮询，绝不重试提交，避免重复任务扣双倍积分；
    #       重试只允许发生在传参/素材上传阶段）----
    task_id = None
    submit_started_ms = int(time.time() * 1000)
    try:
        response = requests.post(endpoint, headers=headers, json=payload, timeout=timeout)
    except requests.exceptions.RequestException as exc:
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
    video_url = None
    last_poll_error = None
    failed_streak = 0
    while attempts < max_poll_attempts:
        time.sleep(poll_interval)
        attempts += 1
        try:
            response = requests.get(
                poll_url,
                headers={"Authorization": f"Bearer {api_key}"},
                timeout=timeout,
            )
            if response.status_code != 200:
                last_poll_error = f"HTTP {response.status_code}: {response.text[:200]}"
                print(f"状态查询失败，将继续轮询: {last_poll_error}")
                continue

            try:
                data = response.json()
            except ValueError:
                last_poll_error = f"状态查询返回非 JSON: {response.text[:200]}"
                print(f"{last_poll_error}，将继续轮询")
                continue
            status = str(data.get("status") or "unknown").lower()

            if status in {"success", "succeeded", "completed", "complete", "done"}:
                failed_streak = 0
                video_url = _extract_video_url(data)
                if not video_url:
                    last_poll_error = "网关报告成功但暂未返回视频链接"
                    print(f"{last_poll_error}，将继续轮询")
                    continue
                print(f"视频生成成功: {video_url}")
                break

            if status in {"refunded", "refund", "refunded_failed"}:
                reason = _extract_fail_reason(data)
                print(f"[WARN] 任务已退款，生成失败: {reason}")
                raise Exception("PLUGIN_ERROR:::生成失败，已退款")

            if status in {"failed", "failure", "fail", "error"}:
                reason = _extract_fail_reason(data)
                raise Exception(f"PLUGIN_ERROR:::视频任务失败: {reason}")

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

    if not video_url:
        error_suffix = f" 最近一次查询异常: {last_poll_error}。" if last_poll_error else ""
        raise Exception(
            f"PLUGIN_ERROR:::等待生成超时（已查询 {max_poll_attempts} 次），视频尚未完成。"
            f"{error_suffix}"
            "可在高级设置中增大「最长等待」后重试"
        )

    # ---- 下载并校验 ----
    if cb:
        cb("下载中", 95)
    print(f"正在下载视频: {video_url}")

    download_headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                      "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
        "Accept": "*/*",
    }
    if str(video_url).startswith(base_url):
        download_headers["Authorization"] = f"Bearer {api_key}"

    video_response = None
    video_error = None
    for dl_attempt in range(4):
        if dl_attempt > 0:
            time.sleep(2 ** dl_attempt)
        try:
            video_response = requests.get(video_url, headers=download_headers, timeout=timeout)
            if video_response.status_code in _RETRYABLE_STATUS_CODES:
                video_error = f"HTTP {video_response.status_code}"
                print(f"[WARN] 视频下载返回 {video_response.status_code}，{2 ** (dl_attempt + 1)}s 后重试（{dl_attempt + 1}/3）")
                continue
            if video_response.status_code != 200:
                raise Exception(f"PLUGIN_ERROR:::下载视频失败: HTTP {video_response.status_code} - {video_response.text}")
            break
        except requests.exceptions.RequestException as exc:
            video_error = str(exc)
            print(f"[WARN] 视频下载网络异常: {exc}，{2 ** (dl_attempt + 1)}s 后重试（{dl_attempt + 1}/3）")
    if video_response is None or video_response.status_code != 200:
        raise Exception(f"PLUGIN_ERROR:::下载视频失败（已重试 3 次）: {video_error}")

    content = video_response.content
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
