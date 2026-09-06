#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Quant push notification helper.

Only ntfy and Gotify are exposed in the Web UI, but the implementation keeps
ntfy/Gotify behavior compatible with the previously working push.py.
"""

from __future__ import annotations

import json
import logging
import os
import re
import time
from datetime import datetime
from email.header import Header
from pathlib import Path
from typing import Any, Dict, List, Tuple

import requests

BASE_DIR = Path(__file__).resolve().parent
PUSH_CONFIG_FILE = Path("/root/quant/push.conf")
PUSH_LOG_FILE = Path("/root/quant/push.log")
PUSH_DETAIL_LOG_FILE = Path("/root/quant/data/push_details.jsonl")
PUSH_LOG_KEEP_LINES = 30

PUSH_DEFAULTS: Dict[str, str] = {
    "PUSH_ENABLED": "yes",
    "PUSH_CHANNEL": "ntfy",
    "GOTIFY_URL": "https://sharq.eu.org:2084",
    "GOTIFY_TOKEN": "",
    "GOTIFY_PRIORITY": "10",
    "NTFY_URL": "http://127.0.0.1:8083",
    "NTFY_TOPIC": "let-rss",
    "NTFY_USERNAME": "",
    "NTFY_PASSWORD": "",
    "NTFY_PRIORITY": "4",
}

# Web code imports this. Keep it iterable and limited to the two supported values.
PUSH_CHANNEL_VALUES = {"gotify", "ntfy"}


def _strip_shell_quotes(value: Any) -> str:
    """Parse push.conf values as literal credentials.

    push.conf is read by Python directly, not sourced by shell. Repair older
    over-escaped dollar values such as Plex0819\\$ back to Plex0819$.
    """
    text = str(value or "").strip()
    if len(text) >= 2 and text[0] == text[-1] and text[0] in {'"', "'"}:
        text = text[1:-1]
    text = re.sub(r"\\+\$", "$", text)
    return text.replace('\\"', '"').replace('\\`', '`').replace('\\\\', '\\')


def _normalize_config(cfg: Dict[str, Any]) -> Dict[str, str]:
    merged = dict(PUSH_DEFAULTS)
    merged.update({k: "" if v is None else str(v).strip() for k, v in (cfg or {}).items() if k in PUSH_DEFAULTS})

    enabled = str(merged.get("PUSH_ENABLED", "yes")).strip().lower()
    merged["PUSH_ENABLED"] = "no" if enabled in {"no", "false", "0", "off"} else "yes"

    channel = str(merged.get("PUSH_CHANNEL", "ntfy")).strip().lower()
    if channel in {"both", "all", "telegram", "pushplus", "none", ""}:
        channel = "ntfy"
    if channel not in PUSH_CHANNEL_VALUES:
        channel = "ntfy"
    merged["PUSH_CHANNEL"] = channel

    try:
        merged["GOTIFY_PRIORITY"] = str(int(float(str(merged.get("GOTIFY_PRIORITY", "10") or "10"))))
    except Exception:
        merged["GOTIFY_PRIORITY"] = "10"

    try:
        ntfy_priority = int(float(str(merged.get("NTFY_PRIORITY", "4") or "4")))
        merged["NTFY_PRIORITY"] = str(max(1, min(5, ntfy_priority)))
    except Exception:
        merged["NTFY_PRIORITY"] = "4"

    merged["GOTIFY_URL"] = str(merged.get("GOTIFY_URL", "")).strip().rstrip("/") or PUSH_DEFAULTS["GOTIFY_URL"]
    merged["NTFY_URL"] = str(merged.get("NTFY_URL", "")).strip().rstrip("/") or PUSH_DEFAULTS["NTFY_URL"]
    merged["NTFY_TOPIC"] = str(merged.get("NTFY_TOPIC", "")).strip().strip("/") or PUSH_DEFAULTS["NTFY_TOPIC"]
    return merged


def load_push_config() -> Dict[str, str]:
    """Read /root/quant/push.conf, falling back to env vars and local push.conf."""
    cfg = dict(PUSH_DEFAULTS)
    for key in cfg:
        if os.getenv(key) is not None:
            cfg[key] = os.getenv(key, cfg[key]) or ""

    for path in (PUSH_CONFIG_FILE, BASE_DIR / "push.conf"):
        if not path.exists():
            continue
        try:
            for raw_line in path.read_text(encoding="utf-8").splitlines():
                line = raw_line.strip()
                if not line or line.startswith("#"):
                    continue
                if line.startswith("export "):
                    line = line[len("export "):].strip()
                if "=" not in line:
                    continue
                key, value = line.split("=", 1)
                key = key.strip()
                if key in cfg:
                    cfg[key] = _strip_shell_quotes(value)
            break
        except Exception as exc:
            logging.error(f"读取推送配置失败 {path}: {exc}")
    return _normalize_config(cfg)


def shell_quote_export(value: Any) -> str:
    """Write values in a readable quoted form without escaping $."""
    text = "" if value is None else str(value)
    return '"' + text.replace('\\', '\\\\').replace('"', '\\"') + '"'


def build_push_config_text(cfg: Dict[str, Any]) -> str:
    merged = _normalize_config(cfg)
    ordered_keys = [
        "PUSH_ENABLED",
        "PUSH_CHANNEL",
        "GOTIFY_URL",
        "GOTIFY_TOKEN",
        "GOTIFY_PRIORITY",
        "NTFY_URL",
        "NTFY_TOPIC",
        "NTFY_USERNAME",
        "NTFY_PASSWORD",
        "NTFY_PRIORITY",
    ]
    lines = [
        "# 自动生成的 Push 配置",
        f"# 更新时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "",
    ]
    for key in ordered_keys:
        lines.append(f"export {key}={shell_quote_export(merged.get(key, ''))}")
    lines.append("")
    return "\n".join(lines)


def write_push_config(cfg: Dict[str, Any]) -> None:
    PUSH_CONFIG_FILE.parent.mkdir(parents=True, exist_ok=True)
    tmp = PUSH_CONFIG_FILE.with_suffix(PUSH_CONFIG_FILE.suffix + ".tmp")
    tmp.write_text(build_push_config_text(cfg), encoding="utf-8")
    tmp.replace(PUSH_CONFIG_FILE)


def prune_push_log_lines(keep_lines: int = PUSH_LOG_KEEP_LINES) -> None:
    try:
        if not PUSH_LOG_FILE.exists():
            return
        keep_lines = max(1, int(keep_lines or PUSH_LOG_KEEP_LINES))
        lines = PUSH_LOG_FILE.read_text(encoding="utf-8", errors="ignore").splitlines()
        if len(lines) > keep_lines:
            PUSH_LOG_FILE.write_text("\n".join(lines[-keep_lines:]) + "\n", encoding="utf-8")
    except Exception as exc:
        logging.debug(f"清理推送日志失败: {exc}")



def _is_snapshot_push_body(body: Any, title: Any = "") -> bool:
    """Return True for daily/status snapshot pushes whose full body should not be stored."""
    text = f"{title or ''}\n{body or ''}"
    snapshot_markers = (
        "每日快照",
        "快照推送",
        "📌每日快照",
        "📌 每日快照",
        "策略运行状态",
    )
    return any(marker in text for marker in snapshot_markers)


def append_push_detail(kind: str, body: Any, log_time: str | None = None, title: Any = "") -> None:
    """Store non-snapshot push body for the Web push-log detail popup.

    push.log only records delivery result. The system page pairs each result line
    with this sidecar file by timestamp, so use the same timestamp as push.log
    whenever possible.
    """
    try:
        body_text = str(body or "").strip()
        if not body_text or _is_snapshot_push_body(body_text, title):
            return
        PUSH_DETAIL_LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
        rec = {
            "time": log_time or datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "kind": str(kind or "push"),
            "title": str(title or ""),
            "body": body_text,
        }
        with PUSH_DETAIL_LOG_FILE.open("a", encoding="utf-8") as file_obj:
            file_obj.write(json.dumps(rec, ensure_ascii=False, separators=(",", ":")) + "\n")
        try:
            lines = PUSH_DETAIL_LOG_FILE.read_text(encoding="utf-8", errors="ignore").splitlines()
            if len(lines) > 300:
                PUSH_DETAIL_LOG_FILE.write_text("\n".join(lines[-300:]) + "\n", encoding="utf-8")
        except Exception:
            pass
    except Exception as exc:
        logging.debug(f"写入推送详情失败: {exc}")

def append_push_log(channel: str, success: bool, detail: str, body: Any = "", title: Any = "", kind: str = "push") -> None:
    try:
        PUSH_LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
        log_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        safe_detail = str(detail).replace(chr(10), " ")[:500]
        status = '成功' if success else '失败'
        title_str = str(title or "").strip()
        if title_str:
            line = f"{log_time} | {title_str} | {channel}:{status}\n"
        else:
            line = f"{log_time} | {channel} | {status} | {safe_detail}\n"
        with PUSH_LOG_FILE.open("a", encoding="utf-8") as file_obj:
            file_obj.write(line)
        if body:
            append_push_detail(kind, body, log_time=log_time, title=title)
        prune_push_log_lines(PUSH_LOG_KEEP_LINES)
    except Exception as exc:
        logging.error(f"写入推送日志失败: {exc}")


def read_push_logs(limit: int = PUSH_LOG_KEEP_LINES) -> List[str]:
    if not PUSH_LOG_FILE.exists():
        return []
    try:
        lines = [line.strip() for line in PUSH_LOG_FILE.read_text(encoding="utf-8", errors="ignore").splitlines() if line.strip()]
        return lines[-int(limit or PUSH_LOG_KEEP_LINES):][::-1]
    except Exception as exc:
        return [f"读取推送日志失败：{exc}"]


def _truncate_msg(text: Any, limit: int = 4000) -> str:
    body = str(text or "")
    if len(body) > limit:
        return body[:limit] + "\n...\n(消息过长，已截断)"
    return body


def _is_symbol_status_block(block: str) -> bool:
    text = str(block or "").strip()
    if not text:
        return False
    patterns = (
        "🟢[INFO]【",
        "🎯[TRADE]【",
        "🎯[ERROR]【",
        "🟡[WARN]【",
        "🎯[STOP]【",
        "[仅监控] 🟢[INFO]【",
        "[仅监控] 🎯[ERROR]【",
        "[仅监控] 🟡[WARN]【",
    )
    if text.startswith(patterns):
        return True
    return bool(re.match(r"^\[仅监控\]\s*[^:：\n]+[:：]\s*暂无状态记录", text)) or bool(re.match(r"^[^:：\n]+[:：]\s*暂无状态记录", text))


def _split_ntfy_symbol_batches(text: Any, batch_size: int = 8) -> List[str]:
    """Split long Quant snapshot messages so ntfy does not turn them into attachments."""
    body = str(text or "").strip()
    if not body:
        return [""]
    batch_size = max(1, int(batch_size or 8))
    paragraphs = [part.strip() for part in re.split(r"\n{2,}", body) if part.strip()]
    if len(paragraphs) <= 1:
        return [body]

    first_idx = None
    for idx, part in enumerate(paragraphs):
        if _is_symbol_status_block(part):
            first_idx = idx
            break
    if first_idx is None:
        return [body]

    header = "\n\n".join(paragraphs[:first_idx]).strip()
    blocks = paragraphs[first_idx:]
    if len(blocks) <= batch_size:
        return [body]

    chunks: List[str] = []
    total = (len(blocks) + batch_size - 1) // batch_size
    for part_no, start in enumerate(range(0, len(blocks), batch_size), start=1):
        batch = blocks[start:start + batch_size]
        prefix = header
        if header and total > 1:
            prefix = f"{header} ({part_no}/{total})"
        elif total > 1:
            prefix = f"Quant 推送 ({part_no}/{total})"
        chunk_parts = [prefix] if prefix else []
        chunk_parts.extend(batch)
        chunks.append("\n\n".join(chunk_parts))
    return chunks or [body]


def _send_gotify(msg: str, cfg: Dict[str, str], title: str = "Quant 推送") -> bool:
    gotify_url = str(cfg.get("GOTIFY_URL", "")).strip().rstrip("/")
    gotify_token = str(cfg.get("GOTIFY_TOKEN", "")).strip()
    if not gotify_url or not gotify_token:
        missing = []
        if not gotify_url:
            missing.append("URL")
        if not gotify_token:
            missing.append("Token")
        logging.info(f"未配置 Gotify {', '.join(missing)}，跳过该通道推送。")
        return False
    try:
        priority = int(float(str(cfg.get("GOTIFY_PRIORITY", "10") or "10")))
    except Exception:
        priority = 10
    payload = {
        "title": str(title or "Quant 推送"),
        "message": _truncate_msg(msg, 6000),
        "priority": priority,
    }
    try:
        resp = requests.post(f"{gotify_url}/message", params={"token": gotify_token}, json=payload, timeout=15)
        if 200 <= resp.status_code < 300:
            logging.info("✅ Gotify 推送成功。")
            return True
        logging.error(f"❌ Gotify 推送失败 (状态码{resp.status_code}): {resp.text[:300]}")
        return False
    except Exception as exc:
        logging.error(f"❌ Gotify 推送异常: {exc}")
        return False


def _encode_http_header_value(value: Any) -> str:
    """Encode non-ASCII HTTP headers like the old working quant.py/push.py."""
    text = str(value or "")
    try:
        text.encode("latin-1")
        return text
    except UnicodeEncodeError:
        return Header(text, "utf-8").encode().replace("\n ", " ").replace("\n", "")


def _send_ntfy_detail(msg: str, cfg: Dict[str, str], title: str = "Quant 推送") -> Tuple[bool, str]:
    """Send ntfy with the previous working request shape.

    Important details kept from the working version:
    - body is explicit UTF-8 bytes via data=payload
    - Title is encoded to an ASCII-safe RFC 2047 header when it contains Chinese
    - headers are Title/Priority/Markdown, not X-* variants
    """
    ntfy_url = str(cfg.get("NTFY_URL", "")).strip().rstrip("/")
    topic = str(cfg.get("NTFY_TOPIC", "")).strip().strip("/")
    if not ntfy_url or not topic:
        missing = []
        if not ntfy_url:
            missing.append("URL")
        if not topic:
            missing.append("Topic")
        detail = f"未配置 ntfy {', '.join(missing)}"
        logging.info(detail + "，跳过该通道推送。")
        return False, detail
    try:
        priority = int(float(str(cfg.get("NTFY_PRIORITY", "4") or "4")))
    except Exception:
        priority = 4
    priority = max(1, min(5, priority))
    headers = {
        "Title": _encode_http_header_value(title),
        "Priority": str(priority),
        "Markdown": "yes",
    }
    auth = None
    username = str(cfg.get("NTFY_USERNAME", "")).strip()
    password = str(cfg.get("NTFY_PASSWORD", ""))
    if username:
        auth = (username, password)
    safe_url = f"{ntfy_url}/{topic}"
    parts = _split_ntfy_symbol_batches(msg, batch_size=8)
    sent = 0
    failed_details: List[str] = []
    total_bytes = 0
    for idx, part in enumerate(parts, start=1):
        part_headers = dict(headers)
        if len(parts) > 1:
            part_headers["Title"] = _encode_http_header_value(f"{title} {idx}/{len(parts)}")
        payload = str(part or "").encode("utf-8")
        total_bytes += len(payload)
        try:
            resp = requests.post(safe_url, data=payload, headers=part_headers, auth=auth, timeout=15)
            body = (resp.text or "")[:500].replace("\n", " ")
            if 200 <= resp.status_code < 300:
                sent += 1
                if len(parts) > 1 and idx < len(parts):
                    time.sleep(1)
                continue
            failed_details.append(f"第{idx}/{len(parts)}条 HTTP {resp.status_code}: {body}")
        except Exception as exc:
            failed_details.append(f"第{idx}/{len(parts)}条异常: {exc}")

    if sent == len(parts):
        detail = f"ntfy成功 {sent}/{len(parts)}, priority={priority}, topic={topic}, bytes={total_bytes}"
        logging.info(f"✅ {detail}")
        return True, detail
    detail = f"ntfy失败 {sent}/{len(parts)}, priority={priority}, topic={topic}, " + " | ".join(failed_details)
    logging.error(f"❌ {detail}")
    return False, detail


def _send_ntfy(msg: str, cfg: Dict[str, str]) -> bool:
    ok, _detail = _send_ntfy_detail(msg, cfg)
    return ok



def build_price_monitor_message(
    *,
    name: str,
    symbol: str,
    now_str: str,
    zone: str,
    current_price: float,
    monitor_price: float,
    current_units: float,
    current_avg_cost: float,
    base_units: float,
    target_units: float,
    limit_units: float,
    position_mode: str,
    ma150: float,
    ma150_source: str,
    trend_price: float,
    clear_price: float,
    box_grid_enabled: bool,
    grid_box_percent: float,
    grid_box_units_percent: float,
    dynamic_k150: float,
    sideways_score: float,
    market_source: str,
    market_status: str,
    strategy_source: str,
    strategy_status: str,
) -> str:
    """Build the one-shot [moni] price-monitor notification body."""

    def _num(value: Any, digits: int = 3) -> str:
        try:
            return f"{float(value):.{digits}f}"
        except (TypeError, ValueError):
            return "-"

    def _pct(value: Any, digits: int = 2) -> str:
        try:
            number = float(value) * 100.0
        except (TypeError, ValueError):
            return "-"
        text = f"{number:.{digits}f}".rstrip("0").rstrip(".")
        return f"{text}%"

    if str(position_mode or "").strip().lower() == "percent":
        position_text = _pct(current_units, 2)
        base_text = _pct(base_units, 2)
        target_text = _pct(target_units, 2)
        limit_text = _pct(limit_units, 2)
    else:
        position_text = _num(current_units, 0)
        base_text = _num(base_units, 0)
        target_text = _num(target_units, 0)
        limit_text = _num(limit_units, 0)

    grid_status = "已开启" if bool(box_grid_enabled) else "未开启"
    source_suffix = str(ma150_source or "").strip()
    ma_text = _num(ma150, 3)
    if source_suffix:
        ma_text += f"({source_suffix})"

    return (
        f"🟢[moni]【{name}】 ({symbol})\n"
        f"🕒时间: {now_str}\n"
        f"🍭区间: {zone}\n"
        f"💲当前: {_num(current_price, 3)},监控：{_num(monitor_price, 2)}\n"
        f"⚖️持仓: {position_text}, 成本: {_num(current_avg_cost, 3)}, 底仓: {base_text}, 补仓初始: {target_text}, 极限: {limit_text}\n"
        f"🔀MA150={ma_text}, Trend={_num(trend_price, 3)}, Clear={_num(clear_price, 3)}\n"
        f"📦箱体网格: {grid_status}，步长{_pct(grid_box_percent, 2)}，单次{_pct(grid_box_units_percent, 2)}\n"
        f"⏳动态K={_num(dynamic_k150, 3)}，横盘评分={_num(sideways_score, 2)}\n"
        f"📡行情源: {market_source}，数据状态: {market_status}。\n"
        f"🧭策略源: {strategy_source}，数据状态: {strategy_status}。"
    )

def send_notification(msg: str, title: str = "Quant 推送", config: Dict[str, Any] | None = None) -> bool:
    cfg = _normalize_config(config or load_push_config())
    enabled = str(cfg.get("PUSH_ENABLED", "yes")).strip().lower()
    channel = str(cfg.get("PUSH_CHANNEL", "ntfy")).strip().lower()
    if enabled in {"no", "false", "0", "off"}:
        logging.info("推送已关闭，跳过通知。")
        append_push_log(channel, True, "推送已关闭，跳过通知")
        return True

    if channel == "gotify":
        ok = _send_gotify(msg, cfg, title=title)
        result = f"Gotify:{'成功' if ok else '失败'}"
    else:
        ok, detail = _send_ntfy_detail(msg, cfg, title=title)
        result = detail
    append_push_log(channel, ok, result, body=msg, title=title, kind="notification")
    return ok


def send_push_test(cfg: Dict[str, Any] | None = None) -> Tuple[bool, str]:
    test_cfg = _normalize_config(cfg or load_push_config())
    if test_cfg.get("PUSH_ENABLED") != "yes":
        append_push_log(test_cfg.get("PUSH_CHANNEL", "ntfy"), False, "测试推送：推送已关闭")
        return False, "推送已关闭，请先启用推送并选择通道。"
    title = "Quant 推送测试"
    message = f"闲云量化 Web 推送配置测试成功。\n时间：{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
    channel = test_cfg.get("PUSH_CHANNEL", "ntfy")
    if channel == "gotify":
        ok = _send_gotify(message, test_cfg, title=title)
        detail = f"Gotify：{'成功' if ok else '失败'}"
    else:
        ok, ntfy_detail = _send_ntfy_detail(message, test_cfg, title=title)
        detail = f"ntfy：{'成功' if ok else '失败'} | {ntfy_detail}"
    append_push_log(channel, ok, f"测试推送：{detail}", body=message, title=title, kind="test")
    return ok, detail
