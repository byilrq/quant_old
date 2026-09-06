#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""One-shot price monitor for Quant.

The monitor is deliberately isolated from trading decisions.  It consumes an
already-validated realtime price, detects the first configured price crossing,
sends one notification, and disables itself only after delivery succeeds.
"""

from __future__ import annotations

import logging
import os
import stat
import tempfile
from pathlib import Path
from typing import Any, Dict, Iterable, Optional, Tuple

from push import build_price_monitor_message, send_notification


def normalize_monitor_enabled(value: Any) -> str:
    return "on" if str(value or "").strip().lower() == "on" else "off"


def _safe_float(value: Any) -> Optional[float]:
    try:
        if isinstance(value, str):
            value = value.strip()
            if not value:
                return None
        number = float(value)
        return number if number > 0 else None
    except (TypeError, ValueError):
        return None


def _monitor_targets(cfg: Dict[str, Any]) -> Tuple[float, ...]:
    values = []
    for key in ("monitor_price_1", "monitor_price_2"):
        price = _safe_float(cfg.get(key))
        if price is not None and price not in values:
            values.append(price)
    return tuple(values)


def _first_crossed_target(previous_price: float, current_price: float, targets: Iterable[float]) -> Optional[float]:
    """Return the first level crossed along the actual price path.

    Equality on the current tick counts as a trigger.  Starting exactly at a
    target does not trigger merely because the next tick moves away from it.
    """
    previous_price = float(previous_price)
    current_price = float(current_price)
    targets = tuple(float(x) for x in targets)
    if current_price > previous_price:
        crossed = sorted(x for x in targets if previous_price < x <= current_price)
        return crossed[0] if crossed else None
    if current_price < previous_price:
        crossed = sorted((x for x in targets if current_price <= x < previous_price), reverse=True)
        return crossed[0] if crossed else None
    return None


def _write_monitor_enabled(config_path: Path, symbol_name: str, enabled: str) -> bool:
    """Update only SYMBOL_CONFIG.<name>.monitor_enabled in quant.yaml atomically."""
    config_path = Path(config_path)
    enabled = normalize_monitor_enabled(enabled)
    try:
        try:
            from ruamel.yaml import YAML
        except ImportError:
            YAML = None

        if YAML is not None:
            yaml = YAML()
            yaml.preserve_quotes = True
            yaml.indent(mapping=2, sequence=4, offset=2)
            yaml.width = 4096
            with config_path.open("r", encoding="utf-8") as fh:
                data = yaml.load(fh) or {}
        else:
            import yaml as pyyaml
            with config_path.open("r", encoding="utf-8") as fh:
                data = pyyaml.safe_load(fh) or {}

        section = (data.get("SYMBOL_CONFIG", {}) or {}).get(symbol_name)
        if not isinstance(section, dict):
            logging.error("价格监控自动关闭失败：quant.yaml 中找不到标的 %s", symbol_name)
            return False
        section["monitor_enabled"] = enabled

        original_mode = stat.S_IMODE(config_path.stat().st_mode) if config_path.exists() else None
        fd, tmp_name = tempfile.mkstemp(prefix=".quant-monitor-", suffix=".yaml", dir=str(config_path.parent))
        os.close(fd)
        tmp_path = Path(tmp_name)
        try:
            with tmp_path.open("w", encoding="utf-8") as fh:
                if YAML is not None:
                    yaml.dump(data, fh)
                else:
                    pyyaml.safe_dump(data, fh, allow_unicode=True, default_flow_style=False, sort_keys=False)
            if original_mode is not None:
                os.chmod(tmp_path, original_mode)
            os.replace(tmp_path, config_path)
        finally:
            if tmp_path.exists():
                tmp_path.unlink(missing_ok=True)
        return True
    except Exception as exc:
        logging.error("价格监控自动关闭失败: %s", exc)
        return False


def _reset_monitor_state(node: Dict[str, Any]) -> None:
    node["was_enabled"] = False
    node["armed"] = False
    node["previous_price"] = None
    node["targets_signature"] = []
    node["pending_target"] = None
    node["disable_pending"] = False


def run_price_monitor(
    *,
    name: str,
    cfg: Dict[str, Any],
    quant_state: Dict[str, Any],
    current_price: float,
    config_path: Path,
    message_context: Dict[str, Any],
    allow_monitor: bool = True,
) -> bool:
    """Run one monitor iteration.

    Returns True only when a monitor notification was delivered successfully.
    No trading state or trading decision is modified here.
    """
    node = quant_state.setdefault("price_monitor", {})
    if not isinstance(node, dict):
        node = {}
        quant_state["price_monitor"] = node

    enabled = normalize_monitor_enabled(cfg.get("monitor_enabled", "off"))

    # A successful push may have happened while the YAML auto-off write failed.
    # Keep retrying the config write without re-arming, preventing duplicates.
    if node.get("disable_pending"):
        if _write_monitor_enabled(config_path, name, "off"):
            cfg["monitor_enabled"] = "off"
            _reset_monitor_state(node)
        return False

    if enabled != "on":
        _reset_monitor_state(node)
        return False

    if not allow_monitor:
        return False

    price = _safe_float(current_price)
    targets = _monitor_targets(cfg)
    signature = [str(cfg.get("monitor_arm_id", "") or "").strip()] + list(targets)
    if price is None or not targets:
        return False

    # Re-opening the switch or changing either target starts a fresh watch from
    # the current live price.  No crossing that happened while off is replayed.
    if not node.get("was_enabled") or node.get("targets_signature") != signature:
        node["was_enabled"] = True
        node["armed"] = True
        node["previous_price"] = price
        node["targets_signature"] = signature
        node["pending_target"] = None
        return False

    pending_target = _safe_float(node.get("pending_target"))
    previous_price = _safe_float(node.get("previous_price"))
    if pending_target is None:
        if previous_price is None:
            node["previous_price"] = price
            return False
        pending_target = _first_crossed_target(previous_price, price, targets)
        node["previous_price"] = price
        if pending_target is None:
            return False
        node["pending_target"] = pending_target

    message = build_price_monitor_message(
        name=name,
        symbol=str(cfg.get("symbol", "") or "").strip(),
        monitor_price=pending_target,
        current_price=price,
        **message_context,
    )
    try:
        sent = bool(send_notification(message, title=f"价格监控【{name}】"))
    except Exception as exc:
        logging.error("%s 价格监控推送异常: %s", name, exc)
        sent = False

    if not sent:
        logging.warning("%s 价格监控已触发 %.3f，但推送失败；保持 ON，下一轮继续重试。", name, pending_target)
        return False

    logging.info("%s 价格监控触发 %.3f，推送成功，自动关闭监控。", name, pending_target)
    cfg["monitor_enabled"] = "off"
    node["pending_target"] = None
    node["was_enabled"] = False
    node["armed"] = False
    node["previous_price"] = None
    node["targets_signature"] = []
    if not _write_monitor_enabled(config_path, name, "off"):
        node["disable_pending"] = True
    else:
        node["disable_pending"] = False
    return True
