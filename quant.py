#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import time as time_module
import json
from pathlib import Path
from datetime import datetime, time, timedelta
import logging
import os
import math
import csv
import shutil
import sys
import re
import random
from datetime import datetime
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

from push import PUSH_LOG_FILE, send_notification
from monitor import run_price_monitor

# 导入策略模块
from strategy import (
    get_zone,
    normalize_position_amount,
    calculate_pyramid_sell_plan,
    get_pyramid_sell_target_step,
    get_clear_pyramid_target_step,
    get_trend_sell_decision,
    get_pyramid_add_enabled,
    get_add_trade_decision,
    POSITION_EPSILON,
)

# ===========================
# 路径配置
# ===========================
BASE_DIR = Path(__file__).parent
config_path = os.path.join(BASE_DIR, "quant.yaml")
STATE_FILE = BASE_DIR / "quant_monitor_state.json"
SYSTEM_CONFIG_FILE = BASE_DIR / "system_config.json"
LOG_DIR = BASE_DIR / "log"
TRADE_LOG_FILE = BASE_DIR / "trade_log.csv"
SNAPSHOT_DIR = BASE_DIR / "data" / "snapshots"
STATE_BACKUP_DIR = BASE_DIR / "data" / "state_backups"
STATE_BACKUP_INDEX = STATE_BACKUP_DIR / "index.json"
PUSH_DETAIL_LOG_FILE = BASE_DIR / "data" / "push_details.jsonl"
LOG_DIR.mkdir(exist_ok=True)

# ===========================
# 数据保留策略
# ===========================
SNAPSHOT_RETENTION_DAYS = 7
PUSH_LOG_KEEP_LINES = 30

def prune_snapshot_files(keep_days: int = SNAPSHOT_RETENTION_DAYS):
    """保留最近 keep_days 天策略快照，删除更早的 YYYY-MM-DD.jsonl。默认保留 30 天。"""
    try:
        SNAPSHOT_DIR.mkdir(parents=True, exist_ok=True)
        today = strategy_now().date() if "strategy_now" in globals() else datetime.now().date()
        cutoff = today - timedelta(days=max(1, int(keep_days or SNAPSHOT_RETENTION_DAYS)) - 1)
        for path in SNAPSHOT_DIR.glob("*.jsonl"):
            try:
                snap_date = datetime.strptime(path.stem, "%Y-%m-%d").date()
            except Exception:
                continue
            if snap_date < cutoff:
                path.unlink()
    except Exception as e:
        logging.debug(f"清理过期策略快照失败: {e}")
        
def prune_strategy_history_cache():
    """Delete all strategy cache files that are not for today."""
    try:
        today = strategy_now().strftime("%Y-%m-%d")
        history_dir = _strategy_history_dir()
        for path in history_dir.glob("*.json"):
            stem = path.stem
            # 文件名格式: SYMBOL_YYYY-MM-DD.json
            parts = stem.rsplit("_", 1)
            if len(parts) != 2:
                continue
            file_date = parts[1]
            if file_date != today:
                path.unlink()
                logging.debug(f"已删除旧策略缓存: {path.name}")
    except Exception as e:
        logging.debug(f"清理全局策略历史缓存失败: {e}")

def prune_push_log_lines(keep_lines: int = PUSH_LOG_KEEP_LINES):
    """只保留 push.log 最近 keep_lines 条。"""
    try:
        if not PUSH_LOG_FILE.exists():
            return
        keep_lines = max(1, int(keep_lines or PUSH_LOG_KEEP_LINES))
        lines = PUSH_LOG_FILE.read_text(encoding="utf-8", errors="ignore").splitlines()
        if len(lines) > keep_lines:
            PUSH_LOG_FILE.write_text("\n".join(lines[-keep_lines:]) + "\n", encoding="utf-8")
    except Exception as e:
        logging.debug(f"清理推送日志失败: {e}")

# ===========================
# 辅助函数
# ===========================
def calculate_new_avg_cost(old_position, old_avg_cost, add_units, add_price):
    if old_position == 0:
        return add_price
    total_cost_before = old_position * old_avg_cost
    total_cost_after = total_cost_before + add_units * add_price
    return total_cost_after / (old_position + add_units)

def _parse_hm(s: str):
    """Parse HH:MM time values from YAML/Web config.

    PyYAML may parse unquoted values such as 16:00 as the integer 960
    (YAML 1.1 sexagesimal).  Treat numeric values in 0..1439 as minutes
    since midnight so 960 correctly becomes 16:00 instead of falling back
    to 09:30 and making the daemon think it is outside trading hours.
    """
    try:
        if isinstance(s, (int, float)) and not isinstance(s, bool):
            total = int(s)
            if 0 <= total < 24 * 60:
                return total // 60, total % 60
        text = str(s or "").strip()
        if text.isdigit():
            total = int(text)
            if 0 <= total < 24 * 60:
                return total // 60, total % 60
        h, m = text.split(":", 1)
        return int(h), int(m)
    except Exception:
        return 9, 30

def round_to_lot(qty, lot_size=100):
    if qty <= 0:
        return 0
    rounded_qty = int(qty // lot_size) * lot_size
    if rounded_qty == 0 and qty > 0:
        rounded_qty = lot_size
    return rounded_qty

def _safe_float(value, default=0.0):
    try:
        if isinstance(value, str):
            value = value.strip()
            if not value:
                return default
        return float(value)
    except Exception:
        return default

def get_position_mode(cfg):
    base = cfg.get("base_units", 0)
    target = cfg.get("target_units", 0)
    if isinstance(base, str) and base.strip().endswith("%"):
        return "percent"
    if isinstance(target, str) and target.strip().endswith("%"):
        return "percent"
    try:
        base_f = float(base)
        target_f = float(target)
        if 0 <= base_f <= 1 and 0 <= target_f <= 1:
            return "percent"
    except Exception:
        pass
    return "absolute"

def parse_position_value(value, mode=None):
    if isinstance(value, str):
        s = value.strip()
        if not s:
            return 0.0
        if s.endswith("%"):
            return float(s[:-1]) / 100.0
        return float(s)
    return _safe_float(value, 0.0)

def get_base_units(cfg):
    return parse_position_value(cfg.get("base_units", 0))

def get_target_units(cfg):
    return parse_position_value(cfg.get("target_units", 0))

def get_limit_units(cfg):
    return get_base_units(cfg) * _safe_float(cfg.get("limit_target", cfg.get("double_target_factor", 2.0)), 2.0)

def normalize_strategy_run_value(value, default="on"):
    """运行开关只允许 on/off；无效或缺失值按 default 处理，默认 on。"""
    s = str(value if value is not None else "").strip().lower()
    if s in {"on", "off"}:
        return s
    return default

def is_strategy_on(cfg):
    return normalize_strategy_run_value(cfg.get("strategy_run", "on"), "on") == "on"

def get_trend_multiple(cfg):
    return _safe_float(cfg.get("trend_multiple", 1.2), 1.2)

def get_sell_multiple(cfg):
    return _safe_float(cfg.get("sell_multiple", 1.5), 1.5)

def get_add_box_step(cfg):
    return _safe_float(cfg.get("box_add_step", cfg.get("add_box_step", 0.05)), 0.05)

def get_pyramid_add_step(cfg):
    return _safe_float(cfg.get("pyramid_add_step", cfg.get("add_box_step", 0.05)), 0.05)

def get_clear_pyramid_weights(cfg):
    return cfg.get("clear_pyramid_weights", cfg.get("pyramid_weights", [0.03, 0.055, 0.08, 0.105, 0.13, 0.155, 0.18, 0.205, 0.23, 0.255]))

def get_pyramid_add_weights(cfg):
    return cfg.get("pyramid_add_weights", cfg.get("pyramid_weights", [0.03, 0.055, 0.08, 0.105, 0.13, 0.155, 0.18, 0.205, 0.23, 0.255]))

def get_clear_pyramid_steps(cfg):
    weights = get_clear_pyramid_weights(cfg) or []
    steps = int(_safe_float(cfg.get("clear_pyramid_steps", cfg.get("pyramid_steps", len(weights))), len(weights)))
    return min(steps, len(weights)) if weights else max(steps, 0)

def get_pyramid_add_steps(cfg):
    weights = get_pyramid_add_weights(cfg) or []
    steps = int(_safe_float(cfg.get("pyramid_add_steps", cfg.get("pyramid_steps", len(weights))), len(weights)))
    return min(steps, len(weights)) if weights else max(steps, 0)

def get_add_box_units_percent(cfg):
    return _safe_float(cfg.get("add_box_units_percent", 0.1), 0.1)

def get_trend_zone_step_percent(cfg):
    return _safe_float(cfg.get("trend_zone_step_percent", 0.01), 0.01)

def get_trend_zone_sell_percent(cfg):
    return _safe_float(cfg.get("trend_zone_sell_percent", 0.05), 0.05)

def get_clear_zone_step_percent(cfg):
    return _safe_float(cfg.get("clear_zone_step_percent", 0.08), 0.08)

def get_box_grid_enabled(cfg):
    value = str(cfg.get("box_grid_enabled", "no")).strip().lower()
    return value in {"yes", "true", "1", "on"}

def get_live_current_units(cfg):
    if "current_units" not in cfg or cfg.get("current_units") in (None, ""):
        return None
    mode = get_position_mode(cfg)
    return normalize_position_amount(parse_position_value(cfg.get("current_units", 0)), mode)

def get_live_current_avg_cost(cfg):
    if "current_avg_cost" not in cfg or cfg.get("current_avg_cost") in (None, ""):
        return None
    return max(_safe_float(cfg.get("current_avg_cost", 0.0), 0.0), 0.0)

def format_percent_ratio(value, digits=2):
    pct = _safe_float(value, 0.0) * 100.0
    s = f"{pct:.{digits}f}".rstrip("0").rstrip(".")
    if s in {"", "-0"}:
        s = "0"
    return f"{s}%"

def format_units_for_display(value, mode):
    if mode == "percent":
        return format_percent_ratio(value)
    return f"{int(round(_safe_float(value, 0.0))):,}股"

def serialize_numeric(value, digits=6):
    if value is None or value == "":
        return ""
    if isinstance(value, str):
        return value
    s = f"{float(value):.{digits}f}".rstrip("0").rstrip(".")
    return s if s else "0"

def build_default_symbol_state(cfg):
    base_units = get_base_units(cfg)
    live_units = get_live_current_units(cfg)
    live_avg_cost = get_live_current_avg_cost(cfg)
    return {
        "last_price": None,
        "last_trade_price": None,
        "last_trade_side": "buy",
        "tick": 0,
        "current_units": live_units if live_units is not None else base_units,
        "avg_cost": live_avg_cost if live_avg_cost is not None else 0.0,
        "ma_short": None,
        "last_status_msg": None,
        "pyramid_step": 0,
        "clear_step": 0,
        "clear_anchor_price": None,
        "strategy_run": normalize_strategy_run_value(cfg.get("strategy_run", "on"), "on"),
        "position_mode": get_position_mode(cfg),
        "last_add_price": None,
        "pyramid_anchor_price": None,
        "pyramid_start_units": None,
        "pyramid_limit_units": None,
        "pyramid_add_active": False,
        "target_reached_once": False,
    }

def normalize_symbol_state(name, cfg, entry):
    mode = get_position_mode(cfg)
    base_units = get_base_units(cfg)
    live_units = get_live_current_units(cfg)
    live_avg_cost = get_live_current_avg_cost(cfg)
    limit_units = get_limit_units(cfg)
    legacy_mode = entry.get("position_mode")
    reset_reason = None
    had_current_units = "current_units" in entry and entry.get("current_units") not in (None, "")
    had_avg_cost = "avg_cost" in entry and entry.get("avg_cost") not in (None, "")
    if "last_trade_price" not in entry:
        entry["last_trade_price"] = None
    if "last_trade_side" not in entry:
        entry["last_trade_side"] = "buy"
    if "avg_cost" not in entry:
        entry["avg_cost"] = 0.0
    if "strategy_run" not in entry:
        entry["strategy_run"] = normalize_strategy_run_value(cfg.get("strategy_run", "on"), "on")
    if "pyramid_step" not in entry:
        entry["pyramid_step"] = 0
    if "clear_step" not in entry:
        entry["clear_step"] = 0
    if "clear_anchor_price" not in entry:
        entry["clear_anchor_price"] = None
    if "last_add_price" not in entry:
        entry["last_add_price"] = None
    if "pyramid_anchor_price" not in entry:
        entry["pyramid_anchor_price"] = None
    if "pyramid_start_units" not in entry:
        entry["pyramid_start_units"] = None
    if "pyramid_limit_units" not in entry:
        entry["pyramid_limit_units"] = None
    if "pyramid_add_active" not in entry:
        entry["pyramid_add_active"] = False
    if "target_reached_once" not in entry:
        entry["target_reached_once"] = False
    current_units = entry.get("current_units", live_units if live_units is not None else base_units)
    try:
        current_units = float(current_units)
    except Exception:
        reset_reason = "current_units 无法解析"
        current_units = base_units
    if legacy_mode and legacy_mode != mode:
        reset_reason = f"状态文件仓位模式为 {legacy_mode}，当前配置为 {mode}"
    if mode == "percent":
        if current_units < -POSITION_EPSILON:
            reset_reason = "current_units 为负数"
        elif current_units > max(1.0, limit_units * 5):
            reset_reason = "检测到旧版按股数状态，无法自动换算为百分比仓位"
    else:
        if current_units < 0:
            reset_reason = "current_units 为负数"
    if reset_reason:
        logging.warning(
            f"⚠️ {name}: {reset_reason}，已重置为基准仓位 {format_units_for_display(live_units if live_units is not None else base_units, mode)}"
        )
        entry["current_units"] = live_units if live_units is not None else base_units
        entry["avg_cost"] = live_avg_cost if live_avg_cost is not None else 0.0
        entry["pyramid_step"] = 0
        entry["clear_step"] = 0
        entry["clear_anchor_price"] = None
        entry["last_add_price"] = None
        entry["pyramid_anchor_price"] = None
        entry["pyramid_start_units"] = None
        entry["pyramid_limit_units"] = None
        entry["pyramid_add_active"] = False
        entry["target_reached_once"] = False
    else:
        # Runtime state is authoritative. Config changes or program restarts must not
        # silently overwrite live strategy anchors/position state. YAML current_units
        # and current_avg_cost are only used to initialize missing/new/reset state.
        entry["current_units"] = normalize_position_amount(current_units, mode)
        if not had_current_units and live_units is not None:
            entry["current_units"] = live_units
        if not had_avg_cost and live_avg_cost is not None:
            entry["avg_cost"] = live_avg_cost
        elif entry["current_units"] <= POSITION_EPSILON:
            entry["avg_cost"] = 0.0
    entry["position_mode"] = mode
    return entry

# ===========================
# 日志轮转与备份函数
# ===========================
def rotate_and_backup_logs(now: datetime = None):
    if now is None:
        now = strategy_now()
    log_file = BASE_DIR / "quant.log"
    backup_date = (now.date() - timedelta(days=1))
    backup_file = LOG_DIR / f"quant.{backup_date.strftime('%Y%m%d')}.log"

    if not log_file.exists():
        logging.info("ℹ️ quant.log 不存在，跳过日志轮转")
        return False

    try:
        # 1. 关闭所有 logger handlers，停止写入原文件
        logger = logging.getLogger()
        for handler in logger.handlers[:]:
            try:
                handler.close()
                logger.removeHandler(handler)
            except Exception as e:
                print(f"关闭 handler 失败: {e}")

        # 2. 重命名当前日志文件作为备份（原子操作，不丢失数据）
        if log_file.exists():
            log_file.rename(backup_file)

        # 3. 重新配置日志系统（会自动创建新的空 quant.log）
        setup_logging()

        # 4. 记录轮转完成信息
        logging.info("=" * 60)
        logging.info(f"🔄 日志轮转完成 - {now.strftime('%Y-%m-%d %H:%M:%S')}")
        logging.info(f"📁 日志已备份至: {backup_file.name}")
        logging.info("=" * 60)
        return True
    except Exception as e:
        print(f"日志轮转失败: {e}")
        try:
            setup_logging()
        except Exception as e2:
            print(f"日志轮转失败后恢复日志系统也失败: {e2}")
        return False

def setup_logging():
    logger = logging.getLogger()
    logger.setLevel(logging.INFO)
    if logger.hasHandlers():
        logger.handlers.clear()
    log_file = BASE_DIR / "quant.log"
    file_handler = logging.FileHandler(
        filename=str(log_file),
        encoding="utf-8",
        mode='a'
    )
    file_handler.setLevel(logging.INFO)
    formatter = logging.Formatter("%(message)s")
    file_handler.setFormatter(formatter)
    logger.addHandler(file_handler)
    return logger

logger = setup_logging()

# ===========================
# 读取配置文件
# ===========================
def load_config(path):
    try:
        import yaml
    except ImportError:
        import json5 as json_mod
        with open(path, "r", encoding="utf-8") as f:
            cfg = json_mod.load(f)
    else:
        with open(path, "r", encoding="utf-8") as f:
            cfg = yaml.safe_load(f)
    cfg = cfg or {}
    quant_cfg = cfg.get("SYMBOL_CONFIG", {}) or {}
    strategy_cfg = cfg.get("STRATEGY", {}) or {}
    return quant_cfg, strategy_cfg, cfg

def save_full_config(full_cfg, path=None):
    target = path or config_path
    try:
        import yaml
    except ImportError:
        return False
    with open(target, "w", encoding="utf-8") as f:
        yaml.dump(full_cfg, f, allow_unicode=True, default_flow_style=False, sort_keys=False)
    return True

def persist_runtime_position_to_config(name, current_units, avg_cost):
    global FULL_CONFIG, SYMBOL_CONFIG
    try:
        _, _, disk_cfg = load_config(config_path)
    except Exception:
        disk_cfg = None
    if not isinstance(disk_cfg, dict):
        disk_cfg = FULL_CONFIG
    if not isinstance(disk_cfg, dict):
        return False
    symbol_cfg = disk_cfg.setdefault("SYMBOL_CONFIG", {})
    if name not in symbol_cfg or not isinstance(symbol_cfg.get(name), dict):
        return False
    mode = get_position_mode(symbol_cfg[name])
    symbol_cfg[name]["current_units"] = format_units_for_display(current_units, mode) if mode == "percent" else int(round(_safe_float(current_units, 0.0)))
    symbol_cfg[name]["current_avg_cost"] = round(_safe_float(avg_cost, 0.0), 6) if _safe_float(avg_cost, 0.0) > 0 else 0.0
    SYMBOL_CONFIG[name]["current_units"] = symbol_cfg[name]["current_units"]
    SYMBOL_CONFIG[name]["current_avg_cost"] = symbol_cfg[name]["current_avg_cost"]
    FULL_CONFIG = disk_cfg
    return save_full_config(disk_cfg)

FULL_CONFIG = {}
STRATEGY = {
    "loop_enabled": "yes",
    "loop_interval": 60,
    "fetch_history_days": 400,
    "ma_period_short": 150,
    "ma_period_long": 300,  # 保留但不再使用
    "session_start": "09:30",
    "session_end": "16:00",
    "daily_push_time": "09:00",
    "log_rotate_time": "09:00",
    # 所有策略时间参数均按该时区解释；不依赖服务器系统时区。
    # 可选示例：Asia/Shanghai、Asia/Tokyo、Asia/Singapore、America/Los_Angeles。
    "timezone": "Asia/Shanghai",
}

TIMEZONE_ALIASES = {
    "shanghai": "Asia/Shanghai",
    "上海": "Asia/Shanghai",
    "china": "Asia/Shanghai",
    "cn": "Asia/Shanghai",
    "tokyo": "Asia/Tokyo",
    "东京": "Asia/Tokyo",
    "japan": "Asia/Tokyo",
    "jp": "Asia/Tokyo",
    "singapore": "Asia/Singapore",
    "新加坡": "Asia/Singapore",
    "sg": "Asia/Singapore",
    "los_angeles": "America/Los_Angeles",
    "los angeles": "America/Los_Angeles",
    "la": "America/Los_Angeles",
    "洛杉矶": "America/Los_Angeles",
}

def get_strategy_timezone_name() -> str:
    raw = str(STRATEGY.get("timezone", "Asia/Shanghai") or "Asia/Shanghai").strip()
    if not raw:
        return "Asia/Shanghai"
    return TIMEZONE_ALIASES.get(raw.lower(), raw)

def resolve_strategy_timezone():
    name = get_strategy_timezone_name()
    try:
        return ZoneInfo(name)
    except ZoneInfoNotFoundError:
        logging.warning(f"⚠️ 策略时区配置无效: {name}，已回退到 Asia/Shanghai")
        return ZoneInfo("Asia/Shanghai")

def strategy_now() -> datetime:
    """Return current time in configured strategy timezone, independent of server timezone."""
    return datetime.now(resolve_strategy_timezone())

# ===========================
# 时间控制函数
# ===========================
def in_trade_session(now: datetime = None) -> bool:
    if now is None:
        now = strategy_now()
    start_str = STRATEGY.get("session_start", "09:30")
    end_str = STRATEGY.get("session_end", "16:00")
    sh, sm = _parse_hm(start_str)
    eh, em = _parse_hm(end_str)
    t = now.time()
    start_t = time(sh, sm)
    end_t = time(eh, em)
    return start_t <= t <= end_t

def should_rotate_logs(state: dict, now: datetime = None) -> bool:
    if now is None:
        now = strategy_now()
    rotate_str = STRATEGY.get("log_rotate_time", "09:00")
    rh, rm = _parse_hm(rotate_str)
    rotate_t = time(rh, rm)
    today = now.date().isoformat()
    meta = state.get("_meta", {})
    last_rotate_date = meta.get("last_log_rotate_date")
    if now.time() >= rotate_t and last_rotate_date != today:
        return True
    return False

def should_do_daily_push(state: dict, now: datetime = None) -> bool:
    if now is None:
        now = strategy_now()
    push_str = STRATEGY.get("daily_push_time", "09:00")
    ph, pm = _parse_hm(push_str)
    push_t = time(ph, pm)
    today = now.date().isoformat()
    meta = state.get("_meta", {})
    last_date = meta.get("last_daily_push_date")
    if now.time() >= push_t and last_date != today:
        return True
    return False

# ===========================
# 状态文件读写
# ===========================
def load_state():
    yesterday = (strategy_now().date() - timedelta(days=1)).isoformat()
    initial_state = {}
    for name, cfg in SYMBOL_CONFIG.items():
        initial_state[name] = build_default_symbol_state(cfg)
    initial_state["_meta"] = {
        "last_daily_push_date": yesterday,
        "last_log_rotate_date": yesterday
    }

    if STATE_FILE.exists():
        try:
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                state = json.load(f)
            if not isinstance(state, dict):
                logging.warning(f"状态文件格式错误，重置为初始状态")
                return initial_state

            for name, cfg in SYMBOL_CONFIG.items():
                if name not in state or not isinstance(state.get(name), dict):
                    state[name] = build_default_symbol_state(cfg)
                else:
                    try:
                        state[name] = normalize_symbol_state(name, cfg, state[name])
                    except Exception as e:
                        logging.warning(f"标的 {name} 状态规范化失败，重置为初始状态: {e}")
                        state[name] = build_default_symbol_state(cfg)

            if "_meta" not in state or not isinstance(state.get("_meta"), dict):
                state["_meta"] = initial_state["_meta"]
            else:
                if "last_log_rotate_date" not in state["_meta"]:
                    state["_meta"]["last_log_rotate_date"] = yesterday
                if "last_daily_push_date" not in state["_meta"]:
                    state["_meta"]["last_daily_push_date"] = yesterday
            return state
        except Exception as e:
            logging.error(f"加载状态文件异常: {e}，重置为初始状态")
            return initial_state
    initial_state = {}
    for name, cfg in SYMBOL_CONFIG.items():
        initial_state[name] = build_default_symbol_state(cfg)
    yesterday = (strategy_now().date() - timedelta(days=1)).isoformat()
    initial_state["_meta"] = {
        "last_daily_push_date": yesterday,
        "last_log_rotate_date": yesterday
    }
    return initial_state

def save_state(state):
    """Persist runtime state without clobbering a newer Web rollback request.

    quant_web.py writes rollback/config requests into quant_monitor_state.json while
    quant.py may still be finishing the current strategy loop.  Without this guard,
    the loop-end save can overwrite the freshly written state_restore_entry with
    the old in-memory position, causing the Web params page to show the restored
    5% position while the daemon continues to run with the previous 20% state.
    """
    out = state if isinstance(state, dict) else {}
    try:
        if STATE_FILE.exists():
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                disk_state = json.load(f)
            if isinstance(disk_state, dict):
                disk_meta = disk_state.get("_meta", {}) if isinstance(disk_state.get("_meta", {}), dict) else {}
                out_meta = out.setdefault("_meta", {})
                disk_seq = _safe_int(disk_meta.get("config_reload_seq", 0), 0)
                out_seq = _safe_int(out_meta.get("config_reload_seq", 0), 0)

                # If Web has just written a trade rollback request that this
                # in-memory loop has not consumed yet, preserve both the meta
                # request and the restored symbol entry.  The next loop will
                # apply_runtime_config_reload_if_needed() and then run the
                # trade-enabled rerun with the restored state.
                if disk_seq > out_seq and disk_meta.get("state_restore_kind") == "trade_backup":
                    restore_name = str(disk_meta.get("state_restore_symbol_key", "") or "").strip()
                    restore_entry = disk_meta.get("state_restore_entry")
                    for key in (
                        "config_reload_seq", "config_reload_requested_at",
                        "config_reload_symbol_key", "config_reload_symbols",
                        "state_restore_kind", "state_restore_symbol_key",
                        "state_restore_backup_id", "state_restore_entry",
                    ):
                        if key in disk_meta:
                            out_meta[key] = disk_meta[key]
                    if restore_name and isinstance(restore_entry, dict):
                        out[restore_name] = restore_entry
    except Exception as e:
        logging.debug(f"保存状态前合并 Web 回滚请求失败，继续保存当前状态: {e}")

    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=2)

def read_state_raw():
    if STATE_FILE.exists():
        try:
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            return data if isinstance(data, dict) else {}
        except Exception as e:
            logging.error(f"读取状态刷新请求失败: {e}")
    return {}

def _safe_int(value, default=0):
    try:
        return int(value)
    except Exception:
        return default

def apply_runtime_config_reload_if_needed(state, last_seen_seq):
    """Apply config reload requests written by quant_web.py without restarting quant.py.

    Trade-state rollback is handled in two phases: restore the exact
    state_before snapshot first, then mark a restore_trade_rerun_seq so the
    main loop immediately runs one trade-enabled calculation with current price.
    """
    disk_state = read_state_raw()
    disk_meta = disk_state.get("_meta", {}) if isinstance(disk_state, dict) else {}
    seq = _safe_int(disk_meta.get("config_reload_seq", 0), 0)
    if seq <= last_seen_seq:
        return last_seen_seq
    state.setdefault("_meta", {})
    state["_meta"].update(disk_meta)
    requested = disk_meta.get("config_reload_symbols") or []
    if isinstance(requested, str):
        requested = [requested]
    if not requested:
        requested = [disk_meta.get("config_reload_symbol_key", "")]
    if "__ALL__" in requested:
        target_names = list(SYMBOL_CONFIG.keys())
    else:
        target_names = [name for name in requested if name in SYMBOL_CONFIG]
    if not target_names:
        logging.info(f"🔁 收到参数刷新请求 seq={seq}，但未匹配到标的，已忽略。")
        return seq
    if disk_meta.get("state_restore_kind") == "trade_backup":
        restore_name = str(disk_meta.get("state_restore_symbol_key", "")).strip()
        restore_entry = disk_meta.get("state_restore_entry")
        restore_backup_id = disk_meta.get("state_restore_backup_id", "")
        if restore_name in SYMBOL_CONFIG and isinstance(restore_entry, dict):
            restored = normalize_symbol_state(restore_name, SYMBOL_CONFIG[restore_name], dict(restore_entry))
            restored["last_status_msg"] = (
                f"已恢复到交易前状态回滚点：{restore_backup_id}；"
                "下一轮将按当前实时价格重新执行策略判断。"
            )
            restored["restore_backup_id"] = restore_backup_id
            restored["restore_applied_at"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
            state[restore_name] = restored
            meta = state.setdefault("_meta", {})
            meta["restore_trade_rerun_seq"] = seq
            meta["restore_trade_rerun_symbol_key"] = restore_name
            meta["restore_trade_rerun_symbols"] = [restore_name]
            meta["restore_trade_rerun_backup_id"] = restore_backup_id
            meta["restore_trade_rerun_requested_at"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
            for _k in ["state_restore_kind", "state_restore_symbol_key", "state_restore_backup_id", "state_restore_entry"]:
                meta.pop(_k, None)
            logging.info(f"↩️ 已恢复交易前状态: {restore_name}，回滚点={restore_backup_id}；将立即按当前价重跑一次策略。")
            save_state(state)
            return seq
        logging.warning(f"⚠️ 收到状态回滚请求，但内容无效: {restore_name}, backup={restore_backup_id}")
        return seq
    for name in target_names:
        old_entry = state.get(name, {}) if isinstance(state.get(name, {}), dict) else {}
        disk_entry = disk_state.get(name, {}) if isinstance(disk_state.get(name, {}), dict) else {}
        if old_entry and disk_entry:
            merged_entry = dict(old_entry)
        else:
            merged_entry = build_default_symbol_state(SYMBOL_CONFIG[name])
        # Web 参数页可能刚把 current_units / avg_cost 写入状态文件。
        # 后台内存 state 不能再用旧值覆盖它，否则用户会看到“已写入”但下一轮仍按旧仓位计算。
        for _k in ("current_units", "avg_cost", "position_mode"):
            if _k in disk_entry and disk_entry.get(_k) not in (None, ""):
                merged_entry[_k] = disk_entry.get(_k)
        state[name] = normalize_symbol_state(name, SYMBOL_CONFIG[name], merged_entry)
        # Do not clear last_status_msg here. Parameter reload must not erase the last complete trading-frame status.
        logging.info(f"🔁 参数已即时刷新: {name}，已加载最新 quant.yaml；运行仓位/成本已合并，状态正文等待下一轮行情刷新。")
    save_state(state)
    return seq


def apply_system_config_update_if_needed(state, last_seen_seq):
    """Apply Web system market-source changes without restarting quant.py.

    When the preferred market source changes, old source confirmation state is no longer useful.
    Clearing it prevents one-time WARN like sina_a -> tencent_api after a deliberate setting change.
    """
    disk_state = read_state_raw()
    disk_meta = disk_state.get("_meta", {}) if isinstance(disk_state, dict) else {}
    seq = _safe_int(disk_meta.get("system_config_seq", 0), 0)
    if seq <= last_seen_seq:
        return last_seen_seq
    state.setdefault("_meta", {}).update(disk_meta)
    for name in list(SYMBOL_CONFIG.keys()):
        entry = state.get(name)
        if not isinstance(entry, dict):
            continue
        for key in ["pending_market_source", "pending_market_source_count", "last_valid_market_source", "market_source"]:
            entry.pop(key, None)
        entry["market_status"] = "system_source_updated"
    logging.info(f"🔁 系统行情源配置已即时生效 seq={seq}，已清理旧行情源确认状态。")
    save_state(state)
    return seq


def read_force_refresh_request(state):
    """Return (is_requested, seq, target_names) for Web manual refresh request.

    Web 状态页刷新只刷新当前选中的标的，避免一次性拉取所有标的
    的多路参考价导致后台循环变慢。旧版全量刷新字段仍会被忽略为
    “当前配置范围内的指定标的”，没有指定时才退回全量。
    """
    disk_state = read_state_raw()
    disk_meta = disk_state.get("_meta", {}) if isinstance(disk_state, dict) else {}
    requested_seq = _safe_int(disk_meta.get("force_refresh_seq", 0), 0)
    done_seq = _safe_int(state.get("_meta", {}).get("force_refresh_done_seq", 0), 0)
    if requested_seq <= done_seq:
        return False, requested_seq, []
    state.setdefault("_meta", {}).update(disk_meta)
    requested = disk_meta.get("force_refresh_symbols") or []
    if isinstance(requested, str):
        requested = [requested]
    if not requested:
        key = str(disk_meta.get("force_refresh_symbol_key", "") or "").strip()
        if key:
            requested = [key]
    if "__ALL__" in requested:
        target_names = list(SYMBOL_CONFIG.keys())
    else:
        target_names = [name for name in requested if name in SYMBOL_CONFIG]
    # 兼容通过代码请求刷新
    code = str(disk_meta.get("force_refresh_symbol_code", "") or "").strip().upper()
    if code and not target_names:
        for name, cfg in SYMBOL_CONFIG.items():
            if isinstance(cfg, dict) and str(cfg.get("symbol", "")).strip().upper() == code:
                target_names.append(name)
                break
    if not target_names:
        target_names = list(SYMBOL_CONFIG.keys())
    return True, requested_seq, target_names


def read_restore_trade_rerun_request(state):
    """Return (is_requested, seq, target_names, backup_id) after rollback.

    This is trade-enabled. It completes rollback by recalculating the selected
    symbol with the current realtime price after state_before has been restored.
    """
    disk_state = read_state_raw()
    disk_meta = disk_state.get("_meta", {}) if isinstance(disk_state, dict) else {}
    mem_meta = state.get("_meta", {}) if isinstance(state, dict) else {}
    requested_seq = _safe_int(disk_meta.get("restore_trade_rerun_seq", mem_meta.get("restore_trade_rerun_seq", 0)), 0)
    done_seq = _safe_int(mem_meta.get("restore_trade_rerun_done_seq", 0), 0)
    if requested_seq <= done_seq:
        return False, requested_seq, [], ""
    state.setdefault("_meta", {}).update(disk_meta)
    requested = disk_meta.get("restore_trade_rerun_symbols") or mem_meta.get("restore_trade_rerun_symbols") or []
    if isinstance(requested, str):
        requested = [requested]
    if not requested:
        key = str(disk_meta.get("restore_trade_rerun_symbol_key", mem_meta.get("restore_trade_rerun_symbol_key", "")) or "").strip()
        if key:
            requested = [key]
    target_names = [name for name in requested if name in SYMBOL_CONFIG]
    if not target_names:
        return False, requested_seq, [], ""
    backup_id = str(disk_meta.get("restore_trade_rerun_backup_id", mem_meta.get("restore_trade_rerun_backup_id", "")) or "")
    return True, requested_seq, target_names, backup_id


def read_source_metrics_refresh_request(state):
    """Return (is_requested, seq, target_names) for Web historical-source metrics refresh.

    This is independent from status refresh. It only calculates MA150/sell/Clear/
    dynamicK/sideways score for each historical source and caches the result for
    Web display. It never triggers trades.
    """
    disk_state = read_state_raw()
    disk_meta = disk_state.get("_meta", {}) if isinstance(disk_state, dict) else {}
    requested_seq = _safe_int(disk_meta.get("source_metrics_refresh_seq", 0), 0)
    done_seq = _safe_int(state.get("_meta", {}).get("source_metrics_refresh_done_seq", 0), 0)
    if requested_seq <= done_seq:
        return False, requested_seq, []
    state.setdefault("_meta", {}).update(disk_meta)
    requested = disk_meta.get("source_metrics_refresh_symbols") or []
    if isinstance(requested, str):
        requested = [requested]
    if not requested:
        key = str(disk_meta.get("source_metrics_refresh_symbol_key", "") or "").strip()
        if key:
            requested = [key]
    if "__ALL__" in requested:
        target_names = list(SYMBOL_CONFIG.keys())
    else:
        target_names = [name for name in requested if name in SYMBOL_CONFIG]
    code = str(disk_meta.get("source_metrics_refresh_symbol_code", "") or "").strip().upper()
    if code and not target_names:
        for name, cfg in SYMBOL_CONFIG.items():
            if isinstance(cfg, dict) and str(cfg.get("symbol", "")).strip().upper() == code:
                target_names.append(name)
                break
    if not target_names:
        target_names = list(SYMBOL_CONFIG.keys())
    return True, requested_seq, target_names



def has_pending_web_refresh_request(state: dict) -> bool:
    """Return True when Web wrote a refresh/control seq newer than what quant.py has consumed.

    The old loop slept for loop_interval seconds unconditionally, so a user could click
    refresh during trading hours and wait up to a full interval before anything happened.
    This helper lets the sleep wake early when Web asks for status, source metrics,
    clear-market-state, config reload, or system source reload.
    """
    try:
        disk_state = read_state_raw()
        disk_meta = disk_state.get("_meta", {}) if isinstance(disk_state, dict) else {}
        mem_meta = state.get("_meta", {}) if isinstance(state, dict) else {}
        pairs = [
            ("force_refresh_seq", "force_refresh_done_seq"),
            ("source_metrics_refresh_seq", "source_metrics_refresh_done_seq"),
            ("clear_market_state_seq", "clear_market_state_done_seq"),
            ("restore_trade_rerun_seq", "restore_trade_rerun_done_seq"),
        ]
        for req_key, done_key in pairs:
            if _safe_int(disk_meta.get(req_key, 0), 0) > _safe_int(mem_meta.get(done_key, 0), 0):
                return True
        if _safe_int(disk_meta.get("config_reload_seq", 0), 0) > _safe_int(mem_meta.get("config_reload_seq", 0), 0):
            return True
        if _safe_int(disk_meta.get("system_config_seq", 0), 0) > _safe_int(mem_meta.get("system_config_seq", 0), 0):
            return True
    except Exception:
        return False
    return False


def sleep_until_next_loop_or_web_request(state: dict, seconds) -> None:
    """Sleep in short slices so Web manual refresh is handled almost immediately."""
    try:
        total = max(1, int(float(seconds or 1)))
    except Exception:
        total = 1
    # 1 second gives responsive manual refresh without busy-waiting.
    for _ in range(total):
        if has_pending_web_refresh_request(state):
            return
        time_module.sleep(1)


def apply_market_state_clear_if_needed(state):
    """Reset one symbol's runtime state requested by Web.

    This is the only normal Web path that intentionally resets strategy runtime
    fields such as last_trade_price, last_add_price, pyramid_step, clear_step,
    current_units and avg_cost. Other symbols are not touched.
    """
    disk_state = read_state_raw()
    disk_meta = disk_state.get("_meta", {}) if isinstance(disk_state, dict) else {}
    seq = _safe_int(disk_meta.get("clear_market_state_seq", 0), 0)
    done_seq = _safe_int(state.get("_meta", {}).get("clear_market_state_done_seq", 0), 0)
    if seq <= done_seq:
        return False, seq, []
    state.setdefault("_meta", {}).update(disk_meta)
    requested = disk_meta.get("clear_market_state_symbols") or []
    if isinstance(requested, str):
        requested = [requested]
    if not requested:
        key = str(disk_meta.get("clear_market_state_symbol_key", "") or "").strip()
        if key:
            requested = [key]
    if "__ALL__" in requested:
        target_names = list(SYMBOL_CONFIG.keys())
    else:
        target_names = [name for name in requested if name in SYMBOL_CONFIG]
    code = str(disk_meta.get("clear_market_state_symbol_code", "") or "").strip().upper()
    if code and not target_names:
        for name, cfg in SYMBOL_CONFIG.items():
            if isinstance(cfg, dict) and str(cfg.get("symbol", "")).strip().upper() == code:
                target_names.append(name)
                break
    reset_names = []
    for name in target_names:
        if name not in SYMBOL_CONFIG:
            continue
        state[name] = normalize_symbol_state(name, SYMBOL_CONFIG[name], build_default_symbol_state(SYMBOL_CONFIG[name]))
        state[name]["last_status_msg"] = "已手动重置该标的运行状态，并清除行情错误/旧价格校验状态，等待下一轮刷新。"
        state[name]["market_status"] = "reset"
        reset_names.append(name)
    state.setdefault("_meta", {})["clear_market_state_done_seq"] = seq
    state.setdefault("_meta", {})["clear_market_state_done_at"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
    save_state(state)
    if reset_names:
        logging.info(f"♻️ 已手动重置标的运行状态并清除行情状态 seq={seq}: {','.join(reset_names)}")
    return bool(reset_names), seq, reset_names

# ===========================
# 构建每日快照
# ===========================
def record_push_detail(kind: str, body: str):
    """Record non-snapshot push body so Web push log can show real detail.

    push.log itself is written by push.py and only contains delivery result;
    this sidecar keeps the actual message body for non-snapshot pushes.
    """
    try:
        kind = str(kind or "").strip() or "push"
        body = str(body or "")
        if not body.strip() or kind == "snapshot":
            return
        PUSH_DETAIL_LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
        rec = {
            "time": strategy_now().strftime("%Y-%m-%d %H:%M:%S"),
            "kind": kind,
            "body": body,
        }
        with PUSH_DETAIL_LOG_FILE.open("a", encoding="utf-8") as f:
            f.write(json.dumps(rec, ensure_ascii=False, separators=(",", ":")) + "\n")
        # Keep the sidecar compact; push.log itself is already trimmed elsewhere.
        try:
            lines = PUSH_DETAIL_LOG_FILE.read_text(encoding="utf-8", errors="ignore").splitlines()
            if len(lines) > 200:
                PUSH_DETAIL_LOG_FILE.write_text("\n".join(lines[-200:]) + "\n", encoding="utf-8")
        except Exception:
            pass
    except Exception as e:
        logging.debug(f"记录推送详情失败: {e}")


def build_daily_snapshot(state: dict) -> str:
    lines = []
    current_time = strategy_now().strftime("%Y.%m.%d.%H:%M")
    for name in SYMBOL_CONFIG.keys():
        quant_state = state.get(name, {})
        status = quant_state.get("last_status_msg")
        cfg = SYMBOL_CONFIG.get(name, {})
        strategy_run = normalize_strategy_run_value(cfg.get("strategy_run", "on"), "on")
        if status:
            old_time_match = re.search(r'🕒时间:\s*(\d{4}\.\d{2}\.\d{2}\.\d{2}:\d{2})', status)
            if old_time_match:
                status = status.replace(old_time_match.group(1), current_time)
            if strategy_run == "off":
                lines.append(f"[仅监控] {status}")
            else:
                lines.append(status)
        else:
            if strategy_run == "off":
                lines.append(f"[仅监控] {name}: 暂无状态记录")
            else:
                lines.append(f"{name}: 暂无状态记录")
    snapshot_header = f"🎯 每日快照 - {strategy_now().strftime('%Y-%m-%d %H:%M:%S')}\n\n"
    return snapshot_header + "\n\n".join(lines)

# ===========================
# 行情数据获取 - 独立接口层
# ===========================
try:
    from market_data import (
        MarketSnapshot,
        get_market_snapshot,
        get_reference_prices,
        get_history_snapshot_by_source,
        get_price_from_api,
        get_history_close,
        get_hk_history_close,
        get_a_history_close,
        get_a_price,
        get_hk_price,
        get_source_display_name as market_get_source_display_name,
        get_source_canonical_key as market_get_source_canonical_key,
        normalize_system_source_value as market_normalize_system_source_value,
    )
except Exception as _market_import_error:
    raise RuntimeError(f"无法导入行情接口文件 market_data.py: {_market_import_error}")


def _is_price_jump_suspicious(current_price, reference_price, max_ratio=0.25):
    try:
        cur = float(current_price)
        ref = float(reference_price)
    except Exception:
        return False, 1.0
    if cur <= 0 or ref <= 0:
        return False, 1.0
    ratio = cur / ref
    if ratio > (1.0 + max_ratio) or ratio < (1.0 - max_ratio):
        return True, ratio
    return False, ratio


def _format_market_message_lines(name, symbol, level, reason, current_price=None, last_known_price=None, closes_count=None, source=None, last_bar_date=None):
    if level == "warn":
        head = f"🟡[WARN]【{name}】 ({symbol})"
        status = "⚠️行情源观察中，本轮只监控不交易。"
    else:
        head = f"🔴[ERROR]【{name}】 ({symbol})"
        status = "❌行情数据异常，已跳过本轮策略，不会触发交易。"
    lines = [
        head,
        f"🕒时间: {strategy_now().strftime('%Y.%m.%d.%H:%M')}",
        status,
        f"原因: {reason}",
    ]
    if source:
        lines.append(f"📡行情源: {source}")
    if last_bar_date:
        lines.append(f"🧾最新K线日期: {last_bar_date}")
    if current_price is not None:
        try:
            lines.append(f"当前价: {float(current_price):.3f}")
        except Exception:
            lines.append(f"当前价: {current_price}")
    if last_known_price is not None:
        try:
            lines.append(f"上次有效价: {float(last_known_price):.3f}")
        except Exception:
            lines.append(f"上次有效价: {last_known_price}")
    if closes_count is not None:
        lines.append(f"历史数据条数: {closes_count}")
    return lines


def _build_market_data_error_message(name, symbol, reason, current_price=None, last_known_price=None, closes_count=None, source=None, last_bar_date=None):
    return chr(10).join(_format_market_message_lines(name, symbol, "error", reason, current_price, last_known_price, closes_count, source, last_bar_date))


def _build_market_data_warn_message(name, symbol, reason, current_price=None, last_known_price=None, closes_count=None, source=None, last_bar_date=None):
    return chr(10).join(_format_market_message_lines(name, symbol, "warn", reason, current_price, last_known_price, closes_count, source, last_bar_date))


def _is_all_sources_failed_reason(reason):
    text = str(reason or "")
    return ("全部数据源失败" in text) or ("全部行情源失败" in text) or ("全部数据源" in text and "失败" in text)


def _maybe_market_alert(quant_state, msg, reason_key):
    """只有全部行情源失败才推送，并按标的/自然日去重。"""
    if not _is_all_sources_failed_reason(reason_key):
        return []
    day_key = strategy_now().strftime("%Y%m%d")
    alert_key = f"{day_key}|all_sources_failed"
    if quant_state.get("last_market_all_sources_alert_key") == alert_key:
        return []
    quant_state["last_market_all_sources_alert_key"] = alert_key
    return [msg]

def _json_safe_value(value):
    """Convert strategy snapshot values to JSON-safe primitives."""
    if value is None or isinstance(value, (str, int, bool)):
        return value
    if isinstance(value, float):
        if math.isnan(value) or math.isinf(value):
            return None
        return value
    if isinstance(value, (list, tuple)):
        return [_json_safe_value(x) for x in value]
    if isinstance(value, dict):
        return {str(k): _json_safe_value(v) for k, v in value.items()}
    try:
        return float(value)
    except Exception:
        return str(value)


def _strategy_snapshot_path(day_text=None):
    day_text = day_text or strategy_now().strftime("%Y-%m-%d")
    return SNAPSHOT_DIR / f"{day_text}.jsonl"


def write_strategy_snapshot(record):
    """Append one JSONL strategy snapshot; never interrupt strategy execution."""
    try:
        SNAPSHOT_DIR.mkdir(parents=True, exist_ok=True)
        rec = {str(k): _json_safe_value(v) for k, v in (record or {}).items()}
        # Normalize source names before writing snapshots so future stats/log views are consistent.
        try:
            for _src_key in ("market_source", "strategy_source", "source"):
                if _src_key in rec:
                    rec[_src_key] = _display_source_name(rec.get(_src_key))
        except Exception:
            pass
        if "time" not in rec:
            rec["time"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
        if "date" not in rec:
            rec["date"] = str(rec["time"])[:10]
        path = _strategy_snapshot_path(rec["date"])
        with path.open("a", encoding="utf-8") as f:
            f.write(json.dumps(rec, ensure_ascii=False, separators=(",", ":")) + "\n")
        today_key = strategy_now().strftime("%Y-%m-%d")
        if getattr(write_strategy_snapshot, "_last_prune_date", None) != today_key:
            prune_snapshot_files(SNAPSHOT_RETENTION_DAYS)
            write_strategy_snapshot._last_prune_date = today_key
    except Exception as e:
        logging.debug(f"写入策略快照失败: {e}")




def _sanitize_filename_part(value):
    text = str(value or "").strip()
    text = re.sub(r"[^A-Za-z0-9_\-\.]+", "_", text)
    return text[:80] or "unknown"


def _read_state_backup_index():
    try:
        if STATE_BACKUP_INDEX.exists():
            data = json.loads(STATE_BACKUP_INDEX.read_text(encoding="utf-8"))
            return data if isinstance(data, list) else []
    except Exception as e:
        logging.debug(f"读取交易前状态索引失败: {e}")
    return []


def _write_state_backup_index(items):
    try:
        STATE_BACKUP_DIR.mkdir(parents=True, exist_ok=True)
        STATE_BACKUP_INDEX.write_text(json.dumps(items or [], ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception as e:
        logging.debug(f"写入交易前状态索引失败: {e}")


def _prune_state_backups(index_items, name, symbol, keep=10):
    """Keep latest N backup points per symbol/name and remove old backup files."""
    keep = max(1, int(keep or 10))
    key_name = str(name or "")
    key_symbol = str(symbol or "").upper()
    matched = [x for x in index_items if x.get("name") == key_name or str(x.get("symbol", "")).upper() == key_symbol]
    matched.sort(key=lambda x: str(x.get("time", "")), reverse=True)
    keep_ids = {x.get("id") for x in matched[:keep]}
    pruned = []
    for item in index_items:
        is_same = item.get("name") == key_name or str(item.get("symbol", "")).upper() == key_symbol
        if is_same and item.get("id") not in keep_ids:
            rel = str(item.get("file", ""))
            try:
                path = (BASE_DIR / rel).resolve() if rel else None
                if path and str(path).startswith(str(STATE_BACKUP_DIR.resolve())) and path.exists():
                    path.unlink()
            except Exception as e:
                logging.debug(f"删除旧交易前状态备份失败: {rel} | {e}")
            continue
        pruned.append(item)
    return pruned


def record_trade_state_backup(name, symbol, quant_state, cfg, trade_info):
    """Record state before a real TRADE so Web can roll back if a false signal occurs."""
    try:
        now = strategy_now()
        day = now.strftime("%Y-%m-%d")
        ts_file = now.strftime("%H%M%S_%f")
        backup_id = f"{day}_{ts_file}_{_sanitize_filename_part(symbol)}"
        day_dir = STATE_BACKUP_DIR / day
        day_dir.mkdir(parents=True, exist_ok=True)
        filename = f"{_sanitize_filename_part(symbol)}_{ts_file}_before_trade.json"
        path = day_dir / filename
        state_before = _json_safe_value(dict(quant_state or {}))
        cfg_before = _json_safe_value(dict(cfg or {}))
        record = {
            "id": backup_id,
            "time": now.strftime("%Y-%m-%d %H:%M:%S"),
            "date": day,
            "name": name,
            "symbol": symbol,
            "position_mode": get_position_mode(cfg or {}),
            "trade": _json_safe_value(trade_info or {}),
            "state_before": state_before,
            "config_before": cfg_before,
            "note": "before_trade",
        }
        path.write_text(json.dumps(record, ensure_ascii=False, indent=2), encoding="utf-8")
        index_item = {
            "id": backup_id,
            "time": record["time"],
            "name": name,
            "symbol": symbol,
            "side": str((trade_info or {}).get("side", "")),
            "reason": str((trade_info or {}).get("reason", "")),
            "zone": str((trade_info or {}).get("zone", "")),
            "price": _json_safe_value((trade_info or {}).get("price")),
            "qty": _json_safe_value((trade_info or {}).get("qty")),
            "pos_before": _json_safe_value((trade_info or {}).get("pos_before")),
            "pos_after": _json_safe_value((trade_info or {}).get("pos_after")),
            "avg_cost_before": _json_safe_value((trade_info or {}).get("avg_cost_before")),
            "avg_cost_after": _json_safe_value((trade_info or {}).get("avg_cost_after")),
            "file": str(path.relative_to(BASE_DIR)),
        }
        index_items = _read_state_backup_index()
        index_items.append(index_item)
        index_items = _prune_state_backups(index_items, name, symbol, keep=10)
        _write_state_backup_index(index_items)
        logging.info(f"🧷 已记录交易前状态回滚点: {name} ({symbol}) {index_item['side']} {index_item['qty']} @ {index_item['price']}")
    except Exception as e:
        logging.warning(f"⚠️ 记录交易前状态回滚点失败: {name} ({symbol}) | {e}")

def write_market_skip_snapshot(name, symbol, quant_state, reason, level="ERROR", source="", current_price=None,
                               last_known_price=None, closes_count=None, last_bar_date=None, trade_allowed=False):
    write_strategy_snapshot({
        "time": strategy_now().strftime("%Y-%m-%d %H:%M:%S"),
        "name": name,
        "symbol": symbol,
        "level": level,
        "action": "SKIP_TRADE",
        "decision": "SKIP_TRADE",
        "reason": str(reason),
        "market_status": "error" if str(level).upper() == "ERROR" else "warn",
        "market_source": _display_source_name(source or quant_state.get("market_source", "")),
        "current_price": current_price,
        "last_valid_price": last_known_price if last_known_price is not None else quant_state.get("last_valid_price"),
        "last_price": quant_state.get("last_price"),
        "last_bar_date": last_bar_date,
        "history_count": closes_count,
        "trade_allowed": bool(trade_allowed),
        "current_units": quant_state.get("current_units"),
        "avg_cost": quant_state.get("avg_cost"),
        "last_trade_price": quant_state.get("last_trade_price"),
        "last_add_price": quant_state.get("last_add_price"),
        "pyramid_step": quant_state.get("pyramid_step"),
        "clear_step": quant_state.get("clear_step"),
    })


def _mark_market_error(quant_state, msg, reason, source=""):
    quant_state["last_status_msg"] = msg
    quant_state["market_status"] = "error"
    quant_state["market_error"] = str(reason)[:500]
    if source:
        quant_state["market_source"] = _display_source_name(source)


def _mark_market_warn(quant_state, msg, reason, source=""):
    quant_state["last_status_msg"] = msg
    quant_state["market_status"] = "warn"
    quant_state["market_error"] = str(reason)[:500]
    if source:
        quant_state["market_source"] = _display_source_name(source)


def _canonical_market_source(source):
    """Canonical source key from market_data.py; fallback only preserves raw value."""
    try:
        return market_get_source_canonical_key(str(source or ""))
    except Exception:
        return str(source or "").strip()

def _display_source_name(source):
    """Customer-facing source name from market_data.py. Internal codes are not shown."""
    s = str(source or "").strip()
    try:
        return market_get_source_display_name(s)
    except Exception:
        if s.startswith("cache_"):
            return "本地缓存"
        return s or "未知"

def _strategy_level_badge(level: str) -> str:
    level = str(level or "INFO").upper()
    if level == "ERROR":
        return "🔴[ERROR]"
    if level == "WARN":
        return "🟡[WARN]"
    return "🟢[INFO]"


def _short_strategy_issue(level: str = "", error: str = "", ma150_source: str = "") -> str:
    """Return a very short issue tag for message headers and pushes."""
    level = str(level or "").upper()
    err = str(error or "").strip()
    src = str(ma150_source or "").strip()
    if level in {"", "INFO", "OK"} and not err:
        return ""
    if src and src != "f":
        return f"MA150={src}"
    low = err.lower()
    if "ma150" in low and ("不足" in err or "insufficient" in low):
        return "K线不足"
    if "历史" in err and "不足" in err:
        return "K线不足"
    if "cookie" in low or "token" in low or "401" in err or "403" in err:
        return "Cookie失效"
    if "timeout" in low or "超时" in err:
        return "超时"
    if "connection" in low or "连接" in err or "disconnected" in low:
        return "连接失败"
    if "price" in low or "价格" in err:
        return "价格异常"
    if "k线" in err or "k线" in low:
        return "K线异常"
    # Keep message compact in the title line.
    return err[:18] if err else ("策略异常" if level == "WARN" else "策略错误")


def _annotate_message_header(msg: str, level: str = "INFO", issue: str = "") -> str:
    """Change the first-line badge and append a compact issue tag."""
    if not msg:
        return msg
    level = str(level or "INFO").upper()
    badge = _strategy_level_badge(level)
    lines = str(msg).split("\n")
    head = lines[0]
    for old in ("🟢[INFO]", "🟡[WARN]", "🔴[ERROR]"):
        if old in head:
            head = head.replace(old, badge, 1)
            break
    if issue and "｜" not in head:
        head = f"{head}｜{issue}"
    lines[0] = head
    return "\n".join(lines)


def _apply_strategy_alert_to_message(msg: str, level: str = "INFO", issue: str = "") -> str:
    """Apply compact strategy/data alert to status or trade push text."""
    level = str(level or "INFO").upper()
    if level not in {"WARN", "ERROR"}:
        return msg
    msg = _annotate_message_header(msg, level, issue)
    if issue and "⚠️策略:" not in msg:
        msg += f"\n⚠️策略: {issue}"
    return msg



def _strategy_source_for_symbol(symbol):
    raw = str(symbol or "").upper().strip()
    cfg = _read_system_config_for_metrics()
    key = cfg.get("HK_BACKTEST_SOURCE", "historical_hk1") if raw.startswith("HK") else cfg.get("A_BACKTEST_SOURCE", "historical_a1")
    return _display_source_name(key)


def _strategy_calc_cache_key(symbol, strategy_source, last_bar_date, ma_len, cfg):
    keys = [
        "k150", "sideways_window_30", "sideways_window_60", "sideways_weight_60", "sideways_min_k150",
        "trend_multiple", "sell_multiple", "price_scale",
    ]
    parts = [str(symbol), str(strategy_source), str(last_bar_date), str(ma_len)]
    for k in keys:
        parts.append(f"{k}={cfg.get(k, '')}")
    return "|".join(parts)


def _check_market_source_switch(quant_state, snapshot, cfg):
    """行情源切换首轮禁止交易，连续确认后才允许新源进入策略。"""
    new_source = snapshot.source
    last_source = quant_state.get("last_valid_market_source") or quant_state.get("market_source")
    if not last_source or last_source == new_source or _canonical_market_source(last_source) in {"", _canonical_market_source(new_source)}:
        quant_state["pending_market_source"] = ""
        quant_state["pending_market_source_count"] = 0
        return True, ""

    try:
        required = int(_safe_float(cfg.get("market_source_switch_confirmations", STRATEGY.get("market_source_switch_confirmations", 2)), 2))
    except Exception:
        required = 2
    required = max(2, required)

    pending_source = quant_state.get("pending_market_source")
    pending_count = int(_safe_float(quant_state.get("pending_market_source_count", 0), 0))
    if pending_source == new_source:
        pending_count += 1
    else:
        pending_source = new_source
        pending_count = 1
    quant_state["pending_market_source"] = pending_source
    quant_state["pending_market_source_count"] = pending_count

    if pending_count < required:
        return False, f"行情源从 {_display_source_name(last_source)} 切换到 {_display_source_name(new_source)}，等待连续确认 {pending_count}/{required}；本轮只监控不交易"

    return True, f"行情源从 {_display_source_name(last_source)} 切换到 {_display_source_name(new_source)}，已连续确认 {pending_count}/{required}"


def _mark_market_ok(quant_state, snapshot):
    quant_state["market_status"] = "ok"
    quant_state["market_error"] = ""
    quant_state["market_source"] = _display_source_name(snapshot.source)
    quant_state["last_valid_market_source"] = _display_source_name(snapshot.source)
    quant_state["last_valid_price"] = snapshot.current_price
    quant_state["last_valid_bar_date"] = snapshot.last_bar_date
    quant_state["pending_market_source"] = ""
    quant_state["pending_market_source_count"] = 0

# ===========================
# 计算简单移动平均线 MA（带数据不足处理）
# ===========================
def calc_ma_with_coef(closes, length, min_coef=None, reference_ma=None):
    """Calculate MA with explicit cold-start marking.

    - f: full MA with length bars.
    - pN: provisional MA using N bars when N >= ma_min_bars (default 75).
    - insufficient_data: fewer than ma_min_bars bars.

    pN is intentionally visible in push/status so cold-start MA is never mistaken
    for a formal MA150.
    """
    closes = list(closes or [])
    count = len(closes)
    if count >= length:
        return sum(closes[-length:]) / length, 'f'
    min_bars = int(_safe_float(STRATEGY.get('ma_min_bars', 75), 75)) if 'STRATEGY' in globals() else 75
    min_bars = max(1, min(min_bars, length))
    if count >= min_bars:
        return sum(closes) / count, f'p{count}'
    return None, 'insufficient_data'

# ===========================
# 横盘指数
# ===========================
def _compute_ma_series(closes, period):
    if len(closes) < period:
        return []
    ma_series = []
    window_sum = sum(closes[:period])
    ma_series.append(window_sum / period)
    for i in range(period, len(closes)):
        window_sum += closes[i] - closes[i - period]
        ma_series.append(window_sum / period)
    return ma_series

def _ma_directional_sideways_score(ma_series, window):
    n = len(ma_series)
    if n < window + 1:
        return 0.5
    seg = ma_series[-(window + 1):]
    deltas = [seg[i+1] - seg[i] for i in range(window)]
    sum_abs = sum(abs(d) for d in deltas)
    if sum_abs == 0:
        return 1.0
    dir_strength = abs(sum(deltas)) / sum_abs
    sideways_score = 1.0 - dir_strength
    return max(0.0, min(1.0, sideways_score))

def compute_sideways_index(closes, cfg):
    period30 = 30
    period60 = 60
    window30 = int(cfg.get("sideways_window_30", 30))
    window60 = int(cfg.get("sideways_window_60", 20))
    weight60 = float(cfg.get("sideways_weight_60", 0.6))
    weight60 = max(0.0, min(1.0, weight60))
    weight30 = 1.0 - weight60
    need_len = max(period30 + window30 + 1, period60 + window60 + 1)
    if len(closes) < need_len:
        return 0.0
    ma30_series = _compute_ma_series(closes, period30)
    ma60_series = _compute_ma_series(closes, period60)
    if not ma30_series or not ma60_series:
        return 0.0
    s30 = _ma_directional_sideways_score(ma30_series, window30)
    s60 = _ma_directional_sideways_score(ma60_series, window60)
    sideways_score = weight30 * s30 + weight60 * s60
    return max(0.0, min(1.0, sideways_score))


# ===========================
# 历史/策略数据源指标对照
# ===========================
def _normalize_system_source_key(field, value):
    """Normalize system source values through market_data.py; no legacy HK Sina alias."""
    try:
        return market_normalize_system_source_value(field, value)
    except Exception:
        raw = str(value or "").strip()
        allowed = {
            "A_BACKTEST_SOURCE": {"historical_a1", "historical_a2"},
            "HK_BACKTEST_SOURCE": {"historical_hk1", "historical_hk2"},
            "A_QUOTE_SOURCE": {"live_a1", "live_a2", "live_a3"},
            "HK_MARKET_SOURCE": {"live_hk1", "live_hk2", "live_hk3"},
        }.get(field, set())
        defaults = {
            "A_BACKTEST_SOURCE": "historical_a1",
            "HK_BACKTEST_SOURCE": "historical_hk1",
            "A_QUOTE_SOURCE": "live_a1",
            "HK_MARKET_SOURCE": "live_hk1",
        }
        return raw if raw in allowed else defaults.get(field, raw)


def _read_system_config_for_metrics():
    cfg = {
        "A_BACKTEST_SOURCE": "historical_a1",
        "HK_BACKTEST_SOURCE": "historical_hk1",
    }
    try:
        if SYSTEM_CONFIG_FILE.exists():
            raw = json.loads(SYSTEM_CONFIG_FILE.read_text(encoding="utf-8") or "{}")
            if isinstance(raw, dict):
                cfg.update({k: "" if v is None else str(v).strip() for k, v in raw.items()})
    except Exception as e:
        logging.debug(f"读取系统回测/策略数据源配置失败: {e}")
    cfg["A_BACKTEST_SOURCE"] = _normalize_system_source_key("A_BACKTEST_SOURCE", cfg.get("A_BACKTEST_SOURCE"))
    cfg["HK_BACKTEST_SOURCE"] = _normalize_system_source_key("HK_BACKTEST_SOURCE", cfg.get("HK_BACKTEST_SOURCE"))
    return cfg



def _history_source_options_for_symbol(symbol):
    """Return historical strategy sources in fallback order.

    The system-selected source is tried first. Other sources are only per-symbol,
    per-run fallbacks and never rewrite system_config.json or quant.yaml.
    """
    raw = str(symbol or "").upper().strip()
    system_cfg = _read_system_config_for_metrics()
    if raw.startswith("HK"):
        selected = system_cfg.get("HK_BACKTEST_SOURCE", "historical_hk1")
        labels = {
            "historical_hk1": "腾讯港股日K",
            "historical_hk2": "Yahoo港股含权息",
            "historical_hk3": "备用港股日K",
        }
        order = [selected, "historical_hk1", "historical_hk2", "historical_hk3"]
    else:
        selected = system_cfg.get("A_BACKTEST_SOURCE", "historical_a1")
        labels = {
            "historical_a1": "腾讯A股/ETF日K",
            "historical_a2": "新浪A股/ETF日K",
            "historical_a3": "BaoStock A股含权息",
        }
        order = [selected, "historical_a1", "historical_a2", "historical_a3"]
    seen = set()
    out = []
    for key in order:
        key = str(key or "").strip()
        if not key or key in seen:
            continue
        seen.add(key)
        out.append((key, labels.get(key, _display_source_name(key))))
    return out


def _calc_source_metric_from_snapshot(source_key, source_label, symbol, cfg, snap, ma_short_len):
    closes = list(getattr(snap, "closes", []) or [])
    if not closes:
        raise RuntimeError("历史K线为空")
    ma150_raw, ma150_source = calc_ma_with_coef(closes, ma_short_len)
    if ma150_raw is None:
        raise RuntimeError(f"历史数据不足，无法计算MA150，count={len(closes)}")
    sideways_score = float(compute_sideways_index(closes, cfg))
    base_k150 = float(cfg.get("k150", 1.0))
    min_k150 = float(cfg.get("sideways_min_k150", 0.85))
    if base_k150 < min_k150:
        min_k150 = base_k150
    dynamic_k150 = min_k150 + (base_k150 - min_k150) * (1.0 - sideways_score)
    ma150 = ma150_raw * dynamic_k150
    sell_price = ma150 * get_trend_multiple(cfg)
    clear_price = ma150 * get_sell_multiple(cfg)
    current_price = float(getattr(snap, "current_price", closes[-1]) or closes[-1])
    try:
        zone = get_zone(current_price, ma150, cfg)
    except Exception:
        zone = ""
    return {
        "key": source_key,
        "label": source_label,
        "ok": True,
        "level": "INFO" if ma150_source == "f" else "WARN",
        "status": "OK" if ma150_source == "f" else "WARN",
        "source": _display_source_name(getattr(snap, "source", source_key)),
        "date": getattr(snap, "last_bar_date", "") or "",
        "count": len(closes),
        "current_price": round(current_price, 4),
        "ma150": round(float(ma150), 4),
        "ma150_source": ma150_source,
        "sell": round(float(sell_price), 4),
        "clear": round(float(clear_price), 4),
        "dynamic_k": round(float(dynamic_k150), 4),
        "sideways_score": round(float(sideways_score), 4),
        "zone": zone,
        "error": "" if ma150_source == "f" else f"策略数据为非完整口径: MA150来源={ma150_source}",
    }


def _source_metric_from_strategy_state(symbol, cfg, quant_state):
    """Build the Web 回测/策略指标 card from the latest strategy calculation cache."""
    strategy_source = _display_source_name(quant_state.get("strategy_source") or _strategy_source_for_symbol(symbol))
    cache = quant_state.get("strategy_calc_cache") if isinstance(quant_state.get("strategy_calc_cache"), dict) else {}
    ma150 = _safe_float(quant_state.get("ma_short", cache.get("ma150")), 0.0)
    dynamic_k = _safe_float(quant_state.get("dynamic_k150", cache.get("dynamic_k150")), 0.0)
    sideways = _safe_float(quant_state.get("sideways_score", cache.get("sideways_score")), 0.0)
    current_price = _safe_float(quant_state.get("last_price"), 0.0)
    ma150_source = str(quant_state.get("ma_short_source") or cache.get("ma150_source") or "")
    last_bar_date = str(cache.get("last_bar_date") or quant_state.get("last_valid_bar_date") or "")
    updated_at = str(quant_state.get("strategy_calc_updated_at") or cache.get("updated_at") or strategy_now().strftime("%Y-%m-%d %H:%M:%S"))
    history_count = _safe_int(cache.get("history_count", quant_state.get("history_count", 0)), 0)
    ok = ma150 > 0 and current_price > 0
    err = str(quant_state.get("strategy_error") or "")
    level = str(quant_state.get("strategy_level") or ("INFO" if ok else "ERROR")).upper()
    status = str(quant_state.get("strategy_status") or ("OK" if ok else "ERROR")).upper()
    if ok and ma150_source and ma150_source != "f" and level == "INFO":
        level = "WARN"
        status = "WARN"
        err = err or f"策略数据为非完整口径: MA150来源={ma150_source}"
    zone = ""
    try:
        if ok:
            zone = get_zone(current_price, ma150, cfg)
    except Exception:
        zone = ""
    return {
        "key": strategy_source,
        "label": f"{strategy_source} 策略值",
        "ok": bool(ok and level != "ERROR"),
        "level": level,
        "status": status,
        "source": strategy_source,
        "date": last_bar_date,
        "updated_at": updated_at,
        "count": history_count,
        "current_price": round(current_price, 4) if current_price else None,
        "ma150": round(ma150, 4) if ma150 else None,
        "ma150_source": ma150_source,
        "sell": round(ma150 * get_trend_multiple(cfg), 4) if ma150 else None,
        "clear": round(ma150 * get_sell_multiple(cfg), 4) if ma150 else None,
        "dynamic_k": round(dynamic_k, 4) if dynamic_k else None,
        "sideways_score": round(sideways, 4),
        "zone": zone,
        "error": err,
    }



def _strategy_history_dir():
    path = BASE_DIR / "data" / "strategy_history"
    path.mkdir(parents=True, exist_ok=True)
    return path


def _strategy_history_path(symbol, day_text=None):
    safe_symbol = re.sub(r"[^A-Za-z0-9_.-]+", "_", str(symbol or "").upper().strip()) or "UNKNOWN"
    day_text = day_text or strategy_now().strftime("%Y-%m-%d")
    return _strategy_history_dir() / f"{safe_symbol}_{day_text}.json"




def _read_strategy_history_cache(symbol, day_text=None):
    path = _strategy_history_path(symbol, day_text)
    if not path.exists():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8") or "{}")
        return data if isinstance(data, dict) else None
    except Exception as e:
        logging.debug(f"读取策略历史缓存失败 {path}: {e}")
        return None

def _prune_strategy_history_for_symbol(symbol, keep_day: str):
    """Delete all strategy cache files for the given symbol except the one matching keep_day."""
    safe_symbol = re.sub(r"[^A-Za-z0-9_.-]+", "_", str(symbol or "").upper().strip()) or "UNKNOWN"
    pattern = f"{safe_symbol}_*.json"
    for path in _strategy_history_dir().glob(pattern):
        stem = path.stem
        parts = stem.rsplit("_", 1)
        if len(parts) != 2:
            continue
        file_date = parts[1]
        if file_date != keep_day:
            try:
                path.unlink()
                logging.debug(f"已删除旧策略缓存: {path.name}")
            except Exception as e:
                logging.debug(f"删除旧策略缓存失败 {path.name}: {e}")


def _write_strategy_history_cache(symbol, record, day_text=None):
    """Write today's strategy calculation cache, then delete all older caches for the same symbol."""
    try:
        if day_text is None:
            day_text = strategy_now().strftime("%Y-%m-%d")
        path = _strategy_history_path(symbol, day_text)
        rec = {str(k): _json_safe_value(v) for k, v in (record or {}).items()}
        rec["symbol"] = str(symbol or "").upper().strip()
        rec["cache_date"] = day_text
        rec["updated_at"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_text(json.dumps(rec, ensure_ascii=False, indent=2), encoding="utf-8")
        tmp.replace(path)

        # Delete any old cache files for this symbol (only keep today's)
        _prune_strategy_history_for_symbol(symbol, day_text)

        return True
    except Exception as e:
        logging.debug(f"写入策略历史缓存失败: {e}")
        return False


def _metric_payload_to_strategy_cache(payload, cfg):
    """Convert a stored strategy-history record back to runtime values."""
    if not isinstance(payload, dict):
        return None
    ma150 = _safe_float(payload.get("ma150"), 0.0)
    ma150_raw = _safe_float(payload.get("ma150_raw"), 0.0)
    dynamic_k150 = _safe_float(payload.get("dynamic_k150"), 1.0)
    if ma150 <= 0 and ma150_raw > 0:
        ma150 = ma150_raw * dynamic_k150
    if ma150_raw <= 0 and ma150 > 0 and dynamic_k150 > 0:
        ma150_raw = ma150 / dynamic_k150
    if ma150 <= 0:
        return None
    return {
        "strategy_source_key": str(payload.get("strategy_source_key") or ""),
        "strategy_source": _display_source_name(payload.get("strategy_source") or payload.get("strategy_source_key") or ""),
        "strategy_source_fallback": bool(payload.get("strategy_source_fallback", False)),
        "strategy_status": str(payload.get("strategy_status") or ("OK" if str(payload.get("ma150_source")) == "f" else "WARN")),
        "last_bar_date": str(payload.get("last_bar_date") or payload.get("date") or ""),
        "history_count": _safe_int(payload.get("history_count", payload.get("count", 0)), 0),
        "ma150": ma150,
        "ma150_raw": ma150_raw,
        "ma150_source": str(payload.get("ma150_source") or ""),
        "sideways_score": _safe_float(payload.get("sideways_score"), 0.0),
        "dynamic_k150": dynamic_k150,
        "k150": _safe_float(payload.get("k150", cfg.get("k150", 1.0)), _safe_float(cfg.get("k150", 1.0), 1.0)),
        "attempts": payload.get("strategy_source_attempts") if isinstance(payload.get("strategy_source_attempts"), list) else [],
        "updated_at": str(payload.get("updated_at") or strategy_now().strftime("%Y-%m-%d %H:%M:%S")),
    }


def _build_strategy_calc_from_snapshot(source_key, source_label, symbol, cfg, snap, ma_short_len):
    closes = list(getattr(snap, "closes", []) or [])
    ma150_raw, ma150_source = calc_ma_with_coef(closes, ma_short_len)
    if ma150_raw is None:
        raise RuntimeError(f"历史数据不足，无法计算MA150，count={len(closes)}")
    sideways_score = float(compute_sideways_index(closes, cfg))
    base_k150 = float(cfg.get("k150", 1.0))
    min_k150 = float(cfg.get("sideways_min_k150", 0.85))
    if base_k150 < min_k150:
        min_k150 = base_k150
    dynamic_k150 = min_k150 + (base_k150 - min_k150) * (1.0 - sideways_score)
    ma150 = ma150_raw * dynamic_k150
    return {
        "strategy_source_key": source_key,
        "strategy_source": source_label or _display_source_name(source_key),
        "strategy_status": "OK" if ma150_source == "f" else "WARN",
        "last_bar_date": str(getattr(snap, "last_bar_date", "") or ""),
        "history_count": len(closes),
        "ma150": ma150,
        "ma150_raw": ma150_raw,
        "ma150_source": ma150_source,
        "sideways_score": sideways_score,
        "dynamic_k150": dynamic_k150,
        "k150": base_k150,
        "updated_at": strategy_now().strftime("%Y-%m-%d %H:%M:%S"),
    }


def _select_strategy_calc_for_symbol(symbol, cfg, market_snapshot, fetch_days, ma_short_len, quant_state=None):
    """Return the final strategy calculation result for this symbol/day.

    Result selection ignores which source produced it after calculation. The
    source is recorded for diagnosis only. Cache is per symbol + strategy date;
    when it is present, intraday loops reuse it and only realtime price is
    refreshed.
    """
    quant_state = quant_state if isinstance(quant_state, dict) else {}
    today_key = strategy_now().strftime("%Y-%m-%d")
    cached = _metric_payload_to_strategy_cache(_read_strategy_history_cache(symbol, today_key), cfg)
    if cached:
        cached["from_cache"] = True
        return cached

    # Daily failure cache: if all historical sources were already traversed today,
    # do not hammer the same sources every loop. The alert path still pushes only
    # once per day. Clear this by deleting state or waiting for the next strategy day.
    if str(quant_state.get("strategy_history_failed_date") or "") == today_key:
        cached_reason = str(quant_state.get("strategy_history_failed_reason") or "").strip()
        if cached_reason:
            raise RuntimeError(cached_reason)

    price_scale = cfg.get("price_scale", 1.0)
    selected_key = _canonical_market_source((_read_system_config_for_metrics().get("HK_BACKTEST_SOURCE") if str(symbol).upper().startswith("HK") else _read_system_config_for_metrics().get("A_BACKTEST_SOURCE")) or "")
    attempts = []
    best_partial = None
    best_partial_count = -1
    for source_key, source_label in _history_source_options_for_symbol(symbol):
        source_display = source_label or _display_source_name(source_key)
        try:
            import market_data as _market_data
            snap = _market_data.get_history_snapshot_by_source(symbol, fetch_days, price_scale=price_scale, source=source_key)
            # market_data may write source-level diagnostic snapshots as a side effect;
            # strategy_history keeps only SYMBOL_YYYY-MM-DD.json final results.
            calc = _build_strategy_calc_from_snapshot(source_key, source_display, symbol, cfg, snap, ma_short_len)
            fallback = _canonical_market_source(source_key) != selected_key
            calc["strategy_source_fallback"] = bool(fallback)
            attempts.append({
                "source_key": source_key,
                "source": source_display,
                "status": calc.get("strategy_status"),
                "ma150_source": calc.get("ma150_source"),
                "count": calc.get("history_count"),
                "last_bar_date": calc.get("last_bar_date"),
                "fallback": bool(fallback),
                "error": "",
            })
            calc["strategy_source_attempts"] = attempts[:]
            if str(calc.get("ma150_source")) == "f":
                quant_state.pop("strategy_history_failed_date", None)
                quant_state.pop("strategy_history_failed_reason", None)
                _write_strategy_history_cache(symbol, calc, today_key)
                calc["from_cache"] = False
                return calc
            count = _safe_int(calc.get("history_count", 0), 0)
            if count > best_partial_count:
                best_partial = dict(calc)
                best_partial_count = count
        except Exception as e:
            attempts.append({
                "source_key": source_key,
                "source": source_display,
                "status": "ERROR",
                "ma150_source": "",
                "count": 0,
                "last_bar_date": "",
                "fallback": _canonical_market_source(source_key) != selected_key,
                "error": str(e)[:240],
            })

    if best_partial:
        best_partial["strategy_source_attempts"] = attempts[:]
        quant_state.pop("strategy_history_failed_date", None)
        quant_state.pop("strategy_history_failed_reason", None)
        _write_strategy_history_cache(symbol, best_partial, today_key)
        best_partial["from_cache"] = False
        return best_partial

    error_text = "；".join(f"{x.get('source')}: {x.get('error') or x.get('status')}" for x in attempts) or "无可用历史数据源"
    final_error = f"全部历史数据源失败，无法计算MA150：{error_text}"
    quant_state["strategy_history_failed_date"] = today_key
    quant_state["strategy_history_failed_reason"] = final_error
    quant_state["strategy_source_attempts"] = attempts[:]
    raise RuntimeError(final_error)


def _maybe_strategy_history_alert(quant_state, msg, reason_key):
    """Push strategy-history data errors at most once per symbol per day."""
    day_key = strategy_now().strftime("%Y%m%d")
    alert_key = f"{day_key}|strategy_history_failed"
    if quant_state.get("last_strategy_history_alert_key") == alert_key:
        return []
    quant_state["last_strategy_history_alert_key"] = alert_key
    return [msg]

def refresh_source_metrics_for_symbol(name, cfg, state):
    """Refresh the final strategy metric for one symbol without source-level snapshots.

    This uses the same final-source selection path as live strategy calculation:
    default history source first, then fallback sources, preferring a complete MA150.
    It writes only the compact SYMBOL_YYYY-MM-DD strategy result cache and the
    state source_metrics card. It deliberately does not calculate/store per-source
    history snapshots such as SYMBOL_historical_a3_400_1p0_YYYY-MM-DD.json.
    """
    symbol = str((cfg or {}).get("symbol", "") or "").strip().upper()
    quant_state = state.setdefault(name, build_default_symbol_state(cfg))
    fetch_days = int(_safe_float(STRATEGY.get("fetch_history_days", 400), 400))
    ma_short_len = int(_safe_float(STRATEGY.get("ma_period_short", 150), 150))
    current_price = _safe_float(quant_state.get("last_price", 0.0), 0.0)
    try:
        strategy_calc = _select_strategy_calc_for_symbol(
            symbol, cfg, None, fetch_days, ma_short_len, quant_state=quant_state
        )
        strategy_source = _display_source_name(strategy_calc.get("strategy_source") or strategy_calc.get("strategy_source_key") or _strategy_source_for_symbol(symbol))
        if bool(strategy_calc.get("strategy_source_fallback")):
            strategy_source = f"{strategy_source}（本轮兜底）"
        ma150 = _safe_float(strategy_calc.get("ma150"), 0.0)
        ma150_raw = _safe_float(strategy_calc.get("ma150_raw"), 0.0)
        ma150_source = str(strategy_calc.get("ma150_source") or "")
        sideways_score = _safe_float(strategy_calc.get("sideways_score"), 0.0)
        dynamic_k150 = _safe_float(strategy_calc.get("dynamic_k150"), 1.0)
        base_k150 = _safe_float(strategy_calc.get("k150"), float(cfg.get("k150", 1.0)))
        strategy_status = strategy_calc.get("strategy_status") or ("OK" if ma150_source == "f" else "WARN")
        level = "INFO" if strategy_status == "OK" else "WARN"
        error = "" if ma150_source == "f" else f"策略数据为非完整口径: MA150来源={ma150_source}"
        updated_at = strategy_calc.get("updated_at") or strategy_now().strftime("%Y-%m-%d %H:%M:%S")
        quant_state["strategy_calc_cache"] = {
            "symbol": symbol,
            "strategy_source": strategy_source,
            "strategy_source_key": strategy_calc.get("strategy_source_key"),
            "strategy_source_fallback": bool(strategy_calc.get("strategy_source_fallback")),
            "strategy_status": strategy_status,
            "last_bar_date": strategy_calc.get("last_bar_date", ""),
            "ma150": ma150,
            "ma150_raw": ma150_raw,
            "ma150_source": ma150_source,
            "sideways_score": sideways_score,
            "dynamic_k150": dynamic_k150,
            "k150": base_k150,
            "history_count": _safe_int(strategy_calc.get("history_count", 0), 0),
            "strategy_source_attempts": strategy_calc.get("attempts") or strategy_calc.get("strategy_source_attempts") or [],
            "updated_at": updated_at,
        }
        quant_state["strategy_source"] = strategy_source
        quant_state["strategy_status"] = strategy_status
        quant_state["strategy_level"] = level
        quant_state["strategy_error"] = error
        quant_state["strategy_calc_updated_at"] = updated_at
        quant_state["ma_short"] = ma150
        quant_state["ma_short_source"] = ma150_source
        quant_state["dynamic_k150"] = dynamic_k150
        quant_state["sideways_score"] = sideways_score
        quant_state["k150"] = base_k150
        quant_state["history_count"] = _safe_int(strategy_calc.get("history_count", 0), 0)
        quant_state["last_valid_bar_date"] = strategy_calc.get("last_bar_date", "")
        if current_price > 0:
            quant_state["last_price"] = current_price
        quant_state["source_metrics"] = [_source_metric_from_strategy_state(symbol, cfg, quant_state)]
        quant_state["source_metrics_updated_at"] = updated_at
        quant_state["source_metrics_error"] = error
        quant_state["strategy_metrics_level"] = level
        logging.info(f"📊 已刷新本标的最终策略指标: {name} ({symbol})，源={strategy_source}，MA150={ma150_source}。")
        return quant_state["source_metrics"]
    except Exception as e:
        reason = str(e)[:500] or "全部历史数据源失败，无法计算MA150"
        updated_at = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
        metric = {
            "key": "strategy_history",
            "label": "本标的策略值",
            "ok": False,
            "level": "ERROR",
            "status": "ERROR",
            "source": "全部历史数据源",
            "date": "",
            "count": 0,
            "current_price": current_price if current_price > 0 else None,
            "ma150": None,
            "ma150_source": "",
            "sell": None,
            "clear": None,
            "dynamic_k": None,
            "sideways_score": None,
            "zone": "",
            "error": reason,
        }
        quant_state["source_metrics"] = [metric]
        quant_state["source_metrics_updated_at"] = updated_at
        quant_state["source_metrics_error"] = reason
        quant_state["strategy_metrics_level"] = "ERROR"
        quant_state["strategy_status"] = "ERROR"
        quant_state["strategy_level"] = "ERROR"
        quant_state["strategy_error"] = reason
        logging.info(f"📊 刷新本标的最终策略指标失败: {name} ({symbol})，{reason}")
        return [metric]



# ===========================
# 推送功能
# ===========================
# 推送实现已独立到 push.py；quant.py 只调用 send_notification。

# ===========================
# 辅助消息生成（与策略无关，保留在实盘中）
# ===========================
def build_status_message(name, symbol, now_str, zone, current_price, last_trade_price, last_trade_side,
                        current_units, current_avg_cost, ma150, ma150_source,
                        base_units, target_units, limit_units, sell_price, clear_price,
                        position_mode="absolute", extra_info=""):
    if last_trade_side == "buy":
        side_label = "（B）"
    elif last_trade_side == "sell":
        side_label = "（S）"
    else:
        side_label = "（B）"
    last_trade_price_msg = f"{last_trade_price:.3f}{side_label}" if last_trade_price is not None else "无"
    msg = (
        f"🟢[INFO]【{name}】 ({symbol})\n"
        f"🕒时间: {now_str}\n"
        f"🍭区间: {zone}\n"
        f"💲当前: {current_price:.3f},上次:{last_trade_price_msg}\n"
        f"⚖️持仓: {format_units_for_display(current_units, position_mode)}, 成本: {current_avg_cost:.3f}, "
        f"底仓: {format_units_for_display(base_units, position_mode)}, "
        f"补仓初始: {format_units_for_display(target_units, position_mode)}, 极限: {format_units_for_display(limit_units, position_mode)}\n"
        f"🔀MA150={ma150:.3f}({ma150_source}), Trend={sell_price:.3f}, Clear={clear_price:.3f}"
    )
    if extra_info:
        msg += f"\n{extra_info}"
    return msg

def build_trade_message(name, symbol, now_str, zone, trade_action, trade_price, trade_qty,
                       last_trade_price, last_trade_side, position_after, avg_cost_after, ma150, ma150_source,
                       base_units, target_units, limit_units, sell_price, clear_price,
                       position_mode="absolute", extra_info=""):
    action_text = str(trade_action or "")
    if "卖" in action_text:
        side_label = "（S）"
    elif "买" in action_text:
        side_label = "（B）"
    elif last_trade_side == "sell":
        side_label = "（S）"
    else:
        side_label = "（B）"
    last_trade_price_msg = f"{last_trade_price:.3f}{side_label}" if last_trade_price is not None else f"{trade_price:.3f}{side_label}"
    trade_qty_display = format_units_for_display(trade_qty, position_mode)
    msg = (
        f"🎯[TRADE]【{name}】 ({symbol})\n"
        f"🕒时间: {now_str}\n"
        f"🍭区间: {zone}\n"
        f"🗞交易: {trade_action} {trade_qty_display} @ {trade_price:.3f}\n"
        f"💲当前: {trade_price:.3f},上次: {last_trade_price_msg}\n"
        f"⚖️持仓: {format_units_for_display(position_after, position_mode)}, 成本: {avg_cost_after:.3f}, "
        f"底仓: {format_units_for_display(base_units, position_mode)}, "
        f"补仓初始: {format_units_for_display(target_units, position_mode)}, 极限: {format_units_for_display(limit_units, position_mode)}\n"
        f"🔀MA150={ma150:.3f}({ma150_source}), Trend={sell_price:.3f}, Clear={clear_price:.3f}"
    )
    if extra_info:
        msg += f"\n{extra_info}"
    return msg

def build_stop_message(name, symbol, now_str, zone, current_price, last_trade_price, last_trade_side, ma150, ma150_source, sell_price, clear_price):
    if last_trade_side == "buy":
        side_label = "（B）"
    elif last_trade_side == "sell":
        side_label = "（S）"
    else:
        side_label = "（B）"
    last_trade_price_msg = f"{last_trade_price:.3f}{side_label}" if last_trade_price is not None else f"{current_price:.3f}{side_label}"
    return (
        f"🎯[STOP]【{name}】 ({symbol})\n"
        f"🕒时间: {now_str}\n"
        f"🍭区间: {zone}\n"
        f"🛑操作: 停止所有交易\n"
        f"💲当前: {current_price:.3f},上次: {last_trade_price_msg}\n"
        f"🔀MA150={ma150:.3f}({ma150_source}), Trend={sell_price:.3f}, Clear={clear_price:.3f}"
    )

def log_trade(quant_name, symbol, price, qty, side, reason, zone=None,
              pos_before=None, pos_after=None,
              avg_cost_before=None, avg_cost_after=None,
              last_trade_price_before=None, last_trade_price_after=None,
              last_trade_side_before=None, last_trade_side_after=None,
              raw_price=None, restor_price=None,
              ma150=None, dividend=None, split_ratio=None,
              last_add_price_before=None):
    file_exists = os.path.isfile(TRADE_LOG_FILE)
    with open(TRADE_LOG_FILE, mode="a", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        if not file_exists:
            writer.writerow([
                "date",
                "quant_name",
                "symbol",
                "action",
                "price",
                "qty",
                "avg_cost_after",
                "zone",
                "reason",
                "raw_price",
                "restor_price",
                "ma150",
                "last_trade_price_before",
                "last_add_price_before",
                "dividend",
                "split_ratio",
            ])
        now_str = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
        writer.writerow([
            now_str,
            quant_name,
            symbol,
            side,
            f"{price:.3f}",
            serialize_numeric(qty),
            f"{avg_cost_after:.3f}" if avg_cost_after is not None else "",
            zone if zone is not None else "",
            reason,
            f"{raw_price:.4f}" if raw_price is not None else "",
            f"{restor_price:.4f}" if restor_price is not None else "",
            f"{ma150:.4f}" if ma150 is not None else "",
            f"{last_trade_price_before:.4f}" if last_trade_price_before is not None else "",
            f"{last_add_price_before:.4f}" if last_add_price_before is not None else "",
            f"{dividend:.6f}" if dividend is not None else "",
            f"{split_ratio:.6f}" if split_ratio is not None else "",
        ])

# ===========================
# 核心策略逻辑（调用 strategy 模块）
# ===========================

def build_no_trade_reason(zone, cfg, quant_state, state_dict, current_price, ma150, current_units,
                          base_units, target_units, limit_units, position_mode, add_reason, add_qty,
                          clear_step, last_trade_price):
    """Explain why a valid market frame did not trigger a BUY/SELL.

    Keep the reason short and user-readable: zone + action + the one key
    condition that blocked the trade + the next trigger price when available.
    """
    def pct(v):
        try:
            return f"{float(v) * 100:.2f}%"
        except Exception:
            return str(v)

    def units(v):
        return format_units_for_display(v, position_mode)

    def price_text(v):
        try:
            return f"{float(v):.3f}"
        except Exception:
            return str(v)

    try:
        cu = normalize_position_amount(current_units, position_mode)
        target = normalize_position_amount(target_units, position_mode)
        limit = normalize_position_amount(limit_units, position_mode)

        if zone == "CHANCE_ZONE":
            mode = get_pyramid_add_enabled(cfg)
            effective_mode = "yes" if mode == "auto" else mode
            if effective_mode != "yes":
                return (
                    "CHANCE_ZONE 未买入：机会倒金字塔未开启，"
                    f"当前价 {price_text(current_price)} < MA150 {price_text(ma150)}，开启后才按机会区规则加仓。"
                )

            if cu >= limit - POSITION_EPSILON:
                return (
                    "CHANCE_ZONE 未买入：当前持仓 "
                    f"{units(cu)} 已达到极限仓位 {units(limit)}，不再继续加仓。"
                )

            target_reached_once = bool(state_dict.get("target_reached_once", False))
            pyramid_step = int(state_dict.get("pyramid_step", 0) or 0)

            if not target_reached_once and pyramid_step <= 0 and cu < target - POSITION_EPSILON:
                need = normalize_position_amount(target - cu, position_mode)
                if need <= POSITION_EPSILON:
                    return (
                        "CHANCE_ZONE 未买入：当前持仓 "
                        f"{units(cu)} < 目标 {units(target)}，但差额太小，无法形成有效买入。"
                    )
                return (
                    "CHANCE_ZONE 未买入：当前持仓 "
                    f"{units(cu)} < 目标 {units(target)}，理论补仓 {units(need)}，"
                    "但本轮买入数量为 0，请检查最小交易单位或仓位配置。"
                )

            if not target_reached_once:
                step_pct = get_pyramid_add_step(cfg)
                anchor = state_dict.get("last_add_price", current_price) or current_price
                if not anchor or anchor <= 0:
                    anchor = current_price
                trigger = anchor * (1 - step_pct)
                return (
                    "CHANCE_ZONE 未买入：当前持仓 "
                    f"{units(cu)} 已达到目标仓位 {units(target)}，本轮确认倒金字塔起点；"
                    f"需价格从 {price_text(anchor)} 再下跌 {pct(step_pct)} 至 {price_text(trigger)} 或以下，"
                    "才触发第 1 步加仓。"
                )

            weights = get_pyramid_add_weights(cfg) or [1.0]
            total_steps = get_pyramid_add_steps(cfg)
            step = int(state_dict.get("pyramid_step", 0) or 0)
            if step >= total_steps:
                return (
                    "CHANCE_ZONE 未买入：倒金字塔加仓步数已用完，"
                    f"当前 {step}/{total_steps} 步。"
                )

            last_add = state_dict.get("last_add_price", current_price) or current_price
            step_pct = get_pyramid_add_step(cfg)
            trigger = last_add * (1 - step_pct)
            if current_price > trigger + POSITION_EPSILON:
                return (
                    "CHANCE_ZONE 未买入：未跌够倒金字塔加仓步长，"
                    f"当前价 {price_text(current_price)} > 触发价 {price_text(trigger)} "
                    f"（上次加仓价 {price_text(last_add)}，步长 {pct(step_pct)}，"
                    f"待加仓第 {step + 1}/{total_steps} 步）。"
                )

            weight = weights[step] if step < len(weights) else 0.0
            start_units = _safe_float(state_dict.get("pyramid_start_units", target), target)
            pyramid_budget = max(limit - start_units, 0.0)
            planned = normalize_position_amount(pyramid_budget * weight, position_mode)
            max_allowed = normalize_position_amount(limit - cu, position_mode)
            if planned <= POSITION_EPSILON or max_allowed <= POSITION_EPSILON:
                return (
                    "CHANCE_ZONE 未买入：已到加仓价，但计划买入量不足，"
                    f"本步计划 {units(planned)}，剩余空间 {units(max_allowed)}"
                    f"（加仓第 {step + 1}/{total_steps} 步）。"
                )

            return f"CHANCE_ZONE 未买入：已接近买入条件，但本轮策略买入数量为 0（加仓第 {step + 1}/{total_steps} 步）。"

        if zone == "BOX_ZONE":
            chance_trigger = ma150 if ma150 and ma150 > 0 else 0.0
            trend_trigger = ma150 * get_trend_multiple(cfg) if ma150 and ma150 > 0 else 0.0

            # 机会区倒金字塔一旦启动，回到 BOX 只代表价格反弹，低吸周期并未结束。
            # strategy.py 会继续在 BOX 中按 last_add_price 的步长判断加仓，因此快照必须
            # 优先展示这条仍在运行的链路，不能再用“箱体区不主动补仓/只等 Trend 卖出”误导。
            pyramid_active = bool(state_dict.get("pyramid_add_active", False)) or get_pyramid_add_enabled(cfg) == "yes"
            if pyramid_active:
                total_steps = get_pyramid_add_steps(cfg)
                step = min(max(int(state_dict.get("pyramid_step", 0) or 0), 0), total_steps)
                step_pct = get_pyramid_add_step(cfg)
                last_add = (
                    state_dict.get("last_add_price")
                    or state_dict.get("pyramid_anchor_price")
                    or chance_trigger
                    or current_price
                )
                try:
                    last_add = float(last_add)
                except (TypeError, ValueError):
                    last_add = float(current_price)

                cycle_end = (
                    f"；涨到 {price_text(trend_trigger)} 以上进入 TREND_ZONE。"
                    if trend_trigger > 0 else
                    "；进入 TREND_ZONE。"
                )

                if cu >= limit - POSITION_EPSILON:
                    return (
                        "BOX_ZONE 未交易：机会倒金字塔加仓周期延续中；"
                        f"当前持仓 {units(cu)} 已达极限 {units(limit)}，不再加仓；"
                        f"当前第 {step}/{total_steps} 步，上次加仓价 {price_text(last_add)}"
                        f"{cycle_end}"
                    )

                if total_steps <= 0 or step >= total_steps:
                    return (
                        "BOX_ZONE 未交易：机会倒金字塔加仓周期延续中；"
                        f"已完成 {step}/{total_steps} 步，当前持仓 {units(cu)}，极限 {units(limit)}"
                        f"{cycle_end}"
                    )

                next_trigger = last_add * (1 - step_pct) if last_add > 0 and step_pct > 0 else 0.0
                if next_trigger > 0 and current_price > next_trigger + POSITION_EPSILON:
                    return (
                        "BOX_ZONE 未交易：机会倒金字塔加仓周期延续中，"
                        f"当前价 {price_text(current_price)} > 触发价 {price_text(next_trigger)}，"
                        f"上次加仓价 {price_text(last_add)}，{pct(step_pct)} 步进，"
                        f"待加仓第 {step + 1}/{total_steps} 步；"
                        f"当前持仓 {units(cu)}，补仓初始 {units(target)}，极限 {units(limit)}"
                        f"{cycle_end}"
                    )

                if next_trigger > 0:
                    return (
                        "BOX_ZONE 未交易：机会倒金字塔加仓周期延续中，"
                        f"当前价 {price_text(current_price)} <= 触发价 {price_text(next_trigger)}，"
                        f"上次加仓价 {price_text(last_add)}，{pct(step_pct)} 步进，"
                        f"待判断第 {step + 1}/{total_steps} 步；"
                        f"当前持仓 {units(cu)}，补仓初始 {units(target)}，极限 {units(limit)}"
                        f"{cycle_end}"
                    )

                return (
                    "BOX_ZONE 未交易：机会倒金字塔加仓周期延续中；"
                    f"当前第 {step}/{total_steps} 步，上次加仓价 {price_text(last_add)}；"
                    f"当前持仓 {units(cu)}，补仓初始 {units(target)}，极限 {units(limit)}"
                    f"{cycle_end}"
                )

            if cu < target - POSITION_EPSILON:
                if chance_trigger > 0:
                    return (
                        "BOX_ZONE 未交易：机会倒金字塔尚未启动；"
                        f"当前持仓 {units(cu)} < 补仓初始仓位 {units(target)}，"
                        f"需跌破 MA150 {price_text(chance_trigger)} 进入 CHANCE_ZONE 后启动本轮低吸。"
                    )
                return (
                    "BOX_ZONE 未交易：机会倒金字塔尚未启动；"
                    f"当前持仓 {units(cu)} < 补仓初始仓位 {units(target)}，需进入 CHANCE_ZONE 后启动本轮低吸。"
                )
            if cu > target + POSITION_EPSILON:
                if trend_trigger > 0:
                    return (
                        "BOX_ZONE 未交易：当前没有延续中的机会倒金字塔加仓周期；"
                        f"当前持仓 {units(cu)} > 补仓初始仓位 {units(target)}，"
                        f"需涨到 {price_text(trend_trigger)} 或以上进入 TREND_ZONE 后才判断卖出。"
                    )
                return (
                    "BOX_ZONE 未交易：当前没有延续中的机会倒金字塔加仓周期；"
                    f"当前持仓 {units(cu)} > 补仓初始仓位 {units(target)}，需进入 TREND_ZONE 后才判断卖出。"
                )
            if chance_trigger > 0 and trend_trigger > 0:
                return (
                    "BOX_ZONE 未交易：机会倒金字塔尚未启动，"
                    f"向下跌破 MA150 {price_text(chance_trigger)} 后启动低吸周期；"
                    f"向上涨到 {price_text(trend_trigger)} 后进入 TREND_ZONE 判断卖出。"
                )
            return "BOX_ZONE 未交易：机会倒金字塔尚未启动，等待进入 CHANCE_ZONE 或 TREND_ZONE。"

        if zone == "TREND_ZONE":
            step_pct = get_trend_zone_step_percent(cfg)
            anchor = last_trade_price if last_trade_price and last_trade_price > 0 else current_price
            trigger = anchor * (1 + step_pct)
            base = normalize_position_amount(base_units, position_mode)
            excess = max(cu - base, 0.0)
            if excess <= POSITION_EPSILON:
                return (
                    "TREND_ZONE 未卖出：当前持仓 "
                    f"{units(cu)} 未超过长期底仓 {units(base)}，没有可卖出的机动仓。"
                )
            if current_price < trigger - POSITION_EPSILON:
                return (
                    "TREND_ZONE 未卖出：未涨够趋势区卖出步长，"
                    f"当前价 {price_text(current_price)} < 触发价 {price_text(trigger)} "
                    f"（锚定价 {price_text(anchor)}，步长 {pct(step_pct)}，"
                    f"每次卖出 {pct(get_trend_zone_sell_percent(cfg))} 机动仓）。"
                )
            sell_pct = get_trend_zone_sell_percent(cfg)
            planned = normalize_position_amount(min(excess, cu * sell_pct), position_mode)
            if planned <= POSITION_EPSILON:
                return (
                    "TREND_ZONE 未卖出：已到卖出价，但机动仓可卖数量太小，无法形成有效卖出"
                    f"（每次卖出 {pct(get_trend_zone_sell_percent(cfg))} 机动仓，步长 {pct(step_pct)}）。"
                )
            return (
                "TREND_ZONE 未卖出：已接近卖出条件，但本轮策略卖出数量为 0"
                f"（每次卖出 {pct(get_trend_zone_sell_percent(cfg))} 机动仓，步长 {pct(step_pct)}）。"
            )

        if zone == "CLEAR_ZONE":
            weights = get_clear_pyramid_weights(cfg)
            plan = calculate_pyramid_sell_plan(base_units, weights, position_mode, 100)
            max_steps = get_clear_pyramid_steps(cfg)
            if max_steps > 0:
                plan = plan[:max_steps]
            total_steps = len(plan)
            if total_steps <= 0:
                return "CLEAR_ZONE 未卖出：Clear区清底仓计划为空，请检查清仓步数或权重配置。"
            target_step = get_clear_pyramid_target_step(current_price, state_dict.get("clear_anchor_price") or (ma150 * get_sell_multiple(cfg)), cfg, total_steps)
            done_step = int(clear_step or 0)
            if target_step <= done_step:
                if target_step <= 0:
                    return (
                        "CLEAR_ZONE 未卖出：尚未达到第 1 步Clear触发价，"
                        f"当前应卖第 {target_step}/{total_steps} 步，已卖 {done_step}/{total_steps} 步。"
                    )
                return (
                    "CLEAR_ZONE 未卖出：未进入新的Clear清底仓步，"
                    f"当前应卖第 {target_step}/{total_steps} 步，已卖 {done_step}/{total_steps} 步。"
                )
            if cu <= POSITION_EPSILON:
                return "CLEAR_ZONE 未卖出：当前已无持仓。"
            return (
                "CLEAR_ZONE 未卖出：已进入新的Clear区间，但本轮可卖数量为 0"
                f"（应卖第 {target_step}/{total_steps} 步，已卖 {done_step}/{total_steps} 步）。"
            )

        return f"{zone or 'UNKNOWN'} 未交易：当前区间没有匹配到买入或卖出规则。"
    except Exception as e:
        return f"未触发交易条件；原因解析失败: {e}"


def append_strategy_issue_to_reason(reason, strategy_issue, ma150_source=None):
    """Append short data-quality hint without making the reason verbose."""
    reason = str(reason or "").strip() or "未触发交易。"
    issue = str(strategy_issue or "").strip()
    if not issue:
        return reason
    source = str(ma150_source or "").strip()
    if issue.startswith("MA150=") or source and source != "f":
        src = source or issue.split("=", 1)[-1].strip()
        return f"{reason}（MA150={src}，触发价为估算）"
    return f"{reason}（{issue}）"

def strategy_for_quant(name, cfg, state, allow_trade=True, allow_monitor=True, refresh_reason="", refresh_reference=False):
    symbol = cfg["symbol"]
    position_mode = get_position_mode(cfg)
    base_units = get_base_units(cfg)
    target_units = get_target_units(cfg)
    limit_units = get_limit_units(cfg)
    strategy_run = normalize_strategy_run_value(cfg.get("strategy_run", "on"), "on")
    quant_state = state.setdefault(name, build_default_symbol_state(cfg))
    quant_state = normalize_symbol_state(name, cfg, quant_state)
    tick = quant_state.get("tick", 0) + 1
    quant_state["tick"] = tick
    last_trade_price = quant_state.get("last_trade_price")
    last_trade_side = quant_state.get("last_trade_side", "buy")
    last_known_price = quant_state.get("last_price")
    current_units = normalize_position_amount(quant_state.get("current_units", base_units), position_mode)
    current_avg_cost = quant_state.get("avg_cost", 0.0)
    # Runtime state is authoritative during normal strategy loops.
    # YAML current_units/current_avg_cost are only used by build_default_symbol_state()
    # for new symbols or explicit Web reset, and must not overwrite live state here.
    price_scale = cfg.get("price_scale", 1.0)
    fetch_days = STRATEGY.get("fetch_history_days", 400)
    ma_short_len = STRATEGY.get("ma_period_short", 150)
    last_valid_price = quant_state.get("last_valid_price") or last_known_price

    try:
        snapshot = get_market_snapshot(symbol, fetch_days, price_scale=price_scale)
    except Exception as e:
        reason = f"日K获取失败: {e}"
        msg = _build_market_data_error_message(
            name, symbol, reason, last_known_price=last_valid_price
        )
        logging.info(msg)
        _mark_market_error(quant_state, msg, reason)
        write_market_skip_snapshot(name, symbol, quant_state, reason, level="ERROR", last_known_price=last_valid_price)
        return _maybe_market_alert(quant_state, msg, reason)

    # 缓存状态页参考价；交易时段内后台每轮刷新当前标的的全部实时源。
    # Web 页面仅读缓存，避免每次打开页面都直接阻塞拉行情。
    if refresh_reference:
        try:
            refs = get_reference_prices(symbol, price_scale=price_scale)
            updated_at = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
            if isinstance(refs, list) and refs:
                for _ref in refs:
                    if isinstance(_ref, dict):
                        _ref["updated_at"] = updated_at
                quant_state["reference_prices"] = refs
                quant_state["reference_prices_updated_at"] = updated_at
                quant_state["reference_prices_error"] = ""
            else:
                quant_state["reference_prices_error"] = "参考价返回为空"
        except Exception as e:
            quant_state["reference_prices_error"] = str(e)[:300]

    if not getattr(snapshot, "trade_allowed", True):
        reason = getattr(snapshot, "error", "行情来自缓存或观察源，本轮只监控不交易") or "行情来自缓存或观察源，本轮只监控不交易"
        msg = _build_market_data_error_message(
            name, symbol, reason, current_price=getattr(snapshot, "current_price", None),
            last_known_price=last_valid_price, closes_count=len(getattr(snapshot, "closes", []) or []),
            source=getattr(snapshot, "source", ""), last_bar_date=getattr(snapshot, "last_bar_date", None)
        )
        logging.warning(msg)
        _mark_market_error(quant_state, msg, reason, getattr(snapshot, "source", ""))
        write_market_skip_snapshot(
            name, symbol, quant_state, reason, level="ERROR",
            current_price=getattr(snapshot, "current_price", None),
            last_known_price=last_valid_price,
            closes_count=len(getattr(snapshot, "closes", []) or []),
            source=getattr(snapshot, "source", ""),
            last_bar_date=getattr(snapshot, "last_bar_date", None),
            trade_allowed=False,
        )
        return _maybe_market_alert(quant_state, msg, reason)

    closes = snapshot.closes
    current_price = snapshot.current_price
    if current_price <= 0:
        reason = "当前价为空或小于等于0"
        msg = _build_market_data_error_message(
            name, symbol, reason, current_price=current_price,
            last_known_price=last_valid_price, closes_count=len(closes),
            source=snapshot.source, last_bar_date=snapshot.last_bar_date
        )
        logging.info(msg)
        _mark_market_error(quant_state, msg, reason, snapshot.source)
        write_market_skip_snapshot(
            name, symbol, quant_state, reason, level="ERROR",
            current_price=current_price, last_known_price=last_valid_price,
            closes_count=len(closes), source=snapshot.source, last_bar_date=snapshot.last_bar_date,
            trade_allowed=False,
        )
        return _maybe_market_alert(quant_state, msg, reason)

    source_ok, source_reason = _check_market_source_switch(quant_state, snapshot, cfg)
    if not source_ok:
        msg = _build_market_data_warn_message(
            name, symbol, source_reason, current_price=current_price,
            last_known_price=last_valid_price, closes_count=len(closes),
            source=snapshot.source, last_bar_date=snapshot.last_bar_date
        )
        logging.warning(msg)
        _mark_market_warn(quant_state, msg, source_reason, snapshot.source)
        write_market_skip_snapshot(
            name, symbol, quant_state, source_reason, level="WARN",
            current_price=current_price, last_known_price=last_valid_price,
            closes_count=len(closes), source=snapshot.source, last_bar_date=snapshot.last_bar_date,
            trade_allowed=False,
        )
        if int(_safe_float(quant_state.get("pending_market_source_count", 0), 0)) == 1:
            try:
                send_notification(
                    f"⚠️ 行情源切换中\n"
                    f"📌标的: {name} ({symbol})\n"
                    f"📡{source_reason}\n"
                    f"⏸️ 确认期间暂停交易，连续确认后自动恢复。",
                    title=f"⚠️[SOURCE]【{name}】行情源切换"
                )
            except Exception:
                pass
        return []
    elif source_reason:
        logging.warning(f"{name} {symbol}: {source_reason}，本轮继续执行行情质量检查。")
        try:
            send_notification(
                f"🔄 行情源切换通知\n"
                f"📌标的: {name} ({symbol})\n"
                f"📡{source_reason}\n"
                f"✅ 新源已连续确认，本轮恢复交易。",
                title=f"🔄[SOURCE]【{name}】行情源切换"
            )
        except Exception:
            pass

    max_jump = _safe_float(cfg.get("max_price_jump_ratio", STRATEGY.get("max_price_jump_ratio", 0.25)), 0.25)
    suspicious, jump_ratio = _is_price_jump_suspicious(current_price, last_valid_price, max_jump)
    if suspicious:
        reason = f"当前价相对上次有效价跳变过大，ratio={jump_ratio:.3f}，阈值={max_jump:.2f}"
        msg = _build_market_data_error_message(
            name, symbol, reason,
            current_price=current_price, last_known_price=last_valid_price, closes_count=len(closes),
            source=snapshot.source, last_bar_date=snapshot.last_bar_date
        )
        logging.warning(msg)
        _mark_market_error(quant_state, msg, reason, snapshot.source)
        write_market_skip_snapshot(
            name, symbol, quant_state, reason, level="ERROR",
            current_price=current_price, last_known_price=last_valid_price,
            closes_count=len(closes), source=snapshot.source, last_bar_date=snapshot.last_bar_date,
            trade_allowed=False,
        )
        # 关键：异常行情不更新交易锚点，不触发交易。
        return _maybe_market_alert(quant_state, msg, reason)

    if len(closes) >= 2:
        suspicious_prev, prev_ratio = _is_price_jump_suspicious(current_price, closes[-2], max(max_jump, 0.35))
        if suspicious_prev:
            reason = f"当前价相对上一根日K跳变过大，ratio={prev_ratio:.3f}"
            msg = _build_market_data_error_message(
                name, symbol, reason,
                current_price=current_price, last_known_price=last_valid_price, closes_count=len(closes),
                source=snapshot.source, last_bar_date=snapshot.last_bar_date
            )
            logging.warning(msg)
            _mark_market_error(quant_state, msg, reason, snapshot.source)
            write_market_skip_snapshot(
                name, symbol, quant_state, reason, level="ERROR",
                current_price=current_price, last_known_price=last_valid_price,
                closes_count=len(closes), source=snapshot.source, last_bar_date=snapshot.last_bar_date,
                trade_allowed=False,
            )
            return _maybe_market_alert(quant_state, msg, reason)

    if last_trade_price is None or last_trade_price <= 0:
        last_trade_price = current_price
        quant_state["last_trade_price"] = current_price
        quant_state["last_trade_side"] = "buy"

    try:
        strategy_calc = _select_strategy_calc_for_symbol(
            symbol, cfg, snapshot, fetch_days, ma_short_len, quant_state=quant_state
        )
    except Exception as e:
        reason = str(e)[:500] or "全部历史数据源失败，无法计算MA150"
        msg = _build_market_data_error_message(
            name, symbol, reason,
            current_price=current_price, last_known_price=last_valid_price, closes_count=len(closes),
            source=snapshot.source, last_bar_date=snapshot.last_bar_date
        )
        logging.info(msg)
        quant_state["strategy_status"] = "ERROR"
        quant_state["strategy_level"] = "ERROR"
        quant_state["strategy_error"] = reason
        quant_state["source_metrics"] = [{
            "key": "strategy_history", "label": "本标的策略值", "ok": False, "level": "ERROR", "status": "ERROR",
            "source": "全部历史数据源", "date": getattr(snapshot, "last_bar_date", "") or "", "count": len(closes),
            "current_price": current_price, "ma150": None, "sell": None, "clear": None,
            "dynamic_k": None, "sideways_score": None, "ma150_source": "", "zone": "", "error": reason,
        }]
        quant_state["source_metrics_updated_at"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
        quant_state["source_metrics_error"] = reason
        _mark_market_error(quant_state, msg, reason, snapshot.source)
        write_market_skip_snapshot(
            name, symbol, quant_state, reason, level="ERROR",
            current_price=current_price, last_known_price=last_valid_price,
            closes_count=len(closes), source=snapshot.source, last_bar_date=snapshot.last_bar_date,
            trade_allowed=False,
        )
        return _maybe_strategy_history_alert(quant_state, msg, reason)

    strategy_source = _display_source_name(strategy_calc.get("strategy_source") or strategy_calc.get("strategy_source_key") or _strategy_source_for_symbol(symbol))
    if bool(strategy_calc.get("strategy_source_fallback")):
        strategy_source = f"{strategy_source}（本轮兜底）"
    ma150 = _safe_float(strategy_calc.get("ma150"), 0.0)
    ma150_raw = _safe_float(strategy_calc.get("ma150_raw"), 0.0)
    ma150_source = str(strategy_calc.get("ma150_source") or "")
    sideways_score = _safe_float(strategy_calc.get("sideways_score"), 0.0)
    dynamic_k150 = _safe_float(strategy_calc.get("dynamic_k150"), 1.0)
    base_k150 = _safe_float(strategy_calc.get("k150"), float(cfg.get("k150", 1.0)))
    strategy_history_count = _safe_int(strategy_calc.get("history_count", 0), len(closes))
    strategy_key = _strategy_calc_cache_key(symbol, strategy_source, strategy_calc.get("last_bar_date") or getattr(snapshot, "last_bar_date", ""), ma_short_len, cfg)
    quant_state["strategy_calc_cache"] = {
        "key": strategy_key,
        "symbol": symbol,
        "strategy_source": strategy_source,
        "strategy_source_key": strategy_calc.get("strategy_source_key"),
        "strategy_source_fallback": bool(strategy_calc.get("strategy_source_fallback")),
        "strategy_status": strategy_calc.get("strategy_status") or ("OK" if ma150_source == "f" else "WARN"),
        "last_bar_date": strategy_calc.get("last_bar_date") or getattr(snapshot, "last_bar_date", ""),
        "ma150": ma150,
        "ma150_raw": ma150_raw,
        "ma150_source": ma150_source,
        "sideways_score": sideways_score,
        "dynamic_k150": dynamic_k150,
        "k150": base_k150,
        "history_count": strategy_history_count,
        "strategy_source_attempts": strategy_calc.get("attempts") or strategy_calc.get("strategy_source_attempts") or [],
        "updated_at": strategy_calc.get("updated_at") or strategy_now().strftime("%Y-%m-%d %H:%M:%S"),
    }
    quant_state["strategy_source_attempts"] = quant_state["strategy_calc_cache"].get("strategy_source_attempts", [])
    if ma150_source and ma150_source != "f":
        strategy_status = "WARN"
        quant_state["strategy_level"] = "WARN"
        quant_state["strategy_error"] = f"策略数据为非完整口径: MA150来源={ma150_source}"
    else:
        strategy_status = "OK"
        quant_state["strategy_level"] = "INFO"
        quant_state["strategy_error"] = ""
    quant_state["strategy_source"] = strategy_source
    quant_state["strategy_status"] = strategy_status
    quant_state["strategy_calc_key"] = strategy_key
    quant_state["strategy_calc_updated_at"] = quant_state.get("strategy_calc_cache", {}).get("updated_at", strategy_now().strftime("%Y-%m-%d %H:%M:%S"))
    quant_state["ma_short"] = ma150
    quant_state["k150"] = base_k150
    quant_state["dynamic_k150"] = dynamic_k150
    quant_state["sideways_score"] = sideways_score
    quant_state["last_price"] = current_price
    _mark_market_ok(quant_state, snapshot)
    quant_state["market_source"] = _display_source_name(snapshot.source)
    quant_state["last_valid_market_source"] = _display_source_name(snapshot.source)
    quant_state["strategy_source"] = strategy_source
    quant_state["strategy_status"] = strategy_status
    quant_state["current_units"] = current_units
    quant_state["avg_cost"] = current_avg_cost
    quant_state["ma_short_source"] = ma150_source
    quant_state["source_metrics"] = [_source_metric_from_strategy_state(symbol, cfg, quant_state)]
    quant_state["source_metrics_updated_at"] = quant_state.get("strategy_calc_updated_at")
    quant_state["source_metrics_error"] = quant_state.get("strategy_error", "")
    quant_state["position_mode"] = position_mode
    if current_units > 0 and current_avg_cost == 0:
        current_avg_cost = current_price
        quant_state["avg_cost"] = current_avg_cost
    zone = get_zone(current_price, ma150, cfg)
    now_str = strategy_now().strftime("%Y.%m.%d.%H:%M")
    quant_state["last_time"] = now_str
    sell_price = ma150 * get_trend_multiple(cfg)
    clear_price = ma150 * get_sell_multiple(cfg)
    # Clear区周期规则：首次进入 CLEAR_ZONE 时锁定本轮第0步锚点；
    # 回到 TREND/BOX 不重置，后续再次进入 CLEAR 继续沿用旧步数与旧锚点；
    # 只有重新进入 CHANCE_ZONE，才说明高位周期结束，重置 Clear 清底仓状态。
    if zone == "CLEAR_ZONE":
        if not quant_state.get("clear_anchor_price") or _safe_float(quant_state.get("clear_anchor_price"), 0.0) <= 0:
            quant_state["clear_anchor_price"] = clear_price
            quant_state["clear_step"] = 0
    elif zone == "CHANCE_ZONE":
        if quant_state.get("clear_anchor_price") is not None or int(quant_state.get("clear_step", 0) or 0) != 0:
            quant_state["clear_anchor_price"] = None
            quant_state["clear_step"] = 0
    def _pct_text(value):
        return format_percent_ratio(value, digits=2)

    def _build_zone_extra_info():
        dynamic_info = f"⏳动态K={dynamic_k150:.3f}，横盘评分={sideways_score:.2f}"
        lines = []
        total_add_pyramid_steps = get_pyramid_add_steps(cfg)
        total_clear_pyramid_steps = get_clear_pyramid_steps(cfg)

        if zone == "BOX_ZONE":
            grid_status = "已开启" if get_box_grid_enabled(cfg) else "未开启"
            grid_step = _safe_float(cfg.get("grid_box_percent", 0.0), 0.0)
            grid_units = _safe_float(cfg.get("grid_box_units_percent", 0.0), 0.0)
            if get_box_grid_enabled(cfg):
                lines.append(f"📦箱体网格: {grid_status}，步长{_pct_text(grid_step)}，单次{_pct_text(grid_units)}")
            else:
                lines.append(f"📦箱体网格: {grid_status}")

            # BOX 只是不启动新的机会倒金字塔周期；如果此前 CHANCE 已激活，
            # strategy.py 会在 BOX 中继续按 last_add_price 步进，因此状态正文同步展示。
            pyramid_active = bool(quant_state.get("pyramid_add_active", False)) or get_pyramid_add_enabled(cfg) == "yes"
            if pyramid_active:
                cur_step = min(max(int(quant_state.get("pyramid_step", 0) or 0), 0), total_add_pyramid_steps)
                step_pct = get_pyramid_add_step(cfg)
                last_add = (
                    quant_state.get("last_add_price")
                    or quant_state.get("pyramid_anchor_price")
                    or ma150
                    or current_price
                )
                next_step = cur_step + 1
                if current_units >= limit_units - POSITION_EPSILON:
                    lines.append(
                        f"🧱机会倒金字塔: BOX延续中，加仓{cur_step}/{total_add_pyramid_steps}步，"
                        f"已达极限{format_units_for_display(limit_units, position_mode)}，回到BOX不重置"
                    )
                elif cur_step >= total_add_pyramid_steps or total_add_pyramid_steps <= 0:
                    lines.append(
                        f"🧱机会倒金字塔: BOX延续中，加仓{cur_step}/{total_add_pyramid_steps}步，"
                        "剩余加仓档位已用完，回到BOX不重置"
                    )
                else:
                    next_trigger = _safe_float(last_add, 0.0) * (1 - step_pct)
                    lines.append(
                        f"🧱机会倒金字塔: BOX延续中，加仓{cur_step}/{total_add_pyramid_steps}步，"
                        f"上次{_safe_float(last_add, current_price):.3f}，下一步{next_trigger:.3f}"
                        f"（第{next_step}/{total_add_pyramid_steps}步，步长{_pct_text(step_pct)}）"
                    )
        elif zone == "CHANCE_ZONE":
            pyramid_mode = get_pyramid_add_enabled(cfg)
            if pyramid_mode == "yes":
                pyramid_status = "已开启"
            elif pyramid_mode == "auto":
                pyramid_status = "已触发" if bool(quant_state.get("pyramid_add_active", False)) else "auto待触发"
            else:
                pyramid_status = "未开启"
            cur_step = int(quant_state.get("pyramid_step", 0) or 0)
            step_pct = get_pyramid_add_step(cfg)
            lines.append(f"🧱机会倒金字塔: {pyramid_status}，加仓{cur_step}/{total_add_pyramid_steps}步，步长{_pct_text(step_pct)}")
        elif zone == "TREND_ZONE":
            step_pct = _safe_float(cfg.get("trend_zone_step_percent", 0.01), 0.01)
            sell_pct = _safe_float(cfg.get("trend_zone_sell_percent", 0.05), 0.05)
            cur_step = 0
            if last_trade_price is not None and last_trade_price > 0 and step_pct > 0:
                cur_step = max(0, int((current_price - last_trade_price) / (last_trade_price * step_pct)))
            lines.append(f"📈趋势卖出: 步长{_pct_text(step_pct)}，当前{cur_step}步，单次目标{_pct_text(sell_pct)}")
        elif zone == "CLEAR_ZONE":
            pyramid_weights_for_sell = get_clear_pyramid_weights(cfg)
            sell_plan = calculate_pyramid_sell_plan(base_units, pyramid_weights_for_sell, position_mode, 100)
            if total_clear_pyramid_steps > 0:
                sell_plan = sell_plan[:total_clear_pyramid_steps]
            total_steps = len(sell_plan)
            cur_clear_step = int(quant_state.get("clear_step", 0) or 0)
            target_clear_step = get_clear_pyramid_target_step(current_price, quant_state.get("clear_anchor_price") or clear_price, cfg, total_steps)
            clear_step_pct = _safe_float(cfg.get("clear_zone_step_percent", 0.08), 0.08)
            lines.append(f"🧹Clear倒金字塔: 已卖{cur_clear_step}/{total_steps}步，目标{target_clear_step}步，步长{_pct_text(clear_step_pct)}")

        lines.append(dynamic_info)
        return "\n".join(lines)

    extra_info_full = _build_zone_extra_info()
    market_line = f"📡行情源: {_display_source_name(snapshot.source)}，数据状态: OK。"
    strategy_level_for_msg = str(quant_state.get("strategy_level") or ("WARN" if strategy_status == "WARN" else "INFO")).upper()
    strategy_issue = _short_strategy_issue(strategy_level_for_msg, quant_state.get("strategy_error", ""), ma150_source)
    strategy_line = f"🧭策略源: {strategy_source}，数据状态: {strategy_status}{('，' + strategy_issue) if strategy_issue else ''}。"
    extra_info_full = (extra_info_full + "\n" if extra_info_full else "") + market_line + "\n" + strategy_line
    status_suffix = f"\n🚦策略运行状态: {strategy_run.upper()}"
    status_msg = build_status_message(
        name=name, symbol=symbol, now_str=now_str, zone=zone,
        current_price=current_price, last_trade_price=last_trade_price, last_trade_side=last_trade_side,
        current_units=current_units, current_avg_cost=current_avg_cost,
        ma150=ma150, ma150_source=ma150_source,
        base_units=base_units, target_units=target_units, limit_units=limit_units,
        sell_price=sell_price, clear_price=clear_price,
        position_mode=position_mode, extra_info=extra_info_full
    )
    status_msg = _apply_strategy_alert_to_message(status_msg, strategy_level_for_msg, strategy_issue)
    logging.info(status_msg + "\n")
    quant_state["last_status_msg"] = status_msg
    quant_state["status_updated_at"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")

    # 价格监控与交易策略完全解耦：只消费本轮已校验的实时行情与状态，
    # 不修改仓位、不调用任何买卖决策；Web 手动刷新由 allow_monitor=False 排除。
    try:
        run_price_monitor(
            name=name,
            cfg=cfg,
            quant_state=quant_state,
            current_price=current_price,
            config_path=Path(config_path),
            allow_monitor=allow_monitor,
            message_context={
                "now_str": now_str,
                "zone": zone,
                "current_units": current_units,
                "current_avg_cost": current_avg_cost,
                "base_units": base_units,
                "target_units": target_units,
                "limit_units": limit_units,
                "position_mode": position_mode,
                "ma150": ma150,
                "ma150_source": ma150_source,
                "trend_price": sell_price,
                "clear_price": clear_price,
                "box_grid_enabled": get_box_grid_enabled(cfg),
                "grid_box_percent": _safe_float(cfg.get("grid_box_percent", 0.0), 0.0),
                "grid_box_units_percent": _safe_float(cfg.get("grid_box_units_percent", 0.0), 0.0),
                "dynamic_k150": dynamic_k150,
                "sideways_score": sideways_score,
                "market_source": _display_source_name(snapshot.source),
                "market_status": "OK",
                "strategy_source": strategy_source,
                "strategy_status": strategy_status,
            },
        )
    except Exception as e:
        logging.exception(f"{name} 价格监控执行失败: {e}")

    units_before_decision = current_units
    avg_cost_before_decision = current_avg_cost
    if not allow_trade:
        # Web 手动刷新只更新页面状态，不写入策略快照。
        # 否则 REFRESH_ONLY / “Web手动刷新，仅更新状态” 会覆盖最近一次真实
        # 策略判断，导致状态页看不到交易时段内的动态 NO_TRADE/TRADE 原因。
        quant_state["last_refresh_only_at"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
        quant_state["last_refresh_only_reason"] = refresh_reason or "manual refresh; monitor only"
        return []
    if strategy_run == "off":
        write_strategy_snapshot({
            "time": strategy_now().strftime("%Y-%m-%d %H:%M:%S"),
            "name": name, "symbol": symbol, "level": strategy_level_for_msg,
            "action": "MONITOR_ONLY", "decision": "MONITOR_ONLY",
            "reason": "strategy_run=off", "market_status": "ok",
            "market_source": _display_source_name(snapshot.source), "strategy_source": strategy_source, "strategy_status": strategy_status, "strategy_level": strategy_level_for_msg, "strategy_issue": strategy_issue, "last_bar_date": snapshot.last_bar_date,
            "history_count": len(closes), "current_price": current_price,
            "ma150": ma150, "ma150_raw": ma150_raw, "ma150_source": ma150_source,
            "dynamic_k150": dynamic_k150, "sideways_score": sideways_score,
            "zone": zone, "sell_price": sell_price, "clear_price": clear_price,
            "current_units_before": units_before_decision, "current_units_after": current_units,
            "avg_cost_before": avg_cost_before_decision, "avg_cost_after": current_avg_cost,
            "target_units": target_units, "limit_units": limit_units,
            "last_trade_price": last_trade_price, "last_trade_side": last_trade_side,
            "last_add_price": quant_state.get("last_add_price"),
            "pyramid_step": quant_state.get("pyramid_step"), "clear_step": quant_state.get("clear_step"),
            "trade_allowed": False,
        })
        return []
    messages = []
    raw_price = current_price
    restor_price = current_price
    dividend = 0.0
    split_ratio = 1.0
    # ========== 倒金字塔加仓相关状态 ==========
    pyramid_step = quant_state.get("pyramid_step", 0)
    clear_step = quant_state.get("clear_step", 0)
    last_add_price = quant_state.get("last_add_price")
    if last_add_price is None or last_add_price <= 0:
        last_add_price = current_price
    pyramid_add_active = quant_state.get("pyramid_add_active", False)
    target_reached_once = quant_state.get("target_reached_once", False)

    state_dict = {
        "current_units": current_units,
        "last_trade_price": last_trade_price,
        "last_add_price": last_add_price,
        "pyramid_anchor_price": quant_state.get("pyramid_anchor_price"),
        "pyramid_start_units": quant_state.get("pyramid_start_units"),
        "pyramid_limit_units": quant_state.get("pyramid_limit_units"),
        "pyramid_step": pyramid_step,
        "pyramid_add_active": pyramid_add_active,
        "target_reached_once": target_reached_once,
        "clear_step": clear_step,
        "clear_anchor_price": quant_state.get("clear_anchor_price"),
    }

    # ========== 加仓决策（统一由 strategy.py 决定） ==========
    add_qty = 0.0
    add_reason = ""
    add_qty, add_reason, add_state, cfg_updates, add_events = get_add_trade_decision(
        state_dict, cfg, target_units, limit_units, current_price, ma150, zone, position_mode, 100
    )
    if cfg_updates.get("pyramid_add_enabled") in {"yes", "auto"} and cfg.get("pyramid_add_enabled") != cfg_updates.get("pyramid_add_enabled"):
        cfg["pyramid_add_enabled"] = cfg_updates["pyramid_add_enabled"]
        persist_runtime_position_to_config(name, current_units, current_avg_cost)
    for _evt in add_events:
        if _evt == "PYRAMID_AUTO_TRIGGERED":
            logging.info(f"[{now_str}] 倒金字塔加仓已激活（价格跌破MA150）")
        elif _evt in {"PYRAMID_SWITCH_TO_AUTO", "PYRAMID_RESET_TO_TREND"}:
            logging.info(f"[{now_str}] 倒金字塔加仓已切回 auto 模式（进入趋势/Clear区）")
    if add_qty > 0:
        new_avg_cost = calculate_new_avg_cost(current_units, current_avg_cost, add_qty, current_price)
        after_units = normalize_position_amount(current_units + add_qty, position_mode)
        record_trade_state_backup(name, symbol, quant_state, cfg, {
            "side": "BUY", "reason": add_reason, "zone": zone,
            "price": current_price, "qty": add_qty,
            "pos_before": current_units, "pos_after": after_units,
            "avg_cost_before": current_avg_cost, "avg_cost_after": new_avg_cost,
            "last_trade_price_before": last_trade_price,
            "last_trade_side_before": last_trade_side,
            "last_add_price_before": last_add_price,
        })
        log_trade(
            quant_name=name, symbol=symbol, price=current_price, qty=add_qty, side="BUY",
            reason=add_reason, zone=zone,
            pos_before=current_units, pos_after=after_units,
            avg_cost_before=current_avg_cost, avg_cost_after=new_avg_cost,
            last_trade_price_before=last_trade_price, last_trade_price_after=current_price,
            last_trade_side_before=last_trade_side, last_trade_side_after="buy",
            raw_price=raw_price, restor_price=restor_price,
            ma150=ma150, dividend=dividend, split_ratio=split_ratio,
            last_add_price_before=last_add_price,
        )
        current_units = after_units
        current_avg_cost = new_avg_cost
        quant_state["current_units"] = current_units
        quant_state["avg_cost"] = current_avg_cost
        quant_state["last_trade_price"] = current_price
        quant_state["last_trade_side"] = "buy"
        quant_state["pyramid_step"] = add_state.get("pyramid_step", pyramid_step)
        quant_state["last_add_price"] = add_state.get("last_add_price", last_add_price)
        quant_state["pyramid_anchor_price"] = add_state.get("pyramid_anchor_price", quant_state.get("pyramid_anchor_price"))
        quant_state["pyramid_start_units"] = add_state.get("pyramid_start_units", quant_state.get("pyramid_start_units"))
        quant_state["pyramid_limit_units"] = add_state.get("pyramid_limit_units", quant_state.get("pyramid_limit_units"))
        quant_state["target_reached_once"] = add_state.get("target_reached_once", target_reached_once)
        quant_state["pyramid_add_active"] = add_state.get("pyramid_add_active", pyramid_add_active)
        persist_runtime_position_to_config(name, current_units, current_avg_cost)
        extra_info = f"🏛{add_reason}: {format_units_for_display(add_qty, position_mode)}\n⏳动态K={dynamic_k150:.3f}，横盘评分={sideways_score:.2f}"
        trade_msg = build_trade_message(
            name=name, symbol=symbol, now_str=now_str, zone=zone,
            trade_action="买入", trade_price=current_price, trade_qty=add_qty,
            last_trade_price=last_trade_price, last_trade_side=last_trade_side,
            position_after=after_units, avg_cost_after=new_avg_cost,
            ma150=ma150, ma150_source=ma150_source,
            base_units=base_units, target_units=target_units, limit_units=limit_units,
            sell_price=sell_price, clear_price=clear_price,
            position_mode=position_mode, extra_info=extra_info
        )
        trade_msg = _apply_strategy_alert_to_message(trade_msg, strategy_level_for_msg, strategy_issue)
        logging.info(trade_msg)
        messages.append(trade_msg)
    state_dict.update(add_state)
    # 即使本轮未成交，也保存机会区倒金字塔的运行锚点。
    # 这能保证中途加入标的后，后续继续以 MA150 第0步和已追认步数推进。
    for _k in ("pyramid_step", "last_add_price", "pyramid_anchor_price", "pyramid_start_units", "pyramid_limit_units", "pyramid_add_active", "target_reached_once"):
        if _k in add_state:
            quant_state[_k] = add_state.get(_k)
    pyramid_step = quant_state.get("pyramid_step", pyramid_step)
    clear_step = quant_state.get("clear_step", clear_step)
    last_add_price = quant_state.get("last_add_price", last_add_price)

    # ========== 卖出决策 ==========
    if zone == "TREND_ZONE":
        sell_qty, new_state = get_trend_sell_decision(
            state_dict, cfg, base_units, position_mode, current_price, ma150, 100
        )
        if sell_qty > 0:
            after_units = normalize_position_amount(current_units - sell_qty, position_mode)
            record_trade_state_backup(name, symbol, quant_state, cfg, {
                "side": "SELL", "reason": "TREND_ZONE_SELL", "zone": "TREND_ZONE",
                "price": current_price, "qty": sell_qty,
                "pos_before": current_units, "pos_after": after_units,
                "avg_cost_before": current_avg_cost, "avg_cost_after": current_avg_cost,
                "last_trade_price_before": last_trade_price,
                "last_trade_side_before": last_trade_side,
                "last_add_price_before": last_add_price,
            })
            log_trade(
                quant_name=name, symbol=symbol, price=current_price, qty=sell_qty, side="SELL",
                reason="TREND_ZONE_SELL", zone="TREND_ZONE",
                pos_before=current_units, pos_after=after_units,
                avg_cost_before=current_avg_cost, avg_cost_after=current_avg_cost,
                last_trade_price_before=last_trade_price, last_trade_price_after=current_price,
                last_trade_side_before=last_trade_side, last_trade_side_after="sell",
                raw_price=raw_price, restor_price=restor_price,
                ma150=ma150, dividend=dividend, split_ratio=split_ratio,
                last_add_price_before=last_add_price,
            )
            current_units = after_units
            quant_state["current_units"] = current_units
            quant_state["last_trade_price"] = current_price
            quant_state["last_trade_side"] = "sell"
            last_trade_price = new_state.get("last_trade_price", last_trade_price)
            persist_runtime_position_to_config(name, current_units, current_avg_cost)
            extra_info = f"🎯趋势区卖出机动仓: {format_units_for_display(sell_qty, position_mode)}\n⏳动态K={dynamic_k150:.3f}，横盘评分={sideways_score:.2f}"
            trade_msg = build_trade_message(
                name=name, symbol=symbol, now_str=now_str, zone="TREND_ZONE",
                trade_action="卖出", trade_price=current_price, trade_qty=sell_qty,
                last_trade_price=last_trade_price, last_trade_side=last_trade_side,
                position_after=after_units, avg_cost_after=current_avg_cost,
                ma150=ma150, ma150_source=ma150_source,
                base_units=base_units, target_units=target_units, limit_units=limit_units,
                sell_price=sell_price, clear_price=clear_price,
                position_mode=position_mode, extra_info=extra_info
            )
            trade_msg = _apply_strategy_alert_to_message(trade_msg, strategy_level_for_msg, strategy_issue)
            logging.info(trade_msg)
            messages.append(trade_msg)
    elif zone == "CLEAR_ZONE":
        pyramid_weights = get_clear_pyramid_weights(cfg)
        sell_plan = calculate_pyramid_sell_plan(base_units, pyramid_weights, position_mode, 100)
        clear_steps_cfg = get_clear_pyramid_steps(cfg)
        if clear_steps_cfg > 0:
            sell_plan = sell_plan[:clear_steps_cfg]
        total_steps = len(sell_plan)
        target_step = get_clear_pyramid_target_step(current_price, state_dict.get("clear_anchor_price") or (ma150 * get_sell_multiple(cfg)), cfg, total_steps)
        if target_step > clear_step:
            for step_info in sell_plan[clear_step:target_step]:
                step = step_info["step"]
                sell_units = min(step_info["units"], current_units)
                if sell_units <= POSITION_EPSILON:
                    clear_step = step
                    continue
                after_units = normalize_position_amount(current_units - sell_units, position_mode)
                record_trade_state_backup(name, symbol, quant_state, cfg, {
                    "side": "SELL", "reason": f"CLEAR_ZONE_PYRAMID_STEP_{step}", "zone": "CLEAR_ZONE",
                    "price": current_price, "qty": sell_units,
                    "pos_before": current_units, "pos_after": after_units,
                    "avg_cost_before": current_avg_cost, "avg_cost_after": current_avg_cost,
                    "last_trade_price_before": last_trade_price,
                    "last_trade_side_before": last_trade_side,
                    "last_add_price_before": last_add_price,
                    "clear_step_before": clear_step,
                    "clear_step_after": step,
                })
                log_trade(
                    quant_name=name, symbol=symbol, price=current_price, qty=sell_units, side="SELL",
                    reason=f"CLEAR_ZONE_PYRAMID_STEP_{step}", zone="CLEAR_ZONE",
                    pos_before=current_units, pos_after=after_units,
                    avg_cost_before=current_avg_cost, avg_cost_after=current_avg_cost,
                    last_trade_price_before=last_trade_price, last_trade_price_after=current_price,
                    last_trade_side_before=last_trade_side, last_trade_side_after="sell",
                    raw_price=raw_price, restor_price=restor_price,
                    ma150=ma150, dividend=dividend, split_ratio=split_ratio,
                    last_add_price_before=last_add_price,
                )
                current_units = after_units
                quant_state["current_units"] = current_units
                quant_state["last_trade_price"] = current_price
                quant_state["last_trade_side"] = "sell"
                clear_step = step
                quant_state["clear_step"] = clear_step
                persist_runtime_position_to_config(name, current_units, current_avg_cost)
                extra_info = f"🧹Clear区倒金字塔清底仓: 第{step}步 ({step_info['weight_percent']:.1f}%)\n{format_units_for_display(sell_units, position_mode)}\n⏳动态K={dynamic_k150:.3f}，横盘评分={sideways_score:.2f}"
                trade_msg = build_trade_message(
                    name=name, symbol=symbol, now_str=now_str, zone="CLEAR_ZONE",
                    trade_action="卖出", trade_price=current_price, trade_qty=sell_units,
                    last_trade_price=last_trade_price, last_trade_side=last_trade_side,
                    position_after=after_units, avg_cost_after=current_avg_cost,
                    ma150=ma150, ma150_source=ma150_source,
                    base_units=base_units, target_units=target_units, limit_units=limit_units,
                    sell_price=sell_price, clear_price=clear_price,
                    position_mode=position_mode, extra_info=extra_info
                )
                trade_msg = _apply_strategy_alert_to_message(trade_msg, strategy_level_for_msg, strategy_issue)
                logging.info(trade_msg)
                messages.append(trade_msg)
                if current_units <= POSITION_EPSILON:
                    break

    # 交易态字段只在真实 BUY/SELL 分支内写入；普通 NO_TRADE 不回写
    # last_add_price/pyramid_step/clear_step/pyramid_add_active/target_reached_once。
    action = "TRADE" if messages else "NO_TRADE"
    if messages:
        reason = "; ".join([line.split("🗞交易:", 1)[-1].strip() for line in messages if "🗞交易:" in line])
    else:
        reason = build_no_trade_reason(
            zone, cfg, quant_state, state_dict, current_price, ma150, current_units,
            base_units, target_units, limit_units, position_mode, add_reason, add_qty,
            clear_step, last_trade_price
        )
    reason = append_strategy_issue_to_reason(reason, strategy_issue, ma150_source)
    write_strategy_snapshot({
        "time": strategy_now().strftime("%Y-%m-%d %H:%M:%S"),
        "name": name, "symbol": symbol, "level": strategy_level_for_msg,
        "action": action, "decision": action, "reason": reason,
        "trade_count": len(messages),
        "market_status": "ok", "market_source": _display_source_name(snapshot.source),
        "strategy_source": strategy_source, "strategy_status": strategy_status, "strategy_level": strategy_level_for_msg, "strategy_issue": strategy_issue,
        "last_bar_date": snapshot.last_bar_date, "history_count": len(closes),
        "current_price": current_price, "ma150": ma150, "ma150_raw": ma150_raw,
        "ma150_source": ma150_source, "dynamic_k150": dynamic_k150,
        "sideways_score": sideways_score, "zone": zone,
        "sell_price": sell_price, "clear_price": clear_price,
        "current_units_before": units_before_decision, "current_units_after": current_units,
        "avg_cost_before": avg_cost_before_decision, "avg_cost_after": current_avg_cost,
        "base_units": base_units, "target_units": target_units, "limit_units": limit_units,
        "last_trade_price": quant_state.get("last_trade_price"),
        "last_trade_side": quant_state.get("last_trade_side"),
        "last_add_price": quant_state.get("last_add_price"),
        "pyramid_step": quant_state.get("pyramid_step"),
        "pyramid_add_active": quant_state.get("pyramid_add_active"),
        "target_reached_once": quant_state.get("target_reached_once"),
        "clear_step": quant_state.get("clear_step"),
        "trade_allowed": True,
    })
    return messages

# ===========================
# 日志清理函数
# ===========================
def clean_old_quant_logs(log_dir: str, keep: int = 7, filename_pattern: str = r"^quant\.(\d{8})\.log$"):
    if keep <= 0:
        keep = 0
    if not os.path.isdir(log_dir):
        logging.warning(f"⚠️ 日志目录不存在，跳过清理: {log_dir}")
        return [], []
    rx = re.compile(filename_pattern)
    candidates = []
    for fn in os.listdir(log_dir):
        m = rx.match(fn)
        if not m:
            continue
        date_str = m.group(1)
        try:
            dt = datetime.strptime(date_str, "%Y%m%d")
        except ValueError:
            continue
        full_path = os.path.join(log_dir, fn)
        candidates.append((dt, full_path))
    candidates.sort(key=lambda x: x[0], reverse=True)
    kept = [p for _, p in candidates[:keep]]
    to_remove = [p for _, p in candidates[keep:]]
    removed = []
    for path in to_remove:
        try:
            os.remove(path)
            removed.append(path)
        except Exception as e:
            logging.error(f"❌ 删除旧日志失败: {path} | {e}")
    if candidates:
        logging.info(f"🧹 日志清理完成：共匹配 {len(candidates)} 份，保留 {len(kept)} 份，删除 {len(removed)} 份")
        for p in removed:
            logging.info(f"🗑️ 已删除旧日志: {os.path.basename(p)}")
    else:
        logging.info("🧹 日志清理：未发现符合 quant.YYYYMMDD.log 格式的日志，无需清理")
    return kept, removed

# ===========================
# 主循环
# ===========================
def main_loop():
    logging.info("=" * 60)
    logging.info("Quant策略启动完成")
    logging.info(f"当前时间: {strategy_now().strftime('%Y-%m-%d %H:%M:%S')}")
    logging.info("=" * 60)
    config_path = os.path.join(BASE_DIR, "quant.yaml")
    global SYMBOL_CONFIG, STRATEGY, FULL_CONFIG
    SYMBOL_CONFIG, STRATEGY_from_conf, FULL_CONFIG = load_config(config_path)
    STRATEGY.update(STRATEGY_from_conf)
    logging.info(f"策略时区: {get_strategy_timezone_name()}，服务器时区不影响 session_start/session_end/daily_push_time/log_rotate_time")
    logging.info("📌 各标的策略运行状态:")
    for name, cfg in SYMBOL_CONFIG.items():
        if not isinstance(cfg, dict):
            logging.error(f"配置项 {name} 不是字典，类型为 {type(cfg)}，已跳过。请检查 quant.yaml 格式。")
            continue
        strategy_run = normalize_strategy_run_value(cfg.get("strategy_run", "on"), "on")
        status_icon = "🟢" if strategy_run == "on" else "🔴"
        logging.info(f" {status_icon} {name}: {strategy_run.upper()}")
    logging.info("=" * 60)
    state = load_state()
    last_config_reload_seq = _safe_int(state.get("_meta", {}).get("config_reload_seq", 0), 0)
    last_system_config_seq = _safe_int(state.get("_meta", {}).get("system_config_seq", 0), 0)
    while True:
        SYMBOL_CONFIG, STRATEGY_from_conf, FULL_CONFIG = load_config(config_path)
        STRATEGY.update(STRATEGY_from_conf)
        for _stale_name in list(state.keys()):
            if _stale_name != "_meta" and _stale_name not in SYMBOL_CONFIG and isinstance(state.get(_stale_name), dict):
                state.pop(_stale_name, None)
                logging.info(f"🧹 已清理已删除标的运行状态: {_stale_name}")
        last_config_reload_seq = apply_runtime_config_reload_if_needed(state, last_config_reload_seq)
        last_system_config_seq = apply_system_config_update_if_needed(state, last_system_config_seq)
        force_refresh, force_refresh_seq, force_refresh_targets = read_force_refresh_request(state)
        restore_rerun, restore_rerun_seq, restore_rerun_targets, restore_rerun_backup_id = read_restore_trade_rerun_request(state)
        source_metrics_refresh, source_metrics_seq, source_metrics_targets = read_source_metrics_refresh_request(state)
        apply_market_state_clear_if_needed(state)
        # clear-market-state may also be paired with a force refresh; re-read after clearing.
        force_refresh, force_refresh_seq, force_refresh_targets = read_force_refresh_request(state)
        restore_rerun, restore_rerun_seq, restore_rerun_targets, restore_rerun_backup_id = read_restore_trade_rerun_request(state)
        now = strategy_now()
        # 日志轮转
        if should_rotate_logs(state, now):
            logging.info("=" * 60)
            logging.info(f"🔄 开始执行日志轮转 - {now.strftime('%Y-%m-%d %H:%M:%S')}")
            logging.info("=" * 60)
            rotate_success = rotate_and_backup_logs(now)
            if rotate_success:
                log_dir = os.path.join(BASE_DIR, "log")
                try:
                    clean_old_quant_logs(log_dir=log_dir, keep=7)
                except Exception as e:
                    logging.exception(f"❌ 执行日志清理函数失败: {e}")

                # 清理非当日的策略缓存文件（全局）
                try:
                    prune_strategy_history_cache()
                    logging.info("🧹 已清理旧策略缓存文件（仅保留今日）")
                except Exception as e:
                    logging.exception(f"❌ 清理策略缓存失败: {e}")

                try:
                    import subprocess
                    back_py = BASE_DIR / "backup.py"
                    if back_py.exists():
                        subprocess.run([sys.executable, str(back_py)], capture_output=True, timeout=60)
                        logging.info("📦 运行数据已备份到 /mnt/rclone/quant")
                except Exception as e:
                    logging.warning(f"📦 运行数据备份失败: {e}")

                snapshot = build_daily_snapshot(state)
                logging.info("=" * 60)
                logging.info("📌每日快照内容:")
                logging.info("=" * 60)
                logging.info(snapshot)
                logging.info("=" * 60)
                try:
                    send_notification(snapshot, title="每日快照")
                    logging.info("✅ 每日快照推送成功")
                except Exception as e:
                    logging.error(f"❌ 推送每日快照失败: {e}")

                state["_meta"]["last_log_rotate_date"] = now.date().isoformat()
                state["_meta"]["last_daily_push_date"] = now.date().isoformat()
                save_state(state)

                logging.info("=" * 60)
                logging.info("✅ 日志轮转与快照推送完成")
                logging.info("🕒 下次轮转时间: 明天 08:00")
                logging.info("=" * 60)

        # 非交易时段：严格按配置的交易时段工作。
        # Web 手动状态刷新 / 指标刷新在盘外只登记为已跳过，不生成状态文本、不拉实时行情、不写策略快照。
        in_session = in_trade_session(now)
        if not in_session:
            if force_refresh:
                state.setdefault("_meta", {})["force_refresh_done_seq"] = force_refresh_seq
                state.setdefault("_meta", {})["force_refresh_done_at"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
                state.setdefault("_meta", {})["force_refresh_skip_reason"] = (
                    f"非交易时段，已跳过 Web 手动刷新；当前策略时间 {now.strftime('%Y-%m-%d %H:%M:%S')}，"
                    f"交易时段 {STRATEGY.get('session_start', '09:30')}-{STRATEGY.get('session_end', '16:00')}"
                )
                save_state(state)
                logging.info(
                    f"⏸️ 非交易时段，跳过 Web 手动刷新 seq={force_refresh_seq}，"
                    f"当前策略时间={now.strftime('%Y-%m-%d %H:%M:%S')}，"
                    f"交易时段={STRATEGY.get('session_start', '09:30')}-{STRATEGY.get('session_end', '16:00')}。"
                )
            if source_metrics_refresh:
                state.setdefault("_meta", {})["source_metrics_refresh_done_seq"] = source_metrics_seq
                state.setdefault("_meta", {})["source_metrics_refresh_done_at"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
                state.setdefault("_meta", {})["source_metrics_refresh_skip_reason"] = (
                    f"非交易时段，已跳过回测/策略指标刷新；当前策略时间 {now.strftime('%Y-%m-%d %H:%M:%S')}，"
                    f"交易时段 {STRATEGY.get('session_start', '09:30')}-{STRATEGY.get('session_end', '16:00')}"
                )
                save_state(state)
                logging.info(
                    f"⏸️ 非交易时段，跳过回测/策略指标刷新 seq={source_metrics_seq}，"
                    f"当前策略时间={now.strftime('%Y-%m-%d %H:%M:%S')}，"
                    f"交易时段={STRATEGY.get('session_start', '09:30')}-{STRATEGY.get('session_end', '16:00')}。"
                )
            if restore_rerun:
                meta = state.setdefault("_meta", {})
                meta["restore_trade_rerun_done_seq"] = restore_rerun_seq
                meta["restore_trade_rerun_done_at"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
                meta["restore_trade_rerun_skip_reason"] = (
                    f"非交易时段，已恢复回滚点但未立即执行策略；当前策略时间 {now.strftime('%Y-%m-%d %H:%M:%S')}，"
                    f"交易时段 {STRATEGY.get('session_start', '09:30')}-{STRATEGY.get('session_end', '16:00')}"
                )
                save_state(state)
                logging.info(
                    f"⏸️ 非交易时段，已恢复回滚点但跳过立即重跑 seq={restore_rerun_seq}，"
                    f"目标={','.join(restore_rerun_targets) or 'ALL'}。"
                )

            sleep_until_next_loop_or_web_request(state, STRATEGY.get("loop_interval", 60))
            continue

        if restore_rerun:
            logging.info("=" * 60)
            logging.info(
                f"↩️ 回滚点已恢复，立即按当前价重跑策略 seq={restore_rerun_seq}，"
                f"回滚点={restore_rerun_backup_id}，目标={','.join(restore_rerun_targets) or 'ALL'}。"
            )
            logging.info("=" * 60)
            restore_trade_msgs = []
            restore_error_msgs = []
            for _name in restore_rerun_targets:
                _cfg = SYMBOL_CONFIG.get(_name)
                if not isinstance(_cfg, dict):
                    continue
                try:
                    msgs = strategy_for_quant(
                        _name, _cfg, state,
                        allow_trade=True,
                        allow_monitor=False,
                        refresh_reason="回滚后按当前价重新执行策略",
                        refresh_reference=True,
                    )
                    for msg in msgs or []:
                        text = str(msg)
                        if "🎯[TRADE]" in text:
                            restore_trade_msgs.append(text)
                        elif "🎯[ERROR]" in text:
                            restore_error_msgs.append(text)
                        else:
                            logging.info(f"回滚后重跑非交易消息未推送: {text[:160]}")
                except Exception as e:
                    logging.exception(f"{_name} 回滚后重跑策略出错: {e}")
            meta = state.setdefault("_meta", {})
            meta["restore_trade_rerun_done_seq"] = restore_rerun_seq
            meta["restore_trade_rerun_done_at"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
            meta["restore_trade_rerun_done_backup_id"] = restore_rerun_backup_id
            save_state(state)
            if restore_trade_msgs:
                body = (chr(10) * 2).join(restore_trade_msgs)
                logging.info("=" * 60)
                logging.info("📨 回滚后重跑触发交易推送:")
                logging.info("=" * 60)
                logging.info(body)
                try:
                    trade_sent = send_notification(body)
                    if trade_sent:
                        logging.info("✅ 回滚后重跑交易推送成功")
                    else:
                        logging.error("❌ 回滚后重跑交易推送失败")
                except Exception as e:
                    logging.error(f"❌ 回滚后重跑交易推送失败: {e}")
            if restore_error_msgs:
                body = (chr(10) * 2).join(restore_error_msgs)
                try:
                    send_notification(body)
                except Exception as e:
                    logging.error(f"❌ 回滚后重跑错误推送失败: {e}")
            sleep_until_next_loop_or_web_request(state, STRATEGY.get("loop_interval", 60))
            continue

        if source_metrics_refresh:
            logging.info("=" * 60)
            logging.info(f"📊 收到 Web 回测/策略数据源刷新请求 seq={source_metrics_seq}，目标={','.join(source_metrics_targets) or 'ALL'}，仅计算指标，不触发交易。")
            logging.info("=" * 60)
            for _name in source_metrics_targets:
                _cfg = SYMBOL_CONFIG.get(_name)
                if isinstance(_cfg, dict):
                    try:
                        refresh_source_metrics_for_symbol(_name, _cfg, state)
                    except Exception as e:
                        logging.exception(f"{_name} 回测/策略数据源指标刷新失败: {e}")
            state.setdefault("_meta", {})["source_metrics_refresh_done_seq"] = source_metrics_seq
            state.setdefault("_meta", {})["source_metrics_refresh_done_at"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
            save_state(state)
            logging.info(f"✅ 回测/策略数据源指标刷新完成 seq={source_metrics_seq}，目标={','.join(source_metrics_targets) or 'ALL'}。")
            sleep_until_next_loop_or_web_request(state, STRATEGY.get("loop_interval", 60))
            continue

        if force_refresh:
            logging.info("=" * 60)
            logging.info(f"🔄 收到 Web 手动刷新请求 seq={force_refresh_seq}，目标={','.join(force_refresh_targets) or 'ALL'}，本轮只刷新行情/状态，不触发交易。")
            logging.info("=" * 60)

        loop_enabled = str(STRATEGY.get("loop_enabled", "yes") or "yes")
        if loop_enabled.lower() in ("no", "off", "false", "0"):
            loop_enabled = False
        else:
            loop_enabled = True

        # 策略执行
        all_trade_msgs = []
        all_market_error_msgs = []
        iter_items = [(name, cfg) for name, cfg in SYMBOL_CONFIG.items() if (not force_refresh or name in force_refresh_targets)]
        for name, cfg in iter_items:
            if not isinstance(cfg, dict):
                logging.error(f"配置项 {name} 不是字典，类型为 {type(cfg)}，已跳过。")
                continue
            try:
                msgs = strategy_for_quant(
                    name, cfg, state,
                    allow_trade=not force_refresh and loop_enabled,
                    allow_monitor=not force_refresh,
                    refresh_reason="Web手动刷新，仅更新状态",
                    refresh_reference=True,
                )
                for msg in msgs or []:
                    text = str(msg)
                    if "🎯[TRADE]" in text:
                        all_trade_msgs.append(text)
                    elif "🎯[ERROR]" in text:
                        all_market_error_msgs.append(text)
                    else:
                        logging.info(f"非交易消息未推送: {text[:160]}")
            except Exception as e:
                logging.exception(f"{name} 策略执行出错: {e}")

        if force_refresh:
            state.setdefault("_meta", {})["force_refresh_done_seq"] = force_refresh_seq
            state.setdefault("_meta", {})["force_refresh_done_at"] = strategy_now().strftime("%Y-%m-%d %H:%M:%S")
            save_state(state)
            logging.info(f"✅ Web 手动刷新完成 seq={force_refresh_seq}，目标={','.join(force_refresh_targets) or 'ALL'}，未触发任何交易推送。")
            sleep_until_next_loop_or_web_request(state, STRATEGY.get("loop_interval", 60))
            continue

        if not loop_enabled:
            save_state(state)
            sleep_until_next_loop_or_web_request(state, STRATEGY.get("loop_interval", 60))
            continue

        save_state(state)

        # 推送交易信号：只有真正 TRADE 才进入买卖推送
        if all_trade_msgs:
            body = (chr(10) * 2).join(all_trade_msgs)
            logging.info("=" * 60)
            logging.info("📨 推送买卖信号:")
            logging.info("=" * 60)
            logging.info(body)
            try:
                # 从第一条消息提取标题信息
                first_msg = all_trade_msgs[0] if all_trade_msgs else ""
                import re
                symbol_match = re.search(r'【(.+?)】', first_msg)
                trade_match = re.search(r'🗞交易: (.+?)(?:\n|$)', first_msg)

                if symbol_match and trade_match:
                    trade_title = f"🎯[TRADE]{symbol_match.group(0)} 🗞交易: {trade_match.group(1).strip()}"
                else:
                    trade_title = "🎯[TRADE]"
                record_push_detail("trade", body)
                trade_sent = send_notification(body, title=trade_title)
                if trade_sent:
                    logging.info("✅ 买卖信号推送成功")
                else:
                    logging.error("❌ 买卖信号推送失败")
            except Exception:
                logging.exception("❌ 推送买卖信号失败")
            logging.info("=" * 60)

        # 推送行情错误：仅全部数据源失败且已按当天去重后的 ERROR 会到这里
        if all_market_error_msgs:
            body = (chr(10) * 2).join(all_market_error_msgs)
            logging.info("=" * 60)
            logging.info("📨 推送行情错误:")
            logging.info("=" * 60)
            logging.info(body)
            try:
                record_push_detail("market_error", body)
                error_sent = send_notification(body)
                if error_sent:
                    logging.info("✅ 行情错误推送成功")
                else:
                    logging.error("❌ 行情错误推送失败")
            except Exception:
                logging.exception("❌ 推送行情错误失败")
            logging.info("=" * 60)

        sleep_until_next_loop_or_web_request(state, STRATEGY.get("loop_interval", 60))

if __name__ == "__main__":
    try:
        main_loop()
    except KeyboardInterrupt:
        logging.info("用户中断程序执行")
    except Exception as e:
        logging.exception(f"程序异常退出: {e}")
