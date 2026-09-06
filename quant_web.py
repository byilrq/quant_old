#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import annotations

import ast
import csv
import json
import logging
import re
import secrets
import subprocess
import sys
from copy import deepcopy
from datetime import datetime, time as dt_time
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError
from pathlib import Path
from io import BytesIO
from zipfile import ZipFile, ZIP_DEFLATED
from typing import Any, Dict, List, Tuple

from flask import (
    Flask,
    abort,
    flash,
    jsonify,
    redirect,
    render_template,
    request,
    send_file,
    session,
    url_for,
)
from ruamel.yaml import YAML
from ruamel.yaml.constructor import DuplicateKeyError
from ruamel.yaml.scalarstring import DoubleQuotedScalarString
import yaml as pyyaml
from werkzeug.security import check_password_hash

from push import (
    PUSH_CONFIG_FILE,
    PUSH_LOG_FILE,
    PUSH_LOG_KEEP_LINES,
    PUSH_DEFAULTS,
    PUSH_CHANNEL_VALUES,
    load_push_config as read_push_config,
    write_push_config,
    read_push_logs,
    send_push_test,
    send_notification,
)

try:
    from market_data import (
        get_all_source_options as market_get_all_source_options,
        get_source_options as market_get_source_options,
        get_source_display_name as market_get_source_display_name,
        get_reference_price_by_source as market_get_reference_price_by_source,
        normalize_system_source_value as market_normalize_system_source_value,
    )
except Exception:
    market_get_all_source_options = None
    market_get_source_options = None
    market_get_reference_price_by_source = None
    market_get_source_display_name = None
    market_normalize_system_source_value = None

BASE_DIR = Path(__file__).resolve().parent
CONFIG_FILE = BASE_DIR / "quant.yaml"
STATE_FILE = BASE_DIR / "quant_monitor_state.json"
WEB_CONFIG_FILE = BASE_DIR / "web_portal.json"
BACKTEST_FILE = BASE_DIR / "backtest_quant.py"
TRADE_LOG_FILE = BASE_DIR / "trade_log.csv"
BACKTEST_OUT_DIR = BASE_DIR / "backtest_out"
SNAPSHOT_DIR = BASE_DIR / "data" / "snapshots"
STATE_BACKUP_DIR = BASE_DIR / "data" / "state_backups"
STATE_BACKUP_INDEX = STATE_BACKUP_DIR / "index.json"
SYSTEM_CONFIG_FILE = BASE_DIR / "system_config.json"
PUSH_DETAIL_LOG_FILE = BASE_DIR / "data" / "push_details.jsonl"

yaml = YAML()
yaml.preserve_quotes = True
yaml.indent(mapping=2, sequence=4, offset=2)
yaml.width = 4096

app = Flask(
    __name__,
    template_folder=str(BASE_DIR / "web_templates"),
    static_folder=str(BASE_DIR / "web_static"),
)

APP_DISPLAY_NAME = "闲云量化"

PAGE_TITLES = {
    "status": "标的",
    "backtest": "回测",
    "push": "系统",
}

PARAM_HELP: Dict[str, str] = {
    "base_units": "长期持有的底仓。普通 BOX/TREND 区不主动卖穿它；只有进入 Clear区才按清仓计划逐步降低这部分底仓。",
    "target_units": "补仓初始仓位。价格跌破 MA150 进入 CHANCE_ZONE 时，若当前持仓低于该值，会先一步补到该仓位；若已达到或超过则不补。该参数不参与 TREND 区卖出。",
    "limit_target": "极限仓位倍数。最大仓位 = 补仓初始仓位 × 极限仓位倍数；倒金字塔额外加仓预算 = 最大仓位 - 补仓初始仓位。",
    "current_units": "当前真实持仓。百分比模式可写 3%/0.03；后台会按该值作为下一轮策略判断的当前仓位。",
    "current_avg_cost": "当前持仓成本。用于实盘状态、摊薄成本和交易提示；回测起始成本不直接使用该字段。",
    "k150": "MA150 动态倍率基准（base_k）。最终 MA150 = 原始MA150 × 动态K，动态K = min_k + (k150 − min_k) × (1 − 横盘评分)。k150 越大→动态K 越大→MA150 越高→CHANCE 买入区门槛（price<MA150）越高、越容易触发买入；同时 Trend/Clear 卖出触发价（MA150×trend_multiple / MA150×sell_multiple）也越高、越难进入卖出区。整体偏多。",
    "sideways_window_30": "横盘评分的 MA30 方向判断窗口（默认 30）。公式：对最近 window30 天的 MA30 序列差分，dir=｜ΣΔ｜÷Σ｜Δ｜，横盘分=1−dir。窗口越小对短期折返越灵敏，越大越平滑。",
    "sideways_window_60": "横盘评分的 MA60 方向判断窗口（默认 20）。公式同 MA30：对最近 window60 天的 MA60 序列差分计算方向强度，横盘分=1−dir。越大越偏向平滑的中期横盘判断。",
    "sideways_weight_60": "横盘评分中 MA60 的权重（0~1，默认 0.6），MA30 权重=1−该值。综合横盘评分 = (1−weight60)×横盘分(MA30) + weight60×横盘分(MA60)。越大越偏中期判断，越小越偏短期判断。",
    "sideways_min_k150": "横盘评分最高时（=1）动态 K 最低压到的下限 min_k（默认 0.85）。动态K = min_k + (k150 − min_k) × (1 − 横盘评分)，横盘越严重动态K越接近 min_k，MA150 下移越多、箱体上沿越低、越容易进入 CHANCE 买入区。若 k150 < min_k 则下限取 k150。",
    "trend_multiple": "箱体区上沿倍数 = MA150 * trend_multiple，超过后进入趋势区。",
    "sell_multiple": "Clear区触发倍数 = MA150 * sell_multiple，超过后开始倒金字塔卖出底仓。",
    "add_box_step": "旧版兼容字段。新页面会分别使用 box_add_step 和 pyramid_add_step。",
    "box_add_step": "箱体区固定加仓步长。保留给箱体区固定回补逻辑使用，和倒金字塔加仓步长互不覆盖。",
    "pyramid_add_step": "倒金字塔加仓步长。进入机会区并补到补仓初始仓位后，价格每相对 last_add_price 下跌该比例，触发下一步加仓。",
    "add_box_units_percent": "旧版箱体区固定加仓比例，最新策略不再使用 BOX 区独立回补。",
    "trend_zone_step_percent": "趋势区卖出步长。价格相对 last_trade_price 上涨达到该比例时，才检查是否卖出高于长期底仓的机动仓。",
    "trend_zone_sell_percent": "趋势区单次卖出比例，按当前持仓计算；只卖出高于 base_units 的机动仓，卖出后不低于长期底仓。",
    "clear_zone_step_percent": "Clear区倒金字塔卖出步长。价格相对 sell_multiple 每上移该比例，推进一个清仓步数。",
    "grid_box_percent": "箱体区网格交易步长。当前回测策略不使用该参数，主要保留给实盘/后续网格逻辑。",
    "grid_box_units_percent": "箱体区网格交易比例。当前回测策略不使用该参数，主要保留给实盘/后续网格逻辑。",
    "box_grid_enabled": "箱体区网格开关。当前回测策略不使用该参数，状态栏可用于展示配置。",
    "pyramid_steps": "旧版兼容字段。新页面会分别使用 clear_pyramid_steps 和 pyramid_add_steps。",
    "pyramid_weights": "旧版兼容字段。新页面会分别使用 clear_pyramid_weights 和 pyramid_add_weights。",
    "clear_pyramid_steps": "Clear区倒金字塔卖出最多步数，实际步数不会超过 clear_pyramid_weights 长度。",
    "clear_pyramid_weights": "Clear区倒金字塔每步卖出权重，按 base_units 长期底仓拆分卖出。",
    "pyramid_add_steps": "机会区/箱体区倒金字塔加仓最多步数，实际步数不会超过 pyramid_add_weights 长度。",
    "pyramid_add_weights": "机会区/箱体区倒金字塔每步加仓权重，按额外加仓预算拆分：极限仓位 - 机会区起点仓位。",
    "pyramid_add_enabled": "倒金字塔加仓开关。auto=等待首次进入机会区后自动切到 yes；yes=机会区先补到补仓初始仓位，再按步长和权重加仓。进入趋势/Clear区才结束本轮机会区倒金字塔并切回 auto。",
}

BACKTEST_HELP_TEXT = """1) 价格口径：信号和区间使用 Adj Close；成交、估值、持仓成本使用 Close；分红按除息日现金入账，拆股按除权日调整仓位和成本。

2) 区间划分：
   CHANCE（机会区）= 价格 < MA150
   BOX（箱体区）= MA150 ~ MA150 × trend_multiple
   TREND（趋势区）= MA150 × trend_multiple ~ MA150 × sell_multiple
   CLEAR（清仓区）= 价格 ≥ MA150 × sell_multiple

3) 机会区倒金字塔加仓：MA150 使用动态 K150 系数修正（横盘时降低 MA150，避免机会区过窄）。首次进入 CHANCE 后自动激活倒金字塔模式，按 pyramid_add_step 步长分步加仓。每步加仓量 = (极限仓位 - 底仓) × 对应权重，步数用完或仓位到极限后停止加仓。机会区不主动卖出。

4) 箱体区：不主动买卖，持仓等于目标仓位时维持不动。仓位低于目标需等跌破 MA150 进入机会区才补仓，仓位高于目标需等涨到 trend_multiple 进入趋势区才卖出。

5) 趋势/离场卖出：TREND 区只卖出高于 base_units 的机动仓，按 trend_zone_step_percent 步长推进，每次卖出 trend_zone_sell_percent 的机动仓。CLEAR 区按 clear_pyramid_weights 权重分步清底仓，每步触发价 = 锚定价 × (1 + clear_zone_step_percent × 步数)，步数由 clear_pyramid_steps 控制。

6) 回测参数：回测页面的"初始仓位"是临时参数，只代表回测第一交易日 current_units，默认 5%；不覆盖策略中的 base_units / target_units / limit_target。初始成本默认取回测第一天 Close，可用 initial_avg_cost 指定真实建仓成本。current_avg_cost 仅用于实盘监控。

7) 收益口径：
   峰值净投入 = 回测期内"已买入但尚未卖出"的仓位所达到的最高值。起始底仓计入，买入时增加，卖出时按当时持仓成本冲减，清仓归零，只取历史最大值。同一笔资金反复来回做不会重复计入分母。
   分红收益率 = 累计分红现金贡献 ÷ 峰值净投入。分红在除息日按当时持仓比例入账，单独统计。
   交易实现收益率 = 累计已实现卖出收益 ÷ 峰值净投入。单笔已实现收益 = 卖出仓位 × (卖出原始价 ÷ 当时持仓成本 - 1)。
   持仓收益率 = 期末浮盈 ÷ 峰值净投入。期末浮盈按原始持仓成本计算，不扣分红和已实现收益。
   综合收益率 = 分红收益率 + 交易实现收益率 + 持仓收益率，三项互不重叠。
   期末持仓收益率 = 最新价格 ÷ 原始持仓成本 - 1，只看期末仍持有的仓位。
   摊薄持仓收益率 = 最新价格 ÷ 摊薄后持仓成本 - 1，摊薄成本把全周期分红和已实现收益摊回成本。该口径与上面几项重叠，仅参考展示，不计入综合收益率。
   所有收益率均不扣手续费；总权益(参考) = 期末总权益 ÷ 起始总权益 - 1，是含现金的账户口径，与综合收益率不是同一个分母。

8) 除权息数据：腾讯/新浪日K源本身不带分红拆股，回测会自动从 BaoStock A股含权息 / Yahoo港股含权息 补齐，报告中的"除权息数据来源"显示实际结果（ok=已补齐，failed/no_data=补齐失败，此时分红收益率为 0）。

9) 百分比模式下，qty 表示仓位比例；交易日志保留上一次成交价和上一次加仓价。"""

BACKTEST_METRICS_HELP_TEXT = """期末持仓收益率：只看期末仍持有的仓位，公式为 最新价格 / 原始持仓成本 - 1。它不扣分红也不扣已实现收益，因为这两块已经作为独立的分红收益率、交易实现收益率单独统计，扣进成本会重复计算。

摊薄持仓收益率：股票软件常见的摊薄成本口径，用整个回测期内累计的分红现金贡献 + 已实现交易收益贡献去扣减持仓成本，再算 最新价格 / 摊薄后持仓成本 - 1。它与分红收益率、交易实现收益率口径重叠，只作参考展示，不计入综合收益率。

综合收益率：按峰值净投入口径计算，公式为 (分红收益贡献 + 交易实现收益贡献 + 期末持仓浮盈贡献) / 峰值净投入仓位。峰值净投入 = 回测期内"已投入但尚未卖出"的仓位所达到的最高值，买入时增加、卖出时按当时持仓成本冲减。同一笔资金反复来回做，不会重复计入分母，因此换手次数不再压低收益率。

分红收益率单独计算：分红按除息日、按当时持仓比例入账，不与其它收益项重复。"""


PUSH_FIELDS: List[Dict[str, str]] = [
    {"key": "PUSH_ENABLED", "label": "启用推送", "type": "switch", "channel": "base", "help": "拨动后立即写入 /root/quant/push.conf 并生效。"},
    {"key": "PUSH_CHANNEL", "label": "推送通道", "type": "select", "channel": "base", "help": "只保留 ntfy 和 Gotify 两种推送方式；切换后页面会自动显示对应配置项。"},
    {"key": "NTFY_URL", "label": "ntfy 服务地址", "type": "text", "channel": "ntfy", "help": "同一台服务器本机调用推荐：http://127.0.0.1:8083；外部访问默认：https://sharq.eu.org:2085。"},
    {"key": "NTFY_TOPIC", "label": "ntfy Topic", "type": "text", "channel": "ntfy", "help": "ntfy 的 Topic 相当于频道名，客户端订阅同一个 Topic 才能收到推送。"},
    {"key": "NTFY_USERNAME", "label": "ntfy 用户名", "type": "text", "channel": "ntfy", "help": "如果 ntfy 开启登录认证，请填写用户名；未开启认证可留空。"},
    {"key": "NTFY_PASSWORD", "label": "ntfy 密码", "type": "password", "channel": "ntfy", "help": "如果 ntfy 开启登录认证，请填写密码；未开启认证可留空。"},
    {"key": "NTFY_PRIORITY", "label": "ntfy 优先级", "type": "number", "channel": "ntfy", "help": "ntfy 优先级范围 1-5，默认 3。"},
    {"key": "GOTIFY_URL", "label": "Gotify 服务地址", "type": "text", "channel": "gotify", "help": "本机 Gotify 默认：https://sharq.eu.org:2084，保存时会自动去掉末尾多余空格。"},
    {"key": "GOTIFY_TOKEN", "label": "Gotify Application Token", "type": "password", "channel": "gotify", "help": "Gotify 网页端 Applications 里创建应用后复制的 token。"},
    {"key": "GOTIFY_PRIORITY", "label": "Gotify 优先级", "type": "number", "channel": "gotify", "help": "默认 10。数值越高优先级越高。"},
]

PUSH_SELECT_OPTIONS = {
    "PUSH_CHANNEL": [
        ("ntfy", "ntfy"),
        ("gotify", "Gotify"),
    ],
}

SYSTEM_DEFAULTS: Dict[str, str] = {
    "A_QUOTE_SOURCE": "live_a1",
    "HK_MARKET_SOURCE": "live_hk1",
    "A_BACKTEST_SOURCE": "historical_a1",
    "HK_BACKTEST_SOURCE": "historical_hk1",
    "XUEQIU_TOKEN": "",
    "XUEQIU_TOKEN_UPDATED_AT": "",
    "XUEQIU_TOKEN_SOURCE": "",
}

SYSTEM_SELECT_OPTIONS = market_get_all_source_options() if market_get_all_source_options else {
    "A_QUOTE_SOURCE": [("live_a1", "腾讯实时"), ("live_a2", "雪球实时"), ("live_a3", "东方财富实时")],
    "HK_MARKET_SOURCE": [("live_hk1", "腾讯港股"), ("live_hk2", "雪球港股"), ("live_hk3", "东方财富港股")],
    "A_BACKTEST_SOURCE": [("historical_a1", "腾讯A股/ETF日K"), ("historical_a2", "新浪A股/ETF日K")],
    "HK_BACKTEST_SOURCE": [("historical_hk1", "腾讯港股日K"), ("historical_hk2", "Yahoo港股日K")],
}

STRATEGY_FIELDS: List[Dict[str, str]] = [
    {"key": "loop_enabled", "label": "策略运行开关", "type": "switch", "help": "总开关，关闭后所有策略暂停运行（仍保留日志轮转）。"},
    {"key": "loop_interval", "label": "循环间隔（秒）", "type": "number", "help": "后台策略循环间隔。保存后下一轮循环开始生效。"},
    {"key": "fetch_history_days", "label": "历史K线天数", "type": "number", "help": "策略与指标计算拉取的历史交易日数量。"},
    {"key": "ma_period_short", "label": "短均线周期", "type": "number", "help": "当前策略使用的 MA 周期，默认 150。"},
    {"key": "ma_period_long", "label": "长均线周期", "type": "number", "help": "保留参数，默认 300。"},
    {"key": "session_start", "label": "交易开始时间", "type": "text", "help": "格式 HH:MM，例如 09:25。"},
    {"key": "session_end", "label": "交易结束时间", "type": "text", "help": "格式 HH:MM，例如 23:00。"},
    {"key": "daily_push_time", "label": "每日快照时间", "type": "text", "help": "格式 HH:MM。"},
    {"key": "log_rotate_time", "label": "日志轮转时间", "type": "text", "help": "格式 HH:MM。"},
    {"key": "timezone", "label": "策略时区", "type": "text", "help": "例如 Asia/Shanghai。"},
]

STRATEGY_DEFAULTS: Dict[str, Any] = {
    "loop_enabled": "yes",
    "loop_interval": 60,
    "fetch_history_days": 400,
    "ma_period_short": 150,
    "ma_period_long": 300,
    "session_start": "09:25",
    "session_end": "23:00",
    "daily_push_time": "08:00",
    "log_rotate_time": "08:00",
    "timezone": "Asia/Shanghai",
}

def normalize_system_source_value(field: str, value: Any) -> str:
    if market_normalize_system_source_value:
        try:
            return market_normalize_system_source_value(field, value)
        except Exception:
            pass
    raw = str(value or "").strip()
    allowed = {x[0] for x in SYSTEM_SELECT_OPTIONS.get(field, [])}
    return raw if raw in allowed else SYSTEM_DEFAULTS.get(field, raw)


FIELD_GROUPS: List[Dict[str, Any]] = [
    {
        "id": "basic",
        "title": "基础信息",
        "items": [
            ("symbol", "代码", "text"),
            ("price_scale", "价格缩放", "number"),
            ("strategy_run", "运行状态", "select_yes_no"),
        ],
    },
    {
        "id": "position",
        "title": "仓位参数",
        "items": [
            ("base_units", "长期底仓", "text"),
            ("target_units", "补仓初始仓位", "text"),
            ("limit_target", "极限仓位倍数", "number"),
            ("current_units", "当前持仓", "text"),
            ("current_avg_cost", "当前成本", "number"),
        ],
    },
    {
        "id": "sideways",
        "title": "均线与横盘",
        "items": [
            ("k150", "K150系数", "number"),
            ("sideways_window_30", "横盘MA30天数", "number"),
            ("sideways_window_60", "横盘MA60天数", "number"),
            ("sideways_weight_60", "横盘MA60权重", "number"),
            ("sideways_min_k150", "动态MA150最小值", "number"),
        ],
    },
    {
        "id": "zones",
        "title": "区间界限",
        "items": [
            ("trend_multiple", "箱体区上沿倍数", "number"),
            ("sell_multiple", "Clear区触发倍数", "number"),
        ],
    },
    {
        "id": "box_add",
        "title": "箱体区加仓",
        "items": [
            ("box_add_step", "箱体固定加仓步长", "number"),
            ("add_box_units_percent", "每次加仓比例", "number"),
        ],
    },
    {
        "id": "box_grid",
        "title": "箱体区网格（底仓已满）",
        "items": [
            ("box_grid_enabled", "开启网格交易", "select_yes_no"),
            ("grid_box_percent", "网格步长", "number"),
            ("grid_box_units_percent", "网格交易比例", "number"),
        ],
    },
    {
        "id": "trend_zone",
        "title": "趋势区减仓",
        "items": [
            ("trend_zone_step_percent", "减仓步长", "number"),
            ("trend_zone_sell_percent", "每次减仓比例", "number"),
        ],
    },
    {
        "id": "clear_zone",
        "title": "Clear区减仓（倒金字塔）",
        "items": [
            ("clear_zone_step_percent", "减仓步长", "number"),
            ("clear_pyramid_steps", "离场倒金字塔步数", "number"),
            ("clear_pyramid_weights", "离场倒金字塔权重", "text"),
        ],
    },
    {
        "id": "pyramid_add",
        "title": "倒金字塔加仓（机会区+箱体区）",
        "items": [
            ("pyramid_add_enabled", "倒金字塔加仓开关", "select"),
            ("pyramid_add_step", "倒金字塔加仓步长", "number"),
            ("pyramid_add_weights", "加仓倒金字塔权重", "text"),
            ("pyramid_add_steps", "加仓倒金字塔步数", "number"),
        ],
    },
]

SELECT_FIELD_OPTIONS = {
    "strategy_run": [("on", "on"), ("off", "off")],
    "box_grid_enabled": [("no", "no"), ("yes", "yes")],
    "pyramid_add_enabled": [("auto", "auto"), ("yes", "yes")],
}

SUMMARY_KEYS = [
    "标的", "模式", "K线数量", "回测初始仓位",
    "期末持仓收益率", "摊薄持仓收益率", "综合收益率",
    "分红收益率", "交易实现收益率", "持仓收益率",
    "最新价格", "首次建仓原始价", "首次建仓复权价", "首次建仓日",
    "除权息数据来源",
    "最大回撤", "最大回撤(参考)",
    "期末持仓", "摊薄后持仓成本", "期末持仓成本", "期末市值权重", "期末市值",
    "期末现金权重", "期末现金", "期末持仓市值",
    "结束总权益(参考)", "结束价值(参考)",
]

def default_web_config() -> Dict[str, Any]:
    return {
        "app_name": APP_DISPLAY_NAME,
        "admin_username": "admin",
        # 明文密码，方便直接在 /root/quant/web_portal.json 中修改。
        # 兼容旧版 password_hash；如果 admin_password 非空，优先使用明文密码登录。
        "admin_password": "admin",
        "password_hash": "",
        "secret_key": secrets.token_hex(32),
        "domain": "sharq.eu.org",
        "public_port": 2096,
        "internal_port": 2097,
        "token_api_key": secrets.token_urlsafe(32),
    }

def load_web_config() -> Dict[str, Any]:
    if not WEB_CONFIG_FILE.exists():
        cfg = default_web_config()
        WEB_CONFIG_FILE.write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")
        return cfg
    raw = WEB_CONFIG_FILE.read_text(encoding="utf-8").strip()
    if not raw:
        cfg = default_web_config()
        WEB_CONFIG_FILE.write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")
        return cfg
    try:
        cfg = json.loads(raw)
        if isinstance(cfg, dict):
            merged = default_web_config()
            merged.update(cfg)
            # 兼容旧版 password 字段：如果 JSON 中有 password 但没有 admin_password，将 password 作为 admin_password
            if "password" in cfg and "admin_password" not in cfg:
                merged["admin_password"] = str(cfg.get("password", ""))
            return merged
    except Exception:
        try:
            cfg = ast.literal_eval(raw)
            if isinstance(cfg, dict):
                merged = default_web_config()
                merged.update(cfg)
                # 兼容旧版 password 字段
                if "password" in cfg and "admin_password" not in cfg:
                    merged["admin_password"] = str(cfg.get("password", ""))
                WEB_CONFIG_FILE.write_text(json.dumps(merged, ensure_ascii=False, indent=2), encoding="utf-8")
                return merged
        except Exception:
            pass
    cfg = default_web_config()
    WEB_CONFIG_FILE.write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")
    return cfg

def ensure_web_config_token_api_key() -> str:
    cfg = load_web_config()
    key = str(cfg.get("token_api_key", "") or "").strip()
    if not key:
        key = secrets.token_urlsafe(32)
        cfg["token_api_key"] = key
        try:
            WEB_CONFIG_FILE.write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")
        except Exception:
            pass
    return key

def init_app_secret() -> None:
    cfg = load_web_config()
    app.secret_key = cfg.get("secret_key") or secrets.token_hex(32)
    ensure_web_config_token_api_key()

init_app_secret()


DCF_NAV_STYLE = """
<style id="quant-responsive-nav-style">
.nav {
  display: grid !important;
  grid-template-columns: repeat(3, minmax(0, 1fr)) !important;
  gap: 10px !important;
  align-items: stretch !important;
}
.nav a {
  min-height: 42px !important;
  padding: 10px 12px !important;
  display: flex !important;
  align-items: center !important;
  justify-content: center !important;
  text-align: center !important;
  white-space: nowrap !important;
}
@media (max-width: 640px) {
  .nav {
    display: flex !important;
    flex-wrap: nowrap !important;
    overflow-x: auto !important;
    -webkit-overflow-scrolling: touch !important;
    padding-bottom: 4px !important;
    scrollbar-width: none !important;
  }
  .nav::-webkit-scrollbar { display: none !important; }
  .nav a {
    flex: 0 0 auto !important;
    min-width: 68px !important;
    padding: 9px 12px !important;
  }
}
</style>
"""

STATUS_AUTO_REFRESH_STYLE = """
<style id="quant-status-auto-refresh-style">
/* 状态页刷新按钮与"回测/策略数据源指标"刷新按钮保持一致 */
form[action$="/refresh-status"] button,
form[action$="/refresh-status"] input[type="submit"],
form[action$="/refresh-source-metrics"] button,
form[action$="/refresh-source-metrics"] input[type="submit"],
form[action$="/clear-market-state"] button,
form[action$="/clear-market-state"] input[type="submit"] {
  min-height: 40px !important;
  padding: 9px 14px !important;
  border-radius: 12px !important;
  font-size: 14px !important;
  line-height: 20px !important;
  font-weight: 700 !important;
  font-family: inherit !important;
  cursor: pointer !important;
  display: inline-flex !important;
  align-items: center !important;
  justify-content: center !important;
  gap: 6px !important;
  text-decoration: none !important;
}

/* 系统页雪球 Token/Cookie 输入框统一为系统选择框尺寸 */
.quant-xq-token-wrap {
  position: relative !important;
  display: block !important;
  width: 100% !important;
}
textarea[name="XUEQIU_TOKEN"], input[name="XUEQIU_TOKEN"] {
  box-sizing: border-box !important;
  width: 100% !important;
  max-width: none !important;
  min-height: 56px !important;
  height: 56px !important;
  padding: 12px 18px 12px 18px !important;
  border-radius: 18px !important;
  font-size: 16px !important;
  line-height: 24px !important;
  font-family: inherit !important;
  resize: vertical !important;
}
	</style>
"""

STATUS_AUTO_REFRESH_SCRIPT = """
<script id="quant-status-auto-refresh-script">
(function () {
  if (window.__quantStatusAutoRefreshInstalled) return;
  window.__quantStatusAutoRefreshInstalled = true;

  function enhanceSymbolSelectors() {
    document.querySelectorAll('select[name="symbol_key"]').forEach(function (sel) {
      if (sel.dataset.quantAutoBound === "1") return;
      sel.dataset.quantAutoBound = "1";
      sel.addEventListener("change", function () {
        if (!(window.location.pathname === "/status" || window.location.pathname === "/")) return;
        if (sel.form && sel.name === "symbol_key") {
          sel.form.submit();
        }
      });
    });

    // 状态页下拉框自动提交，不显示额外"查看"按钮。
    if (window.location.pathname === "/status" || window.location.pathname === "/") {
      document.querySelectorAll('form[action$="/status"] button, form[action$="/status"] input[type="submit"]').forEach(function (el) {
        var text = (el.innerText || el.value || "").trim();
        if (text === "查看" && el.closest && el.closest('form') && el.closest('form').querySelector('select[name="symbol_key"]')) {
          el.style.display = "none";
        }
      });
    }
  }

  function syncMetricRefreshButtonStyle() {
    var statusBtn = document.querySelector('form[action$="/refresh-status"] button, form[action$="/refresh-status"] input[type="submit"]');
    if (!statusBtn) return;
    var cs = window.getComputedStyle(statusBtn);
    var props = [
      "background", "backgroundColor", "border", "borderColor", "borderRadius",
      "boxShadow", "color", "font", "fontFamily", "fontSize", "fontWeight",
      "height", "lineHeight", "minHeight", "padding", "textTransform"
    ];
    document.querySelectorAll('form[action$="/refresh-source-metrics"] button, form[action$="/refresh-source-metrics"] input[type="submit"]').forEach(function (btn) {
      props.forEach(function (prop) {
        try { btn.style[prop] = cs[prop]; } catch (e) {}
      });
      btn.style.cursor = "pointer";
    });
  }



  function startAutoReload() {
    if (!(window.location.pathname === "/status" || window.location.pathname === "/")) return;
    var hasStatus = document.body && document.body.innerText && document.body.innerText.indexOf("实时状态") >= 0 || document.querySelector('form[action$="/refresh-status"]');
    if (!hasStatus) return;
    var intervalMs = 60000;
    window.setInterval(function () {
      if (document.hidden) return;
      if (document.activeElement && /INPUT|TEXTAREA|SELECT/.test(document.activeElement.tagName)) return;
      window.location.reload();
    }, intervalMs);
  }

  enhanceSymbolSelectors();
  syncMetricRefreshButtonStyle();
  startAutoReload();
})();
</script>
"""

@app.after_request
def inject_responsive_nav_style(response):
    """Inject responsive navigation plus status-page auto refresh behavior."""
    try:
        content_type = response.headers.get("Content-Type", "")
        if "text/html" not in content_type.lower():
            return response
        html = response.get_data(as_text=True)
        if "</head>" in html and "quant-responsive-nav-style" not in html:
            html = html.replace("</head>", DCF_NAV_STYLE + "\n</head>", 1)
        if "</head>" in html and "quant-status-auto-refresh-style" not in html:
            html = html.replace("</head>", STATUS_AUTO_REFRESH_STYLE + "\n</head>", 1)
        if "</body>" in html and "quant-xq-token-meta" not in html:
            try:
                _xq_cfg = read_system_config()
                _xq_meta = {
                    "updated_at": str(_xq_cfg.get("XUEQIU_TOKEN_UPDATED_AT", "") or ""),
                    "source": str(_xq_cfg.get("XUEQIU_TOKEN_SOURCE", "") or ""),
                }
                _xq_script = '<script id="quant-xq-token-meta">window.__DCF_XQ_META=' + json.dumps(_xq_meta, ensure_ascii=False) + ';</script>'
                html = html.replace("</body>", _xq_script + "\n</body>", 1)
            except Exception:
                pass
        if "</body>" in html and "quant-status-auto-refresh-script" not in html:
            html = html.replace("</body>", STATUS_AUTO_REFRESH_SCRIPT + "\n</body>", 1)
        response.set_data(html)
        response.headers["Content-Length"] = str(len(response.get_data()))
    except Exception:
        return response
    return response

def normalize_strategy_run_value(value: Any, default: str = "on") -> str:
    """运行开关只允许 on/off；无效或缺失值按 default 处理，默认 on。"""
    s = str(value if value is not None else "").strip().lower()
    if s in {"on", "off"}:
        return s
    return default
TIME_FIELD_DEFAULTS: Dict[str, str] = {
    "session_start": "09:25",
    "session_end": "16:00",
    "daily_push_time": "08:00",
    "log_rotate_time": "08:00",
}

def normalize_hhmm_value(value: Any, default: str = "09:30") -> str:
    """Return a canonical HH:MM string for YAML time fields.

    Web saves these fields as quoted strings so the daemon reads them as
    normal text rather than YAML 1.1 sexagesimal numbers.
    """
    try:
        text = str(value if value is not None else "").strip().strip("'").strip('\"')
        h, m = text.split(":", 1)
        h_i, m_i = int(h), int(m)
        if 0 <= h_i <= 23 and 0 <= m_i <= 59:
            return f"{h_i:02d}:{m_i:02d}"
    except Exception:
        pass
    return default

def normalize_strategy_config(strategy: Dict[str, Any]) -> bool:
    changed = False
    if not isinstance(strategy, dict):
        return changed
    loop_val = strategy.get("loop_enabled", "yes")
    if loop_val in (True, "yes", "on", "true", "1", 1):
        new_loop = "yes"
    elif loop_val in (False, "no", "off", "false", "0", 0):
        new_loop = "no"
    else:
        new_loop = "yes"
    if strategy.get("loop_enabled") != new_loop:
        strategy["loop_enabled"] = new_loop
        changed = True
    int_defaults = {
        "loop_interval": 60,
        "fetch_history_days": 400,
        "ma_period_short": 150,
        "ma_period_long": 300,
    }
    for key, default in int_defaults.items():
        old = strategy.get(key, default)
        try:
            new = int(float(old))
        except Exception:
            new = default
        if key == "loop_interval":
            new = max(1, new)
        elif key == "fetch_history_days":
            new = max(2, new)
        elif key == "ma_period_short":
            new = max(5, new)
        elif key == "ma_period_long":
            new = max(int(strategy.get("ma_period_short", 150) or 150), new)
        if old != new:
            strategy[key] = new
            changed = True
    for key, default in TIME_FIELD_DEFAULTS.items():
        old = strategy.get(key, default)
        new = DoubleQuotedScalarString(normalize_hhmm_value(old, default))
        if str(old) != str(new) or not isinstance(old, DoubleQuotedScalarString):
            strategy[key] = new
            changed = True
    tz_old = strategy.get("timezone", "Asia/Shanghai")
    tz_new = str(tz_old or "Asia/Shanghai").strip() or "Asia/Shanghai"
    if tz_old != tz_new:
        strategy["timezone"] = tz_new
        changed = True
    return changed

def normalize_config(data: Dict[str, Any]) -> bool:
    changed = False
    strategy_section = data.setdefault("STRATEGY", {})
    if isinstance(strategy_section, dict) and normalize_strategy_config(strategy_section):
        changed = True
    common = data.get("COMMON_BACKTEST_CONFIG")
    if isinstance(common, dict):
        # 移除废弃字段（MA300相关及旧字段）
        for k in ["k300", "ma300_min_coef", "pyramid_enabled", "fee_rate", "slippage_bp", "stop_add_above_percent",
                  "core_zone_upper_multiple", "core_sell_start_multiple", "core_sell_step_percent",
                  "sell_percent", "sell_trigger_up_percent"]:
            if k in common:
                common.pop(k, None)
                changed = True
        new_run = normalize_strategy_run_value(common.get("strategy_run", "on"), "on")
        if common.get("strategy_run") != new_run:
            common["strategy_run"] = new_run
            changed = True
        if common.get("box_grid_enabled") not in {"yes", "no"}:
            common["box_grid_enabled"] = "no"
            changed = True
        if common.get("pyramid_add_enabled") not in {"yes", "auto"}:
            common["pyramid_add_enabled"] = "auto"
            changed = True
        # 确保新字段有默认值
        common.setdefault("trend_multiple", 1.2)
        common.setdefault("sell_multiple", 1.5)
        common.setdefault("add_box_step", 0.05)  # legacy alias
        common.setdefault("box_add_step", common.get("add_box_step", 0.05))
        common.setdefault("pyramid_add_step", common.get("add_box_step", 0.05))
        common.setdefault("add_box_units_percent", 0.1)
        common.setdefault("trend_zone_step_percent", 0.01)
        common.setdefault("trend_zone_sell_percent", 0.05)
        common.setdefault("clear_zone_step_percent", 0.08)
        common.setdefault("pyramid_weights", [0.03, 0.055, 0.08, 0.105, 0.13, 0.155, 0.18, 0.205, 0.23, 0.255])  # legacy alias
        common.setdefault("pyramid_steps", 10)  # legacy alias
        common.setdefault("clear_pyramid_weights", list(common.get("pyramid_weights", [])))
        common.setdefault("clear_pyramid_steps", common.get("pyramid_steps", 10))
        common.setdefault("pyramid_add_weights", list(common.get("pyramid_weights", [])))
        common.setdefault("pyramid_add_steps", common.get("pyramid_steps", 10))
        common.setdefault("pyramid_add_enabled", "auto")

    symbol_cfg = data.get("SYMBOL_CONFIG")
    if isinstance(symbol_cfg, dict):
        for _, section in symbol_cfg.items():
            if not isinstance(section, dict):
                continue
            for k in ["k300", "ma300_min_coef", "pyramid_enabled", "fee_rate", "slippage_bp", "stop_add_above_percent",
                      "core_zone_upper_multiple", "core_sell_start_multiple", "core_sell_step_percent",
                      "sell_percent", "sell_trigger_up_percent"]:
                if k in section:
                    section.pop(k, None)
                    changed = True
            new_run = normalize_strategy_run_value(section.get("strategy_run", "on"), "on")
            if section.get("strategy_run") != new_run:
                section["strategy_run"] = new_run
                changed = True
            if section.get("box_grid_enabled") not in {"yes", "no"}:
                section["box_grid_enabled"] = "no"
                changed = True
            if section.get("pyramid_add_enabled") not in {"yes", "auto"}:
                section["pyramid_add_enabled"] = "auto"
                changed = True
            section.setdefault("trend_multiple", 1.2)
            section.setdefault("sell_multiple", 1.5)
            section.setdefault("add_box_step", 0.05)  # legacy alias
            section.setdefault("box_add_step", section.get("add_box_step", 0.05))
            section.setdefault("pyramid_add_step", section.get("add_box_step", 0.05))
            section.setdefault("add_box_units_percent", 0.1)
            section.setdefault("trend_zone_step_percent", 0.01)
            section.setdefault("trend_zone_sell_percent", 0.05)
            section.setdefault("clear_zone_step_percent", 0.08)
            section.setdefault("pyramid_weights", [0.03, 0.055, 0.08, 0.105, 0.13, 0.155, 0.18, 0.205, 0.23, 0.255])  # legacy alias
            section.setdefault("pyramid_steps", 10)  # legacy alias
            section.setdefault("clear_pyramid_weights", list(section.get("pyramid_weights", [])))
            section.setdefault("clear_pyramid_steps", section.get("pyramid_steps", 10))
            section.setdefault("pyramid_add_weights", list(section.get("pyramid_weights", [])))
            section.setdefault("pyramid_add_steps", section.get("pyramid_steps", 10))
            section.setdefault("pyramid_add_enabled", "auto")
    return changed

def read_yaml() -> Dict[str, Any]:
    if not CONFIG_FILE.exists():
        return {}
    raw = CONFIG_FILE.read_text(encoding="utf-8")
    try:
        data = yaml.load(raw) or {}
    except DuplicateKeyError:
        data = pyyaml.safe_load(raw) or {}
        if isinstance(data, dict):
            write_yaml(data)
    if isinstance(data, dict) and normalize_config(data):
        write_yaml(data)
    return data

def _clone_yaml_plain(value):
    """Return a structure without shared list/dict references, so YAML has no &id/*id anchors."""
    if isinstance(value, dict):
        return {k: _clone_yaml_plain(v) for k, v in value.items()}
    if isinstance(value, list):
        return [_clone_yaml_plain(v) for v in value]
    return value


def write_yaml(data: Dict[str, Any]) -> None:
    normalize_config(data)
    with CONFIG_FILE.open("w", encoding="utf-8") as f:
        yaml.dump(data, f)

def read_state() -> Dict[str, Any]:
    if not STATE_FILE.exists():
        return {}
    try:
        return json.loads(STATE_FILE.read_text(encoding="utf-8"))
    except Exception:
        return {}

def snapshot_dates(limit: int = 30) -> List[str]:
    if not SNAPSHOT_DIR.exists():
        return []
    dates = []
    for p in SNAPSHOT_DIR.glob("*.jsonl"):
        if re.match(r"^\d{4}-\d{2}-\d{2}$", p.stem):
            dates.append(p.stem)
    return sorted(dates, reverse=True)[:limit]


def read_snapshot_records(day: str = "", limit: int = 2000) -> List[Dict[str, Any]]:
    day = (day or datetime.now().strftime("%Y-%m-%d")).strip()
    path = SNAPSHOT_DIR / f"{day}.jsonl"
    if not path.exists():
        return []
    try:
        lines = [line.strip() for line in path.read_text(encoding="utf-8", errors="ignore").splitlines() if line.strip()]
        if limit and len(lines) > limit:
            lines = lines[-limit:]
        out = []
        for line in lines:
            try:
                item = json.loads(line)
                if isinstance(item, dict):
                    out.append(item)
            except Exception:
                continue
        return out
    except Exception:
        return []


def _snapshot_matches(record: Dict[str, Any], selected: str, symbol_code: str) -> bool:
    if not isinstance(record, dict):
        return False
    if selected == "COMMON_BACKTEST_CONFIG":
        return True
    name = str(record.get("name", "")).strip()
    symbol = str(record.get("symbol", "")).strip().upper()
    return name == selected or (symbol_code and symbol == symbol_code.upper())


def _snapshot_action(record: Dict[str, Any]) -> str:
    return str(record.get("action") or record.get("decision") or "").strip().upper()


def _is_trade_snapshot(record: Dict[str, Any]) -> bool:
    action = _snapshot_action(record)
    side = str(record.get("side") or "").strip().upper()
    trade_count = safe_int(record.get("trade_count", 0), 0)
    return action in {"TRADE", "BUY", "SELL"} or side in {"BUY", "SELL"} or trade_count > 0


def _is_strategy_decision_snapshot(record: Dict[str, Any]) -> bool:
    """Snapshots that represent a real strategy decision for the status page.

    Exclude Web/manual refresh records so REFRESH_ONLY does not replace the
    latest in-market TRADE/NO_TRADE state. MONITOR_ONLY is also excluded from
    the primary snapshot because it is not an executable strategy decision.
    """
    if record.get("manual_trade"):
        return False
    action = _snapshot_action(record)
    if action in {"REFRESH_ONLY", "MONITOR_ONLY"}:
        return False
    reason = str(record.get("reason") or "").strip()
    if action == "" and ("Web手动刷新" in reason or "manual refresh" in reason.lower()):
        return False
    return action in {"TRADE", "BUY", "SELL", "NO_TRADE"} or _is_trade_snapshot(record)


def get_strategy_snapshots(selected: str, symbol_code: str, day: str = "") -> Tuple[Dict[str, Any], List[Dict[str, Any]]]:
    """Return the latest realtime strategy decision snapshots.

    In-trading-session the card is day-scoped so yesterday's NO_TRADE/TRADE
    does not look like the current live state after the date changes. Outside
    the session (before the first bar of the day) it falls back to the most
    recent available day so the status is preserved instead of showing empty.
    """
    day = (day or datetime.now().strftime("%Y-%m-%d")).strip()
    in_session = web_in_trade_session()

    def _collect(which_day: str) -> Tuple[Dict[str, Any], List[Dict[str, Any]]]:
        records = [normalize_snapshot_source_fields(r) for r in read_snapshot_records(which_day, limit=5000) if _snapshot_matches(r, selected, symbol_code)]
        decision_records = [r for r in records if _is_strategy_decision_snapshot(r)]
        recent = list(reversed(decision_records[-10:]))
        return (recent[0] if recent else {}), recent

    latest, recent = _collect(day)
    if latest or in_session:
        return latest, recent

    for prev_day in snapshot_dates(3650):
        if prev_day == day:
            continue
        latest, recent = _collect(prev_day)
        if latest:
            return latest, recent

    return {}, []


def get_recent_trade_snapshots(selected: str, symbol_code: str, limit: int = 10) -> List[Dict[str, Any]]:
    """Return the latest real trade snapshots across all available days."""
    rows: List[Dict[str, Any]] = []
    for day in snapshot_dates(3650):
        records = [normalize_snapshot_source_fields(r) for r in read_snapshot_records(day, limit=20000) if _snapshot_matches(r, selected, symbol_code)]
        for record in reversed(records):
            if _is_trade_snapshot(record):
                rows.append(record)
                if len(rows) >= limit:
                    return rows
    return rows


def build_market_source_stats(selected: str, symbol_code: str, day: str) -> List[Dict[str, Any]]:
    records = [r for r in read_snapshot_records(day, limit=100000) if _snapshot_matches(r, selected, symbol_code)]
    stats: Dict[str, Dict[str, Any]] = {}
    for r in records:
        source = display_source_name(r.get("market_source") or r.get("source") or "unknown")
        row = stats.setdefault(source, {"source": source, "total": 0, "ok": 0, "warn": 0, "error": 0, "skip": 0})
        row["total"] += 1
        status = str(r.get("market_status") or "").strip().lower()
        level = str(r.get("level") or "").strip().upper()
        action = str(r.get("action") or r.get("decision") or "").strip().upper()
        if status == "ok" or level == "INFO":
            row["ok"] += 1
        elif status == "warn" or level == "WARN":
            row["warn"] += 1
        elif status == "error" or level == "ERROR":
            row["error"] += 1
        if action in {"SKIP_TRADE", "MONITOR_ONLY"}:
            row["skip"] += 1
    result = []
    for row in stats.values():
        total = row["total"] or 1
        row = dict(row)
        row["success_rate"] = f"{row['ok'] / total * 100:.1f}%"
        result.append(row)
    return sorted(result, key=lambda x: (-x["total"], x["source"]))




def read_trade_state_backup_index() -> List[Dict[str, Any]]:
    if not STATE_BACKUP_INDEX.exists():
        return []
    try:
        data = json.loads(STATE_BACKUP_INDEX.read_text(encoding="utf-8"))
        return data if isinstance(data, list) else []
    except Exception:
        return []


def get_trade_state_backups(selected: str, symbol_code: str, limit: int = 10) -> List[Dict[str, Any]]:
    if selected == "COMMON_BACKTEST_CONFIG":
        return []
    symbol_code = (symbol_code or "").strip().upper()
    rows = []
    for item in read_trade_state_backup_index():
        if not isinstance(item, dict):
            continue
        symbol = str(item.get("symbol", "")).strip().upper()
        name = str(item.get("name", "")).strip()
        if name != selected and (not symbol_code or symbol != symbol_code):
            continue
        rel = str(item.get("file", "")).strip()
        if rel:
            try:
                path = (BASE_DIR / rel).resolve()
                if not str(path).startswith(str(STATE_BACKUP_DIR.resolve())) or not path.exists():
                    continue
            except Exception:
                continue
        rows.append(item)
    rows.sort(key=lambda x: str(x.get("time", "")), reverse=True)
    return rows[:limit]


def _load_trade_state_backup(backup_id: str, selected: str, symbol_code: str) -> Dict[str, Any]:
    backup_id = (backup_id or "").strip()
    symbol_code = (symbol_code or "").strip().upper()
    if not backup_id:
        raise ValueError("缺少回滚点 ID")
    for item in read_trade_state_backup_index():
        if str(item.get("id", "")) != backup_id:
            continue
        name = str(item.get("name", "")).strip()
        symbol = str(item.get("symbol", "")).strip().upper()
        if name != selected and (not symbol_code or symbol != symbol_code):
            raise ValueError("回滚点不属于当前标的")
        rel = str(item.get("file", "")).strip()
        path = (BASE_DIR / rel).resolve()
        if not str(path).startswith(str(STATE_BACKUP_DIR.resolve())):
            raise ValueError("回滚点路径非法")
        if not path.exists():
            raise ValueError("回滚点文件不存在")
        data = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(data, dict) or not isinstance(data.get("state_before"), dict):
            raise ValueError("回滚点内容无效")
        return data
    raise ValueError("未找到回滚点")


def _format_units_for_config(value: Any, mode: str) -> Any:
    val = safe_float(value, 0.0)
    if mode == "percent":
        pct = val * 100.0
        text = f"{pct:.6f}".rstrip("0").rstrip(".")
        return f"{text or '0'}%"
    try:
        return int(round(val))
    except Exception:
        return val


def request_runtime_state_restore(selected: str, backup_id: str, state_entry: Dict[str, Any]) -> None:
    state = read_state()
    if not isinstance(state, dict):
        state = {}
    meta = state.setdefault("_meta", {})
    try:
        seq = int(meta.get("config_reload_seq", 0) or 0) + 1
    except Exception:
        seq = 1
    meta["config_reload_seq"] = seq
    meta["config_reload_requested_at"] = current_time_text()
    for _k in ["state_restore_kind", "state_restore_symbol_key", "state_restore_backup_id", "state_restore_entry"]:
        meta.pop(_k, None)
    meta["config_reload_symbol_key"] = selected
    meta["config_reload_symbols"] = [selected]
    meta["state_restore_kind"] = "trade_backup"
    meta["state_restore_symbol_key"] = selected
    meta["state_restore_backup_id"] = backup_id
    meta["state_restore_entry"] = state_entry
    state[selected] = state_entry
    write_state(state)


def restore_trade_state_backup(backup_id: str, selected: str) -> str:
    if selected == "COMMON_BACKTEST_CONFIG":
        raise ValueError("通用回测参数没有交易状态可回滚")
    config = read_yaml()
    section = get_section(config, selected)
    if not section:
        raise ValueError("未找到当前标的配置")
    symbol_code = str(section.get("symbol", "")).strip().upper()
    backup = _load_trade_state_backup(backup_id, selected, symbol_code)
    state_entry = deepcopy(backup.get("state_before") or {})
    mode = str(backup.get("position_mode") or get_position_mode_from_section(section)).strip() or get_position_mode_from_section(section)
    restored_units = state_entry.get("current_units")
    restored_avg_cost = state_entry.get("avg_cost")
    if restored_units is not None:
        section["current_units"] = _format_units_for_config(restored_units, mode)
    if restored_avg_cost is not None:
        section["current_avg_cost"] = round(safe_float(restored_avg_cost, 0.0), 6)
    set_section(config, selected, section)
    write_yaml(config)
    state_entry["last_status_msg"] = f"已恢复到交易前状态回滚点：{backup_id}"
    request_runtime_state_restore(selected, backup_id, state_entry)
    trade = backup.get("trade") or {}
    return f"已恢复到 {backup.get('time', '')} 的交易前状态：{trade.get('side', '')} {trade.get('qty', '')} @ {trade.get('price', '')}"


def get_position_mode_from_section(section: Dict[str, Any]) -> str:
    base = section.get("base_units", 0)
    target = section.get("target_units", 0)
    if isinstance(base, str) and base.strip().endswith("%"):
        return "percent"
    if isinstance(target, str) and target.strip().endswith("%"):
        return "percent"
    try:
        if 0 <= float(base) <= 1 and 0 <= float(target) <= 1:
            return "percent"
    except Exception:
        pass
    return "absolute"

def fmt_snapshot_value(value: Any, digits: int = 3) -> str:
    if value is None or value == "":
        return "-"
    try:
        return f"{float(value):.{digits}f}"
    except Exception:
        return str(value)

def display_source_name(source: Any) -> str:
    """Customer-facing source name from market_data.py; no local hardcoding."""
    s = str(source or "").strip()
    if market_get_source_display_name:
        try:
            return market_get_source_display_name(s)
        except Exception:
            pass
    if s.startswith("cache_"):
        return "本地缓存"
    return s or "未知"


def normalize_snapshot_source_fields(record: Dict[str, Any]) -> Dict[str, Any]:
    if not isinstance(record, dict):
        return record
    out = dict(record)
    for key in ("market_source", "strategy_source", "source"):
        if key in out:
            out[key] = display_source_name(out.get(key))
    return out

def write_state(data: Dict[str, Any]) -> None:
    try:
        STATE_FILE.write_text(json.dumps(data or {}, ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception:
        pass

def request_runtime_config_reload(selected: str, section: Dict[str, Any] | None = None) -> None:
    """Notify quant.py to reload config and let edited position fields take effect.

    Only current_units/current_avg_cost are written into runtime state here. Trading
    anchors such as last_trade_price, last_add_price, pyramid_step and clear_step
    are intentionally preserved, so saving parameters does not behave like a manual reset.
    When section is None (symbol deletion), no state entry is created.
    """
    state = read_state()
    if not isinstance(state, dict):
        state = {}
    if selected != "COMMON_BACKTEST_CONFIG" and isinstance(section, dict) and section:
        node = state.setdefault(selected, {})
        if isinstance(node, dict):
            mode = str(section.get("position_mode", node.get("position_mode", "percent")) or "percent").strip().lower()
            node["symbol"] = str(section.get("symbol", node.get("symbol", "")) or "").strip().upper()
            node["position_mode"] = mode
            if "current_units" in section and section.get("current_units") not in (None, ""):
                node["current_units"] = parse_runtime_position_value(section.get("current_units"))
            if "current_avg_cost" in section and section.get("current_avg_cost") not in (None, ""):
                node["avg_cost"] = safe_float(section.get("current_avg_cost"), node.get("avg_cost", 0.0))
            node["param_saved_at"] = current_time_text()
            node["param_save_notice"] = (
                f"Web参数已保存并写入运行状态：current_units={node.get('current_units')}, "
                f"avg_cost={node.get('avg_cost')}，等待下一轮行情重算完整状态。"
            )
    meta = state.setdefault("_meta", {})
    try:
        seq = int(meta.get("config_reload_seq", 0) or 0) + 1
    except Exception:
        seq = 1
    if selected == "COMMON_BACKTEST_CONFIG":
        reload_symbols = ["__ALL__"]
    else:
        reload_symbols = [selected]
    meta["config_reload_seq"] = seq
    meta["config_reload_requested_at"] = current_time_text()
    for _k in ["state_restore_kind", "state_restore_symbol_key", "state_restore_backup_id", "state_restore_entry"]:
        meta.pop(_k, None)
    meta["config_reload_symbol_key"] = selected
    meta["config_reload_symbol_code"] = str((section or {}).get("symbol", "")).strip().upper()
    meta["config_reload_symbols"] = reload_symbols
    write_state(state)

def delete_symbol_state(selected: str, symbol_code: str = "") -> None:
    state = read_state()
    if not isinstance(state, dict):
        return
    changed = False
    code = (symbol_code or "").strip().upper()
    keys_to_remove = set()
    for key, val in list(state.items()):
        if key == selected or (code and str(key).strip().upper() == code):
            keys_to_remove.add(key)
            continue
        if isinstance(val, dict):
            val_symbol = str(val.get("symbol", "")).strip().upper()
            val_name = str(val.get("name", "")).strip()
            if val_name == selected or (code and val_symbol == code):
                keys_to_remove.add(key)
    for key in keys_to_remove:
        state.pop(key, None)
        changed = True

    meta = state.get("_meta")
    if isinstance(meta, dict):
        for key in list(meta.keys()):
            value = meta.get(key)
            remove_key = False
            if isinstance(value, str):
                remove_key = value == selected or (code and value.strip().upper() == code)
            elif isinstance(value, list):
                remove_key = selected in value or (code and code in [str(x).strip().upper() for x in value])
            elif isinstance(value, dict):
                val_symbol = str(value.get("symbol", "")).strip().upper()
                val_name = str(value.get("name", "")).strip()
                remove_key = val_name == selected or (code and val_symbol == code)
            if remove_key:
                meta.pop(key, None)
                changed = True

    if changed:
        write_state(state)


def _symbol_record_matches_name_code(record: Any, selected: str, symbol_code: str = "") -> bool:
    if not isinstance(record, dict):
        return False
    code = (symbol_code or "").strip().upper()
    names = {selected, str(record.get("name", "") or "").strip(), str(record.get("selected", "") or "").strip()}
    symbols = {str(record.get("symbol", "") or "").strip().upper(), str(record.get("symbol_code", "") or "").strip().upper()}
    return bool(selected and selected in names) or bool(code and code in symbols)


def cleanup_deleted_symbol_snapshots(selected: str, symbol_code: str = "") -> int:
    """Remove deleted symbol records from JSONL snapshot files."""
    removed = 0
    if not SNAPSHOT_DIR.exists():
        return removed
    for path in SNAPSHOT_DIR.glob("*.jsonl"):
        kept: List[str] = []
        changed = False
        try:
            for raw in path.read_text(encoding="utf-8", errors="ignore").splitlines():
                line = raw.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                except Exception:
                    kept.append(raw)
                    continue
                if _symbol_record_matches_name_code(obj, selected, symbol_code):
                    removed += 1
                    changed = True
                else:
                    kept.append(json.dumps(obj, ensure_ascii=False))
            if changed:
                if kept:
                    path.write_text("\n".join(kept) + "\n", encoding="utf-8")
                else:
                    path.unlink(missing_ok=True)
        except Exception:
            continue
    return removed


def cleanup_deleted_symbol_state_backups(selected: str, symbol_code: str = "") -> int:
    """Delete rollback backup files/index entries for a removed symbol."""
    if not STATE_BACKUP_INDEX.exists():
        return 0
    try:
        items = json.loads(STATE_BACKUP_INDEX.read_text(encoding="utf-8"))
    except Exception:
        return 0
    if not isinstance(items, list):
        return 0
    kept = []
    removed = 0
    base = STATE_BACKUP_DIR.resolve()
    for item in items:
        if _symbol_record_matches_name_code(item, selected, symbol_code):
            removed += 1
            try:
                path = Path(str(item.get("path", ""))).resolve()
                if str(path).startswith(str(base)) and path.exists():
                    path.unlink()
            except Exception:
                pass
        else:
            kept.append(item)
    if removed:
        try:
            STATE_BACKUP_INDEX.write_text(json.dumps(kept, ensure_ascii=False, indent=2), encoding="utf-8")
        except Exception:
            pass
    return removed


def cleanup_deleted_symbol_trade_log(selected: str, symbol_code: str = "") -> int:
    """Remove trade log rows for a deleted symbol."""
    if not TRADE_LOG_FILE.exists():
        return 0
    removed = 0
    try:
        lines = TRADE_LOG_FILE.read_text(encoding="utf-8", errors="ignore").splitlines()
        if not lines:
            return 0
        header = lines[0]
        kept = [header]
        for line in lines[1:]:
            row = line.strip()
            if not row:
                continue
            try:
                parts = list(csv.reader([row]))[0]
            except Exception:
                kept.append(row)
                continue
            row_name = str(parts[1] if len(parts) > 1 else "").strip()
            row_symbol = str(parts[2] if len(parts) > 2 else "").strip().upper()
            if row_name == selected or (symbol_code and row_symbol == symbol_code):
                removed += 1
            else:
                kept.append(row)
        if removed:
            TRADE_LOG_FILE.write_text("\n".join(kept) + "\n", encoding="utf-8")
    except Exception:
        pass
    return removed


def _safe_symbol_part(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", (text or "").strip().upper()) or "UNKNOWN"


def cleanup_deleted_symbol_strategy_cache(selected: str, symbol_code: str = "") -> int:
    """Delete strategy history cache files for a deleted symbol."""
    removed = 0
    try:
        cache_dir = _strategy_history_cache_dir()
        if not cache_dir.exists():
            return removed
        patterns = set()
        for name in (selected, symbol_code):
            safe = _safe_symbol_part(name)
            if safe and safe != "UNKNOWN":
                patterns.add(safe)
        if not patterns:
            return removed
        for f in list(cache_dir.iterdir()):
            if f.is_file() and any(f.name.startswith(p + "_") for p in patterns):
                try:
                    f.unlink()
                    removed += 1
                except Exception:
                    pass
    except Exception:
        pass
    return removed


def cleanup_deleted_symbol_backtest_out(selected: str, symbol_code: str = "") -> int:
    """Delete backtest output directory for a deleted symbol."""
    removed = 0
    try:
        code = (symbol_code or "").strip().upper()
        for candidate in (code, selected):
            if not candidate:
                continue
            path = BACKTEST_OUT_DIR / candidate
            if path.exists() and path.is_dir():
                import shutil
                shutil.rmtree(path)
                removed += 1
    except Exception:
        pass
    return removed


def cleanup_deleted_symbol_runtime_files(selected: str, symbol_code: str = "") -> Dict[str, int]:
    return {
        "snapshots": cleanup_deleted_symbol_snapshots(selected, symbol_code),
        "state_backups": cleanup_deleted_symbol_state_backups(selected, symbol_code),
        "trade_log": cleanup_deleted_symbol_trade_log(selected, symbol_code),
        "strategy_cache": cleanup_deleted_symbol_strategy_cache(selected, symbol_code),
        "backtest_out": cleanup_deleted_symbol_backtest_out(selected, symbol_code),
    }


def request_runtime_system_config_reload() -> None:
    """Notify running quant.py that market-source settings changed."""
    state = read_state()
    if not isinstance(state, dict):
        state = {}
    meta = state.setdefault("_meta", {})
    try:
        seq = int(meta.get("system_config_seq", 0) or 0) + 1
    except Exception:
        seq = 1
    meta["system_config_seq"] = seq
    meta["system_config_updated_at"] = current_time_text()
    write_state(state)


def request_force_refresh_symbol(selected: str, symbol_code: str = "") -> int:
    """Ask quant.py to refresh one selected symbol once, even outside trading session.

    The refresh is monitor-only and will not trigger trades. Reference prices for
    the selected symbol's primary source and backup sources are refreshed by the
    background process and then read from state cache by the Web page.
    """
    state = read_state()
    if not isinstance(state, dict):
        state = {}
    meta = state.setdefault("_meta", {})
    try:
        seq = int(meta.get("force_refresh_seq", 0) or 0) + 1
    except Exception:
        seq = 1
    selected = str(selected or "").strip()
    symbol_code = str(symbol_code or "").strip().upper()
    meta["force_refresh_seq"] = seq
    meta["force_refresh_requested_at"] = current_time_text()
    meta["force_refresh_symbol_key"] = selected
    meta["force_refresh_symbol_code"] = symbol_code
    meta["force_refresh_symbols"] = [selected] if selected and selected != "COMMON_BACKTEST_CONFIG" else []
    write_state(state)
    return seq



def _parse_web_time(value: str):
    try:
        return datetime.strptime(str(value or "").strip(), "%Y-%m-%d %H:%M:%S")
    except Exception:
        return None


def _status_age_seconds(selected: str, section: Dict[str, Any], state: Dict[str, Any]) -> float:
    """Return seconds since the selected symbol was last refreshed; inf when unknown."""
    symbol = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
    candidates = [selected, symbol]
    for key, val in (state or {}).items():
        if isinstance(val, dict) and symbol and str(val.get("symbol", "")).strip().upper() == symbol:
            candidates.append(key)
    seen = set()
    for key in candidates:
        if not key or key in seen:
            continue
        seen.add(key)
        node = state.get(key, {}) if isinstance(state, dict) else {}
        if not isinstance(node, dict):
            continue
        raw = node.get("status_updated_at") or node.get("reference_prices_updated_at") or ""
        # last_status_msg uses Chinese text time like 2026.05.18.21:15; keep that as a display value only.
        dt = _parse_web_time(str(raw))
        if dt:
            return max(0.0, (datetime.now() - dt).total_seconds())
    return float("inf")


def request_auto_refresh_if_stale(selected: str, section: Dict[str, Any], max_age_seconds: int = 20) -> int:
    """When a user opens/selects a status symbol, ask quant.py for a fresh monitor-only tick.

    This is throttled so the page's own auto reload does not generate a new seq every time.
    """
    if selected == "COMMON_BACKTEST_CONFIG":
        return 0
    state = read_state()
    if not isinstance(state, dict):
        state = {}
    meta = state.setdefault("_meta", {})
    symbol_code = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
    age = _status_age_seconds(selected, section, state)
    last_key = str(meta.get("web_auto_refresh_symbol_key", "") or "")
    last_at = _parse_web_time(str(meta.get("web_auto_refresh_requested_at", "") or ""))
    recently_requested = bool(last_at and (datetime.now() - last_at).total_seconds() < max(8, int(max_age_seconds)))
    if last_key == selected and recently_requested and age <= max_age_seconds:
        return 0
    if last_key != selected or age > max_age_seconds:
        seq = request_force_refresh_symbol(selected, symbol_code)
        state = read_state()
        if isinstance(state, dict):
            meta = state.setdefault("_meta", {})
            meta["web_auto_refresh_symbol_key"] = selected
            meta["web_auto_refresh_symbol_code"] = symbol_code
            meta["web_auto_refresh_requested_at"] = current_time_text()
            write_state(state)
        return seq
    return 0


def refresh_reference_prices_now(selected: str, section: Dict[str, Any]) -> Tuple[List[Dict[str, Any]], str]:
    """Synchronously refresh the 3 realtime quote cards for the selected symbol."""
    symbol = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
    if not symbol:
        return [], "未找到标的代码"
    try:
        from market_data import get_reference_prices
        refs = get_reference_prices(symbol, price_scale=safe_float(section.get("price_scale", 1.0), 1.0))
        refs = _filter_reference_prices_for_symbol(symbol, refs)
        if symbol.startswith("HK"):
            refs = _sanitize_hk_reference_prices(refs)
        error = "" if refs else "参考价返回为空"
    except Exception as e:
        refs, error = [], str(e)[:300]
    state = read_state()
    if not isinstance(state, dict):
        state = {}
    updated_at = current_time_text()
    if isinstance(refs, list):
        for _ref in refs:
            if isinstance(_ref, dict):
                _ref["updated_at"] = updated_at
    for key in [selected, symbol]:
        if not key:
            continue
        node = state.setdefault(key, {})
        if isinstance(node, dict):
            node["symbol"] = symbol
            node["reference_prices"] = refs
            node["reference_prices_updated_at"] = updated_at
            node["reference_prices_error"] = error
    write_state(state)
    return refs, error


def reference_source_options_for_symbol(symbol_text: str) -> List[Tuple[str, str]]:
    """Return the configured realtime quote source cards for the selected symbol.

    The status page uses this when merging a single-source refresh back into the
    cached 3-card list. Keeping it here avoids a NameError on
    /refresh-reference-price and guarantees the cards stay in the same order as
    market_data.py.
    """
    raw = str(symbol_text or "").upper().strip()
    field = "HK_MARKET_SOURCE" if raw.startswith("HK") else "A_QUOTE_SOURCE"
    return [(str(key), _market_display_source_name(key)) for key, _label in _market_source_options(field)]


def refresh_reference_price_source_now(selected: str, section: Dict[str, Any], source_key: str) -> Tuple[Dict[str, Any], str]:
    """Synchronously refresh exactly one realtime quote card, without touching status text."""
    symbol = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
    source_key = str(source_key or "").strip()
    if not symbol:
        return {}, "未找到标的代码"
    try:
        if not market_get_reference_price_by_source:
            raise RuntimeError("market_data.get_reference_price_by_source 不可用")
        ref = market_get_reference_price_by_source(symbol, source_key, price_scale=safe_float(section.get("price_scale", 1.0), 1.0))
        error = "" if ref else "参考价返回为空"
    except Exception as e:
        ref, error = {}, str(e)[:300]
    state = read_state()
    if not isinstance(state, dict):
        state = {}
    updated_at = current_time_text()
    if isinstance(ref, dict) and ref:
        ref["updated_at"] = updated_at
    for key in [selected, symbol]:
        if not key:
            continue
        node = state.setdefault(key, {})
        if not isinstance(node, dict):
            continue
        node["symbol"] = symbol
        existing = node.get("reference_prices") if isinstance(node.get("reference_prices"), list) else []
        by_key = {str(x.get("key", "")): dict(x) for x in existing if isinstance(x, dict)}
        if ref:
            by_key[source_key] = ref
        # Keep all configured cards present and in configured order. Missing cards stay as 待刷新.
        merged = []
        for opt_key, opt_label in reference_source_options_for_symbol(symbol):
            item = by_key.get(opt_key)
            if not item:
                item = {"key": opt_key, "label": opt_label, "price": None, "source": opt_label, "date": "", "updated_at": "", "ok": False, "primary": False, "error": "待刷新"}
            merged.append(item)
        node["reference_prices"] = merged
        node["reference_prices_updated_at"] = updated_at
        node["reference_prices_error"] = error
    write_state(state)
    return ref, error


def refresh_status_snapshot_now(selected: str, section: Dict[str, Any]) -> Tuple[bool, str]:
    """Best-effort immediate monitor-only status refresh from the Web process.

    In the deployed project this imports quant.py and calls strategy_for_quant with
    allow_trade=False, so clicking refresh updates last_status_msg right away.
    If importing quant.py fails, the normal background seq path still handles it.
    """
    if selected == "COMMON_BACKTEST_CONFIG":
        return False, "通用回测参数无实时状态"
    try:
        import importlib
        quant_runtime = importlib.import_module("quant")
        symbol_cfg, strategy_cfg, full_cfg = quant_runtime.load_config(quant_runtime.config_path)
        quant_runtime.SYMBOL_CONFIG = symbol_cfg
        quant_runtime.FULL_CONFIG = full_cfg
        quant_runtime.STRATEGY.update(strategy_cfg)
        state = read_state()
        if not isinstance(state, dict):
            state = {}
        quant_runtime.strategy_for_quant(
            selected,
            dict(section or {}),
            state,
            allow_trade=False,
            allow_monitor=False,
            refresh_reason="Web即时刷新，仅更新状态",
            refresh_reference=True,
        )
        node = state.get(selected, {}) if isinstance(state, dict) else {}
        if isinstance(node, dict):
            node["status_updated_at"] = current_time_text()
            node["symbol"] = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
        quant_runtime.save_state(state)
        return True, "已即时刷新状态"
    except Exception as e:
        return False, str(e)[:300]


def request_source_metrics_refresh_symbol(selected: str, symbol_code: str = "") -> int:
    """Ask quant.py to calculate per-history-source strategy metrics for one symbol.

    This is independent from status refresh. It is monitor-only and only writes
    source_metrics cache into quant_monitor_state.json for Web display.
    """
    state = read_state()
    if not isinstance(state, dict):
        state = {}
    meta = state.setdefault("_meta", {})
    try:
        seq = int(meta.get("source_metrics_refresh_seq", 0) or 0) + 1
    except Exception:
        seq = 1
    meta["source_metrics_refresh_seq"] = seq
    meta["source_metrics_refresh_requested_at"] = current_time_text()
    meta["source_metrics_refresh_symbol_key"] = selected
    meta["source_metrics_refresh_symbol_code"] = str(symbol_code or "").strip().upper()
    meta["source_metrics_refresh_symbols"] = [selected] if selected and selected != "COMMON_BACKTEST_CONFIG" else []
    write_state(state)
    return seq




def request_clear_market_state(selected: str, symbol_code: str = "") -> int:
    """Ask quant.py to reset runtime state and clear market validation/error state for one symbol."""
    state = read_state()
    if not isinstance(state, dict):
        state = {}
    meta = state.setdefault("_meta", {})
    try:
        seq = int(meta.get("clear_market_state_seq", 0) or 0) + 1
    except Exception:
        seq = 1
    selected = str(selected or "").strip()
    symbol_code = str(symbol_code or "").strip().upper()
    meta["clear_market_state_seq"] = seq
    meta["clear_market_state_requested_at"] = current_time_text()
    meta["clear_market_state_symbol_key"] = selected
    meta["clear_market_state_symbol_code"] = symbol_code
    meta["clear_market_state_symbols"] = [selected] if selected and selected != "COMMON_BACKTEST_CONFIG" else []
    write_state(state)
    return seq

def _market_source_options(field: str) -> List[Tuple[str, str]]:
    """Return source options from market_data.py, with local fallback only for import failure."""
    if market_get_source_options:
        try:
            options = market_get_source_options(field)
            if isinstance(options, list):
                return [(str(k), str(v)) for k, v in options]
        except Exception:
            pass
    return list(SYSTEM_SELECT_OPTIONS.get(field, []))


def _market_display_source_name(source: Any) -> str:
    """Customer-facing source name from market_data.py; no page-level source-name hardcoding."""
    if market_get_source_display_name:
        try:
            return market_get_source_display_name(str(source or ""))
        except Exception:
            pass
    return str(source or "")


def _reference_card_stable_key(field: str, item: Dict[str, Any], allowed_keys: set) -> str:
    """Normalize a cached/reference card to the stable source key for this field."""
    if not isinstance(item, dict):
        return ""
    values = [item.get("key", ""), item.get("source", ""), item.get("label", "")]
    for value in values:
        try:
            key = normalize_system_source_value(field, value)
        except Exception:
            key = str(value or "").strip()
        if key in allowed_keys:
            return key
    return ""


def _filter_reference_prices_for_symbol(symbol_text: str, refs: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Return one realtime-reference card per current source option.

    This deliberately completes stale cached data with placeholders.  If an older
    state file only cached two HK quote cards, the status page will still render
    all three cards from market_data.py, and the missing card will show as待刷新
    until the next manual/background refresh fills it.
    """
    raw = str(symbol_text or "").upper().strip()
    field = "HK_MARKET_SOURCE" if raw.startswith("HK") else "A_QUOTE_SOURCE"
    options = _market_source_options(field)
    if not options:
        return []
    allowed_keys = {str(k) for k, _ in options}
    existing: Dict[str, Dict[str, Any]] = {}
    if isinstance(refs, list):
        for item in refs:
            if not isinstance(item, dict):
                continue
            stable_key = _reference_card_stable_key(field, item, allowed_keys)
            if stable_key and stable_key not in existing:
                existing[stable_key] = dict(item)

    out = []
    try:
        preferred_key = normalize_system_source_value(field, read_system_config().get(field, ""))
    except Exception:
        preferred_key = options[0][0]
    for key, _label in options:
        key = str(key)
        label = _market_display_source_name(key)
        card = existing.get(key, {})
        if card:
            card = dict(card)
            card["key"] = key
            card["label"] = label
            card["source"] = label
            card["primary"] = key == preferred_key
            card.setdefault("ok", False)
            card.setdefault("price", None)
            card.setdefault("date", "")
            card.setdefault("error", "")
            if "easyquotation 未安装" in str(card.get("error", "")):
                card["ok"] = False
                card["price"] = None
                card["error"] = "待刷新"
        else:
            card = {
                "key": key,
                "label": label,
                "price": None,
                "source": label,
                "date": "",
                "ok": False,
                "primary": key == preferred_key,
                "error": "待刷新",
            }
        out.append(card)
    return out


def get_reference_prices_for_status(selected: str, section: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Read cached reference prices for status page.

    The web process must not fetch market APIs synchronously; otherwise clicking
    status/refresh can block Flask workers and cause 500/timeout. quant.py updates
    this cache during normal/forced refresh loops.
    """
    symbol = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
    if not symbol:
        return []
    state = read_state()
    candidates = []
    if selected:
        candidates.append(selected)
    candidates.append(symbol)
    # 兼容状态文件中以标的代码字段保存的情况
    for key, val in (state or {}).items():
        if isinstance(val, dict) and str(val.get("symbol", "")).strip().upper() == symbol:
            candidates.append(key)
    seen = set()
    for key in candidates:
        if not key or key in seen:
            continue
        seen.add(key)
        node = state.get(key, {}) if isinstance(state, dict) else {}
        refs = node.get("reference_prices") if isinstance(node, dict) else None
        if isinstance(refs, list) and refs:
            symbol_text = str((section or {}).get("symbol", "") or "").upper().strip()
            refs = _filter_reference_prices_for_symbol(symbol_text, refs)
            if symbol_text.startswith("HK"):
                return _sanitize_hk_reference_prices(refs)
            return refs
    return []

def _filter_source_metrics_for_current_setting(section: Dict[str, Any], metrics: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Show only the currently selected 回测/策略数据源 metric card.

    Older cached metrics may contain 3 cards from prior versions. The status page
    should now display one card only: the source selected in System settings.
    """
    symbol = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
    options = _metric_source_options_for_symbol(symbol)
    if not options:
        return []
    wanted_key, wanted_label = options[0]
    wanted_display = display_source_name(wanted_key)
    for item in metrics:
        if not isinstance(item, dict):
            continue
        item_key = str(item.get("key", ""))
        item_source = str(item.get("source", ""))
        if item_key == wanted_key or display_source_name(item_key) == wanted_display or display_source_name(item_source) == wanted_display:
            card = dict(item)
            card.setdefault("label", wanted_label)
            card["key"] = display_source_name(card.get("key") or wanted_key)
            card["source"] = display_source_name(card.get("source") or wanted_key)
            return [card]
    return [{
        "key": wanted_key,
        "label": wanted_label,
        "source": wanted_key,
        "ok": True,
        "level": "INFO",
        "status": "PENDING",
        "error": "",
        "current_price": None,
        "ma150": None,
        "sell": None,
        "clear": None,
        "dynamic_k": None,
        "sideways_score": None,
        "ma150_source": "",
        "date": "",
        "count": 0,
        "zone": "",
    }]


def _source_metric_from_strategy_cache_for_status(node: Dict[str, Any], section: Dict[str, Any]) -> Tuple[List[Dict[str, Any]], str, str]:
    """Fallback: show the latest strategy calculation as 回测/策略数据源指标."""
    if not isinstance(node, dict):
        return [], "", ""
    cache = node.get("strategy_calc_cache") if isinstance(node.get("strategy_calc_cache"), dict) else {}
    source = display_source_name(node.get("strategy_source") or cache.get("strategy_source") or "")
    if not source:
        symbol = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
        source = "tencent_hk" if symbol.startswith("HK") else "tencent_a"
    ma150 = safe_float(node.get("ma_short", cache.get("ma150")), 0.0)
    current_price = safe_float(node.get("last_price", cache.get("current_price")), 0.0)
    if ma150 <= 0 and current_price <= 0 and not node.get("strategy_error"):
        return [], "", ""
    ma_src = str(node.get("ma_short_source") or cache.get("ma150_source") or "")
    dynamic_k = safe_float(node.get("dynamic_k150", cache.get("dynamic_k150")), 0.0)
    sideways = safe_float(node.get("sideways_score", cache.get("sideways_score")), 0.0)
    updated_at = str(node.get("strategy_calc_updated_at") or cache.get("updated_at") or node.get("status_updated_at") or "")
    last_bar_date = str(cache.get("last_bar_date") or node.get("last_valid_bar_date") or "")
    level = str(node.get("strategy_level") or ("INFO" if ma150 > 0 else "ERROR")).upper()
    status = str(node.get("strategy_status") or ("OK" if ma150 > 0 else "ERROR")).upper()
    error = str(node.get("strategy_error") or "")
    if ma150 > 0 and ma_src and ma_src != "f" and level == "INFO":
        level = "WARN"
        status = "WARN"
        error = error or f"策略数据为非完整口径: MA150来源={ma_src}"
    zone = ""
    try:
        if ma150 > 0 and current_price > 0:
            zone = _get_zone_for_metrics(current_price, ma150, section)
    except Exception:
        zone = ""
    item = {
        "key": source,
        "label": f"{source} 策略值",
        "ok": bool(ma150 > 0 and level != "ERROR"),
        "level": level,
        "status": status,
        "source": source,
        "date": last_bar_date,
        "updated_at": updated_at,
        "count": int(safe_float(cache.get("history_count", node.get("history_count", 0)), 0)),
        "current_price": round(current_price, 4) if current_price else None,
        "ma150": round(ma150, 4) if ma150 else None,
        "ma150_source": ma_src,
        "sell": round(ma150 * safe_float(section.get("trend_multiple", 1.2), 1.2), 4) if ma150 else None,
        "clear": round(ma150 * safe_float(section.get("sell_multiple", 1.5), 1.5), 4) if ma150 else None,
        "dynamic_k": round(dynamic_k, 4) if dynamic_k else None,
        "sideways_score": round(sideways, 4),
        "zone": zone,
        "error": error,
    }
    return [item], updated_at, error


class MetricDisplayDict(dict):
    """Dictionary wrapper for Jinja templates.

    Jinja dot access on a plain dict can collide with dict methods. In
    particular, ``metric.clear`` resolves to ``dict.clear`` instead of the
    business field named ``clear``. The status template historically uses
    dot access, so expose a read-only attribute that returns the Clear price.
    """

    @property
    def clear(self):
        return self.get("clear")

    @property
    def clear_price(self):
        return self.get("clear")


def _metric_display_card(item: Dict[str, Any]) -> MetricDisplayDict:
    card = MetricDisplayDict(dict(item or {}))
    # Keep an alias for any future template that avoids the reserved dict name.
    if "clear" in card and "clear_price" not in card:
        card["clear_price"] = card.get("clear")
    return card


def _is_pending_metric_message(text: Any) -> bool:
    return str(text or "").strip() in {"", "点击刷新计算", "待刷新", "未刷新", "请点击刷新计算"}

def _metric_error_text(item: Dict[str, Any]) -> str:
    if not isinstance(item, dict):
        return ""
    err = str(item.get("error", "") or "").strip()
    if _is_pending_metric_message(err):
        return ""
    return err

def _collect_metric_errors(metrics: List[Dict[str, Any]]) -> str:
    errors = []
    for item in metrics or []:
        if not isinstance(item, dict):
            continue
        err = _metric_error_text(item)
        level = str(item.get("level", "") or "").upper()
        if err and (not item.get("ok") or level in {"WARN", "ERROR"}):
            errors.append(err)
    return "；".join(errors)

def _status_text_with_badge(status_text: str, level: str) -> str:
    level = str(level or "INFO").upper()
    if level == "ERROR":
        badge = "🔴[ERROR]"
    elif level == "WARN":
        badge = "🟡[WARN]"
    else:
        badge = "🟢[INFO]"
    lines = str(status_text or "").splitlines()
    if not lines:
        return status_text or ""
    head = lines[0]
    for old_badge in ("🟢[INFO]", "🟡[WARN]", "🔴[ERROR]"):
        if old_badge in head:
            head = head.replace(old_badge, badge, 1)
            break
    lines[0] = head
    return "\n".join(lines)


def _normalize_metric_cards(metrics: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    out = []
    for item in metrics or []:
        if not isinstance(item, dict):
            continue
        card = dict(item)
        for key in ("source", "key"):
            if card.get(key):
                card[key] = display_source_name(card.get(key))
        if "level" not in card:
            card["level"] = "INFO" if card.get("ok") else "ERROR"
        if "status" not in card:
            card["status"] = "OK" if card.get("ok") else card.get("level", "ERROR")
        if "clear" in card and "clear_price" not in card:
            card["clear_price"] = card.get("clear")
        out.append(_metric_display_card(card))
    return out


def _metric_display_cards(metrics: List[Dict[str, Any]]) -> List[MetricDisplayDict]:
    return [_metric_display_card(x) for x in (metrics or []) if isinstance(x, dict)]


def _strategy_history_cache_dir() -> Path:
    path = BASE_DIR / "data" / "strategy_history"
    path.mkdir(parents=True, exist_ok=True)
    return path


def _strategy_history_final_cache_path(symbol: str, day_text: str = "") -> Path:
    safe_symbol = re.sub(r"[^A-Za-z0-9_.-]+", "_", normalize_symbol_input(symbol)) or "UNKNOWN"
    day_text = day_text or web_strategy_now(read_yaml()).strftime("%Y-%m-%d")
    return _strategy_history_cache_dir() / f"{safe_symbol}_{day_text}.json"


def _read_strategy_history_final_cache(symbol: str) -> Dict[str, Any]:
    """Read only final strategy result cache: SYMBOL_YYYY-MM-DD.json.

    Ignore source-level diagnostic snapshots like
    SYMBOL_historical_a3_400_1p0_YYYY-MM-DD.json.
    """
    safe_symbol = re.sub(r"[^A-Za-z0-9_.-]+", "_", normalize_symbol_input(symbol)) or "UNKNOWN"
    today = web_strategy_now(read_yaml()).strftime("%Y-%m-%d")
    exact = _strategy_history_final_cache_path(safe_symbol, today)
    candidates = [exact]
    pattern = re.compile(rf"^{re.escape(safe_symbol)}_\d{{4}}-\d{{2}}-\d{{2}}\.json$")
    try:
        candidates.extend(sorted(
            [p for p in _strategy_history_cache_dir().glob(f"{safe_symbol}_*.json") if pattern.match(p.name) and p != exact],
            key=lambda x: x.name,
            reverse=True,
        ))
    except Exception:
        pass
    for path in candidates:
        try:
            if path.exists():
                data = json.loads(path.read_text(encoding="utf-8") or "{}")
                if isinstance(data, dict):
                    return data
        except Exception:
            continue
    return {}




def _metric_from_strategy_history_payload(payload: Dict[str, Any], section: Dict[str, Any], node: Dict[str, Any] = None) -> Tuple[List[Dict[str, Any]], str, str]:
    if not isinstance(payload, dict) or not payload:
        return [], "", ""
    ma150 = safe_float(payload.get("ma150"), 0.0)
    ma150_raw = safe_float(payload.get("ma150_raw"), 0.0)
    dynamic_k = safe_float(payload.get("dynamic_k150"), 1.0)
    if ma150 <= 0 and ma150_raw > 0:
        ma150 = ma150_raw * dynamic_k
    if ma150 <= 0:
        return [], "", ""
    source = display_source_name(payload.get("strategy_source") or payload.get("strategy_source_key") or "")
    if payload.get("strategy_source_fallback"):
        source = f"{source}（本轮兜底）"
    current_price = safe_float((node or {}).get("last_price"), 0.0)
    try:
        if current_price <= 0:
            current_price = safe_float(payload.get("current_price"), 0.0)
    except Exception:
        pass
    trend_multiple = safe_float(section.get("trend_multiple", 1.2), 1.2)
    clear_multiple = safe_float(section.get("sell_multiple", 1.5), 1.5)
    ma_src = str(payload.get("ma150_source") or "")
    status = str(payload.get("strategy_status") or ("OK" if ma_src == "f" else "WARN")).upper()
    level = "INFO" if status == "OK" else "WARN"
    err = "" if ma_src == "f" else f"策略数据为非完整口径: MA150来源={ma_src}"
    try:
        zone = _get_zone_for_metrics(current_price, ma150, section) if current_price > 0 else ""
    except Exception:
        zone = ""
    item = {
        "key": "strategy_history",
        "label": source or "本标的策略值",
        "ok": True,
        "level": level,
        "status": status,
        "source": source,
        "date": str(payload.get("last_bar_date") or payload.get("cache_date") or ""),
        "updated_at": str(payload.get("updated_at") or ""),
        "count": int(safe_float(payload.get("history_count", 0), 0)),
        "current_price": round(current_price, 4) if current_price > 0 else None,
        "ma150": round(ma150, 4),
        "ma150_source": ma_src,
        "sell": round(ma150 * trend_multiple, 4),
        "clear": round(ma150 * clear_multiple, 4),
        "dynamic_k": round(dynamic_k, 4),
        "sideways_score": round(safe_float(payload.get("sideways_score"), 0.0), 4),
        "zone": zone,
        "error": err,
    }
    return [item], str(payload.get("updated_at") or ""), err


def get_source_metrics_for_status(selected: str, section: Dict[str, Any]) -> Tuple[List[Dict[str, Any]], str, str]:
    """Read cached history-source metrics for status page.

    quant.py calculates these after clicking the independent refresh button. The
    Web process only reads local JSON cache to avoid blocking on network calls.
    """
    if selected == "COMMON_BACKTEST_CONFIG":
        return [], "", ""
    state = read_state()
    symbol = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
    final_payload = _read_strategy_history_final_cache(symbol) if symbol else {}
    if final_payload:
        first_node = None
        if isinstance(state, dict):
            first_node = state.get(selected) if isinstance(state.get(selected), dict) else None
            if not first_node and symbol:
                first_node = state.get(symbol) if isinstance(state.get(symbol), dict) else None
        final_metrics, final_updated, final_err = _metric_from_strategy_history_payload(final_payload, section, first_node)
        if final_metrics:
            return _normalize_metric_cards(final_metrics), final_updated, final_err
    candidates = [selected, symbol]
    if symbol:
        for key, val in (state or {}).items():
            if isinstance(val, dict) and str(val.get("symbol", "")).strip().upper() == symbol:
                candidates.append(key)
    seen = set()
    for key in candidates:
        if not key or key in seen:
            continue
        seen.add(key)
        node = state.get(key, {}) if isinstance(state, dict) else {}
        metrics = node.get("source_metrics") if isinstance(node, dict) else None
        if isinstance(metrics, list) and metrics:
            selected_metrics = _normalize_metric_cards(_filter_source_metrics_for_current_setting(section, metrics))
            if selected_metrics:
                err = str(node.get("source_metrics_error", "") or "").strip()
                if _is_pending_metric_message(err):
                    err = ""
                if not err:
                    err = _collect_metric_errors(selected_metrics)
                return selected_metrics, str(node.get("source_metrics_updated_at", "") or ""), err
        fallback, updated_at, err = _source_metric_from_strategy_cache_for_status(node, section)
        if fallback:
            return _normalize_metric_cards(fallback), updated_at, err
    return [], "", ""


def _metric_source_options_for_symbol(symbol: str) -> List[Tuple[str, str]]:
    """Return the selected history source for Web strategy metrics."""
    raw = normalize_symbol_input(symbol)
    system_cfg = read_system_config()
    if raw.startswith("HK"):
        labels = dict(SYSTEM_SELECT_OPTIONS.get("HK_BACKTEST_SOURCE", []))
        preferred = normalize_system_source_value("HK_BACKTEST_SOURCE", system_cfg.get("HK_BACKTEST_SOURCE", "historical_hk1"))
        return [(preferred, labels.get(preferred, preferred))]
    labels = dict(SYSTEM_SELECT_OPTIONS.get("A_BACKTEST_SOURCE", []))
    preferred = normalize_system_source_value("A_BACKTEST_SOURCE", system_cfg.get("A_BACKTEST_SOURCE", "historical_a1"))
    return [(preferred, labels.get(preferred, preferred))]

def _compute_ma_series_for_metrics(closes: List[float], period: int) -> List[float]:
    if len(closes) < period:
        return []
    series = []
    window = sum(closes[:period])
    series.append(window / period)
    for i in range(period, len(closes)):
        window += closes[i] - closes[i - period]
        series.append(window / period)
    return series


def _sideways_score_for_metrics(ma_series: List[float], window: int) -> float:
    n = len(ma_series)
    if n < window + 1:
        return 0.5
    seg = ma_series[-(window + 1):]
    deltas = [seg[i + 1] - seg[i] for i in range(window)]
    total = sum(abs(x) for x in deltas)
    if total == 0:
        return 1.0
    return max(0.0, min(1.0, 1.0 - abs(sum(deltas)) / total))


def _compute_sideways_index_for_metrics(closes: List[float], cfg: Dict[str, Any]) -> float:
    period30, period60 = 30, 60
    window30 = int(safe_float(cfg.get("sideways_window_30", 30), 30))
    window60 = int(safe_float(cfg.get("sideways_window_60", 20), 20))
    weight60 = max(0.0, min(1.0, safe_float(cfg.get("sideways_weight_60", 0.6), 0.6)))
    need = max(period30 + window30 + 1, period60 + window60 + 1)
    if len(closes) < need:
        return 0.0
    ma30 = _compute_ma_series_for_metrics(closes, period30)
    ma60 = _compute_ma_series_for_metrics(closes, period60)
    if not ma30 or not ma60:
        return 0.0
    return max(0.0, min(1.0, (1.0 - weight60) * _sideways_score_for_metrics(ma30, window30) + weight60 * _sideways_score_for_metrics(ma60, window60)))


def _calc_ma_for_metrics(closes: List[float], length: int) -> Tuple[Any, str]:
    if len(closes) >= length:
        return sum(closes[-length:]) / length, "p" if len(closes) < length * 2 else "f"
    if len(closes) >= max(5, length // 2):
        return sum(closes) / len(closes), "p"
    return None, "insufficient_data"


def _get_zone_for_metrics(current_price: float, ma150: float, cfg: Dict[str, Any]) -> str:
    try:
        from strategy import get_zone
        return str(get_zone(current_price, ma150, cfg))
    except Exception:
        trend_multiple = safe_float(cfg.get("trend_multiple", 1.2), 1.2)
        sell_multiple = safe_float(cfg.get("sell_multiple", 1.5), 1.5)
        if current_price < ma150:
            return "CHANCE_ZONE"
        if current_price < ma150 * trend_multiple:
            return "BOX_ZONE"
        if current_price < ma150 * sell_multiple:
            return "TREND_ZONE"
        return "CLEAR_ZONE"


def build_source_metric_placeholders(section: Dict[str, Any]) -> List[Dict[str, Any]]:
    symbol = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
    return [
        {
            "key": key,
            "label": label,
            "source": key,
            "ok": True,
            "level": "INFO",
            "status": "PENDING",
            "error": "",
            "current_price": None,
            "ma150": None,
            "sell": None,
            "clear": None,
            "dynamic_k": None,
            "sideways_score": None,
            "ma150_source": "",
            "date": "",
            "count": 0,
            "zone": "",
        }
        for key, label in _metric_source_options_for_symbol(symbol)
    ]


def _calculate_single_source_metric(symbol: str, section: Dict[str, Any], source_key: str, source_label: str) -> Dict[str, Any]:
    """Return the final cached strategy metric; Web must not call history APIs directly."""
    payload = _read_strategy_history_final_cache(symbol)
    state = read_state()
    node = {}
    if isinstance(state, dict):
        for _k, _v in state.items():
            if isinstance(_v, dict) and normalize_symbol_input(str(_v.get("symbol", "") or "")) == normalize_symbol_input(symbol):
                node = _v
                break
    metrics, _, err = _metric_from_strategy_history_payload(payload, section, node)
    if metrics:
        item = dict(metrics[0])
        item.setdefault("key", "strategy_history")
        return item
    return {
        "key": "strategy_history",
        "label": "本标的策略值",
        "source": "本标的策略值",
        "ok": False,
        "level": "PENDING",
        "status": "PENDING",
        "error": err or "已请求刷新本标的最终策略指标，等待后台策略写入结果。",
        "current_price": None,
        "ma150": None,
        "ma150_source": "",
        "sell": None,
        "clear": None,
        "dynamic_k": None,
        "sideways_score": None,
        "date": "",
        "count": 0,
        "zone": "",
    }

def _store_source_metrics(selected: str, symbol: str, metrics: List[Dict[str, Any]], error: str = "") -> Tuple[List[Dict[str, Any]], str, str]:
    updated_at = current_time_text()
    state = read_state()
    node = state.setdefault(selected, {}) if isinstance(state, dict) else {}
    metrics = _normalize_metric_cards(metrics)
    error = str(error or "").strip()
    if _is_pending_metric_message(error):
        error = ""
    if not error:
        error = _collect_metric_errors(metrics)
    node["source_metrics"] = metrics
    node["source_metrics_updated_at"] = updated_at
    node["source_metrics_error"] = error or ""
    if symbol:
        node["symbol"] = symbol
        state.setdefault(symbol, {})
        if isinstance(state.get(symbol), dict):
            state[symbol]["source_metrics"] = metrics
            state[symbol]["source_metrics_updated_at"] = updated_at
            state[symbol]["source_metrics_error"] = error or ""
            state[symbol]["symbol"] = symbol
    write_state(state)
    return metrics, updated_at, error or ""


def calculate_and_store_source_metric(selected: str, section: Dict[str, Any], source_key: str) -> Tuple[List[Dict[str, Any]], str, str]:
    """Request final strategy metric refresh; do not calculate a single source in Web.

    Source-level history snapshots are no longer generated from the status page.
    The daemon will refresh the final SYMBOL_YYYY-MM-DD strategy cache.
    """
    symbol = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
    payload = _read_strategy_history_final_cache(symbol) if symbol else {}
    state = read_state()
    node = state.get(selected, {}) if isinstance(state, dict) and isinstance(state.get(selected), dict) else {}
    metrics, updated_at, err = _metric_from_strategy_history_payload(payload, section, node)
    if metrics:
        return metrics, updated_at, err
    return build_source_metric_placeholders(section), "", "已请求刷新本标的最终策略指标，等待后台策略写入结果。"


def calculate_and_store_source_metrics(selected: str, section: Dict[str, Any]) -> Tuple[List[Dict[str, Any]], str, str]:
    """Request final strategy metric refresh; never generate per-source snapshots."""
    return calculate_and_store_source_metric(selected, section, "")


def _sanitize_hk_reference_prices(refs: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Protect status page from stale/wrong cached HK reference prices."""
    if not isinstance(refs, list):
        return []
    options = _market_source_options("HK_MARKET_SOURCE")
    primary_key = options[0][0] if options else "live_hk1"
    primary_name = _market_display_source_name(primary_key)
    base = None
    for item in refs:
        try:
            key = str(item.get("key", ""))
            label = str(item.get("label", ""))
            source = str(item.get("source", ""))
            if item.get("ok") and (key == primary_key or label == primary_name or _market_display_source_name(key) == primary_name or _market_display_source_name(source) == primary_name):
                base = float(item.get("price"))
                break
        except Exception:
            pass
    if not base or base <= 0:
        return refs
    clean = []
    for item in refs:
        item = dict(item or {})
        try:
            key = str(item.get("key", ""))
            label = str(item.get("label", ""))
            source = str(item.get("source", ""))
            is_primary = key == primary_key or label == primary_name or _market_display_source_name(key) == primary_name or _market_display_source_name(source) == primary_name
        except Exception:
            is_primary = False
        if not is_primary and item.get("ok"):
            try:
                p = float(item.get("price"))
                ratio = p / base
                if ratio < 0.75 or ratio > 1.25:
                    item["ok"] = False
                    item["error"] = f"参考价偏离{primary_name}过大: {p:.4f} vs {base:.4f}"
                    item["price"] = None
            except Exception:
                item["ok"] = False
                item["error"] = "参考价无法解析"
                item["price"] = None
        clean.append(item)
    return clean


def read_system_config() -> Dict[str, str]:
    cfg = dict(SYSTEM_DEFAULTS)
    if SYSTEM_CONFIG_FILE.exists():
        try:
            raw = json.loads(SYSTEM_CONFIG_FILE.read_text(encoding="utf-8") or "{}")
            if isinstance(raw, dict):
                cfg.update({k: "" if v is None else str(v).strip() for k, v in raw.items()})
        except Exception:
            pass
    for _field in ("A_QUOTE_SOURCE", "HK_MARKET_SOURCE", "A_BACKTEST_SOURCE", "HK_BACKTEST_SOURCE"):
        cfg[_field] = normalize_system_source_value(_field, cfg.get(_field, SYSTEM_DEFAULTS.get(_field, "")))
    cfg["XUEQIU_TOKEN"] = str(cfg.get("XUEQIU_TOKEN", "") or "").strip()
    cfg["XUEQIU_TOKEN_UPDATED_AT"] = str(cfg.get("XUEQIU_TOKEN_UPDATED_AT", "") or "").strip()
    cfg["XUEQIU_TOKEN_SOURCE"] = str(cfg.get("XUEQIU_TOKEN_SOURCE", "") or "").strip()
    return cfg


def write_system_config(cfg: Dict[str, Any]) -> Dict[str, str]:
    merged = dict(SYSTEM_DEFAULTS)
    merged.update({k: "" if v is None else str(v).strip() for k, v in (cfg or {}).items()})
    for _field in ("A_QUOTE_SOURCE", "HK_MARKET_SOURCE", "A_BACKTEST_SOURCE", "HK_BACKTEST_SOURCE"):
        merged[_field] = normalize_system_source_value(_field, merged.get(_field, SYSTEM_DEFAULTS.get(_field, "")))
    SYSTEM_CONFIG_FILE.write_text(json.dumps(merged, ensure_ascii=False, indent=2), encoding="utf-8")
    request_runtime_system_config_reload()
    return merged


def save_system_config_from_form() -> Dict[str, str]:
    cfg = read_system_config()
    for key in SYSTEM_DEFAULTS:
        if key in request.form:
            value = (request.form.get(key, "") or "").strip()
            if key == "XUEQIU_TOKEN" and value and ("=" in value or ";" in value):
                extracted = _extract_xueqiu_token_from_cookie(value)
                if extracted:
                    value = extracted
            cfg[key] = value
            if key == "XUEQIU_TOKEN" and value:
                cfg["XUEQIU_TOKEN_UPDATED_AT"] = current_time_text()
                cfg["XUEQIU_TOKEN_SOURCE"] = "web_manual"
    return write_system_config(cfg)


def read_strategy_settings(config: Dict[str, Any] = None) -> Dict[str, Any]:
    config = config if isinstance(config, dict) else read_yaml()
    raw = config.get("STRATEGY", {}) if isinstance(config, dict) else {}
    settings = dict(STRATEGY_DEFAULTS)
    if isinstance(raw, dict):
        settings.update(raw)
    return settings


def _convert_strategy_form_value(key: str, value: str) -> Any:
    value = str(value or "").strip()
    if key in {"loop_interval", "fetch_history_days", "ma_period_short", "ma_period_long"}:
        try:
            return int(float(value))
        except Exception:
            return int(STRATEGY_DEFAULTS.get(key, 0))
    return value


def save_strategy_settings_from_form(config: Dict[str, Any]) -> Dict[str, Any]:
    strategy = dict(config.get("STRATEGY", {}) or {})
    old_loop = str(strategy.get("loop_enabled", "yes") or "yes")
    if old_loop.lower() in ("no", "off", "false", "0"):
        old_loop_enabled = False
    else:
        old_loop_enabled = True
    for item in STRATEGY_FIELDS:
        key = item["key"]
        if key in request.form:
            strategy[key] = _convert_strategy_form_value(key, request.form.get(key, ""))
    # basic guardrails
    strategy["loop_interval"] = max(1, int(strategy.get("loop_interval", 60) or 60))
    strategy["fetch_history_days"] = max(2, int(strategy.get("fetch_history_days", 400) or 400))
    strategy["ma_period_short"] = max(5, int(strategy.get("ma_period_short", 150) or 150))
    strategy["ma_period_long"] = max(strategy["ma_period_short"], int(strategy.get("ma_period_long", 300) or 300))
    for tkey in ("session_start", "session_end", "daily_push_time", "log_rotate_time"):
        default_time = TIME_FIELD_DEFAULTS.get(tkey, STRATEGY_DEFAULTS.get(tkey, "09:30"))
        strategy[tkey] = DoubleQuotedScalarString(normalize_hhmm_value(strategy.get(tkey, default_time), default_time))
    strategy["timezone"] = str(strategy.get("timezone", "Asia/Shanghai") or "Asia/Shanghai").strip()
    config["STRATEGY"] = strategy
    write_yaml(config)
    new_loop = str(strategy.get("loop_enabled", "yes") or "yes")
    if new_loop.lower() in ("no", "off", "false", "0"):
        new_loop_enabled = False
    else:
        new_loop_enabled = True
    if old_loop_enabled and not new_loop_enabled:
        try:
            push_title = "🔴 策略总开关已关闭"
            push_body = f"策略总开关已手动关闭，时间：{current_time_text()}\n关闭后策略将继续刷新行情数据，但不会触发任何交易。"
            send_notification(push_body, title=push_title)
        except Exception:
            pass
    # quant.py reloads quant.yaml every loop; nudge it so sleep wakes early.
    try:
        state = read_state()
        meta = state.setdefault("_meta", {})
        meta["config_reload_seq"] = int(meta.get("config_reload_seq", 0) or 0) + 1
        meta["config_reload_symbols"] = ["__ALL__"]
        meta["strategy_config_updated_at"] = current_time_text()
        write_state(state)
    except Exception:
        pass
    return strategy


def _parse_push_log_time(text: str):
    try:
        m = re.search(r"(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})", str(text or ""))
        if not m:
            return None
        return datetime.strptime(m.group(1), "%Y-%m-%d %H:%M:%S")
    except Exception:
        return None


def _read_push_detail_records(limit: int = 300) -> List[Dict[str, Any]]:
    records: List[Dict[str, Any]] = []
    try:
        if not PUSH_DETAIL_LOG_FILE.exists():
            return records
        lines = PUSH_DETAIL_LOG_FILE.read_text(encoding="utf-8", errors="ignore").splitlines()
        for line in lines[-max(1, int(limit or 300)):]:
            try:
                obj = json.loads(line)
                if isinstance(obj, dict):
                    records.append(obj)
            except Exception:
                continue
    except Exception:
        pass
    return records


def _find_push_detail_for_log(compact: str, detail_records: List[Dict[str, Any]]) -> str:
    """Return pushed message body for one push.log line when available.

    push.log historically only recorded delivery status/bytes, not the payload.
    push.py/quant.py writes data/push_details.jsonl for non-snapshot pushes;
    this helper pairs records by timestamp and falls back to a clear note for old logs.
    """
    ts = _parse_push_log_time(compact)
    if ts and detail_records:
        best = None
        best_delta = 999999
        for rec in detail_records:
            try:
                rec_time = datetime.strptime(str(rec.get("time", ""))[:19], "%Y-%m-%d %H:%M:%S")
            except Exception:
                continue
            delta = abs((rec_time - ts).total_seconds())
            if delta < best_delta:
                best_delta = delta
                best = rec
        if best and best_delta <= 120:
            body = str(best.get("body", "") or "").strip()
            if body:
                return body
    if "bytes=" in compact or "成功" in compact or "失败" in compact:
        return compact + "\n\n每日快照推送！"
    return compact


def build_push_log_entries(lines: List[str]) -> List[Dict[str, Any]]:
    entries = []
    detail_records = _read_push_detail_records()
    for idx, line in enumerate(lines or []):
        text = str(line or "")
        compact = text.replace("\r", "").strip()
        is_snapshot = ("每日快照" in compact) or ("快照推送" in compact)
        first_line = compact.splitlines()[0] if compact else ""
        summary = first_line[:120] + ("…" if len(first_line) > 120 else "")
        if compact and is_snapshot:
            detail = "每日快照推送！"
        else:
            detail = _find_push_detail_for_log(compact, detail_records) if compact else ""
        entries.append({
            "id": f"push-log-{idx}",
            "summary": summary or compact[:120],
            "detail": detail,
            "is_snapshot": is_snapshot,
            "can_view": bool(compact),
        })
    return entries


def save_push_config_from_form() -> Dict[str, str]:
    cfg = read_push_config()
    for item in PUSH_FIELDS:
        key = item["key"]
        if key in request.form:
            cfg[key] = (request.form.get(key, "") or "").strip()
    if cfg.get("PUSH_ENABLED") not in {"yes", "no"}:
        cfg["PUSH_ENABLED"] = "yes"
    channel = str(cfg.get("PUSH_CHANNEL", "ntfy") or "ntfy").strip().lower()
    if channel in {"both", "all", "telegram", "pushplus", "none", ""}:
        channel = "ntfy"
    if channel not in PUSH_CHANNEL_VALUES:
        channel = "ntfy"
    cfg["PUSH_CHANNEL"] = channel
    try:
        priority = int(float(str(cfg.get("GOTIFY_PRIORITY", "10") or "10")))
    except Exception:
        priority = 10
    cfg["GOTIFY_PRIORITY"] = str(priority)
    try:
        ntfy_priority = int(float(str(cfg.get("NTFY_PRIORITY", "4") or "4")))
    except Exception:
        ntfy_priority = 4
    cfg["NTFY_PRIORITY"] = str(max(1, min(5, ntfy_priority)))
    cfg["NTFY_URL"] = str(cfg.get("NTFY_URL", "")).strip().rstrip("/") or PUSH_DEFAULTS.get("NTFY_URL", "http://127.0.0.1:8083")
    cfg["NTFY_TOPIC"] = str(cfg.get("NTFY_TOPIC", "")).strip().strip("/") or PUSH_DEFAULTS.get("NTFY_TOPIC", "Quant")
    write_push_config(cfg)
    return cfg

def current_time_text() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")

def _parse_hm_web(value: Any, default_h: int = 9, default_m: int = 30) -> Tuple[int, int]:
    default = f"{default_h:02d}:{default_m:02d}"
    text = normalize_hhmm_value(value, default)
    h, m = text.split(":", 1)
    return int(h), int(m)


def _strategy_timezone_name_from_config(config: Dict[str, Any]) -> str:
    aliases = {
        "shanghai": "Asia/Shanghai", "上海": "Asia/Shanghai", "china": "Asia/Shanghai", "cn": "Asia/Shanghai",
        "tokyo": "Asia/Tokyo", "东京": "Asia/Tokyo", "japan": "Asia/Tokyo", "jp": "Asia/Tokyo",
        "singapore": "Asia/Singapore", "新加坡": "Asia/Singapore", "sg": "Asia/Singapore",
        "los_angeles": "America/Los_Angeles", "los angeles": "America/Los_Angeles", "la": "America/Los_Angeles", "洛杉矶": "America/Los_Angeles",
    }
    strategy = config.get("STRATEGY", {}) if isinstance(config, dict) else {}
    raw = str(strategy.get("timezone", "Asia/Shanghai") or "Asia/Shanghai").strip()
    return aliases.get(raw.lower(), raw) if raw else "Asia/Shanghai"


def web_strategy_now(config: Dict[str, Any] = None) -> datetime:
    config = config if isinstance(config, dict) else read_yaml()
    name = _strategy_timezone_name_from_config(config)
    try:
        tz = ZoneInfo(name)
    except ZoneInfoNotFoundError:
        tz = ZoneInfo("Asia/Shanghai")
    return datetime.now(tz)


def web_in_trade_session(config: Dict[str, Any] = None) -> bool:
    config = config if isinstance(config, dict) else read_yaml()
    strategy = config.get("STRATEGY", {}) if isinstance(config, dict) else {}
    now = web_strategy_now(config)
    sh, sm = _parse_hm_web(strategy.get("session_start", "09:30"), 9, 30)
    eh, em = _parse_hm_web(strategy.get("session_end", "16:00"), 16, 0)
    return dt_time(sh, sm) <= now.time() <= dt_time(eh, em)


def trade_session_text(config: Dict[str, Any] = None) -> str:
    config = config if isinstance(config, dict) else read_yaml()
    strategy = config.get("STRATEGY", {}) if isinstance(config, dict) else {}
    return f"{strategy.get('session_start', '09:30')}-{strategy.get('session_end', '16:00')}（{_strategy_timezone_name_from_config(config)}）"

def safe_float(value: Any, default: float = 0.0) -> float:
    try:
        if value is None:
            return default
        if isinstance(value, str):
            value = value.strip()
            if value == "":
                return default
        return float(value)
    except Exception:
        return default

def safe_int(value: Any, default: int = 0) -> int:
    try:
        return int(float(value))
    except Exception:
        return default

def parse_runtime_position_value(value: Any) -> float:
    text = str(value or "").strip()
    if not text:
        return 0.0
    if text.endswith("%"):
        return safe_float(text[:-1], 0.0) / 100.0
    return safe_float(text, 0.0)

def normalize_symbol_input(symbol: str) -> str:
    s = (symbol or "").strip().upper().replace(" ", "")
    if not s:
        return s
    if s.startswith(("SH", "SZ", "HK")):
        return s
    if s.isdigit():
        if len(s) == 6:
            return f"SH{s}" if s.startswith("6") else f"SZ{s}"
        if len(s) <= 5:
            return f"HK{s.zfill(5)}"
    return s

def symbol_options(config: Dict[str, Any]) -> List[Tuple[str, str]]:
    result: List[Tuple[str, str]] = [("COMMON_BACKTEST_CONFIG", "通用回测参数")]
    symbol_cfg = config.get("SYMBOL_CONFIG", {}) or {}
    for name, item in symbol_cfg.items():
        symbol = str(item.get("symbol", "")).strip()
        result.append((name, f"{name} ({symbol})" if symbol else name))
    return result


def first_real_symbol_key(config: Dict[str, Any]) -> str:
    symbol_cfg = config.get("SYMBOL_CONFIG", {}) or {}
    for name in symbol_cfg.keys():
        if str(name).strip():
            return str(name)
    return ""

def get_section(config: Dict[str, Any], selected: str) -> Dict[str, Any]:
    if selected == "COMMON_BACKTEST_CONFIG":
        return config.get("COMMON_BACKTEST_CONFIG", {}) or {}
    return (config.get("SYMBOL_CONFIG", {}) or {}).get(selected, {}) or {}

def set_section(config: Dict[str, Any], selected: str, section: Dict[str, Any]) -> None:
    if selected == "COMMON_BACKTEST_CONFIG":
        config["COMMON_BACKTEST_CONFIG"] = section
    else:
        config.setdefault("SYMBOL_CONFIG", {})
        config["SYMBOL_CONFIG"][selected] = section

def latest_status_for(selected: str, state: Dict[str, Any]) -> str:
    if selected == "COMMON_BACKTEST_CONFIG":
        return "通用回测参数无实时状态。"
    item = state.get(selected, {}) if isinstance(state, dict) else {}
    raw = item.get("last_status_msg") if isinstance(item, dict) else None
    if raw in (None, "", "None"):
        return "暂无最新状态。"
    txt = str(raw).strip()
    if txt.lower().startswith("last_status_msg"):
        txt = txt.split(":", 1)[-1].strip()
    return txt or "暂无最新状态。"

def convert_form_value(key: str, value: str) -> Any:
    value = value.strip()
    if key in {"symbol", "strategy_run", "box_grid_enabled", "base_units", "target_units", "current_units", "pyramid_add_enabled"}:
        return value
    if key in {"pyramid_weights", "clear_pyramid_weights", "pyramid_add_weights"}:
        if not value:
            return []
        return [float(x.strip()) for x in value.split(",") if x.strip()]
    if key in {"sideways_window_30", "sideways_window_60", "pyramid_steps", "clear_pyramid_steps", "pyramid_add_steps"}:
        return int(float(value or 0))
    if value == "":
        return ""
    try:
        return float(value)
    except Exception:
        return value

def get_meta_from_state(selected: str, state: Dict[str, Any]) -> Dict[str, Any]:
    if selected == "COMMON_BACKTEST_CONFIG":
        return {"current_price": "", "last_time": ""}
    node = state.get(selected, {}) if isinstance(state, dict) else {}
    return {
        "current_price": node.get("last_price", ""),
        "last_time": node.get("last_time", ""),
    }

def build_grouped_fields(section: Dict[str, Any]) -> List[Dict[str, Any]]:
    grouped = []
    for group in FIELD_GROUPS:
        item_rows = []
        for key, label, field_type in group["items"]:
            raw = section.get(key, "")
            if isinstance(raw, list):
                display = ", ".join(str(x) for x in raw)
            elif isinstance(raw, bool):
                display = "true" if raw else "false"
            else:
                display = "" if raw is None else str(raw)
            item_rows.append(
                {
                    "key": key,
                    "label": label,
                    "type": field_type,
                    "value": display,
                    "readonly": True,
                    "options": SELECT_FIELD_OPTIONS.get(key, []),
                    "help": PARAM_HELP.get(key, ""),
                }
            )
        grouped.append({"id": group["id"], "title": group["title"], "items": item_rows})
    return grouped

def build_new_symbol_section(config: Dict[str, Any], symbol: str) -> Dict[str, Any]:
    common = deepcopy(config.get("COMMON_BACKTEST_CONFIG", {}) or {})
    common.pop("name", None)
    normalize_config({"COMMON_BACKTEST_CONFIG": common})
    common.pop("name", None)
    common["strategy_run"] = "on"
    common["box_grid_enabled"] = "no"
    common["pyramid_add_enabled"] = "auto"
    common["monitor_enabled"] = "off"
    common["monitor_price_1"] = ""
    common["monitor_price_2"] = ""
    common["monitor_arm_id"] = ""
    common.setdefault("current_units", common.get("base_units", ""))
    common.setdefault("current_avg_cost", 0.0)
    ordered = {"symbol": symbol}
    for k, v in common.items():
        if k != "symbol" and k != "name":
            ordered[k] = v
    return ordered

def _artifact_url(path: Path) -> str:
    return url_for("download_artifact", path=str(path))

def _strip_backtest_explanation(text: str) -> str:
    if not text:
        return text
    lines = []
    for line in text.splitlines():
        s = line.strip()
        if s.startswith('$ /root/quant/.venv/bin/python '):
            continue
        lines.append(line)
    text = "\n".join(lines).strip()
    marker = "\n说明："
    if marker in text:
        text = text.split(marker, 1)[0].rstrip()
    return text

def parse_backtest_output(text: str, symbol: str) -> Dict[str, Any]:
    summary_cards: List[Tuple[str, str]] = []
    files: Dict[str, Dict[str, str]] = {}
    if not text:
        return {"summary_cards": summary_cards, "files": files}
    kv: Dict[str, str] = {}
    artifact_paths: Dict[str, Path] = {}
    for line in text.splitlines():
        line_s = line.strip()
        m = re.match(r"^(日志|交易明细|事件明细|每日详情):\s*(.+)$", line_s)
        if m:
            label = m.group(1)
            path = Path(m.group(2).strip())
            if path.exists():
                artifact_paths[label] = path
            continue
        if ":" in line_s:
            key, value = line_s.split(":", 1)
            key = key.strip()
            value = value.strip()
            if key in SUMMARY_KEYS or key in {"买入次数", "卖出次数", "分红事件", "拆股事件"}:
                kv[key] = value
    # 交易/报告/配置/打包文件
    if symbol:
        outdir = BACKTEST_OUT_DIR / symbol
        report_path = outdir / f"backtest_report_{symbol}.txt"
        trades_path = outdir / f"trades_{symbol}.csv"
        daily_details_path = outdir / f"daily_details_{symbol}.csv"
        if report_path.exists():
            files["回测摘要"] = {"name": "回测摘要", "path": str(report_path), "url": _artifact_url(report_path)}
        if trades_path.exists():
            files["交易日志"] = {"name": "交易日志", "path": str(trades_path), "url": _artifact_url(trades_path)}
        if daily_details_path.exists():
            files["价格行情"] = {"name": "价格行情", "path": str(daily_details_path), "url": _artifact_url(daily_details_path)}

    def add(label: str, value: str):
        if value != "":
            summary_cards.append((label, value))

    def add_key(key: str, display_label: str = None):
        if key in kv:
            add(display_label or key, kv[key])

    # Web 摘要卡片展示顺序
    add_key("回测初始仓位")
    add_key("期末持仓收益率")
    add_key("综合收益率")
    if kv.get("买入次数") or kv.get("卖出次数"):
        add("买入/卖出次数", f"{kv.get('买入次数', '0')} | {kv.get('卖出次数', '0')}")

    add_key("分红收益率")
    add_key("交易实现收益率")
    add_key("持仓收益率")
    add_key("摊薄持仓收益率")

    add_key("最新价格")
    add_key("首次建仓原始价")
    add_key("首次建仓复权价")

    add_key("首次建仓日")
    if kv.get("分红事件") or kv.get("拆股事件"):
        add("分红/拆股事件", f"{kv.get('分红事件', '0')} | {kv.get('拆股事件', '0')}")
    add_key("除权息数据来源")
    if "最大回撤" in kv:
        add("最大回撤", kv["最大回撤"])
    else:
        add_key("最大回撤(参考)", "最大回撤")

    add_key("期末持仓")
    # 兼容旧报告
    add_key("期末持仓(成本口径)", "期末持仓")
    add_key("摊薄后持仓成本")
    # 兼容旧报告
    add_key("期末持仓成本", "摊薄后持仓成本")
    if "期末市值权重" in kv:
        add("期末市值权重", kv["期末市值权重"])
    elif "期末估算市值权重" in kv:
        add("期末市值权重", kv["期末估算市值权重"])
    elif "期末市值" in kv:
        add("期末市值", kv["期末市值"])
    return {"summary_cards": summary_cards, "files": files}

def run_backtest(symbol: str, days: int, initial_units: str) -> Dict[str, Any]:
    if not BACKTEST_FILE.exists():
        return {"output": "❌ 未找到 backtest_quant.py", "summary_cards": [], "files": {}}
    symbol = normalize_symbol_input(symbol)
    cmd = [
        sys.executable,
        str(BACKTEST_FILE),
        "--config",
        str(CONFIG_FILE),
        "--symbol",
        symbol,
        "--days",
        str(days),
    ]
    if initial_units.strip():
        cmd.extend(["--initial-units", initial_units.strip()])
    try:
        result = subprocess.run(
            cmd,
            cwd=str(BASE_DIR),
            capture_output=True,
            text=True,
            timeout=300,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return {"output": "❌ 回测超时，请缩短天数或检查网络。", "summary_cards": [], "files": {}}
    clean_stdout = _strip_backtest_explanation((result.stdout or "").strip())
    parts = []
    if clean_stdout:
        parts.append(clean_stdout)
    if result.stderr:
        parts.append("[stderr]\n" + result.stderr.strip())
    if result.returncode != 0 and not result.stderr and not clean_stdout:
        parts.append(f"❌ 回测失败，退出码={result.returncode}")
    output = "\n\n".join(x for x in parts if x)
    parsed = parse_backtest_output(clean_stdout, symbol)
    return {"output": output, **parsed}

def analyze_total_profit() -> str:
    import csv
    config = read_yaml()
    state = read_state()
    symbol_config = config.get("SYMBOL_CONFIG", {}) if isinstance(config, dict) else {}
    def get_mode_by_name(name: str) -> str:
        cfg = symbol_config.get(name, {}) if isinstance(symbol_config, dict) else {}
        base = cfg.get("base_units", 0)
        target = cfg.get("target_units", 0)
        if isinstance(base, str) and base.strip().endswith("%"):
            return "percent"
        if isinstance(target, str) and target.strip().endswith("%"):
            return "percent"
        try:
            if 0 <= float(base) <= 1 and 0 <= float(target) <= 1:
                return "percent"
        except Exception:
            pass
        return "absolute"
    def parse_dt(s: str):
        for fmt in ("%Y-%m-%d %H:%M:%S", "%Y.%m.%d.%H:%M", "%Y-%m-%d", "%Y/%m/%d %H:%M:%S"):
            try:
                return datetime.strptime(s, fmt)
            except Exception:
                pass
        return None
    if not TRADE_LOG_FILE.exists():
        return "未找到 trade_log.csv，暂无收益分析数据。"
    with TRADE_LOG_FILE.open(newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        rows = list(reader)
    rows.sort(key=lambda r: parse_dt(r.get("date", "")) or datetime.min)
    if not rows:
        return "trade_log.csv 为空。"
    class DCFStat:
        def __init__(self, name: str, symbol: str, mode: str):
            self.name = name
            self.symbol = symbol
            self.mode = mode
            self.trade_count = 0
            self.position = 0.0
            self.avg_cost = 0.0
            self.realized_total = 0.0
            self.total_investment = 0.0
        def process_trade(self, row: Dict[str, str]) -> None:
            price = safe_float(row.get("price", 0))
            qty = safe_float(row.get("qty", 0))
            side = (row.get("side", "") or "").upper()
            pos_after = safe_float(row.get("pos_after", 0))
            avg_cost_before = safe_float(row.get("avg_cost_before", 0))
            avg_cost_after = safe_float(row.get("avg_cost_after", 0))
            self.trade_count += 1
            self.position = pos_after
            if avg_cost_after > 0:
                self.avg_cost = avg_cost_after
            if side == "BUY" and self.mode == "absolute":
                self.total_investment += price * qty
            elif side == "SELL":
                if self.mode == "absolute":
                    self.realized_total += (price - avg_cost_before) * qty if avg_cost_before > 0 else 0.0
                else:
                    self.realized_total += qty * (price / avg_cost_before - 1.0) if avg_cost_before > 0 else 0.0
        def get_current_price(self) -> float:
            d = state.get(self.name, {}) if isinstance(state, dict) else {}
            return safe_float(d.get("last_price", 0))
        def get_current_value_or_weight(self) -> Tuple[float, float]:
            price = self.get_current_price()
            if self.mode == "absolute":
                current_value = self.position * price if price > 0 else self.position * self.avg_cost
                floating = (price - self.avg_cost) * self.position if self.position > 0 and self.avg_cost > 0 and price > 0 else 0.0
                return current_value, floating
            if self.position <= 0:
                return 0.0, 0.0
            if price > 0 and self.avg_cost > 0:
                market_weight = self.position * price / self.avg_cost
                floating = self.position * (price / self.avg_cost - 1.0)
            else:
                market_weight = self.position
                floating = 0.0
            return market_weight, floating
    quant_stats: Dict[Tuple[str, str], Any] = {}
    for row in rows:
        name = (row.get("quant_name", "") or "UNKNOWN").strip() or "UNKNOWN"
        symbol = (row.get("symbol", "") or "").strip()
        key = (name, symbol)
        if key not in quant_stats:
            quant_stats[key] = DCFStat(name, symbol, get_mode_by_name(name))
        quant_stats[key].process_trade(row)
    out: List[str] = ["=" * 60, "Quant 策略收益分析", "=" * 60]
    abs_total_realized = 0.0
    abs_total_investment = 0.0
    abs_total_current_value = 0.0
    pct_total_realized = 0.0
    pct_total_floating = 0.0
    pct_total_market_weight = 0.0
    for (name, symbol), stat in sorted(quant_stats.items(), key=lambda x: x[0][0]):
        out.extend(["", "=" * 50, f"标的: {name} ({symbol})", "-" * 50])
        current_price = stat.get_current_price()
        current_metric, floating_metric = stat.get_current_value_or_weight()
        if stat.mode == "absolute":
            out.append(f"总投入资金: {stat.total_investment:,.2f}")
            out.append(f"已实现收益: {stat.realized_total:,.2f}")
            out.append(f"当前持仓市值: {current_metric:,.2f}")
            abs_total_realized += stat.realized_total
            abs_total_investment += stat.total_investment
            abs_total_current_value += current_metric
        else:
            out.append(f"当前持仓(成本口径): {stat.position * 100:.2f}%")
            out.append(f"当前价格: {current_price:.4f}" if current_price > 0 else "当前价格: -")
            out.append(f"已实现收益贡献: {stat.realized_total * 100:.2f}%")
            out.append(f"浮动收益贡献: {floating_metric * 100:.2f}%")
            out.append(f"综合收益贡献: {(stat.realized_total + floating_metric) * 100:.2f}%")
            pct_total_realized += stat.realized_total
            pct_total_floating += floating_metric
            pct_total_market_weight += current_metric
    out.extend(["", "=" * 60, "总体汇总", "=" * 60])
    if abs_total_investment > 0:
        total_assets = abs_total_current_value + abs_total_realized
        out.append("[股数模式]")
        out.append(f"总投入资金: {abs_total_investment:,.2f}")
        out.append(f"总已实现收益: {abs_total_realized:,.2f}")
        out.append(f"当前持仓市值: {abs_total_current_value:,.2f}")
        out.append(f"总资产: {total_assets:,.2f}")
    if abs(pct_total_market_weight) > 1e-12 or abs(pct_total_realized) > 1e-12 or abs(pct_total_floating) > 1e-12:
        out.append("[百分比模式]")
        out.append(f"当前估算市值权重合计: {pct_total_market_weight * 100:.2f}%")
        out.append(f"已实现收益贡献合计: {pct_total_realized * 100:.2f}%")
        out.append(f"浮动收益贡献合计: {pct_total_floating * 100:.2f}%")
        out.append(f"综合收益贡献合计: {(pct_total_realized + pct_total_floating) * 100:.2f}%")
    return "\n".join(out)

@app.before_request
def require_login() -> Any:
    if request.endpoint in {"login", "static", "download_artifact", "download_backtest_bundle", "tokenapi_update_xueqiu_cookie"}:
        return None
    if not session.get("logged_in"):
        return redirect(url_for("login"))
    return None

@app.route("/login", methods=["GET", "POST"])
def login():
    cfg = load_web_config()
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        password = request.form.get("password", "")
        stored_user = str(cfg.get("admin_username", "admin") or "admin")
        stored_plain = str(cfg.get("admin_password", "") or cfg.get("password", "") or "")
        stored_hash = str(cfg.get("password_hash", "") or "")
        ok = False
        if username == stored_user:
            if stored_plain:
                ok = (password == stored_plain)
            elif stored_hash:
                ok = check_password_hash(stored_hash, password)
        if ok:
            session["logged_in"] = True
            session["username"] = username
            return redirect(url_for("status_page"))
        flash("用户名或密码错误", "error")
    return render_template("login.html", app_name=APP_DISPLAY_NAME, domain=cfg.get("domain", ""))

@app.route("/logout")
def logout():
    session.clear()
    return redirect(url_for("login"))

@app.route("/download-artifact")
def download_artifact():
    path_text = request.args.get("path", "").strip()
    if not path_text:
        abort(404)
    p = Path(path_text).expanduser().resolve()
    allowed_roots = [BACKTEST_OUT_DIR.resolve(), BASE_DIR.resolve()]
    if not any(str(p).startswith(str(root) + "/") or p == root for root in allowed_roots):
        abort(403)
    if not p.exists() or not p.is_file():
        abort(404)
    return send_file(p, as_attachment=True, download_name=p.name)


@app.route("/download-backtest-bundle")
def download_backtest_bundle():
    symbol = normalize_symbol_input(request.args.get("symbol", ""))
    if not symbol:
        abort(404)
    outdir = BACKTEST_OUT_DIR / symbol
    files = [
        outdir / f"backtest_report_{symbol}.txt",
        outdir / f"trades_{symbol}.csv",
        outdir / f"daily_details_{symbol}.csv",
    ]
    existing = [p for p in files if p.exists() and p.is_file()]
    if not existing:
        abort(404)
    bio = BytesIO()
    with ZipFile(bio, "w", ZIP_DEFLATED) as zf:
        for p in existing:
            zf.write(p, arcname=p.name)
    bio.seek(0)
    return send_file(bio, as_attachment=True, download_name=f"backtest_bundle_{symbol}.zip", mimetype="application/zip")

def _selected_key(config: Dict[str, Any], prefer_real_symbol: bool = False) -> str:
    options = symbol_options(config)
    allowed = {key for key, _ in options}
    requested = (request.args.get("symbol_key", "") or "").strip()
    if requested and requested in allowed:
        if prefer_real_symbol and requested == "COMMON_BACKTEST_CONFIG":
            real = first_real_symbol_key(config)
            if real:
                session["selected_symbol_key"] = real
                return real
        session["selected_symbol_key"] = requested
        return requested
    stored = str(session.get("selected_symbol_key", "")).strip()
    if stored in allowed and not (prefer_real_symbol and stored == "COMMON_BACKTEST_CONFIG"):
        return stored
    if prefer_real_symbol:
        real = first_real_symbol_key(config)
        if real:
            session["selected_symbol_key"] = real
            return real
    fallback = options[0][0] if options else "COMMON_BACKTEST_CONFIG"
    session["selected_symbol_key"] = fallback
    return fallback

def build_symbol_cards(config: Dict[str, Any], selected: str, include_common: bool = True) -> List[Dict[str, str]]:
    symbol_cfg = config.get("SYMBOL_CONFIG", {}) or {}
    cards = []
    if include_common:
        cards.append({"key": "COMMON_BACKTEST_CONFIG", "label": "通用回测参数", "symbol": "", "active": selected == "COMMON_BACKTEST_CONFIG"})
    for name, item in symbol_cfg.items():
        cards.append({"key": name, "label": name, "symbol": str(item.get("symbol", "")).strip(), "active": selected == name})
    return cards

def _base_context(config: Dict[str, Any], selected: str) -> Dict[str, Any]:
    state = read_state()
    section = get_section(config, selected)
    meta = get_meta_from_state(selected, state)
    grouped_fields = build_grouped_fields(section)
    bt_symbol_default = normalize_symbol_input(section.get("symbol", "")) if selected != "COMMON_BACKTEST_CONFIG" else ""
    common = config.get("COMMON_BACKTEST_CONFIG", {}) or {}
    # 回测页面的初始仓位是临时参数，只代表回测第一交易日 current_units；不读取/覆盖策略仓位参数。
    bt_initial_default = "5%"
    current_symbol = str(section.get("symbol", "")).strip()
    selected_snapshot_date = datetime.now().strftime("%Y-%m-%d")
    latest_snapshot, recent_snapshots = get_strategy_snapshots(selected, current_symbol, selected_snapshot_date)
    recent_trade_snapshots = get_recent_trade_snapshots(selected, current_symbol, 10)
    market_source_stats = build_market_source_stats(selected, current_symbol, selected_snapshot_date)
    trade_state_backups = get_trade_state_backups(selected, current_symbol, 10)
    return {
        "app_name": APP_DISPLAY_NAME,
        "selected": selected,
        "selected_label": "通用回测参数" if selected == "COMMON_BACKTEST_CONFIG" else selected,
        "selected_symbol_code": current_symbol,
        "section": section,
        "status_text": latest_status_for(selected, state),
        "grouped_fields": grouped_fields,
        "current_time": current_time_text(),
        "current_price": meta.get("current_price", ""),
        "last_time": meta.get("last_time", ""),
        "bt_symbol_default": bt_symbol_default,
        "bt_initial_default": bt_initial_default,
        "is_common": selected == "COMMON_BACKTEST_CONFIG",
        "nav_items": PAGE_TITLES,
        "param_help": PARAM_HELP,
        "backtest_help_text": BACKTEST_HELP_TEXT,
        "backtest_metrics_help_text": BACKTEST_METRICS_HELP_TEXT,
        "symbol_cards": build_symbol_cards(config, selected),
        "system_config": read_system_config(),
        "system_select_options": SYSTEM_SELECT_OPTIONS,
        "strategy_settings": read_strategy_settings(config),
        "snapshot_dates": [],
        "selected_snapshot_date": selected_snapshot_date,
        "latest_snapshot": latest_snapshot,
        "recent_snapshots": recent_snapshots,
        "recent_trade_snapshots": recent_trade_snapshots,
        "market_source_stats": market_source_stats,
        "trade_state_backups": trade_state_backups,
        "reference_prices": [],
        "source_metrics": [],
        "source_metrics_updated_at": "",
        "source_metrics_error": "",
        "fmt_snapshot_value": fmt_snapshot_value,
    }

def _save_all_params(config: Dict[str, Any], selected: str) -> None:
    section = get_section(config, selected).copy()
    for group in FIELD_GROUPS:
        for key, _, _ in group["items"]:
            if key in request.form:
                section[key] = convert_form_value(key, request.form.get(key, ""))

    # 价格监控使用 dashboard.html 中的独立框体，不加入通用 FIELD_GROUPS。
    if selected != "COMMON_BACKTEST_CONFIG":
        old_monitor_enabled = str(section.get("monitor_enabled", "off") or "off").strip().lower()
        if "monitor_enabled" in request.form:
            new_monitor_enabled = str(request.form.get("monitor_enabled", "off") or "off").strip().lower()
            if new_monitor_enabled not in {"on", "off"}:
                new_monitor_enabled = "off"
            section["monitor_enabled"] = new_monitor_enabled
            if new_monitor_enabled == "on" and old_monitor_enabled != "on":
                # 每次手动重新开启生成新批次，确保关闭期间的价格变化不会被补判为穿越。
                section["monitor_arm_id"] = secrets.token_hex(8)
        for monitor_key in ("monitor_price_1", "monitor_price_2"):
            if monitor_key in request.form:
                raw_monitor_price = str(request.form.get(monitor_key, "") or "").strip()
                if not raw_monitor_price:
                    section[monitor_key] = ""
                else:
                    try:
                        monitor_price = float(raw_monitor_price)
                    except (TypeError, ValueError):
                        monitor_price = 0.0
                    section[monitor_key] = monitor_price if monitor_price > 0 else ""
        section.setdefault("monitor_enabled", "off")
        section.setdefault("monitor_price_1", "")
        section.setdefault("monitor_price_2", "")
        section.setdefault("monitor_arm_id", "")

    # 移除已废弃字段
    section.pop("fee_rate", None)
    section.pop("slippage_bp", None)
    section.pop("pyramid_enabled", None)
    section.pop("k300", None)
    section.pop("ma300_min_coef", None)
    if section.get("box_grid_enabled") not in {"yes", "no"}:
        section["box_grid_enabled"] = "no"
    section["strategy_run"] = normalize_strategy_run_value(section.get("strategy_run", "on"), "on")
    if section.get("pyramid_add_enabled") not in {"yes", "auto"}:
        section["pyramid_add_enabled"] = "auto"
    # 兼容旧模块：旧字段仍写回，但新策略优先读取独立字段。
    # add_box_step 作为箱体固定加仓步长的旧别名；pyramid_steps/weights 作为离场倒金字塔旧别名。
    if "box_add_step" in section:
        section["add_box_step"] = section.get("box_add_step")
    if "clear_pyramid_steps" in section:
        section["pyramid_steps"] = section.get("clear_pyramid_steps")
    if "clear_pyramid_weights" in section:
        section["pyramid_weights"] = section.get("clear_pyramid_weights")
    set_section(config, selected, section)
    write_yaml(config)
    request_runtime_config_reload(selected, section)

def _manual_trade_format_units(value, mode):
    if mode == "percent":
        pct = safe_float(value, 0.0) * 100.0
        s = f"{pct:.2f}".rstrip("0").rstrip(".")
        if s in {"", "-0"}:
            s = "0"
        return f"{s}%"
    return f"{int(round(safe_float(value, 0.0))):,}股"

def _manual_trade_write_snapshot(selected, symbol, side, price, qty, units_after, cost_after, position_mode):
    try:
        SNAPSHOT_DIR.mkdir(parents=True, exist_ok=True)
        now = datetime.now()
        day = now.strftime("%Y-%m-%d")
        rec = {
            "time": now.strftime("%Y-%m-%d %H:%M:%S"),
            "date": day,
            "name": selected,
            "symbol": symbol,
            "level": "INFO",
            "action": "TRADE",
            "decision": "TRADE",
            "side": side,
            "reason": "手动交易",
            "manual_trade": True,
            "market_status": "ok",
            "market_source": "",
            "current_price": price,
            "trade_price": price,
            "trade_qty": qty,
            "current_units": units_after,
            "avg_cost": cost_after,
            "position_mode": position_mode,
            "zone": "MANUAL",
        }
        path = SNAPSHOT_DIR / f"{day}.jsonl"
        with path.open("a", encoding="utf-8") as f:
            f.write(json.dumps(rec, ensure_ascii=False, separators=(",", ":")) + "\n")
    except Exception as exc:
        logging.debug(f"记录手动交易快照失败: {exc}")

def _manual_trade_log_csv(selected, symbol, side, price, qty, avg_cost_after, units_after, position_mode):
    try:
        file_exists = TRADE_LOG_FILE.exists()
        with TRADE_LOG_FILE.open("a", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            if not file_exists:
                writer.writerow(["date", "quant_name", "symbol", "action", "price", "qty",
                                 "avg_cost_after", "zone", "reason", "raw_price", "restor_price",
                                 "ma150", "last_trade_price_before", "last_add_price_before",
                                 "dividend", "split_ratio"])
            writer.writerow([
                current_time_text(), selected, symbol, side,
                f"{safe_float(price, 0.0):.3f}", str(safe_float(qty, 0.0)),
                f"{safe_float(avg_cost_after, 0.0):.3f}", "MANUAL", "手动交易",
                "", "", "", "", "", "", "",
            ])
    except Exception as exc:
        logging.debug(f"记录手动交易日志失败: {exc}")

def handle_manual_trade(config: Dict[str, Any], selected: str) -> Tuple[bool, str]:
    """Execute a manual buy/sell outside the strategy and persist position/cost."""
    if selected == "COMMON_BACKTEST_CONFIG":
        return False, "通用回测参数不可手动交易。"
    side = (request.form.get("mt_side", "") or "").strip().lower()
    if side not in {"buy", "sell"}:
        return False, "无效的交易方向。"
    price = safe_float(request.form.get("mt_price", ""), 0.0)
    qty = parse_runtime_position_value(request.form.get("mt_qty", ""))
    if price <= 0:
        return False, "请填写有效的成交价格。"
    if qty <= 0:
        return False, "请填写有效的仓位数量。"

    section = get_section(config, selected)
    symbol = str(section.get("symbol", "") or "").strip().upper()
    position_mode = str(section.get("position_mode", "percent") or "percent").strip().lower()

    state = read_state()
    if not isinstance(state, dict):
        state = {}
    node = state.setdefault(selected, {})
    if not isinstance(node, dict):
        node = state[selected] = {}

    cur_units = parse_runtime_position_value(node.get("current_units", section.get("current_units", 0)))
    cur_cost = safe_float(node.get("avg_cost", section.get("current_avg_cost", 0)), 0.0)

    if side == "buy":
        new_units = cur_units + qty
        if new_units > 0:
            new_cost = (cur_units * cur_cost + qty * price) / new_units
        else:
            new_cost = price
        side_label = "BUY"
        action_label = "买入"
    else:
        new_units = max(cur_units - qty, 0.0)
        new_cost = cur_cost if new_units > 0 else 0.0
        side_label = "SELL"
        action_label = "卖出"

    node["current_units"] = new_units
    node["avg_cost"] = new_cost
    node["last_trade_price"] = price
    node["last_trade_side"] = "buy" if side == "buy" else "sell"
    node["last_trade_at"] = current_time_text()
    node["manual_trade_notice"] = (
        f"🖐️[MANUAL]【{selected}】 手动{action_label} {_manual_trade_format_units(qty, position_mode)} "
        f"@ {price:.3f}，当前持仓 {_manual_trade_format_units(new_units, position_mode)}，成本 {new_cost:.3f}"
    )
    write_state(state)

    section["current_units"] = _manual_trade_format_units(new_units, position_mode)
    section["current_avg_cost"] = round(new_cost, 6) if new_cost > 0 else 0.0
    set_section(config, selected, section)
    write_yaml(config)

    _manual_trade_log_csv(selected, symbol, side_label, price, qty, new_cost, new_units, position_mode)
    _manual_trade_write_snapshot(selected, symbol, side_label, price, qty, new_units, new_cost, position_mode)
    request_runtime_config_reload(selected, section)

    try:
        import threading
        threading.Thread(
            target=send_notification,
            args=(
                f"🖐️[MANUAL]【{selected}】 ({symbol})\n"
                f"🕒时间: {current_time_text()}\n"
                f"🗞交易: {action_label} {_manual_trade_format_units(qty, position_mode)} @ {price:.3f}\n"
                f"⚖️持仓: {_manual_trade_format_units(new_units, position_mode)}, 成本: {new_cost:.3f}",
            ),
            kwargs={"title": f"🖐️[MANUAL]【{selected}】手动{action_label}"},
            daemon=True,
        ).start()
    except Exception:
        pass

    return True, (
        f"手动{action_label}成功：{selected} ({symbol}) "
        f"{_manual_trade_format_units(qty, position_mode)} @ {price:.3f}，"
        f"当前持仓 {_manual_trade_format_units(new_units, position_mode)}，成本 {new_cost:.3f}"
    )

def _handle_symbol_actions(config: Dict[str, Any], selected: str):
    action = request.form.get("action", "")
    if action == "set_symbol":
        new_selected = (request.form.get("symbol_key", "") or "").strip()
        session["selected_symbol_key"] = new_selected or selected
        return redirect(url_for("status_page"))
    if action == "add_symbol":
        symbol_name = (request.form.get("new_name", "") or "").strip()
        symbol_code = normalize_symbol_input(request.form.get("new_symbol", ""))
        if not symbol_name or not symbol_code:
            flash("请填写标的名称和代码。", "error")
        else:
            symbol_cfg = config.setdefault("SYMBOL_CONFIG", {}) or {}
            if symbol_name in symbol_cfg:
                flash("该名称已存在，请换一个。", "error")
            else:
                config.setdefault("SYMBOL_CONFIG", {})[symbol_name] = build_new_symbol_section(config, symbol_code)
                write_yaml(config)
                flash(f"已新增标的：{symbol_name} ({symbol_code})", "success")
                return redirect(url_for("status_page", symbol_key=symbol_name))
    elif action == "delete_symbol":
        if selected == "COMMON_BACKTEST_CONFIG":
            flash("通用回测参数不可删除。", "error")
        else:
            symbol_cfg = config.get("SYMBOL_CONFIG", {}) or {}
            if selected in symbol_cfg:
                symbol_code = str((symbol_cfg.get(selected) or {}).get("symbol", "")).strip().upper()
                del symbol_cfg[selected]
                write_yaml(config)
                delete_symbol_state(selected, symbol_code)
                cleanup_stats = cleanup_deleted_symbol_runtime_files(selected, symbol_code)
                request_runtime_config_reload(selected, None)
                request_runtime_system_config_reload()
                flash(
                    f"已删除标的：{selected}，并清理运行状态、回滚点 {cleanup_stats.get('state_backups', 0)} 条、快照记录 {cleanup_stats.get('snapshots', 0)} 条、交易记录 {cleanup_stats.get('trade_log', 0)} 条、策略缓存 {cleanup_stats.get('strategy_cache', 0)} 条、回测数据 {cleanup_stats.get('backtest_out', 0)} 项。",
                    "success",
                )
                return redirect(url_for("status_page"))
            flash("未找到要删除的标的。", "error")
    return None

@app.route("/")
def home_redirect():
    return redirect(url_for("status_page", symbol_key=request.args.get("symbol_key", "")))

@app.route("/symbols", methods=["GET", "POST"])
def symbols_page():
    config = read_yaml()
    selected = _selected_key(config, prefer_real_symbol=True)
    if request.method == "POST":
        redirect_resp = _handle_symbol_actions(config, selected)
        if redirect_resp is not None:
            return redirect_resp
    return redirect(url_for("status_page"))

@app.route("/status", methods=["GET"])
def status_page():
    config = read_yaml()
    selected = _selected_key(config, prefer_real_symbol=True)
    ctx = _base_context(config, selected)
    ctx["symbol_cards"] = build_symbol_cards(config, selected, include_common=False)
    if selected != "COMMON_BACKTEST_CONFIG":
        section = get_section(config, selected)
        if web_in_trade_session(config):
            request_auto_refresh_if_stale(selected, section, max_age_seconds=60)
        else:
            ctx["status_session_notice"] = f"当前不在交易时段 {trade_session_text(config)} 内，状态页只展示最近一次状态，不自动刷新行情。"
        ctx["reference_prices"] = get_reference_prices_for_status(selected, section)
        metrics, metrics_updated_at, metrics_error = get_source_metrics_for_status(selected, section)
        if not metrics:
            metrics = build_source_metric_placeholders(section)
        ctx["source_metrics"] = _metric_display_cards(metrics)
        ctx["source_metrics_updated_at"] = metrics_updated_at
        ctx["source_metrics_error"] = metrics_error
        if metrics_error:
            metric_level = "ERROR" if any(isinstance(x, dict) and str(x.get("level", "")).upper() == "ERROR" for x in metrics) else "WARN"
            prefix = "🔴[ERROR]" if metric_level == "ERROR" else "🟡[WARN]"
            alert_line = f"{prefix} 回测/策略数据源指标: {metrics_error}"
            status_text = _status_text_with_badge(str(ctx.get("status_text", "") or ""), metric_level)
            if alert_line not in status_text:
                ctx["status_text"] = (status_text.rstrip() + "\n" + alert_line).strip()
            else:
                ctx["status_text"] = status_text
    ctx.update({"page_name": "status"})
    return render_template("dashboard.html", **ctx)


@app.route("/refresh-status", methods=["POST"])
def refresh_status_page():
    config = read_yaml()
    selected = (request.form.get("symbol_key", "") or "").strip()
    allowed = {key for key, _ in symbol_options(config)}
    if selected not in allowed or selected == "COMMON_BACKTEST_CONFIG":
        selected = _selected_key(config)
    section = get_section(config, selected)
    symbol_code = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
    refs, ref_error = refresh_reference_prices_now(selected, section)
    label = selected if selected != "COMMON_BACKTEST_CONFIG" else "当前标的"
    ref_msg = f"3 个实时行情源已更新 {sum(1 for x in refs if isinstance(x, dict) and x.get('ok'))}/{len(refs) or 3}" if refs else f"3 源参考价刷新失败：{ref_error or '暂无返回'}"
    flash(f"已刷新 {label} ({symbol_code}) 的实时参考价；{ref_msg}。状态正文保持最后一帧，不触发交易。", "success")
    return redirect(url_for("status_page", symbol_key=selected))



@app.route("/refresh-reference-price", methods=["POST"])
def refresh_reference_price_page():
    config = read_yaml()
    selected = (request.form.get("symbol_key", "") or "").strip()
    source_key = (request.form.get("source_key", "") or "").strip()
    allowed = {key for key, _ in symbol_options(config)}
    if selected not in allowed or selected == "COMMON_BACKTEST_CONFIG":
        selected = _selected_key(config, prefer_real_symbol=True)
    section = get_section(config, selected)
    symbol_code = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
    ref, err = refresh_reference_price_source_now(selected, section, source_key)
    label = (ref or {}).get("label") or source_key or "实时源"
    if ref and ref.get("ok"):
        flash(f"已刷新 {selected} ({symbol_code}) 的 {label}: {fmt_snapshot_value(ref.get('price'))}。状态正文保持最后一帧。", "success")
    else:
        flash(f"刷新 {selected} ({symbol_code}) 的 {label} 失败：{err or (ref or {}).get('error') or '未知错误'}", "error")
    return redirect(url_for("status_page", symbol_key=selected))


@app.route("/refresh-source-metrics", methods=["POST"])
def refresh_source_metrics_page():
    config = read_yaml()
    selected = (request.form.get("symbol_key", "") or "").strip()
    source_key = (request.form.get("source_key", "") or "").strip()
    allowed = {key for key, _ in symbol_options(config)}
    if selected not in allowed or selected == "COMMON_BACKTEST_CONFIG":
        selected = _selected_key(config)
    section = get_section(config, selected)
    symbol_code = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
    if not web_in_trade_session(config):
        now_text = web_strategy_now(config).strftime("%Y-%m-%d %H:%M:%S")
        flash(f"当前不在交易时段 {trade_session_text(config)} 内，已跳过回测/策略数据源指标刷新。当前策略时间：{now_text}。", "warning")
        return redirect(url_for("status_page", symbol_key=selected))
    try:
        if source_key:
            calculate_and_store_source_metric(selected, section, source_key)
            request_source_metrics_refresh_symbol(selected, symbol_code)
            flash(f"已刷新 {selected} ({symbol_code}) 的 {source_key} 指标。", "success")
        else:
            calculate_and_store_source_metrics(selected, section)
            request_source_metrics_refresh_symbol(selected, symbol_code)
            flash(f"已刷新 {selected} ({symbol_code}) 的当前回测/策略数据源指标。", "success")
    except Exception as e:
        flash(f"刷新回测/策略数据源指标失败：{e}", "error")
    return redirect(url_for("status_page", symbol_key=selected))


@app.route("/clear-market-state", methods=["POST"])
def clear_market_state_page():
    config = read_yaml()
    selected = (request.form.get("symbol_key", "") or "").strip()
    allowed = {key for key, _ in symbol_options(config)}
    if selected not in allowed or selected == "COMMON_BACKTEST_CONFIG":
        selected = _selected_key(config)
    section = get_section(config, selected)
    symbol_code = normalize_symbol_input(str((section or {}).get("symbol", "") or ""))
    clear_seq = request_clear_market_state(selected, symbol_code)
    label = selected if selected != "COMMON_BACKTEST_CONFIG" else "当前标的"
    flash(f"已请求重置 {label} ({symbol_code}) 的运行状态（last_price/last_trade_price/last_add_price/步进等恢复初始），仅影响当前标的。", "success")
    return redirect(url_for("status_page", symbol_key=selected))

@app.route("/restore-trade-state", methods=["POST"])
def restore_trade_state_page():
    config = read_yaml()
    selected = (request.form.get("symbol_key", "") or "").strip()
    allowed = {key for key, _ in symbol_options(config)}
    if selected not in allowed:
        selected = _selected_key(config)
    backup_id = (request.form.get("backup_id", "") or "").strip()
    try:
        detail = restore_trade_state_backup(backup_id, selected)
        flash(detail, "success")
    except Exception as e:
        flash(f"回滚失败：{e}", "error")
    return redirect(url_for("status_page", symbol_key=selected))

@app.route("/params", methods=["GET", "POST"])
def params_page():
    config = read_yaml()
    selected = _selected_key(config)
    if request.method == "POST":
        action = request.form.get("action", "")
        if action == "save_params":
            _save_all_params(config, selected)
            flash("参数已保存到 quant.yaml", "success")
        elif action == "manual_trade":
            ok, detail = handle_manual_trade(config, selected)
            flash(detail, "success" if ok else "error")
    return redirect(url_for("status_page"))

@app.route("/api/backtest-chart/<symbol>")
def api_backtest_chart(symbol):
    symbol = normalize_symbol_input(symbol)
    if not symbol:
        return jsonify({"error": "Invalid symbol"}), 400
    outdir = BACKTEST_OUT_DIR / symbol
    daily_details_path = outdir / f"daily_details_{symbol}.csv"
    trades_path = outdir / f"trades_{symbol}.csv"

    if not daily_details_path.exists():
        return jsonify({"error": f"No backtest data found at {daily_details_path}"}), 404

    try:
        daily_data = []
        with open(daily_details_path, "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            if not reader:
                return jsonify({"error": "CSV has no headers"}), 400
            for row in reader:
                try:
                    price = float(row.get("raw_price", 0) or 0)
                    ma150_str = row.get("ma150", "")
                    ma150 = float(ma150_str) if ma150_str and ma150_str.strip() else None

                    trend_upper_str = row.get("trend_upper", "")
                    trend_upper = float(trend_upper_str) if trend_upper_str and trend_upper_str.strip() else None

                    daily_data.append({
                        "date": row.get("date", ""),
                        "price": price,
                        "ma150": ma150,
                        "trend_upper": trend_upper,
                        "zone": row.get("zone", ""),
                        "holding": row.get("holding", "0"),
                    })
                except Exception as e:
                    logging.error(f"Error parsing row: {row}, {e}")
                    continue

        trades = []
        if trades_path.exists():
            with open(trades_path, "r", encoding="utf-8") as f:
                reader = csv.DictReader(f)
                for row in reader:
                    try:
                        trades.append({
                            "date": row.get("date", ""),
                            "action": row.get("action", ""),
                            "price": float(row.get("raw_price", 0) or 0),
                        })
                    except Exception as e:
                        logging.error(f"Error parsing trade: {row}, {e}")
                        continue

        return jsonify({"data": daily_data, "trades": trades})
    except Exception as e:
        logging.error(f"api_backtest_chart error: {e}")
        return jsonify({"error": f"Error: {str(e)}"}), 500


@app.route("/backtest", methods=["GET", "POST"])
def backtest_page():
    config = read_yaml()
    selected = _selected_key(config)
    backtest_output = ""
    backtest_cards = []
    backtest_files = {}
    chart_symbol = ""
    if request.method == "POST" and request.form.get("action") == "run_backtest":
        bt_symbol = normalize_symbol_input(request.form.get("bt_symbol", "") or _base_context(config, selected)["bt_symbol_default"])
        bt_initial = (request.form.get("bt_initial_units", "") or "").strip()
        bt_days = int(request.form.get("bt_days", "800") or "800")
        if not bt_symbol:
            flash("请填写回测代码。", "error")
        else:
            result = run_backtest(bt_symbol, bt_days, bt_initial)
            backtest_output = result.get("output", "")
            backtest_cards = result.get("summary_cards", [])
            backtest_files = result.get("files", {})
            chart_symbol = bt_symbol
            flash("回测执行完成。", "success")
    ctx = _base_context(config, selected)
    ctx.update({"page_name": "backtest", "backtest_output": backtest_output, "backtest_cards": backtest_cards, "backtest_files": backtest_files, "chart_symbol": chart_symbol})
    return render_template("dashboard.html", **ctx)




def _token_api_response(payload, status=200):
    resp = jsonify(payload)
    resp.status_code = status
    resp.headers["Access-Control-Allow-Origin"] = "*"
    resp.headers["Access-Control-Allow-Headers"] = "Content-Type, X-DCF-TokenAPI-Key, X-API-Key, Authorization"
    resp.headers["Access-Control-Allow-Methods"] = "POST, OPTIONS"
    return resp

def _get_tokenapi_key_from_request() -> str:
    value = (
        request.headers.get("X-DCF-TokenAPI-Key")
        or request.headers.get("X-API-Key")
        or request.args.get("key")
        or request.args.get("api_key")
        or ""
    )
    if not value and request.is_json:
        try:
            value = (request.get_json(silent=True) or {}).get("api_key", "")
        except Exception:
            value = ""
    if not value:
        auth = request.headers.get("Authorization", "")
        if auth.lower().startswith("bearer "):
            value = auth.split(None, 1)[1]
    return str(value or "").strip()

def _extract_xueqiu_token_from_cookie(text: str) -> str:
    m = re.search(r"(?:^|;\s*)xq_a_token=([^;\s]+)", str(text or ""))
    return m.group(1).strip() if m else ""

def _mask_token(token: str) -> str:
    token = str(token or "").strip()
    if not token:
        return ""
    if len(token) <= 8:
        return token
    return token[:4] + "*" * (len(token) - 8) + token[-4:]

@app.route("/tokenapi", methods=["POST", "OPTIONS"])
def tokenapi_update_xueqiu_cookie():
    if request.method == "OPTIONS":
        return _token_api_response({"ok": True})
    data = request.get_json(silent=True) if request.is_json else {}
    if not isinstance(data, dict):
        data = {}
    cookie = str(data.get("cookie") or data.get("cookieHeader") or data.get("cookie_header") or "").strip()
    token = str(data.get("token") or "").strip()
    if not token and cookie:
        token = _extract_xueqiu_token_from_cookie(cookie)
    if token:
        saved_value = token
        mode = "token"
    elif cookie:
        saved_value = cookie
        mode = "cookie"
    else:
        return _token_api_response({"ok": False, "message": "缺少 token 或 cookie"}, 400)
    cfg = read_system_config()
    old_value = cfg.get("XUEQIU_TOKEN", "")
    changed = old_value != saved_value
    cfg["XUEQIU_TOKEN"] = saved_value
    cfg["XUEQIU_TOKEN_UPDATED_AT"] = current_time_text()
    source = str(data.get("source") or "browser_extension").strip()[:80]
    cfg["XUEQIU_TOKEN_SOURCE"] = source
    write_system_config(cfg)
    return _token_api_response({
        "ok": True,
        "changed": changed,
        "mode": mode,
        "token_present": bool(token),
        "cookie_present": bool(cookie),
        "updated_at": cfg["XUEQIU_TOKEN_UPDATED_AT"],
        "source": source,
        "message": "雪球 Token/Cookie 已更新" if changed else "雪球 Token/Cookie 未变化，已刷新更新时间",
    })

@app.route("/push", methods=["GET", "POST"])
def push_page():
    cfg = read_push_config()
    if request.method == "POST":
        action = request.form.get("action", "")
        if action == "save_system":
            save_system_config_from_form()
            flash("行情源设置已保存，并通知主程序即时生效。", "success")
            return redirect(url_for("push_page"))
        if action == "save_strategy":
            config = read_yaml()
            save_strategy_settings_from_form(config)
            flash("系统运行设置已保存到 quant.yaml，主程序将即时读取生效。", "success")
            return redirect(url_for("push_page"))
        if action == "save_push":
            cfg = save_push_config_from_form()
            flash("推送配置已保存到 /root/quant/push.conf", "success")
            return redirect(url_for("push_page"))
        if action == "test_push":
            ok, detail = send_push_test(cfg)
            flash(detail, "success" if ok else "error")
            return redirect(url_for("push_page"))
        if action == "clear_push_log":
            try:
                PUSH_LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
                PUSH_LOG_FILE.write_text("", encoding="utf-8")
                if PUSH_DETAIL_LOG_FILE.exists():
                    PUSH_DETAIL_LOG_FILE.write_text("", encoding="utf-8")
                flash("推送日志已清空。", "success")
            except Exception as e:
                flash(f"清空推送日志失败: {e}", "error")
            return redirect(url_for("push_page"))
    config = read_yaml()
    selected = _selected_key(config)
    ctx = _base_context(config, selected)
    system_cfg = read_system_config()
    ctx.update({
        "page_name": "push",
        "system_config_path": str(SYSTEM_CONFIG_FILE),
        "system_config": system_cfg,
        "system_config_masked_token": _mask_token(system_cfg.get("XUEQIU_TOKEN", "")),
        "system_config_token_updated_at": system_cfg.get("XUEQIU_TOKEN_UPDATED_AT", ""),
        "system_config_token_source": system_cfg.get("XUEQIU_TOKEN_SOURCE", ""),
        "system_select_options": SYSTEM_SELECT_OPTIONS,
        "push_config_path": str(PUSH_CONFIG_FILE),
        "push_log_path": str(PUSH_LOG_FILE),
        "push_config": cfg,
        "push_fields": PUSH_FIELDS,
        "push_select_options": PUSH_SELECT_OPTIONS,
        "push_logs": read_push_logs(PUSH_LOG_KEEP_LINES),
        "push_log_entries": build_push_log_entries(read_push_logs(PUSH_LOG_KEEP_LINES)),
        "strategy_fields": STRATEGY_FIELDS,
        "strategy_settings": read_strategy_settings(config),
    })
    return render_template("dashboard.html", **ctx)

if __name__ == "__main__":
    cfg = load_web_config()
    app.run(host="127.0.0.1", port=int(cfg.get("internal_port", 2096)), debug=False)
