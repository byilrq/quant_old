"""Application service: prepare pure decisions and atomically commit a frame.

Pricing/fetching remains in quant.py. Message formatting remains in push.py or
its existing quant formatters. Store and strategy do not call each other.
"""
from __future__ import annotations
from copy import deepcopy
from datetime import datetime
import logging
import uuid
from strategy import evaluate_frame, apply_trade
from strategy_config import Parameters, number, units_text
from strategy_view import describe_no_trade, zone_details
from runtime_store import get_store, StateConflict


def commit_market_frame(root, name, cfg, before, observed, price, ma, at, *,
                        allow_trade=True, allow_monitor=True, record_snapshot=True,
                        strategy_used=None, source_digest=None,
                        formatter=None, status_formatter=None, context=None):
    store = get_store(root)
    result = evaluate_frame(observed, cfg, price, ma, allow_trade=allow_trade, observed_at=at)
    after = result["state"]
    after["ma_short"] = ma
    context = dict(context or {})
    p = Parameters.from_config(cfg)
    events, messages = [], []
    for trade in result["trades"]:
        identity = uuid.uuid4().hex
        formatted = formatter(trade, before, after, result) if formatter else f"{name} {trade['side']} {trade['qty']} @ {trade['price']}"
        lines = str(formatted).splitlines()
        if lines and lines[0].startswith("🎯[TRADE]【"):
            title = lines[0]
            body = "\n".join(lines[1:]).strip()
        else:
            title = f"🎯[TRADE]【{name}】 ({cfg.get('symbol', '')})"
            body = str(formatted).strip()
        event = dict(id=identity, kind="trade", time=at, name=name, symbol=cfg.get("symbol", ""),
                     position_mode=p.mode, trade=trade, body=body, title=title)
        events.append(event)
        messages.append(formatted)
        after["last_signal_id"] = identity
    # Price monitoring reserves an event but does not mutate economic fields.
    if allow_monitor:
        from monitor import plan_price_monitor
        after, monitor_event = plan_price_monitor(name, cfg, after, price, at, context)
        if monitor_event:
            events.append(monitor_event)
    reason = ("; ".join(f"{t['side']} {units_text(t['qty'],p.mode)} @ {t['price']:.3f}" for t in result["trades"])
              if result["trades"] else describe_no_trade(after, cfg, price, ma, result["zone"], result["trade_allowed"]))
    if cfg.get("box_grid_enabled") in (True, "yes", "on"):
        # Legacy code never had an order branch; do not silently enable new trades.
        after["grid_notice"] = "\u65e7BOX\u7f51\u683c\u4ec5\u6709\u5c55\u793a\uff0c\u672c\u6b21\u4e0d\u81ea\u52a8\u542f\u7528\u65b0\u4ea4\u6613\u89c4\u5219"
    result["state"] = after
    if status_formatter:
        after["last_status_msg"] = status_formatter(after, result)
    after["status_updated_at"] = at
    after["last_decision_reason"] = reason
    after["next_add_price"] = result["add"].get("next_price")
    after["next_clear_price"] = result["clear"].get("next_price")
    snapshot = dict(context, time=at, name=name, symbol=cfg.get("symbol", ""),
                    zone=result["zone"], current_price=price, ma150=ma,
                    action="TRADE" if result["trades"] else ("NO_TRADE" if result["trade_allowed"] else "MONITOR_ONLY"),
                    decision="TRADE" if result["trades"] else ("NO_TRADE" if result["trade_allowed"] else "MONITOR_ONLY"),
                    reason=reason, trade_count=len(result["trades"]), trade_allowed=result["trade_allowed"],
                    current_units_before=before.get("current_units"), current_units_after=after.get("current_units"),
                    avg_cost_before=before.get("avg_cost"), avg_cost_after=after.get("avg_cost"),
                    base_units=p.base, target_units=p.target, limit_units=p.limit,
                    sell_price=ma*p.trend_multiple, clear_price=ma*p.clear_multiple,
                    last_trade_price=after.get("last_trade_price"), last_trade_side=after.get("last_trade_side"),
                    last_add_price=after.get("last_add_price"), pyramid_step=after.get("pyramid_step",0),
                    pyramid_add_active=after.get("pyramid_add_active",False), clear_step=after.get("clear_step",0),
                    next_add_price=after["next_add_price"], next_clear_price=after["next_clear_price"],
                    add_cycle_review=after.get("add_review_required", ""), clear_cycle_review=after.get("clear_review_required", ""))
    # A real market observation is snapshot-worthy even when trading is paused.
    # record_snapshot is false only for Web/reference refreshes, never because
    # allow_trade is false.
    committed_snapshot = snapshot if record_snapshot else None
    store.commit_frame(name, before, after, cfg, events,
                       snapshot=committed_snapshot,
                       strategy_used=strategy_used, source_digest=source_digest)
    return result, snapshot, messages


def manual_trade(root, name, side, price, qty, operation_id, at):
    """Record an actual manually entered fill, never a broker order.

    The event id makes HTTP form retries idempotent. A manual buy changes its
    price anchor, but does not start a low-buy cycle or consume a pyramid step.
    """
    store = get_store(root)
    side = str(side).upper()
    price, qty = number(price), number(qty)
    if side not in {"BUY", "SELL"} or price <= 0 or qty <= 0:
        raise ValueError("invalid manual side/price/quantity")
    import re
    if not re.fullmatch(r"[A-Za-z0-9_-]{8,96}", str(operation_id)):
        raise ValueError("invalid manual request id")
    identity = "manual_" + str(operation_id)
    with store.transaction():
        existing = store.event(identity)
        if existing:
            old = existing.get("trade", {})
            if existing.get("name") != name or any(old.get(k) != v for k, v in {"side": side, "price": price, "qty": qty}.items()):
                raise StateConflict("request id was already used for a different manual fill")
            return store.read_state().get(name, {}), True
        config, state = store.read_config(), store.read_state()
        cfg = config.get("SYMBOL_CONFIG", {}).get(name)
        if not cfg:
            raise ValueError("unknown symbol")
        p = Parameters.from_config(cfg)
        before = deepcopy(state.get(name, {}))
        if side == "SELL" and qty > number(before.get("current_units")) + 1e-9:
            raise ValueError("manual sale exceeds the recorded position; correct quantity first")
        after = apply_trade(before, side, qty, price)
        if p.mode == "percent" and after["current_units"] > 1 + 1e-9:
            raise ValueError("manual position exceeds 100%")
        after.update(last_trade_at=at, manual_trade_at=at)
        if side == "BUY":
            after["last_add_price"] = price
        body = (f"\U0001f590[MANUAL]\u3010{name}\u3011 ({cfg.get('symbol','')})\n"
                f"\U0001f552\u65f6\u95f4: {at}\n\U0001f5de\u4ea4\u6613: {side} {units_text(qty,p.mode)} @ {price:.3f}\n"
                f"\u2696\ufe0f\u6301\u4ed3: {units_text(after['current_units'],p.mode)}, \u6210\u672c: {after['avg_cost']:.3f}")
        after["manual_trade_notice"] = body
        after["last_status_msg"] = body
        after["last_signal_id"] = identity
        trade = dict(side=side, qty=qty, price=price, zone="MANUAL", reason="MANUAL_TRADE",
                     pos_before=before.get("current_units",0), pos_after=after["current_units"],
                     avg_cost_before=before.get("avg_cost",0), avg_cost_after=after["avg_cost"])
        event = dict(id=identity, kind="manual", trade=trade, time=at, name=name, symbol=cfg.get("symbol",""),
                     position_mode=p.mode, body=body, title=f"[MANUAL] {name} {side}")
        snapshot = dict(time=at, name=name, symbol=cfg.get("symbol",""),action="TRADE",decision="TRADE",
                        reason="\u624b\u52a8\u4ea4\u6613", manual_trade=True, zone="MANUAL", current_price=price,
                        current_units_after=after["current_units"],avg_cost_after=after["avg_cost"],trade_qty=qty)
        store.commit_frame(name, before, after, cfg, [event], snapshot)
        return after, False


def state_form_token(node):
    import hashlib
    from runtime_store import json_text
    # Exclude quote timestamps: background price refreshes must not invalidate a form.
    keys = ("current_units", "avg_cost", "last_trade_price", "last_trade_side", "last_add_price",
            "pyramid_step", "pyramid_add_active", "pyramid_anchor_price", "pyramid_plan",
            "clear_step", "clear_active", "clear_anchor_price", "clear_plan", "restore_generation")
    return hashlib.sha256(json_text({k: node.get(k) for k in keys}).encode()).hexdigest()


def config_form_token(section):
    import hashlib
    from runtime_store import json_text
    return hashlib.sha256(json_text(section).encode()).hexdigest()
