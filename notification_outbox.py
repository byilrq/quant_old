"""Durable at-least-once delivery. Sending never changes position or step state.

An acknowledgement lost after a successful send can cause a duplicate message;
all retries carry the same event id and original price/time.
"""
from __future__ import annotations
import logging
import time
from runtime_store import get_store
from strategy_config import enabled


def drain_outbox(root, sender, limit=5, now=None):
    store = get_store(root)
    delivered = 0
    # Claim one at a time, so slow providers cannot outlive the lease of a batch.
    for _ in range(limit):
        if enabled(store.read_config().get("STRATEGY", {}).get("notifications_paused"), False):
            break
        records = store.claim_messages(now=now, limit=1)
        if not records:
            break
        item = records[0]
        message = item["message"]
        body = str(message["body"]).strip()
        if item["attempts"]:
            body += f"\n\U0001f501\u8865\u9001\u7b2c {item['attempts']} \u6b21\uff1b\u4ee5\u539f\u4fe1\u53f7\u65f6\u95f4\u4e3a\u51c6\uff0c\u4e0d\u91cd\u590d\u8bb0\u8d26\u3002"
        error = ""
        try:
            ok = bool(sender(body, title=message.get("title") or "Quant"))
            if not ok:
                error = "notification provider returned false"
        except Exception as exc:
            ok, error = False, str(exc)
            logging.exception("Outbox delivery failed: %s", item["id"])
        store.finish_message(item["id"], item["token"], ok, error, now=now)
        delivered += int(ok)
    return delivered
