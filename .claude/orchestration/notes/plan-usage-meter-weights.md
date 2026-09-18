---
name: plan-usage-meter-weights
description: Fitted on the owner's own limit windows — the plan meter behaves like API weights (cache reads ~0.1, 1h writes ~2, output 5) and Fable counts about 3x Opus
metadata:
  type: project
---

Fitted 2026-09-18 on ten recorded five-hour limit windows of this account (eight on the owner's earlier plan, one exhausted window and one 52% reading on the current plan, which the owner says has five times the earlier capacity): the usage meter is reproduced within about ±15% by API-style weights — cache reads 0.10, one-hour cache writes 2.0, output 5, per input token — with Fable weighted about 3× Opus. "Cache reads are free" fits badly (old windows disagree by ±33% and it predicts 19% where the owner read 52%). Capacity of the current plan comes out near 77M Opus-input-equivalents per five-hour window; one Opus implementer session at ~500K average context uses about 11M per hour (~14%).

**Why:** the owner doubted a usage explanation built on assumed weights; the fit replaced the assumption with the account's own history. The owner's impression that a warm cache yields more dollar value per plan percent was not confirmed by this fit, but the dollar figure the owner compares against was not examined.

**How to apply:** cost any multi-session design as Σ over sessions of (model weight × context carried per request × requests per hour); a Fable session with a large context is the most expensive thing to keep turning — on 2026-09-18 kb plus the Fable maintenance session were about 44% of plan usage while being a fifth of the tokens. See [[fable-knowledge-base-orchestrator]].
