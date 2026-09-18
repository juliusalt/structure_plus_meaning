#!/usr/bin/env python3
"""Context gauge and turn control for the orchestrated sessions (hook script).

Modes (argv[1]):
  gauge     PostToolUse in the implementer: measure the context; deliver the
            soft notice once; raise the rotate flag at the hard threshold.
  tripwire  PreCompact(auto): raise a flag (argv[2], default rotate; base-overflow while a base loads) and block
            the compaction.
  stop      Stop in the implementer: keep it working unless rotation is due
            or it declared itself waiting.
  measure   No hook input; print the context of the transcript in argv[2].

The context is read from the transcript: input + cache read + cache write of
the latest main-chain request, which is what compaction itself records.

State lives beside this script in state/ (ORCH_STATE_DIR overrides):
  soft     the soft notice was delivered
  rotate   rotation is due
  waiting  the implementer is legitimately idle (consumed by one stop)
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
STATE = os.environ.get("ORCH_STATE_DIR") or os.path.join(HERE, "state")
# The target is the whole window. The soft notice leaves only what closing a batch and writing the handoff
# costs; the hard flag is a backstop just under the window, and the compaction tripwire is the real end.
WINDOW = int(os.environ.get("ORCH_WINDOW", 1_000_000))
SOFT = int(os.environ.get("ORCH_SOFT", WINDOW - 60_000))
HARD = int(os.environ.get("ORCH_HARD", WINDOW - 10_000))


def context_tokens(transcript):
    """Context of the latest main-chain request, read from the file's tail."""
    try:
        size = os.path.getsize(transcript)
    except OSError:
        return 0
    span = 400_000
    while True:
        with open(transcript, "rb") as f:
            f.seek(max(0, size - span))
            lines = f.read().decode(errors="ignore").splitlines()
        for line in reversed(lines):
            if '"usage"' not in line:
                continue
            try:
                d = json.loads(line)
            except ValueError:
                continue
            if d.get("type") != "assistant" or d.get("isSidechain"):
                continue
            u = (d.get("message") or {}).get("usage") or {}
            total = (
                (u.get("input_tokens") or 0)
                + (u.get("cache_read_input_tokens") or 0)
                + (u.get("cache_creation_input_tokens") or 0)
            )
            if total:
                return total
        if span >= size or span >= 16_000_000:
            return 0
        span *= 4


def flag(name):
    return os.path.join(STATE, name)


def raise_flag(name, hook, tokens, why):
    os.makedirs(STATE, exist_ok=True)
    if os.path.exists(flag(name)):
        return
    with open(flag(name), "w") as f:
        f.write(f"{hook.get('session_id', '')} {tokens} {why} {time.strftime('%Y-%m-%dT%H:%M:%S')}\n")


def add_context(event, text):
    print(json.dumps({"hookSpecificOutput": {"hookEventName": event, "additionalContext": text}}))


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "gauge"
    if mode == "measure":
        print(context_tokens(sys.argv[2]))
        return 0
    hook = json.load(sys.stdin)
    event = hook.get("hook_event_name", "PostToolUse")
    if hook.get("agent_id"):  # a subagent's tool call says nothing about the main context
        return 0

    if mode == "tripwire":  # argv[2] names the flag to raise: rotate (implementer), base-overflow (a loading base)
        raise_flag(sys.argv[2] if len(sys.argv) > 2 else "rotate", hook,
                   context_tokens(hook.get("transcript_path", "")), "precompact")
        sys.stderr.write("Compaction is not allowed in an orchestrated session: it is replaced instead.\n")
        return 2

    if mode == "stop":
        if os.path.exists(flag("rotate")):
            return 0
        if os.path.exists(flag("waiting")):
            os.rename(flag("waiting"), flag("waiting-declared"))  # the watchdog leaves a declared wait alone
            return 0
        print(json.dumps({
            "decision": "block",
            "reason": (
                "The standing goal is not reached, so the turn does not end here. Continue with the next batch "
                "from HANDOFF.md: batch the problems, the read requests, and the edits with their checks; keep "
                "more than one problem moving while commands run in the background; criticize each batch in the "
                "library's own ideas before exercising it. If you are blocked on the owner and no other work "
                "remains, record the question in owner-ledger.md, run "
                "`.claude/orchestration/impl_state.sh waiting`, and then end the turn."
            ),
        }))
        return 0

    used = context_tokens(hook.get("transcript_path", ""))
    # Bookkeeping for the keep-warm daemon. `.used`: this role is active. `.hit`: the base's cache entry was
    # just refreshed — measured 2026-09-18: every request of a working fork keeps its base's prefix alive.
    role = "impl"
    if os.path.exists(flag("waiting-declared")):
        os.remove(flag("waiting-declared"))  # it is working again
    try:
        os.utime(flag(f"{role}-base.used"))
        if open(flag(f"{role}-mode")).read().strip() == "fork":  # only a fork that read the base shares its entry
            os.utime(flag(f"{role}-base.hit"))
    except OSError:
        pass
    if os.environ.get("ORCH_DEBUG"):
        os.makedirs(STATE, exist_ok=True)
        with open(flag("gauge.log"), "a") as f:
            f.write(f"{time.strftime('%H:%M:%S')} {mode} used={used} soft={SOFT} hard={HARD} tool={hook.get('tool_name')}\n")

    if used >= HARD:
        raise_flag("rotate", hook, used, "hard-threshold")
    if used >= SOFT and not os.path.exists(flag("soft")):
        raise_flag("soft", hook, used, "soft-threshold")
        add_context(event, (
            f"Context is at {used // 1000}K tokens; this session will be replaced before it compacts. Start no "
            "new batch. Close or park the current one, then bring HANDOFF.md current: every open problem and its "
            "state, running jobs with their output paths, uncommitted edits, and the next batch. Then run "
            "`.claude/orchestration/impl_state.sh ready` (a script starts your successor) and "
            f"end the turn. The window is {WINDOW // 1000}K: at {HARD // 1000}K, or when compaction would start, the "
            "session is stopped whether or not this is done, so do this now and keep it short."
        ))
    return 0


if __name__ == "__main__":
    sys.exit(main())
