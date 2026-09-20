#!/usr/bin/env python3
"""Context gauge, mail and turn control for every role (hook script).

Modes (argv[1]):
  gauge     PostToolUse: deliver the session's mail; near the end of the window, tell the session to end its piece of
            work (ENDS: a producing session records its result, partial if need be; the planner its plan; the task
            designer its briefs; the reviewer its verdict; a consultation its answer); record what the session reads
            and produces (work_meter.py); refresh the warmth marks of the session and of what it forked.
  stop      Stop: mail waiting for the session is delivered by continuing the turn; the knowledge base may always end
            its turn; any other session once its piece of work has ended, while it waits on its escalation, or while
            a question of its own is unanswered.
  owner     UserPromptSubmit: what the owner types to the session is recorded verbatim and dated in the owner ledger,
            and (but in a planning episode) is an event for the next planning episode (v2.owner_said)
  tripwire  PreCompact(auto): mark the session at its end (argv[2] names another flag, as base-overflow while a base
            loads) and block the compaction.
  measure   No hook input; print the context of the transcript in argv[2].

The context of a request is read from the transcript: input + cache read + cache write of the latest main-chain
request. When the hook runs, the request that made the tool call is not always recorded yet (2026-09-19: impl-23's
notice said 956K while that request carried 972K), so the gauge counts what the next request carries at least: the
latest recorded request, its output, what was recorded after it, and this tool's response as the model is shown it.

The ceiling is not the window. The API accepted impl-23's request of 972,479 tokens and refused the next, of about
979K ("Prompt is too long"): Claude Code retries a request whose input and max_tokens exceed the context limit with
a smaller max_tokens, but not below 3,000, and its own compaction of a 1M window starts only at 987K. The largest
growth of one request seen in 2,164 requests of impl-8 to impl-25 is 35K (p99 24K), over four requests 53K at p99;
the notice leaves room for a request not yet recorded and the handoff, the hard mark for one ordinary step.
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import v2  # noqa: E402
import work_meter  # noqa: E402

STATE = v2.STATE
CEILING, SOFT, HARD = v2.CEILING, v2.SOFT, v2.HARD
# Characters of recorded JSON per token: theory text runs 2.4 bytes a token before JSON escaping lengthens it,
# prose about 4, so the count errs high rather than low.
CHARS_PER_TOKEN = 2.5
# What a tool's response adds to the next request: the tools that write files answer with a line (what they wrote is
# the calling request's own output), a Read is shown whole, and other output is shown up to 30,000 characters
# (Claude Code's bashOutputMaxChars), beyond which a preview stands for it.
WRITERS = ("Write", "Edit", "MultiEdit", "NotebookEdit")
SHOWN_CHARS = 30_000


def scan(lines):
    """(context, output, characters recorded after it) of the latest main-chain request among transcript lines."""
    after = 0
    for line in reversed(lines):
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("isSidechain"):
            continue
        if d.get("type") == "assistant" and '"usage"' in line:
            u = (d.get("message") or {}).get("usage") or {}
            total = ((u.get("input_tokens") or 0) + (u.get("cache_read_input_tokens") or 0)
                     + (u.get("cache_creation_input_tokens") or 0))
            if total:
                return total, u.get("output_tokens") or 0, after
        elif d.get("type") == "user":
            after += len(json.dumps((d.get("message") or {}).get("content") or ""))
        elif d.get("type") == "attachment":
            after += len(json.dumps(d.get("attachment") or ""))
    return None


def latest_request(transcript):
    """(context, output, characters recorded after it) of the latest main-chain request, read from the file's tail."""
    try:
        size = os.path.getsize(transcript)
    except OSError:
        return 0, 0, 0
    span = 400_000
    while True:
        with open(transcript, "rb") as f:
            f.seek(max(0, size - span))
            found = scan(f.read().decode(errors="ignore").splitlines())
        if found:
            return found
        if span >= size or span >= 16_000_000:
            return 0, 0, 0
        span *= 4


def context_tokens(transcript):
    """Context of the latest recorded main-chain request."""
    return latest_request(transcript)[0]


def response_chars(tool, response):
    if tool in WRITERS:
        return 0
    size = len(json.dumps(response or ""))
    return size if tool == "Read" else min(size, SHOWN_CHARS)


def next_request_tokens(transcript, tool, response):
    """What the next request carries at least; it can exceed this by the output of a request not yet recorded."""
    context, output, after = latest_request(transcript)
    if not context:
        return 0
    return context + output + int((after + response_chars(tool, response)) / CHARS_PER_TOKEN)


def mark(session, what):
    """A per-session flag: soft (the notice was given) or hard (the session is at its end)."""
    return os.path.join(STATE, "flags", f"{session}.{what}")


def raise_mark(session, what, tokens, why):
    os.makedirs(os.path.join(STATE, "flags"), exist_ok=True)
    if not os.path.exists(mark(session, what)):
        open(mark(session, what), "w").write(f"{tokens} {why} {time.strftime('%Y-%m-%dT%H:%M:%S')}\n")


def add_context(event, text):
    print(json.dumps({"hookSpecificOutput": {"hookEventName": event, "additionalContext": text}}))


# How each role ends its piece of work: what its window's end asks of it, and what its Stop hook asks for.
ENDS = {
    "planner": "write HANDOFF.md as the planner's state, the events you have not handled under `## Now`, and the "
               "notes the knowledge base is to hold — everything you have settled since you began, aggregated, with "
               "what has since been answered or superseded left out — and end "
               "(`.claude/orchestration/v2.py planned --notes FILE`); the next planner starts from what you leave",
    "task-designer": "put the tasks you have briefed into the graph in form, each build or fix with its review task, "
                     "and record them (`.claude/orchestration/v2.py briefed {task} NEW...`); what you could not brief "
                     "goes to the planner (`v2.py ask --to planner`)",
    "reviewer": "write your verdict (.build/tasks/{task}/review.md) and record it "
                "(`.claude/orchestration/v2.py verdict {task} accept|reject --file .build/tasks/{task}/review.md`)",
    "consultant": "answer (`.claude/orchestration/v2.py reply {qid} TEXT`)",
}
PRODUCING_END = ("write your result, partial if the task is not finished (what exists, where, and what remains as "
                 "artifacts the next task can take up), to .build/tasks/{task}/result.md and record it "
                 "(`.claude/orchestration/v2.py result {task}`)")


def end_of(role, rec):
    return (ENDS.get(role) or PRODUCING_END).format(task=rec.get("task"), qid=rec.get("qid"))


def notice(role, rec, used):
    return (f"Context is at {used // 1000}K tokens, near the end of your window. Now {end_of(role, rec)}, and end your "
            f"turn. Requests beyond about {CEILING // 1000}K are refused; start nothing else.")


def may_end(role, rec):
    """Whether a session's turn may end: the knowledge base and an episode the owner speaks to always; any other once
    its piece of work has ended (its result, brief, verdict, answer or plan recorded) or it is parked. A producing
    session never waits otherwise (the owner, 2026-09-19: with nothing productive left it parks, and another worker
    produces); another session may also end its turn while a question of its own is open or a background job of its
    own runs (the answer, or the job's completion, runs its turn)."""
    if role in ("kb", "planner") or rec.get("owner") or rec.get("state") in ("done", "parked", "lost"):
        return True  # the planner's turn ends when it has handled what it was given: the next event wakes it, and its
        # mail is taken above, so there is nothing left when this is reached. An episode the owner opened waits for
        # the owner's words between turns.
    if role in v2.PRODUCING:
        # A producing session never waits holding the slot: it goes on, or it parks. But once its work has been
        # taken on by the harness there is nothing left to produce, and if the session record has not been updated
        # to say so there is no way out at all — `v2.py result` answers "End your turn now", this hook blocks it,
        # and ask, escalate and park each refuse a session the harness treats as closed. fix-49.2 sat in that loop
        # on 2026-09-20, recording its result twice, because its result had gone into a worktree's parallel state.
        # The task's stage is the second witness, so the way out does not rest on one piece of bookkeeping.
        return (v2.peek()["tasks"].get(rec.get("task") or "") or {}).get("stage") not in ("running", "fixing", None)
    if v2.running_jobs(rec["name"]):
        return True  # it waits for its own background job: the job's completion runs its turn
    return any(q["from"] == rec["name"] and q["state"] != "answered" for q in v2.peek()["asks"].values())


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "gauge"
    if mode == "measure":
        print(context_tokens(sys.argv[2]))
        return 0
    hook = json.load(sys.stdin)
    event = hook.get("hook_event_name", "PostToolUse")
    if hook.get("agent_id"):  # a subagent's tool call says nothing about the main context
        return 0
    session = hook.get("session_id", "")

    if mode == "tripwire":  # argv[2] names another flag to raise: base-overflow while a base loads
        if len(sys.argv) > 2 and sys.argv[2] != "rotate":
            os.makedirs(STATE, exist_ok=True)
            open(os.path.join(STATE, sys.argv[2]), "a").write(f"{session} precompact {time.strftime('%Y-%m-%dT%H:%M:%S')}\n")
        else:
            raise_mark(session, "hard", context_tokens(hook.get("transcript_path", "")), "precompact")
        sys.stderr.write("Compaction is not allowed in an orchestrated session: it is replaced instead.\n")
        return 2

    role, rec = v2.role_of(session)
    if role is None:
        return 0

    if mode == "owner":  # what the harness says begins with its mark; launch prompts and wrappers are not the owner's
        from extract_owner_directions import owner_statement
        text = owner_statement(hook.get("prompt") or "", set(), session)
        if text:
            v2.owner_said(rec, text)
        return 0

    if mode == "stop":
        mail = v2.take_mail(rec["name"])
        if mail:
            print(json.dumps({"decision": "block", "reason": mail}))
            return 0
        if may_end(role, rec):
            return 0
        reason = (f"Your turn ends only when your piece of work has ended or while you wait on a question of your own. "
                  f"Continue: produce the next part of your deliverable; bring what is not yours to decide to its author "
                  f"or the planner (`v2.py ask`); when you are finished, {end_of(role, rec)}.")
        if os.path.exists(mark(session, "soft")):
            reason = notice(role, rec, 0).split(". ", 1)[1]
        print(json.dumps({"decision": "block", "reason": reason}))
        return 0

    # gauge
    used = next_request_tokens(hook.get("transcript_path", ""), hook.get("tool_name"), hook.get("tool_response"))
    v2.hit_chain(rec["name"])  # its requests keep its own cache entry and its origins' alive (measured 2026-09-18)
    parts = []
    mail = v2.take_mail(rec["name"])
    if mail:
        parts.append(mail)
    if used >= SOFT and not os.path.exists(mark(session, "soft")):
        raise_mark(session, "soft", used, "soft-threshold")
        parts.append(notice(role, rec, used))
    if used >= HARD:
        raise_mark(session, "hard", used, "hard-threshold")
    if role != "kb":
        try:
            note = work_meter.record(hook, rec)
        except Exception:  # the meter never stops the gauge
            note = None
        if note:
            parts.append(note)
    if parts:
        add_context(event, "\n\n".join(parts))
    return 0


if __name__ == "__main__":
    sys.exit(main())
