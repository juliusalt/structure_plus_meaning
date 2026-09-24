#!/usr/bin/env python3
"""Whether the context window still holds as the harness assumes it (v2.CEILING, v2.WRAP_UP, v2.HARD; the owner's order
of 2026-09-23 evening: Claude Opus 5.5, auto-compact off, the ceiling raised, a 30K margin for the wrap-up, "and add a
health tracker that catches if this ever becomes a problem").

Each minute (the watchdog) it reads what was added to the transcript of every session the harness keeps — the roles',
the reasoning layers', the bases' — and keeps, per session, its largest request and how much each request grew its
context. Its own records only: a fork's copy of its origin's history is not its work. Each of these is a sign that the
assumption no longer holds, and is said once, as ATTENTION in the log (health.py shows them with the figures):

- compacted: a compaction in a transcript — auto-compact is off in every settings file, so it should never happen;
- refused: a request refused as too long ("Prompt is too long"; Claude Code's own "Context limit reached") — the
  window's real limit is below the ceiling the gauge works to;
- window stop: a reply stopped at the window (stop_reason model_context_window_exceeded);
- cut short: a reply stopped at its max_tokens once past the notice — the room left for replies ran out;
- over the ceiling: a request larger than the ceiling was accepted — the limit moved, and the ceiling gives room away;
- margin outgrown: a session past the notice came within LAST_STEP of the ceiling (its wrap-up needed more than the
  margin allows), or one request grew a context by more than the whole margin (a step can jump the notice);
- another model: a request on another model than base-model's — a session forked from something older;
- another version: a Claude Code version other than the one the ceiling was read from (v2.CLAUDE_CODE_LIMITS): its
  limits are to be read again;
- declined: a classifier declined a turn (stop_reason refusal) — Claude Opus 5.5's are broader than Claude Opus 5's.

It watches from its first run on (`since`): sessions and records before it were on another model and window.

What Claude Code itself puts into a session's context is read too, once for each stable base — the one session every
other forks, so every fork holds its opening (audit_openings, also run after each build): Claude Code keeps what it
gave it (its instruction files, its session context, a snapshot of its system prompt) in its first records. Said, as
the window's findings are, when any of what the settings files turn off reaches it after all (the owner, 2026-09-23
evening, on the memory that had reached every base: "generalize this and try to find other similar problems"):

- memory reached: Claude Code's memory — its index as an instruction file, or its memory section in the system
  prompt: most of it is the orchestrator's own development (auto-memory off);
- git status reached: a git status and the recent commits, frozen when the base loaded and mostly the orchestrator's
  own files (git instructions off);
- instructions reached: an instruction file Claude Code loaded on its own (a CLAUDE.md added somewhere): only what the
  base's list names is to reach a base;
- skills reached: a list of skills (slash commands off, session-flags).
"""
import contextlib
import datetime
import glob
import json
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import v2  # noqa: E402

GROWTHS_KEPT = 5000  # the most recent own requests' growths, for the percentile health.py shows
FINDINGS_KEPT = 300
TOO_LONG = re.compile(r"(?i)prompt is too long|context limit reached|exceed context limit")
KINDS = {
    "compacted": "was compacted, and auto-compact is off in every settings file: the setting no longer holds",
    "refused": "had a request refused as too long: the window's real limit is below the {ceiling}K ceiling",
    "window stop": "had a reply stopped at the context window",
    "cut short": "had a reply cut at its max_tokens past the notice: the room left for replies ran out",
    "over the ceiling": "had a request of {tokens}K accepted, over the {ceiling}K ceiling: the limit moved, read it again",
    "margin outgrown": "came to {tokens}K after the notice, within {last}K of the {ceiling}K ceiling: the {wrap}K "
                       "wrap-up margin is tight",
    "step outgrown": "grew its context by {tokens}K in one request, more than the {wrap}K wrap-up margin: a step can "
                     "jump the notice",
    "another model": "ran on {model}, not {expected} (base-model)",
    "another version": "ran on Claude Code {version}; the ceiling was read from {limits}: read its limits again",
    "declined": "had a turn declined by a classifier (stop_reason refusal)",
    "memory reached": "opened with Claude Code's memory ({what}): auto-memory is to be off in every settings file",
    "git status reached": "opened with a git status snapshot: git instructions are to be off in every settings file",
    "instructions reached": "opened with an instruction file Claude Code loaded on its own ({what}): only what the "
                            "base's list names is to reach a base",
    "skills reached": "opened with a list of skills: slash commands and skills are to be off (session-flags)",
}
SKILLS = re.compile(r"skills are available|# Skills\b|\bSkill tool\b")


def path():
    return os.path.join(v2.STATE, "window-watch.json")


def load():
    try:
        return json.load(open(path()))
    except (OSError, ValueError):
        return {"since": time.time(), "files": {}, "sessions": {}, "growths": [], "findings": []}


def save(state):
    tmp = path() + f".tmp-{os.getpid()}"
    try:
        json.dump(state, open(tmp, "w"))
        os.replace(tmp, path())
    finally:
        with contextlib.suppress(OSError):
            os.remove(tmp)


def epoch(stamp):
    try:
        return datetime.datetime.fromisoformat(stamp.replace("Z", "+00:00")).timestamp()
    except (AttributeError, ValueError):
        return None


def watched():
    """{sid: (name, started, whether it loads a base)}: every session the harness keeps, and every base's parts."""
    out = {}
    for name, s in v2.peek()["sessions"].items():
        if s.get("sid"):
            out[s["sid"]] = (name, float(s.get("started") or s.get("starting") or 0), False)
    for record in glob.glob(os.path.join(v2.STATE, "*.json")):
        base = os.path.basename(record)
        if not re.fullmatch(r"(max|xhigh|high)-(base|base-next|layer|delta|reasoning|part-[\w-]+)\.json", base):
            continue
        with contextlib.suppress(OSError, ValueError, AttributeError):
            rec = json.load(open(record))
            for node in [rec] + list(rec.get("parts") or []):
                if node.get("sessionId") and node["sessionId"] not in out:
                    # a base's load grows its context by a chunk a request by design: its growth is not a step's
                    out[node["sessionId"]] = (node.get("name") or base[:-5], 0.0, node.get("kind") != "reasoning")
    return out


def read_new(transcript, offset):
    """(the complete lines added since `offset`, the offset after them)."""
    try:
        with open(transcript, "rb") as f:
            f.seek(offset)
            data = f.read()
    except OSError:
        return [], offset
    end = data.rfind(b"\n")
    if end < 0:
        return [], offset
    return data[:end + 1].decode("utf-8", "replace").splitlines(), offset + end + 1


def found(state, kind, sid, name, **values):
    """Record a finding and say it, once for each kind and session."""
    if any(f["kind"] == kind and f["session"] == sid for f in state["findings"]):
        return
    values = dict(ceiling=v2.CEILING // 1000, wrap=v2.WRAP_UP // 1000, last=v2.LAST_STEP // 1000,
                  limits=v2.CLAUDE_CODE_LIMITS, expected=v2.api_model(v2.base_model()), **values)
    text = f"{name} " + KINDS[kind].format(**values)
    state["findings"] = (state["findings"] + [dict(at=time.time(), kind=kind, session=sid, name=name, text=text)])[
        -FINDINGS_KEPT:]
    v2.log(f"ATTENTION window: {text}")


def opening(transcript):
    """([(kind, what)] of what Claude Code put into a session's opening context, whether its opening was read whole):
    its records up to its first reply."""
    out, whole = [], False
    try:
        lines = open(transcript, errors="ignore")
    except OSError:
        return out, whole
    for n, line in enumerate(lines):
        if n > 400:
            break
        try:
            r = json.loads(line)
        except ValueError:
            continue
        if r.get("type") == "assistant":
            break
        a = r.get("attachment") or {}
        if a.get("type") == "instructions":
            for f in a.get("files") or []:
                where = f.get("path") or "?"
                out.append(("memory reached" if f.get("type") == "AutoMem" or "/memory/" in where
                            else "instructions reached", where))
        elif a.get("type") == "session_context":
            if (a.get("context") or {}).get("gitStatus"):
                out.append(("git status reached", ""))
        elif a.get("type") == "prompt_snapshot":
            whole = True
            prompt = "\n".join(p for p in a.get("systemPrompt") or [] if isinstance(p, str))
            if re.search(r"^# Memory\b", prompt, re.M):
                out.append(("memory reached", "the memory section of its system prompt"))
            if SKILLS.search(prompt):
                out.append(("skills reached", ""))
        elif a and SKILLS.search(json.dumps(a)):
            out.append(("skills reached", ""))
    return out, whole


def audit_openings(state=None):
    """Read, once for each stable base, what Claude Code put into its opening context, and say what should not be there."""
    keep = state is None
    state = state or load()
    audited = state.setdefault("audited", [])
    for record in sorted(glob.glob(os.path.join(v2.STATE, "*.json"))):
        if not re.fullmatch(r"(max|xhigh|high)-(base|base-next)\.json", os.path.basename(record)):
            continue
        with contextlib.suppress(OSError, ValueError, AttributeError):
            rec = json.load(open(record))
            sid = rec.get("sessionId")
            if not sid or sid in audited:
                continue
            seen, whole = opening(v2.transcript(sid))
            for kind, what in seen:
                found(state, kind, sid, rec.get("name") or os.path.basename(record)[:-5], what=what)
            if whole:  # a base still loading has not written its opening yet: read again at the next pass
                audited.append(sid)
    if keep:
        save(state)
    return state


def check():
    """Read what every watched transcript added, keep the figures, and say what is new."""
    state = audit_openings(load())
    expected = v2.api_model(v2.base_model())
    for sid, (name, started, loads) in watched().items():
        transcript = v2.transcript(sid)
        offset = state["files"].get(transcript, 0)
        with contextlib.suppress(OSError):
            if os.path.getsize(transcript) <= offset:
                continue
        lines, state["files"][transcript] = read_new(transcript, offset)
        mine = state["sessions"].setdefault(sid, dict(name=name, peak=0, last=0, growth=0, past_notice=False,
                                                      after_notice=0))
        since = max(state["since"], started - 5)
        for line in lines:
            stamp = re.search(r'"timestamp":\s*"([^"]+)"', line)
            at = epoch(stamp.group(1)) if stamp else None
            if at is None or at < since:
                continue  # its origin's history, copied into a fork, or a record from before the watch began
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if r.get("type") == "system" and r.get("subtype") == "compact_boundary":
                found(state, "compacted", sid, name)
                continue
            if r.get("type") != "assistant":
                continue
            m = r.get("message") or {}
            if r.get("isApiErrorMessage"):
                text = " ".join(c.get("text", "") for c in m.get("content") or [] if isinstance(c, dict))
                if TOO_LONG.search(text):
                    found(state, "refused", sid, name)
                continue
            if r.get("version") and r["version"] != v2.CLAUDE_CODE_LIMITS:
                found(state, "another version", sid, name, version=r["version"])
            model, usage = m.get("model"), m.get("usage") or {}
            if model and model != "<synthetic>" and model != expected:
                found(state, "another model", sid, name, model=model)
            stop = m.get("stop_reason")
            if stop == "model_context_window_exceeded":
                found(state, "window stop", sid, name)
            elif stop == "refusal":
                found(state, "declined", sid, name)
            context = usage.get("input_tokens", 0) + usage.get("cache_read_input_tokens", 0) \
                + usage.get("cache_creation_input_tokens", 0)
            if not context:
                continue
            if stop == "max_tokens" and context >= v2.SOFT:
                found(state, "cut short", sid, name)
            if context > v2.CEILING:
                found(state, "over the ceiling", sid, name, tokens=context // 1000)
            grown = context - (mine["last"] or context)
            if mine["last"] and grown > 0 and not loads:
                state["growths"] = (state["growths"] + [grown])[-GROWTHS_KEPT:]
                mine["growth"] = max(mine["growth"], grown)
                if grown > v2.WRAP_UP:
                    found(state, "step outgrown", sid, name, tokens=grown // 1000)
            mine["last"], mine["peak"] = context, max(mine["peak"], context)
            if context >= v2.SOFT:
                mine["past_notice"] = True
                mine["after_notice"] = max(mine["after_notice"], context)
                if context >= v2.HARD and not loads:
                    found(state, "margin outgrown", sid, name, tokens=context // 1000)
    save(state)
    return state


def summary(state=None):
    """The figures and the findings, for health.py: one line, then an ATTENTION line for each finding of the day."""
    state = state or load()
    growths = sorted(state["growths"])
    p99 = growths[min(len(growths) - 1, int(0.99 * len(growths)))] if growths else 0
    sessions = state["sessions"].values()
    past = [s for s in sessions if s.get("past_notice")]
    used = max((s["after_notice"] - v2.SOFT for s in past), default=None)
    lines = [f"window: Claude Code {v2.CLAUDE_CODE_LIMITS} on {v2.api_model(v2.base_model())}, ceiling "
             f"{v2.CEILING // 1000}K, notice at {v2.SOFT // 1000}K ({v2.WRAP_UP // 1000}K to wrap up), end mark at "
             f"{v2.HARD // 1000}K; since {time.strftime('%m-%d %H:%M', time.localtime(state['since']))}: "
             f"{len(state['sessions'])} sessions, largest request {max((s['peak'] for s in sessions), default=0) // 1000}K, "
             f"largest growth of one request {max(growths, default=0) // 1000}K (p99 {p99 // 1000}K), "
             f"{len(past)} past the notice"
             + (f", the most any used of its margin {used // 1000}K of {v2.WRAP_UP // 1000}K" if used is not None else "")]
    lines += [f"ATTENTION window: {f['text']} ({time.strftime('%m-%d %H:%M', time.localtime(f['at']))})"
              for f in state["findings"] if time.time() - f["at"] < 86400]
    return lines


if __name__ == "__main__":
    for line in summary(check()):
        print(line)
