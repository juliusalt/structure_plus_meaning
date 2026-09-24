#!/usr/bin/env python3
"""Regenerate the reviewed Claude owner-direction selection with exact source checks.

Default: preserve owner-directions-selection.json and render its verbatim excerpts.
--verify: check the current curated file without writing it.
--raw: explicitly run the legacy chronological collector and its truncation rules.
--new: write state/owner-directions-new.md, the owner's typed words given after the curated selections were
       collected (`reviewed_through` in owner-directions-selection.json), from Claude sessions and interactive
       Codex sessions of this repository, including what the owner typed while a session was working. Sessions
       that work on the orchestration itself are left out: sessions other than implementers whose own tool
       calls name anything of this directory beyond the working files. So is what the owner ledger records
       already, which the knowledge base reads beside it. v2.py runs this before every planner starts, and the
       planner reads it.
"""
import glob
import json
import os
import re
import hashlib
from pathlib import Path
import sys
import time
import calendar

HERE = os.path.dirname(os.path.abspath(__file__))
PROJECT = os.path.dirname(os.path.dirname(HERE))
SESSIONS = os.path.expanduser("~/.claude/projects/" + PROJECT.replace("/", "-").replace("_", "-"))


def claude_transcripts():
    """The project's Claude transcripts and its task trees' (v2.transcript_dirs): the owner may speak to a session
    that works in a tree of its own."""
    sys.path.insert(0, HERE)
    import v2
    return [f for d in v2.transcript_dirs(SESSIONS) for f in glob.glob(d + "/*.jsonl")]
# what the owner typed that is not a direction: the interruption marks and the slash commands, and a single short
# word — a stray keystroke or a shell command typed into the wrong window ("a" and "ls" both reached a knowledge
# base as directions on 2026-09-20). Out of the session it was typed in, such a word decides nothing.
SKIP = re.compile(r"^\s*(\[Request interrupted[^\]]*\]|continue|/compact|/clear|\w{1,3}|ls\s+[-\w./]*|pwd|clear|exit)\s*$",
                  re.I)
WRAPPED = ("<task-notification>", "<system-reminder>", "<local-command", "<command-message>", "[SYSTEM NOTIFICATION")
PEER = ("<cross-session-message", "[Cross-session")
# A base's load: a fork carries its base's conversation as the first part of its own transcript.
BASE_LOADS = ("You are being loaded as the base", "Load the reference library;")
IMPLEMENTER = "You are impl-"  # the start of an implementer (v1), which works on the library whatever it looks up
# the starts of the sessions that work on the library whatever they look up: v1 implementers, and every role of v2
LIBRARY_ROLES = (IMPLEMENTER, "You are kb-", "You are plan-", "You are design-", "You are brief-", "You are investigate-",
                 "You are review-", "You are implement-", "You are fix-", "You are ask-")
# launch prompts written by the harness are not the owner's typed words
# and neither is what the harness says to a session: its mail, its wakes, its stop hook's reasons
LAUNCH = BASE_LOADS + LIBRARY_ROLES + ("Load the knowledge base as your instructions describe", "You are the live kb",
                                       "You are layer-", "You are churn-", "You are reference-",
                                       "You are max-reasoning,", "You are xhigh-reasoning,", "You are high-reasoning,",
                                       "Keep-warm ping", "You are loading a sealed base", "You were stopped",
                                       "Your turn ended without a result", "Stop hook feedback:", "Message from ",
                                       "[harness]")
LONG, KEEP = 4000, 600
STATE = os.environ.get("ORCH_STATE_DIR") or os.path.join(HERE, "state")
CODEX_SESSIONS = os.path.expanduser(os.environ.get("CODEX_SESSIONS", "~/.codex/sessions"))
CODEX_WRAPPED = ("<environment_context", "<user_instructions", "# AGENTS.md", "<permissions", "<turn_aborted",
                 "<recommended_plugins", "<codex_internal_context")
ORCHESTRATION = re.compile(r"\.claude/orchestration(?:/((?:state/)?[\w.-]+))?")
# What a session working on the library itself reads or runs there. A tool call naming anything else of the directory
# marks a session of no role (and no v1 implementer) as one that works on the orchestration, whose
# conversation is about it rather than about the library.
WORKING_FILES = {"owner-ledger.md", "owner-directions.md", "codex-owner-directions.md", "state/owner-directions-new.md",
                 "show.py"}


def typed_text(d):
    c = (d.get("message") or {}).get("content")
    if isinstance(c, list):
        c = "\n".join(x.get("text", "") for x in c if isinstance(x, dict) and x.get("type") == "text")
    return c if isinstance(c, str) else ""


def owner_statement(t, goals, session):
    """The owner's typed words in a user message, or None for launch prompts, wrappers and bare controls."""
    t = t.strip()
    if not t:
        return None
    goal = re.search(r"<command-name>/goal</command-name>.*?<command-args>(.*?)</command-args>", t, re.S)
    if goal:
        t = goal.group(1).strip()
        key = re.sub(r"\s+", " ", t)
        if not t or key in goals or t in ("clear", "stop", "off", "reset", "none", "cancel"):
            return None
        goals.add(key)
        return "/goal " + t
    if any(w in t for w in WRAPPED + PEER) or t.startswith(LAUNCH + CODEX_WRAPPED) or SKIP.match(t):
        return None
    if len(t) > LONG:  # long statements are mostly pasted third-party text, which is not the owner's word
        t = t[:KEEP].rstrip() + f"\n[… {len(t) - KEEP} further characters omitted: statements over {LONG} characters are cut here because they are mostly pasted material; the full text is in session {session}]"
    return t


def works_on_orchestration(text):
    return any(name not in WORKING_FILES for name in ORCHESTRATION.findall(text))


def queued_text(d):
    """What the owner typed while the session was working: Claude Code records it as a queued command."""
    a = d.get("attachment") or {}
    if a.get("type") != "queued_command" or a.get("commandMode", "prompt") != "prompt" \
            or (a.get("origin") or {}).get("kind") != "human":
        return ""
    p = a.get("prompt")
    if isinstance(p, list):
        p = "\n".join(x.get("text", "") for x in p if isinstance(x, dict) and x.get("type") == "text")
    return p if isinstance(p, str) else ""


def claude_session(path):
    """(timestamp, line, typed text) of the owner's messages, and whether the session works on the orchestration.

    A fork's copy of its base's load is not its own work, and an implementer works on the library whatever it
    looks up in this directory."""
    messages, touched, implementer, copied, background = [], False, False, False, False
    for n, line in enumerate(open(path, errors="ignore"), 1):
        background = background or '"sessionKind":"bg"' in line
        user, queued, tool = '"type":"user"' in line, '"queued_command"' in line, '"tool_use"' in line
        if not user and not queued and not (tool and not touched and not copied):
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("isSidechain"):
            continue
        text = ""
        if d.get("type") == "user" and not (d.get("isMeta") or d.get("isCompactSummary")):
            text = typed_text(d)
        elif d.get("type") == "attachment":
            text = queued_text(d)
        elif d.get("type") == "assistant" and not copied and not touched:
            for c in (d.get("message") or {}).get("content") or []:
                if isinstance(c, dict) and c.get("type") == "tool_use":
                    touched = touched or works_on_orchestration(json.dumps(c.get("input") or {}))
        if text.strip():
            messages.append((d.get("timestamp", ""), n, text))
            if text.lstrip().startswith(BASE_LOADS):
                copied = True
            elif not any(w in text for w in WRAPPED + PEER):
                copied = False
                implementer = implementer or text.lstrip().startswith(LIBRARY_ROLES)
    if background:
        # A background session's prompts are its launcher's — the harness's own sessions, its bases and deltas, the
        # probes a developer starts — never the owner's typing: 30 of the 34 statements collected by 2026-09-23 were
        # such prompts (probes, and delta hold messages with whole theory diffs in them). What the owner types into
        # a harness session reaches the ledger through its hook (ctx_gauge owner), which the knowledge base holds.
        return [], touched and not implementer
    return messages, touched and not implementer


def codex_session(path):
    """The same for a Codex rollout, or None for a session of another directory or an automated (exec) run."""
    messages, orchestration = [], False
    with open(path, errors="ignore") as lines:
        try:
            meta = json.loads(next(lines)).get("payload") or {}
        except (StopIteration, ValueError):
            return None
        if meta.get("cwd") != PROJECT or meta.get("source") == "exec":
            return None
        for n, line in enumerate(lines, 2):
            if '"role":"user"' not in line and not ('_call"' in line and not orchestration):
                continue
            try:
                d = json.loads(line)
            except ValueError:
                continue
            p = d.get("payload") or {}
            if d.get("type") != "response_item":
                continue
            if p.get("type") == "message" and p.get("role") == "user":
                text = "\n".join(c.get("text", "") for c in p.get("content") or [] if isinstance(c, dict))
                if text.strip():
                    messages.append((d.get("timestamp", ""), n, text))
            elif p.get("type") in ("custom_tool_call", "function_call", "local_shell_call"):
                orchestration = orchestration or works_on_orchestration(json.dumps(p))
    return messages, orchestration


def spaced(text):
    """A statement's words, its quotation marks and line breaks left out: a file quotes it wrapped as its lines fall."""
    return " ".join(re.sub(r"(?m)^>[ \t]?", "", text).split())


def ledger_quotes():
    """What the owner ledger records of the owner's words, each quotation as spaced: the knowledge base reads the ledger
    beside this file, so a statement in both stood twice in its context (the two Codex questions of 2026-09-19 did)."""
    try:
        text = Path(HERE, "owner-ledger.md").read_text(errors="ignore")
    except OSError:
        return []
    return [spaced(block) for block in re.findall(r"(?m)(?:^>.*\n?)+", text)]


def uncurated():
    """Write the owner's words that neither curated selection covers and the ledger does not record, oldest first."""
    since = json.loads(Path(HERE, "owner-directions-selection.json").read_text())["reviewed_through"]
    since_epoch = calendar.timegm(time.strptime(since[:19], "%Y-%m-%dT%H:%M:%S"))
    rows, seen, goals = [], set(), set()
    recorded = {q[:300] for q in ledger_quotes()}
    sources = [("Claude", f) for f in claude_transcripts() if os.path.getmtime(f) > since_epoch]
    sources += [("Codex", f) for f in glob.glob(CODEX_SESSIONS + "/*/*/*/rollout-*.jsonl")
                if os.path.getmtime(f) > since_epoch]
    for kind, f in sources:
        scanned = claude_session(f) if kind == "Claude" else codex_session(f)
        if not scanned or scanned[1]:
            continue
        sid = os.path.basename(f)[:-6].split("-", 6)[-1] if kind == "Codex" else os.path.basename(f)[:8]
        for ts, n, text in scanned[0]:
            if ts[:19] <= since[:19]:
                continue
            t = owner_statement(text, goals, sid[:8])
            if t and spaced(t)[:300] in recorded:
                continue  # the ledger records it: read there
            if t and (ts[:19], t) not in seen:
                seen.add((ts[:19], t))
                rows.append((ts, kind, sid[:8], n, t))
    out = ["# Owner directions given since the curated ones", "",
           "The owner's typed words given after the curated owner directions were collected "
           f"({since[:16].replace('T', ' ')} UTC), verbatim and oldest first, from the Claude and Codex sessions of "
           "this repository, less what the owner ledger records (read there). Where directions conflict, the newer "
           "one holds. A statement over "
           f"{LONG} characters is cut after {KEEP}, because such statements are mostly pasted material; the marker "
           "names the session that holds it in full.", ""]
    for ts, kind, sid, n, t in sorted(rows):
        out += [f"## {ts[:16].replace('T', ' ')} UTC · {kind} {sid} · L{n}", ""]
        out += ["> " + ln for ln in t.splitlines()] + [""]
    if not rows:
        out.append("None.")
    path = Path(STATE, "owner-directions-new.md")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(out) + "\n")
    print(f"{len(rows)} owner statements since the curated ones -> {path}")


def main():
    if "--new" in sys.argv:
        return uncurated()
    selection_path = Path(HERE, "owner-directions-selection.json")
    if "--verify" in sys.argv and not selection_path.exists():
        raise ValueError("no reviewed owner-direction selection exists")
    if selection_path.exists() and "--raw" not in sys.argv:
        selection = json.loads(selection_path.read_text())
        out = list(selection["header"])
        for number, section in enumerate(selection["sections"], 1):
            out += [f"## {number}. {section['title']}", "",
                    "Context (editorial): " + section["context"], ""]
            for item in section["excerpts"]:
                with open(item["source"], "rb") as source:
                    source.seek(item["byte_offset"])
                    raw = source.readline()
                if hashlib.sha256(raw).hexdigest() != item["record_sha256"]:
                    raise ValueError("selected source record changed")
                record = json.loads(raw)
                if record.get("type") != "user" or any(
                        record.get(k) for k in ("isSidechain", "isMeta", "isCompactSummary")):
                    raise ValueError("selected record is not an owner input")
                text = typed_text(record)
                quote = text[item["start"]:item["end"]]
                if (hashlib.sha256(text.encode()).hexdigest() != item["text_sha256"]
                        or hashlib.sha256(quote.encode()).hexdigest() != item["quote_sha256"]):
                    raise ValueError("selected source excerpt changed")
                out += [item["timestamp"][:16].replace("T", " ") + " UTC · "
                        + item["session_id"][:8] + f" · L{item['line']}", ""]
                out.extend("> " + line for line in quote.split("\n"))
                out.append("")
        result = "\n".join(out)
        path = Path(HERE, "owner-directions.md")
        if "--verify" in sys.argv:
            if path.read_text() != result:
                raise ValueError("curated document differs from its selected source excerpts")
        else:
            path.write_text(result)
        print(f"{len(selection['sections'])} curated topics; source excerpts verified; {len(result.encode())} bytes")
        return
    out, goals, count = [], set(), 0
    for f in sorted(claude_transcripts(), key=os.path.getmtime):
        rows = []
        for line in open(f, errors="ignore"):
            if '"type":"user"' not in line:
                continue
            try:
                d = json.loads(line)
            except ValueError:
                continue
            if d.get("isSidechain") or d.get("isMeta") or d.get("isCompactSummary"):
                continue
            t = owner_statement(typed_text(d), goals, os.path.basename(f)[:8])
            if not t:
                continue
            rows.append((d.get("timestamp", "")[:16].replace("T", " "), t))
        if rows:
            out.append(f"\n## Session {os.path.basename(f)[:8]}\n")
            for ts, t in rows:
                out.append(f"**{ts} UTC**\n\n" + "\n".join("> " + ln for ln in t.splitlines()) + "\n")
                count += 1
    head = (
        "# Owner directions, verbatim\n\n"
        "Generated by `.claude/orchestration/extract_owner_directions.py` from this project's Claude session\n"
        "records. Every quoted block is the owner's typed text, unedited and in order; nothing here is a\n"
        "summary or a reading. Later statements supersede earlier ones where they conflict. A statement over\n"
        f"{LONG} characters is cut after {KEEP}, with a marker, because such statements are mostly pasted\n"
        "third-party text that does not carry the owner's authority. Codex rollouts are not included.\n"
    )
    path = os.path.join(HERE, "owner-directions.md")
    open(path, "w").write(head + "\n".join(out))
    print(f"{count} owner statements, {os.path.getsize(path) // 1000}K chars -> {os.path.relpath(path, PROJECT)}")


if __name__ == "__main__":
    main()
