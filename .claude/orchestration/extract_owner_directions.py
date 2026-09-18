#!/usr/bin/env python3
"""Regenerate the reviewed Claude owner-direction selection with exact source checks.

Default: preserve owner-directions-selection.json and render its verbatim excerpts.
--verify: check the current curated file without writing it.
--raw: explicitly run the legacy chronological collector and its truncation rules.
--new: write state/owner-directions-new.md, the owner's typed words given after the curated selections were
       collected (`reviewed_through` in owner-directions-selection.json), from Claude sessions and interactive
       Codex sessions of this repository. Sessions that work on the orchestration itself are left out.
       rotate.sh runs this before every implementer starts, and the implementer reads it.
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
SKIP = re.compile(r"^\s*(\[Request interrupted[^\]]*\]|continue|/compact|/clear)\s*$", re.I)
WRAPPED = ("<task-notification>", "<system-reminder>", "<local-command", "<command-message>", "[SYSTEM NOTIFICATION")
PEER = ("<cross-session-message", "[Cross-session")
# launch prompts written by rotate.sh and kb.sh are not the owner's typed words
LAUNCH = ("You are impl-", "Load the knowledge base as your instructions describe", "You are being loaded as the base",
          "You are the live kb", "Keep-warm ping", "Load the reference library;", "You are loading a sealed base",
          "You were stopped (")
LONG, KEEP = 4000, 600
STATE = os.environ.get("ORCH_STATE_DIR") or os.path.join(HERE, "state")
CODEX_SESSIONS = os.path.expanduser(os.environ.get("CODEX_SESSIONS", "~/.codex/sessions"))
CODEX_WRAPPED = ("<environment_context", "<user_instructions", "# AGENTS.md", "<permissions", "<turn_aborted",
                 "<recommended_plugins", "<codex_internal_context")
ORCHESTRATION = re.compile(r"\.claude/orchestration(?:/((?:state/)?[\w.-]+))?")
# What an implementer itself reads or runs there. A tool call naming anything else of the directory marks a
# session that works on the orchestration, whose conversation is about it rather than about the library.
WORKING_FILES = {"owner-ledger.md", "impl_state.sh", "owner-directions.md", "codex-owner-directions.md",
                 "state/owner-directions-new.md"}
BASE_EMIT = re.compile(r"base_pack\.py\S*\s+emit\b")  # a fork's copy of its base's load


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
    if BASE_EMIT.search(text):
        return False
    return any(name not in WORKING_FILES for name in ORCHESTRATION.findall(text))


def claude_session(path):
    """(timestamp, line, typed text) of the user messages, and whether the session works on the orchestration."""
    messages, orchestration = [], False
    for n, line in enumerate(open(path, errors="ignore"), 1):
        user, tool = '"type":"user"' in line, '"tool_use"' in line
        if not user and not (tool and not orchestration):
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("isSidechain"):
            continue
        if d.get("type") == "user" and not (d.get("isMeta") or d.get("isCompactSummary")):
            text = typed_text(d)
            if text.strip():
                messages.append((d.get("timestamp", ""), n, text))
        elif d.get("type") == "assistant":
            for c in (d.get("message") or {}).get("content") or []:
                if isinstance(c, dict) and c.get("type") == "tool_use":
                    orchestration = orchestration or works_on_orchestration(json.dumps(c.get("input") or {}))
    return messages, orchestration


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


def uncurated():
    """Write the owner's words that neither curated selection covers, oldest first."""
    since = json.loads(Path(HERE, "owner-directions-selection.json").read_text())["reviewed_through"]
    since_epoch = calendar.timegm(time.strptime(since[:19], "%Y-%m-%dT%H:%M:%S"))
    rows, seen, goals = [], set(), set()
    sources = [("Claude", f) for f in glob.glob(SESSIONS + "/*.jsonl") if os.path.getmtime(f) > since_epoch]
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
            if t and (ts[:19], t) not in seen:
                seen.add((ts[:19], t))
                rows.append((ts, kind, sid[:8], n, t))
    out = ["# Owner directions given since the curated ones", "",
           "The owner's typed words given after the curated owner directions were collected "
           f"({since[:16].replace('T', ' ')} UTC), verbatim and oldest first, from the Claude and Codex sessions of "
           "this repository. Where directions conflict, the newer one holds. A statement over "
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
    for f in sorted(glob.glob(SESSIONS + "/*.jsonl"), key=os.path.getmtime):
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
