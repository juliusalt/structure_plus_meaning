#!/usr/bin/env python3
"""The run's console: a local web page to monitor and control the orchestration (the owner, 2026-09-23: "a web page
that shows me all the information for a current run allows me to view individual sessions, their messages, what they
produced, how many turns they took, what failed, the batching, the individual commands and in general a full suite in
which I can both monitor and control the run").

    python3 .claude/orchestration/dashboard.py [--port 8765]

Run it from your own terminal (outside Claude Code's sandbox, like start.sh, so that its controls can start and stop
sessions). It listens on 127.0.0.1 only and prints the address with a token made at its start; every request needs the
token (a control needs it as the X-Token header, which another site's page cannot send), and a request naming another
host is refused. No library beyond Python's own.

What it reads, it reads where the harness keeps it — state/v2.json and the archive, the task list, the transcripts,
.build/tasks/ID/, v2.log — and computes nothing the harness does not: a session's turns and calls are read from its
transcript's own part (a fork's transcript begins with its origin's, which is not its own). Its controls are the
harness's own commands and the owner's switches (state files), each said in the log as the owner's.
"""
import argparse
import calendar
import collections
import contextlib
import html
import http.server
import json
import os
import re
import secrets
import socketserver
import subprocess
import sys
import threading
import time
import urllib.parse

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import v2  # noqa: E402
import role_evidence  # noqa: E402

SWITCHES = ("review-beside-check", "continue-by-fork", "measure-bound", "support-apart", "grouped-repairs",
            "role-layers")
HOLDS = {"graph": v2.GRAPH_HELD, "launch": v2.NO_LAUNCH}
CUT = int(os.environ.get("ORCH_DASHBOARD_CUT", 20_000))  # characters of one call's output shown before "the rest"
STAMP = re.compile(r'"timestamp":\s*"(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d)')
# a call that failed as itself: a command's exit, or the tool's own failure (it could not start, the sandbox refused)
FAILED = re.compile(r"(Exit code \d+|Could not start|bwrap:|Error: |<tool_use_error>|File does not exist|Command timed out)")
READ, WRITE, OUTPUT = 0.1, 2.0, 5.0


# ---------------------------------------------------------------- reading

def state_file(name):
    try:
        return open(os.path.join(v2.STATE, name), errors="ignore").read()
    except OSError:
        return None


def all_sessions(archive=False):
    out = {}
    if archive:
        try:
            for line in open(os.path.join(v2.STATE, "v2-archive.jsonl"), errors="ignore"):
                try:
                    s = json.loads(line).get("session")
                except ValueError:
                    continue
                if s and s.get("name"):
                    out[s["name"]] = dict(s, archived=True)
        except OSError:
            pass
    out.update(v2.peek()["sessions"])
    return out


def transcript_path(sid):
    for d in v2.transcript_dirs():
        p = os.path.join(d, f"{sid}.jsonl")
        if os.path.exists(p):
            return p
    return None


def own_records(path, started):
    """A session's own records of its transcript, in order: from its launch on, never its origin's copy."""
    try:
        lines = open(path, errors="ignore")
    except OSError:
        return
    for line in lines:
        m = STAMP.search(line)
        if not m or calendar.timegm(time.strptime(m.group(1), "%Y-%m-%dT%H:%M:%S")) < (started or 0) - 5:
            continue
        try:
            r = json.loads(line)
        except ValueError:
            continue
        if not r.get("isSidechain"):
            yield r


def body_text(content):
    if isinstance(content, list):
        return "\n".join(x.get("text", "") for x in content if isinstance(x, dict))
    return str(content or "")


def cost(u):
    return (u.get("cache_read_input_tokens", 0) * READ + u.get("cache_creation_input_tokens", 0) * WRITE
            + u.get("input_tokens", 0) + u.get("output_tokens", 0) * OUTPUT)


# A transcript that has not grown is not read again. The session list needs every session's summary, which is small,
# so each is kept apart from the whole conversation; only the last PARSED_KEEP conversations are kept whole. Until
# 2026-09-23 one cache held both and was emptied past 200 entries: with 298 sessions every list read every transcript
# again (1.65 s a call, on the Now page every six seconds).
_parsed = collections.OrderedDict()  # (path, size, mtime, started) -> the session's turns, the last read last
_summaries = {}                      # the same key -> its summary alone
_cache = threading.Lock()            # the server answers requests in threads
PARSED_KEEP = int(os.environ.get("ORCH_DASHBOARD_KEEP", 40))
PARSES = 0                           # transcripts parsed since the start, for /api/version (the tests read it)


FACETS = ("read", "write", "input", "output", "requests", "reread")  # an hour bucket's values, in this order


def usage_facets(reqs):
    """A session's tokens by kind — read from cache, written to it, uncached input, output — in all and by the hour its
    requests were made in (UTC, the transcript's own), with its requests, and what each request read again of what its
    first one read (run-report's "base read again": the prefix a fork carries in every request); and what its first
    request wrote (a fork that missed its origin's entry writes its whole prefix)."""
    hours, first = {}, (reqs[0]["usage"] or {}).get("cache_read_input_tokens", 0) if reqs else 0
    for q in reqs:
        u = q["usage"] or {}
        try:
            h = calendar.timegm(time.strptime(q["at"], "%Y-%m-%dT%H:%M:%S")) // 3600 * 3600
        except ValueError:
            continue
        b = hours.setdefault(str(h), [0] * len(FACETS))
        read = u.get("cache_read_input_tokens", 0)
        for i, v in enumerate((read, u.get("cache_creation_input_tokens", 0), u.get("input_tokens", 0),
                               u.get("output_tokens", 0), 1, min(read, first))):
            b[i] += v
    total = [sum(b[i] for b in hours.values()) for i in range(len(FACETS))]
    return dict(read=total[0], write=total[1], input=total[2], reread=total[5], hours=hours,
                first_write=(reqs[0]["usage"] or {}).get("cache_creation_input_tokens", 0) if reqs else 0)


def turns_key(s):
    path = transcript_path(s.get("sid") or "")
    return (path, os.path.getsize(path), os.path.getmtime(path), s.get("started")) if path else None


def session_turns(s):
    """The session's own conversation, as turns: each request the model made (its usage, its thinking — kept, not
    shown by Claude Code — its text, its calls), each call with its command and what came back, what the harness told
    it beside a call (notes) and what it refused; and the messages it was sent (its first, resumes, mail)."""
    global PARSES
    key = turns_key(s)
    if not key:
        return None
    path = key[0]
    with _cache:
        if key in _parsed:
            _parsed.move_to_end(key)
            return _parsed[key]
    PARSES += 1
    items, requests, calls = [], {}, {}
    for r in own_records(path, s.get("started")):
        kind, m = r.get("type"), r.get("message") or {}
        ts = (r.get("timestamp") or "")[:19]
        if kind == "assistant":
            if m.get("model") == "<synthetic>":
                continue  # what Claude Code writes after a turn the harness ended: no request was made
            mid = m.get("id") or ts
            if mid not in requests:
                requests[mid] = dict(kind="request", at=ts, id=mid, n=len(requests) + 1, usage=m.get("usage") or {},
                                     thinking=0, text=[], calls=[])
                items.append(requests[mid])
            q = requests[mid]
            q["usage"] = m.get("usage") or q["usage"]
            q["last"] = ts  # its last block written: the model's answer complete, its calls made from here
            for b in m.get("content") or []:
                if not isinstance(b, dict):
                    continue
                if b.get("type") == "thinking":
                    q["thinking"] += 1
                elif b.get("type") == "text" and b.get("text", "").strip():
                    q["text"].append(b["text"])
                elif b.get("type") == "tool_use":
                    inp = b.get("input") or {}
                    c = dict(id=b.get("id"), tool=b.get("name"), command=inp.get("command") or json.dumps(inp)[:4000],
                             description=inp.get("description", ""), background=bool(inp.get("run_in_background")),
                             result=None, error=False, size=0, refused=None, stopped=None, notes=[])
                    calls[b.get("id")] = c
                    q["calls"].append(c)
        elif kind == "user":
            content = m.get("content")
            results = [b for b in content if isinstance(b, dict) and b.get("type") == "tool_result"] \
                if isinstance(content, list) else []
            for b in results:
                c = calls.get(b.get("tool_use_id"))
                if c is not None:
                    text = body_text(b.get("content"))
                    c.update(result=text[:CUT], cut=len(text) > CUT, size=len(text), error=bool(b.get("is_error")),
                             at_end=ts)
                    if text.lstrip().startswith("refused") and not c["refused"]:
                        c["refused"] = text.strip()[:600]
                    elif c["error"] and not FAILED.match(text.lstrip()):
                        # an error that is neither a command's exit nor the tool's own: the harness's guard stopped the
                        # call before it ran, and what came back is its word (work_meter: "Waiting is refused", "Not by
                        # a redirection into a file", "You are parked") — 96% of the errors of 09-19/23 were these
                        c["stopped"] = text.strip()[:600]
            if not results:
                text = body_text(content)
                if text.strip():
                    items.append(dict(kind="message", at=ts, text=text[:CUT], cut=len(text) > CUT))
        elif kind == "attachment":
            a = r.get("attachment") or {}
            c = calls.get(a.get("toolUseID"))
            if a.get("type") == "hook_additional_context":
                for note in a.get("content") or []:
                    if c is not None:
                        c["notes"].append(str(note))
                    else:
                        items.append(dict(kind="note", at=ts, text=str(note)))
            elif a.get("type") == "hook_success" and '"deny"' in str(a.get("stdout") or "") and c is not None:
                try:
                    out = json.loads(a["stdout"])["hookSpecificOutput"]
                    if out.get("permissionDecision") == "deny":
                        c["refused"] = (out.get("permissionDecisionReason") or "")[:2000]
                except (ValueError, KeyError, TypeError):
                    pass
    reqs = [x for x in items if x["kind"] == "request"]
    spent = timings(items, s.get("started"))
    shell = lambda c: c["command"] if c["tool"] == "Bash" else ""  # what role_evidence reads: a call's shell command
    for i, q in enumerate(reqs):
        q["ops"] = sum(role_evidence.call_ops(shell(c)) for c in q["calls"])
        before = reqs[i - 1]["calls"] if i else []
        q["joinable"] = bool(before) and role_evidence.joinable([shell(c) for c in before], before[0]["result"],
                                                                [shell(c) for c in q["calls"]])
    allcalls = [c for q in reqs for c in q["calls"]]
    changes = [c for c in allcalls if re.search(r"v2\.py change\b", c["command"] or "")]
    produced = []
    for c in changes:
        produced += re.findall(r"^=== (?:write|append|replace|replace-all) (\S+)", c["command"], re.M)
        produced += [f"THEORY_MAP.md row {t}" for t in re.findall(r"^=== row (\S+)", c["command"], re.M)]
        produced += [f"ROOT {t}" for t in re.findall(r"^=== root (\S+)", c["command"], re.M)]
    first_change = next((q["n"] for q in reqs if any(re.search(r"v2\.py change\b", c["command"] or "")
                                                       for c in q["calls"])), None)
    summary = dict(requests=len(reqs), calls=len(allcalls), refused=sum(1 for c in allcalls if c["refused"]),
                   stopped=sum(1 for c in allcalls if c["stopped"]),
                   failed=sum(1 for c in allcalls if c["error"] and not c["refused"] and not c["stopped"]),
                   notes=sum(len(c["notes"]) for c in allcalls), cost=round(sum(cost(q["usage"]) for q in reqs)),
                   output=sum((q["usage"] or {}).get("output_tokens", 0) for q in reqs),
                   context=max([sum((q["usage"] or {}).get(k, 0) for k in ("input_tokens", "cache_read_input_tokens",
                                                                           "cache_creation_input_tokens"))
                                for q in reqs] or [0]),
                   first_change=first_change, produced=list(dict.fromkeys(produced)),
                   batch=round(len(allcalls) / len(reqs), 2) if reqs else 0,
                   ops=round(sum(q["ops"] for q in reqs) / len(reqs), 2) if reqs else 0,
                   joinable=sum(1 for q in reqs if q["joinable"]),
                   first=items[0]["at"] if items else None, last=items[-1]["at"] if items else None,
                   last_call=call_line(allcalls[-1]) if allcalls else None,
                   last_call_at=next((q["last"] for q in reversed(reqs) if q["calls"]), None),
                   last_call_open=bool(allcalls) and allcalls[-1]["result"] is None, **spent)
    summary.update(usage_facets(reqs))
    out = dict(items=items, summary=summary)
    with _cache:
        _parsed[key] = out
        while len(_parsed) > PARSED_KEEP:
            _parsed.popitem(last=False)
        if len(_summaries) > 20_000:  # a growing transcript leaves its earlier keys behind
            _summaries.clear()
        _summaries[key] = summary
    return out


def call_line(c):
    """A call as one line: a shell command's first line, another tool by its name and what it was given."""
    first = next((x for x in (c["command"] or "").splitlines() if x.strip()), "")
    return (first if c["tool"] == "Bash" else f"{c['tool']} {c['description'] or first}")[:240]


def timings(items, started):
    """Where a session's time went, from its transcript's own times: each request's model time (from what it answered
    being ready — its first message, the last result of the calls before, a message — to its last block written), its
    calls' time (from there to the last of their results), and the idle time before a message that came after the
    calls ended (a parked session resumed, mail). Each item gets its own; the sums are returned."""
    prev, total = started, dict(model_s=0, tools_s=0, idle_s=0)
    for it in items:
        if it["kind"] == "message":
            t = utc_epoch(it["at"])
            if t is None:
                continue
            if prev is not None and t > prev and it is not items[0]:
                it["idle_s"] = round(t - prev)
                total["idle_s"] += it["idle_s"]
            prev = t
        elif it["kind"] == "request":
            last = utc_epoch(it.get("last") or it["at"])
            if last is None:
                continue
            it["model_s"] = round(max(0, last - prev)) if prev is not None else 0
            ends = [e for e in (utc_epoch(c.get("at_end")) for c in it["calls"]) if e is not None]
            it["tools_s"] = round(max(0, max(ends) - last)) if ends else 0
            it["open"] = any(c["result"] is None for c in it["calls"])
            total["model_s"] += it["model_s"]
            total["tools_s"] += it["tools_s"]
            prev = max(ends) if ends else last
    return total


def warm_summaries():
    """Every session's summary read once at the start, in the background: the first session list after a start (and
    the server starts again at every change of its source) would read every transcript (1.7 s on 09-23's 298)."""
    try:
        for n, s in all_sessions(archive=True).items():  # the archived too: the costs read them
            session_summary(n, s)
    except Exception:  # noqa: BLE001 — only a head start: a list asked for reads what is missing itself
        pass


def session_summary(name, s, hours=False):
    """A session's record and the summary of its turns; its hour buckets only when asked (the costs read them)."""
    key = turns_key(s) if s.get("sid") else None
    with _cache:
        summary = _summaries.get(key) if key else None
    if key and summary is None:
        summary = (session_turns(s) or {}).get("summary")
    base = {k: s.get(k) for k in ("name", "role", "state", "task", "reviews", "origin", "model", "effort", "tree",
                                  "started", "ended", "sealed", "released", "archived", "layer_of", "churn_of")}
    return dict(base, **{k: v for k, v in (summary or {}).items() if hours or k != "hours"})


def task_record(tid, st):
    task = v2.read_task(tid) or {}
    t = st["tasks"].get(tid) or {}
    return dict(id=tid, subject=task.get("subject", ""), status=task.get("status"), stage=t.get("stage"),
                kind=t.get("kind") or ((task.get("metadata") or {}).get("kind")), session=t.get("session"),
                rejections=t.get("rejections", 0), checks_failed=t.get("checks_failed", 0),
                blocked_by=task.get("blockedBy") or [], parked=(t.get("parked") or {}).get("for"),
                queued=tid in (st.get("queue") or []))


def read_build(tid, name, tail=None):
    try:
        text = open(os.path.join(v2.BUILD, tid, name), errors="ignore").read()
    except OSError:
        return None
    if tail:
        return "\n".join(text.splitlines()[-tail:])
    return text[:200_000]


def overview():
    st = v2.peek()
    live = {n: s for n, s in st["sessions"].items() if s.get("state") in v2.LIVE and not s.get("released")}
    load = v2.softly("the machine's runs", v2.isabelle_load, default={})
    mem_used, mem_total = v2.memory_now()
    try:
        loadavg = open("/proc/loadavg").read().split()[:3]
    except OSError:
        loadavg = []
    claim = v2.exclusive_claim()
    stages = collections.Counter((t.get("stage") or "queued") for t in st["tasks"].values())
    bases = {}
    for who in v2.BASES:
        parts = {}
        for part in ("base", "layer", "delta"):
            with_rec = None
            try:
                with_rec = json.load(open(os.path.join(v2.STATE, f"{who}-{part}.json")))
            except (OSError, ValueError):
                pass
            if with_rec:
                parts[part] = {k: with_rec.get(k) for k in ("sessionId", "name", "context", "sealed", "digest")}
        bases[who] = dict(parts, forks=os.path.basename(v2.base_file(who)), deltas=v2.deltas_on(who))
    layers = {}
    for role in sorted(v2.LAYERABLE):
        rec = v2.role_layer_record(role, st)
        if rec or role in v2.role_layers():
            layers[role] = dict(rec, on=role in v2.role_layers(), forks=v2.role_churn_of(role) or v2.role_layer_of(role))
    pid = (state_file("warm.pid") or "").strip()
    out = dict(
        now=time.strftime("%Y-%m-%dT%H:%M:%S"), active=st.get("active"),
        stopped=(state_file("stopped") or "").strip() or None,
        holds={k: (state_file(v) or "").strip() or (True if os.path.exists(os.path.join(v2.STATE, v)) else None)
               for k, v in HOLDS.items()},
        daemon=bool(pid and os.path.exists(f"/proc/{pid}")),
        switches={k: {"on": os.path.exists(os.path.join(v2.STATE, k)), "value": (state_file(k) or "").strip()}
                  for k in SWITCHES},
        measure_seconds=v2.measure_max(),
        machine=dict(runs=load, memory_used=mem_used, memory_total=mem_total, loadavg=loadavg,
                     cpus=os.cpu_count(), claim=claim, pending=v2.pending_claim()),
        live=[session_summary(n, s) for n, s in sorted(live.items())],
        kb=st.get("kb"), queue=[task_record(t, st) for t in st.get("queue") or []],
        stages=dict(stages), events=st.get("events") or [], asks={k: q for k, q in (st.get("asks") or {}).items()
                                                                   if q.get("state") != "answered"},
        occupancy=v2.softly("the last hour's occupancy", v2.occupancy_text, default=""),
        bases=bases, role_layers=layers)
    return dict(out, attention=attention(out, graph(6.0), log_tail(800)), noise=LOG_NOISE.pattern, ceiling=v2.CEILING)


def task_history(tid, n=400):
    """The log's lines about a task, oldest first: where it was made, its tree, its sessions (fix-279, review-279.1),
    its checks, parks, probes, measurements, its train and its landing — each as the harness said it then."""
    about = re.compile(r"(?:\btasks? (?:#?\d+(?:, | and ))*#?|#|\b[a-z]+-|\bmade (?:\d+(?:, | and ))*)"
                       + re.escape(tid) + r"(?!\d)")
    return [x for x in log_tail(1_000_000) if about.search(x)][-n:]


# the log's lines that say how the harness keeps itself, not what the run did: left out of the Now page's activity and
# the report's events, dimmed in the log (the page reads the pattern from /api/overview)
LOG_NOISE = re.compile(r"^(cache of|told task|resumed |archived |tidied |pruned |plan-\d+ has handled|the working tree of task|"
                       r"task \d+ has its own working tree|cleared the|ping |the run task|the base follows main|"
                       r"check of task \d+: passed \(alone\)|the (high|xhigh|max) (delta|layer) is)|, parked, was told a background run ended")


def local_clock(epoch):
    return time.strftime("%b %d %H:%M", time.localtime(epoch)) if epoch else "—"


def span_text(seconds):
    s = max(0, int(seconds or 0))
    return f"{s}s" if s < 60 else f"{s // 60}m" if s < 3600 else f"{s // 3600}h {s % 3600 // 60:02d}m"


def attention(o, g, log):
    """What needs the owner, read from what the harness keeps: [(tone, text, where, when)] — tone bad, warn or info;
    where, the console's view it is seen in (view or view/id); when, an epoch or None. The Now page's list and the
    report's first findings."""
    out, now = [], time.time()
    going_on = o.get("active") and not o.get("stopped")
    if going_on and not o.get("daemon"):
        out.append(("bad", "The daemon is not running while the run is active: nothing is dispatched or kept warm.", "control", None))
    if o.get("stopped"):
        out.append(("info", f"The run is stopped (since {local_clock(local_epoch(o['stopped']))}): nothing starts until "
                            "it is started again.", "control", None))
    if o["holds"].get("graph"):
        out.append(("warn", "The graph is held: no task starts until it is released.", "control", None))
    if o["holds"].get("launch"):
        out.append(("warn", "Every launch is held: no session starts.", "control", None))
    seen = set()
    for line in reversed([x for x in log if "ATTENTION" in x]):
        at = local_epoch(line[:19])
        if not at or now - at > 3 * 3600:
            continue
        text = line[20:].replace("ATTENTION ", "", 1)
        key = re.sub(r"\d+", "N", text)[:90]
        if key in seen:
            continue
        seen.add(key)
        if len(seen) > 6:
            break
        out.append(("bad", text, "log", at))
    for qid, q in (o.get("asks") or {}).items():
        to_owner = "owner" in (q.get("to") or "")
        first = next((x for x in str(q.get("text") or "").splitlines() if x.strip()), "")
        out.append(("warn" if to_owner else "info", f"{q.get('from')} asks {'you' if to_owner else 'the ' + (q.get('to') or 'planner')} "
                    f"({qid}): {first[:170]}", f"sessions/{q.get('from')}" if q.get("from") else None, None))
    for nd in (x for x in g["nodes"] if x["group"] == "planner"):
        out.append(("info", f"Task #{nd['id']} " + ("is with the planner" if nd["status"] == "with the planner" else "has " + nd["status"])
                    + f": {nd['subject'][:150]}", f"tasks/{nd['id']}", None))
    if going_on:  # a session silent a long time, a task parked long
        for s in o.get("live") or []:
            last = utc_epoch(s.get("last"))
            if last and now - last > 1200:
                call = s.get("last_call")
                out.append(("warn", f"{s['name']} has said nothing for {span_text(now - last)}" + (
                    f" — {'still running' if s.get('last_call_open') else 'its last call'}: {call[:110]}" if call else ""),
                    f"sessions/{s['name']}", None))
        for nd in g["nodes"]:
            if nd.get("parked_since") and now - nd["parked_since"] > 2700:
                out.append(("warn", f"Task #{nd['id']} has been {nd['status']} for {span_text(now - nd['parked_since'])}: "
                                    f"{nd['subject'][:110]}", f"tasks/{nd['id']}", None))
    if (o.get("machine") or {}).get("pending"):
        out.append(("info", f"Task {o['machine']['pending'].get('task')} waits for the whole machine to measure: no new run "
                            "starts meanwhile.", "machine", None))
    if o.get("events"):
        out.append(("info", f"{len(o['events'])} event(s) wait for the planner's next pass.", None, None))
    return out


def log_tail(n=300, grep=None):
    try:
        lines = open(os.path.join(v2.STATE, "v2.log"), errors="ignore").read().splitlines()
    except OSError:
        return []
    if grep:
        lines = [x for x in lines if grep.lower() in x.lower()]
    return lines[-n:]


def state_json(name, default=None):
    try:
        return json.load(open(os.path.join(v2.STATE, name)))
    except (OSError, ValueError):
        return default


def alive(pidfile):
    pid = (state_file(pidfile) or "").strip().split()[:1]
    return bool(pid) and pid[0].isdigit() and os.path.exists(f"/proc/{pid[0]}")


def recent_logs(folder, n=20):
    """The newest logs of a folder of the harness's runs (.build/tasks/batches, .build/trains): name, size, when, and
    whether it grew in the last minute (a run going)."""
    try:
        names = [f for f in os.listdir(folder) if f.endswith(".log")]
    except OSError:
        return []
    rows = []
    for f in sorted(names, key=lambda f: -os.path.getmtime(os.path.join(folder, f)))[:n]:
        p = os.path.join(folder, f)
        rows.append(dict(name=f, path=os.path.relpath(p, v2.PROJECT), size=os.path.getsize(p), at=os.path.getmtime(p),
                         growing=time.time() - os.path.getmtime(p) < 60))
    return rows


def checks():
    """The check batches and landing trains as the harness keeps them — the check queue (waiting, being checked,
    decided), the trees that passed, the batch logs; the landing queue (waiting, landing, landed, failed), the train
    logs, the kept builds (C10) — and the log's lines about them."""
    import train
    cq, lq = state_json("check-queue.json", {}) or {}, state_json("landing-queue.json", {}) or {}
    batching, landing = alive("batcher.pid"), alive("lander.pid")
    def rows(q, running, going_word):
        out = []
        for tid, e in sorted(q.items(), key=lambda x: -(x[1].get("queued") or 0)):
            state = e.get("what") or (going_word if running else "waiting")
            out.append(dict(task=tid, state=state, decided=bool(e.get("decided")), queued=e.get("queued"),
                            decided_at=e.get("decided"), code=e.get("code"), log=e.get("log") or e.get("fail_log"),
                            ref=e.get("ref"), text=e.get("text"), kind=e.get("kind"), head=(e.get("head") or "")[:10]))
        return out
    results = state_json("check-results.json", {}) or {}
    passed = sorted(({"tree": k[:10], **v} for k, v in results.items()), key=lambda x: -(x.get("at") or 0))[:30]
    kept = state_json("kept-builds.json", {}) or {}
    return dict(
        batcher=batching, lander=landing,
        batches=rows(cq, batching, "in a batch, or waiting for the next"), batch_logs=recent_logs(train.BATCH_LOGS),
        passed=passed, trains=rows(lq, landing, "in a train, or waiting for the next"), train_logs=recent_logs(train.LOGS),
        kept=[{"key": k[:12], **(v if isinstance(v, dict) else {"value": v})} for k, v in list(kept.items())[-20:]],
        log=[x for x in log_tail(4000) if re.search(r"\b(batch|train|landing|lands|checked|check of)\b", x)][-300:])


def machine():
    """The machine as the watchdog sees it (state/isabelle-processes.json, written every pass): each Isabelle run —
    heavy or a probe, its command, its session's or a finalizer's, its memory — against the limits; who holds the
    machine or waits to; the probes queued; the measurements sharing it; memory and load; the last hour's occupancy."""
    snap = state_json("isabelle-processes.json", {}) or {}
    runs = {}
    for p in snap.get("processes") or []:
        r = runs.setdefault(p.get("run"), dict(run=p.get("run"), kind=p.get("kind"), command=p.get("run_command"),
                                               rss_mb=0, processes=0, session=False))
        r["rss_mb"] += p.get("rss_mb") or 0
        r["processes"] += 1
    for root in snap.get("roots") or []:
        if root.get("pid") in runs:
            runs[root["pid"]].update(session=root.get("session"), started=root.get("started"))
    shared = []
    try:
        for f in os.listdir(os.path.join(v2.STATE, "measure-shared")):
            m = state_json(os.path.join("measure-shared", f), {})
            shared.append({k: m.get(k) for k in ("task", "why", "session", "at", "call_at")})
    except OSError:
        pass
    probes = state_json("probe-queue.json", {}) or {}
    mem_used, mem_total = v2.memory_now()
    try:
        occupancy = open(os.path.join(v2.STATE, v2.OCCUPANCY), errors="ignore").read().splitlines()[-60:]
    except OSError:
        occupancy = []
    return dict(
        snapshot_at=snap.get("at"), limits=dict(heavy=v2.ISABELLE_MAX, probes=v2.PROBE_MAX, memory_floor_gb=v2.MEM_MARGIN_GB),
        load=v2.softly("the machine's runs", v2.isabelle_load, default={}), runs=sorted(runs.values(), key=lambda r: str(r["kind"])),
        claim=v2.exclusive_claim(), pending=v2.pending_claim(), shared=shared,
        probe_queue=[{"task": t, **{k: e.get(k) for k in ("queued", "decided", "what", "session")}} for t, e in probes.items()],
        memory_used=mem_used, memory_total=mem_total, memory_available_gb=v2.memory_available_gb(),
        loadavg=(open("/proc/loadavg").read().split()[:3] if os.path.exists("/proc/loadavg") else []),
        cpus=os.cpu_count(), measure_seconds=v2.measure_max(), occupancy=occupancy)


def graph(done_hours=6.0):
    """The task graph as its dependencies make it: the open tasks, and those done within `done_hours`, each with where
    it stands — waiting on which blockers, ready, running (its session), parked (for what), in the check queue or a
    check batch, reviewed, fixed, committing, in the landing queue or a train, landed, with the planner."""
    st = v2.peek()
    tasks = {t["id"]: t for t in v2.all_tasks()}
    cq, lq = state_json("check-queue.json", {}) or {}, state_json("landing-queue.json", {}) or {}
    batching, landing = alive("batcher.pid"), alive("lander.pid")
    now = time.time()
    nodes = {}
    for tid, task in tasks.items():
        t = st["tasks"].get(tid) or {}
        done = task.get("status") == "completed" or t.get("stage") in ("done", "deleted")
        path = os.path.join(v2.TASKS, v2.LIST, f"{tid}.json")
        when = t.get("landed_at") or (lq.get(tid) or {}).get("decided") or (
            os.path.getmtime(path) if os.path.exists(path) else 0)
        if done and now - (when or 0) > done_hours * 3600:
            continue
        nodes[tid] = dict(id=tid, subject=task.get("subject", ""), kind=t.get("kind") or (task.get("metadata") or {}).get("kind"),
                          stage=t.get("stage"), done=done, session=t.get("session"), rejections=t.get("rejections", 0),
                          blocked_by=[b for b in task.get("blockedBy") or []], queued=tid in (st.get("queue") or []))
    for tid, n in nodes.items():
        t, stage = st["tasks"].get(tid) or {}, n["stage"]
        c, l = cq.get(tid) or {}, lq.get(tid) or {}
        open_blockers = [b for b in n["blocked_by"] if (tasks.get(b) or {}).get("status") != "completed"]
        if n["done"]:
            status, group = ("landed " + l["ref"] if l.get("what") == "landed" and l.get("ref") else "done"), "done"
        elif l and not l.get("decided"):
            status, group = ("landing in a train" if landing else "waiting for a landing train"), "train"
        elif c and not c.get("decided") and stage in ("checking", "parked"):
            status, group = ("in a check batch, or next" if batching else "waiting for a check batch"), "check"
        elif stage == "checking":
            status, group = "its check running", "check"
        elif stage == "reviewing":
            status, group = "being reviewed" + (f" ({t.get('reviewing')})" if t.get("reviewing") else ""), "review"
        elif stage == "fixing":
            status, group = "being fixed" + (f" ({t.get('fixing')})" if t.get("fixing") else ""), "fix"
        elif stage == "committing":
            status, group = "finalizing: committing and landing", "train"
        elif stage == "running":
            status, group = f"running ({n['session']})" if n["session"] else "running", "running"
        elif stage == "parked":
            status, group = f"parked for {(t.get('parked') or {}).get('for', '?')}", "parked"
        elif stage in ("planner", "unformed"):
            status, group = ("with the planner" if stage == "planner" else "its brief not in form"), "planner"
        elif open_blockers:
            status, group = "waiting on " + ", ".join("#" + b for b in open_blockers[:4]), "waiting"
        else:
            status, group = ("ready" if n["queued"] else "not queued"), "ready" if n["queued"] else "idle"
        n.update(status=status, group=group, open_blockers=open_blockers,
                 check=c.get("what") if c.get("decided") else None,
                 parked_since=(t.get("parked") or {}).get("since") if stage == "parked" else None)
    edges = [(b, tid) for tid, n in nodes.items() for b in n["blocked_by"] if b in nodes]
    holds, held = held_up(nodes, edges)
    for tid, n in nodes.items():
        n["holds"] = holds.get(tid, 0)
    return dict(nodes=list(nodes.values()), edges=edges, queue=st.get("queue") or [], batcher=batching, lander=landing,
                held_up=held)


def held_up(nodes, edges):
    """What each task holds up — the open tasks that wait on it through any chain of waits — and the waiting tasks
    grouped by what holds them: the tasks at the heads of their chains of waits, which do not wait themselves (being
    worked on, parked, with the planner, not queued — or not among the open tasks, when what waits on it never
    starts), most held first. The console's Now and graph and the report read these."""
    kids = collections.defaultdict(list)
    for b, t in edges:
        kids[b].append(t)
    holds = {}
    for tid in nodes:
        seen, todo = set(), [tid]
        while todo:
            for t in kids.get(todo.pop(), ()):
                if t not in seen and t in nodes and not nodes[t]["done"]:
                    seen.add(t)
                    todo.append(t)
        holds[tid] = len(seen)
    memo = {}

    def heads(tid, path=()):
        if tid in memo:
            return memo[tid]
        n = nodes.get(tid)
        if not n or n["group"] != "waiting":
            return {tid}
        if tid in path:  # a cycle: none of it can start, and it is said where it waits
            return set()
        out = set()
        for b in n["open_blockers"]:
            out |= heads(b, path + (tid,))
        memo[tid] = out
        return out
    groups = collections.defaultdict(list)
    for tid, n in nodes.items():
        if n["group"] == "waiting":
            for r in heads(tid):
                groups[r].append(tid)
    num = lambda x: int(x) if str(x).isdigit() else 0
    held = []
    for r, ws in groups.items():
        direct = {w for w in ws if r in nodes[w]["open_blockers"]}
        root = nodes.get(r) or {}
        held.append(dict(root=r, waiting=sorted(ws, key=lambda w: (w not in direct, num(w))), direct=sorted(direct, key=num),
                         status=root.get("status") or "not among the open tasks: what waits on it never starts",
                         group=root.get("group") or "idle", subject=root.get("subject", ""), kind=root.get("kind"),
                         parked_since=root.get("parked_since")))
    held.sort(key=lambda h: (-len(h["waiting"]), num(h["root"])))
    return holds, held


# ---------------------------------------------------------------- the bases and their layers

CACHE_LIFE = 3600  # promptCacheTtl 1h: an entry lives an hour past its last read (v2.WARM_MAX keeps five minutes' margin)
WARM_IDLE_MAX = int(os.environ.get("ORCH_WARM_IDLE_MAX", 43200))  # warm_daemon.sh's: a base unused this long goes cold
STALE_EVERY = int(os.environ.get("ORCH_DASHBOARD_STALE_EVERY", 60))  # how often the bases' staleness is measured
VERDICT = re.compile(r"\b(OK|MISS)\b.*?cache_read=(\d+) cache_write=(\d+)")
STAMPED = re.compile(r"^(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d) (.*)$")


def mark_age(rel):
    """Seconds since state/REL was touched, or None: the harness's marks (a hit, a use, a look, a seal) are times."""
    try:
        return time.time() - os.path.getmtime(os.path.join(v2.STATE, rel))
    except OSError:
        return None


def misses(rel):
    try:  # a base's miss mark gains a line a miss; a session's is there or not
        return len(open(os.path.join(v2.STATE, rel)).read().split()) or 1
    except OSError:
        return 0


def local_epoch(stamp):
    try:
        return time.mktime(time.strptime(stamp, "%Y-%m-%dT%H:%M:%S"))
    except (ValueError, TypeError):
        return None


def verdict(text):
    """What a fork check said (session_fork_check.py) — a keep-warm ping's, or a load's first request: whether it read
    its origin from cache, what it read and wrote, and what that cost — or None."""
    m = VERDICT.search(text)
    if not m:
        return None
    read, write = int(m.group(2)), int(m.group(3))
    return dict(ok=m.group(1) == "OK", read=read, write=write, cost=round(read * READ + write * WRITE))


def warm_log():
    """[(epoch, what, verdict)] of warm.log's verdicts: base.sh's pings (`warm WHO[ stable|layer]: OK|MISS …`) and the
    first requests of its loads (`layer WHO: …`, `delta WHO: …`), each as its line names it."""
    out = []
    try:
        lines = open(os.path.join(v2.STATE, "warm.log"), errors="ignore").read().splitlines()
    except OSError:
        return out
    for line in lines:
        m = STAMPED.match(line)
        what = m and re.match(r"((?:warm|layer|delta|reasoning|direction|catalogue|working) \w+(?: [a-z][a-z0-9_-]*)?):", m.group(2))
        said = what and verdict(m.group(2))
        if said:
            out.append((local_epoch(m.group(1)), what.group(1), said))
    return out


def session_pings():
    """{session: [verdict with its time]} of v2.ping's lines in v2.log (`ping NAME: OK|MISS …`)."""
    out = collections.defaultdict(list)
    for line in log_tail(100_000, grep="ping "):
        m = STAMPED.match(line)
        p = m and re.match(r"ping (\S+): (.*)", m.group(2))
        said = p and verdict(p.group(2))
        if said:
            out[p.group(1)].append(dict(said, at=local_epoch(m.group(1))))
    return out


def daemon_up():
    """Whether warm_daemon.sh runs: its heartbeat (warm.beat, every five seconds), which a sandbox that cannot see its
    process still reads, or its process."""
    beat = mark_age("warm.beat")
    return (beat is not None and beat < 30) or alive("warm.pid")


def entry(hit, miss, rule, last=None):
    """A cache entry: when it was last read (its mark, touched by every read — a fork's request, a ping, a load), when
    it expires (an hour after), whether the harness counts it warm (v2.WARM_MAX), its misses, its last ping, and when it
    is pinged next and why (`rule`, from the read's age)."""
    age = mark_age(hit)
    return dict(read_age=age, expires_in=None if age is None else CACHE_LIFE - age,
                warm=age is not None and age < v2.WARM_MAX, misses=misses(miss), last_ping=last, **rule(age))


def base_rules(who, daemon):
    """The ping rules of a base's entries, as warm_daemon.sh and base.sh keep them: (the rule of what its roles fork —
    `warm WHO`, a read older than WARM_EVERY while a role forks it, used within WARM_IDLE_MAX, never after a miss —, the
    rule of an entry under it — `warm WHO stable|layer --if-due`: only while warm, never after a miss)."""
    import watchdog
    every = watchdog.WARM_EVERY

    def forked(age):
        if not daemon:
            return dict(next_ping=None, why="the daemon is not running: nothing pings")
        if misses(f"{who}-base.miss"):
            return dict(next_ping=None, why="a ping missed: none is made until a load writes the entry again")
        used = mark_age(f"{who}-base.used")
        if used is None or used > WARM_IDLE_MAX:
            return dict(next_ping=None, why=f"unused for {WARM_IDLE_MAX // 3600} h: left to go cold")
        if not v2.shared_part_forked(who):
            return dict(next_ping=None, why="no role forks it: each forks its own churn or layer")
        return dict(next_ping=max(0, every - (age or every)),
                    why=f"pinged {every // 60} min after its last read while a role forks it")

    def under(part, reloaded_by):
        def rule(age):
            if not daemon:
                return dict(next_ping=None, why="the daemon is not running: nothing pings")
            if misses(f"{who}-{part}.miss"):
                return dict(next_ping=None, why=f"a ping missed: {reloaded_by} writes it again")
            if age is None or age >= v2.WARM_MAX:
                return dict(next_ping=None, why=f"cold, so not pinged (a ping would write it for nothing): "
                                                f"{reloaded_by} writes it again")
            return dict(next_ping=max(0, every - age),
                        why=f"its own entry, pinged {every // 60} min after its last read while warm")
        return rule
    return forked, under


def base_view(who,daemon,pings):
    """The published chain, each part's actual parent, own context, purpose and cache entry."""
    import watchdog
    stable,layer,delta=watchdog._record(who,'base'),v2.layer_record(who),v2.delta_record(who)
    if not stable:return None
    chain=(layer or {}).get('parts')
    nodes=[('base' if p['part']=='stable' else p['part'],p) for p in chain] if chain else [('base',stable),('layer',layer)]
    if delta and delta.get('sessionId'):nodes.append(('delta',delta))  # its texts alone are no session (base_stack.cut)
    file=v2.base_file(who)
    forked_part='delta' if file.endswith('-delta.json') else nodes[-1][0] if layer else 'base'
    fork_rule,under=base_rules(who,daemon)
    last=lambda tag:next((dict(v,at=at) for at,what,v in reversed(pings) if what==tag),None)
    parts=[];below=0
    for part,r in nodes:
        if not r:continue
        ctx=int(r.get('context') or 0)
        mark='stable' if part=='base' else part
        if part==forked_part:
            e=entry(f'{who}-base.hit',f'{who}-base.miss',fork_rule,last(f'warm {who}'))
        else:
            own=f"entry-hits/{r.get('sessionId')}"
            hit=own if os.path.exists(os.path.join(v2.STATE,own)) else f'{who}-{mark}.hit'
            miss=own+'.miss' if hit==own else f'{who}-{mark}.miss'
            e=entry(hit,miss,under(mark,'the next dependent build'),last(f'warm {who} {mark}'))
        parts.append(dict(part=part,name=r.get('name'),sid=(r.get('sessionId') or '')[:8],sealed=r.get('sealed'),
                          context=ctx,own=max(0,ctx-below),forked=part==forked_part,entry=e,
                          kind=r.get('kind','material'),purposes=r.get('purposes',[]),parent=r.get('parent'),
                          drift=((_stale.get(who) or {}).get('parts') or {}).get('stable' if part=='base' else part),
                          tokens=r.get('tokens'),layer_tokens=r.get('layer_tokens'),stable_tokens=r.get('stable_tokens'),head=r.get('head')))
        below=ctx
    return dict(who=who,forks=forked_part,deltas=v2.deltas_on(who),parts=parts,
                orphan_delta=bool(watchdog._record(who,'delta') and not delta and v2.deltas_on(who)),
                building=os.path.exists(os.path.join(v2.STATE,f'{who}-layer.building')),
                layer_looked=mark_age(f'{who}-layer.looked'),delta_looked=mark_age(f'{who}-delta.looked'),staleness=_stale.get(who))


def held_view(name, s, st, daemon, pings):
    """A session the watchdog holds warm (watchdog.held): why, its entry and its pings — pinged when its last read is
    v2.PING_AGE old, while the run is going (the watchdog does nothing while it is stopped)."""
    import watchdog
    why = watchdog.held(st, name, s)
    going = daemon and st.get("active") and not os.path.exists(os.path.join(v2.STATE, "stopped"))

    def rule(age):
        if not why:
            return dict(next_ping=None, why="not held: let go at the watchdog's next pass")
        if not going:
            return dict(next_ping=None, why="the run is stopped: the watchdog pings nothing")
        if v2.ping_missed(name):
            return dict(next_ping=None, why="a ping missed: none until the session itself writes its entry")
        return dict(next_ping=max(0, v2.PING_AGE - (age or v2.PING_AGE)), why=why)
    got = pings.get(name) or []
    e = entry(os.path.join("hits", name), os.path.join("hits", name + ".miss"), rule, got[-1] if got else None)
    return dict(name=name, role=s.get("role"), state=s.get("state"), task=s.get("task"), held=why,
                context=s.get("context") or session_summary(name, s).get("context"), entry=e, pings=len(got), ping_cost=sum(p["cost"] for p in got),
                build_cost=s.get("build_cost"), ping_estimate=s.get("ping_cost"),
                worth=watchdog.worth_holding(s) if s.get("role") in v2.LAYER_ROLES else None)


def role_view(role, st, sessions, daemon, pings):
    """A role's own layers — its reasoning layer over the medium layer and its churn over that — as the harness keeps
    them, with what the role's sessions fork now and the churn's staleness against the shared delta (role_churn_care's
    rule: what forks behind it have cost, at STALE_READ a token moved, against its build)."""
    import watchdog
    rec = v2.role_layer_record(role, st)
    who = v2.ROLES[role]["origin"]
    medium_name, _ = v2.medium_record(who)
    base = v2.base_part(medium_name) or who  # the base standing for the role's (FALLBACK while it is not built)
    medium = v2.layer_record(base) if ":" in (medium_name or "") else watchdog._record(base, "base")
    layer_s = sessions.get(rec.get("name") or "") or {}
    under=layer_s.get('origin_context')
    if under is None:
        candidates=[medium,v2.delta_record(base)] + (v2.layer_record(base) or {}).get('parts',[])
        under=next((p.get('context') for p in candidates if p and p.get('sessionId')==layer_s.get('origin_sid')),None)
    churn_s = sessions.get(rec.get("churn") or "") or {}
    delta = v2.delta_record(base) if v2.deltas_on(base) else None
    # what holds the chain's beginning under the next churn: the churn, or a judging role's layer before it has one
    holder = churn_s or (layer_s if role in v2.HOT_BEFORE_ROLE else {})
    moved = abs(int((delta or {}).get("tokens") or 0) + (v2.delta_uncut(base) if delta else 0)
                - int(holder.get("delta_size") or 0)) or v2.DELTA_MIN_TOKENS
    owed = int(rec.get("behind_forks") or 0) * moved * v2.STALE_READ
    forks = v2.role_churn_of(role) or v2.role_layer_of(role)
    return dict(role=role, base=base, on=role in v2.role_layers(),
                placement='above changes' if role in v2.HOT_BEFORE_ROLE else 'below changes',
                origin=layer_s.get('origin'),origin_sid=layer_s.get('origin_sid'),origin_context=under,
                forks=forks or os.path.basename(v2.base_file(base))[:-5],
                layer=held_view(rec["name"], layer_s, st, daemon, pings) if layer_s else None,
                layer_own=max(0, int(layer_s.get("context") or 0) - under) if layer_s.get("context") and under is not None else None,
                built=rec.get("built"), builds=rec.get("builds"), building=rec.get("building"),
                churn=held_view(rec["churn"], churn_s, st, daemon, pings) if churn_s else None,
                churn_own=churn_s.get("delta_tokens"), churn_building=rec.get("churn_building"),
                churn_current=bool(delta and delta.get("digest") in (
                    rec.get("churn_digest") or None, layer_s.get("digest") if role in v2.HOT_BEFORE_ROLE else None)),
                behind_forks=rec.get("behind_forks") or 0, owed=owed,
                churn_build=churn_s.get("build_cost") or v2.CHURN_BUILD_GUESS)


_stale = {}  # base -> what measure_bases found, and when


def measure_bases():
    """Each base's staleness, measured as the watchdog measures it: the share of the medium layer's tokens whose held
    text has moved since it loaded (manifest.py stale-share: a proof changed under statements held unchanged moves
    nothing, an index moves by the words that changed — the refresh rule of a base without a delta), what a delta built
    now would hold (delta-share: of the layer, of the stable reference), what is pending since the delta's last message
    against what a message holding it costs (watchdog.pending_paid), what the delta has cost the forks that carried it against what a
    refresh costs (carried, refresh_cost — the refresh rule under a delta), and what a fork is told is stale."""
    import watchdog
    for who in v2.BASES:
        if not watchdog._record(who, "base"):
            continue
        m, delta = dict(at=time.time()), v2.delta_record(who)
        try:
            m["layer_share"] = float(watchdog.manifest_says("stale-share", who).strip() or 0)
        except (ValueError, OSError, subprocess.SubprocessError):
            pass
        try:
            share, stable, total = watchdog.manifest_says("delta-share", who).split()
            m["delta_now"] = dict(share=float(share), stable=int(stable), tokens=int(total))
        except (ValueError, OSError, subprocess.SubprocessError):
            pass
        with contextlib.suppress(Exception):  # the delta's next message and its consolidation, by the watchdog's rules
            m["pending"] = v2.delta_pending(who)
            m["pending_owed"], m["pending_cost"] = watchdog.pending_paid(who, delta, m["pending"]) if m["pending"] \
                else (0.0, 0.0)
            m["chain"] = len(v2.chain_of(delta))
            m["session_len"] = v2.session_len(delta)
            m["waste_owed"], m["waste_cost"] = watchdog.stack_waste(who, delta) if delta else (0.0, 0.0)
        with contextlib.suppress(Exception):
            m["told_layer"] = watchdog.manifest_says("changed", who).strip()
            if delta:
                m["told_delta"] = watchdog.manifest_says("changed", who, "--since-layer", delta["sessionId"]).strip()
        with contextlib.suppress(Exception):
            m["carried"], m["refresh_cost"] = watchdog.carried(who), watchdog.refresh_cost(who)
        with contextlib.suppress(Exception):  # each part on its own schedule: the lowest whose account has paid
            m["refresh_plan"] = watchdog.refresh_plan(who) if (v2.layer_record(who) or {}).get("parts") else None
            m["carried_parts"] = watchdog.carried_parts(who) if m["refresh_plan"] is not None or \
                (v2.layer_record(who) or {}).get("parts") else None
        with contextlib.suppress(Exception):  # whether the stable base loaded what the list's stable part names now
            m["stable_listed"] = watchdog.manifest_says("stable-listed", who).strip()
        try:  # the stable part drifts too, more slowly: its moved share, and what it holds that the list no longer names
            share, moved, total, unlisted = watchdog.manifest_says("stable-share", who).split()
            m["stable"] = dict(share=float(share), moved=int(moved), tokens=int(total), unlisted=int(unlisted))
        except (ValueError, OSError, subprocess.SubprocessError):
            pass
        if (v2.layer_record(who) or {}).get('parts'):
            import base_stack
            m['parts']=base_stack.drift(who)
            m['required']=base_stack.refresh_reason(who)
        _stale[who] = m


_projected = {}  # base -> what a build from scratch would hold now (select_base_load.projection), and when
_role_messages = {}  # role -> the tokens of the message its layer would be built from now (its evidence and protocol)
PROJECT_EVERY = int(os.environ.get("ORCH_DASHBOARD_PROJECT_EVERY", 600))  # sessions change slowly; a projection reads
# the frontier's window of transcripts (about 5 s a base)


def project_bases():
    """What each base would be built as from scratch now — its stable part as the list writes it, its layer with the
    frontier chosen again (select_base_load.projection: the choice --frontier would make, nothing written) — and what
    each role's layer would be built from (its message: the protocol with its evidence,
    role_evidence.evidence, read now; its reasoning comes on top and is known only once built)."""
    import select_base_load
    for who in v2.BASES:
        try:
            _projected[who] = dict(select_base_load.projection(who),at=time.time(),valid=True)
        except Exception as error:
            _projected[who] = dict(at=time.time(),valid=False,error=str(error))
    for role in sorted(v2.LAYERABLE):
        with contextlib.suppress(Exception):
            text = v2.render("role-layer", NAME=f"layer-{role}", ROLE=role, STALE="", PROTOCOL=v2.generic_protocol(role),
                             EVIDENCE=role_evidence.evidence(role), DONE=v2.ROLE_LAYER_DONE)
            _role_messages[role] = int(len(text) / 3.05)  # Markdown's characters a token (manifest.RATIO)


def projecting():
    while True:
        with contextlib.suppress(Exception):
            project_bases()
        time.sleep(PROJECT_EVERY)


def measuring():
    while True:
        with contextlib.suppress(Exception):
            measure_bases()
        time.sleep(STALE_EVERY)


def going():
    """Whether the run goes: the watchdog does nothing, and the dispatch builds nothing, while it is stopped."""
    return bool(v2.peek().get("active")) and not os.path.exists(os.path.join(v2.STATE, "stopped"))


def layer_entry_cold(who):
    """Whether the medium layer's own entry is gone (watchdog.layer_entry_age): a delta over it would write it again."""
    import watchdog
    age = watchdog.layer_entry_age(who)
    return age is None or age >= v2.WARM_MAX


def bases():
    """/api/bases: every base with its parts, the roles' own layers, the other sessions held warm, and the recent pings
    of all of them — with the rules and thresholds they are kept by, and whether the run goes (a role's layer is built
    only then)."""
    import watchdog
    st, daemon = v2.peek(), daemon_up()
    base_pings, pings = warm_log(), session_pings()
    sessions = st["sessions"]
    roles = [role_view(r, st, sessions, daemon, pings) for r in sorted(v2.LAYERABLE)]
    layered = {x for r in roles for x in (r["layer"], r["churn"]) if x}
    held = [held_view(n, s, st, daemon, pings) for n, s in sorted(sessions.items())
            if s.get("sid") and not s.get("released") and s.get("state") != "lost" and s.get("role") not in v2.LAYER_ROLES
            and (s.get("state") not in v2.LIVE or (s.get("state") == "waiting" and s.get("sealed")))  # as holds() reads
            and watchdog.held(st, n, s)]
    recent = sorted([dict(v, at=at, what=what) for at, what, v in base_pings[-60:]]
                    + [dict(p, what=f"ping {n}") for n, ps in pings.items() for p in ps[-10:]],
                    key=lambda x: -(x["at"] or 0))[:60]
    views = [b for b in (base_view(w, daemon, base_pings) for w in v2.BASES) if b]
    shown = [r for r in roles if r["on"] or r["layer"] or r["churn"]]
    return dict(now=time.time(), daemon=daemon, active=st.get("active"),
                stopped=(state_file("stopped") or "").strip() or None, bases=views, roles=shown,
                going=going(), held=held, recent=recent,
                projected={w: _projected.get(w) for w in v2.BASES}, role_messages=dict(_role_messages),
                kb=st.get("kb"), layered=len(layered),
                rules=dict(cache_life=CACHE_LIFE, warm_max=v2.WARM_MAX, warm_every=watchdog.WARM_EVERY,
                           ping_age=v2.PING_AGE, idle_max=WARM_IDLE_MAX, layer_stale=watchdog.LAYER_STALE,
                           layer_every=watchdog.LAYER_EVERY, delta_every=watchdog.DELTA_EVERY,
                           stale_every=STALE_EVERY, stale_read=v2.STALE_READ,
                           stable_delta_max=watchdog.STABLE_DELTA_MAX, project_every=PROJECT_EVERY))


# ---------------------------------------------------------------- what the run costs

COLD_WRITE = 50_000  # a first request that wrote this much read nothing of its origin: a fork that missed its entry


def costs(hours=24.0, until=None):
    """/api/costs: what the sessions cost within the last `hours` (0: all) and in the span before it, in the harness's
    input-equivalent tokens (cache read 0.1, write 2, uncached input 1, output 5) — by kind, by time, by role, by
    session and by task, what was read again of each fork's prefix, the forks that wrote their prefix anew — and the
    keep-warm pings and the loads of the bases and the roles' layers, from what the harness logged of each."""
    now, sessions = until or time.time(), all_sessions(archive=True)
    summaries = {n: session_summary(n, s, hours=True) for n, s in sessions.items() if s.get("sid")}
    if hours <= 0:
        first = min((int(h) for x in summaries.values() for h in (x.get("hours") or {})), default=int(now))
        span = max(3600, now - first)
    else:
        span = hours * 3600
    step = 3600 if span <= 86400 * 1.01 else 3 * 3600 if span <= 3 * 86400 * 1.01 else 6 * 3600 \
        if span <= 7 * 86400 * 1.01 else 86400
    since = (now - span) // step * step  # bars on whole hours (the transcripts' buckets are hours)
    span = now - since
    before = since - span
    weight = dict(read=READ, write=WRITE, input=1, output=OUTPUT)
    kinds = ("read", "write", "input", "output")

    def blank():
        return dict({k: 0 for k in kinds}, requests=0, reread=0, sessions=0)
    total, prev = blank(), blank()
    buckets = [dict(at=since + i * step, **{k: 0.0 for k in kinds + ("pings", "loads")})
               for i in range(int(span // step) + 1)]
    by_role, by_task, rows, cold = collections.defaultdict(blank), collections.defaultdict(blank), [], []
    prev_role = collections.defaultdict(blank)
    for name, x in summaries.items():
        mine, theirs = blank(), blank()
        for h, b in (x.get("hours") or {}).items():
            h = int(h)
            into = mine if since - 3600 < h <= now else theirs if before - 3600 < h <= since - 3600 else None
            if into is None:
                continue
            for i, k in enumerate(FACETS):
                into[k] += b[i]
            if into is mine:
                slot = buckets[min(len(buckets) - 1, max(0, int((h - since) // step)))]
                for i, k in enumerate(kinds):
                    slot[k] += b[i] * weight[k]
        for got, sums, role_sums in ((mine, total, by_role), (theirs, prev, prev_role)):
            if not got["requests"]:
                continue
            got["sessions"] = 1
            for k in got:
                sums[k] += got[k]
                role_sums[x.get("role") or "?"][k] += got[k]
        if not mine["requests"]:
            continue
        c = sum(mine[k] * weight[k] for k in kinds)
        rows.append(dict(name=name, role=x.get("role"), task=x.get("task") or x.get("reviews"), cost=round(c),
                         requests=mine["requests"], read=mine["read"], write=mine["write"], output=mine["output"],
                         started=x.get("started"), state=x.get("state")))
        tid = str(x.get("task") or x.get("reviews") or "")
        if tid:
            for k in mine:
                by_task[tid][k] += mine[k]
        first = utc_epoch(x.get("first"))
        if x.get("first_write", 0) >= COLD_WRITE and first and since <= first <= now and x.get("origin"):
            cold.append(dict(name=name, role=x.get("role"), at=first, write=x["first_write"],
                             cost=round(x["first_write"] * WRITE), origin=x.get("origin")))
    keep, loads = [], []
    for at, what, v in warm_log():
        if at and since <= at <= now:
            (keep if what.startswith("warm ") else loads).append(dict(v, at=at, what=what))
    for n, ps in session_pings().items():
        keep += [dict(p, what=f"ping {n}") for p in ps if p["at"] and since <= p["at"] <= now]
    for e, key in [(e, "pings") for e in keep] + [(e, "loads") for e in loads]:
        buckets[min(len(buckets) - 1, max(0, int((e["at"] - since) // step)))][key] += e["cost"]
    cost_of = lambda d: sum(d[k] * weight[k] for k in kinds)
    per_role = []
    for role, d in sorted(by_role.items(), key=lambda kv: -cost_of(kv[1])):
        mine = sorted(r["cost"] for r in rows if r["role"] == role)
        p = prev_role.get(role)
        per_role.append(dict(role=role, **d, cost=round(cost_of(d)), previous=round(cost_of(p)) if p else 0,
                             median=mine[len(mine) // 2] if mine else 0))
    tasks = sorted(({"task": t, **d, "cost": round(cost_of(d))} for t, d in by_task.items()), key=lambda r: -r["cost"])
    subjects = {t["id"]: t.get("subject", "") for t in v2.all_tasks()}
    for t in tasks[:25]:
        t["subject"] = subjects.get(t["task"], "")
    if not total["requests"] and hours > 0 and until is None:
        # nothing in the span (a run stopped for longer than it): the same span up to the run's last activity, said so,
        # rather than an empty chart
        last = max((int(h) for x in summaries.values() for h in (x.get("hours") or {})), default=None)
        if last is not None and last + 3600 <= since:  # its last hour ends where the span begins, or before
            said = max((e for e in (utc_epoch(x.get("last")) for x in summaries.values()) if e), default=last + 3600)
            return dict(costs(hours, until=last + 3600), shifted=dict(last=min(said, last + 3600)))
    return dict(now=now, since=since, span=span, step=step, weights=weight, total=dict(total, cost=round(cost_of(total))),
                previous=dict(prev, cost=round(cost_of(prev))), buckets=buckets, roles=per_role,
                sessions=sorted(rows, key=lambda r: -r["cost"])[:25], tasks=tasks[:25],
                cold=sorted(cold, key=lambda r: -r["at"])[:40],
                keep=dict(count=len(keep), missed=sum(1 for e in keep if not e["ok"]),
                          cost=sum(e["cost"] for e in keep), events=sorted(keep, key=lambda e: -e["at"])[:80]),
                loads=dict(count=len(loads), missed=sum(1 for e in loads if not e["ok"]),
                           cost=sum(e["cost"] for e in loads), events=sorted(loads, key=lambda e: -e["at"])[:40]))


def utc_epoch(stamp):
    """A transcript's time (UTC, its zone cut off at 19 characters) as an epoch."""
    try:
        return calendar.timegm(time.strptime(stamp[:19], "%Y-%m-%dT%H:%M:%S"))
    except (ValueError, TypeError):
        return None


# ---------------------------------------------------------------- following its source

WATCHED = [os.path.join(HERE, f) for f in ("dashboard.py", "v2.py", "role_evidence.py", "watchdog.py", "train.py")] \
    + [p for p in os.environ.get("ORCH_DASHBOARD_WATCH", "").split(os.pathsep) if p]
STARTED = time.time()


def source_stamp():
    return tuple((p, os.path.getmtime(p)) for p in WATCHED if os.path.exists(p))


def compiles(paths):
    """Whether each Python source compiles: a server that re-executed into a file that does not would be gone."""
    for p in paths:
        if p.endswith(".py"):
            try:
                compile(open(p, encoding="utf-8").read(), p, "exec")  # in memory: nothing written beside it
            except (OSError, SyntaxError, ValueError) as e:
                print(f"(not reloaded: {os.path.basename(p)} does not compile: {e})", flush=True)
                return False
    return True


def follow(server, args, seen=None):
    """Re-execute the server, on the same port with the same token, when its Python changes and compiles; the page
    reloads itself when it sees the server's start change (/api/version) or its HTML change. `seen`: the sources as
    they stood when the process started, read before it serves anything — read here, a change made between the first
    request answered and this thread's first line was taken for the start, and never followed (2026-09-23: the
    console's test waited 30 s for a restart that never came)."""
    seen = seen or source_stamp()
    while True:
        time.sleep(1.5)
        now = source_stamp()
        if now == seen:
            continue
        changed = [p for (p, m) in now if (p, m) not in seen]
        seen = now
        if not compiles(changed):
            continue
        print(f"(reloading: {', '.join(os.path.basename(p) for p in changed)} changed)", flush=True)
        RELOAD.append(True)
        server.shutdown()  # serve_forever returns in the main thread, which re-executes (main)
        return


RELOAD = []


def project_file(rel):
    """A file of the project, by its path from it, for viewing: never outside it."""
    full = os.path.realpath(os.path.join(v2.PROJECT, rel))
    if not full.startswith(os.path.realpath(v2.PROJECT) + os.sep) or not os.path.isfile(full):
        return None
    with open(full, errors="ignore") as f:
        return f.read(400_000)


# ---------------------------------------------------------------- controls

BUILD_HOOK = os.environ.get("ORCH_DASHBOARD_BUILD")  # what the tests run in place of base.sh (its arguments: WHO PART)


def base_build(who, part):
    """base.sh WHO PART in the background, as the watchdog starts it (watchdog.base_run: what it says kept in
    warm.log)."""
    import watchdog
    if BUILD_HOOK:
        return subprocess.Popen([BUILD_HOOK, who, part], start_new_session=True)
    return watchdog.base_run(who, part)


LAYERS_ALL = "layers-build.json"  # the owner's build of every base's layer from the console: its order, start, process


def layer_building(who):
    """Whether a build over the base's layer is going: base.sh's lock, as young as base.sh counts one (LAYER_LOCK)."""
    age = mark_age(f"{who}-layer.building")
    return age is not None and age < int(os.environ.get("LAYER_LOCK", 2400))


def layers_all_going():
    rec = state_json(LAYERS_ALL, {}) or {}
    return rec if rec.get("pid") and os.path.exists(f"/proc/{rec['pid']}") else None


def build_all_layers():
    """Every base's layer built, one after another in the order of v2.BASES (base.sh WHO layer each), in one process
    that outlives the console: one after another, since the builds regenerate the indexes they share
    (select_base_load --refresh-index writes theory-names, plan-index and decisions-index in place), and a build
    beside another could pack one half written. A base whose layer a build is already going over says so and the
    next goes on (base.sh's lock); what each says is in warm.log."""
    order = [w for w in v2.BASES if os.path.exists(os.path.join(v2.STATE, f"{w}-base.json"))]
    if not order:
        return "refused: no base stands to build a layer over (base.sh WHO build, status, seal)"
    if layers_all_going():
        return "refused: a build of every layer is going (see Control: Bases and layers)"
    going = [w for w in order if layer_building(w)]
    if going:
        return f"refused: a build over the {', '.join(going)} layer is going: build every layer once it has ended"
    runner = [BUILD_HOOK] if BUILD_HOOK else ["sh", os.path.join(HERE, "base.sh")]
    script = 'for w in "$@"; do "$0" "$w" layer; done' if BUILD_HOOK else 'for w in "$@"; do sh "$0" "$w" layer; done'
    p = subprocess.Popen(["sh", "-c", script, runner[-1], *order], cwd=v2.PROJECT, stdout=subprocess.DEVNULL,
                         stderr=open(os.path.join(v2.STATE, "warm.log"), "a"), start_new_session=True)
    with open(os.path.join(v2.STATE, LAYERS_ALL), "w") as f:
        json.dump(dict(pid=p.pid, started=time.time(), order=order), f)
    return (f"every layer is being built, one after another: {', '.join(order)} (base.sh WHO layer each); what each "
            "says goes to state/warm.log" + ("" if daemon_up() else " — the daemon is not running, so nothing keeps "
                                              "them warm once built: start the run within the hour"))


def builds():
    """/api/builds: each base's layer as it stands — the layout it was built in (a chain of named parts, or the stable
    base and one medium layer), when it sealed, whether its entry is warm, whether a build is going over it — the
    owner's build of every layer and where it has got to, what a build from scratch would hold, and warm.log's latest
    lines about builds."""
    chain, running = state_json(LAYERS_ALL, {}) or {}, layers_all_going()
    out = []
    for who in v2.BASES:
        stable = state_json(f"{who}-base.json")
        if not stable:
            continue
        layer = v2.layer_record(who) or {}
        sealed = local_epoch(layer.get("sealed")) if layer.get("sealed") else None
        if layer_building(who):
            status = "building"
        elif chain.get("started") and who in chain.get("order", []) and sealed and sealed >= chain["started"] - 60:
            status = "built by the build of every layer"
        elif running and who in running.get("order", []):
            status = "waiting its turn"
        elif chain.get("started") and who in chain.get("order", []) and not running:
            status = "not built by the build of every layer: see warm.log"
        else:
            status = None
        proj = _projected.get(who) or {}
        out.append(dict(who=who, parts=[p.get("part") for p in layer.get("parts") or []], layer=bool(layer),
                        sealed=layer.get("sealed"), context=layer.get("context"), stable_sealed=stable.get("sealed"),
                        warm=(mark_age(f"{who}-base.hit") or 1e9) < v2.WARM_MAX, status=status,
                        projected=(sum(p.get("tokens") or 0 for p in proj.get("parts") or [])
                                   or (proj.get("stable") or 0) + (proj.get("layer") or 0)) if proj.get("valid") else None))
    try:
        lines = open(os.path.join(v2.STATE, "warm.log"), errors="ignore").read().splitlines()
    except OSError:
        lines = []
    about = re.compile(r"\b(layer|stable|reasoning|direction|inventory|catalogue|working|load|seal|built|build|fail|refused)\b", re.I)
    return dict(bases=out, chain=dict(chain, going=bool(running)) if chain else None, daemon=daemon_up(), going=going(),
                log=[x for x in lines if about.search(x) and not re.search(r"^\S+ warm \w+", x)][-40:])


def role_layer_now(role):
    """The owner's build of a role's layer: its evidence read, then its fork — what role_layer_build does over two
    dispatches, carried through here while the evidence is read (at most ROLE_LAYER_BUILD_MAX)."""
    end = time.time() + v2.ROLE_LAYER_BUILD_MAX
    while time.time() < end:
        v2.role_layer_build(role, "asked for by the owner from the console")
        if v2.role_layer_record(role).get("building"):
            return
        time.sleep(5)


def build(data):
    """A build asked for from the console, refused where the watchdog or the dispatch would not build: over a layer a
    build is going over, a delta over a layer whose own entry is cold (it would write it again), a role's layer or
    churn while the run is stopped (nothing would seal it or keep it warm: it would go cold within the hour)."""
    part = data.get("part")
    if part == "layers":
        return build_all_layers()
    if part in ("layer", "delta", "restable"):
        who = data.get("who")
        if who not in v2.BASES or not os.path.exists(os.path.join(v2.STATE, f"{who}-base.json")):
            return f"refused: there is no {who!r} base"
        if layer_building(who) or (layers_all_going() and who in layers_all_going().get("order", [])):
            return f"refused: a build over the {who} layer is going, or waits its turn in the build of every layer"
        if part == "delta":
            if not v2.deltas_on(who):
                return f"refused: the {who} base is not switched to deltas (state/deltas)"
            if not v2.layer_record(who):
                return f"refused: the {who} base has no layer to build a delta over"
            if layer_entry_cold(who):
                return (f"refused: the {who} layer's own entry is cold, so a delta over it would write it again: "
                        "refresh the layer first")
        base_build(who, part)
        return (f"base.sh {who} {part} started in the background; what it says goes to state/warm.log"
                + ("" if daemon_up() else " — the daemon is not running, so nothing keeps it warm once it is built"))
    if part in ("role-layer", "churn"):
        role = data.get("role")
        if role not in v2.LAYERABLE:
            return f"refused: {role!r} is no role with a layer of its own"
        if role not in v2.role_layers():
            return f"refused: the {role}'s layer is switched off (the role-layers switch names the roles)"
        if not (going() and daemon_up()):
            return ("refused: the run is stopped, so nothing would seal what is built or keep it warm, and it would go "
                    "cold within the hour: start the run first")
        rec = v2.role_layer_record(role)
        if part == "role-layer":
            if rec.get("building"):
                return f"refused: the {role}'s layer is being built ({rec['building']})"
            threading.Thread(target=role_layer_now, args=(role,), daemon=True).start()
            return f"the {role}'s evidence is being read; its layer is forked once it is, and sealed when it replies"
        if rec.get("churn_building"):
            return f"refused: the {role}'s churn is being built ({rec['churn_building']})"
        if not v2.role_layer_current(role):
            return f"refused: the {role} has no layer standing on its medium layer as it is: build its layer first"
        v2.role_churn_care(role, force=True)
        now = v2.role_layer_record(role).get("churn_building")
        return f"the {role}'s churn {now} is being built" if now else \
            f"no churn built for the {role}: it holds the delta standing, or no delta stands (see the log)"
    return f"refused: nothing to build called {part!r}"


def place(tid, where):
    """One task's place in the queue, moved in the order as it stands (first, up, down, last) or taken out of it: the
    whole order, so changed, given again — taking it out is said (v2.py queue --drop-unnamed)."""
    order = list(v2.peek().get("queue") or [])
    if where not in ("first", "up", "down", "last", "out"):
        return f"refused: no place {where!r}"
    if not v2.in_list(tid):
        return f"refused: no task {tid!r} in the list"
    at = order.index(tid) if tid in order else None
    if where == "out":
        if at is None:
            return f"refused: task {tid} is not in the queue"
        order.pop(at)
        if not order:
            return "refused: it is the only task queued, and an empty order is none (v2.py queue)"
        said = v2.cmd_queue(order, drop_unnamed=True)
        return said if said.startswith("refused") else f"task {tid} taken out of the queue: {len(order)} task(s) queued ({said})"
    else:
        if at is not None:
            order.pop(at)
        to = {"first": 0, "last": len(order), "up": max(0, (at if at is not None else len(order)) - 1),
              "down": min(len(order), (at if at is not None else len(order) - 1) + 1)}[where]
        order.insert(to, tid)
    said = v2.cmd_queue(order)
    return said if said.startswith("refused") else f"task {tid} placed {where}: {len(order)} task(s) queued ({said})"


def control(action, data):
    """One of the owner's controls: what it did, as the harness said it."""
    who = "the owner (console)"
    if action == "switch":
        name = data.get("name")
        if name not in SWITCHES:
            return f"refused: no switch {name!r}"
        path = os.path.join(v2.STATE, name)
        if data.get("on"):
            value = str(data.get("value") or "").strip()
            if name == "measure-bound" and value and not value.isdigit():
                return "refused: the measurement's window is a number of seconds"
            with open(path, "w") as f:
                f.write(value + ("\n" if value else ""))
            said = f"switch {name} on" + (f" ({value})" if value else "")
        else:
            if os.path.exists(path):
                os.remove(path)
            said = f"switch {name} off"
    elif action == "hold":
        name, on = data.get("what"), data.get("on")
        if name not in HOLDS:
            return f"refused: no hold {name!r}"
        path = os.path.join(v2.STATE, HOLDS[name])
        if on:
            with open(path, "w") as f:
                f.write(f"the owner's order from the console, {time.strftime('%Y-%m-%d %H:%M')}\n")
            said = f"{name} held"
        else:
            if os.path.exists(path):
                os.remove(path)
            said = f"{name} released"
            v2.kick()
    elif action == "tell":
        said = v2.cmd_tell(str(data.get("task")), str(data.get("text") or ""))
    elif action == "queue":  # the named first, the rest after them; the rest out only when said (--drop-unnamed)
        said = v2.cmd_queue([str(x) for x in data.get("ids") or []], drop_unnamed=bool(data.get("drop_unnamed")))
    elif action == "place":
        said = place(str(data.get("id") or ""), data.get("where"))
        if said.startswith("refused"):
            return said
    elif action == "drop":
        said = v2.cmd_drop([str(x) for x in data.get("ids") or []])
    elif action == "ping":
        said = v2.ping(str(data.get("name")))
    elif action == "release":
        name = str(data.get("name"))
        if name not in v2.peek()["sessions"]:
            return f"refused: no session {name!r}"
        v2.release(name)
        said = f"released {name}"
    elif action == "dispatch":
        v2.kick()
        said = "the dispatch is asked to run"
    elif action == "build":
        said = build(data)
    elif action in ("start", "stop"):
        script = os.path.join(HERE, f"{action}.sh")
        args = ["sh", script] + (["--no-attach"] if action == "start" else ["--keep-warm"] if data.get("keep_warm")
                                 else [])
        if action == "start" and data.get("fresh"):
            args.append("--fresh")
        done = subprocess.run(args, cwd=v2.PROJECT, capture_output=True, text=True, timeout=300)
        said = (done.stdout + done.stderr).strip()[-3000:] or f"{action}.sh exited {done.returncode}"
    else:
        return f"refused: no control {action!r}"
    v2.log(f"{who}: {action} — {str(said)[:300]}")
    return said


# ---------------------------------------------------------------- the server

class Handler(http.server.BaseHTTPRequestHandler):
    token = ""
    port = 0

    def log_message(self, *args):  # the console's own requests are not the run's log
        pass

    def allowed(self, header_only=False):
        host = (self.headers.get("Host") or "").split(":")[0]
        if host not in ("127.0.0.1", "localhost"):
            return False
        given = self.headers.get("X-Token")
        if not header_only:
            query = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            given = given or (query.get("token") or [""])[0]
        return bool(given) and secrets.compare_digest(given, self.token)

    def send(self, code, body, kind="application/json"):
        data = body if isinstance(body, bytes) else (body if isinstance(body, str) else json.dumps(body)).encode()
        self.send_response(code)
        self.send_header("Content-Type", kind + "; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Content-Security-Policy", "default-src 'self'; style-src 'self' 'unsafe-inline'; "
                         "script-src 'self' 'unsafe-inline'; connect-src 'self'")
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        if not self.allowed():
            return self.send(403, {"error": "the console's token is needed (printed when it started)"})
        url = urllib.parse.urlparse(self.path)
        q = {k: v[0] for k, v in urllib.parse.parse_qs(url.query).items()}
        try:
            if url.path == "/":
                return self.send(200, open(os.path.join(HERE, "dashboard.html")).read().replace(
                    "__TOKEN__", html.escape(self.token)), "text/html")
            if url.path == "/api/overview":
                return self.send(200, overview())
            if url.path == "/api/sessions":
                ss = all_sessions(archive=q.get("all") == "1")
                rows = [session_summary(n, s) for n, s in ss.items()]
                return self.send(200, sorted(rows, key=lambda r: -(r.get("started") or 0)))
            if url.path == "/api/session":
                s = all_sessions(archive=True).get(q.get("name", ""))
                if not s:
                    return self.send(404, {"error": "no such session"})
                return self.send(200, dict(session=s, **(session_turns(s) or {"items": [], "summary": {}})))
            if url.path == "/api/tasks":
                st = v2.peek()
                ids = list(dict.fromkeys([t["id"] for t in v2.all_tasks()] + list(st["tasks"])))
                return self.send(200, [task_record(t, st) for t in sorted(ids, key=lambda x: -int(x) if x.isdigit() else 0)])
            if url.path == "/api/task":
                tid, st = q.get("id", ""), v2.peek()
                task = v2.read_task(tid) or {}
                sessions = [session_summary(n, s) for n, s in all_sessions(archive=True).items()
                            if str(s.get("task")) == tid or str(s.get("reviews")) == tid]
                files = {n: read_build(tid, n) for n in ("result.md", "review.md", "commit.md", "finalize.json",
                                                         "brief.json", "measurements.log")}
                files["finalize.log (its end)"] = read_build(tid, "finalize.log", tail=200)
                dependents = [t["id"] for t in v2.all_tasks() if tid in (t.get("blockedBy") or [])]
                return self.send(200, dict(record=task_record(tid, st), task=task, state=st["tasks"].get(tid) or {},
                                           files={k: v for k, v in files.items() if v is not None},
                                           sessions=sorted(sessions, key=lambda r: r.get("started") or 0),
                                           history=task_history(tid), dependents=dependents))
            if url.path == "/api/log":
                return self.send(200, log_tail(int(q.get("n", 300)), q.get("grep")))
            if url.path == "/api/checks":
                return self.send(200, checks())
            if url.path == "/api/machine":
                return self.send(200, machine())
            if url.path == "/api/bases":
                return self.send(200, bases())
            if url.path == "/api/builds":
                return self.send(200, builds())
            if url.path == "/api/costs":
                return self.send(200, costs(float(q.get("hours", 24))))
            if url.path == "/api/graph":
                return self.send(200, graph(float(q.get("hours", 6))))
            if url.path == "/api/version":
                page = os.path.join(HERE, "dashboard.html")
                return self.send(200, {"started": STARTED, "page": os.path.getmtime(page) if os.path.exists(page) else 0,
                                       "parses": PARSES})
            if url.path == "/api/file":
                text = project_file(q.get("path", ""))
                return self.send(200 if text is not None else 404, {"path": q.get("path"), "text": text})
            return self.send(404, {"error": "no such page"})
        except Exception as e:  # noqa: BLE001  one failing view does not take the console down
            return self.send(500, {"error": repr(e)})

    def do_POST(self):
        if not self.allowed(header_only=True):  # a control needs the header, which another site's page cannot send
            return self.send(403, {"error": "a control needs the console's token in the X-Token header"})
        if urllib.parse.urlparse(self.path).path != "/api/control":
            return self.send(404, {"error": "no such control"})
        try:
            data = json.loads(self.rfile.read(int(self.headers.get("Content-Length") or 0)) or b"{}")
            return self.send(200, {"said": control(data.get("action"), data)})
        except Exception as e:  # noqa: BLE001
            return self.send(500, {"error": repr(e)})


class Server(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True
    allow_reuse_address = True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, default=int(os.environ.get("ORCH_DASHBOARD_PORT", 8765)))
    args = ap.parse_args()
    Handler.token = os.environ.get("ORCH_DASHBOARD_TOKEN") or secrets.token_urlsafe(18)
    started_from = source_stamp()  # before anything is served: what follow() measures a change against
    server = Server(("127.0.0.1", args.port), Handler)
    Handler.port = server.server_address[1]
    print(f"the run's console: http://127.0.0.1:{Handler.port}/?token={Handler.token}", flush=True)
    if not v2.control():
        print("(inside Claude Code's sandbox: its views work, its controls that start or stop sessions do not)",
              flush=True)
    threading.Thread(target=follow, args=(server, args, started_from), daemon=True).start()
    threading.Thread(target=warm_summaries, daemon=True).start()
    threading.Thread(target=measuring, daemon=True).start()
    threading.Thread(target=projecting, daemon=True).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    server.server_close()
    if RELOAD:  # the same port and token, the new source
        os.environ.update(ORCH_DASHBOARD_TOKEN=Handler.token)
        os.execv(sys.executable, [sys.executable, os.path.abspath(__file__), "--port", str(Handler.port)])
    return 0


if __name__ == "__main__":
    sys.exit(main())
