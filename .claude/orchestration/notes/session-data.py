#!/usr/bin/env python3
"""One record per orchestrated session of a day, from its own transcript: what it cost and what it read.

    python3 -B notes/session-data.py [DAY] [--out FILE]      DAY as YYYY-MM-DD (today by default)

Beside it, state/analysis/names-DAY.jsonl: for each session the identifiers its own writing uses — its commands,
the texts of its changes and its visible replies, never what came back to it — the evidence of which held content a
session worked with even where it read none of it (a name with an underscore, a prime or an inner capital, at least
four characters: Isabelle's and Python's names, not English words).

Not part of the harness; read-only but for its output (state/analysis/sessions-DAY.jsonl by default). A session's
own requests are those that start at or after its launch: a fork's transcript begins with a copy of its origin's
conversation, ids and timestamps kept, and counted with it every fork would carry its base's load (the fault
notes/delta-measure.py had until 2026-09-22). Timestamps in transcripts are UTC.

Per session: name, role, origin (the base it forked), task, launch time; its requests, each with cache read, cache
write, fresh input and output tokens and its number of tool calls; the cost in input-equivalent tokens (cache read
0.1, 1-hour write 2, input 1, output 5 — every entry the harness writes is a 1-hour one); and each tool call: the
command (cut), the kind, the files it names, the sources of a `v2.py read`, the size of what came back, whether it
failed or was refused.
"""
import calendar
import json
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HERE)
import v2  # noqa: E402

READ, WRITE, OUTPUT = 0.1, 2.0, 5.0
PATH = re.compile(r"(?<![\w/.-])((?:\.claude/orchestration/|theories/|tools/|validation/|\.build/|docs/|notes/|protocols/|"
                  r"~/\.claude/[\w./-]+/|/home/julius/structure_and_semantics/)?[\w./-]*\w\.(?:thy|md|py|json|jsonl|txt|sh|ML|log))\b")
V2READ = re.compile(r"v2\.py read ([^;&|\n]+)")


def cost(u):
    return (u.get("cache_read_input_tokens", 0) * READ + u.get("cache_creation_input_tokens", 0) * WRITE
            + u.get("input_tokens", 0) + u.get("output_tokens", 0) * OUTPUT)


def kind(cmd):
    c = cmd.strip()
    for pat, k in ((r"v2\.py read\b", "read"), (r"v2\.py change\b", "change"), (r"v2\.py again\b", "again"),
                   (r"v2\.py check\b", "check"), (r"probe_theories\.py", "probe"), (r"incremental_check\.py", "check"),
                   (r"v2\.py (result|finalize|verdict|end|park|ask|reply|tell|queue|ledger|propose)\b", "harness"),
                   (r"v2\.py\b", "harness"), (r"^\s*(sed|cat|head|tail|awk|nl)\b", "shell-read"),
                   (r"\b(grep|rg)\b", "search"), (r"python3?\b", "script"), (r"\bgit\b", "git")):
        if re.search(pat, c):
            return k
    return "other"


def rel(p):
    p = p.replace("/home/julius/structure_and_semantics/", "")
    return re.sub(r"^\.build/trees/[^/]+/", "", p)


def transcripts():
    out = {}
    for d in v2.transcript_dirs():
        try:
            for f in os.listdir(d):
                if f.endswith(".jsonl"):
                    out[f[:-6]] = os.path.join(d, f)
        except OSError:
            pass
    return out


def session_record(name, s, path):
    started = s.get("started") or 0
    reqs, order, calls, results, said = {}, [], {}, {}, []
    for line in open(path, errors="ignore"):
        try:
            r = json.loads(line)
        except ValueError:
            continue
        ts = r.get("timestamp") or ""
        if not ts or r.get("isSidechain"):
            continue
        try:
            t = calendar.timegm(time.strptime(ts[:19], "%Y-%m-%dT%H:%M:%S"))
        except ValueError:
            continue
        if t < started - 5:
            continue
        m = r.get("message") or {}
        content = m.get("content")
        if r.get("type") == "assistant" and isinstance(content, list):
            said.extend(b.get("text", "") for b in content if isinstance(b, dict) and b.get("type") == "text")
            mid = m.get("id")
            if mid not in reqs:
                u = m.get("usage") or {}
                reqs[mid] = dict(t=t, read=u.get("cache_read_input_tokens", 0), write=u.get("cache_creation_input_tokens", 0),
                                 fresh=u.get("input_tokens", 0), out=u.get("output_tokens", 0), calls=0)
                order.append(mid)
            for b in content:
                if isinstance(b, dict) and b.get("type") == "tool_use":
                    i = b.get("input") or {}
                    cmd = i.get("command") or i.get("file_path") or json.dumps(i)[:300]
                    calls[b.get("id")] = dict(req=order.index(mid), tool=b.get("name"), cmd=cmd)
                    reqs[mid]["calls"] += 1
        elif r.get("type") == "user" and isinstance(content, list):
            for b in content:
                if isinstance(b, dict) and b.get("type") == "tool_result":
                    body = b.get("content")
                    if isinstance(body, list):
                        body = "\n".join(x.get("text", "") for x in body if isinstance(x, dict))
                    body = body or ""
                    results[b.get("tool_use_id")] = (len(body), bool(b.get("is_error")),
                                                     body[:160] if (b.get("is_error") or "refused" in body[:200]) else "")
    out_calls = []
    for cid, c in calls.items():
        size, err, head = results.get(cid, (0, False, ""))
        cmd = c["cmd"]
        body_free = re.sub(r"<<-?\s*'?(\w+)'?\n.*?\n\1\b", "<<HEREDOC", cmd, flags=re.S)  # a change's text is not a read
        out_calls.append(dict(req=c["req"], tool=c["tool"], kind=kind(cmd), cmd=cmd[:400], bytes=size, error=err,
                              said=head, files=sorted({rel(p) for p in PATH.findall(body_free)}),
                              v2read=[x.strip() for m in V2READ.findall(body_free) for x in m.split()]))
    rq = [reqs[m] for m in order]
    WRITTEN.append(" ".join(c["cmd"] for c in calls.values()) + " " + " ".join(said))
    return dict(name=name, role=s.get("role"), origin=s.get("origin"), task=s.get("task"), started=started,
                sid=s.get("sid"), requests=rq, cost=sum(cost(dict(cache_read_input_tokens=q["read"],
                                                                  cache_creation_input_tokens=q["write"],
                                                                  input_tokens=q["fresh"], output_tokens=q["out"]))
                                                              for q in rq),
                calls=out_calls)


WRITTEN = []
NAME = re.compile(r"[A-Za-z][A-Za-z0-9_']{3,}")


def names(text):
    return sorted({w for w in NAME.findall(text) if "_" in w or "'" in w or re.search(r"[a-z][A-Z]", w)})


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    day = args[0] if args else time.strftime("%Y-%m-%d")
    out = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else os.path.join(v2.STATE, "analysis",
                                                                                       f"sessions-{day}.jsonl")
    lo = time.mktime(time.strptime(day, "%Y-%m-%d"))
    hi = lo + 86400
    paths, st, n = transcripts(), v2.peek(), 0
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w") as f, open(os.path.join(os.path.dirname(out), f"names-{day}.jsonl"), "w") as words:
        for name, s in sorted(st["sessions"].items(), key=lambda kv: kv[1].get("started") or 0):
            if not (lo <= (s.get("started") or 0) < hi):
                continue
            path = paths.get(s.get("sid") or "")
            if not path:
                continue
            rec = session_record(name, s, path)
            f.write(json.dumps(rec) + "\n")
            words.write(json.dumps(dict(name=name, role=rec["role"], origin=rec["origin"], names=names(WRITTEN.pop()))) + "\n")
            n += 1
    print(f"{n} sessions -> {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
