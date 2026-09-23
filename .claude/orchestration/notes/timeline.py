#!/usr/bin/env python3
"""Where each orchestrated session's wall time went, from its own transcript: one record per session.

    python3 -B notes/timeline.py [--out FILE]      every session the state or its archive names

Not part of the harness; read-only but for its output (state/analysis/timeline.jsonl by default). A session's own
part of its transcript starts at its launch (a fork's begins with a copy of its origin's conversation). Each interval
between two consecutive entries is charged to what the later entry is: an assistant entry's to the model (its
prefill, thinking and writing), a tool result's to the tool that ran, a prompt's (a launch, a resume with mail or a
result) to waiting — the session was parked, idle or not yet resumed. The prompt that ends a wait is kept (its first
words say what resumed the session). Per request: when it was sent, when its last block came, its tokens, and its
calls with how long each ran, their kind (session-data.py's), and the size of what came back.
"""
import calendar
import importlib.util
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HERE)
import v2  # noqa: E402

_spec = importlib.util.spec_from_file_location("session_data", os.path.join(HERE, "notes", "session-data.py"))
sd = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(sd)


def stamp(ts):
    try:
        return calendar.timegm(time.strptime(ts[:19], "%Y-%m-%dT%H:%M:%S")) + float("0" + ts[19:23].rstrip("Z"))
    except ValueError:
        return None


def all_sessions():
    st = v2.peek()
    out = {}
    try:
        for line in open(os.path.join(v2.STATE, "v2-archive.jsonl")):
            try:
                r = json.loads(line)
            except ValueError:
                continue
            s = r.get("session")
            if s and s.get("name"):
                out[s["name"]] = s
    except OSError:
        pass
    out.update(st["sessions"])
    return out


def record(name, s, path):
    started = s.get("started") or 0
    entries = []
    for line in open(path, errors="ignore"):
        try:
            r = json.loads(line)
        except ValueError:
            continue
        if r.get("isSidechain") or r.get("type") not in ("user", "assistant"):
            continue
        t = stamp(r.get("timestamp") or "")
        if t is None or t < started - 5:
            continue
        entries.append((t, r))
    entries.sort(key=lambda e: e[0])
    model = tool = wait = 0.0
    waits, reqs, calls, byid = [], [], {}, {}
    prev = None
    for t, r in entries:
        m = r.get("message") or {}
        content = m.get("content")
        if r.get("type") == "assistant":
            if prev is not None:
                model += max(0.0, t - prev)
            mid = m.get("id")
            if mid not in byid:
                u = m.get("usage") or {}
                byid[mid] = dict(sent=prev if prev is not None else t, done=t, read=u.get("cache_read_input_tokens", 0),
                                 write=u.get("cache_creation_input_tokens", 0), out=u.get("output_tokens", 0), calls=[])
                reqs.append(byid[mid])
            byid[mid]["done"] = t
            if isinstance(content, list):
                for b in content:
                    if isinstance(b, dict) and b.get("type") == "tool_use":
                        i = b.get("input") or {}
                        cmd = i.get("command") or i.get("file_path") or json.dumps(i)[:300]
                        c = dict(tool=b.get("name"), kind=sd.kind(cmd), cmd=cmd[:160], at=t, dur=None, bytes=0,
                                 error=False)
                        calls[b.get("id")] = c
                        byid[mid]["calls"].append(c)
        else:
            results = [b for b in content if isinstance(b, dict) and b.get("type") == "tool_result"] \
                if isinstance(content, list) else []
            if results:
                if prev is not None:
                    tool += max(0.0, t - prev)
                for b in results:
                    c = calls.get(b.get("tool_use_id"))
                    if c is not None:
                        body = b.get("content")
                        if isinstance(body, list):
                            body = "\n".join(x.get("text", "") for x in body if isinstance(x, dict))
                        c["dur"] = round(t - c["at"], 1)
                        c["bytes"] = len(body or "")
                        c["error"] = bool(b.get("is_error"))
            else:
                text = content if isinstance(content, str) else " ".join(
                    b.get("text", "") for b in (content or []) if isinstance(b, dict) and b.get("type") == "text")
                if prev is not None and t - prev > 0:
                    wait += t - prev
                    waits.append(dict(at=prev, dur=round(t - prev, 1), by=text[:140]))
        prev = t
    for c in calls.values():
        c.pop("at", None)
    first = entries[0][0] if entries else started
    last = entries[-1][0] if entries else started
    return dict(name=name, role=s.get("role"), origin=s.get("origin"), task=s.get("task"), started=started,
                ended=s.get("ended"), first=first, last=last, model=round(model, 1), tool=round(tool, 1),
                wait=round(wait, 1), waits=waits, requests=[dict(q, sent=round(q["sent"], 1), done=round(q["done"], 1))
                                                             for q in reqs])


def main():
    out = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else os.path.join(v2.STATE, "analysis",
                                                                                       "timeline.jsonl")
    paths, n = sd.transcripts(), 0
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w") as f:
        for name, s in sorted(all_sessions().items(), key=lambda kv: kv[1].get("started") or 0):
            path = paths.get(s.get("sid") or "")
            if not path:
                continue
            f.write(json.dumps(record(name, s, path)) + "\n")
            n += 1
    print(f"{n} sessions -> {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
