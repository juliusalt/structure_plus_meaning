#!/usr/bin/env python3
"""Report whether a session forked from a base (`--resume BASE --fork-session`) read the base's prompt cache.

usage: session_fork_check.py <fork-session-id> <base-session-id>

The fork's transcript begins with a copy of the base's conversation. Its first own request should be a
cache read about as large as the base's final context, with a cache write about as large as the first
message it was given; a cold fork shows a cache write of that size instead.
"""
import json
import os
import sys

PROJECT = os.path.expanduser("~/.claude/projects/" + os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))).replace("/", "-").replace("_", "-"))


def requests(session):
    out = []
    for line in open(f"{PROJECT}/{session}.jsonl", errors="ignore"):
        if '"usage"' not in line:
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("type") != "assistant" or d.get("isSidechain"):
            continue
        m = d.get("message") or {}
        u = m.get("usage") or {}
        total = tuple(u.get(k) or 0 for k in ("input_tokens", "cache_read_input_tokens", "cache_creation_input_tokens"))
        if sum(total):
            out.append((m.get("id"), total, m.get("model"), d.get("timestamp", "")))
    return out


def main():
    fork, base = sys.argv[1], sys.argv[2]
    base_reqs = requests(base)
    if not base_reqs:
        print("base has no recorded requests")
        return 1
    seen = {r[0] for r in base_reqs}
    base_context = sum(base_reqs[-1][1])
    own = [r for r in requests(fork) if r[0] not in seen]
    if not own:
        print("fork has made no request of its own yet")
        return 1
    (_, (fresh, read, write), model, ts) = own[0]
    share = 100 * read // (fresh + read + write)
    ok = read >= 0.9 * base_context and model == base_reqs[-1][2]
    print(
        f"{'OK  ' if ok else 'MISS'} session fork {fork[:8]} of base {base[:8]}: first own request "
        f"cache_read={read} cache_write={write} uncached={fresh} ({share}% read); base context={base_context}; "
        f"model fork={model} base={base_reqs[-1][2]}; own requests so far={len(own)}"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
