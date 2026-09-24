#!/usr/bin/env python3
"""Report whether a session forked from a base (`--resume BASE --fork-session`) read the base's prompt cache.

usage: session_fork_check.py <fork-session-id> <base-session-id>
       session_fork_check.py --is-fork <fork-session-id> <base-session-id>   exit 0 when it is a fork of that base

The fork's transcript begins with a copy of the base's conversation. Its first own request should be a
cache read about as large as the base's final context, with a cache write about as large as the first
message it was given; a cold fork shows a cache write of that size instead.
"""
import json
import os
import sys

PROJECT = os.path.expanduser("~/.claude/projects/" + os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))).replace("/", "-").replace("_", "-"))


def transcript(session):
    """The session's transcript: the project's, or its task tree's when it was started in one (v2.transcript_dirs)."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import v2
    return next((p for d in v2.transcript_dirs(PROJECT) for p in [f"{d}/{session}.jsonl"] if os.path.exists(p)),
                f"{PROJECT}/{session}.jsonl")


def requests(session):
    out = []
    path = transcript(session)
    if not os.path.exists(path):
        # a session that has written nothing yet, or whose transcript is gone: a ping's throwaway fork is deleted as
        # soon as its verdict has been read, and a check running beside it wrote a traceback into warm.log
        return out
    for line in open(path, errors="ignore"):
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


def is_fork(fork, base):
    """Whether the session is a fork of the base: its transcript holds every request of the base's (a fork's begins
    with a copy of its origin's conversation, ids and all). `base.sh layer --adopt` records nothing else."""
    base_reqs = requests(base)
    held = {r[0] for r in requests(fork)}
    missing = [r for r in base_reqs if r[0] not in held]
    if not base_reqs or missing:
        print(f"{fork[:8]} is not a fork of {base[:8]}: "
              + ("the base has no recorded requests" if not base_reqs else f"{len(missing)} of its requests are not in it"))
        return 1
    return 0


def main():
    if sys.argv[1] == "--is-fork":
        return is_fork(sys.argv[2], sys.argv[3])
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
