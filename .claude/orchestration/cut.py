#!/usr/bin/env python3
"""What one call shows at most: { ( CMD ) 2>&1; printf '\\n\\036%s\\n' "$?"; } | cut.py BYTES head|tail DIR [N].

A call shows at most READ_BYTES (the owner, 2026-09-21: 5K bytes, so that a large chunk is read deliberately, split
into many reads, rather than taken whole when most of it is taken by accident; and the limit applies to everything,
outputs and checks too). The guard runs every command whose output's size it cannot know beforehand through this, by
rewriting it before it runs (work_meter.bounded). A longer output is kept whole in DIR, and what is shown is its
beginning — or its end, for a check and for any command that failed, since that is where a command says how it
ended and what went wrong — with where the whole is kept and how to read the rest by its lines. Reading on had meant running the command again, which for a check is another run of minutes.

It ends with the command's own status, which the group writes after the output: a pipeline's status is its last
command's, and a failing check must still read as failing. A command that ended failing is told, by its number N
among the session's kept commands, to be fixed rather than written again whole (`v2.py again N`).
"""
import os
import re
import sys

KEEP = 50  # the outputs a session's directory holds: the newest
# the line a failure is said on: Isabelle's message, an exception after its traceback, a native panic, an `error:`
FAILURE = re.compile(rb"^\s*(?:\*\*\*.*|[\w.]+(?:Error|Exception)\b.*|.*\bpanicked at\b.*|(?:error|Error|ERROR)(?:\[\w+\])?:\s.*)$")


def said_before(data, shown_from):
    """The last line of a failed command's output that says its failure, when it stands before the part shown (a
    program's output is buffered in a pipe and its error is not, so the error can come first): (its line, text)."""
    lines = data.split(b"\n")
    for n in range(len(lines) - 1, -1, -1):
        if FAILURE.match(lines[n]):
            return (n + 1, lines[n].decode(errors="replace").strip()[:300]) if n + 1 < shown_from else None
    return None


def status_of(data):
    """(the output, the command's status) from what the group wrote; 0 when it wrote no status (it exited early)."""
    i = data.rfind(b"\n\x1e")
    if i >= 0 and data[i + 2:].strip().isdigit():
        return data[:i], int(data[i + 2:].strip())
    return data, 0


def numbered(directory):
    return [int(f[:-4]) for f in os.listdir(directory) if f.endswith(".txt") and f[:-4].isdigit()]


def keep(directory, data):
    """The path the whole output is kept at: the next number in the session's directory, the oldest past KEEP gone."""
    os.makedirs(directory, exist_ok=True)
    n = max(numbered(directory), default=0) + 1
    while True:  # parallel calls of one request cut at once
        path = os.path.join(directory, f"{n}.txt")
        try:
            fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
            break
        except FileExistsError:
            n += 1
    with os.fdopen(fd, "wb") as f:
        f.write(data)
    for old in sorted(numbered(directory))[:-KEEP]:
        try:
            os.remove(os.path.join(directory, f"{old}.txt"))
        except OSError:
            pass
    return path


def fix_note(n, status):
    """What a command that ended failing is told: its correction, not the command again (the owner, 2026-09-21)."""
    return (f"[command {n} ended with status {status}. If it failed, send the correction and not the command again: "
            f"`.claude/orchestration/v2.py again {n} <<'EOF'` with SEARCH/REPLACE blocks on its text runs it fixed.]\n")


def main():
    limit, end, directory = int(sys.argv[1]), sys.argv[2], sys.argv[3]
    kept = sys.argv[4] if len(sys.argv) > 4 else None
    data, status = status_of(sys.stdin.buffer.read())
    note = fix_note(kept, status) if kept and status else ""
    if len(data) <= limit:
        sys.stdout.buffer.write(data)
        if note:
            sys.stdout.write(("\n" if data and not data.endswith(b"\n") else "") + note)
        return status
    lines = data.count(b"\n") + (0 if data.endswith(b"\n") else 1)
    try:
        path, failed = keep(directory, data), None
    except OSError as e:
        path, failed = None, e.strerror
    per = max(1, int(limit * lines / len(data)))  # about a read's worth of its lines

    def rest(a, b):
        return (f"the whole output is kept in {path}: read the rest by its lines (`sed -n '{a},{b}p' {path}` and on), "
                "several reads in one batch" if path else f"the whole output could not be kept ({failed}): narrow the "
                "command")
    if end == "tail" or status:  # a failure is said at the end: a traceback, a native error, a check's summary
        part = data[-limit:]
        start = part.find(b"\n")
        if 0 <= start < limit // 2:  # from a line's start: half a line is read twice or misread
            part = part[start + 1:]
        first = lines - (part.count(b"\n") + (0 if part.endswith(b"\n") else 1)) + 1
        before = said_before(data, first) if status else None
        sys.stdout.write(f"[this call's output is cut: it shows its last lines, {first}-{lines} ({len(part):,} of "
                         f"{len(data):,} bytes), where it says how it ended. A read shows at most {limit:,} "
                         f"bytes; {rest(1, min(per, first - 1))}.]\n"
                         + (f"[its failure is said before them, at line {before[0]}: {before[1]}]\n" if before else ""))
        sys.stdout.flush()
        sys.stdout.buffer.write(part)
        sys.stdout.flush()
        if note:
            sys.stdout.write(("" if part.endswith(b"\n") else "\n") + note)
        return status
    head = data[:limit]
    stop = head.rfind(b"\n")
    if stop >= limit // 2:  # at a line's end when one is near
        head = head[:stop + 1]
    shown = head.count(b"\n") + (0 if head.endswith(b"\n") else 1)
    on = shown + 1 if head.endswith(b"\n") else shown
    sys.stdout.buffer.write(head if head.endswith(b"\n") else head + b"\n")
    sys.stdout.write(f"[this call's output stops here: it showed lines 1-{shown} ({len(head):,} of {len(data):,} "
                     f"bytes) of {lines}. A read shows at most {limit:,} bytes; {rest(on, on + per - 1)}.]\n" + note)
    return status


if __name__ == "__main__":
    sys.exit(main())
