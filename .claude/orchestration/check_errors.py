#!/usr/bin/env python3
"""A check run to its end, which ends by listing every error it reported: check_errors.py [--watch PATH]...
[--keep DIR] -- COMMAND...

The owner, 2026-09-21: better to wait for the full run and give the session all its errors, to be dealt with at once,
than to stop at the first and have them fixed one by one — a check after each single fix spends a whole run on each.
The guard runs every check of a session through this (work_meter.bounded). It passes the check's output through, and
when the check has ended it gathers the errors Isabelle reported (its `***` messages) from that output and from the
logs the check wrote meanwhile — each PATH a file, or every *.log under a directory (a probe's under its --work, a
check's under its --output), since the repository's checks log Isabelle's output and print a summary only at their
end — and prints them last, one line each with where it stands, so that the end a check's cut shows holds them. A
check that failed says also what else failed, which is no Isabelle message: a native execution, a recipe, a host test,
a tool that raised — each part its output names as failed, with the failure its log ends on, each log written meanwhile
that ends on one, and the check's own summary error (found 2026-09-21: a native controller's errors would have reached
nobody but by reading the logs one by one). A list longer than ROOM is kept whole in DIR and named. It ends with the
check's own status.
"""
import json
import os
import re
import subprocess
import sys
import time

# the bytes the list takes at most in the check's output: its cut shows the last read's worth (READ_BYTES, the harness's
# figure, which reaches here as its default), and a note heads it
ROOM = int(os.environ.get("ORCH_READ_BYTES", 5_000)) - 800
KEEP = 10  # the full lists a session's directory holds: the newest
WHERE = re.compile(r'\s*\(line (\d+) of "([^"]+)"\)')


def logs(watched, since):
    """The logs among the watched paths written since the check began: one written before is another run's."""
    for path in watched:
        found = [path] if os.path.isfile(path) else [
            os.path.join(root, name) for root, _, names in os.walk(path) for name in names if name.endswith(".log")]
        for log in sorted(found):
            try:
                if os.path.getmtime(log) >= since:
                    yield log
            except OSError:
                pass


def errors_in(text):
    """Every error message in a text, one line each: `FILE:LINE: its first line`, where the message says where.
    Isabelle's message is a run of `***` lines ending, in a theory, with `At command "…" (line N of "…")`, which is
    where it stands (its first line may name an ML file); two messages side by side without it part where a line of
    its own names a place."""
    out, message = [], []

    def close():
        if message:
            places = [m for m in map(WHERE.search, message) if m]
            place = next((m for line, m in zip(message, map(WHERE.search, message)) if m and line.startswith("At command")),
                         places[0] if places else None)
            first = WHERE.sub("", message[0]).rstrip(":").strip() or " ".join(message)[:120]
            out.append((f"{os.path.basename(place.group(2))}:{place.group(1)}: " if place else "") + first[:160])
            message.clear()
    for line in text.splitlines():
        if not line.startswith("***"):
            close()
            continue
        body = line[3:]
        if message and not body.startswith("  ") and WHERE.search(body) and not body.strip().startswith("At command") \
                and any(WHERE.search(x) for x in message):
            close()
        message.append(body.strip())
        if body.strip().startswith("At command"):
            close()
    close()
    return out


# the line a failure ends on that is no Isabelle message: an exception after its traceback, a native panic, a compiler's
# or a tool's `error:`, a failed test's FAILED
FAILED_LINE = re.compile(r"^\s*(?:[\w.]+(?:Error|Exception)\b.*|.*\bpanicked at\b.*|(?:error|Error|ERROR)(?:\[\w+\])?:\s.*"
                         r"|FAILED\b.*|Fatal\b.*)$")
ENDS = 20  # a log ends on a failure when its failure stands among its last lines


def last_failure(text):
    """The failure a text ends on, other than Isabelle's messages, or None."""
    return next((line.strip()[:200] for line in reversed(text.splitlines()[-ENDS:]) if FAILED_LINE.match(line)), None)


def failures(output, logs_read):
    """What a failed check says failed besides Isabelle: each part its output names as failed — a JSON row with
    "status": "failed" and a name (a recipe) — with the failure its own log ends on, the check's summary error, and
    each other log written meanwhile that ends on a failure."""
    out, used = [], set()
    by_name = {os.path.splitext(os.path.basename(path))[0]: (path, text) for path, text in logs_read}
    for line in output.splitlines():
        line = line.strip()
        try:
            row = json.loads(line) if line.startswith("{") and line.endswith("}") else None
        except ValueError:
            row = None
        if not isinstance(row, dict) or row.get("status") != "failed":
            continue
        name = row.get("recipe") or row.get("name")
        if name:
            log = by_name.get(name)
            said = last_failure(log[1]) if log else None
            used.add(log[0] if log else None)
            out.append(f"{name} failed" + (f" (exit {row['exit_code']})" if "exit_code" in row else "")
                       + (f": {said}" if said else "") + (f" [{os.path.relpath(log[0])}]" if log else ""))
        elif row.get("error"):
            out.append(f"the check: {str(row['error'])[:200]}")
    for path, text in logs_read:
        said = last_failure(text) if path not in used else None
        if said:
            out.append(f"{said} [{os.path.relpath(path)}]")
    return out


def listed(errors, keep):
    """The list the check ends with: whole when it fits, else what fits and where the whole is kept."""
    head = (f"[this check reported {len(errors)} error{'s' * (len(errors) > 1)}, listed here with where each stands. "
            "Fix them all — and what the same cause breaks elsewhere — before the next check: a check after each "
            "single fix spends a whole run on each.]\n")
    lines, size = [], len(head.encode())
    for e in errors:
        size += len(e.encode()) + 3
        if size > ROOM:
            break
        lines.append(f"- {e}\n")
    if len(lines) == len(errors):
        return head + "".join(lines)
    rest = f"[… and {len(errors) - len(lines)} more"
    if keep:
        try:
            os.makedirs(keep, exist_ok=True)
            n = 1 + max((int(f[7:-4]) for f in os.listdir(keep) if re.fullmatch(r"errors-\d+\.txt", f)), default=0)
            path = os.path.join(keep, f"errors-{n}.txt")
            open(path, "w").write("".join(f"- {e}\n" for e in errors))
            for old in sorted(int(f[7:-4]) for f in os.listdir(keep) if re.fullmatch(r"errors-\d+\.txt", f))[:-KEEP]:
                os.remove(os.path.join(keep, f"errors-{old}.txt"))
            rest += f": the whole list is kept in {path}"
        except OSError as e:
            rest += f" (the whole list could not be kept: {e.strerror})"
    return head + "".join(lines) + rest + "]\n"


def main():
    args = sys.argv[1:]
    if "--" not in args or not args[args.index("--") + 1:]:
        print(__doc__.splitlines()[0], file=sys.stderr)
        return 2
    split = args.index("--")
    watched = [args[i + 1] for i in range(split - 1) if args[i] == "--watch"]
    keep = next((args[i + 1] for i in range(split - 1) if args[i] == "--keep"), None)
    since = time.time() - 1  # a file system's times are coarser than the clock's
    process = subprocess.Popen(args[split + 1:], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    seen = []
    for chunk in iter(lambda: process.stdout.readline(), b""):
        sys.stdout.buffer.write(chunk)
        sys.stdout.buffer.flush()
        seen.append(chunk.decode(errors="replace"))
    status = process.wait()
    output, logs_read = "".join(seen), []
    for log in logs(watched, since):
        try:
            logs_read.append((log, open(log, errors="replace").read()))
        except OSError:
            pass
    errors = errors_in(output) + [e for _, text in logs_read for e in errors_in(text)]
    if status:  # a failed check says what else failed; one that passed has nothing to fix
        errors += failures(output, logs_read)
    errors = list(dict.fromkeys(errors))  # one message in the output and in a log is one error
    if errors:
        sys.stdout.write(("" if not seen or seen[-1].endswith("\n") else "\n") + listed(errors, keep))
    return status


if __name__ == "__main__":
    sys.exit(main())
