#!/usr/bin/env python3
"""A check run to its end, which ends by listing every error it reported: check_errors.py [--watch PATH]...
[--keep DIR] [--note TEXT] -- COMMAND...

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
nobody but by reading the logs one by one). A list longer than ROOM is kept whole in DIR and named. TEXT, what the guard
changed of the command (work_meter.forked), is said after the output, before the list. It ends with the check's own
status.
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


DETAIL_LINES = 10  # of a message's own lines under its first: a proof's goal, a type error's term and type


SESSION = re.compile(r"^Running (\S+) \.\.\.", re.M)
TIMED_OUT = re.compile(r"^\*\*\* Timeout\s*$", re.M)
NAMED = 6  # the unfinished theories named on a timeout's line; the rest counted


def isabelle_homes():
    """Where the proofs' Isabelle homes are: the harness's places (v2.places), or ORCH_ISABELLE_HOMES."""
    named = os.environ.get("ORCH_ISABELLE_HOMES")
    if named:
        return named.split(os.pathsep)
    try:
        import v2
        return [v2.places()[1], v2.OLD_HOME]
    except Exception:  # a harness that cannot be read leaves a timeout as Isabelle says it
        return []


def unfinished(text):
    """The theories a proof's session left unfinished when its time ran out: its sources without the markup Isabelle
    exports when a theory ends, from the session's log database; None for a text with no timeout or no database. Isabelle
    says `*** Timeout` and names no theory: the batch of tasks 227 and 223 ran its 1,200 s out (2026-09-22 18:40) on
    three native-control theories, and its report named nothing a task changed, nor anything its sessions could fix."""
    m = SESSION.search(text)
    if not m or not TIMED_OUT.search(text):
        return None
    import glob
    import sqlite3
    for home in isabelle_homes():
        for db in glob.glob(os.path.join(home, ".isabelle", "*", "heaps", "*", "log", m.group(1) + ".db")):
            try:
                with sqlite3.connect(f"file:{db}?mode=ro", uri=True) as c:
                    ended = {t.split(".", 1)[-1] for (t,) in c.execute(
                        "select distinct theory_name from isabelle_exports where name = 'PIDE/markup'")}
                    names = [os.path.splitext(os.path.basename(n))[0] for (n,) in c.execute(
                        "select name from isabelle_sources")]
            except sqlite3.Error:
                continue
            if names:  # a session's sources are written when it ends: none, and it has not
                return sorted(n for n in names if n not in ended)
    return None


def detailed(text):
    """Every error message in a text: (`FILE:LINE: its first line`, the lines under it), where the message says where.
    Isabelle's message is a run of `***` lines ending, in a theory, with `At command "…" (line N of "…")`, which is
    where it stands (its first line may name an ML file); two messages side by side without it part where a line of
    its own names a place. The lines under the first are what fixing it needs — a failed proof's goal, a type
    error's term and type — which fix-220 read from the probe's log after each list (requests 8 and 10, 2026-09-22)."""
    out, message, cut = [], [], set()

    def close():
        if message:
            if message[0].startswith("  "):  # a message whose beginning the log's own limit cut off ("...")
                cut.add(len(out))
            lines = [x.strip() for x in message]
            places = [m for m in map(WHERE.search, lines) if m]
            place = next((m for line, m in zip(lines, map(WHERE.search, lines)) if m and line.startswith("At command")),
                         places[0] if places else None)
            first = WHERE.sub("", lines[0]).rstrip(":").strip() or " ".join(lines)[:120]
            under = [x.rstrip()[1:] if x.startswith(" ") else x.rstrip() for x in message[1:]
                     if x.strip() and not x.strip().startswith("At command")]
            out.append(((f"{os.path.basename(place.group(2))}:{place.group(1)}: " if place else "") + first[:160],
                        [WHERE.sub("", x)[:200] for x in under[:DETAIL_LINES]]
                        + ([f"… ({len(under) - DETAIL_LINES} lines more)"] if len(under) > DETAIL_LINES else [])))
            message.clear()
    trace = False  # after a message's command: the commands it was reported through, an importing theory's ML
    for line in text.splitlines():
        if not line.startswith("***"):
            close()
            trace = False
            continue
        body = line[3:]
        if trace and (not body.strip() or body.strip().startswith("At command")):
            continue  # one failure, not another: task 223's proof came again through two theories' `ML` (2026-09-22)
        trace = False
        if message and not body.startswith("  ") and WHERE.search(body) and not body.strip().startswith("At command") \
                and any(WHERE.search(x) for x in message):
            close()
        message.append(body)
        if body.strip().startswith("At command"):
            close()
            trace = True
    close()
    whole = {e.split(": ", 1)[0] for i, (e, _) in enumerate(out) if i not in cut}
    out = [(e, d) if i not in cut else ("(its beginning cut off in the log) " + e, d)
           for i, (e, d) in enumerate(out) if i not in cut or e.split(": ", 1)[0] not in whole]
    late = unfinished(text) if any(e == "Timeout" for e, _ in out) else None
    if late:
        said = (f"Timeout: the proof's session ran out of its time with {len(late)} theor{'ies' if len(late) > 1 else 'y'}"
                f" unfinished: {', '.join(late[:NAMED])}" + (f" and {len(late) - NAMED} more" if len(late) > NAMED else ""))
    elif late is not None:  # task 227's check, 19:01: all 106 theories ended, their commands in 598 s of 1,200
        said = ("Timeout: every theory of the proof's session ended, and the session still ran out of its time: a proof "
                "forked from its theory, which the session joins only at its end, did not finish — a probe with "
                "IN_PLACE=1 stops at it")
    if late is not None:
        out = [(said, (late or [])[NAMED:]) if e == "Timeout" else (e, d) for e, d in out]
    return out


def errors_in(text):
    """Every error message in a text, one line each: `FILE:LINE: its first line` (detailed, without what is under it)."""
    return [head for head, _ in detailed(text)]


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


def keep_whole(errors, keep, details):
    """The whole list, each error with its lines, kept in `keep` (the newest KEEP of them): its path, or None."""
    if not keep:
        return None
    try:
        os.makedirs(keep, exist_ok=True)
        n = 1 + max((int(f[7:-4]) for f in os.listdir(keep) if re.fullmatch(r"errors-\d+\.txt", f)), default=0)
        path = os.path.join(keep, f"errors-{n}.txt")
        open(path, "w").write("".join(f"- {e}\n" + "".join(f"    {d}\n" for d in details.get(e) or []) for e in errors))
        for old in sorted(int(f[7:-4]) for f in os.listdir(keep) if re.fullmatch(r"errors-\d+\.txt", f))[:-KEEP]:
            os.remove(os.path.join(keep, f"errors-{old}.txt"))
        return path
    except OSError:
        return None


def listed(errors, keep, details=None):
    """The list the check ends with: every error's line, and under each what fixing it needs (`details`: its lines by
    error) while room is left, in order; whole when it fits, else what fits and where the whole is kept."""
    details = details or {}
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
        left, shown, dropped = ROOM - size - 200, [], 0  # the goals under the lines, while room is left
        for e, line in zip(errors, lines):
            under = "".join(f"    {d}\n" for d in details.get(e) or [])
            if under and len(under.encode()) <= left:
                left -= len(under.encode())
                line += under
            elif under:
                dropped += 1
            shown.append(line)
        if not dropped:
            return head + "".join(shown)
        where = keep_whole(errors, keep, details)
        return head + "".join(shown) + (f"[the goals of {dropped} more are kept in {where}]\n" if where else
                                        f"[{dropped} more have lines under them not shown here]\n")
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
    note = next((args[i + 1] for i in range(split - 1) if args[i] == "--note"), None)
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
    found = detailed(output) + [e for _, text in logs_read for e in detailed(text)]
    details = {}
    for e, under in found:
        details.setdefault(e, under)
    errors = [e for e, _ in found]
    if status:  # a failed check says what else failed; one that passed has nothing to fix
        errors += failures(output, logs_read)
    errors = list(dict.fromkeys(errors))  # one message in the output and in a log is one error
    ended = not seen or seen[-1].endswith("\n")
    if note:
        sys.stdout.write(("" if ended else "\n") + note + "\n")
        ended = True
    if errors:
        sys.stdout.write(("" if ended else "\n") + listed(errors, keep, details))
    return status


if __name__ == "__main__":
    sys.exit(main())
