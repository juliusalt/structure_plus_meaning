#!/usr/bin/env python3
"""Some lines of a file, and what was left out of them: lines.py FILE NAME A-B[,C-D...] NOTE

A read of lines that are partly in the session's context already shows the rest and says what it left out (the owner,
2026-09-21: filter what is in context, rather than refuse the read or show it again). The guard rewrites such a read
into this (work_meter.filtered); each shown part is headed by its lines and the file's NAME (as the note names it), and
the note ends it.
"""
import sys


def main():
    path, name, spans, note = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4] if len(sys.argv) > 4 else ""
    try:
        lines = open(path, errors="ignore").read().splitlines()
    except OSError as e:
        print(f"{path}: {e.strerror}", file=sys.stderr)
        return 1
    for span in spans.split(","):
        a, b = (int(x) for x in span.split("-"))
        print(f"[lines {a}-{min(b, len(lines))} of {name}]")
        for i in range(a, min(b, len(lines)) + 1):
            print(lines[i - 1])
    if note:
        print(note)
    return 0


if __name__ == "__main__":
    sys.exit(main())
