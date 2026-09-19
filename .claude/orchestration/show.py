#!/usr/bin/env python3
"""Print named lemmas, definitions and other named commands of the theories whole, with their proofs.

  show.py NAME [NAME ...]              every command of theories/ that introduces NAME
  show.py --in FILE [--in FILE] NAME   look in these theory files as well (candidates under .build/, say)
  show.py --statement NAME [NAME ...]  the same commands with their proofs left out (the planner's view)
  show.py --statements THEORY [...]    a theory's statements: every command, proofs and code left out

A theory's name may qualify NAME (Theory.name). The commands are cut out with the parser the loaded library's
digests use (digest.chunks), so a lemma comes with its whole proof, a definition with its equations and a
locale with its assumptions, each with its file and line, in one call.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from digest import GOAL, NAMED, chunks, held_text, split_goal  # noqa: E402

PROJECT = os.environ.get("ORCH_PROJECT") or os.path.dirname(os.path.dirname(HERE))
THEORIES = os.path.join(PROJECT, "theories")


def mentioning(name, extra):
    """Theory files whose text contains the name as a word: one grep over theories/, and the extra files."""
    out = subprocess.run(["grep", "-rlw", "--include=*.thy", "--", name, THEORIES], capture_output=True, text=True).stdout
    return sorted(set(out.split()) | {f for f in extra if os.path.exists(f)})


def introductions(path, name):
    """(line, command text) of every command in the file whose name is the given one."""
    text = open(path, errors="ignore").read()
    line, out = 1, []
    for cmd, lines in chunks(text):
        if cmd:
            m = NAMED.match(lines[0])
            if m and m.group(1) == name:
                out.append((line, "\n".join(lines).rstrip()))
        line += len(lines)
    return out


def main():
    args, extra, names, statement = sys.argv[1:], [], [], False
    if args[:1] == ["--statements"]:
        for theory in args[1:]:
            path = os.path.join(THEORIES, theory.removesuffix(".thy") + ".thy")
            if not os.path.exists(path):
                print(f"== {theory}: no such theory\n")
                continue
            print(f"== {os.path.relpath(path, PROJECT)}\n{held_text(path, 'statements')[0]}")
        return 0
    while args:
        a = args.pop(0)
        if a == "--in" and args:
            extra.append(os.path.abspath(args.pop(0)))
        elif a == "--statement":
            statement = True
        elif a.startswith("-"):
            print(__doc__)
            return 2
        else:
            names.append(a)
    if not names:
        print(__doc__)
        return 2
    missing = 0
    for full in names:
        theory, _, name = full.rpartition(".")
        files = mentioning(name, extra)
        if theory:
            files = [f for f in files if os.path.basename(f) == theory + ".thy"]
        found = [(f, line, text) for f in files for line, text in introductions(f, name)]
        if not found:
            missing += 1
            near = ", ".join(os.path.basename(f)[:-4] for f in files[:12]) or "none"
            print(f"== {full}: no command introduces it; theories mentioning it: {near}\n")
        for f, line, text in found:
            if statement:
                cmd = text.split(None, 1)[0]
                text = split_goal(text.splitlines())[0] if cmd in GOAL else text
            print(f"== {os.path.relpath(f, PROJECT)}:{line}\n{text}\n")
    return 1 if missing == len(names) else 0


if __name__ == "__main__":
    sys.exit(main())
