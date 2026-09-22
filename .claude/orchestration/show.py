#!/usr/bin/env python3
"""Print named lemmas, definitions and other named commands of the theories whole, with their proofs.

  show.py NAME [NAME ...]              every command of theories/ that introduces NAME
  show.py --in FILE [--in FILE] NAME   look in these theory files as well (candidates under .build/, say)
  show.py --statement NAME [NAME ...]  the same commands with their proofs left out (the planner's view)
  show.py --statements THEORY [...]    a theory's statements: every command, proofs and code left out

A theory's name may qualify NAME (Theory.name), and a locale's (Locale.name: a fact stated in its `locale … begin` or
`context … begin` block, or by `lemma (in Locale)`), or an interpretation's prefix (prefix.name: the fact of the locale
it interprets). The commands are cut out with the parser the loaded library's
digests use (digest.chunks), so a lemma comes with its whole proof, a definition with its equations and a
locale with its assumptions, each with its file and line, in one call.
"""
import os
import re
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


BLOCK = ("locale", "context", "class", "instantiation", "overloading", "bundle", "experiment")
TARGET = re.compile(r"^\s*\w+\s+\(in\s+([A-Za-z_][\w.]*)\)")
PREFIX = re.compile(r"\b(?:sublocale|interpretation|global_interpretation|interpret)\s+([A-Za-z_][\w]*)\s*:\s*"
                    r"([A-Za-z_][\w.]*)")


def introductions(path, name, within=None):
    """(line, command text) of every command in the file whose name is the given one — with `within`, only those stated
    in one of those locales: in its `locale … begin` or `context … begin` block, or by `lemma (in L)`."""
    text = open(path, errors="ignore").read()
    line, out, stack, opened = 1, [], [], None
    for cmd, lines in chunks(text):
        if cmd in BLOCK:
            m = re.match(r"\s*\w+\s+([A-Za-z_][\w.]*)", lines[0])
            owner = m.group(1) if m and cmd in ("locale", "context", "class") and m.group(1) != "begin" else None
            if re.search(r"\bbegin\s*$", "\n".join(lines)):
                stack.append(owner)
            else:
                opened = (owner,)  # its `begin` is the next command, if it has a block
        elif cmd == "begin" and opened:
            stack.append(opened[0])
        elif cmd == "end" and stack:
            stack.pop()
        if cmd not in BLOCK:
            opened = None
        if cmd:
            m = NAMED.match(lines[0])
            target = TARGET.match(lines[0])
            owner = target.group(1) if target else (stack[-1] if stack else None)
            if m and m.group(1) == name and (within is None or owner in within):
                out.append((line, "\n".join(lines).rstrip()))
        line += len(lines)
    return out


def interpreted(prefix, extra):
    """The locales an interpretation (or a sublocale) named `prefix` interprets: prefix.name is their fact name."""
    files = mentioning(prefix, extra)
    return {m.group(2) for f in files for m in PREFIX.finditer(open(f, errors="ignore").read()) if m.group(1) == prefix}


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
        # a qualifier is a theory where a theory has that name, else a locale or an interpretation's prefix: brief-230's
        # store_found_program.any_exact was looked for in a theory store_found_program, and "no command introduces it;
        # theories mentioning it: none" said of five locale facts (19 such names in 12 sessions of 2026-09-22)
        *quals, name = full.split(".")
        is_theory = lambda q: os.path.exists(os.path.join(THEORIES, q + ".thy")) or any(
            os.path.basename(f) == q + ".thy" for f in extra)
        theory = next((q for q in quals if is_theory(q)), None)
        scopes = [q for q in quals if q != theory]
        every = mentioning(name, extra)
        files = [f for f in every if os.path.basename(f) == theory + ".thy"] if theory else every
        within, said = None, ""
        if scopes:
            within = {scopes[-1]} | interpreted(scopes[-1], extra)
            if within != {scopes[-1]}:
                said = (f" ({scopes[-1]} interprets {', '.join(sorted(within - {scopes[-1]}))}: {name} is "
                        f"{'its' if len(within) == 2 else 'their'} fact)")
        found = [(f, line, text) for f in files for line, text in introductions(f, name, within)]
        if not found:
            missing += 1
            near = ", ".join(os.path.basename(f)[:-4] for f in every[:12]) or "none"
            print(f"== {full}: no command introduces it"
                  + (f" in {' or '.join(sorted(within))}" if within else "")
                  + f"; theories mentioning {name}: {near}\n")
        for f, line, text in found:
            if statement:
                cmd = text.split(None, 1)[0]
                text = split_goal(text.splitlines())[0] if cmd in GOAL else text
            print(f"== {os.path.relpath(f, PROJECT)}:{line}{said}\n{text}\n")
    return 1 if missing == len(names) else 0


if __name__ == "__main__":
    sys.exit(main())
