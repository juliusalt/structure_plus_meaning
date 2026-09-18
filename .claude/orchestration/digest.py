#!/usr/bin/env python3
"""The text of a source file that the base holds: what states its ideas, without its implementation.

A theory: every command verbatim — header, commentary, definitions, datatypes, locales and their assumptions,
interpretations, declarations, and the statements of all lemmas and theorems — with each proof replaced by a
comment giving its length (and, on request, the library facts it cites). ML bodies are replaced the same way.
At the coarser level "definitions" the lemmas and theorems are reduced to their names, in place, so that a
notion, its commentary and the list of what is proved about it stay in view at about half the size. A Python tool:
its module docstring, constants, signatures with docstrings, and command-line arguments.

This is a mechanical projection of the source, verbatim where it keeps anything; it adds no reading and
carries no authority. Anything to be edited, or whose proof matters, is read from the source itself.

usage: digest.py <file>            print the held text
       digest.py --measure <files>  one line per file: source and held size
"""
import ast
import glob
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PROJECT = os.path.dirname(os.path.dirname(HERE))

GOAL = {"lemma", "theorem", "corollary", "proposition", "schematic_goal", "function", "termination",
        "interpretation", "sublocale", "global_interpretation", "instance", "subclass", "typedef",
        "lift_definition", "quotient_type", "specification", "free_constructors", "bnf", "functor", "rep_datatype"}
CODE = {"ML", "ML_val", "ML_command", "setup", "local_setup", "method_setup", "attribute_setup", "simproc_setup",
        "parse_translation", "print_translation", "typed_print_translation", "declaration", "syntax_declaration", "oracle"}
TOP = GOAL | CODE | {
    "theory", "imports", "begin", "end", "chapter", "section", "subsection", "subsubsection", "paragraph",
    "subparagraph", "text", "text_raw", "definition", "abbreviation", "type_synonym", "datatype", "codatatype",
    "record", "fun", "primrec", "primcorec", "corec", "partial_function", "inductive", "inductive_set",
    "coinductive", "coinductive_set", "locale", "class", "context", "instantiation", "lemmas", "named_theorems",
    "declare", "notation", "no_notation", "type_notation", "no_type_notation", "syntax", "no_syntax",
    "translations", "no_translations", "consts", "axiomatization", "setup_lifting", "lifting_forget",
    "lifting_update", "code_printing", "code_identifier", "code_reserved", "code_datatype", "export_code",
    "value", "values", "ML_file", "SML_file", "hide_const", "hide_fact", "hide_type", "hide_class", "bundle",
    "unbundle", "open_bundle", "experiment", "notepad", "method", "print_theorems", "thm", "term", "typ", "prop",
    "find_theorems", "find_consts", "alias", "type_alias", "overloading", "adhoc_overloading",
    "no_adhoc_overloading", "nonterminal", "default_sort", "external_file", "generate_file",
    "export_generated_files", "compile_generated_files", "derive", "nitpick", "quickcheck"}
PROOF_START = {"proof", "by", "apply", "using", "unfolding", "supply", "including", "sorry", "oops", "done",
               "qed", ".", "..", "subgoal", "defer", "prefer"}
TOKEN = re.compile(r"\\<open>|\\<close>|‹|›|\(\*|\*\)|\"|[A-Za-z_][A-Za-z0-9_']*|\.\.|\.|\S")


def depth_after(line, depth, in_str, in_cmt):
    """Nesting of cartouches, strings and comments after a line."""
    for t in TOKEN.findall(line):
        if in_cmt:
            in_cmt += (t == "(*") - (t == "*)")
        elif in_str:
            in_str = t != '"'
        elif t == "(*":
            in_cmt = 1
        elif t == '"':
            in_str = True
        elif t in ("\\<open>", "‹"):
            depth += 1
        elif t in ("\\<close>", "›"):
            depth -= 1
    return depth, in_str, in_cmt


def command_of(line):
    words = line.split()
    while words and words[0] in ("private", "qualified"):
        words = words[1:]
    w = words[0] if words else ""
    return w if w in TOP else None


def chunks(text):
    """(command, lines) for each outer command, recognized only outside cartouches, strings and comments."""
    out, cur, cmd = [], [], None
    depth, in_str, in_cmt = 0, False, 0
    for line in text.splitlines():
        c = command_of(line) if depth == 0 and not in_str and not in_cmt else None
        if c:
            if cur:
                out.append((cmd, cur))
            cur, cmd = [], c
        cur.append(line)
        depth, in_str, in_cmt = depth_after(line, depth, in_str, in_cmt)
    if cur:
        out.append((cmd, cur))
    return out


def split_goal(lines):
    """Statement text and proof text of a goal command: the proof starts at the first proof keyword outside
    cartouches, strings and comments."""
    text = "\n".join(lines)
    depth, in_str, in_cmt, first = 0, False, 0, True
    for m in TOKEN.finditer(text):
        t = m.group(0)
        if in_cmt:
            in_cmt += (t == "(*") - (t == "*)")
        elif in_str:
            in_str = t != '"'
        elif t == "(*":
            in_cmt = 1
        elif t == '"':
            in_str = True
        elif t in ("\\<open>", "‹"):
            depth += 1
        elif t in ("\\<close>", "›"):
            depth -= 1
        elif depth == 0 and not first and t in PROOF_START:
            return text[:m.start()].rstrip(), text[m.start():]
        first = False
    return text.rstrip(), ""


_facts = None


def library_facts():
    """Names of every lemma, theorem and fact collection declared in theories/, and <constant>_def of every definition."""
    global _facts
    if _facts is None:
        _facts = set()
        named = re.compile(r"^\s*(?:private\s+|qualified\s+)?(?:lemma|theorem|corollary|proposition|lemmas|named_theorems)\s+(?:\([^)]*\)\s*)?([A-Za-z][A-Za-z0-9_']*)", re.M)
        defined = re.compile(r"^\s*(?:private\s+|qualified\s+)?(?:definition|abbreviation|fun|function|primrec|inductive)\s+(?:\([^)]*\)\s*)?([A-Za-z][A-Za-z0-9_']*)", re.M)
        for f in glob.glob(os.path.join(PROJECT, "theories", "*.thy")):
            t = open(f, errors="ignore").read()
            _facts.update(named.findall(t))
            _facts.update(n + "_def" for n in defined.findall(t))
        _facts -= {"assms", "that", "this"}
    return _facts


def cites(proof):
    """Library facts a proof names. Only compound names count: in this library facts are descriptive
    snake_case, while one-word matches are local labels and proof methods."""
    seen, out = set(), []
    for w in re.findall(r"[A-Za-z][A-Za-z0-9_']*", proof):
        if "_" in w and w in library_facts() and w not in seen:
            seen.add(w)
            out.append(w)
    return out


NAMED = re.compile(r"^\s*(?:private\s+|qualified\s+)?\w+\s+(?:\([^)]*\)\s*)?([A-Za-z][A-Za-z0-9_']*)")


def thy_digest(text, level="statements", with_cites=False):
    """level "statements": every command verbatim, proofs replaced by a comment.
    level "definitions": commentary, definitions, datatypes, locales and declarations verbatim; of the lemmas
    and theorems only their names, in place, so the notion and everything proved about it stay in view."""
    out, pending = [], []

    def flush():
        if pending:
            out.append("  (* proved here: " + ", ".join(pending) + " *)")
            pending.clear()

    for cmd, lines in chunks(text):
        if cmd in GOAL and level == "definitions" and cmd in ("lemma", "theorem", "corollary", "proposition", "schematic_goal"):
            m = NAMED.match(lines[0])
            pending.append(m.group(1) if m else "(unnamed)")
        elif cmd in GOAL:
            flush()
            stmt, proof = split_goal(lines)
            out.append(stmt)
            if proof:
                note = f"proof omitted: {proof.count(chr(10)) + 1} lines"
                c = cites(proof) if with_cites else []
                if c:
                    note += "; cites " + ", ".join(c[:8]) + (f", … {len(c) - 8} more" if len(c) > 8 else "")
                out.append(f"  (* {note} *)")
        elif cmd in CODE and len(lines) > 3:
            flush()
            out.append(lines[0])
            out.append(f"  (* code omitted: {len(lines) - 1} lines *)")
        else:
            flush()
            out.extend(lines)
    flush()
    return re.sub(r"\n{3,}", "\n\n", "\n".join(out)) + "\n"


def py_digest(text):
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return text
    src = text.splitlines()
    out = []
    doc = ast.get_docstring(tree)
    if doc:
        out += ['"""' + doc + '"""', ""]

    def signature(node, indent=""):
        first = src[node.lineno - 1:node.body[0].lineno - 1] or [src[node.lineno - 1]]
        head = " ".join(s.strip() for s in first)
        out.append(indent + head)
        d = ast.get_docstring(node)
        if d:
            out.append(indent + '    """' + d + '"""')

    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            signature(node)
        elif isinstance(node, ast.ClassDef):
            signature(node)
            for sub in node.body:
                if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    signature(sub, "    ")
        elif isinstance(node, ast.Assign) and all(isinstance(t, ast.Name) and t.id.isupper() for t in node.targets):
            out.append(src[node.lineno - 1][:160])
    args = [ln.strip() for ln in src if "add_argument(" in ln or "add_parser(" in ln]
    if args:
        out += ["", "# command line:"] + ["#   " + a[:200] for a in args]
    return "\n".join(out) + "\n"


def held_text(path, level="statements"):
    """(text the base holds for this file, whether it is a digest)."""
    text = open(path, errors="ignore").read()
    if path.endswith(".thy"):
        return thy_digest(text, level), True
    if path.endswith(".py"):
        return py_digest(text), True
    return text, False


if __name__ == "__main__":
    if sys.argv[1:2] == ["--measure"]:
        a = b = 0
        for p in sys.argv[2:]:
            t, _ = held_text(p)
            s = os.path.getsize(p)
            a += s
            b += len(t)
            print(f"{os.path.basename(p):46s} {s:7d} -> {len(t):7d} chars ({100 * len(t) // max(1, s)}%)")
        print(f"{'total':46s} {a:7d} -> {b:7d} chars ({100 * b // max(1, a)}%)")
    else:
        sys.stdout.write(held_text(sys.argv[1])[0])
