#!/usr/bin/env python3
"""The guards of every role, and what a session reads and produces.

  work_meter.py guard   PreToolUse hook: refuse what a role may not do
  ctx_gauge.py gauge calls record() after every tool call of a working session.

The planner, the task designer, the knowledge base and consultations of it read statements, not details: theory
sources only through `show.py --statement(s)` or `v2.py read`, never proof text, code bodies, logs or diffs;
listing names (ls, find, `git log` without patches) is free. The task graph is edited only by the planner and
the task designer.

Every working session produces. Production is a change to its role's deliverables (v2.deliverables_of: a producing
session's files under its brief's Deliverable and its drafts under .build/tasks/ID/; the task designer's briefs and
TaskCreate or TaskUpdate; the reviewer's verdict; the planning episode's HANDOFF.md, notes and graph edits; a
consultation's reply) that adds or changes content: in a theory a command (definition, statement, locale, proof)
added or changed, its comments and layout aside, or COMMENTARY_WORDS words of commentary; in a document PROSE_WORDS
words added or rewritten; in code CODE_LINES non-blank, non-comment lines.

Reading is limited in two tiers (the owner, 2026-09-21), counted in reads, and a read is a batch: one request,
however many reads it holds — that is the point of batching — and it reads at most BATCH bytes, past which the rest of
the batch is refused, so that no batch reads everything. Each call in it shows at most READ_BYTES: a read of a file's
lines longer than that is refused with the lines that fit named, and every other call's output — a search, a script,
a check — is cut there, its whole output kept in a file under .build/outputs/ to be read on by its lines (cut.py).
Between two production events a session may make ROUNDS reads; past that, each read draws one from a reserve of
RESERVE, and each production restarts the first tier and gives one back to the reserve, never beyond RESERVE. Writing,
asking, parking and a refused read count for nothing (reading_requests). When both tiers are spent, reads, searches and
checks are refused, and what remains is to produce, to ask, or to record what it has; after every read, search or
check the session is told what it has left in both. Reading was also bounded in tokens until the owner had it taken
out (2026-09-21): every read being bounded in bytes, the tokens bound nothing the bytes did not. Replayed on impl-8 to impl-30 (421 stretches between writes, 2,334 requests that read, searched or checked), 3
rounds would have bound in 42% of the stretches and held back 68% of those requests, 6 rounds in 30% and 47%
(measured before the reserve).

A check that fails with the same failure (theory, line, error) after a fix, CIRCLING times in a row, stops further
checks until an answer on the obstruction has come. Failures that move are progress. A check runs to its end and ends
by listing every error it reported (check_errors.py). Waiting is refused (sleep, wait loops, `tail -f`, reading a background job's output before its
completion notice), and so are subagents. A read of lines partly in the session's context and unchanged since shows the
rest and says what it left out; one wholly in context shows only that, and counts as no read (nothing is ever cleared
from its context). Files are changed with `v2.py change` alone. A quick fix has its own budget: FIX_MINUTES minutes and
FIX_ROUNDS rounds from its start. A session has Bash, TaskCreate, TaskUpdate and TaskStop; every other tool is refused
(REMOVED_TOOLS).
"""
import collections
import contextlib
import fcntl
import hashlib
import shlex
import json
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import v2  # noqa: E402
from digest import chunks  # noqa: E402

STATE = v2.STATE
ROUNDS, RESERVE, CIRCLING = v2.ROUNDS, v2.READ_RESERVE, v2.CIRCLING
BATCH, READ_BYTES = v2.BATCH_BYTES, v2.READ_BYTES
# A call may say how much of it it wants shown, at most the batch's: `SHOW=20K grep …` (the owner, 2026-09-22: let the
# model declare the maximum it wants from each read). At READ_BYTES alone design-171 spent 6 of its 46 requests reading
# on outputs cut at 5K, a request each (~70K) where showing the rest cost a few thousand. The assignment is the shell's
# own and changes nothing of what runs.
SHOW = re.compile(r"^(\s*(?:cd\s+[^;&|\n]+?\s*&&\s*)?)SHOW=(\d+)([kK]?)\s+")
BATCH_WAIT = float(os.environ.get("ORCH_BATCH_WAIT", 0.5))  # how long the guard waits to see its call written
READING = ("read", "check", "other")  # the kinds of call that are reads, which the limits hold
# the commands that write files by name: WRITE_SHELL knows them as writes and write_targets finds what they write
FILE_WRITERS = ("rm", "rmdir", "touch", "truncate", "mkdir", "ln", "chmod", "mv", "cp", "install", "tee")
PROSE_WORDS, COMMENTARY_WORDS, CODE_LINES = 40, 40, 5
FIX_MINUTES, FIX_ROUNDS = v2.FIX_MINUTES, v2.FIX_ROUNDS
READ_LINES = 2_000  # what a Read without a limit shows at most
CODE = (".py", ".sh", ".ML", ".sml", ".js")
COMMENTARY = {"text", "text_raw", "chapter", "section", "subsection", "subsubsection", "paragraph", "subparagraph"}
GUARD_QUIET = v2.GUARD_QUIET  # how often a failing guard is said; the harness's one interval for such a failure
SED = re.compile(r"""^sed\s+-n\s+(['"]?)(\d+),(\d+)p\1\s+(\S+)$""")
CAT = re.compile(r"^cat\s+(\S+)$")
HEAD = re.compile(r"^head\s+(?:-n\s*|-)(\d+)\s+(\S+)$")
TAIL = re.compile(r"^tail\s+(?:-n\s*|-)(\d+)\s+(\S+)$")
# What the shell itself does, read on the command with its heredoc bodies and quoted words removed: a grep pattern
# holding `>>`, or a theory's \<open>, is data and not a redirection (2026-09-20).
# A command inside a loop or a condition is a command all the same: task 56's `for f in …; do cp … theories/$f.thy;
# done` read as `do`, no write, and four theories went into the tree another task held (2026-09-22).
SHELL_KEYWORDS = ("do", "then", "else", "elif", "if", "while", "until", "!", "{", "time")
WRITE_SHELL = re.compile(r"\bsed\s+-i\b|(?<![0-9&])>>?\s*(?!/dev/null\b|&)[^\s|;&>]+|\btee\s+(?:-a\s+)?[^\s|;&]+"
                         r"|(?:^|[;&|(]\s*)(?:(?:do|then|else|elif|if|while|until|!|\{|time)\s+)*(?:"
                         + "|".join(w for w in FILE_WRITERS if w != "tee") + r")\s")
# What a script inside the command writes, named where it writes it
WRITE_SCRIPT = re.compile(r"""\.write_text\(|\.writelines\(|shutil\.(?:copy|move)|open\(\s*[^)]*['"][wa]""")
HEREDOC = re.compile(r"<<-?\s*(['\"]?)(\w+)\1\r?\n.*?^\s*\2\s*$", re.S | re.M)
QUOTED = re.compile(r"'[^']*'|\"[^\"]*\"")
REDIRECT = re.compile(r"""(?<![0-9&])>>?\s*(?:'([^']+)'|"([^"]+)"|([^\s|;&>]+))""")
# a path a script inside the command writes to, named literally
SCRIPT_TARGET = re.compile(r"""(?:Path\(\s*|open\(\s*)['"]([^'"]+)['"]\s*\)?\s*(?:\.\s*write_text|\.\s*open\(\s*['"][wa])"""
                           r"""|open\(\s*['"]([^'"]+)['"]\s*,\s*['"][wa]""")
# and by a name a literal path was given first (`p='.build/tasks/26/result.md'; … open(p, 'w')`): implement-26 and
# fix-97.2 were refused their own result's edit as a script whose target could not be read (2026-09-22)
SCRIPT_NAMED = re.compile(r"""open\(\s*(\w+)\s*,\s*['"][wa]|\b(\w+)\.write_text\(|Path\(\s*(\w+)\s*\)\s*\.\s*write_text""")
PY_ASSIGN = re.compile(r"""^[ \t]*(\w+)\s*=\s*(?:Path\(\s*)?['"]([^'"\n]+)['"]""", re.M)
# Every place a script writes, by the expression it writes to: open(EXPR, 'w…'), Path(EXPR).write_text/bytes,
# NAME.write_text/bytes. Where the expression is made at run time its fixed beginning is read (script_writes).
WRITE_SITE = re.compile(r"""open\(\s*([^,()\n]+?)\s*,\s*['"][wax]b?\+?['"]"""
                        r"""|Path\(\s*([^()\n]+?)\s*\)\s*\.\s*write_(?:text|bytes)\("""
                        r"""|\b(\w+)\s*\.\s*write_(?:text|bytes)\("""
                        r"""|\(\s*(\w+)\s*/[^()\n]*\)\s*\.\s*write_(?:text|bytes)\(""")
# a name given the temporary directory, or a path made from it or from a literal: `T=os.environ['TMPDIR']+'/mf'`
PY_PREFIX = re.compile(r"""^[ \t]*(\w+)\s*=\s*(?:Path\(\s*)?(os\.environ\[['"]TMPDIR['"]\]|os\.environ\.get\(\s*['"]TMPDIR['"][^)]*\)"""
                       r"""|os\.getenv\(\s*['"]TMPDIR['"][^)]*\)|tempfile\.gettempdir\(\s*\)|f?['"][^'"\n]*['"])\s*(.*)$""", re.M)


# Isabelle's symbols and cartouches (\<open>, \<close>, \<exists>, \<Rightarrow>): `\<` is no shell syntax and the
# `>` that closes one is no redirection. Theory text that reaches this parser outside a heredoc it could strip — an
# indented delimiter is enough — otherwise names one file per cartouche, and named 116 of the 123 entries the tree's
# ownership held on 2026-09-20: `a`, `q.`, `lemma`, `The`, the word after every `\<open>`.
ISABELLE_SYMBOL = re.compile(r"\\<[A-Za-z][A-Za-z0-9_^]*>")


def shell_syntax(command):
    """The command as the shell reads it: a heredoc body is data, an Isabelle symbol is data, and so is a quoted word
    — unless a redirection is what precedes it, so that `grep '>>'` names nothing while `> "a file"` still names its
    file (2026-09-20)."""
    text, kept, i = ISABELLE_SYMBOL.sub(" ", HEREDOC.sub(" <<heredoc ", command or "")), [], 0
    # a comparison in arithmetic or a test is no redirection, and `&>` writes the output and its errors both
    text = re.sub(r"&>", " >", re.sub(r"\$?\(\([^()]*\)\)|\[\[.*?\]\]", " ", text))
    for m in QUOTED.finditer(text):
        kept.append(text[i:m.start()])
        kept.append(m.group(0) if kept[-1].rstrip().endswith(">") else " ")
        i = m.end()
    kept.append(text[i:])
    return "".join(kept)


def redirections(command):
    """The targets of the command's redirections."""
    return [m for match in REDIRECT.findall(shell_syntax(command)) for m in match if m]


# git commands that change the index, the working tree or the history: the finalizer's alone
GIT_MUTATE = re.compile(r"\bgit\s+(?:-[Cc]\s+\S+\s+)*(?:add|commit|checkout|reset|restore|rm|mv|merge|rebase|push|pull"
                        r"|clean|switch|cherry-pick|revert|apply|am|update-index|update-ref|gc|prune|filter-branch"
                        r"|replace|branch\s+-[dDmMfc]"
                        # their reading forms stand: a stash's list and show, the worktrees', the tags', a note shown
                        r"|stash(?!\s+(?:list|show)\b)|worktree(?!\s+list\b)|notes(?!\s+(?:show|list)\b)"
                        r"|tag\s+(?!-l\b|--list\b|-n\d*\b|--contains\b|--points-at\b)[^\s|;&]+)(?![\w-])")
# (?![\w-]): `git merge-base` is a read, and \b let `merge` match it — refused four times, in four sessions, 2026-09-21
READS = re.compile(r"^\s*(?:cd\s+[^;&|]+&&\s*)?(?:sed\s+-n|cat|head|tail|grep|rg|find|ls|wc|awk|nl|less|more"
                   r"|git\s+(?:show|log|diff|status|grep|blame)|(?:python3?\s+)?\S*show\.py)\b")
CHECK_TOOL = re.compile(r"(?:^|/)(?:probe_theories|incremental_check|replay_development_answers)\.py$|(?:^|/)tools/build\.py$")
PREFIXES = ("timeout", "nice", "nohup", "env", "time", "command", "exec", "stdbuf")


def programs(command):
    """(program, words) of each simple command the shell runs, past the prefixes that run another (`timeout 600 env
    X=1 isabelle …`)."""
    for words in segments(shell_syntax(command)):
        while words and os.path.basename(words[0]) in PREFIXES:  # a prefix, its options and assignments
            words = words[1:]
            while words and (words[0].startswith("-") or re.match(r"^\w+=", words[0]) or re.match(r"^\d+[smhd]?$", words[0])):
                words = words[1:]
        if words:
            yield os.path.basename(words[0]), words


INTERPRETERS = ("python", "perl", "ruby", "node")


def runs_script(command):
    """Whether the command runs an interpreter, whose script may write: `grep -n "shutil.copy" tools/…` was taken for a
    script that writes, its pattern read as code (investigate-82, 2026-09-22)."""
    return any(prog.startswith(INTERPRETERS) for prog, _ in programs(command))


def runs_check(command, cwd=None):
    """Whether a command runs a check: a check's tool as the program it runs (by a runner, or by its path), or
    `isabelle build|process|ML_process` — not a read of the tool's text, nor its help. Named anywhere in the command,
    `grep … tools/incremental_check.py`, `sed … tools/probe_theories.py`, `probe_theories.py --help` and a script
    reading a check's output directory were checks, refused while the machine was full (fix-81, implement-56, fix-80.2:
    six requests, 2026-09-21). A heredoc naming a tool is prose; a replay is a heavy run, and a check here too. A shell
    script the command runs from a file is read as part of it (scripts_run)."""
    return any(checks_here(text) for text in (command, *scripts_run(command, cwd)))


def repository_check(command):
    """Whether a command runs the repository's check (`tools/incremental_check.py check`), which the harness runs in
    batches for a session in its own tree (v2.cmd_check, train.Batch)."""
    for prog, words in programs(command):
        script = next((w for w in words[1:] if not w.startswith("-")), "") if prog.startswith("python") else words[0]
        if script.endswith("incremental_check.py") and "check" in words[words.index(script) + 1:words.index(script) + 2]:
            return True
    return False


def batches_on():
    import train
    return train.BATCHES


def checks_here(command):
    """runs_check within the command's own text."""
    for prog, words in programs(command):
        script = next((w for w in words[1:] if not w.startswith("-")), "") if prog.startswith("python") else words[0]
        if CHECK_TOOL.search(script) and not {"--help", "-h"} & set(words):
            return True
        if prog == "isabelle" and len(words) > 1 and words[1] in ("build", "process", "ML_process"):
            return True
    return False


SHELLS = ("bash", "sh", "zsh", "dash", "source", ".")
SYSTEM_DIRS = ("/usr/", "/bin/", "/sbin/", "/opt/", "/etc/", "/nix/")


def scripts_run(command, cwd=None, depth=2):
    """The text of each shell script a command runs from a file — `bash FILE`, `source FILE`, or a file run by its path
    (`.build/tasks/76/runprobe.sh`) — and of the scripts those run, `depth` deep. implement-76 put its probe in a
    script of its own and ran it as `bash .build/tasks/76/runprobe.sh …` (2026-09-22): read from the command alone that
    was no check — its change and the probe after it refused in one call, and a probe run so was one the machine's
    limits and a measurement's claim of the whole machine did not reach. Only what a check is, and the kind and
    bound of the run it makes, are read from here; where a script writes is read as before (write_targets)."""
    base, known = shell_context(command, cwd)
    texts = []
    for prog, words in programs(command):
        if prog in SHELLS:
            if "-c" in words[1:]:
                continue  # the script is the command's own text
            name = next((x for x in words[1:] if not x.startswith("-")), None)
        elif "/" in words[0]:
            name = words[0]
        else:
            continue
        if not name:
            continue
        path = os.path.normpath(os.path.join(base, os.path.expanduser(re.sub(
            r"\$\{?(\w+)\}?", lambda m: known.get(m.group(1), m.group(0)), name.strip("'\"")))))
        if path.startswith(SYSTEM_DIRS):
            continue
        try:
            if not os.path.isfile(path) or os.path.getsize(path) > 200_000:
                continue
            with open(path, errors="ignore") as f:
                text = f.read()
        except OSError:
            continue
        if prog not in SHELLS and not path.endswith(".sh") and not re.match(r"#!(?:\S*/)?(?:env\s+)?(?:ba|z|da)?sh\b",
                                                                              text):
            continue  # run by its path, a program of another language: its tool, if a check's, is the program
        texts.append(text)
        if depth > 1:
            texts += scripts_run(text, base, depth - 1)
    return texts
WAIT = re.compile(r"\bsleep\s+(?:[2-9]|\d{2,}|\d+[smh])|\btail\s+-[a-zA-Z]*f\b|\bwatch\s|\b(?:until|while)\b[^;]*;\s*do\b[^;]*\bsleep\b")
RUNNERS = ("python", "python3", "sh", "bash", "env")
# What the planner does not read: theory and code bodies, logs, and under .build anything but the tasks' documents.
# a task tree's own documents too (.build/trees/N/DECISIONS.md): plan-37, judging design 85, was refused its entry in
# the design's tree, seven reads of one request (2026-09-22 06:21)
# a planner's notes (.build/plans/plan-N/*.md) are no body: the planner reads statements alone, so what it writes is
# statements too — brief-230 was refused the note plan-45 had sent it by its path, twice (2026-09-22 16:34)
BODY = re.compile(r"\.(?:thy|ML|sml|py|sh|log|out|output)$|(?:^|/)(?:theories|tools)(?:/|$)|(?:^|/)\.build(?:/|$)"
                  r"(?!tasks/[^/]+/[^/]+\.md$|outputs/|trees/[^/]+/[^/]+\.md$|plans/[^/]+/[^/]+\.md$"
                  r"|tasks/[^/]+/(?:brief|finalize|finalized|active-context)\.json$)")
# the harness's records of a task (its brief, its hand-over, its outcome) and the base's pointer are no body either: they
# are the planner's to read — plan-43 was refused task 128's outcome after the reboot, and plan-44 which base stood
# (2026-09-22 13:08, 15:10)
CONTENT = {"cat", "sed", "head", "tail", "grep", "egrep", "fgrep", "rg", "awk", "nl", "less", "more", "bat", "diff",
           "strings", "xxd", "od", "cut", "sort", "uniq", "jq", "tac"}
PATTERNED = {"grep", "egrep", "fgrep", "rg", "sed", "awk"}  # their first operand is a pattern or a script
STAT = re.compile(r"--(?:stat|shortstat|numstat|name-only|name-status|summary)\b")
PATCH = re.compile(r"(?:^|\s)(?:-p|-u|--patch|-L\S*|--word-diff\S*|--full-diff)(?:\s|$)")


CHANGE_VERB = re.compile(r"\bv2\.py\s+change\b")
# the one form of a change: its changes in a quoted heredoc of the same call, and nothing else in it but a leading cd
# the runner of a harness command, by name or by path and with its flags, as own_command reads it: `/usr/bin/python3
# …/v2.py again 6` was refused as out of form while every other check took it for the session's own (ask-q23, 2026-09-21)
RUNNER_ARG = r"(?:(?:\S*/)?python3?(?:\s+-[A-Za-z]+)*\s+)?"
CHANGE_POINTER = ("Files are changed with `.claude/orchestration/v2.py change <<'EOF'` … `EOF`: any number of changes "
                  "to any number of files in one call — `=== write PATH` and the whole file, or `=== replace PATH` and "
                  "blocks of `<<<<<<< SEARCH`, the text as it stands, `=======`, its replacement, `>>>>>>> REPLACE` — "
                  "judged whole, written all or none, and what refuses it said.")


# What follows a change runs only if it went through. Not `status`: Claude Code runs a session's command in zsh, where
# `status` is $? itself and read-only — the line failed there on every call that went on after a change ("(eval):42:
# read-only variable: status"), 157 times from 2026-09-21 23:08 to 2026-09-22 10:40, each redone alone, while the tests
# ran the rewritten commands in bash (brief-142 said "the shell wrapper failed again after the change").
STATUS_LINE = 'orch_rc=$?; [ "$orch_rc" -eq 0 ] || exit "$orch_rc"'

# A change may stand in a call with any other commands, each judged as it would be alone, and what follows a change runs
# only if it went through (the owner, 2026-09-22: "why not allow any batch of commands in general"). Until then a call
# held its change and at most the harness's inert commands or one check after it, and sessions lost requests to reads,
# removals and preparations joined to their changes — nine refusals of the form on the night of 2026-09-21/22.
CHANGE_OPEN = re.compile(RUNNER_ARG + r"\S*v2\.py\s+change\s*<<(-?)\s*(['\"]?)(\w+)\2")
ANY_HEREDOC = re.compile(r"<<(-?)\s*(['\"]?)(\w+)\2")
CD_BY_SEMICOLON = re.compile(r"(?:^|&&|;|\n)\s*cd\s+([^;&|\n]+?)\s*(?:;|\n)\s*$")


class ChangeParts(collections.namedtuple("ChangeParts", "changes rest")):
    """A call's changes — each (the text before it in the call, whether its delimiter is quoted, its text) — and the
    rest of the call with each change and its heredoc replaced by `true`, to be judged as any command is."""


def change_parts(command):
    """The changes of a call that makes one or more with `v2.py change`, and the rest of it (ChangeParts), or None.
    A heredoc of another command in the call is the rest's own; a change is a `v2.py change` whose heredoc opens on its
    line."""
    if not command or not CHANGE_VERB.search(shell_syntax(command)) or not own_command(command):
        return None
    lines, out, changes, i = command.split("\n"), [], [], 0
    while i < len(lines):
        line = lines[i]
        opened = {m.end(): m for m in CHANGE_OPEN.finditer(line)}
        docs = [(m, opened.get(m.end())) for m in ANY_HEREDOC.finditer(line)]
        kept = line
        for m, change in reversed(docs):
            if change:
                kept = kept[:change.start()] + "true" + kept[m.end():]
        out.append(kept)
        i += 1
        for m, change in docs:
            body = []
            while i < len(lines) and (lines[i].lstrip("\t") if m.group(1) else lines[i]).rstrip() != m.group(3):
                body.append(lines[i])
                i += 1
            closing = lines[i] if i < len(lines) else None
            i += 1
            if change:
                changes.append(("\n".join(out[:-1] + [line[:change.start()]]), bool(m.group(2)), "\n".join(body)))
            else:
                out.extend(body + ([closing] if closing is not None else []))
    return ChangeParts(changes, "\n".join(out)) if changes else None


QUEUE_ASKED = re.compile(r"(^|[\s;&|(])QUEUE=1\s+")


def queued_probe(command, run, rec):
    """The call a probe refused for the machine becomes when its session marked it QUEUE=1 (it has nothing else to do
    until it has run): its changes as they are, then `v2.py queue-probe` with the probe, which is queued and run as soon
    as the machine has room while the session is parked (v2.cmd_queue_probe, v2.run_queued_probes). None otherwise."""
    if run != "probe" or rec.get("role") not in v2.PRODUCING or not QUEUE_ASKED.search(HEREDOC.sub(" ", command)):
        return None
    kept = through_changes(command)
    rest = command[len(kept):].lstrip("\n") if kept else command
    rest = QUEUE_ASKED.sub(r"\1", rest)
    if not rest.strip() or kind("Bash", {"command": rest}) != "check" or v2.run_kind(rest) != "probe":
        return None
    import base64
    call = (f"{shlex.quote(sys.executable)} -B {shlex.quote(os.path.join(HERE, 'v2.py'))} queue-probe "
            f"{base64.b64encode(rest.encode()).decode()}")
    return (kept + "\n" + STATUS_LINE + "\n" + call) if kept else call


def through_changes(command):
    """The call up to the end of its last change, when every check it holds comes after that: a check refused for the
    machine then takes nothing with it. The whole call was refused, its changes too: implement-189, implement-182 and
    fix-227 each learned so only by looking, and fix-227 spent three requests on it (2026-09-22, 17:21–17:30, while
    task 220 waited to measure). None when the call holds no change, or a check before its last."""
    if not change_parts(command):
        return None
    lines, i, end = command.split("\n"), 0, None
    while i < len(lines):
        opened = {m.end(): m for m in CHANGE_OPEN.finditer(lines[i])}
        docs = [(m, opened.get(m.end())) for m in ANY_HEREDOC.finditer(lines[i])]
        i += 1
        for m, change in docs:
            while i < len(lines) and (lines[i].lstrip("\t") if m.group(1) else lines[i]).rstrip() != m.group(3):
                i += 1
            i += 1
            if change:
                end = i
    if end is None or end >= len(lines):
        return None
    head = "\n".join(lines[:end])
    parts = change_parts(head)
    if parts and kind("Bash", {"command": parts.rest}) == "check":
        return None
    return head


def after_changes_only(command):
    """A call with changes, rewritten so that what follows each change runs only if it went through: on a new line
    after the heredoc it would run anyway, and `v2.py result` after a refused change would record the result the change
    was to write."""
    if not change_parts(command):
        return command
    lines, out, i = command.split("\n"), [], 0
    while i < len(lines):
        line = lines[i]
        opened = {m.end() for m in CHANGE_OPEN.finditer(line)}
        docs = [(m, m.end() in opened) for m in ANY_HEREDOC.finditer(line)]
        out.append(line)
        i += 1
        for m, is_change in docs:
            while i < len(lines) and (lines[i].lstrip("\t") if m.group(1) else lines[i]).rstrip() != m.group(3):
                out.append(lines[i])
                i += 1
            if i < len(lines):
                out.append(lines[i])
                i += 1
            if is_change and any(l.strip() for l in lines[i:]) and lines[i:i + 1] != [STATUS_LINE]:
                out.append(STATUS_LINE)
    return "\n".join(out)


def own_directory(where, cwd=None):
    """Whether a cd names the session's own working directory: then one that failed leaves the session where it
    already is, and a change joined to it by `;` writes where the guard read it (every one-tree session led its
    changes with `cd <the project>;` on 2026-09-21, 3 of the 4 refusals of the form that evening)."""
    here = os.path.normpath(cwd or v2.PROJECT)
    return os.path.normpath(os.path.join(here, os.path.expanduser(where))) == here


TEMPFILE = re.compile(r"\btempfile\.(?:TemporaryDirectory|mkdtemp|NamedTemporaryFile|mkstemp|TemporaryFile)\(")
TEMP_DIRS = tuple(dict.fromkeys(os.path.join(d, "") for d in ("/tmp", os.environ.get("TMPDIR") or "/tmp")))


def scratch(path):
    """Whether a path is the build directory's own — a task's drafts, a run's output — where a command's output may be
    written: not a task's tree, which holds the repository's files, nor what the harness keeps of a session's calls."""
    rel = os.path.relpath(path, v2.PROJECT)
    if rel.startswith("..") and os.path.normpath(path).startswith(TEMP_DIRS):  # the machine's temporary space
        return True  # review-97.3's `git show … > $TMPDIR/main.md` was refused as a write into its tree (2026-09-22)
    inside = re.match(r"\.build/trees/[^/]+/(.*)$", rel)  # a tree's .build is the one .build, behind a link
    rel = inside.group(1) if inside else rel
    return rel.startswith(".build/") and not rel.startswith((".build/trees/", ".build/outputs/"))



# a script's triple-quoted strings are text it handles, not code it runs: fix-265's `inj.replace("""…theory.write_text(…)…""")`
# was refused as a script whose target could not be read (2026-09-22 20:08)
TRIPLE = re.compile(r'"""[\s\S]*?"""' + "|'''" + r"[\s\S]*?'''")


def script_writes(command, cwd=None):
    """Where a script inside the command writes, each place as the file it names or the directory its path begins in:
    plan-42's `open('.build/plans/plan-42/b'+tid+'.md','w')` and review-94.2's `open(f'{T}/{n}','wb')` with
    `T=os.environ['TMPDIR']+'/mf'` were refused as scripts whose targets could not be read (2026-09-22 11:01, 11:05),
    both writing their own drafts. None when any place cannot be read: a path handed in, or made from nothing fixed."""
    base, _ = shell_context(command, cwd)
    tmp = os.environ.get("TMPDIR") or "/tmp"
    command = TRIPLE.sub('""', command)
    names = {}
    for name, value, rest in PY_PREFIX.findall(command):  # in order, each from those before it
        if value.startswith(("os.", "tempfile.")):
            head = tmp
        else:
            head = fixed_start(value, names)
            if head is None:
                continue
        tail = re.match(r"""^\+\s*f?['"]([^'"{]*)""", rest.strip())
        names[name] = (head + tail.group(1)) if tail else head
    places = []
    for m in WRITE_SITE.finditer(command):
        expr = next(g for g in m.groups() if g)
        start = fixed_start(expr, names)
        if not start:
            return None
        whole = os.path.normpath(os.path.join(base, os.path.expanduser(start)))
        places.append(whole if re.fullmatch(r"""f?['"][^'"{]*['"]|\w+""", expr.strip()) or start.endswith("/")
                      else os.path.dirname(whole))
    return places or None


def fixed_start(expr, names):
    """The fixed beginning of a path expression: a literal, an f-string up to its first field (a known name as its
    first field is read), or a known name; None when nothing fixed begins it."""
    expr = expr.strip()
    m = re.match(r"""^(f?)(['"])(.*?)\2""", expr)
    if m:
        text = m.group(3)
        if m.group(1):
            field = re.match(r"\{(\w+)\}(.*)$", text)
            if field and field.group(1) in names:
                text = names[field.group(1)] + field.group(2)
            text = text.split("{", 1)[0]
        return text or None
    m = re.match(r"^(\w+)\b", expr)
    return names.get(m.group(1)) if m else None


def content_write(command, cwd=None):
    """Why a command that writes a file's content is refused, or None (the owner, 2026-09-21: one way to change files,
    which names them exactly and fails loudly). A redirection, tee, `sed -i` or a script that writes fails silently
    when it matches nothing, and names its files only as far as the shell can be read; a command that moves, copies
    or removes files names them, and stands."""
    parts = change_parts(command)
    if not parts and own_command(command) and CHANGE_VERB.search(shell_syntax(command)):
        return ("`v2.py change` takes its changes in a quoted heredoc of the same call: `.claude/orchestration/v2.py "
                "change <<'EOF'`, the changes, `EOF`.")
    if parts:  # each change in its form, and the rest of the call judged as it would be alone
        for before, quoted, _ in parts.changes:
            if not quoted:
                return ("Quote the heredoc's delimiter (`v2.py change <<'EOF'`): unquoted, the shell expands `$` and "
                        "backquotes inside the changes before the command sees them.")
            cd = CD_BY_SEMICOLON.search(before)
            if cd and not own_directory(cd.group(1).strip().strip("'\""), cwd):
                return ("A `cd` before a change is joined to it by `&&`, not by `;` or a new line: one that failed would "
                        "leave the change writing where the call did not mean it to.")
        return content_write(parts.rest, cwd)
    syntax = shell_syntax(command)
    how = ("a redirection into a file" if any(not t.strip("'\"").startswith("/dev/") for t in redirections(command))
           else "tee" if any(os.path.basename(w[0]) == "tee" for w in segments(syntax))
           else "an in-place edit" if re.search(r"\b(?:sed|perl)\s+(?:-\w+\s+)*-\w*i", syntax)
           else "a script that writes" if WRITE_SCRIPT.search(command) and runs_script(command) else None)
    if not how:
        return None
    # what writes content, not a copy beside it: implement-62's `git show HEAD:$f > .build/tasks/62/head/$f` was
    # refused for the `cp` of those files into the tree that followed it, and copying stands (2026-09-22 03:10)
    targets = write_targets("Bash", {}, command, cwd, content=True)
    if targets and all(scratch(t) for t in targets):  # a program's output, or a draft, in the build directory
        return None
    places = script_writes(command, cwd) if how == "a script that writes" else None
    if places and all(scratch(p) or scratch(os.path.join(p, "x")) for p in places) \
            and all(scratch(t) for t in targets):  # its paths made at run time, each in a draft's directory
        return None
    if how == "a script that writes" and not targets and TEMPFILE.search(command):
        # what it writes it writes into a temporary directory it makes: review-122's test of fix-122's function in a
        # `tempfile.TemporaryDirectory()` was refused twice (2026-09-22 06:55); a path it names is still judged above
        return None
    # fix-80.2's script wrote under .build/ to a path given it as an argument, and was told only that .build/ is
    # allowed (2026-09-21): where a script writes is read from the command only when the command names it
    unread = "" if targets else (" Where this writes could not be read from the command (a path handed to a script "
                                 "as an argument, or made inside it): name the file under .build/ in the script "
                                 "itself, or print and redirect (`> .build/…`).")
    # review-94.2 moved its merge files to .build/outputs/, which the harness keeps for sessions' calls, and was
    # refused a third time on the same words (2026-09-22 11:01)
    harness = [t for t in targets + (places or []) if re.match(r"\.build/(outputs|trees)/", os.path.relpath(t, v2.PROJECT))]
    where = (" .build/outputs/ is the harness's (what it keeps of your calls) and .build/trees/ holds the tasks' trees: "
             "neither is a draft's place." if harness else "")
    return (f"Not by {how}: {CHANGE_POINTER} A command's output may be written under .build/ — your drafts under "
            ".build/tasks/<your task>/, or the machine's temporary directory ($TMPDIR); the repository's own files "
            f"change by `v2.py change` alone. Moving, copying and removing files stand.{where}{unread}")


# Every command a session makes is kept, numbered (the owner, 2026-09-21), so that one that failed or was refused is
# fixed rather than written again whole: of the first runs' 1,799 commands 146 failed, and 40 were followed by a
# near-copy of themselves — 88K characters written again, the largest 12K — and with every file's change now a
# command, a refused batch would be written again whole too. `v2.py again N` sends only the correction: SEARCH/REPLACE
# blocks on command N's text, applied here, and what they make is guarded and run as if it had been typed.
# The heredoc is optional: `v2.py again N` alone runs command N as it was, which the protocol's "no block" names and
# the planner read as no heredoc at all — refused for that on 2026-09-21, a request spent on the form.
AGAIN = re.compile(r"^\s*" + RUNNER_ARG + r"\S*v2\.py\s+again(?:\s+(\d+))?\s*"
                   r"(?:<<-?\s*(['\"]?)(\w+)\2[ \t]*\n(.*?)\n?^[ \t]*\3[ \t]*$)?\s*\Z", re.S | re.M)
AGAIN_VERB = re.compile(r"\bv2\.py\s+again\b")
# The call holds nothing else, so that it is read as the one command it runs (its kind, what it writes, how it is
# bounded). A change that command needs first — the draft it reads — is a call of its own before it in the same
# request, which is still one batch: Claude Code runs a request's calls that write one after another, in order
# (measured 2026-09-21: the second call started after the first had ended). The planner put the two in one call and
# was refused without being told this, a request spent (2026-09-21).
AGAIN_ALONE = ("`v2.py again N` runs your command N (your last, N left out) as it was, or fixed by the SEARCH/REPLACE "
               "blocks in a quoted heredoc of the same call (`v2.py again N <<'EOF'` … `EOF`), and the call holds "
               "nothing else. A change the command needs first — a draft it reads — is a call of its own before it "
               "in the same request: a request's calls that change something run one after another, in order.")
KEPT_COMMANDS = 50  # a session's newest commands kept; all of them go when it is released (v2.release)


def commands_of(name):
    return os.path.join(v2.outputs_of(name), "commands")


def keep_command(name, command):
    """The number a session's command is kept under, in the order they were made."""
    folder = commands_of(name)
    os.makedirs(folder, exist_ok=True)
    n = max((int(f[:-3]) for f in os.listdir(folder) if f.endswith(".sh") and f[:-3].isdigit()), default=0) + 1
    while True:  # the calls of one request are guarded side by side
        try:
            fd = os.open(os.path.join(folder, f"{n}.sh"), os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
            break
        except FileExistsError:
            n += 1
    with os.fdopen(fd, "w") as f:
        f.write(command)
    for old in sorted(int(f[:-3]) for f in os.listdir(folder) if f.endswith(".sh") and f[:-3].isdigit())[:-KEPT_COMMANDS]:
        for kept in (f"{old}.sh", f"{old}.run"):  # the newest are what a correction is sent for; .run: spilled()
            with contextlib.suppress(OSError):
                os.remove(os.path.join(folder, kept))
    return n


def kept_command(name, n=None):
    """(its number, its text) of a session's kept command n, or of its last; None when there is none."""
    try:
        numbers = sorted(int(f[:-3]) for f in os.listdir(commands_of(name)) if f.endswith(".sh") and f[:-3].isdigit())
    except OSError:
        return None
    n = numbers[-1] if n is None and numbers else n
    return (n, open(os.path.join(commands_of(name), f"{n}.sh")).read()) if n in numbers else None


def again(name, command):
    """(the command a `v2.py again` call runs, or None; why it is refused, or None). Anything else: (None, None)."""
    if not (own_command(command) and AGAIN_VERB.search(HEREDOC.sub(" ", command))):
        return None, None
    m = AGAIN.match(command)
    if not m:
        return None, AGAIN_ALONE
    if m.group(3) and not m.group(2):
        return None, "Quote the heredoc's delimiter (`v2.py again N <<'EOF'`), so that the blocks reach it as they are."
    kept = kept_command(name, int(m.group(1)) if m.group(1) else None)
    if not kept:
        return None, (f"No command {m.group(1)} of yours is kept." if m.group(1) else "No command of yours is kept yet.")
    n, text = kept
    if not (m.group(4) or "").strip():  # no correction: the command as it was, not written again
        return text, None
    ops, problems = v2.change_blocks(f"=== replace command {n}\n" + m.group(4), markers=False)
    for op in ops if not problems else []:  # every block judged, as a change's are, and all that fail said
        fixed, _, problem = v2.replace_one(text, op, f"command {n}")
        text = text if problem else fixed
        problems += [problem] if problem else []
    if problems:
        return None, f"Nothing was run: command {n} could not be fixed so.\n- " + "\n- ".join(problems)
    return text, None


def fix_note(n):
    return (f"[kept as command {n}: when the command is what is wrong, send the correction and not the command again — "
            f"`.claude/orchestration/v2.py again {n} <<'EOF'` with SEARCH/REPLACE blocks on its text runs it fixed]")


ADMITTED_NOW = []  # the session whose heavy check this call marked as starting (v2.admit_session)
MEASURED_NOW = []  # the task whose measurement this call runs, under its hold of the machine (v2.claim_call)


def deny(text, fixable=False, end=False):
    """A refusal; `fixable` when what is wrong is the command itself, which is then told how to send its correction
    (guard() takes the mark off before Claude Code sees the answer); `end` when it also ends the session's turn, which
    has nothing left in it — the request that would only say "Parked; ending my turn" is not made (v2.turn_over)."""
    out = {"hookSpecificOutput": {"hookEventName": "PreToolUse", "permissionDecision": "deny",
                                  "permissionDecisionReason": text}}
    if end:
        out.update({"continue": False, "stopReason": text})
    return dict(out, fixable=True) if fixable else out


# ---------------------------------------------------------------- the planner

def body(path, cwd=None, own=()):
    """Whether a path the planner names is a body: a theory, code, a log, a draft, or a directory that holds them — not
    what is its own (own_dirs): its drafts, and what the harness kept of its own calls."""
    p = path.strip("'\"")
    if not p or p.startswith("-"):
        return False
    full = os.path.normpath(p if os.path.isabs(p) else os.path.join(cwd or v2.PROJECT, p))
    if any((full + os.sep).startswith(os.path.join(d, "")) for d in own):
        return False
    tree = cwd if cwd and os.path.exists(os.path.join(cwd, "ROOT")) else v2.PROJECT
    rel = os.path.relpath(full, tree)
    return bool(BODY.search(rel)) or rel == "." or full in (tree, v2.PROJECT)


def own_dirs(rec):
    """What a statements reader may read though it stands under .build: its own drafts — the planner's edit files and
    notes, a task designer's proposal — which it writes and must be able to correct, and its own kept outputs and
    commands (found 2026-09-21: a proposal the planner refused could not be read back by the one fixing it)."""
    drafts = v2.deliverables_of(rec).get("drafts") if rec.get("role") else ""
    return tuple(os.path.normpath(os.path.join(v2.PROJECT, d)) for d in (drafts,) if d) + (
        (v2.outputs_of(rec["name"]),) if rec.get("name") else ())


V2_READS = re.compile(r"\bv2\.py\s+(?:read|proposal|graph|status|who)\b")


def own_command(command):
    """Whether the command runs the harness's own v2.py, however the session writes the path: it is free of the
    reading limits. The protocols give both `.claude/orchestration/v2.py result 4` and `v2.py park run`, and only
    the first was recognised — so a session that wrote the short form had the one command that ends its turn
    counted as reading, and refused once its budget was spent (2026-09-21). It is the command being run and not a
    word in one: `grep v2.py HANDOFF.md` reads."""
    for words in segments(shell_syntax(command)):
        head = [os.path.basename(w.strip("'\"`")) for w in words[:2]]
        if head[:1] == ["v2.py"] or (head[:1] and head[0] in RUNNERS and head[1:] == ["v2.py"]):
            return True
    return False


def harness_only(command):
    """Whether every simple command of a call is the harness's own (a leading cd aside), and nothing in it is run from
    inside a quote: then its quoted words and heredocs are what it carries — a message, a change's text — and never
    what it runs. plan-32's question to the owner named `git rm --cached` in its quoted text and was refused as a git
    command (2026-09-21). A call with anything else in it is read whole, quotes and all."""
    bare = HEREDOC.sub(" ", command or "")
    if not command or "$(" in bare or "`" in bare:
        return False
    parts = segments(shell_syntax(command))
    return bool(parts) and all(w[0] in ("cd", "true") or own_command(" ".join(w)) for w in parts)


def segments(command):
    """The simple commands of a command line, as argument lists (a pipeline's and a sequence's parts apart)."""
    out = []
    for part in re.split(r"\|\|?|&&|;|\n", command):
        try:
            words = shlex.split(part)
        except ValueError:
            words = part.split()
        while words and (re.match(r"^\w+=", words[0]) or words[0] in SHELL_KEYWORDS or words[0][:1] in "({"):
            if words[0][:1] in "({" and len(words[0]) > 1:  # a subshell or group opened on the command's own word
                words[0] = words[0][1:]
                continue
            words.pop(0)
        if words:
            out.append(words)
    return out


def reads_body(words, cwd, own=()):
    """Whether one simple command prints the content of a body."""
    cmd = os.path.basename(words[0])
    if cmd == "git":
        args = words[1:]
        while args and args[0] in ("-C", "-c") and len(args) > 1:
            args = args[2:]
        sub, rest = (args[0] if args else ""), " ".join(args[1:])
        if sub in ("show", "diff"):
            return not STAT.search(rest)
        if sub == "log":
            return bool(PATCH.search(" " + rest + " "))
        return sub in ("blame", "grep", "cat-file")
    if cmd not in CONTENT:
        return False
    operands, script = [], cmd in PATTERNED
    rest = words[1:]
    while rest:
        w = rest.pop(0)
        if w in ("-e", "--regexp", "-f", "--file") or (cmd == "sed" and w == "-e"):
            script = False
            rest = rest[1:]
        elif w.startswith("-"):
            continue
        else:
            operands.append(w)
    files = operands[1:] if script else operands
    recursive = cmd == "rg" or any(re.fullmatch(r"-\w*[rR]\w*|--recursive|--dereference-recursive", w) for w in words[1:])
    if cmd in ("grep", "egrep", "fgrep", "rg") and recursive and not files:
        return True  # the whole working directory
    return any(body(f, cwd, own) for f in files)


def planner_guard(tool, inp, cwd=None, own=()):
    detail = ("Your role reads statements, not details: theories through `.claude/orchestration/show.py --statement "
              "NAME` or `--statements THEORY` (or `v2.py read`), results and documents under .build/tasks/*/, "
              "the plan, the ledger, `git log`; never proof text, code bodies, logs or diffs. Listing names (ls, "
              "find) is free.")
    if tool == "Bash":
        c = inp.get("command") or ""
        parts = change_parts(c)
        if parts:  # what a change writes is not read: brief-141's draft saying "show.py finds none" was refused as a
            c = parts.rest  # reading of details (2026-09-22 10:44)
        if re.search(r"show\.py\b", c) and not re.search(r"--statements?\b", c):
            return deny(detail)
        if any(reads_body(words, cwd, own) for words in segments(c)):
            return deny(detail)
    return None


# ---------------------------------------------------------------- a session's state

def path_of(session):
    return os.path.join(STATE, f"work-{session}.json")


def load(session):
    fresh = {"reads": {}, "production_at": None, "fixed_since": False, "last_check": None, "prev_sig": None,
             "repeats": 0, "reserve": RESERVE, "refused": [], "batches": {}}
    try:
        return {**fresh, **json.load(open(path_of(session)))}  # a meter written before a field existed has it now
    except (OSError, ValueError):
        return fresh


@contextlib.contextmanager
def meter(session):
    """A session's meter, read and written under a lock: parallel calls of one request run their hooks side by side,
    and each wrote back what it had read before the other's change — a refused call or a production lost that way is
    a read charged that was not made, or a count that never restarts."""
    os.makedirs(STATE, exist_ok=True)
    with open(path_of(session) + ".lock", "a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        st = load(session)
        yield st
        save(session, st)


def save(session, st):
    os.makedirs(STATE, exist_ok=True)
    tmp = path_of(session) + ".tmp"
    json.dump(st, open(tmp, "w"))
    os.replace(tmp, path_of(session))


def brief_of(rec):
    """What counts as a session's production (v2.deliverables_of)."""
    out = v2.deliverables_of(rec)
    # the deliverables stand where the session works: in a task's own tree its theory is written there, and measured
    # in the one tree its production was never seen — after three reads it was refused everything (found 2026-09-21)
    out["root"] = v2.tree_of(rec)
    return out


def lines_of(path):
    try:
        with open(path, "rb") as f:
            return sum(1 for _ in f)
    except OSError:
        return None


def stamp(path):
    try:
        s = os.stat(path)
        return [s.st_size, s.st_mtime_ns]
    except OSError:
        return None


def shown_bound(command):
    """What a call shows at most: what it declares (SHOW), within READ_BYTES and the batch's BATCH, else READ_BYTES."""
    # declared at the head of any command the call runs, the largest: `sed …; SHOW=12K sed …` was cut at the default,
    # the declaration read at the call's start alone (implement-130, 2026-09-22 14:54)
    heads = [SHOW.match(part) for part in re.split(r"(?:&&|\|\||;|\n)\s*", command or "")]
    declared = [int(m.group(2)) * (1000 if m.group(3) else 1) for m in heads if m]
    if not declared:
        return READ_BYTES
    return max(READ_BYTES, min(max(declared), BATCH))


def requested(tool, inp, cwd):
    """(file, first line, last line or None for the end, form) of a read the re-read guard knows, else None."""
    def where(p):
        p = p.strip("'\"")
        if re.search(r"[|;&<>()`$*?\s]", p):
            return None
        return os.path.normpath(p if os.path.isabs(p) else os.path.join(cwd or v2.PROJECT, p))
    if tool == "Read":
        p = inp.get("file_path")
        if not p:
            return None
        first = max(1, int(inp.get("offset") or 1))
        return os.path.normpath(p), first, first + int(inp.get("limit") or READ_LINES) - 1, "read"
    if tool != "Bash":
        return None
    c = SHOW.sub(lambda m: m.group(1), " ".join((inp.get("command") or "").split()), count=1)  # its bound said apart
    for rx, form in ((SED, "sed"), (CAT, "cat"), (HEAD, "head"), (TAIL, "tail")):
        m = rx.match(c)
        if not m:
            continue
        p = where(m.groups()[-1])
        if not p:
            return None
        if form == "sed":
            return p, int(m.group(2)), int(m.group(3)), form
        if form == "cat":
            return p, 1, None, form
        if form == "head":
            return p, 1, int(m.group(1)), form
        total = lines_of(p)
        return (p, max(1, total - int(m.group(1)) + 1), None, form) if total is not None else None
    return None


# Not a session's tools (the owner, 2026-09-21): taken out of session-flags, so that no base and no fork has them, and
# refused if one is ever called, each with where its work goes. A session has Bash, TaskCreate, TaskUpdate and
# TaskStop. Grep, Glob, WebFetch and WebSearch show what no hook can bound (a hook rewrites a call before it runs, and
# replaces only an MCP tool's result after), and the limit applies to everything; Read, Edit and Write were one file
# a call where Bash and `v2.py change` take many, bounded and named; Agent, TaskOutput and Monitor were always refused
# and never used; ToolSearch loaded the tools Claude Code defers, and with it gone every tool loads at the start.
_SEARCH = "Search and list through Bash (`grep -n`, `rg`, `find`, `ls`), whose output is cut to a read like any other."
_WAIT = "Waiting is refused: a background job's completion notifies you; continue with the task meanwhile."
REMOVED_TOOLS = {
    "Read": (f"Read through Bash: `sed -n 'A,Bp' FILE` (at most a read's {READ_BYTES // 1000}K bytes; lines already in your context are "
             "left out, and said), or `.claude/orchestration/v2.py read SOURCE...` for any source."),
    "Edit": CHANGE_POINTER, "Write": CHANGE_POINTER, "MultiEdit": CHANGE_POINTER, "NotebookEdit": CHANGE_POINTER,
    "Grep": _SEARCH, "Glob": _SEARCH,
    "WebFetch": "The web is not read from here.", "WebSearch": "The web is not read from here.",
    "Agent": ("A session starts no subagents: it does its piece of work itself; a question goes to its author, the "
              "knowledge base or the planner (`v2.py ask`)."),
    "TaskOutput": _WAIT, "Monitor": _WAIT,
    "ToolSearch": "Every tool you have is loaded at your start: there is nothing to search for.",
}
# The tools the guard acts on, and so the tools the PreToolUse matcher of planner-settings.json and
# worker-settings.json must name: a tool left out of that matcher never reaches the guard at all, and its refusals
# and its records simply do not happen. Write, Edit, MultiEdit and NotebookEdit were left out of it for the whole
# first live run (2026-09-20): every write of the roles' usual tool went unguarded — HANDOFF.md, a finalization's
# locked files and a tree another task holds were all open to them — and the tree's ownership was built from the
# words of Bash commands alone, 116 of its 123 entries being shell and Isabelle fragments with not one of them
# naming a path that had changed. The tests call the guard directly, which is past the matcher, so only
# test_the_settings_let_every_guarded_tool_reach_the_guard sees this.
GUARDED_TOOLS = ("Bash",                                         # reading, checks, waiting, git, changing files
                 "TaskCreate", "TaskUpdate",                     # the graph's roles' edits; a worker's own plan
                 *REMOVED_TOOLS)                                 # not a session's tools, and refused if one is tried
# Named by kind() and deliberately not in the matcher: matching them would change nothing.
UNGUARDED_TOOLS = ("TaskStop",)  # stopping its own background job: nothing is refused and nothing is counted


def kind(tool, inp, cwd=None):
    """write, read, check, own (the harness's commands), or other; cwd is where a script a command runs is found."""
    if tool in ("Edit", "Write", "MultiEdit", "NotebookEdit"):
        return "write"
    if tool == "Read":
        return "read"
    if tool in ("TaskCreate", "TaskUpdate"):
        return "task"
    if tool in ("ToolSearch", "TaskStop"):
        return "own"
    if tool == "Bash":
        c = inp.get("command") or ""
        parts = change_parts(c)
        if parts:  # judged as the check it holds, if it runs one (its bound, the machine's limits), else as the write;
            return "check" if runs_check(parts.rest, cwd) else "write"  # its changes by write_guard and content_write
        # read from the syntax, quoted words out: task 56's question to the planner, which named `v2.py change` in its
        # text, was refused as a change out of its form (2026-09-22)
        if own_command(c) and CHANGE_VERB.search(shell_syntax(c)):
            return "write"  # the one way a session changes files
        if own_command(c):
            # the harness's commands that print what a session reads are reads, bounded as any is: `v2.py proposal`
            # printed every brief it was asked for at once, counted as nothing (2026-09-21)
            return "read" if V2_READS.search(c) else "own"
        if runs_check(c, cwd):
            return "check"
        if WRITE_SHELL.search(shell_syntax(c)) or (WRITE_SCRIPT.search(c) and runs_script(c)):
            return "write"
        if READS.match(c):
            return "read"
    return "other"


def rounds_since(transcript, since, tool_use=None, refused=()):
    """Requests recorded after a moment (v2.iso: the transcripts' form), and the request making this call when it is not
    recorded yet: a hook can run before the request that made its call is written (ctx_gauge.py). A request whose
    calls were all refused counts for nothing (the owner, 2026-09-21)."""
    if not since:
        return 0
    try:
        size = os.path.getsize(transcript)
        with open(transcript, "rb") as f:
            f.seek(max(0, size - 4_000_000))
            lines = f.read().decode(errors="ignore").splitlines()
    except OSError as e:
        # said once in a while: this runs on every guarded tool call, and a cause that stands would fill the log
        v2.say_once("rounds-unreadable", f"ATTENTION a transcript could not be read, so nothing is counted since the "
                    f"last production ({transcript}): {e!r}")
        return 0
    calls, current, refused = {}, False, set(refused)
    for line in lines:
        if '"assistant"' not in line:
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("type") == "assistant" and not d.get("isSidechain") and d.get("timestamp", "") > since:
            m = d.get("message") or {}
            calls.setdefault(m.get("id"), []).extend(c.get("id") for c in m.get("content") or []
                                                     if isinstance(c, dict) and c.get("type") == "tool_use")
            current = current or bool(tool_use and tool_use in line)
    counted = [mid for mid, ids in calls.items() if not (ids and all(i in refused for i in ids))]
    return len(counted) + (0 if current else 1)


def transcript_tail(transcript):
    """The last 4 MB of a transcript as lines; None when it cannot be read (said, once in a while)."""
    try:
        size = os.path.getsize(transcript)
        with open(transcript, "rb") as f:
            f.seek(max(0, size - 4_000_000))
            return f.read().decode(errors="ignore").splitlines()
    except OSError as e:
        v2.say_once("rounds-unreadable", f"ATTENTION a transcript could not be read, so nothing is counted since the "
                    f"last production ({transcript}): {e!r}")
        return None


def tool_uses(lines, since=""):
    """(message id, call) of every call of the session's own requests after a moment, in the transcript's order."""
    for line in lines or []:
        if '"assistant"' not in line or '"tool_use"' not in line:
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("type") != "assistant" or d.get("isSidechain") or d.get("timestamp", "") <= since:
            continue
        m = d.get("message") or {}
        for c in m.get("content") or []:
            if isinstance(c, dict) and c.get("type") == "tool_use":
                yield m.get("id"), c


def is_read(call, refused, resolved=None):
    """A call the limits hold: of a reading kind, reaching the guard, and not refused — a `v2.py again` call being the
    command it ran (resolved: by the call's id)."""
    inp = {"command": resolved[call.get("id")]} if call.get("id") in (resolved or {}) else call.get("input") or {}
    return call.get("id") not in refused and call.get("name") in GUARDED_TOOLS and kind(call.get("name"), inp) in READING


def reading_requests(transcript, since, refused=(), tool_use=None, resolved=None):
    """The reads since a moment, a batch being one: a request that read, searched or checked counts once, however
    many such calls it held (the owner, 2026-09-21: the point of batching is that it counts as one read). What only
    writes, asks or parks counts for nothing, and so does a read the guard refused. The calling request counts when it is not written yet (a hook can run before it is).

    Every request was counted until 2026-09-21, whatever it held: a question, a park, a write too small to be
    production, and a read the guard had refused each took one of the three a production allows."""
    if not since:
        return 0
    lines = transcript_tail(transcript)
    if lines is None:
        return 0
    batches, current, refused = set(), False, set(refused)
    for mid, c in tool_uses(lines, since):
        current = current or (tool_use is not None and c.get("id") == tool_use)
        if is_read(c, refused, resolved):
            batches.add(mid)
    return len(batches) + (1 if tool_use is not None and not current else 0)


def batch_id(transcript, tool_use, wait=0.0):
    """The batch — the request, by its message id — a call belongs to; None when the call cannot be found in the
    transcript. A request's calls are written as they are made and run as soon as each is complete, so the calls
    before this one are there when its hook runs; this one may be written a moment after, which is what `wait`
    (seconds) is for. Not found, the guard takes the call for a batch of its own: it refuses nothing it cannot place,
    since a read wrongly refused is a session working blind."""
    end = time.time() + wait
    while True:
        mine = next((mid for mid, c in tool_uses(transcript_tail(transcript) or []) if c.get("id") == tool_use), None)
        if mine is not None or time.time() >= end:
            return mine
        time.sleep(0.05)


# A request that only changes files, or checks, right after one that only changed files — nothing read, no mail, no job
# ended between — could use nothing the one before it learnt: a change that went through answers only "changed: …".
# What it holds was ready in that request, which re-read the whole context for it (brief-10 wrote the ten briefs of
# its proposal in five such requests on 2026-09-21, implement-54 each probe of its change in the request after it).
# Said, not refused: a refusal would spend one more request and have the text written again.
READY_NOTE = ("[What this request holds was ready in your last one: that request only changed files, and nothing reached "
              "you since. Put what you have ready in one request — every change in one `v2.py change`, and a check or "
              "a command that needs them as a call of its own after it: a request's calls that change something run "
              "one after another, in order.]")
NEWS = re.compile(r'"type":\s*"queued_command"')  # a background job's end or mail, queued for the session


def ready_before(transcript, tool_use, resolved=None):
    """Whether this call's request only changes files or checks (its task list aside), and follows a request that only
    changed files, every change of it gone through, with nothing reaching the session between (READY_NOTE)."""
    lines = (transcript_tail(transcript) or [])[-3000:]  # the two requests are the last; a long result is one line
    order, calls, answers, news, pending = [], {}, {}, {}, False
    for line in lines:
        try:
            d = json.loads(line)
        except ValueError:
            continue
        kind_of = d.get("type")
        if kind_of == "assistant" and not d.get("isSidechain"):
            mid = (d.get("message") or {}).get("id")
            if mid not in calls:
                order.append(mid)
                calls[mid], news[mid], pending = [], pending, False
            calls[mid] += [c for c in (d.get("message") or {}).get("content") or []
                           if isinstance(c, dict) and c.get("type") == "tool_use"]
        elif kind_of == "user":
            content = (d.get("message") or {}).get("content")
            blocks = content if isinstance(content, list) else [{"type": "text"}]
            for b in blocks:
                if isinstance(b, dict) and b.get("type") == "tool_result":
                    body = b.get("content")
                    answers[b.get("tool_use_id")] = body if isinstance(body, str) else "".join(
                        x.get("text", "") for x in body or [] if isinstance(x, dict))
                elif not d.get("isMeta"):
                    pending = True  # the harness's mail, the owner's words: something new
        elif kind_of == "attachment" and NEWS.search(line):
            pending = True
    mine = next((m for m in order if any(c.get("id") == tool_use for c in calls[m])), None)
    if mine is None or order.index(mine) == 0 or news.get(mine):
        return False
    before = order[order.index(mine) - 1]

    def kinds(mid):
        return [kind(c.get("name"), {"command": (resolved or {}).get(c.get("id"))} if c.get("id") in (resolved or {})
                     else c.get("input") or {}) for c in calls[mid]]
    changed = calls[before] and all(k == "write" and own_command((c.get("input") or {}).get("command") or "")
                                    for k, c in zip(kinds(before), calls[before]))
    went = all((answers.get(c.get("id")) or "").lstrip().startswith("changed:") for c in calls[before])
    return bool(changed and went and all(k in ("write", "check", "task") for k in kinds(mine)))


# A reading request that read little, followed by another: the two could have been one, and each cost a whole read.
# Every read was told the same count, whatever it held, and nothing named it: implement-24 read four small things in
# four requests, two of them from its reserve (2026-09-21). Said once between two productions, as a cost and not a
# refusal: whether the second read needed the first's answer cannot be seen from here.
SMALL_READ = READ_BYTES // 2


def small_read_before(transcript, tool_use, st):
    """The bytes the request before this call's showed, when every call of it read (no run, no change, no check among
    them) and together they showed under SMALL_READ; None otherwise. Summed from what the post-hook recorded of each
    call by its id (`calls_shown`), the request's calls read from the transcript, where a finished request stands whole:
    the bytes it had recorded by batch missed a call whose batch it could not place — implement-192 was told its last
    request "read 3,966 bytes" after one that read about 33K in three calls — and counted a probe's output as a read
    (fix-279, 2026-09-22)."""
    calls = list(tool_uses(transcript_tail(transcript) or []))
    order = []
    for mid, _ in calls:
        if mid not in order:
            order.append(mid)
    mine = next((mid for mid, c in calls if c.get("id") == tool_use), None)
    if mine is None or order.index(mine) == 0:
        return None
    before = order[order.index(mine) - 1]
    seen = st.get("calls_shown") or {}
    shown = [seen.get(c.get("id")) for mid, c in calls if mid == before]
    if not shown or any(x is None or x[0] not in ("read", "other") for x in shown):
        return None
    total = sum(x[1] for x in shown)
    return total if total < SMALL_READ else None


PROBE_TIMEOUT = re.compile(r"--timeout(?:=|\s+)(\d+)")


def probe_timeout(command):
    """The --timeout a probe's command names (its last), or None."""
    found = PROBE_TIMEOUT.findall(command or "")
    return int(found[-1]) if found else None


PROBE_TOOL = re.compile(r"([^\s'\"]*probe_theories\.py)")
TOOL_DEFAULT = re.compile(r"^DEFAULT_TIMEOUT\s*=\s*(\d+)|'--timeout',\s*type=int,\s*default=(\d+)", re.M)


def probe_default(command, cwd):
    """The --timeout the probe tool a command runs gives a probe that names none, read from that tool where the session
    runs it, or None. It became 60 at 2026-09-21 23:02 (bba91b39); a tree made before holds the tool whose default was
    1200, and a probe there still names its limit."""
    m = PROBE_TOOL.search(command or "")
    try:
        text = open(os.path.join(cwd or v2.PROJECT, m.group(1))).read() if m else ""
    except OSError:
        return None
    d = TOOL_DEFAULT.search(text)
    return int(d.group(1) or d.group(2)) if d else None


PROBE_WORK = re.compile(r"probe_theories\.py\b((?:[^;&|\n\\]|\\.)*)")
WORK_ARG = re.compile(r"--work(?:=|\s+)(['\"]?)([^\s'\"]+)\1")


def probe_work(command, cwd):
    """The directories the probes of a command name as their `--work`, as the shell would resolve them: after a
    leading `cd`, with $TMPDIR and the call's own assignments filled in (shell_context)."""
    base, known = shell_context(command, cwd)
    out = []
    for args in PROBE_WORK.findall(command or ""):
        for _, value in WORK_ARG.findall(args):
            value = re.sub(r"\$\{?(\w+)\}?", lambda m: known.get(m.group(1), m.group(0)), value)
            if "$" not in value:
                out.append(os.path.normpath(os.path.join(base, os.path.expanduser(value))))
    return out


def shown_bytes(tool, response):
    """The bytes a call showed the session: a command's output, and anything else as it came back. It was the call's
    result encoded as JSON, which counted every line break twice."""
    if isinstance(response, dict) and tool == "Bash":
        return len(((response.get("stdout") or "") + (response.get("stderr") or "")).encode())
    return len(json.dumps(response or "").encode())


def reserve_of(st):
    """The reserve a meter holds, never more than RESERVE: a meter written under a larger setting keeps no more than
    the setting now gives."""
    return max(0, min(st.get("reserve", RESERVE), RESERVE))


def tiers(n):
    """(what the first tier holds, what the reserve has given) in a stretch of n reads: the first tier is ROUNDS reads,
    and every read past it is drawn from the reserve."""
    return ROUNDS, max(0, n - ROUNDS)


def stretch_ends(st, transcript, now):
    """A production: the reserve gives back one and pays what the stretch drew from it, never below none nor above
    RESERVE, and the first tier restarts whole."""
    _, drawn = tiers(reading_requests(transcript, st.get("production_at"), st.get("refused") or [],
                                      resolved=st.get("resolved")))
    st["reserve"] = min(RESERVE, max(0, reserve_of(st) - drawn) + 1)
    st["production_at"], st["refused"], st["batches"], st["resolved"] = now, [], {}, {}
    st["pending"] = {}  # rewrites of calls that never ran, if any
    st["fixed_since"] = True
    st["productions"] = st.get("productions", 0) + 1


# ---------------------------------------------------------------- production

def deliverable_files(brief):
    out = []
    for p in brief.get("deliverables", []):
        full = os.path.join(brief.get("root") or v2.PROJECT, p)
        if os.path.isdir(full):
            out += [os.path.join(r, f) for r, _, fs in os.walk(full) for f in fs]
        else:
            out.append(full)
    drafts = os.path.join(v2.PROJECT, brief.get("drafts", ""))
    if brief.get("drafts") and os.path.isdir(drafts):
        out += [os.path.join(r, f) for r, _, fs in os.walk(drafts) for f in fs if written_by_hand(r, f)]
    return sorted(set(out))


# What production is measured in is what a session writes: a theory, a document, code. A run's output under the same
# directory is not production, and snapshotting it cost 68,706 files and 6.0 GB for one session on 2026-09-20, walked
# and copied again on every tool call.
PRODUCED = (".thy", ".md", ".py", ".sh", ".ML", ".sml", ".txt", ".diff", ".patch")
RUN_OUTPUT = ("probe", "replay", "check-", "complete-", "recipes", "exports", "export", "proof", "run", "log")
NOT_PRODUCTION = ("brief.json", "result.md", "finalize.json", "finalize.log", "finalized.json", "root-lines.json")


def written_by_hand(directory, name):
    """Whether a file under a task's drafts is something the session wrote, rather than something a run left there."""
    if name in NOT_PRODUCTION or not name.endswith(PRODUCED):
        return False
    parts = os.path.normpath(directory).split(os.sep)
    return not any(p.startswith(RUN_OUTPUT) for p in parts)


def units(path):
    """What production is measured in: theory commands (hashed, comments and layout aside) with their commentary
    words, document words, or code lines."""
    try:
        text = open(path, errors="ignore").read()
    except OSError:
        return {"kind": "none"}
    if path.endswith(".thy"):
        commands, words = [], []
        for cmd, lines in chunks(text):
            body = re.sub(r"\(\*.*?\*\)", "", "\n".join(lines), flags=re.S)
            if cmd in COMMENTARY:
                words += body.split()[1:]
            elif body.strip():
                commands.append(hashlib.sha1(" ".join(body.split()).encode()).hexdigest())
        return {"kind": "thy", "commands": commands, "words": words}
    if path.endswith(CODE):
        return {"kind": "code", "lines": [l.strip() for l in text.splitlines()
                                          if l.strip() and not l.strip().startswith(("#", "(*", "//"))]}
    return {"kind": "md", "words": text.split()}


def changed(old, new):
    """Units of new beyond old, as multisets: words or lines added or rewritten count; moved or deleted ones do not."""
    return sum((collections.Counter(new) - collections.Counter(old)).values())


def produced(old, new):
    old = old or {}
    if new.get("kind") == "thy":
        before = set(old.get("commands", []))
        return (any(c not in before for c in new["commands"])
                or changed(old.get("words", []), new["words"]) >= COMMENTARY_WORDS)
    if new.get("kind") == "code":
        return changed(old.get("lines", []), new["lines"]) >= CODE_LINES
    if new.get("kind") == "md":
        return changed(old.get("words", []), new["words"]) >= PROSE_WORDS
    return False


def snapshot_dir(session):
    return os.path.join(STATE, f"work-{session}.snap")


def check_production(session, brief, st):
    """Whether the deliverables now hold production beyond the last production's snapshot, which then advances. A file
    unchanged since it was last measured (size and time) is not measured again."""
    snap = snapshot_dir(session)
    os.makedirs(snap, exist_ok=True)
    baseline = st.get("production_at") is None
    any_new = False
    for path in deliverable_files(brief):
        key = os.path.join(snap, hashlib.sha1(path.encode()).hexdigest() + ".json")
        try:
            old = json.load(open(key))
        except (OSError, ValueError):
            old = None
        now = stamp(path)
        if old is not None and old["stamp"] == now:
            continue
        new = units(path)
        if old is None and baseline:
            old = {"units": new}  # the baseline, taken at the session's first call
        elif produced((old or {}).get("units"), new):
            any_new = True
            old = {"units": new}
        json.dump({"stamp": now, "units": old["units"] if old else {"kind": "none"}}, open(key, "w"))
    return any_new


# ---------------------------------------------------------------- checks

def failure_signature(text):
    """(file, line, error) of the first failure a check reports, or None when it reports none."""
    m = re.search(r"\*\*\*\s*(.+)", text or "")
    if not m:
        return None
    loc = re.search(r'line (\d+) of "([^"]+)"', text[m.start():m.start() + 2000])
    return [os.path.basename(loc.group(2)) if loc else "", loc.group(1) if loc else "", m.group(1).strip()[:120]]


def settle_check(st):
    """Read the outcome of the last check (its output file, for one run in the background) into the circling count."""
    last = st.get("last_check")
    if not last:
        return
    text = last.get("text") or ""
    if last.get("path") and os.path.exists(last["path"]):
        text = open(last["path"], errors="ignore").read()[-200_000:]
    sig = failure_signature(text)
    if sig is None:
        st["repeats"] = 0
    elif sig == st.get("prev_sig") and last.get("fixed_before"):
        st["repeats"] += 1
    elif sig != st.get("prev_sig"):
        st["repeats"] = 0
    st["prev_sig"] = sig
    st["last_check"] = None


# ---------------------------------------------------------------- a working session's guard and record

def session_guard(hook, rec):
    """What any working session may not do: wait, start subagents, read what is already in its context, check again
    after the same failure, and read past its limits before it has produced (a quick fix: past its budget)."""
    tool, inp, session = hook.get("tool_name"), hook.get("tool_input") or {}, hook.get("session_id", "")
    if rec.get("state") == "parked":  # woken early (its run's completion): the harness resumes it when it may go on
        return deny("You are parked: the producing slot is another worker's until what you wait for has come and the "
                    "slot is free, and then the harness resumes you here, your context intact. End your turn now.",
                    end=True)
    # planner-settings.json is what puts a session on the shared graph (CLAUDE_CODE_TASK_LIST_ID); every other
    # session's task list is its own, and a worker is told to make its plan there.
    if tool in ("TaskCreate", "TaskUpdate") and rec.get("settings") == v2.GRAPH_SETTINGS \
            and not v2.ROLES.get(rec.get("role"), {}).get("graph"):
        return deny("The task graph is the planner's alone to edit. A task designer proposes its tasks and where to "
                    "place them (`v2.py propose ID FILE`) and the planner places them; any other role proposes a "
                    "task to the planner (`v2.py ask --to planner`) or names it in its result.")
    if tool == "TaskUpdate" and v2.ROLES.get(rec.get("role"), {}).get("graph"):
        refused = graph_edit_refusal(inp)
        if refused:
            return deny(refused)
    c = (inp.get("command") or "") if tool == "Bash" else ""
    # the harness's own scripts are not a session's to run: `finalize.py commit ID` would put a task's work in the
    # history with no check and no verdict, and health.py would read it the whole state. Its interface is v2.py,
    # and show.py for reading (2026-09-21).
    for words in segments(shell_syntax(c)):
        for w in words[:2]:
            raw = w.strip("'\"`")
            # the path, not the name: `tools/digest.py` is the repository's even if the harness ever holds one too
            path = os.path.normpath(os.path.join(hook.get("cwd") or v2.PROJECT, os.path.expanduser(raw)))
            # under the harness by its own path, or by the one every protocol writes (.claude/orchestration/…):
            # the two differ only in a test world, where the harness stands outside the project it is given
            under = path.startswith(os.path.join(v2.HERE, "")) or os.path.dirname(path).endswith(
                os.path.join(".claude", "orchestration"))
            if raw.endswith((".py", ".sh")) and under and os.path.basename(path) not in ("v2.py", "show.py"):
                return deny(f"{os.path.basename(path)} is the harness's own to run: the orchestration runs it at the "
                            "moment it belongs. Your commands are `v2.py` — read, change, ask, escalate, park, "
                            "finalize, result, and what your role's protocol names — and `show.py` for reading.")
    if c and any(os.path.basename(w.strip("'\"`")) == "claude" for words in segments(shell_syntax(c)) for w in words[:1]):
        # the Agent tool is refused above, and `claude --bg` is the same thing by another door: a session outside
        # every slot, every limit and every record the harness keeps (2026-09-21)
        return deny("A session starts no session: the harness starts them, in its slots and on its record. Do your "
                    "piece of work yourself, and take a question to its author, the knowledge base or the planner "
                    "(`v2.py ask`).")
    # what the command runs: a change's text is data the harness writes into a file, never run, so these read the call
    # without it — fix-48's edit of its commit message, which named `git rm --cached`, was refused as a git command
    # (2026-09-21). Every other heredoc stays: a script piped to python3 runs what it names.
    ran = shell_syntax(c) if harness_only(c) else c
    parts = change_parts(c) if c else None  # a change's text is data; the rest of its call is read as any command
    if parts:
        ran = shell_syntax(parts.rest) if harness_only(parts.rest) else parts.rest
    if ran and WAIT.search(ran):
        return deny("Waiting is refused (sleep, wait loops, tail -f): a background job's completion notifies you. "
                    "Continue with what follows or with an independent part of the task.")
    out = re.search(r"/tasks/(\w+)\.output\b", ran or "")
    if out and not completed(hook.get("transcript_path", ""), out.group(1)):
        return deny("That job is still running; its completion notifies you. Continue with the task meanwhile.")
    if ran and (GIT_MUTATE.search(ran) or any(GIT_MUTATE.search(shell_syntax(t)) for t in scripts_run(ran, hook.get("cwd")))):
        return deny("The working tree changes only by writing files, and the index and history only by the finalizer: "
                    "no session stages, commits, stashes, checks out, resets, merges or pushes. Read with git status, "
                    "diff, log and show.")
    k = kind(tool, inp, hook.get("cwd"))
    if k == "write" or parts:  # where it writes first: a harness file or another's tree is refused whatever the form
        refused = write_guard(tool, inp, c, rec, hook.get("cwd"))
        if refused:
            return refused
    # then how: whatever the command is, a check's too
    refused = content_write(c, hook.get("cwd")) if c else None
    if refused:
        return deny(refused, fixable=True)
    if k == "check":
        ran = "\n".join((ran, *scripts_run(ran, hook.get("cwd"))))  # a probe in a script is bound as one in the call
        own, run = (rec.get("task"), rec.get("reviews")), v2.run_kind(ran)
        claim = v2.exclusive_claim()
        if repository_check(ran) and rec.get("role") in v2.PRODUCING and v2.apart(rec.get("task")) and \
                not (claim and claim["task"] in own) and batches_on():
            return deny("The repository's check is the harness's: ask for it with `.claude/orchestration/v2.py "
                        "check` — your tree's work is checked with main and the work of every other task waiting, once "
                        "for all, and you are parked until its result comes (the same tree handed over is not checked "
                        "again). Probe what you change meanwhile (`tools/probe_theories.py`, seconds); a timing claims "
                        "the machine first (`v2.py measuring`).")
        capped = None
        if run == "probe" and not (claim and claim["task"] in own):
            limit, named = probe_timeout(ran), True
            if limit is None:  # the tool's own default where it is run: 60 since 2026-09-21 23:02, 1200 before
                limit, named = probe_default(ran, hook.get("cwd")), False
            if limit is None or limit > v2.PROBE_SECONDS:
                capped = (f"A probe gets `--timeout {v2.PROBE_SECONDS}` at most, named in its command"
                          + (f" (this one names {limit})" if named else " (without one it would get the tool's own "
                             + (f"{limit}, as it stands where you run it)" if limit else "default, which could not be "
                                "read where you run it)"))
                          + ": it loads theories on the base heap and takes seconds — every ordinary probe "
                          "of 2026-09-21 took 3-4 — and one that runs longer has a proof method that did not terminate "
                          "(implement-24's hung at a `have` for its whole 900 s, holding a run slot): its log names the "
                          "command it stopped at. A run that needs longer is a measurement: claim the machine first "
                          "(`v2.py measuring`).")
        with v2.admission():  # decided and marked as one: two sessions' guards at once saw room for one run each
            blocked = v2.run_blocked(own, run)
            if not blocked and run == "heavy":
                v2.admit_session(rec.get("name"), rec.get("task"))
                ADMITTED_NOW.append(rec.get("name"))  # taken back if a later part of the guard refuses the call
        if blocked:
            with meter(hook.get("session_id", "")) as m:
                m["run_refused"] = run  # the kind a wait for the machine waits for (v2.cmd_park, v2.machine_wait)
            # "try it when one has ended" invited trying again: implement-78, with nothing else left, tried seven times
            # in forty seconds and then asked the planner, since no park reason fitted (2026-09-21)
            wait = ("park for the machine (`.claude/orchestration/v2.py park machine`)" if rec.get("role") in v2.PRODUCING
                    else "end your turn")  # a supporting session has no slot to free: it ends its turn and is woken
            said = (blocked + " Continue with what needs no check (drafts, the next step's writing); when nothing "
                    f"else is left, {wait}: you are resumed when a run may start."
                    + (" Or lead the probe with QUEUE=1: it is queued, runs as soon as the machine has room, and you "
                       "are parked and resumed with its output." if run == "probe" and rec.get("role") in v2.PRODUCING
                       else ""))
            queued = queued_probe(c, run, rec) if not capped else None
            if queued:
                return allow(dict(inp, command=queued))
            kept = None if capped else through_changes(c)
            if kept:  # the changes go through; only what follows them waits for the machine
                return allow(dict(inp, command=kept + "\n" + STATUS_LINE + "\nprintf '%s\\n' " + shlex.quote(
                    "[Your changes were made; what followed them in this call was not run. " + said + "]")))
            return deny(said + (" And: " + capped if capped else ""), fixable=bool(capped))
        if capped:
            return deny(capped, fixable=True)
        if load(hook.get("session_id", "")).get("run_refused"):  # let through: it waits on the machine no longer
            with meter(hook.get("session_id", "")) as m:
                m["run_refused"] = None
        if claim and claim["task"] in own and not inp.get("run_in_background"):
            MEASURED_NOW.append(claim["task"])  # its run in this call holds the machine (v2.claim_call), if let through
    st = load(session)
    fix = rec.get("fix") or {}
    if fix and k not in ("own",):
        result = os.path.join(".build", "tasks", str(rec.get("task")), "result.md")
        spent = time.time() - fix["since"] > FIX_MINUTES * 60 or rounds_since(
            hook.get("transcript_path", ""), v2.iso(fix["since"]), hook.get("tool_use_id"), st.get("denied") or []) \
            > FIX_ROUNDS
        targets = write_targets(tool, inp, c, hook.get("cwd")) if k == "write" else []
        if spent and not (targets and all(t.endswith(result) for t in targets)):
            return deny(f"The quick fix's budget ({FIX_MINUTES} minutes, {FIX_ROUNDS} requests) is spent: record your result "
                        f"(`v2.py result {rec['task']}`), partial if the fix is not done, so that it becomes a task.")
    r = requested(tool, inp, hook.get("cwd"))
    rewrite, pending = None, None
    if r and k in READING:
        path, first, last, _ = r
        total = lines_of(path)
        if total is not None:
            end = total if last is None else min(last, total)
            known, at = in_context(st, path)
            missing = gaps(known, first, end)
            rel = os.path.relpath(path, v2.PROJECT)
            if end >= first and not missing:  # the filtered read is empty: only its note is shown, and it reads nothing
                return deny(left_out(rel, [(first, end)], at) + " That is the whole of this read, so there is nothing "
                            "else to show, and it counts as no read. Use what you have.")
            size = sum(read_size(path, a, b) or 0 for a, b in missing) if missing else read_size(path, first, last)
            most = shown_bound(inp.get("command")) if tool == "Bash" else READ_BYTES
            shown, rest = within(path, missing, most) if size is not None and size > most else (missing, [])
            if rest and (tool != "Bash" or not shown):  # a quick fix's reads too: its budget is its own
                return deny(too_large(path, missing[0][0] if missing else first,
                                      missing[-1][1] if missing else last, size), fixable=True)
            if rest or (missing and missing != [(first, end)]):  # partly in context, or more than a read shows: what
                rewrite, pending = filtered(inp, path, rel, first, end, missing, at, shown, rest, most)  # it shows, said
    if k == "check":
        answered = [q for q in v2.peek()["asks"].values() if q["from"] == rec.get("name") and q.get("answered")]
        last_answer = max((q["answered"] for q in answered), default=0)
        with meter(session) as st:
            settle_check(st)
            if st["repeats"] >= CIRCLING and last_answer > (st.get("circled_at") or time.time()):
                st["repeats"], st["circled_at"] = 0, None  # an answer on the obstruction has come: check again
            elif st["repeats"] >= CIRCLING:
                st["circled_at"] = st.get("circled_at") or time.time()
        if st["repeats"] >= CIRCLING:
            return deny(f"The same failure came back {st['repeats']} times after fixes ({' '.join(st['prev_sig'] or [])}): "
                        "the fixes are not working. Bring the obstruction to its author or the planner (`v2.py ask`), "
                        "with what you tried, and continue meanwhile with what does not depend on it.")
    if (k == "write" or parts) and rec.get("task"):  # the working tree's changes are the task's that writes them
        v2.own(rec["task"], [os.path.relpath(t, v2.PROJECT) for t in write_targets(
            tool, inp, c, hook.get("cwd")) if t.startswith(v2.PROJECT + os.sep)])
    if k in READING and not fix:
        began = time.time()
        batch = batch_id(hook.get("transcript_path", ""), hook.get("tool_use_id"), BATCH_WAIT)
        with meter(session) as m:  # a read's guard waits up to BATCH_WAIT for its call's line: the guard of a read took
            # a median 0.64 s, of any other call 0.10-0.16 s (09-22) — whether the wait finds it is what these say
            looked = m.setdefault("batch_lookups", {"found": 0, "missed": 0, "seconds": 0.0})
            looked["found" if batch else "missed"] += 1
            looked["seconds"] = round(looked["seconds"] + time.time() - began, 3)
        read = (st.get("batches") or {}).get(batch, 0) if batch else 0
        if read >= BATCH:
            return deny(f"This batch has read {read // 1000}K bytes, and a batch reads at most {BATCH // 1000}K: the "
                        "rest goes in your next batch, which is one more read. A batch is one read however many reads "
                        "it holds; what it may hold is bounded by bytes, so that no batch reads everything.")
        n = reading_requests(hook.get("transcript_path", ""), st.get("production_at"), st.get("refused") or [],
                             hook.get("tool_use_id"), st.get("resolved"))
        first, drawn = tiers(n)
        if drawn > reserve_of(st):
            return deny(f"{n - 1} reads since your last production: the {first} a production allows and the "
                        f"{reserve_of(st)} your reserve held. Write the next part of your "
                        "deliverable from what you hold — a production restarts the first and gives one back to the "
                        f"reserve (it holds at most {RESERVE}) — ask (`v2.py ask`), or record what you have.")
    if rewrite:
        with meter(session) as m:  # what the rewritten read shows, for its record (a Read's note of what it left out)
            m["pending"] = dict(m.get("pending") or {}, **{hook.get("tool_use_id") or "": pending})
        return rewrite
    if (st.get("pending") or {}).get(hook.get("tool_use_id") or ""):  # an earlier rewrite of this call, not run so:
        with meter(session) as m:                                     # what it would have shown is not what it shows
            (m.get("pending") or {}).pop(hook.get("tool_use_id") or "", None)
    if (k == "write" or parts) and tool == "Bash":  # judged as written; what follows a change needs it to go through
        inp = dict(inp, command=after_changes_only(inp.get("command") or ""))
    return bounded(tool, inp, k, hook.get("cwd"), rec.get("name"), hook.get("kept"))



# ---------------------------------------------------------------- what one read shows

CUT, LINES = os.path.join(HERE, "cut.py"), os.path.join(HERE, "lines.py")


def read_size(path, first, last):
    """The bytes of lines first..last (None: to the end) of a file, or None when it cannot be read."""
    try:
        with open(path, "rb") as f:
            return sum(len(line) for i, line in enumerate(f, 1) if i >= first and (last is None or i <= last))
    except OSError:
        return None


def fitting(path, first):
    """The last line from `first` on that a read of READ_BYTES reaches, or first - 1 when line `first` alone is more."""
    total, last = 0, first - 1
    try:
        with open(path, "rb") as f:
            for i, line in enumerate(f, 1):
                if i < first:
                    continue
                total += len(line)
                if total > READ_BYTES:
                    break
                last = i
    except OSError:
        pass
    return last


def too_large(path, first, last, size):
    """Why a read whose size is known is refused, and the read that fits."""
    rel = os.path.relpath(path, v2.PROJECT)
    fits = fitting(path, first)
    end = "the end" if last is None else str(last)
    how = (f"line {first} alone is {read_size(path, first, first):,} bytes: take it in pieces (`cut -c 1-{READ_BYTES} {rel}` "
           "and on)" if fits < first else
           f"lines {first}-{fits} fit: read them (`sed -n '{first},{fits}p' {rel}`), and the rest in further reads")
    return (f"Lines {first}-{end} of {rel} are {size:,} bytes, and one read shows at most {READ_BYTES:,}, so that a "
            f"large chunk is read deliberately, in pieces, rather than taken whole: {how}. A batch of such reads is "
            f"one read, up to {BATCH // 1000}K bytes.")


def in_context(st, path):
    """(the line ranges of a file in the session's context, when it last read them): nothing when the file has changed
    since."""
    seen = st["reads"].get(path)
    if not seen or seen["stamp"] != stamp(path):
        return [], ""
    return seen["ranges"], seen.get("at", "")


def gaps(ranges, first, last):
    """The segments of lines first..last that no range covers, in order. Ranges come as lists from the meter's JSON
    (saw) and as tuples from gaps itself, and sorted() cannot order the two: a read cut at READ_BYTES whose lines were
    partly in context already — two overlapping sources of one read, or a range read before — crashed with a
    TypeError instead of showing anything (review-23 and the planner, 2026-09-21). Each is read as a pair."""
    out, line = [], first
    for a, b in sorted((int(x), int(y)) for x, y in ranges):
        if b < line:
            continue
        if a > last:
            break
        if a > line:
            out.append((line, min(a - 1, last)))
        line = max(line, b + 1)
        if line > last:
            break
    if line <= last:
        out.append((line, last))
    return out


def spans(segments):
    return ", ".join(f"{a}-{b}" if a != b else str(a) for a, b in segments)


def left_out(rel, segments, at):
    """What a filtered read says it left out."""
    return f"[lines {spans(segments)} of {rel} are already in your context (read at {at}, unchanged since) and are left out]"


def saw(st, path, a, b):
    """Lines a..b of a file are in the session's context now; what it held of the file before it changed is not."""
    seen = st["reads"].get(path)
    if not seen or seen["stamp"] != stamp(path):
        seen = st["reads"][path] = {"stamp": stamp(path), "ranges": [], "at": ""}
    seen["ranges"].append([a, b])
    seen["at"] = time.strftime("%H:%M")


def filtered(inp, path, rel, first, end, missing, at, shown=None, rest=(), most=READ_BYTES):
    """(the rewritten call, what it shows) for a read of lines partly in context: the rest, and what was left out said.
    It was refused only when every line was in context, and read whole again when some were (the owner, 2026-09-21:
    filter what is in context and give the rest, saying what was filtered). A read of more than READ_BYTES shows the
    lines that fit (within) and names the rest: it was refused, and of the ten refused on the night of 2026-09-21 six
    were within 12% of the bound (5,013 bytes the least) — a request spent each, the next read the same lines less
    the last few. A command's output is cut at the same bound (bounded, cut.py)."""
    shown = missing if shown is None else shown
    before = gaps(missing, first, end)
    note = " ".join(filter(None, (left_out(rel, before, at) if before else "", cut_short(path, rel, rest, most))))
    command = (f"{shlex.quote(sys.executable)} {shlex.quote(LINES)} {shlex.quote(path)} {shlex.quote(rel)} "
               f"{','.join(f'{a}-{b}' for a, b in shown)} {shlex.quote(note)}")
    return allow(dict(inp, command=command)), {"path": path, "spans": [list(x) for x in shown]}


def within(path, segments, most=READ_BYTES):
    """(the lines of the segments, in order, that one read of `most` bytes shows, and the rest), each as segments."""
    wanted = [i for a, b in segments for i in range(a, b + 1)]
    sizes, top = {}, max(wanted, default=0)
    try:
        with open(path, "rb") as f:
            for i, line in enumerate(f, 1):
                if i > top:
                    break
                sizes[i] = len(line)
    except OSError:
        return [], list(segments)
    wanted = [i for i in wanted if i in sizes]
    total, n = 0, 0
    while n < len(wanted) and total + sizes[wanted[n]] <= most:
        total += sizes[wanted[n]]
        n += 1
    return runs(wanted[:n]), runs(wanted[n:])


def runs(lines):
    """Line numbers, in order, as segments of consecutive ones."""
    out = []
    for i in lines:
        if out and out[-1][1] == i - 1:
            out[-1][1] = i
        else:
            out.append([i, i])
    return [tuple(x) for x in out]


def cut_short(path, rel, rest, most=READ_BYTES):
    """What a read of more than it shows (READ_BYTES, or its declared bound) says of the lines it did not show, and how
    to read on."""
    if not rest:
        return ""
    fits = fitting(path, rest[0][0])
    on = (f"`sed -n '{rest[0][0]},{min(fits, rest[0][1])}p' {rel}`" if fits >= rest[0][0]
          else f"line {rest[0][0]} alone is more: `cut -c 1-{READ_BYTES} {rel}` and on")
    return (f"[lines {spans(rest)} of {rel} are not shown: this read shows at most {most:,} bytes (lead a call with "
            f"`SHOW=20K` for more, up to {BATCH // 1000}K). Read on where you need to ({on}); a batch of such reads is "
            f"one read, up to {BATCH // 1000}K bytes]")


def allow(inp):
    """The call, run as rewritten: a PreToolUse hook's `updatedInput` (Claude Code 2.1.273). Under auto mode the
    rewritten call still goes to the classifier; an allow from a hook does not pass it by."""
    return {"hookSpecificOutput": {"hookEventName": "PreToolUse", "permissionDecision": "allow", "updatedInput": inp}}


# The shape of a command sent through cut.py: the session's command in a group whose status is written after its
# output, for cut.py to end with (a pipeline ends with the status of its last command, and the check's failing must
# still read as a failure), and a leading `cd` outside it, so that it still moves the session's shell as it asked.
# unwrapped() takes it off again, for whatever reads the call after it ran.
WRAP_OPEN, WRAP_CLOSE = "{ ( ", "\n) 2>&1; printf '\\n\\036%s\\n' \"$?\"; } | "  # ( ): an `exit` still has its status written
WRAPPED = re.compile(r"^(\s*cd\s+[^;&|]+?\s*&&\s*)?" + re.escape(WRAP_OPEN) + r"(.*)" + re.escape(WRAP_CLOSE)
                     + r"[^\n]*cut\.py[^\n]*$", re.S)
KEPT = re.compile(r"output is kept in (\S+?\.txt)")  # cut.py's words for where it kept a call's output


# A check a session runs goes to its end and ends by listing every error it reported, one line each with where it
# stands (the owner, 2026-09-21: all the errors at once, dealt with at once, rather than one run for each): its output
# alone says little — the repository's checks log Isabelle's messages and print a summary at their end — so
# check_errors.py gathers them from the logs it wrote too (a probe's under its --work, a check's under its --output).
# The runner stands inside the cut, whose end is where the list stands, and alone for a check in the background.
CHECK_ERRORS = os.path.join(HERE, "check_errors.py")
RUNNER = re.compile(r"^\S+ \S*check_errors\.py(?: --(?:watch|keep|note) (?:'[^']*'|\S+))* -- bash -c (.+)$", re.S)
LOGGED = re.compile(r"--(?:work|output)(?:=|\s+)(\S+)")  # where a probe or a check writes its logs


def gathering(body, cwd, keep):
    """A check's command, run to its end and ending with every error it reported: through check_errors.py, watching
    where it logs, a long list kept whole in the session's outputs; a probe's proofs forked (forked)."""
    body, dropped = forked(body)
    watched = [os.path.normpath(os.path.join(cwd or v2.PROJECT, os.path.expanduser(p.strip("'\""))))
               for p in LOGGED.findall(HEREDOC.sub(" ", body))]
    return (f"{shlex.quote(sys.executable)} {shlex.quote(CHECK_ERRORS)}"
            + "".join(f" --watch {shlex.quote(w)}" for w in dict.fromkeys(watched))
            + f" --keep {shlex.quote(keep)}" + (f" --note {shlex.quote(FORKED_NOTE)}" if dropped else "")
            + f" -- bash -c {shlex.quote(body)}")


# A probe checked in place (`--parallel-proofs 0`) stops at the first proof that fails; with its proofs forked it
# reports every failing proof of a theory in one run, in the same seconds (5.4 s either way for a theory with three,
# 2026-09-22). 512 of the day's 728 probes ran in place, and 100 times, in 31 sessions, the next probe failed further
# down the same theory: a request and a run for each proof (implement-221 found lines 60, 390 and 395 of one theory in
# three probes). The owner: "the failure outputs should be batched and then fixed together". In place stays for what it
# is for, which proof does not return after a probe timed out, when the call says IN_PLACE=1.
IN_PLACE = re.compile(r"(probe_theories\.py\b(?:[^;&|\n\\]|\\.)*?)\s+--parallel-proofs(?:\s+|=)0(?=\s|$|[;&|)])", re.S)
IN_PLACE_ASKED = re.compile(r"(?:^|[\s;&|(])IN_PLACE=1\s")
FORKED_NOTE = ("[--parallel-proofs 0 was left out of this probe: in place a probe stops at the first proof that fails, "
               "forked it reports every one in the same run. To find a proof that does not return, after a probe timed "
               "out, lead the call with IN_PLACE=1.]")


def forked(body):
    """(the body, whether `--parallel-proofs 0` was left out of a probe in it), heredocs, which are data, as they are."""
    if IN_PLACE_ASKED.search(HEREDOC.sub(" ", body)):
        return body, False
    pieces, at, dropped = [], 0, False
    for m in list(HEREDOC.finditer(body)) + [None]:
        piece = body[at:m.start() if m else len(body)]
        kept = IN_PLACE.sub(r"\1", piece)
        dropped |= kept != piece
        pieces += [kept, m.group(0) if m else ""]
        at = m.end() if m else len(body)
    return "".join(pieces), dropped


def bounded(tool, inp, k, cwd, name, kept=None):
    """A call whose output's size cannot be known before it runs, made to show at most READ_BYTES: a command's output
    through cut.py, which keeps the whole under .build/outputs/NAME/ and says how to read on by its lines. Every
    command is — a check, a script, a write, the harness's own (the owner, 2026-09-21: the limit applies to
    everything, outputs and checks too); a check shows its end, which lists every error it reported (gathering). A
    read of a file's lines is measured beforehand instead (too_large), `v2.py read` bounds itself, and a background
    command writes a file, whose reading is a read: a check in the background still ends with its errors listed."""
    c = inp.get("command") or ""
    if tool != "Bash" or not c.strip() or requested(tool, inp, cwd) or reads_itself(c):
        return None
    m = re.match(r"^(\s*cd\s+([^;&|]+?)\s*&&\s*)(.*)$", c, re.S)
    prefix, body = (m.group(1), m.group(3)) if m else ("", c)
    keep = v2.outputs_of(name)
    if k == "check":
        body = gathering(body, os.path.join(cwd or v2.PROJECT, m.group(2).strip().strip("'\"")) if m else cwd, keep)
    if inp.get("run_in_background"):
        return allow(dict(inp, command=prefix + body)) if k == "check" else None
    return allow(dict(inp, command=f"{prefix}{WRAP_OPEN}{body}{WRAP_CLOSE}{shlex.quote(sys.executable)} "
                                   f"{shlex.quote(CUT)} {shown_bound(c)} {'tail' if k == 'check' else 'head'} "
                                   f"{shlex.quote(keep)}" + (f" {kept}" if kept and k != "check" and not answers(body)
                                                             else "")))
    # a check that failed is fixed in what it checks, not in its command: it is not told to fix the command


def reads_itself(command):
    """Whether the call is a `v2.py read`, which bounds what it shows itself: each source at most READ_BYTES (a brief
    named whole, whole), the call at most BATCH_BYTES (v2.cmd_read)."""
    return own_command(command) and bool(re.search(r"\bv2\.py\s+read\b", command))


# commands whose status 1 is an answer, not a failure: nothing found, a difference, a test that did not hold
ANSWERS = {"grep", "egrep", "fgrep", "rg", "diff", "cmp", "test", "["}


def answers(command):
    """Whether a command's status is its last command's answer rather than its failure."""
    words = segments(shell_syntax(command))
    return bool(words) and os.path.basename(words[-1][0]) in ANSWERS


def unwrapped(command):
    """The command a session made, from the one bounded() made of it — cut, run to list its errors, or both; any
    other command as it is (without the zsh option every command is run with, globbing)."""
    if command.startswith(NONOMATCH):
        command = command[len(NONOMATCH):]
    m = WRAPPED.match(command) or re.match(r"^(\s*cd\s+[^;&|]+?\s*&&\s*)?(.*)$", command, re.S)
    prefix, body = m.group(1) or "", m.group(2)
    runner = RUNNER.match(body)
    if runner:
        with contextlib.suppress(ValueError):
            body = shlex.split(runner.group(1))[0]
    return prefix + body if runner or WRAPPED.match(command) else command


def write_targets(tool, inp, command, cwd, content=False):
    """The files a command writes: a change's files, the targets of its redirections and file commands, and the paths
    a script inside it names where it writes them. A path a command merely mentions is not one: a heredoc's
    prose naming `ROOT` had drafts under a task's own directory refused as writes to the tree (2026-09-20). What
    keeps prose out is shell_syntax, which drops heredoc bodies, quoted words and Isabelle's symbols before any of
    this reads them — not a test of the word itself, which would have to drop `ROOT` and every file not yet made.
    `content`: only what writes a file's content (redirections, tee, an in-place edit, a script), not the files a
    command moves, copies, links or removes, which stand (content_write)."""
    command = command or ""
    parts = change_parts(command)
    if parts:  # the files its changes write, exactly, read from the blocks the command will apply; and the rest's
        if content:
            return write_targets(tool, inp, parts.rest, cwd, content=True)
        changed = [v2.change_path(shell_context(before, cwd)[0], op["path"])
                   for before, _, text in parts.changes for op in v2.change_blocks(text)[0]]
        return list(dict.fromkeys(changed + write_targets(tool, inp, parts.rest, cwd)))
    base, known = shell_context(command, cwd)
    at = lambda w: os.path.normpath(os.path.join(base, os.path.expanduser(
        re.sub(r"\$\{?(\w+)\}?", lambda m: known.get(m.group(1), m.group(0)), w.strip("'\"`")))))
    # a redirection writes where the call stands then: every `cd` before it counts, not only a leading one —
    # brief-141's `v2.py change … EOF` then `cd .build/tasks/141/brief && jq … > proposal.json` was read as writing the
    # project's proposal.json, and refused (2026-09-22 10:46)
    names, here = [], cwd or v2.PROJECT
    for seg in re.split(r"&&|\|\||;|\n", shell_syntax(command)):
        moved = re.match(r"^\s*cd\s+(\S+)\s*$", seg)
        if moved and "$" not in moved.group(1):
            here = os.path.normpath(os.path.join(here, os.path.expanduser(moved.group(1).strip("'\""))))
            continue
        names += [os.path.join(here, os.path.expanduser(m)) if "$" not in m else m
                  for match in REDIRECT.findall(seg) for m in match if m]
    for words in segments(shell_syntax(command)):
        if not words:
            continue
        cmd, operands = os.path.basename(words[0]), [w for w in words[1:] if not w.startswith("-")]
        if cmd in ("cp", "install", "ln"):  # what it copies from is read: only where it copies to is written
            given = next((words[x + 1] for x in range(1, len(words) - 1) if words[x] in ("-t", "--target-directory")),
                         next((w.split("=", 1)[1] for w in words if w.startswith("--target-directory=")), None))
            # implement-56's `cp theories/A.thy … .build/tasks/56/draft/` was refused as writing the tree (2026-09-21)
            operands = [given] if given else operands[-1:]
        if cmd in FILE_WRITERS and not (content and cmd not in ("tee", "truncate")):
            names += operands
        elif (cmd == "sed" and any(w.startswith("-i") for w in words[1:])) or (cmd == "perl" and any(
                re.match(r"^-(?![MmIx])\w*i", w) for w in words[1:])):  # its script is not one of its files
            # perl's were not read: implement-76's `perl -0pi -e '…' runprobe.sh` on its own draft under .build/ was
            # refused as an in-place edit of files that could not be read (2026-09-22)
            names += [w for w in operands if os.path.lexists(at(w))]
    names += [m for match in SCRIPT_TARGET.findall(command) for m in match if m]
    given = dict(PY_ASSIGN.findall(command))
    names += [given[v] for match in SCRIPT_NAMED.findall(command) for v in match if v and v in given]
    return list(dict.fromkeys(at(w) for w in names if w.strip("'\"`") not in ("", "/dev/null")))


ASSIGN = re.compile(r"(?:^|[;\n]|&&)\s*(?:export\s+)?([A-Za-z_]\w*)=(\"[^\"`]*\"|'[^']*'|[^\s;&|`'\"(]+)(?=\s*(?:$|[;\n]|&&))")


def shell_context(command, cwd):
    """(where relative paths start, {NAME: value}): a leading `cd DIR` moves the start, and a plain assignment standing
    as a command of its own (`W=.build/tasks/80/time;`) gives its value — so that `cd DIR && … > out` and
    `… > $W/out` are judged where they write. fix-80.2 was refused four writes under .build/ that the guard read as
    written into its tree (2026-09-21). A value made from variables known before it is followed (review-227's
    `T="$TMPDIR/r227"; … > "$T/$n"` was refused as a redirection into the tree, 2026-09-22 20:12); one made by a
    command is not."""
    base = cwd or v2.PROJECT
    lead = re.match(r"^\s*cd\s+([^;&|\n]+?)\s*(?:&&|;|\n)", shell_syntax(command))
    if lead and "$" not in lead.group(1):
        base = os.path.normpath(os.path.join(base, os.path.expanduser(lead.group(1).strip("'\""))))
    known = {"PWD": base, "TMPDIR": os.environ.get("TMPDIR") or "/tmp"}  # a temporary file's place, as the shell has it
    for name, value in ASSIGN.findall(HEREDOC.sub(" ", command or "")):
        known[name] = value.strip("'") if value.startswith("'") else re.sub(
            r"\$\{?(\w+)\}?", lambda m: known.get(m.group(1), m.group(0)), value.strip('"'))
    return base, known


def write_guard(tool, inp, command, rec, cwd):
    """HANDOFF.md is the planner's; while another task's finalization is in flight, it holds the working tree: every
    other session writes only under .build/ (and the harness's own files), and is told when the tree is free.

    A task file is written by no session at all. "The task graph is the planner's alone to edit" was held over
    TaskCreate and TaskUpdate, and the list is a directory of JSON files a Write or a redirection reaches as easily
    — past the lock Claude Code keeps on a task and past the id allocation, and for every role (2026-09-21)."""
    targets = write_targets(tool, inp, command, cwd)
    graph = os.path.join(v2.TASKS, v2.LIST) + os.sep
    if any(t.startswith(graph) for t in targets):
        return deny("A task file is not written by hand: the graph's own tools write it, and they take Claude Code's "
                    "lock on the task and allocate its id — TaskCreate and TaskUpdate for the planner, "
                    "`v2.py blockers` for an edge, `v2.py accept` for a brief's proposed tasks, and `v2.py propose` "
                    "for a task designer, which proposes and does not write.")
    # the harness is the owner's, and nothing in it is a task's deliverable: a session that edited it would change
    # the rules it is working under, and `.claude/` is exempt from the tree's ownership, so nothing would record it
    # its state included: `state/no-launch`, `state/graph-held` and `state/stopped` are the owner's switches, and a
    # session that removed one would start the run again from inside it. The harness writes its own state through
    # its commands, which are `own` and never reach this guard.
    harness = [os.path.join(d, "") for d in (v2.HERE, v2.STATE)]  # the state stands elsewhere when ORCH_STATE_DIR says
    # and every task tree's copy of it: a tree session's hooks run that copy, so one that edited it — the line that
    # hands its calls to the one harness first — would run under rules it wrote itself (2026-09-21)
    copy = os.sep + os.path.join(".claude", "orchestration") + os.sep
    trees = os.path.join(v2.PROJECT, v2.TREE_DIR, "")
    if any(t.startswith(h) for t in targets for h in harness) or any(t.startswith(trees) and copy in t for t in targets):
        return deny("The orchestration's own files are the owner's, its state and its switches included: a session "
                    "does the work of its task and does not change the harness it runs under. What you found in it "
                    "goes into your result, or to the planner (`v2.py ask --to planner`, or `v2.py escalate "
                    "--efficiency` for a cost).")
    if rec.get("role") == "reviewer":
        refused = reviewer_write_refusal(targets, command, rec, cwd)
        if refused:
            return deny(refused)
    theirs = {os.path.join(d, f) for d in (v2.PROJECT, v2.tree_of(rec)) for f in ("HANDOFF.md", v2.PLANNER_LOG)}
    if rec.get("role") != "planner" and theirs & set(targets):
        return deny(f"HANDOFF.md is the planner's state and {v2.PLANNER_LOG} is its log: what you did goes into your "
                    "result, which reaches the planner.")
    # A task's own tree is its own: the one tree's holds reach nobody working in one, and what one writes reaches
    # nobody else — as long as each writes where it stands. The library the sessions hold names the repository's
    # own directory by absolute path, so a session in a tree that wrote one of those paths would install its work in
    # the one tree: owned there by its task, which then works there, holding the tree against every other.
    here, trees = v2.tree_of(rec), os.path.join(v2.PROJECT, v2.TREE_DIR, "")
    for t in targets:
        if t.startswith(trees) and not (here != v2.PROJECT and (t + os.sep).startswith(os.path.join(here, ""))):
            other = os.path.relpath(t, trees).split(os.sep)[0]
            return deny(f"{os.path.relpath(t, v2.PROJECT)} is in task {other}'s own tree, which is that task's alone: "
                        "no other session writes it. What its work needs goes to its session or the planner "
                        "(`v2.py ask`); your own work is written where you stand.")
    if here != v2.PROJECT:
        main = [t for t in targets if t.startswith(v2.PROJECT + os.sep) and not v2.exempt(os.path.relpath(t, v2.PROJECT))]
        if main:
            rel, mine = os.path.relpath(main[0], v2.PROJECT), os.path.relpath(here, v2.PROJECT)
            return deny(f"You work in your task's own tree, {mine}, and {rel} is the repository's own directory: "
                        f"the absolute paths you hold from the library point there. Write {mine}/{rel} (or {rel} "
                        "relative to where you stand); the one tree is written only by the tasks that work in it.",
                        fixable=True)
    st = v2.peek()
    locked = v2.locked_files(st, rec)
    for t in targets:  # the files of a finalization in flight are its own until it is committed
        if t in locked:
            task = locked[t]
            return deny(f"{os.path.relpath(t, v2.PROJECT)} belongs to task {task}'s finalization, which is "
                        f"{st['tasks'][task]['stage']}: no other session writes it until that task has landed. Write "
                        f"your change to a draft under .build/tasks/{rec.get('task')}/ and install it after.", fixable=True)
    holder = v2.tree_holder(st, rec)
    tree = [t for t in targets if t.startswith(v2.PROJECT + os.sep) and not v2.exempt(os.path.relpath(t, v2.PROJECT))]
    if holder and tree:
        v2.mark_tree_wait(rec["name"], holder)
        stage = st["tasks"][holder]["stage"]
        what = ("parked for its run, which reads its changes" if stage == "parked" else
                f"its finalization, {stage}: its check, review and commit see its changes alone")
        if not rec.get("task"):  # the planner, a consultant: no drafts of a task, no park — the holder's to change
            # plan-35 was told to write drafts under `.build/tasks/None/` and to park (2026-09-22 03:14)
            return deny(f"Task {holder} holds the working tree ({what}): until it lets it go, what stands there is "
                        f"changed by that task alone. Tell it what should change (`.claude/orchestration/v2.py tell "
                        f"{holder} \"…\"`); it lets the tree go at its hand-over.")
        return deny(f"Task {holder} holds the working tree ({what}). Until it lets it go, write new files as drafts under "
                    f".build/tasks/{rec.get('task')}/ and keep your edits of existing files for after; you are told when "
                    "the tree is yours. With nothing productive left meanwhile, park for it "
                    "(`.claude/orchestration/v2.py park tree`): another worker produces.", fixable=True)
    # fixable: its number is said, since the correction is its paths moved under the drafts — implement-62, told no
    # number, corrected its next command and then a guessed one (2026-09-22)
    return None


def reviewer_write_refusal(targets, command, rec, cwd):
    """What a reviewer may write in the repository, or why not (C7, the owner's yes of 2026-09-23): its own record and
    the reviewed task's (.build/tasks/ID/ — its verdict, its scratch, and the task's commit message and result, which
    it corrects where they misstate the work), and by `=== row THEORY` the row of a theory that task changed, when
    THEORY_MAP.md is among the files it hands over. Nothing else of the repository or of the task's tree: a finding
    about a theory, code or a decision entry is a rejection, and "the reviewer judges, never produces" holds by
    construction (a reviewer stands in the reviewed task's tree, which no guard kept it from writing). Its scratch
    outside the repository is its own. About 12 of 31 rejections were words a reviewer had already found, each a fix
    round (about 1.7M and 45 minutes)."""
    rid, tid = str(rec.get("task") or ""), str(rec.get("reviews") or rec.get("task") or "")
    real = os.path.realpath
    records = [real(os.path.join(v2.BUILD, x)) + os.sep for x in {rid, tid} if x]
    handed = {real(os.path.join(v2.BUILD, tid, f)) for f in ("finalize.json", "brief.json")}  # the harness's own
    index = real(os.path.join(v2.tree_of(rec), "THEORY_MAP.md"))
    try:
        files = json.load(open(os.path.join(v2.BUILD, tid, "finalize.json")))["files"]
    except (OSError, ValueError, KeyError, TypeError):
        files = []
    changed = {os.path.basename(f)[:-4] for f in files if f.startswith("theories/") and f.endswith(".thy")}
    parts = change_parts(command) if command else None
    ops = [(op, real(v2.change_path(shell_context(before, cwd)[0], op["path"])))
           for before, _, text in (parts.changes if parts else []) for op in v2.change_blocks(text)[0]]
    project = real(v2.PROJECT) + os.sep
    for t in targets:
        r = real(t)
        if not r.startswith(project) or (any((r + os.sep).startswith(d) for d in records) and r not in handed):
            continue
        if r == index:
            wrong = [op for op, path in ops if path == index and not (op["op"] == "row" and op.get("theory") in changed)]
            if "THEORY_MAP.md" in files and ops and not wrong:
                continue
            return ("A reviewer corrects a THEORY_MAP.md row only by `=== row THEORY`, for a theory the task it judges "
                    f"changed ({', '.join(sorted(changed)) or 'none'}), and only when that task hands THEORY_MAP.md "
                    "over; name it under `## Corrected` in your accepting verdict. Anything else in the map is a "
                    "finding: reject, and say it.")
        return (f"A reviewer judges; it writes its verdict and scratch under .build/tasks/{tid}/ (or outside the "
                "repository), and corrects only words that misstate the work: the task's commit message and result "
                f"(.build/tasks/{tid}/commit.md, result.md) and, by `=== row THEORY`, the row of a theory the task "
                "changed — each named under `## Corrected` in an accepting verdict. "
                f"{os.path.relpath(t, cwd or v2.PROJECT)} is none of those: a finding about a theory, code or a "
                "decision entry is a rejection.")
    return None


def graph_edit_refusal(inp):
    """What the planner may not do with TaskUpdate, which is the one door to the graph the harness does not own:
    complete a build, a fix or a review by hand — those complete by landing (check, review, commit) and by a verdict,
    and review comes before commit (the owner, 2026-09-21) — or add a further goal to a chain past the limit
    (v2.goal_refusal)."""
    tid = str(inp.get("taskId") or "")
    task = v2.read_task(tid) or {}
    kind = v2.brief_kind(task.get("description") or "")
    if inp.get("status") == "completed" and task.get("status") != "completed" and kind in v2.LANDS + ("review",):
        return (f"Task {tid} is a {kind} task, and it is not completed by hand: "
                + ("a review is completed by its verdict" if kind == "review" else
                   "its work is complete when it has landed — its check passes, its review accepts it, the "
                   "finalizer commits it — and then the harness completes it and its reviews")
                + ". Review comes before commit, never after. To stop it, drop it (`v2.py drop ID`); to finish work "
                "that stands, queue the task and it goes through its check, review and commit.")
    added, blocks = [str(b) for b in inp.get("addBlockedBy") or []], [str(b) for b in inp.get("addBlocks") or []]
    if added:
        refused = v2.goal_refusal(tid, (task.get("blockedBy") or []) + added, blocks)
        if refused:
            return refused
    for other in blocks:  # `addBlocks` makes another task wait on this one: that one may be the goal being hung
        refused = v2.goal_refusal(other, ((v2.read_task(other) or {}).get("blockedBy") or []) + [tid])
        if refused:
            return refused
    return None


def completed(transcript, job):
    try:
        size = os.path.getsize(transcript)
        with open(transcript, "rb") as f:
            f.seek(max(0, size - 4_000_000))
            text = f.read().decode(errors="ignore")
    except OSError:
        return True
    return re.search(rf"<task-id>{re.escape(job)}</task-id>.*?<status>", text, re.S) is not None


def record(hook, rec):
    """After a working session's tool call: its reads, its production and its checks. Returns a note for it, or None."""
    session, tool, inp = hook.get("session_id", ""), hook.get("tool_name"), hook.get("tool_input") or {}
    if tool == "Bash":
        v2.release_claim(hook.get("tool_use_id"))  # a measurement's hold ends with the call that ran it
        v2.lap("the machine's claim")
        v2.keep_probes(rec.get("task"))  # its probes kept as they are after the call, whatever it removes later
        v2.lap("its probes kept")
    if tool == "Bash" and inp.get("command"):  # the call as the session made it, whichever of the two is given here
        inp = dict(inp, command=unwrapped(inp["command"]))
    response = hook.get("tool_response")
    with meter(session) as st:
        v2.lap("its meter's lock")
        note = _record(hook, rec, st, session, tool, inp, response)
        v2.lap("its reads and production")
        return note


def _record(hook, rec, st, session, tool, inp, response):
    resolved = (st.get("resolved") or {}).get(hook.get("tool_use_id") or "")
    if tool == "Bash" and resolved:  # a `v2.py again` call is the command it ran, whichever form comes here
        inp = dict(inp, command=resolved)
    brief = brief_of(rec)
    now = v2.iso()
    transcript = hook.get("transcript_path", "")
    shown_by_rewrite = (st.get("pending") or {}).pop(hook.get("tool_use_id") or "", None)
    ran = isinstance(response, dict) and response.get("stdout") and not response.get("interrupted")
    if shown_by_rewrite and ran:  # a read filtered of what was in context: the lines it showed are what it read
        for a, b in shown_by_rewrite["spans"]:
            saw(st, shown_by_rewrite["path"], a, b)
    if st.get("production_at") is None:
        check_production(session, brief, st)  # the baseline
        st["production_at"] = now
    k = kind(tool, inp, hook.get("cwd"))
    r = requested(tool, inp, hook.get("cwd"))
    total = lines_of(r[0]) if r and ran else None
    if total is not None and not shown_by_rewrite:  # a read of a file's lines, bounded before it ran: it showed what
        path, first, last, _ = r                     # it named — one rewritten showed what the rewrite did (above)
        saw(st, path, first, total if last is None else min(last, total))
    note = None
    # the call's own request, waited for as the guard waits (BATCH_WAIT): a call that returns at once — a probe put in
    # the background — has its hook run before its line is written, and looked up without waiting its request was
    # not found, so a read's bytes went uncounted in its batch and implement-68 was never told its change and probe
    # could have been one request (2026-09-21)
    mid = batch_id(transcript, hook.get("tool_use_id"), BATCH_WAIT) if k in READING + ("write",) else None
    if k in READING:
        shown = shown_bytes(tool, response)
        most = BATCH if tool == "Bash" and reads_itself(inp.get("command") or "") else (
            shown_bound(inp.get("command")) if tool == "Bash" else READ_BYTES)
        if tool == "Bash" and not inp.get("run_in_background") and shown > most + 1_000:
            # a call the guard sends through cut.py showed more than a read may: the rewrite did not take
            v2.say_once("cut-not-applied", f"ATTENTION a call of {rec.get('name')} showed {shown:,} bytes, more than "
                        f"the {READ_BYTES:,} a read shows: the guard's rewrite of it through cut.py did not apply")
        if mid:  # what the batch has read, which bounds what more it may (the guard)
            st["batches"] = dict(st.get("batches") or {}, **{mid: (st.get("batches") or {}).get(mid, 0) + shown})
    if hook.get("tool_use_id"):  # each call's kind and what it showed, by its id (small_read_before), the last 200
        seen = st.get("calls_shown") or {}
        seen[hook["tool_use_id"]] = [k, shown_bytes(tool, response) if k in READING else 0]
        st["calls_shown"] = dict(list(seen.items())[-200:])
    if k == "check":
        text = json.dumps(response or "")
        # its whole output: a run in the background writes it to a file, and one cut to a read's bytes is kept whole
        path = re.search(r"Output is being written to: (\S+?\.output)", text) or KEPT.search(text)
        st["last_check"] = {"path": path.group(1) if path else None, "text": None if path else text[-200_000:],
                            "fixed_before": st.get("fixed_since", False)}
        st["fixed_since"] = False
    n = reading_requests(transcript, st["production_at"], st.get("refused") or [], hook.get("tool_use_id"),
                         st.get("resolved")) if k in READING else 0
    if (k in ("write", "other", "check") and check_production(session, brief, st)) or (k == "task" and brief["task_tools"]) \
            or (k == "own" and brief["task_tools"] and graph_edited(inp, response)):
        stretch_ends(st, transcript, now)
        if not rec.get("fix"):
            note = (f"Production recorded: the count restarts ({ROUNDS} reads), and your reserve holds "
                    f"{st['reserve']} of {RESERVE}.")
    elif k in READING and not rec.get("fix"):
        note = countdown(st, n)
    if k in ("read", "other") and mid and st.get("small_told") != st.get("production_at"):
        small = small_read_before(transcript, hook.get("tool_use_id"), st)
        if small is not None:
            st["small_told"] = st.get("production_at")  # once between two productions
            note = " ".join(filter(None, [note, (
                f"[Your last request read {small:,} bytes and cost a whole read, as this one does; a read holds up to "
                f"{BATCH // 1000}K. When a step needs several things, name them in one request: several sources in "
                "one `v2.py read`, several calls in one request.]")]))
    if k in ("write", "check") and mid and st.get("ready_told") != mid and ready_before(transcript, hook.get("tool_use_id"), st.get("resolved")):
        st["ready_told"] = mid  # said once a request
        note = " ".join(filter(None, [note, READY_NOTE]))
    return note


# The planner's production is its graph: TaskCreate and TaskUpdate counted, and the harness's own commands that edit
# the graph did not — so the batched edit, `v2.py edit`, and `blockers`, `queue`, `drop`, `accept` spent the reading
# budget that a TaskUpdate a call would have given back (found 2026-09-21, while making every command batchable).
GRAPH_EDITS = re.compile(r"v2\.py\s+(edit|accept|blockers|queue|drop)\b")


def graph_edited(inp, response):
    """Whether a harness command edited the graph: a graph-editing command, and at least one of its answers not a
    refusal (a batch answers once for each group)."""
    if not GRAPH_EDITS.search(inp.get("command") or ""):
        return False
    out = response.get("stdout", "") if isinstance(response, dict) else str(response or "")
    return any(line.strip() and not line.lstrip().startswith("refused") for line in out.splitlines())


def countdown(st, n):
    """What a session has left before it must produce, told after every read, search or check: both tiers."""
    first, drawn = tiers(n)
    reserve = reserve_of(st)
    left, spare = max(0, first - n), max(0, reserve - drawn)
    head = f"Since your last production: {min(n, first)} of {first} reads"
    if drawn:
        head += f"; {drawn} drawn from your reserve, which has {spare} left of {reserve}."
    else:
        head += f"; your reserve holds {reserve} of {RESERVE}."
    # How reads are counted is said once, where it starts to bite — the first read drawn from the reserve and the last
    # one — not after every read: said every time it was 2,850 notes of ~300 characters in sixteen hours of 2026-09-22,
    # 200 of each the same sentence the protocol holds, kept in the context and read again by every later request
    tail = (f" A read is one batch — one request — however many reads it holds, up to {BATCH // 1000}K bytes: put what "
            "you need together. A production restarts the first tier and gives one back to the reserve."
            if drawn == 1 or (left == 0 and spare == 0) else "")
    if left == 0 and spare == 0:
        return (head + " That was your last read: the next produces (writes the next part of a deliverable), asks "
                "(`v2.py ask`) or records a partial result." + tail)
    if left == 0:
        return head + f" The next {spare} read{'s' if spare > 1 else ''} come{'' if spare > 1 else 's'} from the reserve." + tail
    return head + f" {left} more read{'s' if left > 1 else ''} before the reserve." + tail


def guard(hook):
    """The guard's decision, and every refusal recorded: a refused call is a call not made, and it counts in no limit
    counted in requests (the owner, 2026-09-21). Only a read refused late was recorded, for the reading tiers; one
    refused early (a removed tool, a malformed `again`) counted as a read, and the quick fix's budget counted every
    request, refused or not — fix-46 lost one of its eight to a refused form."""
    decision = _guard(hook)
    said = (decision or {}).get("hookSpecificOutput") or {}
    if said.get("permissionDecision") == "deny" and hook.get("tool_use_id"):
        with meter(hook.get("session_id", "")) as st:
            uid = hook["tool_use_id"]
            st["refused"] = (st.get("refused") or []) + ([uid] if uid not in (st.get("refused") or []) else [])
            st["denied"] = ((st.get("denied") or []) + [uid])[-DENIED_KEPT:]  # the quick fix's count: kept past productions
    return decision


DENIED_KEPT = 500  # the newest refused calls kept for counting requests; a quick fix makes at most FIX_ROUNDS


def _guard(hook):
    role, rec = v2.role_of(hook.get("session_id", ""))
    if role is None:
        return None
    tool, inp = hook.get("tool_name"), hook.get("tool_input") or {}
    if tool in REMOVED_TOOLS:
        return deny(f"{tool} is not a session's tool (the owner, 2026-09-21). {REMOVED_TOOLS[tool]}")
    if role == "role-layer":  # what it reasons over is its message: a read would stand in every fork of it
        return deny("A reasoning layer uses no tool: everything it reasons over is in its message, and whatever it "
                    f"read would stand in the prefix of every session of its role. Reason in your reply, and end it "
                    f"with the line `{v2.ROLE_LAYER_DONE}`.")
    fixed = kept = None
    if tool == "Bash" and inp.get("command"):
        fixed, why = again(rec.get("name"), inp["command"])
        if why:
            return deny(why)
        if fixed:  # guarded, rewritten and counted as the command it runs, as if it had been typed
            inp = dict(inp, command=fixed)
            hook = dict(hook, tool_input=inp)
            if hook.get("tool_use_id"):
                with meter(hook.get("session_id", "")) as st:
                    st["resolved"] = dict(st.get("resolved") or {}, **{hook["tool_use_id"]: fixed})
        kept = keep_command(rec.get("name"), inp["command"])
        hook = dict(hook, kept=kept)
    refused = planner_guard(tool, inp, hook.get("cwd"), own_dirs(rec)) if v2.statements_only(rec) else None
    if role != "kb":
        refused = refused or session_guard(hook, rec)
    fixable = (refused or {}).pop("fixable", False)
    said = (refused or {}).get("hookSpecificOutput") or {}
    denied = said.get("permissionDecision") == "deny"
    if denied:  # a check let start by the machine's count, then refused for another reason, starts no run
        for name in ADMITTED_NOW:
            with contextlib.suppress(OSError):
                os.remove(os.path.join(v2.ADMITTED, v2.SESSION_MARK + (name or "unnamed")))
    ADMITTED_NOW.clear()
    if tool == "Bash" and rec.get("task"):
        if not denied:  # where each probe of the call runs, so that it is found wherever that is (v2.probe_dirs)
            v2.softly("where the call's probes run", lambda: v2.note_probe_dirs(
                rec.get("task"), probe_work(inp.get("command") or "", hook.get("cwd"))), default=False)
        v2.keep_probes(rec.get("task"))  # before the call: a call that removes its probes keeps nothing of them
    if MEASURED_NOW and not denied:
        v2.claim_call(MEASURED_NOW[0], hook.get("tool_use_id"))
    MEASURED_NOW.clear()
    if denied and kept and fixable:
        said["permissionDecisionReason"] += " " + fix_note(kept)
    if fixed and not denied and "updatedInput" not in said:
        refused = allow(inp)
    if kept and not denied:
        refused = spilled(refused, inp, rec, kept, hook)
    if tool == "Bash" and not denied:
        refused = globbing(refused, inp)
    return refused  # a refusal is recorded by guard(), whichever check made it


# The sessions' shell is zsh, which ends a whole command at a glob that matches nothing ("no matches found") — however
# its errors are redirected — while the sessions write for bash, where the unmatched glob stays as it is: 65 of the
# 8,842 calls of 2026-09-22, in 41 sessions, lost what followed (design-218 looked for a batch's report with
# `ls -d .build/*150712* … 2>/dev/null`). The owner: every command starts with `setopt nonomatch`; in bash it is an
# unknown command, silenced, and nothing else.
NONOMATCH = "setopt nonomatch 2>/dev/null; "


def globbing(decision, inp):
    said = (decision or {}).get("hookSpecificOutput") or {}
    final = said.get("updatedInput") or inp
    command = final.get("command") or ""
    if not command.strip() or command.startswith(NONOMATCH):
        return decision
    return allow(dict(final, command=NONOMATCH + command))


# A command Claude Code starts is its argument to the shell, and Linux takes at most 128K bytes in one argument
# (MAX_ARG_STRLEN). The sandbox's profile goes into that argument too — a deny path for each of the settings, skills
# and hooks of every registered git worktree among them, so it grows with the trees standing when the session began:
# implement-38's change of 59K bytes (60.7K as the guard ran it) was "command line 200.3KB … (largest single arg
# 200.3KB)" (2026-09-22 09:56, and implement-36's at 07:52), and fix-255's of 23.8K was "145KB" (19:14), where 8.1K
# had started in the same session: its room was about 10K. A call over ARG_SAFE is run from a file, which costs nothing
# — about 8% of the calls of 2026-09-22, every change of a theory's worth among them.
ARG_SAFE = 6_000


def spilled(decision, inp, rec, kept, hook):
    """A call longer than ARG_SAFE, run from a file: the command as it would run is written beside the session's kept
    command (N.run) and the shell sources it (`. FILE`), which reads the same text in the same shell. What the meter
    records is the command as made (`resolved`), as for `v2.py again`."""
    said = (decision or {}).get("hookSpecificOutput") or {}
    final = said.get("updatedInput") or inp
    command = final.get("command") or ""
    if len(command.encode()) <= ARG_SAFE:
        return decision
    path = os.path.join(commands_of(rec.get("name")), f"{kept}.run")
    with open(path, "w") as f:
        f.write(command + "\n")
    if hook.get("tool_use_id"):
        with meter(hook.get("session_id", "")) as st:
            st["resolved"] = dict(st.get("resolved") or {}, **{hook["tool_use_id"]: inp["command"]})
    return allow(dict(final, command=". " + shlex.quote(path)))


def main():
    if sys.argv[1:2] != ["guard"]:
        print(__doc__)
        return 2
    watch = v2.Stopwatch("the guard")
    try:
        hook = json.load(sys.stdin)
        decision = guard(hook)
        watch.done(lambda: f"the guard of a {hook.get('tool_name')} call of "
                           f"{(v2.role_of(hook.get('session_id', ''))[1] or {}).get('name')}")
    except Exception as e:  # noqa: BLE001
        # A guard that fails lets the call through rather than block the work — but silently, it is every limit and
        # every refusal switched off with nothing to show for it, which is the fault of the PreToolUse matcher in
        # another form. It is said, at most once a GUARD_QUIET, because this runs on every tool call of every
        # session and a crashing guard would otherwise flood the log it is meant to be read in.
        if (v2.age_of("guard-failed") or GUARD_QUIET + 1) > GUARD_QUIET:
            with contextlib.suppress(OSError):
                open(os.path.join(v2.STATE, "guard-failed"), "w").write(str(time.time()))
            v2.log(f"ATTENTION the guard failed and let the call through: {e!r}")
        return 0
    if decision:
        print(json.dumps(decision))
    return 0


if __name__ == "__main__":
    sys.exit(main())
