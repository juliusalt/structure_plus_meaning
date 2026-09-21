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
WRITE_SHELL = re.compile(r"\bsed\s+-i\b|(?<![0-9&])>>?\s*(?!/dev/null\b|&)[^\s|;&>]+|\btee\s+(?:-a\s+)?[^\s|;&]+"
                         r"|(?:^|[;&|]\s*)(?:" + "|".join(w for w in FILE_WRITERS if w != "tee") + r")\s")
# What a script inside the command writes, named where it writes it
WRITE_SCRIPT = re.compile(r"""\.write_text\(|\.writelines\(|shutil\.(?:copy|move)|open\(\s*[^)]*['"][wa]""")
HEREDOC = re.compile(r"<<-?\s*(['\"]?)(\w+)\1\r?\n.*?^\s*\2\s*$", re.S | re.M)
QUOTED = re.compile(r"'[^']*'|\"[^\"]*\"")
REDIRECT = re.compile(r"""(?<![0-9&])>>?\s*(?:'([^']+)'|"([^"]+)"|([^\s|;&>]+))""")
# a path a script inside the command writes to, named literally
SCRIPT_TARGET = re.compile(r"""(?:Path\(\s*|open\(\s*)['"]([^'"]+)['"]\s*\)?\s*(?:\.\s*write_text|\.\s*open\(\s*['"][wa])"""
                           r"""|open\(\s*['"]([^'"]+)['"]\s*,\s*['"][wa]""")


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
                        r"|tag\s+(?!-l\b|--list\b|-n\d*\b|--contains\b|--points-at\b)[^\s|;&]+)\b")
READS = re.compile(r"^\s*(?:cd\s+[^;&|]+&&\s*)?(?:sed\s+-n|cat|head|tail|grep|rg|find|ls|wc|awk|nl|less|more"
                   r"|git\s+(?:show|log|diff|status|grep|blame)|(?:python3?\s+)?\S*show\.py)\b")
CHECK = re.compile(r"probe_theories\.py|incremental_check\.py|isabelle\s+(?:build|ML_process|process)|tools/build\.py")
WAIT = re.compile(r"\bsleep\s+(?:[2-9]|\d{2,}|\d+[smh])|\btail\s+-[a-zA-Z]*f\b|\bwatch\s|\b(?:until|while)\b[^;]*;\s*do\b[^;]*\bsleep\b")
RUNNERS = ("python", "python3", "sh", "bash", "env")
# What the planner does not read: theory and code bodies, logs, and under .build anything but the tasks' documents.
BODY = re.compile(r"\.(?:thy|ML|sml|py|sh|log|out|output)$|(?:^|/)(?:theories|tools)(?:/|$)|(?:^|/)\.build(?:/|$)(?!tasks/[^/]+/[^/]+\.md$|outputs/)")
CONTENT = {"cat", "sed", "head", "tail", "grep", "egrep", "fgrep", "rg", "awk", "nl", "less", "more", "bat", "diff",
           "strings", "xxd", "od", "cut", "sort", "uniq", "jq", "tac"}
PATTERNED = {"grep", "egrep", "fgrep", "rg", "sed", "awk"}  # their first operand is a pattern or a script
STAT = re.compile(r"--(?:stat|shortstat|numstat|name-only|name-status|summary)\b")
PATCH = re.compile(r"(?:^|\s)(?:-p|-u|--patch|-L\S*|--word-diff\S*|--full-diff)(?:\s|$)")


CHANGE_VERB = re.compile(r"\bv2\.py\s+change\b")
# the one form of a change: its changes in a quoted heredoc of the same call, and nothing else in it but a leading cd
CHANGE_CALL = re.compile(r"^\s*(?:cd\s+([^;&|\n]+?)\s*&&\s*)?(?:python3?\s+)?\S*v2\.py\s+change\s*<<-?\s*(['\"]?)(\w+)\2"
                         r"[ \t]*\n(.*?)\n?^[ \t]*\3[ \t]*$\s*\Z", re.S | re.M)
CHANGE_POINTER = ("Files are changed with `.claude/orchestration/v2.py change <<'EOF'` … `EOF`: any number of changes "
                  "to any number of files in one call — `=== write PATH` and the whole file, or `=== replace PATH` and "
                  "blocks of `<<<<<<< SEARCH`, the text as it stands, `=======`, its replacement, `>>>>>>> REPLACE` — "
                  "judged whole, written all or none, and what refuses it said.")


def change_call(command):
    """(the directory a `v2.py change` call changes from, relative to the session's, or ""; whether its heredoc is
    quoted; the text of its changes), or None when the call is not in that one form."""
    m = CHANGE_CALL.match(command or "")
    return ((m.group(1) or "").strip().strip("'\""), bool(m.group(2)), m.group(4)) if m else None


def scratch(path):
    """Whether a path is the build directory's own — a task's drafts, a run's output — where a command's output may be
    written: not a task's tree, which holds the repository's files, nor what the harness keeps of a session's calls."""
    rel = os.path.relpath(path, v2.PROJECT)
    inside = re.match(r"\.build/trees/[^/]+/(.*)$", rel)  # a tree's .build is the one .build, behind a link
    rel = inside.group(1) if inside else rel
    return rel.startswith(".build/") and not rel.startswith((".build/trees/", ".build/outputs/"))


def content_write(command, cwd=None):
    """Why a command that writes a file's content is refused, or None (the owner, 2026-09-21: one way to change files,
    which names them exactly and fails loudly). A redirection, tee, `sed -i` or a script that writes fails silently
    when it matches nothing, and names its files only as far as the shell can be read; a command that moves, copies
    or removes files names them, and stands."""
    if own_command(command) and CHANGE_VERB.search(HEREDOC.sub(" ", command)):
        call = change_call(command)
        if not call:
            return ("`v2.py change` takes its changes in a quoted heredoc of the same call, and the call holds nothing "
                    "else: `.claude/orchestration/v2.py change <<'EOF'`, the changes, `EOF` (a `cd DIR &&` may lead).")
        if not call[1]:
            return ("Quote the heredoc's delimiter (`v2.py change <<'EOF'`): unquoted, the shell expands `$` and "
                    "backquotes inside the changes before the command sees them.")
        return None
    syntax = shell_syntax(command)
    how = ("a redirection into a file" if any(not t.strip("'\"").startswith("/dev/") for t in redirections(command))
           else "tee" if any(os.path.basename(w[0]) == "tee" for w in segments(syntax))
           else "an in-place edit" if re.search(r"\b(?:sed|perl)\s+(?:-\w+\s+)*-\w*i", syntax)
           else "a script that writes" if WRITE_SCRIPT.search(command) else None)
    if not how:
        return None
    targets = write_targets("Bash", {}, command, cwd)
    if targets and all(scratch(t) for t in targets):  # a program's output, or a draft, in the build directory
        return None
    return (f"Not by {how}: {CHANGE_POINTER} A command's output may be written under .build/ (a task's drafts, a "
            "run's output); the repository's own files change by `v2.py change` alone. Moving, copying and removing "
            "files stand.")


# Every command a session makes is kept, numbered (the owner, 2026-09-21), so that one that failed or was refused is
# fixed rather than written again whole: of the first runs' 1,799 commands 146 failed, and 40 were followed by a
# near-copy of themselves — 88K characters written again, the largest 12K — and with every file's change now a
# command, a refused batch would be written again whole too. `v2.py again N` sends only the correction: SEARCH/REPLACE
# blocks on command N's text, applied here, and what they make is guarded and run as if it had been typed.
AGAIN = re.compile(r"^\s*(?:python3?\s+)?\S*v2\.py\s+again(?:\s+(\d+))?\s*<<-?\s*(['\"]?)(\w+)\2[ \t]*\n(.*?)\n?^[ \t]*\3[ \t]*$\s*\Z",
                   re.S | re.M)
AGAIN_VERB = re.compile(r"\bv2\.py\s+again\b")
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
        with contextlib.suppress(OSError):  # the newest are what a correction is sent for
            os.remove(os.path.join(folder, f"{old}.sh"))
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
        return None, ("`v2.py again N <<'EOF'` takes the SEARCH/REPLACE blocks that fix command N (your last, N left "
                      "out; none, to run it as it was) in a quoted heredoc of the same call, and the call holds nothing "
                      "else.")
    if not m.group(2):
        return None, "Quote the heredoc's delimiter (`v2.py again N <<'EOF'`), so that the blocks reach it as they are."
    kept = kept_command(name, int(m.group(1)) if m.group(1) else None)
    if not kept:
        return None, (f"No command {m.group(1)} of yours is kept." if m.group(1) else "No command of yours is kept yet.")
    n, text = kept
    if not m.group(4).strip():  # no correction: the command as it was, not written again
        return text, None
    ops, problems = v2.change_blocks(f"=== replace command {n}\n" + m.group(4))
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


def deny(text, fixable=False):
    """A refusal; `fixable` when what is wrong is the command itself, which is then told how to send its correction
    (guard() takes the mark off before Claude Code sees the answer)."""
    out = {"hookSpecificOutput": {"hookEventName": "PreToolUse", "permissionDecision": "deny",
                                  "permissionDecisionReason": text}}
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


def segments(command):
    """The simple commands of a command line, as argument lists (a pipeline's and a sequence's parts apart)."""
    out = []
    for part in re.split(r"\|\|?|&&|;|\n", command):
        try:
            words = shlex.split(part)
        except ValueError:
            words = part.split()
        while words and re.match(r"^\w+=", words[0]):
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
    c = " ".join((inp.get("command") or "").split())
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


def kind(tool, inp):
    """write, read, check, own (the harness's commands), or other."""
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
        if own_command(c) and CHANGE_VERB.search(HEREDOC.sub(" ", c)):
            return "write"  # the one way a session changes files
        if own_command(c):
            # the harness's commands that print what a session reads are reads, bounded as any is: `v2.py proposal`
            # printed every brief it was asked for at once, counted as nothing (2026-09-21)
            return "read" if V2_READS.search(c) else "own"
        if CHECK.search(HEREDOC.sub(" ", c)):  # a heredoc naming a check's tool is prose, not a check
            return "check"
        if WRITE_SHELL.search(shell_syntax(c)) or WRITE_SCRIPT.search(c):
            return "write"
        if READS.match(c):
            return "read"
    return "other"


def rounds_since(transcript, since, tool_use=None):
    """Requests recorded after a moment (v2.iso: the transcripts' form), and the request making this call when it is not
    recorded yet: a hook can run before the request that made its call is written (ctx_gauge.py)."""
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
    ids, current = set(), False
    for line in lines:
        if '"assistant"' not in line:
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("type") == "assistant" and not d.get("isSidechain") and d.get("timestamp", "") > since:
            ids.add((d.get("message") or {}).get("id"))
            current = current or bool(tool_use and tool_use in line)
    return len(ids) + (0 if current else 1)


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
                    "slot is free, and then the harness resumes you here, your context intact. End your turn now.")
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
    if c and WAIT.search(c):
        return deny("Waiting is refused (sleep, wait loops, tail -f): a background job's completion notifies you. "
                    "Continue with what follows or with an independent part of the task.")
    out = re.search(r"/tasks/(\w+)\.output\b", c)
    if out and not completed(hook.get("transcript_path", ""), out.group(1)):
        return deny("That job is still running; its completion notifies you. Continue with the task meanwhile.")
    if c and GIT_MUTATE.search(c):
        return deny("The working tree changes only by writing files, and the index and history only by the finalizer: "
                    "no session stages, commits, stashes, checks out, resets, merges or pushes. Read with git status, "
                    "diff, log and show.")
    k = kind(tool, inp)
    if k == "write":  # where it writes first: a harness file or another's tree is refused whatever the form
        refused = write_guard(tool, inp, c, rec, hook.get("cwd"))
        if refused:
            return refused
    refused = content_write(c, hook.get("cwd")) if c else None  # then how: whatever the command is, a check's too
    if refused:
        return deny(refused, fixable=True)
    if k == "check":
        claim, runs = v2.exclusive_claim(), v2.isabelle_runs()
        holder = claim["task"] if claim else None
        if holder and holder not in (rec.get("task"), rec.get("reviews")):
            return deny(f"Task {holder} holds the machine ({claim['why']}): nothing else runs meanwhile. Continue with "
                        "what needs no check (drafts, the next step's writing); try it after.")
        if runs >= v2.ISABELLE_MAX:
            return deny(f"{runs} Isabelle runs are going on this machine (at most {v2.ISABELLE_MAX}: three have filled its "
                        "memory). Continue with what needs no check; try it when one has ended.")
    st = load(session)
    fix = rec.get("fix") or {}
    if fix and k not in ("own",):
        result = os.path.join(".build", "tasks", str(rec.get("task")), "result.md")
        spent = time.time() - fix["since"] > FIX_MINUTES * 60 or rounds_since(
            hook.get("transcript_path", ""), v2.iso(fix["since"]), hook.get("tool_use_id")) > FIX_ROUNDS
        targets = write_targets(tool, inp, c, hook.get("cwd")) if k == "write" else []
        if spent and not (targets and all(t.endswith(result) for t in targets)):
            return deny(f"The quick fix's budget ({FIX_MINUTES} minutes, {FIX_ROUNDS} rounds) is spent: record your result "
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
            if size is not None and size > READ_BYTES:  # a quick fix's reads too: its budget is its own
                return deny(too_large(path, missing[0][0] if missing else first,
                                      missing[-1][1] if missing else last, size), fixable=True)
            if missing and missing != [(first, end)]:  # partly in context: the rest is read, and what is left out said
                rewrite, pending = filtered(inp, path, rel, first, end, missing, at)
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
    if k == "write" and rec.get("task"):  # the working tree's changes are attributed to the task that writes them
        v2.own(rec["task"], [os.path.relpath(t, v2.PROJECT) for t in write_targets(tool, inp, c, hook.get("cwd"))
                             if t.startswith(v2.PROJECT + os.sep)])
    if k in READING and not fix:
        batch = batch_id(hook.get("transcript_path", ""), hook.get("tool_use_id"), BATCH_WAIT)
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
    """The segments of lines first..last that no range covers, in order."""
    out, line = [], first
    for a, b in sorted(ranges):
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


def filtered(inp, path, rel, first, end, missing, at):
    """(the rewritten call, what it shows) for a read of lines partly in context: the rest, and what was left out said.
    It was refused only when every line was in context, and read whole again when some were (the owner, 2026-09-21:
    filter what is in context and give the rest, saying what was filtered)."""
    note = left_out(rel, gaps(missing, first, end), at)
    command = (f"{shlex.quote(sys.executable)} {shlex.quote(LINES)} {shlex.quote(path)} {shlex.quote(rel)} "
               f"{','.join(f'{a}-{b}' for a, b in missing)} {shlex.quote(note)}")
    return allow(dict(inp, command=command)), {"path": path, "spans": [list(x) for x in missing]}


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
RUNNER = re.compile(r"^\S+ \S*check_errors\.py(?: --(?:watch|keep) (?:'[^']*'|\S+))* -- bash -c (.+)$", re.S)
LOGGED = re.compile(r"--(?:work|output)(?:=|\s+)(\S+)")  # where a probe or a check writes its logs


def gathering(body, cwd, keep):
    """A check's command, run to its end and ending with every error it reported: through check_errors.py, watching
    where it logs, a long list kept whole in the session's outputs."""
    watched = [os.path.normpath(os.path.join(cwd or v2.PROJECT, os.path.expanduser(p.strip("'\""))))
               for p in LOGGED.findall(HEREDOC.sub(" ", body))]
    return (f"{shlex.quote(sys.executable)} {shlex.quote(CHECK_ERRORS)}"
            + "".join(f" --watch {shlex.quote(w)}" for w in dict.fromkeys(watched))
            + f" --keep {shlex.quote(keep)} -- bash -c {shlex.quote(body)}")


def bounded(tool, inp, k, cwd, name, kept=None):
    """A call whose output's size cannot be known before it runs, made to show at most READ_BYTES: a command's output
    through cut.py, which keeps the whole under .build/outputs/NAME/ and says how to read on by its lines. Every
    command is — a check, a script, a write, the harness's own (the owner, 2026-09-21: the limit applies to
    everything, outputs and checks too); a check shows its end, which lists every error it reported (gathering). A
    read of a file's lines is measured beforehand instead (too_large), `v2.py read` bounds itself, and a background
    command writes a file, whose reading is a read: a check in the background still ends with its errors listed."""
    c = inp.get("command") or ""
    if tool != "Bash" or not c.strip() or requested(tool, inp, cwd) \
            or (own_command(c) and re.search(r"\bv2\.py\s+read\b", c)):
        return None
    m = re.match(r"^(\s*cd\s+([^;&|]+?)\s*&&\s*)(.*)$", c, re.S)
    prefix, body = (m.group(1), m.group(3)) if m else ("", c)
    keep = v2.outputs_of(name)
    if k == "check":
        body = gathering(body, os.path.join(cwd or v2.PROJECT, m.group(2).strip().strip("'\"")) if m else cwd, keep)
    if inp.get("run_in_background"):
        return allow(dict(inp, command=prefix + body)) if k == "check" else None
    return allow(dict(inp, command=f"{prefix}{WRAP_OPEN}{body}{WRAP_CLOSE}{shlex.quote(sys.executable)} "
                                   f"{shlex.quote(CUT)} {READ_BYTES} {'tail' if k == 'check' else 'head'} "
                                   f"{shlex.quote(keep)}" + (f" {kept}" if kept and k != "check" and not answers(body)
                                                             else "")))
    # a check that failed is fixed in what it checks, not in its command: it is not told to fix the command


# commands whose status 1 is an answer, not a failure: nothing found, a difference, a test that did not hold
ANSWERS = {"grep", "egrep", "fgrep", "rg", "diff", "cmp", "test", "["}


def answers(command):
    """Whether a command's status is its last command's answer rather than its failure."""
    words = segments(shell_syntax(command))
    return bool(words) and os.path.basename(words[-1][0]) in ANSWERS


def unwrapped(command):
    """The command a session made, from the one bounded() made of it — cut, run to list its errors, or both; any
    other command as it is."""
    m = WRAPPED.match(command) or re.match(r"^(\s*cd\s+[^;&|]+?\s*&&\s*)?(.*)$", command, re.S)
    prefix, body = m.group(1) or "", m.group(2)
    runner = RUNNER.match(body)
    if runner:
        with contextlib.suppress(ValueError):
            body = shlex.split(runner.group(1))[0]
    return prefix + body if runner or WRAPPED.match(command) else command


def write_targets(tool, inp, command, cwd):
    """The files a command writes: a change's files, the targets of its redirections and file commands, and the paths
    a script inside it names where it writes them. A path a command merely mentions is not one: a heredoc's
    prose naming `ROOT` had drafts under a task's own directory refused as writes to the tree (2026-09-20). What
    keeps prose out is shell_syntax, which drops heredoc bodies, quoted words and Isabelle's symbols before any of
    this reads them — not a test of the word itself, which would have to drop `ROOT` and every file not yet made."""
    command = command or ""
    call = change_call(command) if CHANGE_VERB.search(command) else None
    if call:  # the files it changes, exactly: read from the blocks the command itself will apply
        where = os.path.join(cwd or v2.PROJECT, os.path.expanduser(call[0]))
        return list(dict.fromkeys(v2.change_path(where, op["path"]) for op in v2.change_blocks(call[2])[0]))
    names = redirections(command)
    for words in segments(shell_syntax(command)):
        if not words:
            continue
        cmd, operands = os.path.basename(words[0]), [w for w in words[1:] if not w.startswith("-")]
        if cmd in FILE_WRITERS:
            names += operands
        elif cmd == "sed" and any(w.startswith("-i") for w in words[1:]):  # its script is not one of its files
            names += [w for w in operands if os.path.lexists(os.path.join(cwd or v2.PROJECT, w))]
    names += [m for match in SCRIPT_TARGET.findall(command) for m in match if m]
    return list(dict.fromkeys(os.path.normpath(os.path.join(cwd or v2.PROJECT, os.path.expanduser(w.strip("'\"`"))))
                              for w in names if w.strip("'\"`") not in ("", "/dev/null")))


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
                        f"your change to a draft under .build/tasks/{rec.get('task')}/ and install it after.")
    holder = v2.tree_holder(st, rec)
    tree = [t for t in targets if t.startswith(v2.PROJECT + os.sep) and not v2.exempt(os.path.relpath(t, v2.PROJECT))]
    if holder and tree:
        v2.mark_tree_wait(rec["name"], holder)
        stage = st["tasks"][holder]["stage"]
        what = ("parked for its run, which reads its changes" if stage == "parked" else
                f"its finalization, {stage}: its check, review and commit see its changes alone")
        return deny(f"Task {holder} holds the working tree ({what}). Until it lets it go, write new files as drafts under "
                    f".build/tasks/{rec.get('task')}/ and keep your edits of existing files for after; you are told when "
                    "the tree is yours. With nothing productive left meanwhile, park for it "
                    "(`.claude/orchestration/v2.py park tree`): another worker produces.")
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
    if tool == "Bash" and inp.get("command"):  # the call as the session made it, whichever of the two is given here
        inp = dict(inp, command=unwrapped(inp["command"]))
    response = hook.get("tool_response")
    with meter(session) as st:
        return _record(hook, rec, st, session, tool, inp, response)


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
    k = kind(tool, inp)
    r = requested(tool, inp, hook.get("cwd"))
    total = lines_of(r[0]) if r and ran else None
    if total is not None:  # a read of a file's lines, bounded before it ran: it showed what it named
        path, first, last, _ = r
        saw(st, path, first, total if last is None else min(last, total))
    note = None
    if k in READING:
        shown = shown_bytes(tool, response)
        if tool == "Bash" and not inp.get("run_in_background") and shown > READ_BYTES + 1_000:
            # a call the guard sends through cut.py showed more than a read may: the rewrite did not take
            v2.say_once("cut-not-applied", f"ATTENTION a call of {rec.get('name')} showed {shown:,} bytes, more than "
                        f"the {READ_BYTES:,} a read shows: the guard's rewrite of it through cut.py did not apply")
        batch = batch_id(transcript, hook.get("tool_use_id"))
        if batch:  # what the batch has read, which bounds what more it may (the guard)
            st["batches"] = dict(st.get("batches") or {}, **{batch: (st.get("batches") or {}).get(batch, 0) + shown})
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
    tail = (f" A read is one batch — one request — however many reads it holds, up to "
            f"{BATCH // 1000}K bytes: put what you need together. A production restarts the first tier and gives "
            "one back to the reserve.")
    if left == 0 and spare == 0:
        return (head + " That was your last read: the next produces (writes the next part of a deliverable), asks "
                "(`v2.py ask`) or records a partial result." + tail)
    if left == 0:
        return head + f" The next {spare} read{'s' if spare > 1 else ''} come{'' if spare > 1 else 's'} from the reserve." + tail
    return head + f" {left} more read{'s' if left > 1 else ''} before the reserve." + tail


def guard(hook):
    role, rec = v2.role_of(hook.get("session_id", ""))
    if role is None:
        return None
    tool, inp = hook.get("tool_name"), hook.get("tool_input") or {}
    if tool in REMOVED_TOOLS:
        return deny(f"{tool} is not a session's tool (the owner, 2026-09-21). {REMOVED_TOOLS[tool]}")
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
    if denied and kept and fixable:
        said["permissionDecisionReason"] += " " + fix_note(kept)
    if fixed and not denied and "updatedInput" not in said:
        refused = allow(inp)
    if denied and kind(tool, inp) in READING and hook.get("tool_use_id"):
        # a read refused is a read not made: it takes nothing from either tier
        with meter(hook.get("session_id", "")) as st:
            st["refused"] = (st.get("refused") or []) + [hook["tool_use_id"]]
    return refused


def main():
    if sys.argv[1:2] != ["guard"]:
        print(__doc__)
        return 2
    try:
        decision = guard(json.load(sys.stdin))
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
