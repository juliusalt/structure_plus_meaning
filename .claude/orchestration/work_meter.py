#!/usr/bin/env python3
"""The guards of every role, and what a session reads and produces.

  work_meter.py guard   PreToolUse hook: refuse what a role may not do
  ctx_gauge.py gauge calls record() after every tool call of a working session.

The planner, the task designer, the knowledge base and consultations of it read statements, not details: theory
sources only through `show.py --statement(s)` or a gather (`v2.py step`), never proof text, code bodies, logs or diffs;
listing names (ls, find, Glob, `git log` without patches) is free. The task graph is edited only by the planner and
the task designer.

Every working session produces. Production is a change to its role's deliverables (v2.deliverables_of: a producing
session's files under its brief's Deliverable and its drafts under .build/tasks/ID/; the task designer's briefs and
TaskCreate or TaskUpdate; the reviewer's verdict; the planning episode's HANDOFF.md, notes and graph edits; a
consultation's reply) that adds or changes content: in a theory a command (definition, statement, locale, proof)
added or changed, its comments and layout aside, or COMMENTARY_WORDS words of commentary; in a document PROSE_WORDS
words added or rewritten; in code CODE_LINES non-blank, non-comment lines. Between two production events a session
may take at most ROUNDS requests and read at most READ_TOKENS tokens (a producing session's planned inputs do not
count on their first read, nor does a gather); past either, reads, searches and checks are refused, and what remains
is to produce, to ask, or to record what it has. After every read, search or check the session is told how many
requests and tokens it has left. Replayed on impl-8 to impl-30 (421 stretches between writes, 2,334 requests that
read, searched or checked), 3 rounds would have bound in 42% of the stretches and held back 68% of those requests, 6
rounds in 30% and 47%: under v1 an implementer read one slice per request, and 3 rounds (the owner's choice) force the
reads a step needs into one or two requests.

A check that fails with the same failure (theory, line, error) after a fix, CIRCLING times in a row, stops further
checks until an answer on the obstruction has come. Failures that move are progress. Waiting is refused (sleep, wait
loops, `tail -f`, TaskOutput, reading a background job's output before its completion notice), and so are subagents.
A read of lines that are in the session's context and unchanged since is refused (nothing is ever cleared from its
context); a Read only when the same lines were read with Read before, since Edit and Write accept a file only after a
Read of it. A quick fix has its own budget: FIX_MINUTES minutes and FIX_ROUNDS rounds from its start.
"""
import collections
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
ROUNDS, READ_TOKENS, CIRCLING = v2.ROUNDS, v2.READ_TOKENS, v2.CIRCLING
PROSE_WORDS, COMMENTARY_WORDS, CODE_LINES = 40, 40, 5
FIX_MINUTES, FIX_ROUNDS = v2.FIX_MINUTES, v2.FIX_ROUNDS
SHOWN = 30_000  # characters of command output shown whole (Claude Code's bashOutputMaxChars)
READ_LINES = 2_000  # what a Read without a limit shows at most
CHARS_PER_TOKEN = 2.5
CODE = (".py", ".sh", ".ML", ".sml", ".js")
COMMENTARY = {"text", "text_raw", "chapter", "section", "subsection", "subsubsection", "paragraph", "subparagraph"}
SED = re.compile(r"""^sed\s+-n\s+(['"]?)(\d+),(\d+)p\1\s+(\S+)$""")
CAT = re.compile(r"^cat\s+(\S+)$")
HEAD = re.compile(r"^head\s+(?:-n\s*|-)(\d+)\s+(\S+)$")
TAIL = re.compile(r"^tail\s+(?:-n\s*|-)(\d+)\s+(\S+)$")
# What the shell itself does, read on the command with its heredoc bodies and quoted words removed: a grep pattern
# holding `>>`, or a theory's \<open>, is data and not a redirection (2026-09-20).
WRITE_SHELL = re.compile(r"\bsed\s+-i\b|(?<![0-9&])>>?\s*(?!/dev/null\b|&)[^\s|;&>]+|\btee\s+(?:-a\s+)?[^\s|;&]+"
                         r"|(?:^|[;&|]\s*)(?:cp|mv|install|rm|touch|ln|mkdir|rmdir|truncate|chmod)\s")
# What a script inside the command writes, named where it writes it
WRITE_SCRIPT = re.compile(r"""\.write_text\(|\.writelines\(|shutil\.(?:copy|move)|open\(\s*[^)]*['"][wa]""")
HEREDOC = re.compile(r"<<-?\s*(['\"]?)(\w+)\1\r?\n.*?^\s*\2\s*$", re.S | re.M)
QUOTED = re.compile(r"'[^']*'|\"[^\"]*\"")
REDIRECT = re.compile(r"""(?<![0-9&])>>?\s*(?:'([^']+)'|"([^"]+)"|([^\s|;&>]+))""")
# a path a script inside the command writes to, named literally
SCRIPT_TARGET = re.compile(r"""(?:Path\(\s*|open\(\s*)['"]([^'"]+)['"]\s*\)?\s*(?:\.\s*write_text|\.\s*open\(\s*['"][wa])"""
                           r"""|open\(\s*['"]([^'"]+)['"]\s*,\s*['"][wa]""")


def shell_syntax(command):
    """The command as the shell reads it: a heredoc body is data, and so is a quoted word — unless a redirection is
    what precedes it, so that `grep '>>'` names nothing while `> "a file"` still names its file (2026-09-20)."""
    text, kept, i = HEREDOC.sub(" <<heredoc ", command or ""), [], 0
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
GIT_MUTATE = re.compile(r"\bgit\s+(?:-[Cc]\s+\S+\s+)*(?:add|commit|stash|checkout|reset|restore|rm|mv|merge|rebase|push|pull"
                        r"|clean|switch|cherry-pick|revert|apply|am|update-index|update-ref|worktree|gc|prune|filter-branch"
                        r"|replace|notes|tag|branch\s+-[dDmMfc])\b")
READS = re.compile(r"^\s*(?:cd\s+[^;&|]+&&\s*)?(?:sed\s+-n|cat|head|tail|grep|rg|find|ls|wc|awk|nl|less|more"
                   r"|git\s+(?:show|log|diff|status|grep|blame)|(?:python3?\s+)?\S*show\.py)\b")
CHECK = re.compile(r"probe_theories\.py|incremental_check\.py|isabelle\s+(?:build|ML_process|process)|tools/build\.py")
WAIT = re.compile(r"\bsleep\s+(?:[2-9]|\d{2,}|\d+[smh])|\btail\s+-[a-zA-Z]*f\b|\bwatch\s|\b(?:until|while)\b[^;]*;\s*do\b[^;]*\bsleep\b")
OWN = re.compile(r"\.claude/orchestration/v2\.py\b")
# What the planner does not read: theory and code bodies, logs, and under .build anything but the tasks' documents.
BODY = re.compile(r"\.(?:thy|ML|sml|py|sh|log|out|output)$|(?:^|/)(?:theories|tools)(?:/|$)|(?:^|/)\.build(?:/|$)(?!tasks/[^/]+/[^/]+\.md$)")
CONTENT = {"cat", "sed", "head", "tail", "grep", "egrep", "fgrep", "rg", "awk", "nl", "less", "more", "bat", "diff",
           "strings", "xxd", "od", "cut", "sort", "uniq", "jq", "tac"}
PATTERNED = {"grep", "egrep", "fgrep", "rg", "sed", "awk"}  # their first operand is a pattern or a script
STAT = re.compile(r"--(?:stat|shortstat|numstat|name-only|name-status|summary)\b")
PATCH = re.compile(r"(?:^|\s)(?:-p|-u|--patch|-L\S*|--word-diff\S*|--full-diff)(?:\s|$)")
DOCUMENTS = re.compile(r"\.(?:md|txt|json|toml|ya?ml)\b")


def deny(text):
    return {"hookSpecificOutput": {"hookEventName": "PreToolUse", "permissionDecision": "deny",
                                   "permissionDecisionReason": text}}


# ---------------------------------------------------------------- the planner

def body(path, cwd=None):
    """Whether a path the planner names is a body: a theory, code, a log, a draft, or a directory that holds them."""
    p = path.strip("'\"")
    if not p or p.startswith("-"):
        return False
    full = os.path.normpath(p if os.path.isabs(p) else os.path.join(cwd or v2.PROJECT, p))
    tree = cwd if cwd and os.path.exists(os.path.join(cwd, "ROOT")) else v2.PROJECT
    rel = os.path.relpath(full, tree)
    return bool(BODY.search(rel)) or rel == "." or full in (tree, v2.PROJECT)


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


def reads_body(words, cwd):
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
    return any(body(f, cwd) for f in files)


def planner_guard(tool, inp, cwd=None):
    if tool in ("Agent", "TaskOutput"):
        return deny("A session starts no subagents and waits on nothing: it acts and ends its turn.")
    detail = ("Your role reads statements, not details: theories through `.claude/orchestration/show.py --statement "
              "NAME` or `--statements THEORY` (or a gather, `v2.py step`), results and documents under .build/tasks/*/, "
              "the plan, the ledger, `git log`; never proof text, code bodies, logs or diffs. Listing names (ls, find, "
              "Glob) is free.")
    if tool == "Read" and body(inp.get("file_path", ""), cwd):
        return deny(detail)
    if tool == "Grep":
        path, glob, typ = inp.get("path") or "", inp.get("glob") or "", inp.get("type") or ""
        full = os.path.join(cwd or v2.PROJECT, path) if path else ""
        narrowed = (path and os.path.isfile(full) and not body(path, cwd)) or (
            (glob or typ) and DOCUMENTS.search(glob or "." + typ) and not BODY.search(glob))
        if not narrowed or (path and body(path, cwd)):
            return deny(detail + " A search names the documents it searches (a file, or a glob such as *.md).")
    if tool == "Bash":
        c = inp.get("command") or ""
        if re.search(r"show\.py\b", c) and not re.search(r"--statements?\b", c):
            return deny(detail)
        if any(reads_body(words, cwd) for words in segments(c)):
            return deny(detail)
    return None


# ---------------------------------------------------------------- a session's state

def path_of(session):
    return os.path.join(STATE, f"work-{session}.json")


def load(session):
    try:
        return json.load(open(path_of(session)))
    except (OSError, ValueError):
        return {"reads": {}, "read_tokens": 0, "production_at": None, "inputs_read": [], "fixed_since": False,
                "last_check": None, "prev_sig": None, "repeats": 0}


def save(session, st):
    os.makedirs(STATE, exist_ok=True)
    tmp = path_of(session) + ".tmp"
    json.dump(st, open(tmp, "w"))
    os.replace(tmp, path_of(session))


def brief_of(rec):
    """What counts as a session's production (v2.deliverables_of), and the planned inputs of a producing session."""
    out = v2.deliverables_of(rec)
    out["inputs"] = []
    if rec.get("role") in v2.PRODUCING:
        try:
            out["inputs"] = json.load(open(os.path.join(v2.BUILD, rec["task"], "brief.json"))).get("inputs", [])
        except (OSError, ValueError, KeyError):
            pass
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


def covered(ranges, first, last):
    line = first
    for a, b in sorted(ranges):
        if a > line:
            break
        line = max(line, b + 1)
        if line > last:
            return True
    return line > last


def kind(tool, inp):
    """write, read, check, own (the harness's commands), or other."""
    if tool in ("Edit", "Write", "MultiEdit", "NotebookEdit"):
        return "write"
    if tool in ("Read", "Grep", "Glob"):
        return "read"
    if tool in ("TaskCreate", "TaskUpdate"):
        return "task"
    if tool == "ToolSearch":
        return "own"
    if tool == "Bash":
        c = inp.get("command") or ""
        if OWN.search(c):
            return "own"
        if CHECK.search(c):
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
    except OSError:
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


# ---------------------------------------------------------------- production

def deliverable_files(brief):
    out = []
    for p in brief.get("deliverables", []):
        full = os.path.join(v2.PROJECT, p)
        if os.path.isdir(full):
            out += [os.path.join(r, f) for r, _, fs in os.walk(full) for f in fs]
        else:
            out.append(full)
    drafts = os.path.join(v2.PROJECT, brief.get("drafts", ""))
    if brief.get("drafts") and os.path.isdir(drafts):
        out += [os.path.join(r, f) for r, _, fs in os.walk(drafts) for f in fs
                if f not in ("brief.json", "result.md", "finalize.json", "finalize.log", "finalized.json")]
    return sorted(set(out))


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
    if tool == "Agent":
        return deny("A session starts no subagents: it does its piece of work itself; a question goes to its author, "
                    "the knowledge base or the planner (`v2.py ask`).")
    if tool == "TaskOutput":
        return deny("Waiting is refused: a background job's completion notifies you; continue with the task meanwhile.")
    if tool in ("TaskCreate", "TaskUpdate") and rec.get("settings") == "planner-settings.json" \
            and not v2.ROLES.get(rec.get("role"), {}).get("graph"):
        return deny("The task graph is the planner's and the task designer's: propose a task to the planner instead "
                    "(`v2.py ask --to planner`), or name it in your result.")
    c = (inp.get("command") or "") if tool == "Bash" else ""
    if c and WAIT.search(c):
        return deny("Waiting is refused (sleep, wait loops, tail -f): a background job's completion notifies you. "
                    "Continue with what follows or with an independent part of the task.")
    out = re.search(r"/tasks/(\w+)\.output\b", c or inp.get("file_path", ""))
    if out and not completed(hook.get("transcript_path", ""), out.group(1)):
        return deny("That job is still running; its completion notifies you. Continue with the task meanwhile.")
    if c and GIT_MUTATE.search(c):
        return deny("The working tree changes only by writing files, and the index and history only by the finalizer: "
                    "no session stages, commits, stashes, checks out, resets, merges or pushes. Read with git status, "
                    "diff, log and show.")
    k = kind(tool, inp)
    if k == "write":
        refused = write_guard(tool, inp, c, rec, hook.get("cwd"))
        if refused:
            return refused
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
        if spent and not (k == "write" and inp.get("file_path", "").endswith(result)):
            return deny(f"The quick fix's budget ({FIX_MINUTES} minutes, {FIX_ROUNDS} rounds) is spent: record your result "
                        f"(`v2.py result {rec['task']}`), partial if the fix is not done, so that it becomes a task.")
    r = requested(tool, inp, hook.get("cwd"))
    if r:
        path, first, last, form = r
        seen = st["reads"].get(path)
        total = lines_of(path)
        if seen and total is not None and seen["stamp"] == stamp(path) and (form != "read" or seen.get("tool_read")):
            end = total if last is None else min(last, total)
            if end >= first and covered(seen["ranges"], first, end):
                return deny(f"Lines {first}-{end} of {os.path.relpath(path, v2.PROJECT)} are already in your context: "
                            f"you read them at {seen['at']} and the file has not changed since. Use what you have.")
    if k == "check":
        settle_check(st)
        answered = [q for q in v2.peek()["asks"].values() if q["from"] == rec.get("name") and q.get("answered")]
        last_answer = max((q["answered"] for q in answered), default=0)
        if st["repeats"] >= CIRCLING and last_answer > (st.get("circled_at") or time.time()):
            st["repeats"], st["circled_at"] = 0, None  # an answer on the obstruction has come: check again
        elif st["repeats"] >= CIRCLING:
            st["circled_at"] = st.get("circled_at") or time.time()
        save(session, st)
        if st["repeats"] >= CIRCLING:
            return deny(f"The same failure came back {st['repeats']} times after fixes ({' '.join(st['prev_sig'] or [])}): "
                        "the fixes are not working. Bring the obstruction to its author or the planner (`v2.py ask`), "
                        "with what you tried, and continue meanwhile with what does not depend on it.")
    if k == "write" and rec.get("task"):  # the working tree's changes are attributed to the task that writes them
        v2.own(rec["task"], [os.path.relpath(t, v2.PROJECT) for t in write_targets(tool, inp, c, hook.get("cwd"))
                             if t.startswith(v2.PROJECT + os.sep)])
    if k in ("read", "check", "other") and not fix:
        rounds = rounds_since(hook.get("transcript_path", ""), st.get("production_at"), hook.get("tool_use_id"))
        if rounds > ROUNDS or st["read_tokens"] > READ_TOKENS:
            return deny(f"{rounds - 1} requests and about {st['read_tokens'] // 1000}K tokens of reading since your last "
                        f"production (the limits are {ROUNDS} requests and {READ_TOKENS // 1000}K): write the next part "
                        "of your deliverable from what you hold, ask (`v2.py ask`), or record what you have. Reads, "
                        "searches and checks wait until you have produced.")
    return None


EXTENSIONS = {"md", "thy", "py", "json", "jsonl", "sh", "txt", "out", "log", "diff", "patch", "yaml", "yml", "toml",
              "cfg", "csv", "tsv", "pyc", "lock", "ML", "tex", "html", "svg", "png"}


def path_like(word, cwd):
    """The file a word of a command names, or None. A command carries heredocs, quoted text and prose, and every word
    that ends a sentence has a dot in it, so a word counts only when it names something that is there, or a new file
    of a known kind in a directory that is (2026-09-20: the owner record held 319 entries, five of them paths)."""
    for w in re.findall(r"[A-Za-z0-9_./~-]+", word):
        if not w or w.startswith("-") or w.endswith(".") or ".." in w or w == "/dev/null":
            continue
        full = os.path.normpath(os.path.join(cwd or v2.PROJECT, os.path.expanduser(w)))
        base = os.path.basename(w)
        ext = base.rsplit(".", 1)[-1] if "." in base[1:] else ""
        if os.path.lexists(full) or (ext in EXTENSIONS and os.path.isdir(os.path.dirname(full))):
            yield full


def write_targets(tool, inp, command, cwd):
    """The files a command writes: an Edit's or Write's file, the targets of its redirections and file commands, and
    the paths a script inside it names where it writes them. A path a command merely mentions is not one: a heredoc's
    prose naming `ROOT` had drafts under a task's own directory refused as writes to the tree (2026-09-20)."""
    if tool in ("Edit", "Write", "MultiEdit", "NotebookEdit"):
        p = inp.get("file_path") or inp.get("notebook_path") or ""
        return [os.path.normpath(p if os.path.isabs(p) else os.path.join(cwd or v2.PROJECT, p))] if p else []
    command = command or ""
    names = redirections(command)
    for words in segments(shell_syntax(command)):
        if not words:
            continue
        cmd, operands = os.path.basename(words[0]), [w for w in words[1:] if not w.startswith("-")]
        if cmd in ("rm", "rmdir", "touch", "truncate", "mkdir", "ln", "chmod", "mv", "cp", "install", "tee"):
            names += operands
        elif cmd == "sed" and any(w.startswith("-i") for w in words[1:]):  # its script is not one of its files
            names += [w for w in operands if os.path.lexists(os.path.join(cwd or v2.PROJECT, w))]
    names += [m for match in SCRIPT_TARGET.findall(command) for m in match if m]
    return list(dict.fromkeys(os.path.normpath(os.path.join(cwd or v2.PROJECT, os.path.expanduser(w.strip("'\"`"))))
                              for w in names if w.strip("'\"`") not in ("", "/dev/null")))


def write_guard(tool, inp, command, rec, cwd):
    """HANDOFF.md is the planner's; while another task's finalization is in flight, it holds the working tree: every
    other session writes only under .build/ (and the harness's own files), and is told when the tree is free."""
    targets = write_targets(tool, inp, command, cwd)
    handoffs = {os.path.join(v2.PROJECT, "HANDOFF.md"), os.path.join(v2.tree_of(rec), "HANDOFF.md")}
    if rec.get("role") != "planner" and handoffs & set(targets):
        return deny("HANDOFF.md is the planner's state: what you did goes into your result, which reaches the planner.")
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
    response = hook.get("tool_response")
    st, brief = load(session), brief_of(rec)
    now = v2.iso()
    if st.get("production_at") is None:
        check_production(session, brief, st)  # the baseline
        st["production_at"] = now
    k = kind(tool, inp)
    r = requested(tool, inp, hook.get("cwd"))
    if r:
        path, first, last, form = r
        shown = None
        if form == "read":
            f = response.get("file") if isinstance(response, dict) else None
            if f and not f.get("truncatedByTokenCap") and f.get("numLines"):
                shown = (int(f.get("startLine") or 1), int(f.get("startLine") or 1) + int(f["numLines"]) - 1)
        elif isinstance(response, dict) and response.get("stdout") and len(response["stdout"]) < SHOWN and not response.get("interrupted"):
            shown = (first, last)
        total = lines_of(path)
        if shown and total is not None:
            a, b = shown
            b = total if b is None else min(b, total)
            seen = st["reads"].get(path)
            if not seen or seen["stamp"] != stamp(path):
                seen = st["reads"][path] = {"stamp": stamp(path), "ranges": [], "at": ""}
            seen["ranges"].append([a, b])
            seen["at"] = time.strftime("%H:%M")
            seen["tool_read"] = seen.get("tool_read", False) or form == "read"
    note = None
    if k == "read":
        target = inp.get("file_path") or inp.get("command") or ""
        planned = [p for p in brief.get("inputs", []) if p in target and p not in st["inputs_read"]]
        if planned:
            st["inputs_read"] += planned
        else:
            size = len(json.dumps(response or ""))
            st["read_tokens"] += int((size if tool == "Read" else min(size, SHOWN)) / CHARS_PER_TOKEN)
    if k == "check":
        text = json.dumps(response or "")
        path = re.search(r"Output is being written to: (\S+?\.output)", text)
        st["last_check"] = {"path": path.group(1) if path else None, "text": None if path else text[-200_000:],
                            "fixed_before": st.get("fixed_since", False)}
        st["fixed_since"] = False
    if (k in ("write", "other", "check") and check_production(session, brief, st)) or (k == "task" and brief["task_tools"]):
        st["production_at"], st["read_tokens"], st["fixed_since"] = now, 0, True
        st["productions"] = st.get("productions", 0) + 1
        if not rec.get("fix"):
            note = f"Production recorded: the count restarts ({ROUNDS} requests, {READ_TOKENS // 1000}K tokens of reading)."
    elif k in ("read", "check", "other") and not rec.get("fix"):
        note = countdown(rounds_since(hook.get("transcript_path", ""), st["production_at"], hook.get("tool_use_id")),
                         st["read_tokens"])
    save(session, st)
    return note


def countdown(rounds, read_tokens):
    """What a session has left before it must produce, told after every read, search or check."""
    left = max(0, ROUNDS - rounds)
    head = (f"Since your last production: {rounds} of {ROUNDS} requests, {read_tokens // 1000}K of "
            f"{READ_TOKENS // 1000}K tokens read.")
    if left == 0 or read_tokens >= READ_TOKENS:
        return (head + " That was the last request that may read, search or check: the next produces (writes the next "
                "part of a deliverable), asks (`v2.py ask`) or records a partial result.")
    return head + f" {left} more request{'s' if left > 1 else ''} may read, search or check; issue a step's reads together."


def guard(hook):
    role, rec = v2.role_of(hook.get("session_id", ""))
    if role is None:
        return None
    tool, inp = hook.get("tool_name"), hook.get("tool_input") or {}
    if v2.statements_only(rec):
        refused = planner_guard(tool, inp, hook.get("cwd"))
        if refused:
            return refused
    if role == "kb":
        return None
    return session_guard(hook, rec)


def main():
    if sys.argv[1:2] != ["guard"]:
        print(__doc__)
        return 2
    try:
        decision = guard(json.load(sys.stdin))
    except Exception:  # a guard that fails lets the call through rather than block the work
        return 0
    if decision:
        print(json.dumps(decision))
    return 0


if __name__ == "__main__":
    sys.exit(main())
