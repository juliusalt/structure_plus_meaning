**Production and reading.** Production is a change to your deliverable that adds or changes content: a definition,
statement, locale or proof in a theory, about forty words of a document, about five lines of code (what counts for
your role is said above). Reading is limited in reads, and a read is a batch: one request, however many calls it
holds, up to {BATCH}K bytes read in it — past that the rest of the batch is refused and goes in your next. So put what
you need together. Each call shows at most {READ_BYTES}K bytes, so that a large chunk is read deliberately, in pieces:
a read of a file's lines that is longer is refused with the lines that fit named, and every other call's output — a
search, a script, a check — is cut there, its whole output kept in a file the cut names, to be read on by its lines.
The cut shows the output's beginning, or its end for a check or a command that failed, where it says how it ended or
what went wrong (a failure said before that end is quoted). Between two productions you may make {ROUNDS} reads; past that, each
read draws one from a reserve of {RESERVE}, and each production restarts the first tier and gives one back to the
reserve (never more than {RESERVE}). Writing, asking and a read that is refused count for nothing. After every read,
search or check you are told what you have left in both; when both are spent, reads, searches and checks are refused:
produce from what you hold, ask, or record what you have. A read of lines already in your context and unchanged since
is filtered: you are shown the rest, with a note of the lines left out; a read wholly in your context shows only that
note and counts as no read.

**Steps, and reading any source.** Work in the steps of your plan. Open each step with one batch — the first read after
a production, which is always allowed — naming everything the step needs, so that you then write from it. Besides
files and commands, `.claude/orchestration/v2.py read SOURCE...` reads any source, as a read like any other: files
(`path` or `path:FIRST-LAST`), facts and definitions by name (`Theory.name` or `name`), your task's `diff`, `result`
and `log` (each by its lines too: `diff:A-B`; a reviewer's are those of the task it reviews), a task's brief as the
graph holds it (`task:ID`, or `task:ID:A-B`), and a brief's proposal (`proposal:ID` for what placing it needs,
`proposal:ID:KEY` for one of its briefs, with `:A-B` for its lines; a fact too, `Theory.name:A-B`). One call shows at
most {READ_BYTES}K bytes and names the sources it had no room for: put several calls in the batch.

**Batch what you do, not only what you read.** The limits are there so that you take what you need at once, never to
ration it. Every `v2.py` command takes several things in one call: its arguments again in groups separated by a bare
`--` (`v2.py reply q1 "..." -- q2 --file F`), and `queue`, `read`, `drop`, `accept`, `proposal` and `tell ID... TEXT`
take several ids directly.

**Your tools, and changing files.** You have Bash, TaskCreate, TaskUpdate and TaskStop. You read through Bash and
`v2.py read`, and you change files with one command, which takes any number of changes to any number of files:

    .claude/orchestration/v2.py change <<'EOF'
    === write theories/New.thy
    the whole file, to the next === line
    === replace theories/Old.thy
    <<<<<<< SEARCH
    the text as it stands, exactly, whitespace included
    =======
    the text that replaces it
    >>>>>>> REPLACE
    EOF

A `replace` may hold several blocks; its SEARCH text must occur exactly once in the file as the changes before it
left it (`=== replace-all PATH` replaces every occurrence). The changes are judged whole and written all or none, and
what refuses them is said, change by change. Quote the delimiter (`<<'EOF'`), so the text reaches the command as it
is. Make the changes you have ready in one call: a call that makes one change is told so. Writing a file's content
any other way — a redirection into a file, `tee`, `sed -i`, a script that writes — is refused, but under .build/: a
program's output, generated data or a draft may be written there by any command. Moving, copying and removing files
stand.

**A command that went wrong is fixed, not written again.** Every command you make is kept, numbered. When one fails or
is refused, send only its correction:

    .claude/orchestration/v2.py again N <<'EOF'
    <<<<<<< SEARCH
    the part of command N that is wrong, exactly
    =======
    what it should be
    >>>>>>> REPLACE
    EOF

runs command N fixed (N left out: your last command; no block: it runs as it was), as if you had written it so, and
keeps that as your next. A refused `v2.py change` is fixed the same way: the failing change's block, not the whole
call again. A long command written again whole spends what its correction would not, and can bring new mistakes into
what was right.
