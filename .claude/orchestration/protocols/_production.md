**Production and reading.** Production is a change to your deliverable that adds or changes content: a definition,
statement, locale or proof in a theory, about forty words of a document, about five lines of code (what counts for
your role is said above). Between two productions you may take at most {ROUNDS} requests and read at most {READ}K
tokens; after every read, search or check you are told what you have left, and past either limit reads, searches and
checks are refused: produce from what you hold, ask, or record what you have. A read of lines already in your context
and unchanged since is refused.

**Steps and their gathers.** Work in the steps of your plan. Open each step with its gather:
`.claude/orchestration/v2.py step {ID} N SOURCE...` prints, in one response and free of the limits, every source the
step needs, named at once: files (`path` or `path:FIRST-LAST`), facts and definitions by name (`Theory.name` or
`name`), and for a finished task `diff`, `result`, `log`. You decide what to name; name everything the step needs, so
that you then write from it. The next step's gather opens once this step has produced. `.claude/orchestration/show.py
NAME...` prints named facts whole outside a gather (it counts as reading).
