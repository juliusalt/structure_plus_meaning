# The owner's third word of 2026-09-23: the console's graph, machine and trains; a change that probes

The owner (verbatim): "I want a task dag view in which it is also shown what is being checked/waiting/finalizing/in a
train. Also a seperate view for probes/machine slots and trains/batches also I want the dashboard to update when you
update the source so I do not have to restart it every time and just a refresh is enough. Regarding this - changed
theory itself and put the result in the change's reply. That removes the change→probe splits (30 in the window) - what
if it wants to change more before running the probe which would then make the probe output irrelevant? We can allow it
to pass a special flag that would allow this maybe, if you think that is adequate and coherent"

Nothing committed (the owner's hold of 10:10).

## Tasks

1. [x] **The task graph.** A view of the open tasks (and those done in the last hours, on a toggle) as the DAG their
   dependencies make — laid out in layers by the longest chain of blockers, drawn in SVG, no outside library — each
   node saying where its task stands: queued and waiting on which blockers, ready, running (its session), parked (for
   what), waiting for or in a check batch, being reviewed, being fixed, committing, waiting for or in a landing train,
   landed, with the planner. Click: the task.
2. [x] **The machine.** The watchdog's snapshot of every Isabelle run (heavy and probes, each with its command, its
   session or finalizer, its memory), the limits (heavy slots, probe slots, the memory floor) against what is used,
   who holds the machine or waits to, the queued probes, the shared measurements, the last hour's occupancy.
3. [x] **Batches and trains.** The check queue (waiting, being checked, decided), the passed trees, the batch logs;
   the landing queue (waiting, landing, landed, failed) and the train logs; the kept builds (C10); the log's lines.
4. [x] **The console follows its source.** The page reloads itself when dashboard.html changes; the server re-executes
   itself — same port, same token — when its Python (dashboard.py, v2.py, role_evidence.py, watchdog.py, train.py)
   changes, after compiling it (a file that does not compile is not run; the old server goes on). A refresh is enough.
5. [x] **A change that writes a theory probes it — when it says so.** (Built first with the probe by default and
   `--no-probe`; the owner then: "No default flag - a deliberate choice again", and "this is only for theory changes
   right? we do not want probing on changes to normal files": a change that writes a theory of the session's tree says
   `--probe` or `--no-probe`, or is refused; a change of any other file says neither.) Originally: `v2.py change` in a producing session with a task, having written
   theories/*.thy, runs the probe of those theories as the change left them (a probe slot, the machine's admission,
   bounded at PROBE_SECONDS, in a directory of its own under the task's folder, recorded as its probes are) and says
   in its reply what the probe found: complete or not, the errors, the time, where its log is. `v2.py change
   --no-probe` when more changes are to come before the theory can load: no probe, said so. Why this and not a probe
   asked for by a flag: the probe after a theory change is the step every session takes, and 30 of the 09-22
   afternoon's requests did nothing else; a default the session opts out of costs a forgotten intermediate state a few
   seconds of a probe slot, where an opt-in costs every forgotten probe a request of the whole context (about 64K).
6. [x] **Coherence.** Protocols (_production.md, _checks.md: the probe comes with the change), README, tests, mutation
   cases, the suite, the handoff.
