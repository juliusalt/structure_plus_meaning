# The owner's second word of 2026-09-23: the tasks and the plan

The owner (verbatim): "C9 - the same reviewer gets reused and the gets what has changed since mechanically? If not
then fix this and then enable C9. The session's next foreground check runs beside probes and heavy runs, past their
limits and past the planner's order of checks. - this is not what I wanted the only difference should be that it gets
ran without holding all of the machine, but if it is heavy then it uses a heavy slot if it is like a probe it uses a
probe slot. Also there should be no default it should say shared not exclusive so that the choice is deliberate.
Regarding role layers I think you made a grave conceptual mistake - isn't the reasoning of the model itself part of the
context not just the content it produced? If so does it need to write anything at all? Writing something is for the
user to see, but in this case there is no user to read its output. Also now there should be 4 layers - the base, the
medium layer, the churn layer and the role layer did you think about the placement of it and is the placement coherent
and adequate between all of the 4 layers? Reason thoruhg all of this and make the apropriate changes. I also want a web
page that shows me all the information for a current run allows me to view individual sessions, their messages, what
they produced, how many turns they took, what failed, the bathcing, the individual commands and in general a full suite
in which I can both monitor and control the run."

Working rules: nothing committed (the owner's "No commit" of 10:10); each change built in the dev copy, tested,
mutation-checked, the suite run, deployed with a backup and an entry in notes/v2-build-handoff.md.

## What the code does now (read before planning)

- **C9's re-review.** After a rejection the reviewer that rejected is resumed while warm, told "judge those findings
  and whatever the fix broke", with the result, log, probes and restatements read again — but not what changed since
  its verdict: it finds that itself, from the whole diff. After an accept voided by a failed check (both C9 paths) the
  review's verdict is None, so `accepted_by` finds no one and the watchdog does not hold the reviewer: a fresh reviewer
  forks the middle base and reads everything again. So: reused only after a rejection, and never told the change
  mechanically.
- **The shared measurement** went past the machine's order and the heavy and probe limits. The owner wants only the
  whole-machine hold dropped: a heavy measurement takes a heavy slot, a probe-like one a probe slot, in the machine's
  order. And `v2.py measuring` defaulted to the exclusive hold.
- **The role layer's reasoning.** The transcripts show every assistant turn's thinking stored as a signature (its text
  empty) and carried into the next request: plan-47's request of 31,593 output tokens, nearly all thinking, grew the
  next request's context by 34,819; review-251's of 5,987 by 11,729. A fork resumes that conversation, so it carries
  the layer's reasoning itself. Its written practices duplicated that reasoning at five times the cost of input, for
  no reader.
- **The layers.** Each base (high, xhigh) is a stable part (days), a frontier layer (the medium one, refreshed when its
  delta has cost the forks a refresh: hours) and a delta (the churn: every change of 4K tokens, at most every 20
  minutes). The role layer forked the delta, so every churn rebuild — up to three an hour — invalidated every role
  layer of the base: rebuilt each time (its message written again, its reasoning thought again) or, until rebuilt, not
  forked at all.

## Tasks

Status: `[ ]` open, `[~]` in progress, `[x]` done.

1. [x] **C9: the same reviewer, told what changed, mechanically; then C9 on.** At every verdict the harness keeps the
   files the reviewer judged (`.build/tasks/RID/reviewed/`, their list and time in `reviewed.json`). A re-review — after
   a rejection, after an accept voided by a failed check, after an accept whose task came back — resumes the reviewer
   that judged it (held for it while the task is fixed and checked) with the diff from what it judged to what stands
   now (`v2.py read since`: the files then and now, each difference as a unified diff), beside the fix's result, log,
   probes and restatements. Then `state/review-beside-check`.
2. [x] **The measurement: shared or exclusive, said each time.** `v2.py measuring --shared|--exclusive "what"`; bare is
   refused, saying both. A shared measurement is admitted as any run of its kind (its slot, the machine's order, the
   memory floor) and differs only in holding nothing: its probe is bounded at the window, and it is told the machine's
   load over it. Protocols, messages and tests say which.
3. [x] **The role layer reasons and writes nothing.** Its message asks it to think the work through — the evidence and
   the content of the work ahead — and to reply with the done line alone; its forks are told that the reasoning before
   their message is their role's.
4. [x] **Four layers in the order of their change.** The order that makes each rebuild invalidate only what changes
   faster: the base (days) → the medium layer (hours) → the role layer (hours, by its own policy) → the churn
   (minutes). So the role layer forks the medium layer, never the delta, and survives every churn rebuild; each
   role's churn is a fork of its role layer holding the shared delta's text (the same text, one request), rebuilt when
   the shared delta changes and the role is wanted, with the shared delta's snapshot, so a fork is told only what
   changed after it. A role whose layer is not ready forks the shared delta as before. The medium layer's refresh
   builds the role layers again; the watchdog's refresh arithmetic counts what their forks carry and what their
   churns wrote.
5. [x] **A web console for the run.** `dashboard.py`: a local server (127.0.0.1, a token in its address, no outside
   library) and one page: the run (active, stopped, held; switches; the machine; slots; the queue and every task's
   stage; events; the bases and their layers), every session (role, state, task, origin, turns and requests, cost, when)
   and each one whole — its messages, each request with the calls it batched, every command and what came back (cut,
   expandable), what was refused and why, the harness's notes, what it produced; every task (brief, stage, result,
   review, finalize log, measurements, commits); checks, batches and trains; the log as it grows; and controls: the
   switches (the measurement window's seconds too), the graph held or released, the run stopped, a message to a task's
   session, a task queued or dropped, a session pinged or released.
6. [x] **Coherence.** README (the four layers, the measurement, C9's re-review, the console), the concepts plan's
   State, the first planner's event, the handoff, the whole suite, a full mutation run, memory.

## Why this placement (task 4)

A layer's rebuild takes everything above it with it. Ordered by how often each must change, a faster layer never sits
under a slower one: the stable base (rebuilt by the owner), the medium layer (by its carried cost, hours), the role
layer (by its role's evidence and work ahead, hours), the churn (by every landing, minutes). Above the churn, the role
layer was rebuilt with each churn — its reasoning, the most expensive thing in it (output at five times input), thrown
away up to three times an hour. Below the medium layer it could not see the frontier its work is in. Between them it
sees the frontier as the medium layer holds it and the churn above it brings what changed since, as it does for every
role. The price: a churn per role (the same text, a request each, only for roles that are wanted), against a role
layer's reasoning kept for hours.
