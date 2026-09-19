Every piece of work beyond a question is a task of the graph with a brief in this form, sized so that it fits one
window; a piece of work beyond one window is several tasks, with their dependencies:

    Kind: design | investigate | build | fix | brief | review
    Serves: what it serves, and why now
    Deliverable: what it produces: files in backticks (not directories) for design, investigate, build and fix; the
      tasks it briefs for brief; the verdict for review
    Reviews: the task it reviews (a review task only)
    Acceptance: the check that accepts it
    Inputs: the sources it rests on, by name (theories, facts, documents), and the decisions with where they are written
    Decided: what is decided and must be respected
    Plan:
    1. the steps in order: each one's purpose and output, the sources it rests on by name, what it depends on, where
       its check falls (one check after a group of steps)
    2. ...
    Yours: what the session decides itself
    Planner's: what it must bring to the planner
    While checks run: what can proceed
    Size: an estimate in tokens of work (for example `about 150K`), within the room its session's base leaves: about
      {ROOM_DESIGN}K for a design, investigation, brief or review task, about {ROOM_TASK}K for a build or fix task; a
      task beyond its room is refused and split

A step is a unit its session gathers for at once (`v2.py step`) and then writes. The plan is malleable: the session
follows it while it holds, changes it when the work shows a better course, and says what it changed and why.

A build or fix task is written for the implementation base, which holds neither native_control_plan.md nor
REASONING_REUSE.md: what of them the task rests on is stated under Decided, or named under Inputs as the section its
first gather reads. A task that needs more of them than that is a design task, not a build task.
