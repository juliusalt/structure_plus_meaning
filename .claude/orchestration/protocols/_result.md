**The result**, in .build/tasks/{ID}/result.md — HANDOFF.md is the planner's state and PLANNING_LOG.md its log, and
what you did reaches the planner through your result:

    Status: done | partial | blocked
    ## Produced          the artifacts and statements, with where they are
    ## Decisions         what you decided, with reasons
    ## Plan as followed  the steps as done, and the changes to the brief's plan with their reasons
    ## Remains           what is left, as artifacts a next task can take up
    ## Questions         what the planner should decide
    ## Follow-ups        tasks the work shows are needed (the planner decides on them)

Write it and record it in one call — the change that writes result.md, then `.claude/orchestration/v2.py result {ID}`
on the line after it (it runs only if the change went through). Your turn ends only with your result recorded or once
you have parked
(`v2.py park`): you never wait holding the producing slot. Recording your result is refused while a job of yours runs,
since you are stopped then, which would kill it (let it finish, or stop it with TaskStop); parking for that run is
not. Near the end of your window you are told to record a partial result: do so at once.
