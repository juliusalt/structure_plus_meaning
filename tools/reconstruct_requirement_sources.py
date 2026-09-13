"""Reconstruct complete source retention and the native installation observations."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name="requirement-sources",
    roots=("Requirement_Source_Execution",),
    export="Requirement_Source_Execution:requirement_sources.ML",
    session="Requirement_Source_Reconstruction",
    groups=((
        Execution("source-boundary", "check_requirement_source_boundary.py", ("--project", "{project}")),
        Execution("retained-clauses", "check_retained_clauses.py", ("--project", "{project}")),
        Execution("native-meanings", "check_native_guard_meanings.py", ("--project", "{project}")),
        Execution("native-plans", "check_native_requirement_plans.py", ("--project", "{project}")),
    ),),
    boundary=("A run without --proof rebuilds all dependency proofs from HOL, recovers the complete diagnostics, "
              "exports the accepted code and executes every source-retention and meaning observation. "
              "The inputs name complete internally defined programs and artifact environments. Native "
              "package recovery, exact source inclusion, whole-clause admission and all-term meaning "
              "contracts establish the observations. The report comparison establishes reproduction only. "
              "Checked recursive plans have a proved installation over the actual retained native source. "
              "The finite reports do not execute that existential constructor or establish a complete development protocol."))


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
