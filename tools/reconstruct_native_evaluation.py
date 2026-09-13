"""Rebuild actual program judgments, their operation investigation and native executions."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name="native-evaluation",
    roots=("Program_Evaluation_Execution",),
    export="Program_Evaluation_Execution:program_evaluation.ML",
    session="Native_Evaluation_Reconstruction",
    groups=((Execution("comparison", "check_program_evaluation.py", ("--project", "{project}"), 1200),
             Execution("native", "check_native_evaluation.py", ("--project", "{project}"), 1800)),),
    boundary=("A run without --proof rebuilds the complete contracts from HOL. Actual program clauses "
              "supply complete requested applications; checked head scope and closed demand give the "
              "original positive meaning with no true seeds supplied. Computed method comparisons and "
              "revisions retain their actual subjects, including the corrected material operands. The "
              "selected operation reads and evaluates actual native packages under the existing positive-query "
              "contract. All complete reports are compared. Unrestricted program decision, native proof "
              "construction, complete development-cycle enforcement, its cost account and genesis remain open."))


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
