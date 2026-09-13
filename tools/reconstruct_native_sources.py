"""Rebuild source observations, their revisions and actual source-checked package extensions."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name="native-sources",
    roots=("Native_Source_Execution",),
    export="Native_Source_Execution:native_sources.ML",
    session="Native_Source_Reconstruction",
    groups=((Execution("observations", "check_source_observations.py", ("--project", "{project}"), 900),
             Execution("extensions", "check_source_extensions.py", ("--project", "{project}"), 1800)),),
    boundary=("A run without --proof rebuilds the complete source and extension contracts from HOL. "
              "Native readers derive observations on the actual complete inputs; the existing investigation "
              "computes revisions and re-evaluates them. The source-checking constructor derives its complete "
              "source premise from each actual environment, then extends the package under the same universal "
              "meaning and preservation theorem. Every complete report is compared. Arbitrary alpha-model "
              "search, the whole development protocol, its cost account and genesis remain open."))


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
