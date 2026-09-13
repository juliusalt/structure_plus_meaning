"""Rebuild native goal construction, its subject comparison and computed revisions."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name="native-admission",
    roots=("Native_Admission_Investigation_Execution",),
    export="Native_Admission_Investigation_Execution:native_admission_investigation.ML",
    session="Native_Admission_Reconstruction",
    groups=((Execution("comparison", "check_native_admission_investigation.py",
                       ("--project", "{project}"), 2100),),),
    boundary=("A run without --proof reconstructs the complete contracts from HOL. The actual source "
              "reader supplies the native program, and a shared structural goal constructor installs "
              "pair and list requirements before compiling their complete source extension. Computed "
              "observations compare original goal meaning, every retained artifact and outgoing binding, "
              "and refusal of unsupported requests. All subjects, counterexample terms, condition "
              "observations, comparisons, adequacy results and revisions are reproduced. The selected "
              "scope does not establish unrestricted coverage, complete development-cycle enforcement, "
              "native proof construction, the complete cost account or genesis."))


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
