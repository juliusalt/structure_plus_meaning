"""Rebuild and execute complete native package construction from repository sources."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name="native-extensions",
    roots=("Native_Extension_Execution",),
    export="Native_Extension_Execution:native_extensions.ML",
    session="Native_Extension_Reconstruction",
    groups=((Execution("extensions", "check_native_extensions.py", ("--project", "{project}"), 1200),),),
    boundary=("A run without --proof rebuilds the complete constructor and source proofs from HOL, "
              "exports the accepted code and executes all complete package reports. Every returned "
              "artifact, binding, interface, clause and coordinate is retained in the reproduced output. "
              "Complete source correspondence is proved for the concrete source models and remains "
              "a premise of the general constructor contract. General native admission of that "
              "correspondence, the whole development protocol and its cost account remain open."))


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
