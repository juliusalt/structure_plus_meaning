"""Rebuild source-derived certificates and inspect every complete proof against its original program."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name="native-derivations",
    roots=("Native_Derivation_Investigation_Execution",),
    export="Native_Derivation_Investigation_Execution:native_derivation_investigation.ML",
    session="Native_Derivation_Reconstruction",
    groups=((Execution("presentation", "check_presented_report.py", ("--project", "{project}",
                       "--module", "Native_Derivation_Investigation_Execution",
                       "--report", "native_derivation_report_value", "--scope", "native_derivation_indices",
                       "--selections", "native_derivation_report_selections", "--workers", "8"), 2400),),),
    boundary=("A run without --proof reconstructs the complete contracts from HOL. The certificate "
              "constructor recovers the actual source and follows its complete finite inference history. "
              "Each original requested positive call has a complete valid certificate, and the independent "
              "recursive checker is exactly the original schema proof checker on every finite input. "
              "Every original source, candidate answer and certificate, complete inspection, comparison "
              "and revision is reproduced. A sufficient finite certificate family need not enumerate "
              "all proofs of a cyclic program. The finite scope does not establish arbitrary-method "
              "coverage, recursive explanation traces, native artifact positioning and placement, native "
              "mathematical-proof checking, complete development-cycle enforcement, the whole cost "
              "account or genesis."))


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
