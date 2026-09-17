"""Reconstruct the complete native certificates execution from repository sources."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-certificates',
    roots=('Native_Certificate_Investigation_Execution',),
    export='Native_Certificate_Investigation_Execution:native_certificate_investigation.ML',
    session='Reconstruct_native_certificates',
    groups=((Execution("presentation", "check_presented_report.py", ("--project", "{project}",
                       "--module", "Native_Certificate_Investigation_Execution",
                       "--report", "native_certificate_report_value", "--scope", "native_certificate_indices",
                       "--selections", "native_certificate_report_selections", "--workers", "8"), 2400),),),
    boundary='Complete original native sources and certificates determine every path, actual path coordinate and full graph correspondence. All sixteen candidate outputs, seven conditions, complete comparisons and three revision cycles are reproduced. Native placement, the complete development workflow, cost and genesis remain separate.')


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
