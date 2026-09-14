"""Reconstruct the complete certificate development execution from repository sources."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='certificate-development',
    roots=('Native_Certificate_Development_Execution',),
    export='Native_Certificate_Development_Execution:certificate_development.ML',
    session='Reconstruct_certificate_development',
    groups=((Execution("comparison", 'check_native_certificate_development.py', ("--project", "{project}"), 2100),),),
    boundary='The initial shared development cycle retains every actual subject, candidate, condition, comparison, revision, original-scope criticism and admission. Missing original identity/sharing witnesses prevent admission despite comparison selection. The scoped gate does not establish the complete workflow.')


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
