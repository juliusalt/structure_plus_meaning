"""Reconstruct the complete certificate development execution from repository sources."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='certificate-development',
    roots=('Native_Certificate_Development_Execution',),
    export='Native_Certificate_Development_Execution:certificate_development.ML',
    session='Reconstruct_certificate_development',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Certificate_Development_Execution', '--module', 'Native_Certificate_Development_Execution', '--report', 'native_certificate_development_report_value', '--scope', 'native_certificate_indices', '--selections', 'native_certificate_development_report_selections', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='The initial shared development cycle retains every actual subject, candidate, condition, comparison, revision, original-scope criticism and admission. Missing original identity/sharing witnesses prevent admission despite comparison selection. The scoped gate does not establish the complete workflow.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
