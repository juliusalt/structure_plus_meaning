"""Reconstruct the complete certificate coverage execution from repository sources."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='certificate-coverage',
    roots=('Native_Certificate_Coverage_Execution',),
    export='Native_Certificate_Coverage_Execution:certificate_coverage.ML',
    session='Reconstruct_certificate_coverage',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Certificate_Coverage_Execution', '--module', 'Native_Certificate_Coverage_Execution', '--report', 'certificate_coverage_report_value', '--scope', 'certificate_coverage_report_scope', '--selections', 'certificate_coverage_report_selections', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='The complete initial original certificate-family scope and its two actual outputs determine retention and every proof/call/sharing witness. All four conditions and three complete revision cycles are reproduced. This failed coverage result is retained as the original development problem.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
