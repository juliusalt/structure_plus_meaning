"""Reconstruct the complete certificate scope repair execution from repository sources."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='certificate-scope-repair',
    roots=('Native_Certificate_Scope_Repair_Execution',),
    export='Native_Certificate_Scope_Repair_Execution:certificate_scope_repair.ML',
    session='Reconstruct_certificate_scope_repair',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Certificate_Scope_Repair_Execution', '--module', 'Native_Certificate_Scope_Repair_Execution', '--report', 'certificate_scope_repair_report_value', '--scope', 'certificate_scope_repair_report_scope', '--selections', 'certificate_scope_repair_report_selections', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='The actual scope correction retains every full original input and appends compiled native sources and independently checked supplied certificates. Every complete input, source/proof check, original family, conflict witness, comparison and revision is reproduced. The correction is assessed against the original retention and coverage conditions.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
