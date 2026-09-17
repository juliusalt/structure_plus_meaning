"""Reconstruct exact original-policy cause admission and independent requirement decisions."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='required-causes',
    roots=('Required_Cause_Execution',),
    export='Required_Cause_Execution:required_cause.ML',
    session='Reconstruct_required_causes',
    groups=((Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Required_Cause_Execution', '--module', 'Required_Cause_Execution', '--report', 'required_cause_report_value', '--scope', 'required_cause_indices', '--selections', 'required_cause_report_selections', '--workers', '4', '--timeout', '1200'), 1300),),),
    boundary='The complete original source and requirement family determine the constructed policy and entry. Actual native records, scope and application readings, independent original requirement decisions, all method conditions and revision reasons are reconstructed. Exact policy identity is separate from payload permission and from admitting alternative proved policy realizations. Full workflow policy coverage, enforced transitions, history permission, physical cost and genesis remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
