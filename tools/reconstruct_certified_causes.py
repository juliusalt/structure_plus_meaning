"""Reconstruct complete native recorded-cause comparisons from source."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='certified-causes',
    roots=('Certified_Cause_Execution',),
    export='Certified_Cause_Execution:certified_cause.ML',
    session='Reconstruct_certified_causes',
    groups=((Execution('comparison', 'check_certified_causes.py', ('--project', '{project}'), 3900),
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Certified_Cause_Execution', '--module', 'Certified_Cause_Execution', '--report', 'certified_cause_report_value', '--scope', 'certified_cause_indices', '--selections', 'certified_cause_report_selections', '--workers', '4', '--timeout', '1200'), 1300),),),
    boundary='Complete native generation subjects, arbitrary recorded judgment scopes, literal applications and retained closed replays determine each original certified-base-cause condition. Every method result, derived observation and revision reason is reproduced. The test policy and history remain explicitly empty; full workflow policy, historical permission, coverage, cost and genesis remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
