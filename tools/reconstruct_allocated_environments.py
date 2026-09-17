"""Reconstruct native allocation-state transitions and actual path observations."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='allocated-environments',
    roots=('Allocated_Environment_Execution',),
    export='Allocated_Environment_Execution:allocated_environment.ML',
    session='Reconstruct_allocated_environments',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Allocated_Environment_Execution', '--module', 'Allocated_Environment_Execution', '--report', 'allocated_environment_report_value', '--scope', 'allocated_update_indices', '--selections', 'allocated_environment_report_selections', '--workers', '4', '--timeout', '600'), 660),
    ),),
    boundary='A closed store carries original formation and a strict actual head bound. Checked loading derives the bound from complete source rows; local allocation and binding updates preserve it with exact whole original-constructor contracts. Complete optional states, actual candidate results, original-condition observations, comparisons, revisions and persistent chains are reconstructed. Both traversals of the actual next insertion are counted. Current unary path growth, generic encoded stores, graft and generation adoption, full physical cost, complete workflow enforcement and genesis remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
