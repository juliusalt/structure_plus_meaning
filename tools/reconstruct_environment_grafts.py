"""Reconstruct complete environment graft and mapping comparisons."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='environment-grafts',
    roots=('Graft_Execution',),
    export='Graft_Execution:graft.ML',
    session='Reconstruct_environment_grafts',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Graft_Execution', '--module', 'Graft_Execution', '--report', 'graft_report_value', '--scope', 'graft_indices', '--selections', 'graft_report_selections', '--workers', '4', '--timeout', '600'), 660),
    ),),
    boundary='Actual complete environment pairs and a shared use produce all candidate maps and whole grafted environments. The original merge and rename operations determine output meaning; general boundary embedding and compatibility contracts govern formation. Exact native observations retain every mapping, output row, formation observation, coordinate count, comparison and revision reason. Scope, indexed and generation adoption, full physical cost, workflow and genesis remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
