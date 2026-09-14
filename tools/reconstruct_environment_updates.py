"""Reconstruct complete native environment updates and persistent store chains."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='environment-updates',
    roots=('Environment_Update_Execution',),
    export='Environment_Update_Execution:environment_update.ML',
    session='Reconstruct_environment_updates',
    groups=((Execution('comparison', 'check_environment_updates.py', ('--project', '{project}'), 1200),),),
    boundary='The complete original artifact and binding relations, requested update, original guarded '
             'constructor and all candidate output fields determine soundness and completeness. '
             'The closed store API preserves original environment formation by construction. '
             'Persistent chains initialize once and retain every final artifact, binding and actual '
             'fixed-key lookup count. Index preparation, full value equality, whole-view observation, '
             'generation allocation, workflow integration, full physical cost and genesis remain separate.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
