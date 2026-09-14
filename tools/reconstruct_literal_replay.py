"""Reconstruct complete native literal-replay reports from their original sources."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='literal-replay',
    roots=('Literal_Replay_Execution',),
    export='Literal_Replay_Execution:literal_replay.ML',
    session='Reconstruct_literal_replay',
    groups=((Execution("comparison", 'check_literal_replay.py', ("--project", "{project}"), 2100),),),
    boundary='Complete source, native application, proof root and requested payload determine the admission condition. The actual requirement decision and full keyed certificate/replay family, all reader outputs, coverage, method decisions and comparison reasons are reconstructed. The explicitly empty test policy does not establish whole-workflow policy adequacy; arbitrary cause reading, history permission, cost and genesis remain open.')


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
