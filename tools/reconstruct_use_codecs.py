"""Reconstruct complete original-use codec and path-budget comparisons."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='use-codecs',
    roots=('Use_Codec_Execution',),
    export='Use_Codec_Execution:use_codec.ML',
    session='Reconstruct_use_codec',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Use_Codec_Execution', '--module', 'Use_Codec_Execution', '--report', 'use_codec_report_value', '--scope', 'use_codec_indices', '--selections', 'use_codec_report_selections', '--workers', '4', '--timeout', '600'), 660),
    ),),
    boundary='Actual complete uses, arbitrary path inputs and original coordinate bounds produce both complete codec graphs, every original-condition observation, semantic and path-cost comparison, and revision reason. All-input codec laws and digit-length bounds are proved separately. Finite scope, store integration, arithmetic, full physical decision cost, workflow and genesis remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
