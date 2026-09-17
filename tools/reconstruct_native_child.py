"""Rebuild the native child example and every native control and construction over it."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-child',
    roots=('Inference_Claim_Input_Execution', 'Factor_Executable_Environment_Values'),
    export='Inference_Claim_Input_Execution:inference_claim_input.ML',
    session='Native_Child_Reconstruction',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Inference_Claim_Input_Execution', '--module', 'Native_Reasoning', '--report', 'native_child_report_value', '--scope', 'child_projection_cases', '--workers', '8', '--timeout', '1200'), 1300),
    ),),
    boundary=('A run without --proof reconstructs proof and exported code from repository sources. Every claim-table '
              'control, paired projection, fibre control, source reader application and guided construction is a '
              'definition over the existing child example and its native operations, and every result is presented. '
              'The assertion child remains an assumption; whole-graph and closed-proof admission are separate.'))


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
