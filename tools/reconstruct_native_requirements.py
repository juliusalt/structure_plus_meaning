"""Rebuild native requirement construction, its subject comparison and computed revisions."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-requirements',
    roots=('Native_Requirement_Investigation_Execution',),
    export='Native_Requirement_Investigation_Execution:native_requirement_investigation.ML',
    session='Native_Requirement_Reconstruction',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Requirement_Investigation_Execution', '--module', 'Native_Requirement_Investigation_Execution', '--report', 'native_requirement_report_value', '--scope', 'native_requirement_indices', '--selections', 'native_requirement_report_selections', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='A run without --proof reconstructs the complete contracts from HOL. The actual source reader supplies the native program, and a shared structural goal constructor installs every goal occurrence and a final conjunction before compiling their complete source extension. Computed observations compare the original same-term conjunction, every retained artifact and outgoing binding, and refusal of unsupported requests. All subjects, counterexample terms, condition observations, comparisons, adequacy results and revisions are reproduced. The selected scope does not establish unrestricted coverage, complete development-cycle enforcement, native proof construction, the complete cost account or genesis.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
