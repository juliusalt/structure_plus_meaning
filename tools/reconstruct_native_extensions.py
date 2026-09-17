"""Rebuild and execute complete native package construction from repository sources."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-extensions',
    roots=('Native_Extension_Execution',),
    export='Native_Extension_Execution:native_extensions.ML',
    session='Native_Extension_Reconstruction',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Extension_Execution', '--module', 'Native_Extension_Execution', '--report', 'native_extension_report_value', '--scope', 'source_requirement_variants', '--selections', 'native_control_indices', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='A run without --proof rebuilds the complete constructor and source proofs from HOL, exports the accepted code and executes all complete package reports. Every returned artifact, binding, interface, clause and coordinate is retained in the reproduced output. Complete source correspondence is proved for the concrete source models and remains a premise of the general constructor contract. General native admission of that correspondence, the whole development protocol and its cost account remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
