"""Reconstruct the complete certificate scope repair execution from repository sources."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='certificate-scope-repair',
    roots=('Native_Certificate_Scope_Repair_Execution',),
    export='Native_Certificate_Scope_Repair_Execution:certificate_scope_repair.ML',
    session='Reconstruct_certificate_scope_repair',
    groups=((Execution("comparison", 'check_native_certificate_scope_repair.py', ("--project", "{project}"), 2100),),),
    boundary='The actual scope correction retains every full original input and appends compiled native sources and independently checked supplied certificates. Every complete input, source/proof check, original family, conflict witness, comparison and revision is reproduced. The correction is assessed against the original retention and coverage conditions.')


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
