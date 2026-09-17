"""Reconstruct complete native artifact lookup and local update observations."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='artifact-lookup',
    roots=('Artifact_Lookup_Execution',),
    export='Artifact_Lookup_Execution:artifact_lookup.ML',
    session='Reconstruct_artifact_lookup',
    groups=((Execution('comparison', 'check_artifact_lookup.py', ('--project', '{project}'), 1200),
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Artifact_Lookup_Execution', '--module', 'Artifact_Lookup_Execution', '--report', 'artifact_lookup_report_value', '--scope', 'artifact_lookup_indices', '--selections', 'artifact_lookup_report_selections', '--workers', '4', '--timeout', '600'), 660),),),
    boundary='Every complete original artifact row, query use, reference and candidate result, native soundness and completeness observation, comparison, revision, counted key path and before/after lookup is reproduced from source. The index preserves original artifact membership on all inputs; path-position counts are separate from index preparation, value equality, global formation and the complete physical decision cost.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
