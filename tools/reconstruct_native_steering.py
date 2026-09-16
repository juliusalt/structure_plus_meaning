"""Reconstruct the closed native producer-selection cycle from original subjects."""
from compressed_reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-steering',
    roots=('Native_Development_Steering',),
    export='Native_Development_Steering:native_steering.ML',
    session='Reconstruct_Native_Steering',
    groups=((Execution('subjects', 'check_native_steering.py',
        ('--project', '{project}', '--workers', '16'), 900),
        Execution('empty', 'check_native_steering.py',
        ('--project', '{project}', '--empty', '--workers', '2'), 900),
        Execution('first', 'check_native_steering.py',
        ('--project', '{project}', '--first', '--workers', '4'), 900)),
        (Execution('questions', 'roundtrip_native_steering.py',
        ('--project', '{project}', '--comparison', '{output}/subjects/results.log.gz', '--workers', '16'), 900),)),
    fixtures=('tools/isabelle_native_execution.py', 'tools/native_development_input.py',
              'tools/native_development_json.py', 'tools/compressed_reconstruction_suite.py'),
    boundary='The complete original development questions reconstruct every actual producer result and '
             'independent original-goal reference. Computed observations construct ordinary native criteria '
             'with a proved original-subject equation. The closed native cycle derives producer selection '
             'through generation, original-condition compilation, certified observations, independent criticism, '
             'comparison, revision and admission. The unique native choice executes subsequent original requests; '
             'every resulting claim is checked against the original request again. Empty original scope refuses, '
             'retaining the unexecuted requests. A single-question scope exercises actual choice ambiguity. Full original questions and requests roundtrip. The finite '
             'producer and subject scope, broader development coverage and genesis remain explicit.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
