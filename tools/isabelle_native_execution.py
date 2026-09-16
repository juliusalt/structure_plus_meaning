"""Run proved Eval exports with Isabelle's existing ordered parallel runtime."""
from pathlib import Path
import json
import resource
import time

import compressed_native_execution
from evidence_io import digest, write_json


def checked_execution(proof_path, poly, output, *, workers, program, input_paths, **arguments):
    assert 1 <= workers <= 16
    poly, output = Path(poly).resolve(), Path(output).resolve()
    assert poly == Path('/opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly')
    runtime_inputs = [
        Path('/opt/isabelle/src/Pure/ML/ml_statistics.ML'),
    ]

    started = time.monotonic()
    cpu_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    result = compressed_native_execution.checked_execution(proof_path, poly, output,
        program=program, workers=workers, runtime_target='Eval',
        input_paths=[Path(__file__), *runtime_inputs, *input_paths], **arguments)
    cpu_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    elapsed = time.monotonic() - started
    write_json(output / 'physical-runtime.json', {
        'status': result['status'], 'workers': workers, 'seconds': elapsed,
        'cpu_user_seconds': cpu_after.ru_utime - cpu_before.ru_utime,
        'cpu_system_seconds': cpu_after.ru_stime - cpu_before.ru_stime,
        'runtime_command_sha256': digest(output / 'runtime-command.json')
            if (output / 'runtime-command.json').is_file() else None,
        'boundary': 'Physical execution and retention metadata only. The proved native source '
                    'and its registered complete subject contract establish meaning.'})
    return result
