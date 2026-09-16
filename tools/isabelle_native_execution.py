"""Run proved Eval exports with Isabelle's existing ordered parallel runtime."""
from pathlib import Path
import json
import resource
import time

import compressed_native_execution
import investigate
from evidence_io import digest, write_json


def checked_execution(proof_path, poly, output, *, workers, program, input_paths, **arguments):
    assert 1 <= workers <= 16
    poly, output = Path(poly).resolve(), Path(output).resolve()
    assert poly == Path('/opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly')
    isabelle = Path('/opt/isabelle/bin/isabelle')
    runtime_inputs = [
        Path('/opt/isabelle/heaps/polyml-5.9.2_x86_64_32-linux/Pure'), isabelle, Path('/usr/bin/env'),
        Path('/opt/isabelle/src/Pure/ML/ml_process.scala'),
        Path('/opt/isabelle/src/Pure/ML/ml_statistics.ML'),
        Path('/opt/isabelle/src/HOL/Library/Parallel.thy'),
        Path('/opt/isabelle/src/Pure/Concurrent/par_list.ML'),
        Path('/opt/isabelle/src/Pure/Concurrent/future.ML'),
        Path('/opt/isabelle/src/Pure/Concurrent/task_queue.ML'),
        Path('/opt/isabelle/src/Pure/Concurrent/multithreading.ML'),
        Path('/opt/isabelle/contrib/polyml-5.9.2-2/etc/settings'),
    ]
    engine_path = None

    def runtime_program(engine, inputs):
        nonlocal engine_path
        engine_path = Path(engine).resolve()
        code = program(engine, inputs)
        loading = 'use ' + investigate.ml_string(str(engine)) + ';\n'
        assert code.count(loading) == 1
        code = code.replace(loading, '', 1)
        return 'val print = fn text => TextIO.output (TextIO.stdOut, text);\n' + code + \
            '\nval () = TextIO.flushOut TextIO.stdOut;\n' \
            'val () = Future.shutdown ();\nval () = OS.Process.exit OS.Process.success;\n'

    original_execution = compressed_native_execution.compressed_execution

    def runtime_execution(command, log, timeout):
        assert engine_path is not None and engine_path.is_file()
        home = output / 'runtime-home'
        home.mkdir()
        actual = ['/usr/bin/env', 'USER_HOME=' + str(home), str(isabelle),
                  'ML_process', '-l', 'Pure', '-o', 'threads=' + str(workers),
                  '-f', str(engine_path), '-f', command[-1]]
        write_json(output / 'runtime-command.json', actual)
        return original_execution(actual, log, timeout)

    started = time.monotonic()
    cpu_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    compressed_native_execution.compressed_execution = runtime_execution
    try:
        result = compressed_native_execution.checked_execution(proof_path, poly, output,
            program=runtime_program, input_paths=[Path(__file__), *runtime_inputs, *input_paths], **arguments)
    finally:
        compressed_native_execution.compressed_execution = original_execution
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
