"""Run accepted Eval exports in Isabelle's ordered parallel runtime."""
from pathlib import Path
import json

import investigate
import native_artifact_stream


def inputs():
    return [Path(p) for p in [
        '/opt/isabelle/heaps/polyml-5.9.2_x86_64_32-linux/Pure',
        '/opt/isabelle/bin/isabelle', '/usr/bin/env',
        '/opt/isabelle/src/Pure/ML/ml_process.scala',
        '/opt/isabelle/src/Pure/Concurrent/par_list.ML',
        '/opt/isabelle/src/Pure/Concurrent/future.ML',
        '/opt/isabelle/src/Pure/Concurrent/task_queue.ML',
        '/opt/isabelle/src/Pure/Concurrent/multithreading.ML',
        '/opt/isabelle/src/HOL/Library/Parallel.thy',
        '/opt/isabelle/contrib/polyml-5.9.2-2/etc/settings']]


def prepare(proof, engine, code, poly, output, *, workers=16, target=None):
    """Choose transport/execution only; the accepted export retains semantic authority."""
    runtime = output / 'execute.ML'
    command = [str(poly), '--script', str(runtime)]
    extra = []
    target = target or proof.get('code_target')
    if proof.get('complete_artifact_transport'):
        code = native_artifact_stream.program(code, parallel=target == 'Eval',
                                             terms=proof.get('complete_term_transport', False))
    if target == 'Eval':
        if not 1 <= workers <= 16:
            raise ValueError('Expected between one and sixteen native workers.')
        loading = 'use ' + investigate.ml_string(str(engine)) + ';\n'
        if code.count(loading) != 1:
            raise ValueError('The Eval export must have one exact source load.')
        code = code.replace(loading, '', 1)
        # The Pure toplevel echoes every bound value. Printing whole native packets
        # dominated execution time; tagged reports are printed explicitly below.
        code = ('val () = ML_Print_Depth.set_print_depth 0;\n'
                'val print = fn text => TextIO.output (TextIO.stdOut, text);\n' + code)
        code += '\nval () = TextIO.flushOut TextIO.stdOut;\nval () = Future.shutdown ();\n' \
                'val () = OS.Process.exit OS.Process.success;\n'
        home = output / 'runtime-home'
        home.mkdir()
        command = ['/usr/bin/env', 'USER_HOME=' + str(home), '/opt/isabelle/bin/isabelle',
                   'ML_process', '-l', 'Pure', '-o', 'threads=' + str(workers), '-o', 'threads_stack_limit=0',
                   '-f', str(engine), '-f', str(runtime)]
        extra = inputs()
    (output / 'runtime-command.json').write_text(json.dumps(command) + '\n')
    return code, command, extra
