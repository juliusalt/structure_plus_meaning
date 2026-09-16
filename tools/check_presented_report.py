#!/usr/bin/env python3
"""Execute a proved report presentation and retain the digest of its complete digit word."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import re
import subprocess
import traceback
import uuid

import investigate
import native_execution_runtime
import proved_code
from evidence_io import write_json

TAG = 'PRESENTED_REPORT_WORD'
CONSTANT = re.compile(r'[a-z][a-z_0-9]*')
MODULE = re.compile(r'[A-Z][A-Za-z_0-9]*')
BOUNDARY = ('The exported report value presents the complete report through the presentations of its notions; '
            'each presentation identifies its subject exactly, and a store exactly by its original view. '
            'finite_term_shared_word_fold delivers the proved prefix-free digit word of that presentation, with every '
            'distinct artifact given once. The host packs '
            'the delivered bits into bytes, followed by one terminating bit and zero padding, and retains their size '
            'and SHA-256; it never reads a generated representation. Equal words identify equal presented reports. '
            'The chosen collection order of a word carries no meaning of its own.')


def program(engine, inputs, word):
    """Stream the proved word of one report value into a byte file."""
    report = 'N.' + inputs['report'] + ' N.' + inputs['scope'] + ' N.' + inputs['selections']
    return ('use ' + investigate.ml_string(str(engine)) + ';\n'
            'structure N = ' + inputs['module'] + ';\n'
            'val stream = BinIO.openOut ' + investigate.ml_string(str(word)) + ';\n'
            'fun sink (acc, n) b =\n'
            '  let val acc = acc * 2 + (if b then 1 else 0)\n'
            '  in if n = 7 then (BinIO.output1 (stream, Word8.fromInt acc); (0, 0)) else (acc, n + 1) end;\n'
            'fun pad (acc, n) = if n = 0 then () else pad (sink (acc, n) false);\n'
            'val () = pad (sink (N.finite_term_shared_word_fold sink (' + report + ') (0, 0)) true);\n'
            'val () = BinIO.closeOut stream;\n')


def retain_word(word, compressed):
    """Hash the complete byte word and keep it compressed as run evidence."""
    checksum = hashlib.sha256()
    size = 0
    with word.open('rb') as source, gzip.open(compressed, 'wb', compresslevel=1) as target:
        while block := source.read(1 << 20):
            checksum.update(block)
            target.write(block)
            size += len(block)
    return {'bytes': size, 'sha256': checksum.hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    for name in ['module', 'report', 'scope', 'selections']:
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--theory', help='Exporting Isabelle theory; defaults to the ML module name.')
    parser.add_argument('--timeout', type=int, default=2400)
    args = parser.parse_args()
    if not __debug__:
        raise ValueError('Presented report checks require Python assertions.')
    assert MODULE.fullmatch(args.module)
    theory = args.theory or args.module
    assert MODULE.fullmatch(theory)
    assert all(CONSTANT.fullmatch(getattr(args, name)) for name in ['report', 'scope', 'selections'])
    output, poly = args.output.resolve(), args.poly.resolve()
    proof_path = args.proof.resolve()
    proof, engine, sources = proved_code.proved_export(proof_path, required_theories=[theory],
                                                       project=args.project.resolve())
    assert not output.exists(), 'Retain preceding executions and use a new directory.'
    output.mkdir(parents=True)
    inputs = {'theory': theory, 'module': args.module, 'report': args.report,
              'scope': args.scope, 'selections': args.selections}
    receipt = {'status': 'failed', 'invocation': str(uuid.uuid4()), 'inputs': inputs, 'boundary': BOUNDARY}
    word = output / 'report.word'
    try:
        input_file = output / 'cases.json'
        write_json(input_file, inputs)
        code, command, runtime_inputs = native_execution_runtime.prepare(
            proof, engine, program(engine, inputs, word), poly, output)
        runtime = output / 'execute.ML'
        runtime.write_text(code)
        modules = [investigate, native_execution_runtime, proved_code]
        paths = {proof_path, engine, poly, runtime, input_file, Path(__file__).resolve(),
                 *(Path(m.__file__).resolve() for m in modules), *(Path(p) for p in sources),
                 *runtime_inputs, output / 'runtime-command.json'}
        tracked = {str(p): investigate.file_hash(p) for p in paths}
        write_json(output / 'execution-inputs.json', tracked)
        proved_code.archive_execution_inputs(output, receipt, tracked, external=[poly])
        with (output / 'native.log').open('w') as log:
            completed = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout)
        receipt['exit_code'] = completed.returncode
        assert completed.returncode == 0, 'See the retained native.log.'
        value = retain_word(word, output / 'report.word.gz')
        word.unlink()
        assert value['bytes'] > 0
        record = TAG + ' ' + json.dumps(value, separators=(',', ':')) + '\n'
        (output / 'results.log').write_text(record)
        with gzip.open(output / 'results.log.gz', 'wt') as compressed:
            compressed.write(record)
        stable = proved_code.execution_inputs_unchanged(tracked, receipt, external=[poly])
        assert stable, 'Execution source, input or retained evidence changed.'
        receipt.update(status='accepted', word=value, sources_and_tools_unchanged=stable,
                       proof_receipt_sha256=investigate.file_hash(proof_path),
                       export_sha256=investigate.file_hash(engine),
                       results_sha256=investigate.file_hash(output / 'results.log'), execution_inputs=tracked)
    except Exception as error:
        receipt['status'] = 'failed'
        receipt['error'] = str(error)
        receipt['error_type'] = type(error).__name__
        receipt['error_traceback'] = traceback.format_exc()
        word.unlink(missing_ok=True)
    write_json(output / 'receipt.json', receipt)
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'), 'word': receipt.get('word')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
