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

import build
import execution_support as investigate
import native_execution_runtime
import proved_code
from evidence_io import write_json

TAG = 'PRESENTED_REPORT_WORD'
CONSTANT = re.compile(r'[a-z][a-z_0-9]*')
MODULE = re.compile(r'[A-Z][A-Za-z_0-9]*')
SUBJECT = re.compile(r"[A-Za-z][A-Za-z_0-9']*(\.[A-Za-z][A-Za-z_0-9']*)*")
BOUNDARY = ('The exported report value presents the complete report through the presentations of its notions; '
            'each presentation identifies its subject exactly, and a store exactly by its original view. '
            'finite_term_shared_word_fold delivers the proved prefix-free digit word of that presentation, with every '
            'distinct artifact given once. The host packs '
            'the delivered bits into bytes, followed by one terminating bit and zero padding, and retains their size '
            'and SHA-256; it never reads a generated representation. Equal words identify equal presented reports. '
            'The chosen collection order of a word carries no meaning of its own.')


BITS = ('fun octet_bits w = List.tabulate (8, fn i => Word8.andb (Word8.>> (w, Word.fromInt (7 - i)), 0w1) = 0w1);\n'
        'fun file_bits path = let val stream = BinIO.openIn path; val octets = BinIO.inputAll stream\n'
        '  in BinIO.closeIn stream; List.concat (Word8Vector.foldr (fn (w, acc) => octet_bits w :: acc) [] octets) end;\n')


def program(engine, inputs, word):
    """Stream the proved word of one report value into a byte file.

    The value is the report applied to its constant arguments, then to a subject name and to the bits of a
    supplied file of octets, each when given; the octets are unpacked most significant bit first, padding
    included, so the value's own reader decides what they present. With a word constant `c`, proved in its
    theory to satisfy `c f x z = finite_term_shared_word_fold f (report x) z`, the word is `c` applied to the
    sink and the same arguments: the same bits, computed as that constant's code equation computes them."""
    arguments = ['N.' + inputs[name] for name in ['scope', 'selections'] if inputs.get(name) is not None]
    if inputs.get('subject') is not None:
        arguments.append(investigate.ml_string(inputs['subject']))
    if inputs.get('bits') is not None:
        arguments.append('(file_bits ' + investigate.ml_string(inputs['bits']) + ')')
    if inputs.get('word') is not None:
        word_value = 'N.' + inputs['word'] + ' sink ' + ' '.join('(' + a + ')' for a in arguments) + ' (0, 0)'
    else:
        word_value = 'N.finite_term_shared_word_fold sink (' + ' '.join(['N.' + inputs['report'], *arguments]) + ') (0, 0)'
    return ('use ' + investigate.ml_string(str(engine)) + ';\n'
            'structure N = ' + inputs['module'] + ';\n' + (BITS if inputs.get('bits') is not None else '') +
            'val stream = BinIO.openOut ' + investigate.ml_string(str(word)) + ';\n'
            'fun sink (acc, n) b =\n'
            '  let val acc = acc * 2 + (if b then 1 else 0)\n'
            '  in if n = 7 then (BinIO.output1 (stream, Word8.fromInt acc); (0, 0)) else (acc, n + 1) end;\n'
            'fun pad (acc, n) = if n = 0 then () else pad (sink (acc, n) false);\n'
            'val () = pad (sink (' + word_value + ') true);\n'
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
    for name in ['module', 'report']:
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--scope', help='First constant argument of the report value.')
    parser.add_argument('--selections', help='Second argument of the report value; omitted for a report of its scope alone.')
    parser.add_argument('--subject', help='A name argument of the report value, after its constant arguments.')
    parser.add_argument('--bits', type=Path, help='A file of octets whose bits are the last argument of the report value.')
    parser.add_argument('--word', help='An exported constant c, proved to satisfy '
                        'c f x z = finite_term_shared_word_fold f (report x) z, that computes the word instead.')
    parser.add_argument('--theory', help='Exporting Isabelle theory; defaults to the ML module name.')
    parser.add_argument('--workers', type=int, default=16)
    parser.add_argument('--timeout', type=int, default=2400)
    args = parser.parse_args()
    if not __debug__:
        raise ValueError('Presented report checks require Python assertions.')
    assert MODULE.fullmatch(args.module)
    theory = args.theory or args.module
    assert MODULE.fullmatch(theory)
    assert 1 <= args.workers <= 16
    assert CONSTANT.fullmatch(args.report)
    assert args.scope is not None or args.subject is not None, 'A report value takes a scope or a subject.'
    assert all(getattr(args, name) is None or CONSTANT.fullmatch(getattr(args, name)) for name in ['scope', 'selections'])
    assert args.subject is None or SUBJECT.fullmatch(args.subject)
    assert args.word is None or CONSTANT.fullmatch(args.word)
    bits = None if args.bits is None else args.bits.resolve()
    assert bits is None or bits.is_file()
    output, poly = args.output.resolve(), args.poly.resolve()
    proof_path = args.proof.resolve()
    proof, engine, sources = proved_code.proved_export(proof_path, required_theories=[theory],
                                                       project=args.project.resolve())
    assert not output.exists(), 'Retain preceding executions and use a new directory.'
    output.mkdir(parents=True)
    inputs = {'theory': theory, 'module': args.module, 'report': args.report,
              'scope': args.scope, 'selections': args.selections, 'subject': args.subject,
              'bits': None if bits is None else str(bits)}
    if args.word is not None:
        inputs['word'] = args.word
    receipt = {'status': 'failed', 'invocation': str(uuid.uuid4()), 'inputs': inputs,
               'workers': args.workers, 'boundary': BOUNDARY}
    word = output / 'report.word'
    try:
        input_file = output / 'cases.json'
        write_json(input_file, inputs)
        code, command, runtime_inputs = native_execution_runtime.prepare(
            proof, engine, program(engine, inputs, word), poly, output, workers=args.workers)
        runtime = output / 'execute.ML'
        runtime.write_text(code)
        modules = [build, investigate, native_execution_runtime, proved_code]
        paths = {proof_path, engine, poly, runtime, input_file, Path(__file__).resolve(),
                 *(Path(m.__file__).resolve() for m in modules), *(Path(p) for p in sources),
                 *runtime_inputs, output / 'runtime-command.json', *([bits] if bits is not None else [])}
        tracked = {str(p): investigate.file_hash(p) for p in paths}
        write_json(output / 'execution-inputs.json', tracked)
        proved_code.archive_execution_inputs(output, receipt, tracked, external=[poly])
        with (output / 'native.log').open('w') as log:
            returncode = build.run_session(command, stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout)
        receipt['exit_code'] = returncode
        assert returncode == 0, 'See the retained native.log.'
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
