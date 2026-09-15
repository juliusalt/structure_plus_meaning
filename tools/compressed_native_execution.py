"""Retain a complete proved execution through verified lossless compression."""
from pathlib import Path
import gzip
import hashlib
import json
import os
import selectors
import subprocess
import sys
import time
import traceback
import uuid

import investigate
from evidence_io import write_json
import proved_code


def uncompressed_identity(path):
    checksum = hashlib.sha256()
    size = 0
    with gzip.open(path, 'rb') as source:
        while block := source.read(1024 * 1024):
            checksum.update(block)
            size += len(block)
    return {'sha256': checksum.hexdigest(), 'bytes': size}


def compressed_execution(command, output, timeout):
    checksum = hashlib.sha256()
    size = 0
    started = time.monotonic()
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    try:
        with selectors.DefaultSelector() as ready, gzip.open(output, 'wb', compresslevel=1) as target:
            ready.register(process.stdout, selectors.EVENT_READ)
            while ready.get_map():
                remaining = timeout - (time.monotonic() - started)
                if remaining <= 0:
                    raise subprocess.TimeoutExpired(command, timeout)
                for key, _ in ready.select(min(1, remaining)):
                    block = os.read(key.fd, 1024 * 1024)
                    if block:
                        checksum.update(block)
                        size += len(block)
                        target.write(block)
                    else:
                        ready.unregister(key.fileobj)
            result = process.wait(timeout=max(0.001, timeout - (time.monotonic() - started)))
        identity = {'sha256': checksum.hexdigest(), 'bytes': size}
        assert uncompressed_identity(output) == identity
        return result, identity
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
        process.stdout.close()


def checked_execution(proof_path, poly, output, *, required_theories, inputs,
                      input_paths, program, assess, question, boundary, timeout, project):
    proof_path, poly, output = (Path(p).resolve() for p in (proof_path, poly, output))
    _, engine, sources = proved_code.proved_export(proof_path, required_theories=required_theories, project=project)
    assert not output.exists(), 'Use a new directory after retaining preceding executions.'
    output.mkdir(parents=True)
    receipt = {'status': 'failed', 'invocation': str(uuid.uuid4()), 'question': question, 'boundary': boundary}
    try:
        cases = output / 'cases.json'
        write_json(cases, inputs)
        runtime = output / 'execute.ML'
        runtime.write_text(program(engine, inputs))
        directory = Path(__file__).resolve().parent
        modules = {Path(m.__file__).resolve() for m in tuple(sys.modules.values())
                   if getattr(m, '__file__', None) and Path(m.__file__).resolve().is_relative_to(directory)
                   and Path(m.__file__).is_file()}
        paths = {proof_path, engine, poly, runtime, cases, *modules,
                 *(Path(p).resolve() for p in input_paths), *(Path(p) for p in sources)}
        tracked = {str(p): investigate.file_hash(p) for p in paths}
        write_json(output / 'execution-inputs.json', tracked)
        proved_code.archive_execution_inputs(output, receipt, tracked, external=[poly])
        log = output / 'results.log.gz'
        code, identity = compressed_execution([str(poly), '--script', str(runtime)], log, timeout)
        receipt.update(exit_code=code, uncompressed_results=identity)
        assert code == 0, 'See the complete retained results.log.gz.'
        assessment = assess(inputs, log)
        stable = proved_code.execution_inputs_unchanged(tracked, receipt, external=[poly])
        assert stable, 'Execution source, input or retained evidence changed.'
        write_json(output / 'complete-results.json', assessment)
        receipt.update(status='accepted', sources_and_tools_unchanged=stable, assessment=assessment,
                       proof_receipt_sha256=investigate.file_hash(proof_path),
                       export_sha256=investigate.file_hash(engine), results_file=log.name,
                       results_sha256=investigate.file_hash(log), execution_inputs=tracked)
    except Exception as error:
        receipt.update(status='failed', error=str(error), error_type=type(error).__name__,
                       error_traceback=traceback.format_exc())
    write_json(output / 'receipt.json', receipt)
    return receipt


def accepted_execution(directory, poly, proof):
    directory, poly, proof = (Path(p).resolve() for p in (directory, poly, proof))
    receipt = json.loads((directory / 'receipt.json').read_text())
    assert receipt['status'] == 'accepted' and receipt['exit_code'] == 0
    assert receipt['proof_receipt_sha256'] == investigate.file_hash(proof)
    assert receipt['results_file'] == 'results.log.gz'
    log = directory / receipt['results_file']
    assert investigate.file_hash(log) == receipt['results_sha256']
    assert uncompressed_identity(log) == receipt['uncompressed_results']
    assert proved_code.execution_inputs_unchanged(receipt['execution_inputs'], receipt, external=[poly])
    return receipt
