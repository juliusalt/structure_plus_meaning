"""Use compressed report storage with the unchanged reconstruction stage checks."""
from collections import Counter
from contextlib import contextmanager
import hashlib
from pathlib import Path
import zlib

import compressed_machine_reports
from evidence_io import digest
import machine_reports
import reconstruction
from reconstruction import Execution, Recipe


def compressed_boundary(path):
    path = Path(path)
    assert path.name == 'results.log'
    compressed = path.with_name('results.log.gz')
    if not compressed.is_file():
        raise FileNotFoundError(compressed)
    counts = Counter()
    checksum = hashlib.sha256()
    try:
        for row in compressed_machine_reports.reports(compressed):
            counts[row['tag']] += 1
            compressed_machine_reports.canonical_update(checksum, row)
    except (EOFError, zlib.error) as error:
        raise ValueError('Incomplete or invalid compressed report stream: ' + str(error)) from error
    return {'records': sum(counts.values()), 'tags': dict(sorted(counts.items())), 'sha256': checksum.hexdigest()}


@contextmanager
def compressed_storage():
    """Select the storage reader for this process and retain its actual inputs."""
    assert reconstruction.boundary is machine_reports.boundary
    original_finish = reconstruction.finish_reconstruction
    extra_inputs = {str(path): digest(path) for path in (
        Path(__file__).resolve(), Path(compressed_machine_reports.__file__).resolve())}

    def finish(output, project, recipe, steps, expected, tracked, supplied_export):
        assert not (tracked.keys() & extra_inputs.keys()) or all(
            tracked[p] == extra_inputs[p] for p in tracked.keys() & extra_inputs.keys())
        return original_finish(output, project, recipe, steps, expected, tracked | extra_inputs, supplied_export)

    reconstruction.boundary = compressed_boundary
    reconstruction.finish_reconstruction = finish
    try:
        yield
    finally:
        reconstruction.finish_reconstruction = original_finish
        reconstruction.boundary = machine_reports.boundary


def main(recipe, entrypoint, argv=None):
    with compressed_storage():
        return reconstruction.main(recipe, entrypoint, argv)
