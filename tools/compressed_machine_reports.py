"""Feed losslessly decompressed bytes through the existing complete report parser."""
from pathlib import Path
import gzip
import json
import os
import shutil
import tempfile
import threading

import machine_reports


def reports(path):
    with tempfile.TemporaryDirectory(prefix='native-report-stream-') as temporary:
        pipe = Path(temporary) / 'complete.log'
        os.mkfifo(pipe)
        failures = []

        def produce():
            try:
                with gzip.open(path, 'rb') as source, pipe.open('wb') as target:
                    shutil.copyfileobj(source, target, 1024 * 1024)
            except BrokenPipeError:
                pass
            except BaseException as error:
                failures.append(error)

        worker = threading.Thread(target=produce)
        worker.start()
        parsed = machine_reports.reports(pipe)
        try:
            yield from parsed
        finally:
            parsed.close()
            worker.join()
        if failures:
            raise failures[0]


def canonical_update(checksum, row):
    # Each complete record is independent; use the original parser's canonical encoding.
    encoded = json.dumps(row, sort_keys=True, separators=(',', ':'), allow_nan=False)
    checksum.update(encoded.encode('utf-8'))
    checksum.update(b'\n')
