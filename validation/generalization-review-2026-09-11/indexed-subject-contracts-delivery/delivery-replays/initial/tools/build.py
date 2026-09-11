#!/usr/bin/env python3
"""Build the Isabelle session and bind the result to its exact source bytes."""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import uuid

ROOT = Path(__file__).resolve().parents[1]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def source_hashes() -> dict[str, str]:
    paths = [ROOT / "ROOT", *sorted((ROOT / "theories").glob("*.thy"))]
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in paths}


def tool_hashes() -> dict[str, str]:
    return {f"tools/{name}": hashlib.sha256((ROOT / "tools" / name).read_bytes()).hexdigest()
            for name in ("build.py", "check.py")}


def atomic_json(path: Path, value: dict) -> None:
    """Readers see either the previous whole report or its whole replacement."""
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "w") as stream:
            json.dump(value, stream, indent=2)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


@contextmanager
def validation_lock():
    """Serialize the shared reports and Isabelle diagnostic cache on POSIX."""
    output = ROOT / "validation"
    output.mkdir(parents=True, exist_ok=True)
    with (output / ".validation.lock").open("a") as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        yield


class RunInterrupted(Exception):
    def __init__(self, signum: int):
        self.signum = signum
        super().__init__(f"Interrupted by signal {signum}.")


@contextmanager
def interruption_signals():
    def interrupt(signum, _frame):
        raise RunInterrupted(signum)

    signals = (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)
    previous = {s: signal.signal(s, interrupt) for s in signals}
    try:
        yield
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)


def stop_process(process: subprocess.Popen) -> None:
    """Stop the whole spawned session, including surviving child processes."""
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired:
        pass
    finally:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()


def run_command(command: list[str], env: dict, log, verbose: bool = False, *, display: bool = True) -> tuple[int, str]:
    process = subprocess.Popen(command, cwd=ROOT, env=env, text=True, bufsize=1,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               start_new_session=True)
    lines = []
    try:
        assert process.stdout is not None
        for line in process.stdout:
            lines.append(line)
            log.write(line)
            log.flush()
            if display and (verbose or line.startswith(("Running ", "Finished ", "***", "Unfinished ")) or " FAILED " in line):
                print(line, end="", flush=True)
        return process.wait(), "".join(lines)
    finally:
        stop_process(process)
        if process.stdout is not None:
            process.stdout.close()


def add_arguments(parser: argparse.ArgumentParser, *, combined: bool = False) -> None:
    parser.add_argument("--isabelle", default="isabelle")
    parser.add_argument("--threads", type=int, default=min(12, os.cpu_count() or 1) if combined else 4)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--cache-home", type=Path,
                        default=Path(tempfile.gettempdir()) / "structural-isabelle")
    if not combined:
        parser.add_argument("--verbose", action="store_true")
        parser.add_argument("--session", action="append", default=[])
    else:
        parser.set_defaults(verbose=False, session=[])


def run_build(args, invocation: str) -> dict:
    """Return this invocation's evidence directly; caller holds validation_lock."""
    output = ROOT / "validation"
    receipt_path = output / "build.json"
    log_path = output / "build.log"
    env = os.environ.copy()
    env["USER_HOME"] = str(args.cache_home.resolve())
    command = [args.isabelle, "build", "-v", "-o", f"threads={args.threads}",
               "-o", f"timeout={args.timeout}"]
    command += ["-d", str(ROOT), *args.session] if args.session else ["-D", str(ROOT)]
    receipt = {"invocation": invocation, "status": "running", "started_utc": utc_now(),
               "command": command, "base_session": "HOL", "exit_code": 1,
               "session_diagnostics": ""}
    atomic_json(receipt_path, receipt)
    try:
        # Truncate before probing the executable so startup errors cannot retain an old log.
        with log_path.open("w") as log:
            log.write(f"Invocation: {invocation}\n")
            receipt["sources"] = source_hashes()
            receipt["tools"] = tool_hashes()
            code, version = run_command([args.isabelle, "version"], env, log, display=False)
            if code:
                receipt["exit_code"] = code
                raise RuntimeError(f"Isabelle version command exited with {code}: {version.strip()}")
            receipt["isabelle_version"] = version.strip()
            print(version.strip(), flush=True)
            code, build_output = run_command(command, env, log, args.verbose)
            receipt["exit_code"] = code
            receipt["sources_unchanged"] = source_hashes() == receipt["sources"]
            receipt["tools_unchanged"] = tool_hashes() == receipt["tools"]
            if not receipt["sources_unchanged"] or not receipt["tools_unchanged"]:
                raise RuntimeError("Theory sources or validation tools changed during the build.")
            # Only a session started by this invocation can supply cache diagnostics.
            if code:
                sessions = []
                for line in build_output.splitlines():
                    if line.startswith(("Running ", "Building ")) and " ..." in line:
                        name = line.split()[1]
                        if name not in sessions:
                            sessions.append(name)
                diagnostics = []
                for name in sessions:
                    _, detail = run_command([args.isabelle, "build_log", "-H", "Error", name], env, log, display=False)
                    diagnostics.append(detail)
                receipt["session_diagnostics"] = "".join(diagnostics)
            receipt["status"] = "accepted" if code == 0 else "failed"
    except RunInterrupted as error:
        receipt.update(status="interrupted", exit_code=128 + error.signum, error=str(error))
    except KeyboardInterrupt:
        receipt.update(status="interrupted", exit_code=130, error="Interrupted.")
    except Exception as error:
        receipt.update(status="failed", exit_code=receipt["exit_code"] or 1, error=str(error))
        print(f"Build failed: {error}", file=sys.stderr)
    finally:
        receipt["finished_utc"] = utc_now()
        if log_path.exists():
            receipt["log_sha256"] = hashlib.sha256(log_path.read_bytes()).hexdigest()
        atomic_json(receipt_path, receipt)
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    add_arguments(parser)
    args = parser.parse_args()
    if args.threads < 1 or args.timeout < 1:
        parser.error("--threads and --timeout must be positive")
    with interruption_signals(), validation_lock():
        invocation = str(uuid.uuid4())
        atomic_json(ROOT / "validation/check.json", {
            "invocation": invocation, "status": "not_checked", "started_utc": utc_now(),
            "reason": "Standalone build; combined structural source checks were not requested."})
        return run_build(args, invocation)["exit_code"]


if __name__ == "__main__":
    raise SystemExit(main())
