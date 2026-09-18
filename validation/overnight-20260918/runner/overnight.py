#!/usr/bin/env python3
"""Sequential Codex goal supervisor, Linux, Python 3.11+.

No third-party Python dependencies. Does not interpret or certify project proofs.
Run preflight on YOUR authenticated machine before run. Unit tests use a fake CLI.
"""
from __future__ import annotations

import argparse
import ctypes
from contextlib import contextmanager
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from typing import Any, Iterator
import uuid

HERE = Path(__file__).resolve().parent
CONTROL_FILES = ('overnight.py', 'overnight_hook.py', 'result.schema.json', 'WORKER.md', 'RECOVERY.md', 'REVIEW.md')
STATUSES = {'continue', 'candidate_complete', 'blocked'}
STOP_SIGNAL: int | None = None


class StopRun(RuntimeError):
    """A condition that must not automatically launch another worker."""


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def atomic_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.' + uuid.uuid4().hex + '.tmp')
    try:
        with temporary.open('x', encoding='utf-8') as stream:
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def write_json(path: Path, value: Any) -> None:
    atomic_text(path, json.dumps(value, indent=2, default=str) + '\n')


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding='utf-8'))


def command(args: list[str], root: Path, timeout: int = 120) -> str:
    result = subprocess.run(args, cwd=root, text=True, capture_output=True, timeout=timeout)
    if result.returncode:
        raise StopRun(f'{args[0]} failed ({result.returncode}): {result.stderr[-3000:]}')
    return result.stdout


def file_hash(path: Path) -> str:
    digest = hashlib.sha256()
    if path.is_symlink():
        return hashlib.sha256(os.readlink(path).encode()).hexdigest()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def artifact_fingerprint(root: Path) -> str:
    """Change/no-change tripwire, never a semantic acceptance test."""
    result = subprocess.run(['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard'],
                            cwd=root, capture_output=True, check=True)
    names = sorted(set(result.stdout.split(b'\0')) - {b''})
    digest = hashlib.sha256()
    for raw in names:
        name = os.fsdecode(raw)
        if name.split('/')[0] in {'.overnight', '.codex'}:
            continue
        path = root / name
        digest.update(raw + b'\0')
        if path.is_symlink():
            digest.update(os.readlink(path).encode())
        elif path.is_file():
            digest.update(file_hash(path).encode())
        else:
            digest.update(b'<absent>')
    return digest.hexdigest()


def control_signature(root: Path, args: argparse.Namespace, version: str) -> str:
    values: dict[str, Any] = dict(root=str(root), version=version, model=args.model,
                                  effort=args.effort, context=args.context,
                                  hard=args.hard, soft=args.soft, target=args.target, codex=args.codex)
    values['files'] = {name: file_hash(HERE / name) for name in CONTROL_FILES}
    for name in ('.codex/hooks.json', '.codex/config.toml'):
        path = root / name
        values[name] = file_hash(path) if path.is_file() else None
    home = Path(os.environ.get('CODEX_HOME', str(Path.home() / '.codex')))
    # Changing user config or user hooks requires a new local smoke test too.
    for name in ('config.toml', 'hooks.json'):
        path = home / name
        values['user_' + name] = file_hash(path) if path.is_file() else None
    return hashlib.sha256(json.dumps(values, sort_keys=True).encode()).hexdigest()


def tail(path: Path, limit: int = 65536) -> str:
    try:
        with path.open('rb') as stream:
            stream.seek(0, 2)
            start = max(0, stream.tell() - limit)
            stream.seek(start)
            data = stream.read()
        if start:
            data = data.partition(b'\n')[2]
        return data.decode('utf-8', errors='replace')
    except OSError:
        return ''


def snapshot(root: Path, directory: Path) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    atomic_text(directory / 'git-status.txt', command(['git', 'status', '--short', '--branch'], root))
    atomic_text(directory / 'git-head.txt', command(['git', 'rev-parse', 'HEAD'], root))
    # No mutation of index or working files; binary diff includes staged+unstaged net changes.
    with (directory / 'tracked.patch').open('wb') as stream:
        subprocess.run(['git', 'diff', '--no-ext-diff', '--binary', 'HEAD'], cwd=root, stdout=stream,
                       stderr=subprocess.DEVNULL, check=True, timeout=120)
    atomic_text(directory / 'untracked.txt', command(['git', 'ls-files', '--others', '--exclude-standard'], root))
    for name in ('STATE.md', 'HANDOFF.md', 'JOBS.json'):
        src = root / '.overnight' / name
        if src.is_file():
            shutil.copy2(src, directory / name)


def validate_result(value: Any) -> dict[str, Any]:
    keys = {'status', 'summary', 'next_action', 'handoff_markdown', 'evidence_paths'}
    if not isinstance(value, dict) or set(value) != keys or value.get('status') not in STATUSES:
        raise ValueError('Invalid final result shape/status')
    for key in ('summary', 'next_action', 'handoff_markdown'):
        if not isinstance(value[key], str) or not value[key].strip():
            raise ValueError(f'Missing {key}')
    if not 80 <= len(value['handoff_markdown']) <= 30000:
        raise ValueError('Handoff must be 80–30,000 characters, with concrete evidence pointers')
    if not isinstance(value['evidence_paths'], list) or not all(isinstance(x, str) for x in value['evidence_paths']):
        raise ValueError('Invalid evidence_paths')
    return value


def active_catalog(root: Path, args: argparse.Namespace) -> dict[str, Any]:
    raw = command([args.codex, 'debug', 'models'], root, timeout=180)
    try:
        value = json.loads(raw)
    except ValueError as error:
        raise StopRun('codex debug models did not return JSON. Update/check the CLI; do not use bundled data as account verification.') from error
    models = value.get('models', []) if isinstance(value, dict) else value
    if not isinstance(models, list):
        raise StopRun('Unrecognized runtime model catalog structure')
    model = next((m for m in models if isinstance(m, dict) and m.get('slug') == args.model), None)
    if not model:
        raise StopRun(f'{args.model} was not found in this account\'s runtime catalog')
    levels = model.get('supported_reasoning_levels', [])
    efforts = [x.get('effort') if isinstance(x, dict) else x for x in levels]
    if args.effort not in efforts:
        raise StopRun(f'Runtime catalog does not advertise {args.effort}: {efforts}; no automatic model/effort substitution')
    ceiling = model.get('max_context_window') or model.get('context_window')
    if type(ceiling) is not int or ceiling < args.context:
        raise StopRun(f'Requested context {args.context} exceeds or cannot be checked against advertised ceiling {ceiling}')
    percent = model.get('effective_context_window_percent') or 95
    if type(percent) is not int or not 0 < percent <= 100:
        raise StopRun('Unrecognized effective context percentage in runtime catalog')
    if args.hard >= args.context * percent // 100:
        raise StopRun('Rollover backstop must be below the effective context window; increase --context or lower --hard')
    fields = ('slug', 'context_window', 'max_context_window', 'effective_context_window_percent',
              'auto_compact_token_limit', 'supported_reasoning_levels', 'supports_experimental_context')
    return {key: model.get(key) for key in fields}


@contextmanager
def locked(root: Path) -> Iterator[None]:
    state = root / '.overnight'
    state.mkdir(exist_ok=True)
    with (state / 'supervisor.lock').open('a') as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise StopRun('Another supervisor is already using this checkout') from error
        yield


def disk_check(root: Path, args: argparse.Namespace) -> None:
    for location in {root, Path(tempfile.gettempdir())}:
        if shutil.disk_usage(location).free < args.min_free_gib * 1024 ** 3:
            raise StopRun(f'Free disk below {args.min_free_gib} GiB at {location}; retained evidence was NOT deleted')
    state = root / '.overnight'
    if args.max_log_gib:
        size = sum(p.stat().st_size for p in state.rglob('*') if p.is_file() and not p.is_symlink())
        if size > args.max_log_gib * 1024 ** 3:
            raise StopRun(f'.overnight exceeds {args.max_log_gib} GiB. Review old artifacts before cleanup; none were deleted.')


@contextmanager
def controlled_signals() -> Iterator[None]:
    global STOP_SIGNAL
    STOP_SIGNAL = None

    def request_stop(number: int, _frame: Any) -> None:
        global STOP_SIGNAL
        STOP_SIGNAL = number

    previous = {number: signal.signal(number, request_stop)
                for number in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)}
    try:
        yield
    finally:
        for number, handler in previous.items():
            signal.signal(number, handler)


def check_control(root: Path, deadline: float) -> None:
    if STOP_SIGNAL is not None:
        raise StopRun(f'operator_signal_{signal.Signals(STOP_SIGNAL).name}')
    if (root / '.overnight' / 'STOP').exists():
        raise StopRun('operator_stop')
    if time.monotonic() >= deadline:
        raise StopRun('night_deadline')


def enable_subreaper() -> None:
    """Adopt orphaned descendants, including builds that create new sessions."""
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(36, 1, 0, 0, 0) != 0:  # Linux PR_SET_CHILD_SUBREAPER
        raise StopRun(f'Cannot establish process ownership: {os.strerror(ctypes.get_errno())}')


def process_info(pid: int) -> dict[str, Any] | None:
    try:
        fields = Path(f'/proc/{pid}/stat').read_text().rsplit(') ', 1)[1].split()
        return dict(pid=pid, state=fields[0], ppid=int(fields[1]),
                    pgrp=int(fields[2]), start_ticks=int(fields[19]))
    except (OSError, ValueError, IndexError):
        return None


def owned_processes(process: subprocess.Popen, include_adopted: bool) -> list[dict[str, Any]]:
    process.poll()  # Reap the CLI through Popen so its exit status is preserved.
    rows = [info for path in Path('/proc').iterdir() if path.name.isdigit()
            if (info := process_info(int(path.name))) is not None]
    parents = {os.getpid()} if include_adopted else {process.pid}
    owned = {row['pid'] for row in rows if row['pgrp'] == process.pid}
    while True:
        found = {row['pid'] for row in rows if row['ppid'] in parents | owned}
        if found <= owned:
            break
        owned.update(found)
    alive = []
    for row in rows:
        if row['pid'] not in owned or row['pid'] == os.getpid():
            continue
        if row['state'] in {'Z', 'X'}:
            if row['ppid'] == os.getpid() and row['pid'] != process.pid:
                try:
                    os.waitpid(row['pid'], os.WNOHANG)
                except ChildProcessError:
                    pass
        else:
            alive.append(row)
    return alive


def stop_process(process: subprocess.Popen, *, include_adopted: bool = False,
                 grace: float = 3) -> list[dict[str, Any]]:
    """Finish the entire owned tree; never infer identity from PID alone."""
    signalled: dict[tuple[int, int], dict[str, Any]] = {}
    for number in (signal.SIGINT, signal.SIGTERM, signal.SIGKILL):
        until = time.monotonic() + grace
        sent: set[tuple[int, int]] = set()
        while True:
            alive = owned_processes(process, include_adopted)
            if not alive:
                process.wait()
                return list(signalled.values())
            for row in alive:
                identity = (row['pid'], row['start_ticks'])
                if identity in sent:
                    continue
                current = process_info(row['pid'])
                if current and current['start_ticks'] == row['start_ticks']:
                    try:
                        os.kill(row['pid'], number)
                        signalled[identity] = row
                    except ProcessLookupError:
                        pass
                sent.add(identity)
            if time.monotonic() >= until:
                break
            time.sleep(0.05)
    if owned_processes(process, include_adopted):
        raise StopRun('Owned processes survived cleanup; refusing to overlap another worker')
    process.wait()
    return list(signalled.values())


def retry_delay(root: Path, args: argparse.Namespace, deadline: float,
                attempt: int, reason: str) -> None:
    seconds = min(args.max_retry_seconds, args.retry_seconds * 2 ** min(attempt - 1, 12))
    until = time.monotonic() + seconds
    write_json(root / '.overnight' / 'STATUS.json',
               dict(state='waiting_to_retry', reason=reason, seconds=seconds, updated=utc()))
    print(f'[{utc()}] Continuing after {seconds:g}s backoff: {reason}', flush=True)
    check_at = 0.0
    while time.monotonic() < until:
        check_control(root, deadline)
        if time.monotonic() >= check_at:
            disk_check(root, args)
            check_at = time.monotonic() + 10
        time.sleep(min(1, max(0, until - time.monotonic())))
    check_control(root, deadline)


def service_error(directory: Path) -> str | None:
    # Inspect CLI errors, not arbitrary successful tool output quoting these words.
    messages = [tail(directory / 'stderr.log')]
    for line in tail(directory / 'events.jsonl').splitlines():
        try:
            event = json.loads(line)
            if isinstance(event, dict) and event.get('type') in {'error', 'turn.failed'}:
                messages.append(json.dumps(event))
        except ValueError:
            continue
    text = '\n'.join(messages).lower()
    if any(word in text for word in ('insufficient_quota', 'quota exceeded', 'unauthorized',
                                     'authentication failed', 'invalid api key')):
        return 'account_or_authentication_blocker'
    if any(word in text for word in ('usage limit', 'usage_limit', 'rate limit', 'rate_limit',
                                     'too many requests', '429', '503', 'overloaded',
                                     'connection', 'timed out', 'stream disconnected')):
        return 'temporary_service_error'
    return None


def invocation(root: Path, args: argparse.Namespace, directory: Path, prompt: str,
               deadline: float, *, role: str, hard: int | None = None) -> dict[str, Any]:
    check_control(root, deadline)
    directory.mkdir(parents=True, exist_ok=False)
    nonce = uuid.uuid4().hex
    env = dict(os.environ, OVERNIGHT_REPO=str(root), OVERNIGHT_INVOCATION=str(directory),
               OVERNIGHT_NONCE=nonce, OVERNIGHT_SOFT_TOKENS=str(args.soft),
               OVERNIGHT_TARGET_TOKENS=str(args.target))
    cmd = [args.codex, 'exec', '-C', str(root), '-m', args.model,
           '-c', f'model_reasoning_effort="{args.effort}"',
           '-c', f'model_context_window={args.context}',
           '-c', f'model_auto_compact_token_limit={hard if hard is not None else args.hard}',
           '-c', 'model_auto_compact_token_limit_scope="total"',
           '-c', 'features.context_management.experimental_mode=false',
           '-c', 'features.multi_agent=false', '-c', 'features.hooks=true',
           '-c', 'features.memories=false', '-c', 'features.goals=false',
           '-c', 'approval_policy="never"', '--json',
           '--output-schema', str(HERE / 'result.schema.json'),
           '--output-last-message', str(directory / 'final.json')]
    if role != 'worker':
        cmd += ['--sandbox', 'read-only']
    cmd += ['-']  # Read the prompt from stdin, not the shell or argv.
    atomic_text(directory / 'prompt.txt', prompt)
    write_json(directory / 'invocation.json', dict(role=role, command=cmd, started=utc(), nonce=nonce))
    print(f'[{utc()}] {role}: {directory.name}', flush=True)
    write_json(root / '.overnight' / 'STATUS.json', dict(state=role, invocation=str(directory), updated=utc()))
    started_at = time.monotonic()
    active_at = started_at
    activity = None
    boundary_seen: float | None = None
    failure: str | None = None
    fatal = False
    check_at = 0.0
    with (directory / 'prompt.txt').open('rb') as source, \
         (directory / 'events.jsonl').open('wb') as stdout, \
         (directory / 'stderr.log').open('wb') as stderr:
        process = subprocess.Popen(cmd, cwd=root, env=env, stdin=source,
                                   stdout=stdout, stderr=stderr, start_new_session=True)
        try:
            write_json(directory / 'process.json', process_info(process.pid))
            while process.poll() is None:
                now = time.monotonic()
                check_control(root, deadline)
                if args.worker_minutes and now - started_at > args.worker_minutes * 60:
                    failure = 'worker_timeout'
                    break
                observed = tuple((path.stat().st_size, path.stat().st_mtime_ns) if path.exists() else None
                                 for path in (directory / 'events.jsonl', directory / 'stderr.log',
                                              directory / 'telemetry.json', root / '.overnight' / 'STATE.md'))
                if observed != activity:
                    activity, active_at = observed, now
                if args.idle_minutes and now - active_at > args.idle_minutes * 60:
                    failure = 'worker_idle_timeout'
                    break
                if (directory / 'unexpected_compaction.json').exists():
                    failure = 'unexpected_compaction'
                    break
                if now - started_at > 90 and not (directory / 'started.json').exists():
                    failure = 'missing_SessionStart_hook_receipt'
                    fatal = True
                    break
                if (directory / 'rollover.json').exists():
                    boundary_seen = boundary_seen or now
                    if now - boundary_seen > 90:
                        failure = 'rollover_did_not_exit_cleanly'
                        break
                if now >= check_at:
                    disk_check(root, args)
                    check_at = now + 10
                time.sleep(0.25)
        except StopRun as error:
            failure, fatal = str(error), True
        finally:
            terminated = stop_process(process, include_adopted=True)
        returncode = process.returncode
    if terminated and failure is None:
        failure = 'unfinished_jobs_at_handoff'
    receipt_path = directory / 'started.json'
    try:
        started = load_json(receipt_path) if receipt_path.exists() else {}
        if not isinstance(started, dict):
            started = {}
    except (OSError, ValueError):
        started = {}
    service = service_error(directory) if returncode or failure else None
    if service == 'account_or_authentication_blocker':
        failure, fatal = service, True
    elif not fatal and service:
        failure = service
    if started.get('nonce') != nonce and service != 'temporary_service_error':
        failure, fatal = failure or 'missing_or_stale_SessionStart_hook_receipt', True
    elif started.get('model') != args.model:
        if started:
            failure, fatal = 'unexpected_model_at_session_start', True
    if (directory / 'unexpected_compaction.json').exists():
        failure = failure or 'unexpected_compaction'
    try:
        rollover = load_json(directory / 'rollover.json') if (directory / 'rollover.json').exists() else None
    except (OSError, ValueError):
        rollover = {}
    if rollover is not None and (not isinstance(rollover, dict) or rollover.get('nonce') != nonce
                                 or rollover.get('session_id') != started.get('session_id')):
        failure, fatal = 'stale_rollover_receipt', True
    record = dict(returncode=returncode, failure=failure, rollover=rollover,
                  session_id=started.get('session_id'), finished=utc(), terminated_processes=terminated)
    write_json(directory / 'exit.json', record)
    atomic_text(directory / 'events-tail.txt', tail(directory / 'events.jsonl'))
    transcript_path = started.get('transcript_path')
    if transcript_path:
        atomic_text(directory / 'transcript-tail.txt', tail(Path(transcript_path)))
    if fatal or (failure and role == 'preflight'):
        raise StopRun(f'{failure}; inspect {directory}. No new agent was started.')
    return record


def save_handoff(root: Path, directory: Path, result: dict[str, Any]) -> None:
    heading = (f'<!-- Operational locator only; not proof acceptance.\n'
               f'Written {utc()} from {directory.name}. -->\n\n')
    text = heading + result['handoff_markdown'].rstrip() + '\n'
    atomic_text(root / '.overnight' / 'HANDOFF.md', text)
    atomic_text(directory / 'accepted-handoff.md', text)
    write_json(root / '.overnight' / 'LATEST_RESULT.json', result)


def invocation_result(directory: Path, record: dict[str, Any]) -> dict[str, Any] | None:
    if record['returncode'] or record['rollover'] or record['failure']:
        return None
    try:
        return validate_result(load_json(directory / 'final.json'))
    except (OSError, ValueError):
        return None


def auxiliary(root: Path, args: argparse.Namespace, run: Path, index: int,
              old: Path, deadline: float, counts: dict[str, int], *, role: str) -> dict[str, Any]:
    source = 'RECOVERY.md' if role == 'recovery' else 'REVIEW.md'
    prompt = (HERE / source).read_text() + '\n\nPrevious invocation directory:\n' + str(old) + '\n'
    prompt += 'Inspect exit.json, started.json, snapshot/, events-tail.txt and transcript-tail.txt when present.\n'
    attempt = 0
    while True:
        check_control(root, deadline)
        attempt += 1
        if role == 'recovery':
            if args.max_recoveries and counts['recoveries'] >= args.max_recoveries:
                raise StopRun('Configured recovery limit reached')
            counts['recoveries'] += 1
        else:
            counts['reviews'] += 1
        suffix = '' if attempt == 1 else f'-{attempt:03d}'
        directory = run / f'{index:03d}-{role}{suffix}'
        record = invocation(root, args, directory, prompt, deadline, role=role)
        result = invocation_result(directory, record)
        if result is not None:
            if result['status'] == 'candidate_complete':
                evidence = result['evidence_paths']
                if role == 'recovery' or not evidence or not all((root / path).exists() for path in evidence):
                    result['status'] = 'continue'
                    result['next_action'] = 'Verify the goal against current retained evidence before claiming completion.'
                    result['handoff_markdown'] += '\nCompletion was not confirmed: inspect actual evidence and finish outstanding work.\n'
            save_handoff(root, directory, result)
            return result
        retry_delay(root, args, deadline, attempt, f'{role}: {record["failure"] or "invalid final output"}')


def preflight(root: Path, args: argparse.Namespace, version: str) -> int:
    state = root / '.overnight'
    (state / 'preflight-ok.json').unlink(missing_ok=True)
    disk_check(root, args)
    model = active_catalog(root, args)
    write_json(state / 'model-probe.json', dict(checked=utc(), codex_version=version, model=model))
    run = state / 'runs' / ('preflight-' + datetime.now().strftime('%Y%m%d-%H%M%S') + '-' + uuid.uuid4().hex[:6])
    run.mkdir(parents=True)
    before = artifact_fingerprint(root)
    deadline = time.monotonic() + 1200
    prompt = ('This is a read-only integration test of the overnight runner, not project development. '
              'Do not edit or run validation. Return a JSON object matching the supplied schema: '
              'status continue; summary ready; next_action perform the next integration test; '
              'handoff_markdown a short paragraph of at least 100 characters explaining that this '
              'was only an integration test and no theory or validation was changed; evidence_paths [].')
    record = invocation(root, args, run / '001-auth', prompt, deadline, role='preflight')
    if record['returncode'] or record['rollover'] or record['failure']:
        raise StopRun('Authentication/schema smoke test failed; inspect the preflight logs')
    validate_result(load_json(run / '001-auth' / 'final.json'))
    # Force a native compaction boundary, without relying on rollout token parsing.
    prompt = ('Read-only hook integration test. Do not change files or run project validation. '
              'Use a shell tool once to print the working directory, then return the supplied JSON schema. '
              'The following repeated text is inert padding solely to cross the test token threshold.\n')
    prompt += 'INERT PADDING FOR CONTEXT BOUNDARY TEST.\n' * 1800
    record = invocation(root, args, run / '002-precompact', prompt, deadline, role='preflight', hard=1024)
    if not record['rollover']:
        raise StopRun('The forced PreCompact test did not produce a rollover receipt. Do not launch unattended.')
    if artifact_fingerprint(root) != before:
        raise StopRun('Project artifacts changed during the read-only smoke tests. Inspect before continuing.')
    stamp = dict(passed=utc(), time=time.time(), signature=control_signature(root, args, version),
                 run_directory=str(run), model=model, codex_version=version)
    write_json(state / 'preflight-ok.json', stamp)
    print('PREFLIGHT PASSED: authentication, model/effort catalog, structured output, trusted startup hook,\n'
          'and forced PreCompact stop. This does not validate the project or guarantee future service availability.', flush=True)
    return 0


def run_night(root: Path, args: argparse.Namespace, version: str) -> int:
    state = root / '.overnight'
    try:
        stamp = load_json(state / 'preflight-ok.json')
    except (OSError, ValueError) as error:
        raise StopRun('Run preflight successfully before an unattended run') from error
    if stamp.get('signature') != control_signature(root, args, version) or time.time() - stamp.get('time', 0) > 86400:
        raise StopRun('Preflight is stale or the runner/configuration changed. Run preflight again.')
    for name in ('TASK.md', 'OWNER_UPDATES.md'):
        if not (state / name).is_file():
            raise StopRun(f'Missing {state / name}')
    active_catalog(root, args)
    disk_check(root, args)
    run = state / 'runs' / (datetime.now().strftime('%Y%m%d-%H%M%S') + '-' + uuid.uuid4().hex[:6])
    run.mkdir(parents=True)
    atomic_text(state / 'LATEST_RUN.txt', str(run) + '\n')
    deadline = time.monotonic() + args.hours * 3600 if args.hours else math.inf
    write_json(run / 'run.json', dict(started=utc(), codex_version=version, arguments=vars(args)))
    stagnant = 0
    blocked = 0
    failures = 0
    counts = dict(recoveries=0, reviews=0, workers=0)
    direction = ''
    outcome = 'generation_limit'
    try:
        snapshot(root, run / 'initial-snapshot')
        previous = artifact_fingerprint(root)
        while not args.max_generations or counts['workers'] < args.max_generations:
            if time.monotonic() >= deadline:
                outcome = 'night_deadline'
                break
            check_control(root, deadline)
            disk_check(root, args)
            counts['workers'] += 1
            index = counts['workers']
            directory = run / f'{index:03d}-worker'
            prompt = (HERE / 'WORKER.md').read_text()
            prompt += (f'\n\nSegment {index}. Persist towards the goal in TASK.md. '
                       f'Assess context relevance from {args.soft:,} tokens; {args.target:,} is an approximate '
                       f'planning target, and {args.hard:,} is the emergency backstop. '
                       'Choose your own handoff at a task transition when most current context will not help '
                       'the next task. Do not end merely because one batch finished or a reminder arrived.\n')
            if direction:
                prompt += '\nContinuation guidance:\n' + direction + '\n'
            try:
                record = invocation(root, args, directory, prompt, deadline, role='worker')
            finally:
                if directory.exists():
                    snapshot(root, directory / 'snapshot')
            result = invocation_result(directory, record)
            if result is None:
                failures += 1
                if record['failure'] == 'temporary_service_error' or failures > 1:
                    retry_delay(root, args, deadline, failures, record['failure'] or 'repeated worker failures')
                result = auxiliary(root, args, run, index, directory, deadline, counts, role='recovery')
            else:
                failures = 0
                save_handoff(root, directory, result)
            if result['status'] == 'candidate_complete':
                result = auxiliary(root, args, run, index, directory, deadline, counts, role='review')
            print(f'[{utc()}] {result["status"]}: {result["summary"]}', flush=True)
            write_json(run / 'latest-result.json', result)
            if result['status'] == 'candidate_complete':
                outcome = 'candidate_complete'
                break
            direction = result['next_action']
            blocked = blocked + 1 if result['status'] == 'blocked' else 0
            if blocked:
                direction += ('\nThe previous segment reported a blocker. Reassess the whole goal, choose '
                              'independent authorized work, repair prerequisites, or revise the plan consistently '
                              'with owner intent. Retain actual permission/input gaps. Do not repeat the same attempt.')
                if blocked >= 3:
                    retry_delay(root, args, deadline, blocked - 2, 'reassessing a persistent blocker')
            current = artifact_fingerprint(root)
            stagnant = stagnant + 1 if current == previous else 0
            previous = current
            if stagnant >= args.max_stagnant:
                direction += (f'\n{stagnant} segments had no project file changes. This is a replanning signal. '
                              'Inspect retained analysis and validation evidence; batch another useful frontier, '
                              'address a measured bottleneck, or change the failed method. Do not make cosmetic '
                              'edits to satisfy a file-change counter. Keep advancing the goal.')
                write_json(run / 'replanning.json', dict(segment=index, stagnant=stagnant, guidance=direction))
    except StopRun as error:
        outcome = 'stopped: ' + str(error)
        raise
    except KeyboardInterrupt:
        outcome = 'operator_interrupt'
        raise
    except Exception as error:
        outcome = f'error: {type(error).__name__}: {error}'
        raise
    finally:
        write_json(run / 'summary.json', dict(finished=utc(), outcome=outcome,
                   **counts, note='Operational outcome only. No formal project acceptance is asserted.'))
        write_json(state / 'STATUS.json', dict(state='ended', outcome=outcome, updated=utc()))
        print(f'RUN ENDED: {outcome}\nArtifacts: {run}', flush=True)
    return 0


def main() -> int:
    os.umask(0o077)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('preflight', 'run'))
    parser.add_argument('--repo', type=Path, default=Path.cwd())
    parser.add_argument('--codex', default='codex')
    parser.add_argument('--model', default='gpt-6-astra')
    parser.add_argument('--effort', default='max')
    parser.add_argument('--context', type=int, default=384000)
    parser.add_argument('--soft', type=int, default=140000)
    parser.add_argument('--target', type=int, default=260000, help='Advisory handoff planning target')
    parser.add_argument('--hard', type=int, default=300000, help='Emergency PreCompact backstop')
    parser.add_argument('--hours', type=float, default=0, help='Total time limit; 0 continues until completion')
    parser.add_argument('--worker-minutes', type=float, default=0, help='Optional segment time limit; 0 disables it')
    parser.add_argument('--idle-minutes', type=float, default=30, help='Recover a silent session after this interval; 0 disables it')
    parser.add_argument('--max-generations', type=int, default=0, help='Optional worker limit; 0 is unlimited')
    parser.add_argument('--max-recoveries', type=int, default=0, help='Optional recovery limit; 0 is unlimited')
    parser.add_argument('--max-stagnant', type=int, default=2, help='Replan after this many unchanged segments; does not stop')
    parser.add_argument('--retry-seconds', type=float, default=60, help='Initial interruptible retry delay')
    parser.add_argument('--max-retry-seconds', type=float, default=3600, help='Maximum retry delay')
    parser.add_argument('--min-free-gib', type=float, default=10)
    parser.add_argument('--max-log-gib', type=float, default=0, help='Optional log size limit; 0 disables it')
    args = parser.parse_args()
    if not sys.platform.startswith('linux') or not Path('/proc/self/stat').exists():
        parser.error('Use Linux or WSL2; automatic recovery needs /proc and child-subreaper process ownership.')
    if not 0 < args.soft < args.target < args.hard < args.context:
        parser.error('Require 0 < soft < target < hard < context')
    limits = (args.hours, args.worker_minutes, args.idle_minutes, args.max_generations,
              args.max_recoveries, args.max_log_gib, args.min_free_gib)
    if any(not math.isfinite(x) or x < 0 for x in limits):
        parser.error('Limits must be finite and nonnegative; 0 disables optional limits')
    if (args.max_stagnant < 1 or not math.isfinite(args.retry_seconds) or args.retry_seconds <= 0
            or not math.isfinite(args.max_retry_seconds) or args.max_retry_seconds < args.retry_seconds):
        parser.error('Require max-stagnant >= 1 and 0 < retry-seconds <= max-retry-seconds')
    root = args.repo.resolve()
    if not root.is_dir():
        raise StopRun('Repository path does not exist')
    actual = Path(command(['git', 'rev-parse', '--show-toplevel'], root).strip()).resolve()
    if actual != root:
        raise StopRun(f'Use the repository root: {actual}')
    if not shutil.which(args.codex):
        raise StopRun('Codex executable not found on PATH')
    if (root / '.overnight' / 'STOP').exists():
        raise StopRun('STOP file exists. Remove it deliberately only when ready to restart.')
    for name in ('AGENTS.md', 'DEVELOPMENT_WORKFLOW.md'):
        if not (root / name).is_file():
            raise StopRun(f'Required current project instruction file missing: {name}')
    version = command([args.codex, '--version'], root).strip()
    with locked(root), controlled_signals():
        enable_subreaper()
        if args.action == 'preflight':
            return preflight(root, args, version)
        return run_night(root, args, version)


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except StopRun as error:
        print(f'STOP: {error}', file=sys.stderr)
        raise SystemExit(2)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f'ERROR: {type(error).__name__}: {error}', file=sys.stderr)
        raise SystemExit(2)
    except KeyboardInterrupt:
        print('Interrupted. Inspect saved state and any detached validation jobs before restarting.', file=sys.stderr)
        raise SystemExit(130)
