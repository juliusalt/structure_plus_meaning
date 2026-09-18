#!/usr/bin/env python3
"""Local Codex hook. Inert unless launched by the companion supervisor.

PostToolUse token telemetry is advisory: rollout JSONL is not a stable API.
PreCompact is the documented native backstop, independent of that parser.
"""
from __future__ import annotations

import fcntl
import json
import os
from pathlib import Path
import sys
import time
import uuid
from typing import Any


def atomic_json(path: Path, value: Any) -> None:
    temporary = path.with_name(path.name + '.' + uuid.uuid4().hex + '.tmp')
    try:
        with temporary.open('x', encoding='utf-8') as stream:
            json.dump(value, stream, indent=2)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def last_context_tokens(path: Path) -> int | None:
    """Read a bounded tail, ignoring incomplete lines and unknown formats."""
    try:
        with path.open('rb') as stream:
            stream.seek(0, 2)
            end = stream.tell()
            start = max(0, end - 2 * 1024 * 1024)
            stream.seek(start)
            lines = stream.read().splitlines()
        if start and lines:
            lines = lines[1:]
        for line in reversed(lines):
            try:
                row = json.loads(line)
                payload = row.get('payload', {})
                if row.get('type') != 'event_msg' or payload.get('type') != 'token_count':
                    continue
                value = payload['info']['last_token_usage']['total_tokens']
                if type(value) is int and value >= 0:
                    return value
            except (ValueError, TypeError, KeyError, AttributeError):
                continue
    except OSError:
        pass
    return None


def main() -> int:
    root_value = os.environ.get('OVERNIGHT_REPO')
    directory_value = os.environ.get('OVERNIGHT_INVOCATION')
    nonce = os.environ.get('OVERNIGHT_NONCE')
    if not root_value or not directory_value or not nonce:
        return 0  # Ordinary interactive Codex sessions are unaffected.

    root = Path(root_value).resolve()
    directory = Path(directory_value).resolve()
    if not directory.is_relative_to(root / '.overnight' / 'runs') or not directory.is_dir():
        return 0
    event = json.load(sys.stdin)
    cwd = Path(event.get('cwd', '')).resolve()
    if cwd != root:
        return 0
    name = event.get('hook_event_name', '')
    record = {key: event.get(key) for key in (
        'hook_event_name', 'session_id', 'turn_id', 'model',
        'cwd', 'transcript_path', 'trigger', 'source')}
    record.update(nonce=nonce, time=time.time())

    if name == 'SessionStart':
        atomic_json(directory / 'started.json', record)
        if event.get('source') == 'compact':
            atomic_json(directory / 'unexpected_compaction.json', record)
            print(json.dumps({'continue': False, 'stopReason': 'Unexpected compaction; stop for review.'}))
        return 0

    # Ignore subagent events or stale metadata. The runner disables multi_agent too.
    try:
        started = json.loads((directory / 'started.json').read_text())
        if started.get('session_id') != event.get('session_id') or started.get('nonce') != nonce:
            return 0
    except (OSError, ValueError):
        # A PreCompact stop is still safer than proceeding without its receipt.
        if name not in ('PreCompact', 'PostCompact'):
            return 0

    if name in ('PreCompact', 'PostCompact'):
        filename = 'rollover.json' if name == 'PreCompact' else 'unexpected_compaction.json'
        atomic_json(directory / filename, record)
        print(json.dumps({'continue': False, 'stopReason': 'Overnight supervisor: end this thread at the context boundary.'}))
        return 0

    if name == 'PostToolUse':
        tokens = last_context_tokens(Path(event['transcript_path'])) if event.get('transcript_path') else None
        with (directory / 'counter.lock').open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            counter_path = directory / 'telemetry.json'
            try:
                old = json.loads(counter_path.read_text())
            except (OSError, ValueError):
                old = {}
            calls = int(old.get('completed_local_tool_calls', 0)) + 1
            threshold = int(os.environ.get('OVERNIGHT_SOFT_TOKENS', '140000'))
            # Counts remind the worker to retain state; they never force a rollover.
            due = (tokens is not None and tokens >= threshold) or calls >= 80
            last_nudge = int(old.get('last_nudge_call', 0))
            nudge = due and (last_nudge == 0 or calls - last_nudge >= 8)
            record.update(completed_local_tool_calls=calls, approximate_last_request_tokens=tokens,
                          last_nudge_call=calls if nudge else last_nudge)
            atomic_json(counter_path, record)
        if nudge:
            reason = f'approximately {tokens} tokens in the latest recorded request' if tokens is not None and tokens >= threshold else f'{calls} completed local tool calls'
            target = int(os.environ.get('OVERNIGHT_TARGET_TOKENS', '260000'))
            print(json.dumps({'hookSpecificOutput': {
                'hookEventName': 'PostToolUse',
                'additionalContext': (
                    f'Advisory overnight checkpoint reminder ({reason}). '
                    'Refresh .overnight/STATE.md with exact obligations, evidence, jobs and next action. '
                    'Choose a handoff when the next task will mostly not need the current context. '
                    f'About {target:,} tokens is a planning target, not a deadline. '
                    'Keep working while this context is useful; a reminder or tool count alone is not a reason to end. '
                    'When ready for rollover, return final JSON with status continue and a concrete handoff. '
                    'The supervisor will start the next fresh context automatically. '
                    'This reminder is operational bookkeeping, not semantic evidence.'
                )}}))
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except Exception as error:
        # Never silently permit compaction after a critical hook error.
        print(json.dumps({'continue': False, 'stopReason': f'Overnight hook error: {type(error).__name__}: {error}'}))
        raise SystemExit(0)
