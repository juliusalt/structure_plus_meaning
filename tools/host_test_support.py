"""What the host tests share: waiting for an event a child process or a file makes observable.

A test that needs a child to exist, a file to appear or a process to stop waits for that event,
polling it, rather than sleeping a fixed time or bounding its wait by how fast the machine happens
to be. The bound is generous: it is reached only when the event never comes, and the failure then
names what was waited for. A test that measures a bound itself states that bound, not this one."""
from __future__ import annotations

from pathlib import Path
import time

GENEROUS = 120


def wait_for(condition, what, timeout=GENEROUS, interval=0.01):
    """Poll condition until it returns a true value, and return that value.

    Past timeout seconds the wait fails with an AssertionError naming what it waited for."""
    deadline = time.monotonic() + timeout
    while True:
        value = condition()
        if value:
            return value
        if time.monotonic() >= deadline:
            raise AssertionError(f"waited {timeout} s for {what}, which did not come")
        time.sleep(interval)


def process_stopped(pid):
    """A process has stopped when it no longer exists or has exited and is awaiting its reaper."""
    try:
        return Path(f"/proc/{pid}/stat").read_text().split()[2] == "Z"
    except FileNotFoundError:
        return True
