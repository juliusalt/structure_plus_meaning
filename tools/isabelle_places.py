"""Where the proof base lives: the Isabelle heap store, the active-context pointer and the fallback base; and where
Isabelle itself lives: its distribution's home, the Poly/ML it runs and the directory of the store its heaps are in.

Each is named here once, and every tool that spawns Isabelle or reads the base takes them from here.
They lie under the repository's `.build/tasks/base-lasting/`: a place that outlives a reboot of the machine,
that every session's sandbox and the finalizer write, and that no task's cleanup removes. A task's tree is a
git worktree inside the repository, so the place is found from the nearest directory above this file that
holds a `.git` directory, and every tree names the same place as the repository it belongs to.
"""
from pathlib import Path


def repository(start):
    for directory in start.parents:
        if (directory / '.git').is_dir():
            return directory
    return start.parents[1]


LASTING = repository(Path(__file__).resolve()) / '.build' / 'tasks' / 'base-lasting'
USER_HOME = LASTING / 'isabelle-home'
ACTIVE_CONTEXT = LASTING / 'active-context.json'
FALLBACK_BASE = LASTING / 'accepted'

ISABELLE_HOME = Path('/opt/isabelle')
POLY = ISABELLE_HOME / 'contrib/polyml-5.9.2-2/x86_64_32-linux/poly'
HEAPS = USER_HOME / '.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64_32-linux'

# The heap store's former place. A context recorded by the tools of before this module names its heap and
# database there; while a link stands at that place such a path and one under USER_HOME name the same file.
FORMER_USER_HOME = Path('/tmp/structural-isabelle')


def in_store(path):
    """A recorded heap or database path, placed in the current store: the store is where a heap lives, not what
    it is, so a path recorded under the former store and one under USER_HOME name the same stored file."""
    path = Path(path)
    for home in (USER_HOME, FORMER_USER_HOME):
        if path.is_relative_to(home):
            return str(USER_HOME / path.relative_to(home))
    return str(path)


def stored_in_store(stored):
    """A recorded heap-and-database identity with its paths placed in the current store."""
    return {key: in_store(value) if key in ('heap', 'database') else value for key, value in stored.items()}
