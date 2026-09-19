#!/bin/sh
# Stop everything: the daemon first (its watchdog would restart what is stopped), then every role (v2.py stop: the
# planner, the producing worker and the kept ones; the orchestration becomes inactive, and the next planner is told
# what was interrupted), then the check and build processes they left running. The sealed bases and all state stay;
# start.sh resumes.
HERE=$(cd "$(dirname "$0")" && pwd); PROJECT=${ORCH_PROJECT:-$(cd "$HERE/../.." && pwd)}; STATE="${ORCH_STATE_DIR:-$HERE/state}"
mkdir -p "$STATE"
date +%Y-%m-%dT%H:%M:%S > "$STATE/stopped"
p=$(cat "$STATE/warm.pid" 2>/dev/null); [ -n "$p" ] && kill "$p" 2>/dev/null; rm -f "$STATE/warm.pid"; echo "daemon stopped"
"$HERE/v2.py" stop
echo "HANDOFF.md was last written $(date -r "$PROJECT/HANDOFF.md" +%H:%M:%S 2>/dev/null || echo never)"
sleep "${ORCH_PAUSE:-2}"
# what the sessions launched in the background outlives them as orphans: this project's python tools and the
# Isabelle, java and poly processes under them (a finalizer, under .claude/orchestration, finishes its task)
python3 - "$PROJECT" <<'PY'
import os, signal, sys, time
root = sys.argv[1]
procs = {}
for pid in filter(str.isdigit, os.listdir("/proc")):
    try:
        args = open(f"/proc/{pid}/cmdline", "rb").read().decode(errors="ignore").replace("\0", " ")
        cwd = os.readlink(f"/proc/{pid}/cwd")
        ppid = int(open(f"/proc/{pid}/stat").read().rsplit(")", 1)[1].split()[1])
    except OSError:
        continue
    procs[int(pid)] = (ppid, args, cwd)
roots = [p for p, (pp, a, c) in procs.items() if "python" in a.split(" ")[0] and "tools/" in a and c.startswith(root) and "orchestration" not in a]
def tree(p):
    out = [p]
    for q, (pp, _, _) in procs.items():
        if pp == p:
            out += tree(q)
    return out
victims = sorted({q for r in roots for q in tree(r)})
for q in victims:
    try: os.kill(q, signal.SIGTERM)
    except OSError: pass
time.sleep(4 if victims else 0)
for q in victims:
    try: os.kill(q, signal.SIGKILL)
    except OSError: pass
print(f"stopped {len(roots)} leftover tool runs ({len(victims)} processes)")
PY
left=$(ps -eo comm | grep -c -x -e poly -e java); echo "poly/java processes still running on this machine: $left"
