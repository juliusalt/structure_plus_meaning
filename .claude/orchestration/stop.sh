#!/bin/sh
# Stop everything: the daemon first (its watchdog would restart what is stopped), then the implementer, then
# the check and build processes it left running. The sealed base and all state stay; start.sh resumes.
HERE=$(cd "$(dirname "$0")" && pwd); STATE="${ORCH_STATE_DIR:-$HERE/state}"; mkdir -p "$STATE"
date +%Y-%m-%dT%H:%M:%S > "$STATE/stopped"
p=$(cat "$STATE/warm.pid" 2>/dev/null); [ -n "$p" ] && kill "$p" 2>/dev/null; rm -f "$STATE/warm.pid"; echo "daemon stopped"
cur=$(cat "$STATE/current-impl" 2>/dev/null)
if [ -n "$cur" ]; then
  set -- $("$HERE/session_row.py" "$cur")
  if [ "${1:-}" = background ]; then
    pid=$(claude agents --json | python3 -c "import json,sys; print(next((r.get('pid') for r in json.load(sys.stdin) if r.get('name')=='$cur'), ''))")
    claude stop "$2" >/dev/null 2>&1; echo "stopped $cur ($2); HANDOFF.md was last written $(date -r "$HERE/../../HANDOFF.md" +%H:%M:%S)"
  else echo "$cur is not a live background session"; fi
fi
sleep 2
# what the implementer launched in the background outlives it as orphans: this project's python tools and
# the Isabelle, java and poly processes under them
python3 - "$(cd "$HERE/../.." && pwd)" <<'PY'
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
time.sleep(4)
for q in victims:
    try: os.kill(q, signal.SIGKILL)
    except OSError: pass
print(f"stopped {len(roots)} leftover tool runs ({len(victims)} processes)")
PY
left=$(ps -eo comm | grep -c -x -e poly -e java); echo "poly/java processes still running on this machine: $left"
