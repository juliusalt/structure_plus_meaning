---
name: transcript-bash-results-stripped
description: Claude Code stores Bash tool results in session transcripts with trailing newlines removed; exact-match checks must strip
metadata:
  type: project
---

Verified 2026-09-18 on this machine: 0 of 47 Bash tool results in a session transcript kept the final newline their commands printed. Any check that searches a transcript for exact emitted text (for example `base_pack.py check-load`, which looked for chunk envelopes ending in "\n") must compare without trailing newlines, and its tests must store tool results the same way.

**Why:** the packed-base loader's check-load refused a faithful transcript 0/75 while its own tests, which stored the exact envelope, passed.

**How to apply:** when verifying loads or outputs from transcripts, rstrip both sides; build test fixtures from real transcript records. Related: [[fable-knowledge-base-orchestrator]].
