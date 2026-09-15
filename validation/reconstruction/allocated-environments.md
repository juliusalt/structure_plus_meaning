# Allocation states and actual insertion paths

The closed allocation store carries original environment formation and a strict
head bound for every original use. Loading computes the bound from complete
source rows. Later allocation reserves `Some [next_head]`, checks the new
artifact, updates the same persistent store and advances the bound. Binding
updates retain all original local prerequisites and leave the head unchanged.
The actual operations do not reconstruct the whole view or scan old rows.

Independent original environment guards and constructors determine the complete
result. All-input theorems relate the typed operations to that whole original
boundary, including the returned head. An unavailable prepared input has no
result row; a rejected operation on a prepared input has an explicit absent
result row. Complete relation comparison preserves this distinction.

Twelve methods run on sixteen actual prepared states and requested operations.
The typed API and original finite reference are selected and adequate. Controls
omit the head increment, skip artifact formation, reset the bound, change the
allocated use, skip binding prerequisites, remove results, add an absent result,
conflate unavailable input, keep the old state or reject. Actual typed chains
retain 1, 33 and 129 artifacts after zero, 32 and 128 allocations. The original
payload at `None` still takes two structural lookup positions.

Criticism of that fixed lookup adds the actual next insertion path. A reusable
counted relation insertion equals the original complete insertion and counts
both its bucket lookup and update. They each visit 4, 36 and 132 positions in
those three chains. The current unary component encoding has length n+1, so
local state maintenance and one-coordinate words do not settle physical cost.
The extended reports retain every original report as an exact projection; all
forty complete previous projections were directly compared after execution.

```sh
python3 -B tools/reconstruct_allocated_environments.py \
  --poly /opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly \
  --output /tmp/allocated-environments-reconstruction
```

All forty reports retain complete subjects, results, conditions, comparison and
revision reasons, and both original and extended chain observations. Shorter
exact path encoding, generic encoded stores, whole graft and generation-store
adoption, complete historical permission and workflow enforcement, full physical
cost, native mathematical-proof admission and genesis remain open.
