# Complete incremental environment updates

The index represents every original artifact and binding, including all values
of conflicting rows. Use words retain arbitrary natural coordinates; `None`
and a present empty word have distinct paths. Separate outer and inner paths
represent binding keys. Complete entry enumeration and exact path decoding
recover the whole original environment.

The abstract store type carries original environment formation. Initialization
checks the complete original rows once. Artifact insertion checks the new value
and its empty use; binding insertion checks the actual source slot, existing
target and unbound slot. Each operation preserves the invariant without checking
the whole old environment again. Independent all-input equations identify both
the typed API and the complete raw guard with the original guarded constructor.

Eleven actual methods run on sixteen complete subjects. Computed soundness and
completeness select the typed API and complete raw guard. Omitting old formation,
freshness, new formation, target presence, source-slot presence or unboundness
has a separate counterexample. Refusal and returning the old environment also
fail. Complete output equality retains every artifact and binding.

Three persistent chains initialize once and perform 0, 32 or 128 successive
insertions. Their complete views contain 1, 33 and 129 artifacts. The same
original lookup returns the same artifact in two structural path steps. This
count does not measure index preparation, artifact equality, complete-view
observation or the whole physical cost of a development decision.

```sh
python3 -B tools/reconstruct_environment_updates.py \
  --poly /opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly \
  --output /tmp/environment-updates-reconstruction
```

All forty reports reproduce full subjects, original and candidate outputs,
conditions, comparison and revision reasons, and complete chain results.
Adoption by the generation store, fresh allocation, complete workflow policy,
historical permission, full physical cost and genesis remain open.
