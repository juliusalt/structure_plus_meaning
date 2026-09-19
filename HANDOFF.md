# Handoff — impl-18 working: B9 COMMITTED+PUSHED; B10 (development-layer residual record) in design

## CURRENT STATE (impl-18, read first)

- ACTIVE BASE: `.build/check-20260919s/proof` (B9's check, adopted). Confirming check `.build/check-20260919t`
  ACCEPTED (no rebuild, 50 recipes re-executed all words equal, 171+35 tests) and RETAINED. Replay
  `.build/impl17/replay-b`: 13 reconstructed, walk adopted, none differing. B9 plan section "A question's
  comparison is asked through indexes and its wrapper by insertion — 2026-09-19" and its REASONING_REUSE
  section appended; COMMITTED+PUSHED ("Ask a question's comparison through indexes and wrap its program by
  insertion").
- B10 MEASURED (probe `.build/probe-impl17-m`, theory `.build/impl17/layer/Probe_Development_Layer.thy`): the
  loop closure of the machinery's 14 roots restricted to the 102 theories added since c4dfad1 = 409 constants;
  state 820 names, 1,381 entities, 3.0M HOL nodes; define 24.9 s; code_reflect compile + counts + selection
  392 s; 362 residual problems (definition reading), 313 depend on another, 49 ready = 49 selected.
  Type sizes (probe `.build/probe-impl18-a`, theory `.build/impl18/typesize/Probe_Type_Sizes.thy`,
  constructor counts): layer full 226,238, terms without types 33,432, types at constant occurrences 162,828,
  other types 19,604; typargs instead of occurrence types 116,685; distinct-type table 128,099 (2,869 types);
  hash-consed type DAG 66,494 (6,124 nodes). Machinery (14 roots): full 23,311, skeleton 1,870, DAG 4,439.
- RUNNING: probe `.build/probe-impl18-b` (theory `.build/impl18/compile/Probe_Compile_Cost.thy`): compile cost
  per node kind (20,000 numerals / type constructors / zeros / units) to attribute the 392 s (numerals vs
  constructors vs codegen vs ML compile). Output `.build/impl18/probe-b.out`, log `.build/probe-impl18-b/probe.log`.
- Scratch to remove: `.build/probe-impl17-*`, `.build/probe-impl16-*`, `.build/impl16/solo`, `.build/impl15`,
  checks q/r (keep s, t and s's lineage).

## impl-17 session (2026-09-19)

- B7(b) COMMITTED+PUSHED a785747 ("Ask an artifact through its reading when syntax is read back").
- B7(a)+(c) INSTALLED AND VALIDATED, UNCOMMITTED: staging `.build/impl17/ac/` (impl-16's staging + fixed proof step,
  corrected readiness text, `workflow_stage_requests_demanded`/`workflow_stage_demand_ready`, and Keyed_Native_Evaluation's
  three keyed code equations over the demanded calls, which impl-16's staging had missed) copied into theories/;
  ROOT (Finite_Binary_Values, Factor_Demanded_Program_Calls), THEORY_MAP rows (installer misplaced the Workflow_Stage row
  into Workflow_Execution's: repaired). Check `.build/check-20260919q --advance-base`: 275 theories 212 s accepted; 5
  storage recipes words equal; 6 native-question recipes changed ONLY question-packet words (all stages exit 0; seed
  succession/publication words equal) -> re-recorded; `adopt --proof .build/check-20260919q/proof` (ACTIVE BASE: q);
  confirming check `.build/check-20260919r` ACCEPTED (11 recipes equal, 171+35 tests) and RETAINED.
  Replay --rerecord (`.build/impl17/replay-a`): 13 reconstructed with every word equal, walk adopted, none differing.
  Plan section "A native question evaluates what its requests demand — 2026-09-19" and REASONING_REUSE section appended;
  COMMITTED+PUSHED ("Present question candidates in binary and evaluate only what a stage's requests demand").
- B7(a)+(c) COMMITTED+PUSHED 83225db ("Present question candidates in binary and evaluate only what a stage's requests demand").
- B9 INSTALLED (theories/: Ordered_Member_Trees `ordered_member_tree_listed`; Finite_Investigation_Execution_Sharing and
  Finite_Investigation_Basis_Sharing indexed relation/rows + `investigation_loss_order`/`investigation_select_loss_order`;
  Factor_Invariant_Evaluation_Sharing listed residual/conflicts/available repairs (`[code abstract]`); NEW
  RRA_Inserted_Attachments (attach unions with operands exchanged); ROOT, NER import, THEORY_MAP rows). Staging and install
  script `.build/impl17/b9/`. Proofs checked by probe `.build/probe-impl17-k` (renamed copies). RUNNING: check
  `.build/check-20260919s --advance-base` (proof accepted 3:18; recipes executing; ALL words must be equal — pure
  refinements). Then: adopt, confirming check, retain, replay; docs drafts `.build/impl17/rr-b9.md`,
  `.build/impl17/plan-b9-draft.md` (fill EVIDENCE/OPEN); commit+push.
- B9 MEASURED (probe `.build/impl17/b9all`, all three fixes): question construct 0.21/0.87/5.3/64.6 s at 64/128/256/512
  (68.6 at 256 before B9); at 256: ground source 0.115 s (9.1), revise 0.69 (70.7), compare 0.017 (1.75), review 0.37,
  generation 2.5, observations 1.8. At 512: generation 24.8, observations 18.2, review 17.5, revise 5.2 s (package
  read-back ~n^2.5 and the review's per-call search of its whole input remain).
- EXPORT MEASURED (probe `.build/impl17/export`): context nodes 338K/925K/2.3M/6.0M/13.1M at 100/200/400/800/1535 closure
  constants (every constant occurrence carries its whole translated type: ~160x the kernel+code term size); items and
  certification linear (certify 5.1 s at 13.1M); `Local_Theory.define` of the full closure did not finish in 413 s.
  A type table (types as positions, like names) would make state size linear: needed if states grow past ~1,000 constants.
- NEXT (B10, provisional residual choice): residual record over the development layer = the loop closure's constants
  declared in the 102 theories added since the plan's accepted base c4dfad1 (`.build/impl17/root-c4dfad1.txt` vs
  `root-now.txt`); measure its size and export cost first; owner question to add (scope of the record).

## impl-16 session (2026-09-19) — parked at the context limit; its B7(b) committed by impl-17

- ACTIVE BASE: `.build/check-20260919p/proof` (check p ACCEPTED with --advance-base and RETAINED: 153 theories 208.2 s,
  37 recipes re-executed with EVERY word equal, 171+35 tests). Nothing runs. Nothing committed this session.
- B7(b) DONE, VALIDATED, UNCOMMITTED: `theories/Factor_Indexed_Readings.thy` (readings over the SET of artifact readings at
  a use, exact for every environment, code equations only for the `_formed` readers = seed frontier constants; the
  guarded entries = 7 of the seed's 10 roots keep their code, so the seed state is unchanged), ROOT, NER import,
  THEORY_MAP row, REASONING_REUSE section (final text). impl-15's first version (entries' code replaced) failed check o on
  all 11 seed words (would answer 7 seeded problems outside the loop) and was removed.
  TO COMMIT (successor, first): append `.build/impl16/plan-b7b-draft.md` to native_control_plan.md, replacing the word
  SOLO by: "Run alone after the check, recipes whose check times had grown under the load of 37 concurrent executions ran
  faster than their retained times: digit replay 7.7 s (13.4 retained), quoted history 8.7 s (13.9), the machinery
  recipe 15.8 s summed (27.1) and the seed recipe 186.9 s summed (216.7)." Then commit (existing style, NO attribution)
  and `git push origin main`. Check comparison (in check p vs retained, under load): 33 of 37 slower, e.g. seed stage sum
  216.7->343.8, digit replay 13.4->25.0, machinery 27.1->49.8 — all explained by load per the solo runs above.
- MEASURED (reworked candidate): package read 0.006/0.020/0.086/0.322 s at 16/32/64/128 rows (was 0.031/0.287/3.766 at
  16-64); whole native question (binary candidates) construct 0.12/0.29/1.02/4.41/27.7 s, admission 0.15/0.36/1.31/5.92/
  42.6 s at 8..128; unary indices construct 0.33/2.74/38.2 s at 8/16/32 (review input 10x larger). Scope review
  attribution (probe `.build/probe-impl16-e`, theory `.build/impl16/review/`): at 64 candidates the term demand has 4,960
  calls, evaluation 3.93 s, certificates 3.67 s; the DEMANDED calls are 1 call, 0.012 s evaluation, same answers.
- NEXT BATCH B7(a)+(c), STAGED in `.build/impl16/ac/` (+ `install.py` copies them into theories/ and edits ROOT and
  THEORY_MAP): Finite_Binary_Values (new), Finite_Presented_Coordinates, Factor_Finite_Development_Questions (binary
  `finite_development_index`), Factor_Demanded_Program_Calls (new; STALE copy — take the current one from
  `.build/impl16/c7/`), Factor_Workflow_{Stage,Reference,Evidence_Meaning,Execution_Sharing} (stage demand =
  `workflow_stage_demand` = `finite_program_demanded_calls`). Probe of the C7-renamed chain passed before the readiness
  lemmas were added. ONE FAILING STEP in `.build/impl16/c7/Factor_Demanded_Program_Calls.thy` line ~113
  (`finite_program_demanded_calls_closed`, the `edge` proof): goal `e ∈ snd ` fset H` from `called: e |∈| fimage snd H`
  -> add `fimage.rep_eq` (or use `called[unfolded fimage.rep_eq]`) to the simp list. Probe:
  `python3 -B tools/probe_theories.py --work .build/probe-impl16-j --candidates .build/impl16/c7 --theory
  Factor_Demanded_Program_Calls --parallel-proofs 0 --timeout 240`. Then add to Factor_Workflow_Stage (c7/real + ac):
  `workflow_stage_requests_demanded` (requests ⊆ term demand when entry ∈ defs, via finite_program_term_demand_root) and
  `workflow_stage_demand_ready` (from `finite_program_demanded_calls_ready`), regenerate `.build/impl16/c7/probe/C7_*`
  (renaming script in this session: prefix C7_, strip `export_code ... checking SML`) and re-probe the chain; copy c7 into
  ac; run install.py; write REASONING_REUSE section; `incremental_check.py check --advance-base --output
  .build/check-20260919q`: native-question recipe words WILL change (index presentation, stage D/A/T): verify all stages
  exit 0, re-record with `.build/impl14/record_words.py CHECK RECIPE`, `adopt --proof`, confirming check, retain, replay
  retained answers `--rerecord`, plan section, commit+push. ~272 theories rebuild.
- Scratch to remove after commit: `.build/probe-impl16-{b,d,e,g,h,i,j}`, `.build/impl16/solo`, `.build/impl15`.

## impl-15 session (2026-09-19)

- ACTIVE BASE unchanged: `.build/check-20260919m/proof`. Nothing committed yet this session; scratch in `.build/impl15/`.
- B7 MEASURED with a carrier-size fix (candidate `.build/impl15/cand/Ordered_Finite_Cardinality.thy`: code_unfold
  `fcard (A::'a::linorder fset)=length (sorted_list_of_fset A)`; probes `.build/probe-impl15-{a,b,c}`): the fuel
  `fcard (finite_carrier ..)` of every pattern/term reading was the remdups; with the fix the package read at
  16/32/64/128/256 payload rows costs source 0.019/0.128/0.808/6.32/51.9 s (was 0.031/0.287/3.766 at 16/32/64):
  still ~n^3. Profile at 128 rows: equal_lista+filtera ~85% = whole-artifact scans per node
  (`finite_headed_incidence`, `finite_payload_values`, `finite_basis_slice`, carrier membership), ~40-80 scans per
  clause; sorting for fcard ~12%. Stage probe (unary indices): construct 25.3 s at 24 candidates, 99.6 s at 32;
  selection 32 candidates 225 s. Three separate factors: (b) per-node artifact scans in the formed readers
  (dominant), (a) unary development indices (`finite_development_index` = unary `natural_data_term`; source O(n^2);
  the existing binary notion is `finite_binary_natural_value` in Finite_Presented_Coordinates, one payload leaf),
  (c) the scope review evaluates the whole question as data (term demand over all components).
- B7 DESIGN (being implemented): an artifact reading record (heads, values, counted, member, size) with the
  scanning reading of an artifact and an indexed reading built once (reusing the walk answer's index lemmas
  `indexed_heads_exact`, `indexed_values_exact`, `indexed_counted_exact`, `finite_payload_at_read`,
  `finite_slice_empty_read` from Development_Answer_0ccf746fe2cf), proved equal; the lowest syntax bodies stated
  once over a reading (instances = the existing functions); the formed reader family
  (Factor_Formation_Once_Readings/Definitions) converted in place to take the reading of the one artifact at the
  read use (formed environments hold at most one artifact per use), built once per entry. Then (a) binary indices
  (words change: re-record), then measure (c).
- B7(b) CANDIDATE WRITTEN, ALMOST PROVED (parked by impl-15 at the context limit; nothing in theories/ changed):
  `.build/impl15/cand2/Factor_Indexed_Readings.thy` (reading record, scanned/indexed readings + equality,
  bodies over a reading with `_scanned` instance lemmas, use-level readings over `A :: artifact_reading option`
  with `_exact` lemmas stated for any `A` with `artifact_reading_at E u=A`, code equations replacing the
  formed-once/demanded ones). Probe: `python3 -B tools/probe_theories.py --work .build/probe-impl15-d --candidates
  .build/impl15/cand2 --candidates .build/impl15/parts2 --theory Probe_Indexed_Parts --timeout 380` (forked proofs
  collect all errors; log `.build/probe-impl15-d/probe.log`, grep `Failed to finish`). ONLY TWO PROOFS FAIL:
  `read_schema_readings_exact` and `read_scoped_pattern_readings_exact` (Some branch: the body/scoped lemma was
  instantiated with the abstract A, the goal has `Some (scanned C)`): add `read_schema_body_readings_exact[OF formed]`
  resp. `read_scoped_record_exact[OF formed]` and `reading` to the final `simp_all only` (premise
  `artifact_reading_at E u=Some ..` then discharges via reading + case premise). MEASURED (code loads even with
  the failing proofs): package source read 0.006/0.019/0.070/0.327 s at 16/32/64/128 payload rows (was
  0.031/0.287/3.766/- ; with only the fcard fix 0.019/0.128/0.808/6.32); remaining ~n^2 is environment formation
  (O(A^2), 0.104 s at 3117 addresses) and root family; package read repeats its traversal ~3x (sites, formed,
  graph) - one-traversal code equation for `finite_native_package_readings` is a follow-up.
- NEXT (in order): (1) fix the two proofs, confirm `loaded: true` with `--parallel-proofs 0`; run the stage probe
  `.build/impl15/stages2/Probe_Indexed_Stages.thy` (binary-presented candidates, 8..128) as its own probe dir to
  measure the whole question; (2) integrate: copy Factor_Indexed_Readings into theories/, ROOT (after
  Factor_Demanded_Package_Readings / Development_Answer_0ccf746fe2cf), import it in Native_Execution_Refinements,
  THEORY_MAP row, REASONING_REUSE section, plan section; `incremental_check.py check --advance-base --output
  .build/check-20260919o` (every recipe re-executes; ALL words must be equal), adopt, confirm, retain, commit+push;
  (3) B7(a) binary indices prepared in `.build/impl15/binary/` (new theories/Finite_Binary_Values.thy, edited
  Finite_Presented_Coordinates.thy and Factor_Finite_Development_Questions.thy; ROOT entry needed near
  Natural_Binary_Digits): apply after (2) validates; words of every recipe presenting native questions change ->
  re-record with `.build/impl14/record_words.py CHECK RECIPE`, replay retained answers `--rerecord`; (4) measure (c)
  the scope review; (5) then task 3 (residual record over the whole development layer).
- The fcard code_unfold candidate (`.build/impl15/cand/Ordered_Finite_Cardinality.thy`) is superseded by the
  reading's size field (computed once per reading); do not integrate it unless a measurement asks for it.
- Probe dirs `.build/probe-impl15-{a,b,c}` can be removed; keep `-d`. Nothing runs.

## impl-14 session (2026-09-19)

- G1 FINISHED: confirming replay `.build/impl13/replay-b` gave {"replayed": 14, "reconstructed": 13, "adopted":
  ["indexed-data-walk"], "differing": []}; plan section "The loop's decisions are admitted generations — 2026-09-19"
  appended; committed and pushed as "Admit the loop's decisions as generations and record them with known readings".
  ACTIVE BASE: `.build/check-20260919k/proof`.
- B6 WRITTEN (uncommitted): NEW theories/Development_Constant_Problems.thy (problem of a constant over (reading, kind):
  scope, statements, stated constant, contract, question, contract packets, problem, mentions, premises, dependencies,
  problems, unstated + contracts); Development_Refinement_Contracts = code-equation instance only; isabelle_definition_
  proposition moved to Isabelle_Code_Equations; development_refinement_scope renamed development_constant_scope
  (Requests, Successor); Repair's definition problems = constant problems under the definition reading (contract = the
  constant as declared); Requests: development_selection_packet / development_packet_selected(_ready) (3rd use), used by
  Seed_Loop; NEW theories/Development_Machinery.thy (14 roots, residual problems, dependencies, contract packets,
  selection, problem/loop reports) and Native_Development_Machinery.thy; ROOT; NEW recipe
  tools/reconstruct_native_development_machinery.py with placeholder validation/reconstruction/native-development-
  machinery-reports.json (all null); THEORY_MAP rows; REASONING_REUSE section; plan draft `.build/impl14/plan-b6-draft.md`.
- B6 VALIDATED: check `.build/check-20260919m --advance-base` (19 theories 44.9 s; seed words all equal 162.6 s;
  machinery recipe failed only on null words) -> words recorded (`.build/impl14/record_words.py CHECK RECIPE`), `adopt
  --proof .build/check-20260919m/proof` (ACTIVE BASE: check m), confirming check `.build/check-20260919n` ACCEPTED and
  RETAINED (171+35 tests). Probe of the state: 150 names, 121 entities, 51 frontier, 14 residuals, none unstated,
  3 dependencies, 11 ready = 11 selected (6.6 s). Plan draft `.build/impl14/plan-b6-draft.md` (only REPLAY left),
  commit message `.build/impl14/commit-b6.txt` (REPLAY left).
- Replay --rerecord: 12 reconstructed, walk adopted, introduced-helper re-recorded (verdict word only: its repair's
  definition problem carries the helper as declared). Plan section "The loop's notions are native residual problems —
  2026-09-19" appended; B6 COMMITTED+PUSHED ("Pose the loop's own notions as native residual problems").
- NEXT BATCH B7 (chosen provisionally, a residual; reason: an inevitable cost on the loop's own path): the native
  selection question is steeply superlinear (probe `.build/probe-impl14-b`, theory `.build/impl14/scale/
  Probe_Selection_Scale.thy`: 1.7 s at 4 candidates, 2.5 at 8, 15.3 at 16; 32 and 64 did not finish in the probe's
  budget), so selection over the complete residual record (~330 development constants) is infeasible. Attribute per
  stage (question construction, generation, compiled conditions, observations, review input, scope review, comparison,
  revision, admission) at 4/8/16/32 with a code_reflect probe, fix at the cause as proved code equations (preferably
  as refinement answers through the loop: demanded request, answer, verdict, adoption), then extend the residual
  record to the whole development layer.
- B7 ATTRIBUTION (probes in `.build/impl14/{stages,rows,parts}/`, code_reflect; probe dirs `.build/probe-impl14-{c,d,e}`):
  stages at 4/8/16/24 candidates: generation 0.006/0.058/1.12/8.48 s, compiled conditions 0.006/0.058/1.13/8.51,
  observations 0.012/0.116/2.24/17.0, scope review 0.08/0.24/1.83/8.54 (review input 35K/101K/482K/1.38M bits),
  compare/revise ~0. All three dominant stages read an installed ground program back (`finite_native_source`).
  Rows probe: reading back a ground program of n one-octet payload rows costs 0.005/0.031/0.289/4.24 s at
  8/16/32/64 (~n^3-4 in the row COUNT), unary natural index rows 0.030/0.579/4.40 at 8/16/24 (worse: row size adds).
  Suspected cause: per-call whole-artifact scans in the syntax readers (`finite_headed_incidence` filters every
  incidence row, `finite_data_empty_on`/`finite_payload_values` every binding, per socket and per node), multiplied
  by the n clauses of one artifact. Package probe (parts: root family, definition readings/sites/graph, program,
  package formed, source) running at 16/32/64 to confirm which part dominates. Fix direction (walk answer pattern):
  syntax readers stated over artifact readers, instantiated with indexes built once per artifact
  (`Binary_Relation_Stores` by `address_binary_path`, `Ordered_Member_Trees`); indices of native questions are unary
  (`finite_development_index` = unary `natural_data_term`), a second, separate factor.
- B7 PARKED by impl-14 at the context limit (nothing running, nothing uncommitted except this HANDOFF). Package probe
  (`.build/impl14/parts/Probe_Package_Parts.thy`, 16/32/64 payload rows, artifact 237/429/813 addresses): ONE
  definition read 0.006/0.055/0.812 s; sites 0.012/0.112/1.505, graph and program the same traversal again,
  package-formed 0.018/0.172/2.252, whole source read 0.031/0.287/3.766 -> the package read repeats the same
  demanded traversal ~4-5 times (sites, graph/program, formed check): compute it ONCE (code equation for
  `finite_native_package_readings`/`finite_native_source` from one `finite_demanded_readings` result).
  TIME PROFILE of one definition read at 64 rows (`.build/impl14/profile/Probe_Package_Profile.thy`; ML_Profiling
  with `Private_Output.tracing_fn` routed to writeln; parse `ML_profiling_entry name=..count=..` from the log):
  remdups 691 of 878 ticks, equal_lista 96, filtera 72. HOL-Library FSet executes finite sets as lists via
  `code_unfold` of `fimage/ffilter/sup_fset/fset_of_list .rep_eq`, so `ffUnion (fimage ..)` builds lists that keep
  duplicates, and cardinality/equality/singleton tests dedupe them quadratically with deep equality. NEXT: find
  which reader call feeds remdups (fcard in `finite_record_candidates`/`finite_singleton_option`, set equality in
  `finite_family_body_at`, `finite_socket_readings`), then give the readers deduplicated listings (ordered keys where
  a key exists, `Keyed_Finite_Sets`/`Ordered_Member_Trees`) as proved code equations; re-run the stage probe
  (`.build/impl14/stages`) and the selection scaling probe (`.build/impl14/scale`) to measure. Probe dirs
  `.build/probe-impl14-{c,d,e,f}` can be removed.

## impl-13 session (2026-09-19) — parked at the context limit; G1 validated (committed by impl-14)

- G1 DONE in theories/ (answers cite only the issue; recording stated over the record constructor `_using`,
  `_with` = original instances with `_with_unfold` lemmas; chain tops execute with the known-predecessor
  constructor: `development_answer_publication_known [code]`, `development_seed_publication_from_known` used
  by `development_seed_publication_prepared`). Probe `.build/probe-impl13-a`: all proofs, seed publication
  51.4 s (149.9 without known readings, 38.0 before G1), harness publication 19.6 s.
- VALIDATED: check `.build/check-20260919k --advance-base` (6 theories 40.0 s; seed recipe failed only on the
  publication word, re-recorded 09ccf853->a4525800), `adopt --proof .build/check-20260919k/proof` (ACTIVE BASE:
  check k), confirming check `.build/check-20260919l` ACCEPTED (seed recipe 142 s) and RETAINED (171+35 tests).
  `replay_development_answers.py --rerecord`: 7 refusals/failures reconstructed, walk adopted, 6 judged answers
  re-recorded (verdict words unchanged; publication words, base/harness digests and B5's parts step changed).
- RUNNING at park: confirming replay `.build/impl13/replay-b` (pid `.build/impl13/replay-b.pid`, summary
  `.build/impl13/replay-b.out`): expect {"reconstructed": 13, "adopted": ["indexed-data-walk"], "differing": []}.
- TO FINISH G1 (in order): (1) read replay-b.out; if all reconstructed, append `.build/impl12/plan-g1-draft.md`
  (complete; its last evidence sentence claims the second replay reconstructed all six — fix if not) to
  native_control_plan.md; (2) commit with the message in `.build/impl13/commit-g1.txt` (replace the trailing
  word REPLAY by the replay result sentence; NO attribution) and `git push origin main`; (3) remove scratch:
  `.build/impl12/g1`, `.build/probe-impl13-a`, `.build/probe-impl13-b`, `.build/impl13/replay-*`,
  `.build/check-20260919l` after commit (heapless confirm check; retained in validation).
- Uncommitted edits (all part of G1): theories Development_{Publication,Certified_Generations,Decision_Generations
  (new),Admitted_Publication,Seed_Publication}.thy, ROOT, THEORY_MAP.md, REASONING_REUSE.md (G1 section incl.
  known readings), tools/reconstruct_native_development_seed.py (boundary text), validation/development-answers/
  {6 records, README.md}, validation/reconstruction/native-development-seed-*.json, validation/incremental-check.json,
  validation/reconstruction/current-verified.json, HANDOFF.md.
- OPEN, recorded in the plan draft: the seed report presents every transaction's whole successor snapshot (word
  39.6 MB, stage ~145 s; quadratic in publications; retention/condition 3); cause size ~30x payload (payload
  quoted twice) blocks recording large payloads (notion families 1K-60K addresses, probe impl13-b).
- NEXT BATCH B6 (provisional, residual choice; design `.build/impl13/b6-design.md`, probe `.build/impl13/basis/
  Probe_Machinery_State.thy` measured the loop's 8 notions as a state: 103 names, 80 entities, 0.7 s): the
  machinery's notions become native residual problems — unify definition problems (contract = the constant as
  declared, like refinement; the repair's definition problems use it, re-record retained answers), factor the
  statement reading of Development_Refinement_Contracts (code equations vs kernel definitions) at its second use,
  a machinery state rooted at the loop's notions, residual problems (origin Residual, authority Generated) with
  dependencies, readiness and the native selection, in a recipe of its own.

## impl-12 session (2026-09-19)

- B5 VALIDATED AND COMMITTED (see git log): theories/Development_Answer_Parts.thy is the final version (name-shadowing
  refusal; the equation is no longer lexed as outer syntax, which would refuse `STR ''..''` literals). Check
  `.build/check-20260919j --advance-base` ACCEPTED (1 theory, 22.8 s proof, no recipe, 171+35 tests) and RETAINED.
  ACTIVE BASE: `.build/check-20260919j/proof` (lineage j->i->h->f->e->d->c->a->...).
  Six controls (validation/development-answers/{injected-ml,escaped-equation,continued-proof,declared-attribute,
  ml-method,axiom}.json) refused at their parts in ~16 s each; replay of all 14 retained answers reconstructed 12, walk
  adopted, and failed-proof differed only because its old record named its failure `refusal`: renamed to `error`, the
  replay now compares `error` too, and a re-judgment reproduced the error. Plan section "Answers are confined to their
  declared parts — 2026-09-19" appended; owner question Q4 (agent executor) added to the ledger.
- G1 IN PROGRESS, UNCOMMITTED (impl-12 parked at the context limit). All in theories/ + ROOT:
  - Development_Publication: `development_issue_locus`, `development_selection_locus`, `development_decision_loci_distinct`,
    `development_data_target_injective`, `development_publication_admitted` (admission at an absent locus).
  - Development_Certified_Generations: `development_payload_generation_with` (+ `_fields`, `_certified`), family/incumbent/
    answer restated through it; `development_judged_generation_fields` moved here; `development_answer_citations` = rows at
    the problem's ISSUE locus only (answer cites the issue; the issue cites the incumbent: direct edges only).
  - NEW theories/Development_Decision_Generations.thy (ROOT after Certified_Generations): selection/issue payloads,
    `_generation_with`, `_fields`, `_certified`, `development_loop_decisions(_made)`, `development_recorded_issue_with`
    (returns env, answer rows [issue row], Q) + `_fields`.
  - Development_Admitted_Publication: publication = (incumbent, issue, answer, results); issue admitted then answer
    replaces incumbent; `development_answer_publication_applied` (both apply); `development_answer_published` needs both.
  - Development_Seed_Publication: rewritten (decisions once via `development_loop_decisions`; selection + issues +
    answers; prepared keys incl. decision payloads; report (S0, Sel, rows (Q,G,H,results,equal), sequential)).
  - THEORY_MAP rows, REASONING_REUSE section "The loop's decisions are admitted generations", seed recipe boundary text
    (tools/reconstruct_native_development_seed.py) are written; plan section drafted in `.build/impl12/plan-g1-draft.md`
    (fill COST-AND-EVIDENCE, fix its "answer cites incumbent and issue" to "cites the issue").
  - PROBE STATUS: renamed copies in `.build/impl12/g1/` (G1_*.thy; regenerate from theories/ with the sed-rename used in
    this session: Development_X -> G1_X for the five theories). Before the citation change all proofs LOADED and the
    executed seed publication summary was [1,10,10,10,10,21,21,10] (correct) but took 133 s vs 38 s before G1.
    Attribution (G1_Probe_Attribution.thy, code_reflect): recording in the incumbent's env re-checks env formation (1.0 s)
    and re-reads cited predecessors (incumbent cause 350,817 addresses): answer citing incumbent+issue 20.2 s vs 9.5 s.
    FIX APPLIED (not yet probed): answers cite only the issue. RUNNING: probe `.build/probe-impl12-a` (PID file
    `.build/probe-impl12-a.pid`, output `.build/probe-impl12-a.out`, log `.build/probe-impl12-a/probe.log`, grep PROBE):
    expect loaded + summary [1,10,10,10,10,21,21,10] and a lower time. If still slow: carry known predecessors with the
    library's `finite_construct_known_original_generation` (+ `finite_check_generation_included`, recording contract
    `finite_construct_generation_record_correct`) via a recorder parameter, code equations at the chain tops.
  - THEN: `incremental_check.py check --advance-base --output .build/check-20260919k`; seed recipe will fail only on the
    publication word -> re-record it in validation/reconstruction/native-development-seed-reports.json, `adopt --proof`,
    confirm check, retain; `replay_development_answers.py --rerecord` (publication words change; verdict words must not);
    append plan section; commit+push G1.
- Stage-3 remainder (agent executor confined to its packet) waits on Q4; deterministic executor + replay carry it now.

## impl-11 session (2026-09-19)

- B2 INSTALLED from `.build/impl10/b2/` (theories/Development_Certified_Generations.thy, Factor_Certificate_Policy_Readiness.thy,
  RRA_Formed_Snapshot_Transactions.thy; Probe_Seed_Publication.thy -> theories/Development_Seed_Publication.thy with the
  theory name changed back); ROOT lists RRA_Formed_Snapshot_Transactions after RRA_Finite_Transactions and
  Factor_Certificate_Policy_Readiness before Development_Certified_Generations. Probe `.build/probe-impl10-a` finished:
  loaded true (every proof checked), publication 38.0 s (was 109), publication value 55.9 s, summary 1,10,10,10,10.
- Check `.build/check-20260919f --advance-base`: proof accepted (9 theories, 39.1 s); seed recipe failed ONLY on
  presentation-publication (all ten other words equal); stage 90.9 s, word 32.6 MB (was 20.5 s, 19 MB). The new word
  `09ccf853...` is re-recorded in validation/reconstruction/native-development-seed-reports.json; `adopt --proof
  .build/check-20260919f/proof` done. ACTIVE BASE: `.build/check-20260919f/proof` (lineage f->e->d->...).
- RUNNING: confirming check `.build/check-20260919g` (PID in `.build/check-20260919g.pid`, log `.build/check-20260919g.out`).
  When accepted: `incremental_check.py retain --output .build/check-20260919g`, then COMMIT+PUSH the B2 milestone.
- Plan section "Development causes are certified under the first loop's policy — 2026-09-19" is appended (numbers filled);
  THEORY_MAP rows, REASONING_REUSE section, seed recipe boundary text were already current.
- B2 COMMITTED+PUSHED: 001113f "Certify development causes under the first loop's policy" (check g retained).
- B3 IMPLEMENTED (uncommitted): theories/Development_Admitted_Publication.thy (route `development_admitted_route`,
  `development_answer_publication(_with)`, `development_admitted_publication`, theorems `_applied` for every judge, prepared
  parallel judgments, presentation `development_answer_publication_data`, predicate `development_answer_published`; probe
  `.build/probe-impl11-c` loaded, unchanged seed answer publishes in 10.2 s, renamed in 14.9 s); `development_repair_state`
  added to Development_Refinement_Repair and used by Development_Successor's repaired successor (no inline restatement);
  ROOT, THEORY_MAP, REASONING_REUSE section "Admitted answers are published natively"; harness: second presented report
  `development_answer_publication_value` -> `publication_word`, summary field `published`; replay compares both words;
  adoption requires `published` and equal publication words; tests (10 pass); answers README.
- DONE: `.build/check-20260919h --advance-base` ACCEPTED (8 theories, 38.8 s, no recipe reached, 169+35 tests) and
  RETAINED. ACTIVE BASE: `.build/check-20260919h/proof` (lineage h->f->e->...). Replay --rerecord: every verdict word
  equal; seven judged records gained publication words; the ADOPTED walk record was restored from HEAD (its record is
  the pre-adoption admission; the replay tool now never re-records adopted answers and reports them separately).
  Control adoption of demanded-reformulated through the new gate: adopted+withdrawn (check 151 theories 170 s, 48
  recipes equal); receipt copied to validation/development-adoptions/Development_Answer_5aba3385cee9.json; READMEs and the
  plan section "Admitted answers are published natively — 2026-09-19" written.
- RUNNING: confirming replay `.build/impl11/replay-b` (no --rerecord; expect 8 reconstructed + walk adopted). When it
  reconstructs: COMMIT+PUSH B3.
- NEXT BATCH (B5, chosen provisionally, reason below): answer parts isolation (stage 3). The harness builds the answer
  theory by string concatenation, so an executor's `definitions` can carry any theory command (ML, setup, declare,
  code_printing — ML can even run shell commands during judgment), the `equation` can close its quotes and the `proof` can
  continue past its lemma. Design: a repository theory `Development_Answer_Parts` (ML) that parses the three fields with
  Isabelle's own outer syntax in the frame's keyword table and refuses anything but whitelisted theory commands
  (definition, fun, function, termination, primrec, lemma/theorem/corollary WITHOUT attributes, text/section headings) and
  whitelisted proof commands; the equation must lex as one string token and the proof as proof commands closing the
  lemma; a harness step `parts` runs it in its own small session (imports = frame imports + the parts theory) BEFORE the
  answer theory is ever processed; refusal is recorded with its reason. Open after it: base-name shadowing by introduced
  constants.
- B4 DEFERRED (criticism): the request context is already the answer's dependency reading in the development history
  (the answer record keeps E, the issue record its library reading, and request currency is computed from E); a single
  "context generation" has no natural locus (the problem's locus holds the incumbent; a locus equal to its payload
  conflates locus and payload) and no consumer until re-evaluation reads RRA predecessors instead of those records. Revisit
  together with G1 (selection/issue/scheduling recorded as certified generations, guarded by their own admission — the
  B2 family-policy pattern generalized by a guard; loci per record kind).
- B3 DESIGN (as implemented above): keep admission and selection apart as separate REPORTS — the harness's
  verdict word stays unchanged (no re-record of verdicts); a second presented report `development_answer_publication_value`
  (certified incumbent of the request state, the certified answer recorded beside it, finite_locus_publications over the
  incumbent's snapshot; repaired answers against `development_request_extension` + the reissued request) gives a
  `publication_word` and summary field `published`; the reusable composition goes into a repository theory (not the
  generated harness text); `tools/development_adoption.py adoptable()` requires published; replay/re-record adds the
  publication word to the eight retained answers.

## impl-10 session (2026-09-19)

- The listed-union fix is integrated: `theories/Listed_Set_Unions.thy`, `theories/RRA_Listed_Environment_Positions.thy`
  (ROOT after Factor_Demanded_Graph_Readings; imported by Native_Execution_Refinements), THEORY_MAP rows, REASONING_REUSE
  section "Unions computed once are listed", plan section "Certified causes pay for what they read — 2026-09-19".
  Check `.build/check-20260919e --advance-base` ACCEPTED (152 theories 200.3 s, 16 recipes re-executed all words equal,
  168+35 tests) and RETAINED. ACTIVE BASE: `.build/check-20260919e/proof` (lineage e->d->c->a->z->x->w->u->s->p->complete-n).
  Committed and pushed together with impl-9's demanded graph readings as one milestone.
- Probe b finished (both fixes, first seed family, payload 11,589): policy 0.326 s, proofs 0.336, pick 0.001, replay 1.560,
  record 3.976 (cause 350,817 addresses: the payload twice, as policy literal and as call argument), check 13.736 (reads the
  cause back), ok true; the second family (17,649) did not finish its replay before the 400 s probe timeout (load time
  unknown, not attributed).
- COMMITTED+PUSHED 7961fce "Read proof graphs on demand and list environment positions once". Base e.
- B2 (certified development causes), PARKED MID-BATCH, uncommitted. Current design (all proofs checked in probes up to the
  timing theory): scratch `.build/impl10/b2/` holds the CURRENT versions: `Development_Certified_Generations.thy`
  (judgment `development_policy_judgment` = policy -> certificate -> replay -> quote -> known-scope check, a function of
  the payload alone; recording `development_recorded_generation`; `development_certified_generation_route` proves
  judgment+recording = library `certificate_policy_record`; family key/payload judgment; incumbent/answer via a supplied
  judge `_with`), `Factor_Certificate_Policy_Readiness.thy` (NEW: readiness from the replay contract + code eq for
  certificate_policy_record), `RRA_Formed_Snapshot_Transactions.thy` (NEW: finite_transact_formed, formation carried,
  `finite_locus_publications` formed-once code), `Probe_Seed_Publication.thy` (= the new Development_Seed_Publication,
  theory name to change back; judgments prepared by parallel_computed_function; rows/publication via
  finite_locus_publications; row type now (G,H,results list,equal)), `Development_Policy_Prelude.thy` (probe only),
  `Probe_Impl10_B2.thy` (timings).
- theories/ currently holds STALE B2 copies: Development_Certified_Generations.thy (first version) and
  Development_Seed_Publication.thy (impl-9 draft) -> REPLACE with the .build/impl10/b2 versions; add
  RRA_Formed_Snapshot_Transactions (ROOT after RRA_Finite_Transactions) and Factor_Certificate_Policy_Readiness (ROOT before
  Development_Certified_Generations). Already correct in theories/: Development_Policy.thy (generalized),
  Development_Publication.thy (uncertified constructors removed, text edited). ROOT already lists
  Development_Certified_Generations. THEORY_MAP rows, REASONING_REUSE section "Development causes are certified", seed
  recipe boundary text (tools/reconstruct_native_development_seed.py) already describe the CURRENT design.
- RUNNING at park: probe `.build/probe-impl10-a` (PID 3903556; log `.build/probe-impl10-a/probe.log`, summary
  `.build/probe-impl10-a.out`): read PROBE lines judgments10 / publication / publication_value. Before the split:
  per generation policy 0.35 s, certificate 0.35, replay 1.6, record 5.3; ten incumbents parallel 13.5 s; one answer 9.8 s;
  snapshot formation 2.65 s per transaction; whole seed publication 109 s (results correct: 10 applied, 10 conflicts,
  equal payloads, 10 sequential applied). Probe code context must import Native_Execution_Refinements.
  At park the probe was still running (judged 10 in 0.000 s: "judgments10" timed only the prepared function's
  construction, since parallel_computed_function is lazy only in its keys -- read the "publication" line for the real
  cost); its background waiter was killed for low memory (60 GiB machine, 12 free), the probe itself survived.
- NEXT: fill `.build/impl10/plan-b2-draft.md` (numbers marked ~) and append it to native_control_plan.md; copy theories;
  `incremental_check.py check --advance-base --output .build/check-20260919f` (expect only the seed recipe's
  presentation-publication word to change: re-record it from the check's reconstruction.json into
  validation/reconstruction/native-development-seed-reports.json, `adopt --proof`, re-check, retain); commit+push.
- THEN B3: the answer harness's verification theory (tools/development_answer.py verification_theory) also computes the
  native publication (certified incumbent of the request state + certified answer + finite_locus_publications over it;
  for repaired answers against the extended state/reissued request), in the verdict word and summary; adoption requires
  it applied; re-record retained answers. B4: answer predecessors include the request-context generation.

## impl-9 session (2026-09-19) — parked at the context limit

- COMMITTED+PUSHED: 5ea1fbf "Address complete data quotations compactly and list their rows once" (B1 + sorted rows).
- VALIDATED, NOW COMMITTED BY impl-10 (with the listed-union fix below as one performance milestone):
  `theories/Factor_Demanded_Graph_Readings.thy` (2nd instance of Finite_Demanded_Closures: recovered proof graphs read
  nodes only at sites the root reaches; code eq `finite_recovered_graph_demanded_code`), ROOT entry, import in
  `Native_Execution_Refinements`, THEORY_MAP row, REASONING_REUSE row (+ Finite_Demanded_Closures row updated),
  `tools/probe_theories.py --candidates DIR` (probe theories from a scratch dir; never touch theories/ while a check runs).
  Check `.build/check-20260919d --advance-base` ACCEPTED (151 theories 201.9 s, 15 recipes re-executed all words equal,
  168+35 tests) and RETAINED. ACTIVE BASE: `.build/check-20260919d/proof` (lineage d->c->a->z->x->w->u->s->p->complete-n).
- NEXT FIX, PROBED, NOT INTEGRATED: `.build/impl9/listed/Listed_Set_Unions.thy` (listed_union: set xs ∪ set ys executed as
  set (xs@ys); listed_image_union with fold code) and `.build/impl9/listed/RRA_Listed_Environment_Positions.thy`
  (`[code abstract]` fset (finite_environment_positions E) = listed_image_union ...; accepted in probe-impl9-e).
  Cause: library set union inserts member by member (quadratic); environment positions were quadratic, and certificate
  replay/installation inherited it. Probe e (payload 1601/3201/6401/11601): app readiness 0.049/0.189/0.764 -> 0.002/
  0.003/0.007/0.014 s; graph installation 0.140/0.558/2.474 -> 0.005/0.010/0.025/0.056; whole certificate replay at
  11,601 addresses 13.7 -> 1.3 s. TO DO: copy both into theories/, ROOT (after Factor_Demanded_Graph_Readings), import
  RRA_Listed_Environment_Positions in Native_Execution_Refinements, THEORY_MAP rows, REASONING_REUSE rows, plan section
  "Certified causes pay for what they read — 2026-09-19" (graph reading + listed positions + evidence: replay-proves at
  101/201/401: 0.015/0.069/0.366 s universe reading; demanded graph 0.011/0.024/0.050 at 401/801/1601), then
  `incremental_check.py check --advance-base --output .build/check-20260919e` (all words equal expected), retain, COMMIT+PUSH.
- RUNNING at park (may have finished): probe `.build/probe-impl9-b` (seed chain with both fixes; log
  `.build/probe-impl9-b/probe.log`, summary `.build/probe-impl9-b.out`) — read PROBE lines: policy/proofs/pick/replay/
  record/check at 11589, incumbents10, answer1. Before the listed fix: policy 0.35 s, proofs 0.35 s, replay 13.7 s,
  record 4.0 s, check did not return in >60 s (check = finite_certified_policy_cause; its base_cause and
  judgment_readings grow ~x2.6 per doubling: 0.151/0.302/0.668/1.758 s at 401..3201 — attribute next if still slow).
- Probe b partial result at park (both fixes): PROBE policy 11589 0.326;PROBE counts single ~1;PROBE counts full 3,3,3,1,1,3;PROBE proofs 11589 0.336;PROBE pick 11589 0.001;PROBE replay 11589 1.560;PROBE record 11589 3.976;
- B2 DRAFTS (not in theories/; probe them from `.build/impl9/drafts` via --candidates): Development_Policy.thy
  (impl-8's generalization + development_policy_with_package), Development_Certified_Generations.thy (judgment =
  policy -> ONE source read with TERM DEMAND `finite_program_term_demand Q {|t|}` (the one-call demand is not closed:
  the guard calls the listing entry on the same payload) -> pick certificate -> finite_certificate_replay; recorded
  generation via finite_record_native_replay + finite_certified_policy_cause check; family generation guarded by
  set es ⊆ set (snd C); per-problem incumbents each in its OWN environment (one growing environment makes every later
  record/check pay for all earlier ones); answers recorded beside their incumbent citing it), Development_Publication.thy
  (recorded-cause constructors removed; only Development_Seed_Publication used them), Development_Seed_Publication.thy
  (incumbents computed per problem with Parallel.map inside the report, not as a load-time constant). Theorems drafted:
  _recorded_generation_certified/_listed, _family_generation_certified, _certified_incumbent_base,
  _certified_answer_accepted — none probed yet. Also update recipe boundary text in
  tools/reconstruct_native_development_seed.py (publication stage) and re-record its word after the check.
- Scratch: `.build/impl9/{candidates,cost,cost2,union,listed,drafts}`, probe dirs `.build/probe-impl9-{b,c,d,e}`.
  Tasks #1-#3 in the task list mirror this.

## impl-8 session (2026-09-19) — parked at the context limit; B1 validated, NOT committed

- Commit 78ae153 (pushed) holds everything through impl-7's batch. Owner direction (ledger + memory
  `commit-push-at-milestones`): commit and push at validated milestones, existing style, no attribution.
- B1 DONE AND VALIDATED (uncommitted): the executable complete data quotation is compact.
  `theories/Factor_Finite_Data_Syntax.thy` (compact_syntax_address from natural_binary_digits,
  data_syntax_position/_address, data_syntax_carrier interval, finite_data_syntax_at, contracts
  finite_data_syntax_domain/_sound/_exact/_complete_quotation), `Factor_Finite_Syntax_Accumulation.thy`
  (five-address finite_syntax_rows_pair; prefix pair lemmas removed), `Factor_Finite_Accumulated_Data_Syntax.thy`
  (counter-threaded rows, finite_data_syntax_accumulated_code). THEORY_MAP rows and a REASONING_REUSE
  section written. check a (`.build/check-20260919a`, 302 theories, 207.5 s) accepted every proof; 13 recipe
  words changed only by the readdressing (exit 0, same record shapes, smaller words) and were re-recorded
  in `validation/reconstruction/*-reports.json`; `adopt --proof .build/check-20260919a/proof`; check b
  (`.build/check-20260919b`) ACCEPTED and RETAINED. ACTIVE BASE: `.build/check-20260919a/proof`.
- OPEN REGRESSION, cause verified, fix designed (do this FIRST): history recipes are slower alone
  (digit-history 15.0 s, concurrent-history 19.0, history-index 14.4 vs retained 11.3/13.6/11.1). Probe
  `.build/probe-impl8-l` (theory `.build/impl8/Probe_Impl8_Sorted.thy`): the prefix construction emitted its
  rows in ascending order, so canonical listings took the linear fast path; compact rows are unordered, so
  every listing/equality sorts again (x20 at 4,000 elements: listing 0.446 vs 0.024 s sorted, equality 0.849
  vs 0.084, formation 1.077 vs 0.545). FIX: in Factor_Finite_Accumulated_Data_Syntax's code equation return
  `finite_syntax_rows_object (sorted_list_of_set (set U), sorted_list_of_set (set I), sorted_list_of_set (set B))`
  (same fsets: one lemma via set_sorted_list_of_set; add imports "HOL-Library.List_Lexorder"
  "HOL-Library.Product_Lexorder"). Then check (words unchanged expected: same fset values), measure the
  history recipes alone, write the plan section "The executable quotation is compact" (evidence above +
  this fix), and COMMIT + PUSH B1.
- NEXT BATCH B2 (drafted, not probed): certified development causes. Generalized policy ready in
  `.build/impl8/Development_Policy.thy.new` (development_policy_source_with over listed presentations,
  development_policy_with_exact; entity policy = instance via development_policy_source_listed); copy it over
  theories/Development_Policy.thy. Draft theory `.build/impl8/Probe_Certified_Causes.thy`:
  development_certified_generation xs H l rows R (policy -> native source -> program proofs -> pick
  certificate -> finite_certificate_replay -> finite_record_native_replay -> finite_certified_policy_cause),
  theorems _cause and _listed (payload target is listed), plus stage timings and a seed publication shape
  check. Design: one environment of generations; incumbents recorded first, each certified under the
  policy listing its family's compact quotation target; each answer recorded from that environment citing
  its incumbent's row, certified under the policy that lists its payload only when the verdict accepted
  it (the constructor's condition; the verdict stays in the development history record). The required
  history is NOT used: its single fixed policy and own-member predecessors do not fit per-answer evidence.
  Then Development_Publication/Seed_Publication consume certified records (compute answer records once per
  request, Parallel.map). Residuals: the per-answer listing policy (Q1), this route choice.
- Scratch: `.build/impl8/` (probe theories, transplant.py, solo runs). Nothing runs. Remove
  `.build/probe-impl8-*` and `.build/check-20260918z`-era dirs no longer in the lineage when convenient.

## impl-7 session (2026-09-18 night) — its batch was validated and committed by impl-8

The owner said "Ok write the handoff and stop" while the last probe was running. State below is exact.

- WHAT THIS BATCH DOES (impl-6's parked blocker fix, now written and almost verified): a native package
  read a definition at EVERY position of the environment (`finite_native_definition_rows` over
  `finite_environment_positions`), so reading one package cost the material beside it — the cause impl-6
  measured behind the superlinear cause read-back. Two new theories replace that by a frontier traversal:
  - `theories/Finite_Demanded_Closures.thy` (generic, reusable): `finite_site_rows`, `finite_row_successors`,
    `finite_row_edges`, `finite_rooted_sites` (the universe formulation), `finite_demanded_step` /
    `finite_demanded_readings` (while_option over (visited,frontier,rows)) and
    `finite_demanded_readings_exact`: under the premise "every site with a row lies in the universe" the
    traversal returns exactly the rooted sites and the rows there. Also `finite_edge_closure_empty`.
  - `theories/Factor_Demanded_Package_Readings.thy` (instance): `finite_definition_site_reading(_formed)`,
    `finite_definition_dependencies`, the premise proved from the existing definition grammar
    (`finite_definition_reading_position`, via `native_definition_position`), the two rewritings
    (`..._edges_row_edges`, `..._rows_at_sites`), `finite_demanded_definition_readings(_formed)` and the two
    code equations for `finite_native_definition_sites` / `finite_native_definition_graph`, guarded by one
    environment-formation check (the guard is otherwise paid at every site read).
    `Factor_Recovered_Graph_Sharing.finite_native_definition_graph_shared_code` and
    `finite_native_definition_sites_def` are `code del`-ed here.
  - `ROOT` (both theories, after `Factor_Recovered_Graph_Sharing`) and
    `theories/Native_Execution_Refinements.thy` (imports `Factor_Demanded_Package_Readings`) are updated.
- STATE OF VERIFICATION: the two theories loaded with every proof checked (probe `.build/probe-impl7-a`,
  4.2 s, `loaded: true`) BEFORE the last two edits. The last probe run failed only at
  `finite_native_definition_graph_unformed` (`ffilter P {||} = {||}` not reduced); the same failure one
  lemma earlier was fixed by `auto simp: ... fset_eq_iff ffilter.rep_eq bot_fset.rep_eq sup_fset.rep_eq`
  and that fix is now applied to the graph lemma too but NOT YET PROBED. Next command (≈50 s):
  `python3 -B tools/probe_theories.py --work .build/probe-impl7-g --theory Finite_Demanded_Closures
   --theory Factor_Demanded_Package_Readings --parallel-proofs 0 --timeout 240`
  Then THEORY_MAP.md rows are still missing (add rows for both theories and
  `Factor_Demanded_Package_Readings` to the `Native_Execution_Refinements` import list), then the full
  `incremental_check.py check --output .build/check-20260918z` (expect ~150 theories rebuilt and EVERY
  recipe re-executed because the exported module changes; every report word must stay equal — that is the
  validation of this batch), then `--advance-base` and `retain`.
- MEASURED (probes `.build/probe-impl7-b/-c/-d/-e`, synthetic payload = data list of n elements, carrier
  4n+1; old numbers from impl-6's `.build/impl6/probe-scaling.log`):
  - `finite_native_source` of a one-target ground source: 0.310 s -> 0.041 s at carrier 801; 14.1 s -> 10.4 s
    at carrier 11,601 (the size of a real seed payload). Construction (`finite_ground_source`) 28.3 -> 2.3 s.
  - The environment-size factor is gone; what remains grows with the PAYLOAD artifact alone.
  - Attribution of the remainder (probe `-c`/`-e`, carrier 3,201, 4 artifacts of 9/19/26/3,201 addresses):
    the two definition sites sit in artifacts of 26 and 19 addresses, yet one site reading costs 0.24 s —
    about 5x the whole-artifact formation check (0.048 s) — and grows 4x per doubling. So the cost is in
    carrying the literal target's whole artifact through the reading fsets (deep structural comparison in
    every fset union/dedup over readings that contain `Finite_Whole R`), not in the sites read.
    `..._readings_formed` saves only ~18% over the guarded reading. NEXT CAUSE TO FIX, if the process
    selects it: readings compared by an ordered key (`Ordered_Artifact_Comparison`, `Keyed_Finite_Sets`,
    `Complete_Value_References`) instead of by whole artifacts — or, per impl-6's design, a cause that
    quotes one data term rather than a whole-artifact target.
- Scratch parked outside `theories/`: `.build/impl7-probe-cost1.thy`, `-cost2.thy`, `-cost3.thy` (the cost
  probes; copy back into `theories/` only while probing). Probe dirs `.build/probe-impl7-a..f` can be
  removed. No job is running. ACTIVE BASE unchanged: `.build/check-20260918x/proof`.
- NOT STARTED (impl-6's designed next batch, unchanged): certify development causes under the first loop's
  policy (`development_policy_source_with`, the family policy over one quoted target, the certified
  generation route through `finite_prepare_required_history` / `finite_native_program_proofs` /
  `finite_certificate_replay` / `finite_required_history_attempt`), predecessors as the request-context
  generation, then the adoption's native transaction. Its criticism and the open owner questions Q1/Q2 are
  in impl-6's section below and in `.claude/orchestration/owner-ledger.md`.

## impl-6 session (2026-09-18 night) — in progress, nothing committed

- impl-5's publication batch is on the base: the seed recipe run on check x's export reproduced all ten
  earlier words and gave the new `presentation-publication` word (stage 20.5 s), recorded in
  `validation/reconstruction/native-development-seed-reports.json`; `.build/check-20260918x/proof` was
  adopted; `.build/check-20260918y` (no rebuild, seed recipe 19.7 s, 50 reused, 168+35 tests) accepted and
  retained. ACTIVE BASE: `.build/check-20260918x/proof` (lineage x -> w -> u -> s -> p -> complete-20260918n).
  Removed: check v, probes impl3-b/impl4-a/b/impl5-a/b/c. impl-2's probe stays in `.build/impl3-scratch/`.
- Cost observed: the seed recipe went 7.5 s -> 19.7 s wall because the publication stage alone takes ~20 s
  (others ~5-8 s). Attributed (probe below): one publication row 0.86 s, one transaction 0.40 s, the word
  2.1 s for 153,177,377 bits (~19 MB; generation targets are whole artifacts, so the report word presents
  every artifact's rows — a presentation to reconsider: the targets are complete data quotations, so their
  data terms are the smaller member of the same presentation class).
- NEXT BATCH (designed, nothing written yet): certify development causes under the first loop's policy
  (HANDOFF item 1), predecessors as the request-context generation, then the adoption's native transaction.
  Design decided (record as residuals when written): (a) generalize `Development_Policy` to
  `development_policy_source_with present xs` (ground source over any injective presentation; the entity
  policy becomes its instance) — the family policy is that constructor over the ONE item
  `Finite_Target (Finite_Whole R)`, R = the complete data quotation of the family presented with its names
  (`isabelle_local_entities`), guarded by `set es ⊆ set (snd C)` (the checked context accepted them), so a
  cause quotes one target instead of the whole state (the n×|policy| growth kb A1 flagged); (b) a certified
  generation = ground source -> `finite_prepare_required_history` -> `finite_native_program_proofs` ->
  `finite_certificate_replay` -> `finite_required_history_attempt` (record + `finite_certified_policy_cause`),
  i.e. impl-2's route with the material shared per request, predecessors as rows; (c) the answer generation's
  predecessors = {incumbent generation, request-context generation (payload = the request's least context
  presented with its names)}.
- BLOCKER MEASURED FIRST (probe `.build/impl6/Probe_Publication_Cost.thy`, log `.build/impl6/probe-scaling.log`):
  certifying ONE cause for a seed payload took policy construction 28.3 s, policy read 14.1 s, proofs 14.7 s
  (payload artifact 11,589 carrier addresses). Scaling on synthetic payloads (carrier 101/201/401/801):
  formation 0.000/0.000/0.001/0.002 s and ground-source installation 0.000/0.001/0.003/0.008 s are linear,
  but reading the installed program back (`finite_native_source`) is 0.001/0.007/0.042/0.310 s and
  `finite_prepare_required_history` 0.003/0.014/0.088/0.618 s — about x7 per doubling (~cubic).
  CAUSE FOUND: `Factor_Executable_Packages.finite_native_definition_rows` reads a definition at EVERY
  position of the environment (`finite_environment_positions E`), so every address of a literal target
  artifact is probed, each probe scanning that artifact; `finite_proof_node_rows` (recovered graphs) does the
  same. The package only needs the sites reachable from its roots.
  FIX (designed, next implementer): a generic theory `Finite_Demanded_Closures` — `finite_site_rows`,
  `finite_row_edges`, `finite_rooted_sites` (the present all-positions formulation) and a frontier traversal
  `finite_demanded_step`/`finite_demanded_readings` (while_option over (visited,frontier,rows), reading each
  demanded site once), with `finite_demanded_readings_exact` proving it returns exactly the rooted sites and
  the rows at them. Invariant: S∩T={}, S∪T ⊆ sites, roots ⊆ S∪T, S closed under Edges into S∪T, A = rows at S;
  measure `2*fcard((U∪roots)-S) + (if T={||} then 0 else 1)` with `measure_while_option_Some`; leastness of
  `finite_rooted_sites` by `trancl_induct` (`finite_edge_closure_correct`, and `|∈|` is set membership in
  `fset`). Then code equations for `finite_native_definition_sites`/`_graph`/`finite_native_package_readings`
  (replacing `Factor_Recovered_Graph_Sharing.finite_native_definition_graph_shared_code`, which must be
  `code del`-ed) and, if the replay stays slow, the same for `finite_recovered_graph` (its edges are
  (child,parent), so roots={|root|} with successors = the children of a read node). New theory goes into
  `Native_Execution_Refinements`' imports; every recipe re-executes (words must be equal).

- State at rotation: no job running; nothing committed; workspace clean of probes (the probe theory is parked
  in `.build/impl6/`, not in `theories/`). Uncommitted edits are impl-5's batch plus this session's
  `validation/reconstruction/native-development-seed-reports.json` (publication word) and HANDOFF.md.
- Criticism of the parked design (base terms): the family policy lists only the payload's family, so the
  rule that admits is the fixed constructor plus Isabelle's acceptance of the checked context, not the ground
  listing (owner question Q1); the alternative (a policy listing every unit of the state) is the same rule at
  n×|policy| cost, so the choice rests on cost, which has no internal account (Q2) — record it as a residual
  with that reason. Certification is acceptance entering native admission; the verdict stays the recorded
  admission evidence of the history, not a native predicate.

## impl-5 session (2026-09-18 night) — superseded by impl-6 above, nothing committed

- impl-4's open items are done: the walk adoption receipt is retained as
  `validation/development-adoptions/Development_Answer_0ccf746fe2cf.json` (READMEs of development-adoptions and
  development-answers describe it and the control `demanded-reformulated`); the exporter reads logical constants
  only (`define_again` in `Isabelle_Entity_Export`); `.build/check-20260918w --advance-base` was accepted (154
  theories, 197.7 s proof, 11 recipes equal, 168+35 tests) and retained. ACTIVE BASE: `.build/check-20260918w/proof`.
- 5a evidence measured (probe `.build/probe-impl5-a`, impl-2's `Probe_Entity_Targets`, removed from theories/):
  certified base cause read-back 0.14/0.19/0.31/0.55 s at 1/2/4/8 entities, was 1.1/1.6/3.6/9.7 s. Recorded in the
  plan section "The declared-equation reading on the base; ...".
- NEW, probed (all proofs checked on base w, `.build/probe-impl5-c`): `RRA_Finite_Transactions`,
  `Development_Publication`, `Development_Seed_Publication`; execution: 10 incumbents, all 10 first publications
  applied, all 10 second publications conflict, payloads equal, sequential publication applies all 10. ROOT,
  THEORY_MAP, `Native_Development_Seed` (imports/exports `development_seed_publication_value`), the recipe stage
  `presentation-publication` in `tools/reconstruct_native_development_seed.py` (with boundary text), the plan
  section "Publication is a transaction against the published state" and the REASONING_REUSE section are written.
- FINISHED at rotation (proof accepted: 4 theories rebuilt, 31.4 s; only `native-development-seed` failed, as
  expected for the new stage — verify the other stage words are unchanged before recording): `incremental_check.py check --advance-base --output .build/check-20260918x` (log
  `.build/check-20260918x.out`). Expected: proof accepted, seed recipe FAILS only for the new stage (no expected
  word) — possibly also old stages if exports changed (they should not). Then: copy
  `report_boundaries['presentation-publication']` from `.build/check-20260918x/recipes/native-development-seed/reconstruction.json`
  into `validation/reconstruction/native-development-seed-reports.json` (`reports` dict), `incremental_check.py
  adopt --proof .build/check-20260918x/proof`, run `check --output .build/check-20260918y` (no rebuild), then
  `incremental_check.py retain --output .build/check-20260918y`. If a proof fails, fix at the reported line.
- Cleanup after that: remove `.build/check-20260918v`, `.build/probe-impl4-a`, `.build/probe-impl4-b`,
  `.build/probe-impl5-a/b/c`, `.build/probe-impl3-b` (keep lineage p, s, u, w, x and complete-20260918n).
- NEXT batch: (1) certify development causes under the first loop's policy (impl-2's route:
  `finite_construct_source_requirements` over the ground source of entity targets, `finite_native_program_proofs`,
  `finite_certificate_replay`, `finite_required_history_step`; its read-back is now fast); (2) predecessors as base
  generations of the request context's entities; (3) the refinement layer's published state natively, so
  `tools/development_adoption.py` records the native transaction of an adoption.
- Criticism of this batch (base terms): admission (verdict + policy) and selection (transaction into the
  snapshot) are kept apart; history keeps every admitted answer while the snapshot selects one per locus; the
  locus is the problem's contract, not its payload; publication expects exactly what was read at the locus.
  Open in it: causes are recorded judgments (acceptance, verdict) not yet certified under the policy (L2: impl-2's
  route through `finite_required_history_step`); predecessors hold only the incumbent, not base generations of the
  other context entities; the refinement layer's published state is not native yet, so the host adoption tool
  still installs without a native transaction record; the choice of this batch was made outside the process.

## impl-4 session (2026-09-18 night) — superseded by impl-5 above, nothing committed

- Facts impl-3 could not record (from the maintenance session; impl-3 was stopped at 18:59 local by the
  owner's "stop everything"): check-20260918t was killed unfinished (no result); after its last handoff
  write impl-3 added `--rerecord` to `tools/replay_development_answers.py` and changed the
  REASONING_REUSE.md code-equation row to "read exactly as declared". The knowledge base `kb` no longer
  exists; `.claude/orchestration/state/qa.log` is history only.
- The declared-equation reading is validated: `Isabelle_Entities` text now says "exactly as declared";
  `.build/check-20260918u --advance-base` proved 519 rebuilt theories (233 s) and failed only on the ten
  seed words, as expected. A probe on that proof (`.build/probe-impl4-a`) showed every structural seed
  observation unchanged (104 names; 18 base, 10 development, 32 frontier constants, 10 definitions, 10
  code equations, all Pure equalities; 10 problems, one incumbent equation each, none unstated; without
  Pure.eq 20 malformed and 70 unreached, without HOL.eq nothing; 2 ungrouped candidates), so only the
  presented equation terms changed. The seed words were re-recorded from u's reconstruction, the seed
  recipe's boundary text now states the contract as the declared constant with its incumbent family, u was
  adopted as the base, and `.build/check-20260918v` (no rebuild, seed recipe 7.49 s, 50 reused, 168 tool
  and 35 kernel tests) was accepted and retained. Active base: `.build/check-20260918u/proof` (parent s ->
  p -> complete-20260918n).
- Owner ledger: Q1 (bootstrap admission rule vs OD-2), Q2 (authority of the first loop's problems and a
  cost criterion), Q3 (what Isabelle establishes about adequacy) recorded with provisional choices.
- Retained answers re-recorded on base u (`replay_development_answers.py --rerecord`): all outcomes equal to
  HEAD, only words changed; `deterministic.json` packet/executor digests updated (the regenerated packet gives
  the identical executor answer).
- FIRST REAL ADOPTION DONE: the walk answer was revised to reuse `Binary_Relation_Stores` +
  `address_binary_path` and `Ordered_Member_Trees` (no new index notion; scratch
  `.build/impl4-scratch/Probe_Indexed_Walk2.thy`, answer `.build/impl4/walk-answer.json`), judged
  (`validation/development-answers/indexed-data-walk.json`: refused for 6 introduced constants, repaired,
  extension accepted) and adopted by `tools/development_adoption.py` (receipt
  `.build/impl4/walk-adoption/receipt.json`: status adopted, check accepted 205 s, 150 theories rebuilt,
  11 recipes executed with equal words, 40 reused). The workspace now holds
  `theories/Development_Answer_0ccf746fe2cf.thy`, imported by `Native_Execution_Refinements` (and in ROOT).
  Probe: indexed walk 0.116 s vs scan 5.9 s at 8,817 addresses; 4.2 s at 124,981.
- NOT YET DONE (next, in order): (1) copy the adoption receipt to `validation/development-adoptions/`
  (name by theory) and add README entries there and in `validation/development-answers/README.md`;
  (2) apply the parked exporter fix `.build/impl4/exporter-abbreviations.txt` to
  `theories/Isabelle_Entity_Export.thy` (define_again collects logical constants only);
  (3) `incremental_check.py check --advance-base --output .build/check-20260918w` then `retain`;
  (4) measure the cause read-back after adoption with impl-2's probe
  (`.build/impl3-scratch/Probe_Entity_Targets.thy`, copy into theories/ only while probing; earlier
  1.1/1.6/3.6/9.7 s at 1/2/4/8 entities) as the 5a "consumed by later work" evidence; (5) add the adoption
  results to the plan section "The declared-equation reading on the base; ..." (already appended, lacks the
  adoption outcome) and to REASONING_REUSE (rows appended).
- Designed, not started: `RRA_Finite_Transactions` — an executable finite layer of RRA_Transaction
  (finite_snapshot = finite_generation fset, decode_finite_snapshot, finite_snapshot_formed via fcard of
  loci, finite_snapshot_lookup via finite_singleton_option, finite_transaction record, finite_transact
  returning Finite_Applied/Finite_Conflict, exactness against `transact`), then development publication as
  an advancement (`Factor_Continuation.factor_advances`: transact + continuation permission) with loci =
  problem presentations, payload = answer entities, cause = verdict; history separate from the snapshot.
- Owner said (ledger): never wait in the foreground; waiters only with run_in_background.

Checkpoint: 2026-09-18, third session of the day (impl-1 under the kb orchestration; questions and
answers in `.claude/orchestration/state/qa.log`). Read [AGENTS.md](AGENTS.md) and
[DEVELOPMENT_WORKFLOW.md](DEVELOPMENT_WORKFLOW.md) first. The owner's current goal is implementing
[native_control_plan.md](native_control_plan.md) (broad structure, not source of truth); its last four
dated sections record what the recent sessions established and what is open. Do not drift into
optimizing validation fixtures: the owner stopped that twice; work on plan items directly.

## State at this checkpoint (uncommitted batch on top of d0b70ea)

- Base: a complete source proof `.build/complete-20260918n` (1,757 theories, 524 s) was adopted, then
  advanced once by `.build/check-20260918p/proof` (stored heap; 511 theories rebuilt for the reading
  fix); the active pointer names `.build/check-20260918p/proof`. `.build/check-20260918p` is retained
  (all 51 recipes reused, 168 tool and 35 kernel tests). `.build/check-20260918q` validated the final
  texts of this batch (accepted: 68 theories rebuilt in 164 s, 50 recipes unchanged, 1 reused, 168 tool and
  35 kernel tests) and is retained. No job is running. The batch is complete and uncommitted (commit only
  on the owner's word). Older `.build/check-*`
  directories back to `overnight-20260918` are superseded; remove them once nothing refers to them.
- Theories changed: `Isabelle_Constant_Closure` owns `code_equation_theorems` (read under an EMPTY
  simpset — the global context had rewritten every declared code equation by all simp rules) and
  `note_code_equations`; `Isabelle_Entity_Export` uses it; `Isabelle_Entities` presents a rooted state
  once (`isabelle_rooted_context_data`), reused by `Development_Successor` and
  `Native_Control_Syntax_Statements` (`Native_Control_Quotation_Construction` unfolds it); texts say the
  code-equation entity kind means declared, certified equations (a residual choice with its reason).
- Tools: `tools/development_answer.py` names an answer's theory by its canonical content, frames a
  refinement-layer answer at its adoption position (the boundary's imports), judges an adopted answer as
  the published state's unchanged answer, and `--retain PATH` writes the retained record;
  `tools/development_adoption.py --record R --output DIR [--control]` adopts (precondition, install,
  check, re-judgment, receipt; withdraws on refusal or for a control). Tests in
  `tools/test_development_answer.py`.
- Evidence: `validation/development-answers/demanded-reformulated.json` (control with a different
  equation, accepted), `introduced-helper.json` re-recorded (its helper is now named under the answer's
  theory), the other five replay unchanged; `validation/development-adoptions/` holds the control's
  adoption receipt (run in an isolated copy, withdrawn).
- Plan, REASONING_REUSE, THEORY_MAP, the answer and adoption READMEs are updated.

## impl-3 session (2026-09-18 evening) — in progress, nothing committed

- The walk packet failed (`exception Match` at `the (development_named_request ...)`): `finite_data_walk` has
  two code equations and the contract was the single demanded statement, so no problem existed. kb Q1/A1
  (qa.log): contract = the constant as the state declares it; incumbent = the demanded family in the least
  context. Implemented: `isabelle_declaration_term` (Isabelle_Entities), `development_refinement_declarations`
  and the new contract (Development_Refinement_Contracts; `_contract_constant`, `_contract_unstated` replace
  `_contract_statement`, `_refuses_ambiguity`), request fields lemma (incumbent family in the context),
  packet field `constant`, seed axiom control states the incumbent equations, executor restates the single
  incumbent. Plan section "A refinement's contract is its constant", REASONING_REUSE and THEORY_MAP rows.
  Residual: the contract notion was chosen outside a native question. Limit recorded: one-equation frame.
- Indexed walk proved (scratch `.build/impl3-scratch/Probe_Indexed_Walk.thy`, moved out of theories/; probe
  `.build/probe-impl3-a` loaded): identical results for 1..80 seed entities; old walk 4.27 s vs indexed
  0.12 s at 8,817 carrier addresses (old: 0.017/0.018/0.024/0.034/0.069/4.27 s at 541..8,817). Reuse answer
  to kb A2: `Binary_Relation_Stores` keeps no multiplicity (fset buckets) and needs binary path keys, so the
  counted bag slice would stay a scan; `grouped_rows` groups rows under any linear key with multiplicity;
  the carrier uses `Ordered_Member_Trees`. Answer prepared: `.build/impl3/walk-answer.json` (definitions =
  the scratch sections 1-3; equation `finite_data_walk n C r=indexed_data_walk C n r`).
- `tools/development_adoption.py` adopts a repaired answer (route `repaired request`: summary.repaired and
  summary.extension) besides an accepted one.
- Contract batch validated: check-20260918r failed only on the seed words expected to change (problems,
  problems-answered, loop, succession; verification unchanged), re-recorded in
  `validation/reconstruction/native-development-seed-reports.json`; `check-20260918s --advance-base`
  accepted (68 theories, 175.6 s proof) and retained; active base = `.build/check-20260918s/proof`
  (parent check-20260918p -> complete-20260918n). Superseded checks, overnight dir and their heaps removed.
- The walk packet still failed: the demanded state held NO code equation of `finite_data_walk` (impl-1's
  reading `get_cert ctxt []` cannot certify Suc-pattern equations without the generator's function
  transformers; the silent `[]` hid it). kb Q2/A2: graph certificate rejected (not local: carries callees'
  sort demands). Implemented: `Isabelle_Constant_Closure.code_equation_theorems` = declared equations
  captured through `Code.get_cert`'s transformer hook (receiver returns NONE), unoverloaded; probe
  (`.build/impl3-scratch/Probe_Code_Reading.thy`): finite_data_walk 2 equations, 11/13 compared constants
  differ in form from the certified reading (HOL = vs Pure ==), notable as theorems in a local theory.
  Plan row added. TODO once the check is done: Isabelle_Entities text still says "declared and certified"
  (lines ~10-13) -> "as declared"; kb A2 open items: dependency reading from the code graph, Abstr/Proj specs.
- Running: `.build/check-20260918t` (reading change; ~500 dependents of Isabelle_Constant_Closure). Expect
  seed recipe words to change everywhere -> re-record the seed reports from its reconstruction.json (all
  stages), then `check --advance-base` (fresh dir), then `incremental_check.py retain`.
- Retained answers: replay on base s showed 7 of 8 words differ (failed-proof reconstructs); re-record all
  after the reading change is on the base: per record extract `answer`, run `development_answer.py answer
  --answer A --output DIR --retain validation/development-answers/NAME.json`; deterministic.json also keeps
  executor/packet digests (regenerate its packet: `development_answer.py packet --state development_seed
  --subject Factor_Digit_Replay_Methods.digit_replay_inspect`, run tools/development_executor.py, compare).
- Then: packet for finite_data_walk (two incumbent equations now), judge `.build/impl3/walk-answer.json`
  with `--retain validation/development-answers/indexed-data-walk.json` (expect refused for introduced
  constants, repaired + extension accepted), adopt with tools/development_adoption.py (real, not control),
  retain costs (certified causes before/after, 21.3-30.9 s). kb A1/A2 criticisms still to answer in the
  record: depth (definition requests), ranking by measured cost (no internal account).

## impl-2 session (2026-09-18 evening) — parked, nothing committed, nothing adopted

Measured (probe on the base heap, `theories/Probe_Entity_Targets.thy`, scratch, not in ROOT): seed entities
as whole-artifact literal targets (`Finite_Target (Finite_Whole (finite data syntax of isabelle_entity_data e))`),
policy = `finite_construct_source_requirements` over `finite_ground_source` of the targets, certificates by
`finite_native_program_proofs`, replay by `finite_certificate_replays`, record by `finite_required_history_step`.
Every stage is milliseconds EXCEPT reading the cause back: `finite_certified_base_cause` and the alignment fBex
over `finite_generation_judgment_readings` take 1.1/1.6/3.6/9.7 s at 1/2/4/8 entities, cause artifacts of
6,657/8,377/12,393/19,789 carrier addresses (quadratic). Cause: the complete data walk
(`finite_data_walk`, Factor_Complete_Data_Walks) scans all incidence rows (`finite_headed_incidence`), all
bindings/bag (`finite_payload_values`, `finite_basis_slice`) and the carrier per node.

In progress (task 1): an indexed walk, `theories/Probe_Indexed_Walk.thy` (scratch, not in ROOT): walk
parameterized by readers (`data_walk_read` heads/slice/member), `data_walk_read_artifact` = `finite_data_walk`,
readers indexed once (`grouped_rows` RBT by head / by address, `ordered_member_tree` for the carrier),
`indexed_data_walk_exact`. Last probe: 4 proofs still fail (leaf_values_read_artifact needs
`finite_payload_leaf_body_def` unfolded under ffilter (use ffilter_cong/fset_eqI); `filter_mset_eq_empty_iff`
does not exist (use `filter_mset_eq_conv`/multiset_eq_iff or `filter_mset_empty_conv`);
artifact_head_index_exact and artifact_slice_index_exact need `force`/explicit image rewriting);
first timing: carrier 541, new walk 0.005 s. Rerun with
`python3 -B tools/probe_theories.py --work .build/probe-impl2-b --theory Probe_Indexed_Walk --timeout 380`.
Decision (provisional, a residual; kb Q2/A2 in qa.log): refine `Factor_Complete_Data_Walks.finite_data_walk`
(NOT the seed root `finite_complete_data_readings_prepared`) through the loop: its declaration stays on the
seed's frontier, so the seed state and seed words do not change, avoiding the seeded-state adoption case (kb
A2.4, still open). Route: packet (running at start of rotation: `.build/impl2/walk-packet`, log
`.build/impl2/walk-packet.out`; `development_answer.py packet --state refinement_layer --subject
Factor_Complete_Data_Walks.finite_data_walk`) -> answer written from the packet (retain packet + answer;
unisolated executor = residual) with equation `finite_data_walk n C r=indexed_data_walk C n r` and the helpers
as introduced constants -> `development_answer.py answer --retain` -> repair (introduced helpers) ->
EXTEND `tools/development_adoption.py` to adopt a repaired answer (today it asserts summary.accepted, the first
verdict) -> adopt -> measure before/after on the same samples and on certified-causes (21.3 s), retain as
observations. kb A2 criticism to answer: earlier "index" candidates were rejected
(validation/reconstruction/decision-replay-cost-measurements.json) — confirm this is new evidence; reuse
Binary_Relation_Stores/Keyed_Finite_Sets instead of a new grouping if they fit; depth (three leaves: index
with lookup contract, indexed walk = finite_data_walk, the equation) and definition requests are open.
Then task 2: seed units as RRA base generations under the seed policy (kb A1): unit = (entity kind, subject
names) family, locus by names (isabelle_name_data), payload = self-contained presentation (local name table);
acceptance made presentation-parametric (no duplicate); re-sample the n*|policy| growth (each cause quotes the
whole ground policy) as its own machinery problem. Verdict as a second requirement goal (kb A1.3) is a candidate.
OWNER QUESTION (provisional choice, proceed without waiting, ask via kb): a policy built from each answer's own
checked context conflicts with OD-2 ("No successor may justify its own adoption under rules introduced only by
itself"); provisional: during bootstrap the fixed rule is Isabelle acceptance of the checked context + the
verdict, instantiated per context; after genesis only the amendment/transition chain. Not sent to the owner yet.
Scratch to remove when done: theories/Probe_Entity_Targets.thy, theories/Probe_Indexed_Walk.thy,
.build/probe-impl2-a, .build/probe-impl2-b.

## Next

1. Development generations as RRA generations (kb A2, qa.log): present problems, entities and verdicts
   as whole-artifact targets through their injective presentations (Factor_Finite_Term_Encoding,
   Factor_Finite_Data_Syntax, Factor_Target_Values), so every existing contract applies — certified
   policy cause, history append (`finite_required_history_append_valid`), one-locus replacement
   (RRA_Replacement) and publication (RRA_Publication's snapshot/dependency/evidence selections).
   Predecessors = the generations that established the request context (plan, Verifying step 5); base
   entities need base generations (Factor_Base_Cause, Factor_Base_Programs). Submit this route and the
   generic-selection route with their coverage of cause/append/publication as facets. Known cost on the
   path: native installation's quadratic compile — fix at its cause.
2. The persistent history: one development state whose roots grow by demand (reuse the repair's
   extension and `define_again`); the history holds refusals and admitted-unselected answers too;
   adoption frames import exactly the adoptions their request context depends on (a DAG, not the
   current chain through the boundary's full imports); any linearization is identification only.
3. Still open: ranking by measured cost (no internal account of a physical measurement), seeded-state
   adoption, a real (non-control) adoption consumed by later work (5a), the native residual record,
   stage 4 policy extension (proceed provisionally under the owner's 2026-09-18 direction, ask via kb),
   agent isolation, stage-1 provenance and locality (adoption can exercise locality).
4. Pitfalls: never wait or kill with a pattern contained in the command's own command line; Isar
   keywords as labels fail far from the cause; `blast`/`auto` on existential goals can run for minutes;
   keep a check's inputs fixed while it runs; `sleep` in the foreground is blocked — wait on PIDs
   (`tail --pid`) in one background waiter; three concurrent heavy Isabelle runs reached 59 of 60 GiB —
   run one check at a time beside at most a few harness sessions; zsh does not word-split `$VAR`
   (use `bash -c`).

## Committed work and validation boundary

53 theories are integrated into `theories/` and `ROOT`, byte-identical to their
accepted overnight providers. The [inventory](validation/overnight-20260918/integration.json)
binds each theory to its original source and provider. A fresh Isabelle/HOL build
checked their entire 1,080-theory closure with zero project theories reused in
311.491 seconds including startup, without session errors. This is a **partial
scope**, not a successful build of the whole `ROOT` session.

Fresh exports match the overnight modules byte for byte. Both the certificate
and material replays match their complete original assessments and native words.
The cleanup retains complete report identities and a source-only reconstruction
boundary. Generated output is rebuilt when needed.

[validation/overnight-20260918](validation/overnight-20260918/README.md) retains
the source closure, native requests, expected complete-report identities, compact
verification and the retirement record. Unique diagnostics/candidates are explicit
source files under `unfinished/`, outside ROOT. Full historical logs, generated
outputs and superseded snapshots remain recoverable from commit `d85a02e`; none is
a current reconstruction input. No old `/tmp` provider or active pointer is needed.

Segment 10 proposed application-result selection and source-reader staging but
left no implemented theory candidate for them.
The missing argument to `Development_Refinement` in `Development_Seed` is repaired
below; the seed recipe's expected reports are still empty placeholders.

## Latest native results

The actual subject is the checked rooted context and complete proposition for
`Original_Union`, with the universally quantified `finite_syntax_join` refinement.
`Native_Control_Syntax_Statements` checks theorem propositions and absence of
hypotheses. This covers neither arbitrary theorems nor every paused refinement.

The admitted root application retains the original quoted guard, four bindings
and all three sockets. Native observation selects `Observed_Parts` under both
original facets. An application is not a root proof.

The certificate review retains all original full/leaf demands and both
`Requested_Certificates` and `Checked_Certificates`. Full children, projection
and quotation have no original two-facet choice. The natural body leaf has a
singleton complete proof-set result, preserved under reversal and duplication.
All absent reports refuse. One quotation control with only
`Requested_Certificates` accepts the supplied original-body report; exact question
equality remains unknown. Do not claim every wrong-report control refused.

The material review, completed after the older handoff, finished quotation and
both body clauses. Projection timed out at 90 seconds and is unresolved. All
15 completed method choices return `None`; multiple satisfactory methods do not
select a unique method. Complete application-value equality is still unknown.
All 15 absent/wrong-body report controls refuse. Timeout supplies no negative
semantic observation.

Guard installation proves source existence and definition-coordinate transport
under its installation premise. Actual source execution timed out: no complete
returned source record was accepted. Definition-site injection does not transport
clause, variable or socket proof coordinates. Certificate/policy continuation
retains actual original proof checking, literal replay and aligned policy/history
premises. No installed guard certificate, replay or governing cause exists.

## The seeded refinement contracts — 2026-09-18

`Development_Seed` applied `Development_Refinement` to no argument, so the theory did not
load and the complete repository check stopped there. That argument is now chosen by
readings computed on the actual seeded state, and the state itself is no longer defined
twice: the theory instantiates the accepted `Native_Control_Seed_Subject` instead of
repeating its exporter.

Three reusable theories carry the account. `Isabelle_Code_Equations` reads the executable
content of an entity, which the existing subject reading cannot distinguish from a kernel
definition. `Filtered_Native_Questions` holds the native question over actual subjects with
a computed condition, extracted from its first use in `Native_Control_Syntax_Candidate`,
which now instantiates it; `Faceted_Native_Questions` was already a second user through the
import chain. `Development_Refinement_Contracts` keeps two readings apart: the scope of a
constant is what the state presents about it, and the demand selects what a refinement must
establish inside that scope. The contract is the single demanded statement under the
existing `list_singleton_option` reading, so a repeated presentation is still one statement
and several distinct statements are refused rather than resolved by position.

Executed on the seeded state inside the checked context: every root constant has a scope of
exactly two entities, its kernel definition and its code equation, and exactly one is
demanded. `native_development_admission` admits exactly the computed demand for all ten
roots. Every root therefore has a contract and none is retained as unstated. The demanded
statements mention no other root, so every computed premise set is empty and the ten
problems are independent; the grouping into three measured candidates asserted a dependency
structure the state's statements do not supply, and the kernel definitions carry a different
relation. Two of the three groupings cover more than one constant and are retained as an
obstruction: the equations are Pure equalities and the table holds no `HOL.Trueprop`, so the
state states no single refinement of several constants.

Scoping the question is also what makes it affordable. Ranging the candidates over all
eighty entities conflates what a problem is about with what its answer must establish, and
that question had not returned after 243 seconds; the scoped question and its admission for
all ten roots complete in 11 seconds including the load. The four new or rewritten theories
check in 3.2 seconds on the accepted base heap.

The contract, scope, demand and dependencies are computed. Selecting these ten root
constants from the measured candidates remains a residual generated outside the process,
and every seeded problem records that origin and generated authority. Nothing here
establishes that an answer satisfies a demanded statement, that these roots are adequate to
the measured candidates, or that any refinement work has been done.

## The seed presentations complete — acceptance consumes its contract

The seed recipe's five rooted-state presentations had each reached the 1200-second timeout,
and their Isabelle processes kept running after it: the runner stopped only the wrapper it
started. Attributed on samples, the whole cost was the acceptance decision. The context term
forms in 0.3 seconds; `isabelle_demand_acceptance` over the 80 entities did not return in
2,281 seconds, and within it only compiling the ground definition was slow (not returned in
1,363 seconds). Clause by clause the compile is quadratic in the term (43.2 seconds for the 80
clauses alone, 13.6 for the largest), and the compiled forest then joins 124,800 carrier
addresses through member-by-member unions of listed sets.

The decision now consumes the notion's contract. `Factor_Finite_Ground_Evaluation` proves
that native evaluation answers every entry demand of an installed ground source, so
`isabelle_demand_acceptance` is total, and `isabelle_demand_acceptance_members` (demanded
entities split by membership in the supplied ones) is its code equation. The seed's
acceptance computes in 0.001 seconds; all seven presentations complete in about 2.2 seconds,
and their boundaries are recorded from that accepted run. The quadratic compile remains a
measured machinery problem for the process (see [REASONING_REUSE.md](REASONING_REUSE.md)).

The first execution also falsified one control. Moving `HOL.eq` observed nothing, because
every definition and code equation of the state is a Pure equality. The controls are now
derived from the reader's `isabelle_equality_names`: without `Pure.eq` twenty entities lose
their subjects and are malformed and seventy are no longer reached; without `HOL.eq` nothing
changes. Timeouts in the recipe, report, execution, check and probe runners now stop the
whole process session (`build.run_session`), and the probe tool resolves a child context's
parent sessions.

## The first loop's selection, group and requests — native and reconstructed

Stage 2 has begun. `Development_Requests` states selection as the filtered native question on
computed readiness, proves admitted problems pairwise independent, and constructs a
refinement request with its demanded statement, support and least context (exact, closed,
least). `Development_Seed_Loop` executes the seed's ten contract decisions and its selection
as native packets and presents them with the admitted group and the ten requests; the seed
recipe reconstructs that report in 9.2 seconds. Settlement in `Development_Problems` was
corrected so that a dependency row fires only for an answered problem, and the generic
admitted-subject consumers moved from `Native_Control_Admitted_Selection` into
`Filtered_Native_Questions`. The repository check of this batch was accepted (145 seconds of
proof for 53 rebuilt theories, one recipe re-executed) and retained. Requests are not issued
yet: the verifier of a refinement answer and the leafhood account come next. A native
question over sixteen candidates costs about 13 seconds; that cost is being removed.

## Rebuild without overnight temporary files

Use Python 3.14 and Isabelle2025-2 (`isabelle` on PATH; the existing runtime helper
expects Poly/ML under `/opt/isabelle`). This is the normative bootstrap toolchain.
Heaps are generated caches. Each output directory must be fresh. Current proof
and replay reconstruction reads only current repository inputs and the toolchain.

```sh
python3 -B tools/materialize_source_boundary.py --project . --manifest validation/overnight-20260918/sources.json --output .build/next-native-source
python3 -B tools/reconstruct_overnight.py prove --output .build/next-native-proof
python3 -B tools/reconstruct_overnight.py export --context .build/next-native-proof --output .build/next-native-exports
python3 -B tools/reconstruct_overnight.py replay certificates --exports .build/next-native-exports --output .build/next-certificates
python3 -B tools/reconstruct_overnight.py replay materials --exports .build/next-native-exports --output .build/next-materials
```

Proof builds directly from HOL without the active-context pointer. Export
verifies/adopts only the new context. Replay loads unchanged historical
request/assessment function ASTs with fresh paths and compares complete
assessment boundaries and native word identities. Material timeout outcomes can change;
review a difference rather than force it to match. Concurrent JVM jobs must
share a process namespace: separate sandbox namespaces can collide in shared
`hsperfdata`. Native per-subject material preparation remains parallel.

The fresh proof can supply `tools/prove_context.py --parent-project` for covered
theories; do not activate it as a full repository context. Useful unaccepted
source is directly inspectable in
[unfinished/](validation/overnight-20260918/unfinished/README.md). It is not part
of the accepted theory scope. No archive extractor or historical heap is needed.

## Remaining obligations and next content batch

1. Submit the application-result-selection gap and source/material bottlenecks
   through the native/bootstrap process. Instantiate faceted/singleton contracts
   with complete values and both original facets; establish their equality and
   observation equations. Expose source-reader/material substages without changing
   the operations. No optimization is selected by this storage consolidation.
2. Construct/check projection and quotation certificates and the full child
   family. Establish natural-to-installed clause/variable/socket proof transport
   or an independently checked native-source construction. Then construct the
   root proof, literal replay and aligned policy cause/history.
3. Preserve every `finite_program_evaluation_ready` premise: formed source,
   coverage of **every** clause at demanded definitions and demand closure.
   The guard lacks head variables `{1,2,3}`; projection needs material variables.
   Source existence or one leaf cannot discharge these premises. Do not increase
   timeouts or weaken checks to bypass the missing account.
4. Establish owner-authorized governing requirements, fixed policy/source/entry,
   authority/current basis, derived support and least contexts, dependency/absence/
   invalidation, recursively admitted selection/scheduling/requests, inert
   executors, predecessor-admitted amendments and first-use factoring.
5. The seed's contract choice is repaired through its native account and its report
   boundaries are recorded from an accepted run, both described above; the complete
   repository check on this workspace is the remaining validation of the item. Conditions 1–4, practical 5a and 6 remain open; theoretical 5b is
   deferred. O-73 stays Open, O-85 Partial, and genesis absent. This checkpoint retains
   reconstruction boundaries; the broader native retention/workflow account is still open.

The old segment-9 retention job and several interrupted/timed-out descendants
lack positive exit evidence in their original PID namespaces. Their records are
preserved; current numeric PIDs are not identities. Current reconstruction does not
depend on them. The owner-requested cleanup removed verified duplicate validation
trees without signalling processes or claiming exit evidence. Original temporary
provider caches remain untouched; their historical paths are not build inputs.
