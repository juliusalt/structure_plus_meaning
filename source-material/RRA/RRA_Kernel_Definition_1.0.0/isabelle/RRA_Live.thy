theory RRA_Live
  imports RRA_Artifact
begin

type_synonym locus_ref = octets

type_synonym generation_ref = record_ref

record generation =
  generation_locus :: locus_ref
  predecessors :: "generation_ref set"
  generation_payload :: record_ref
  generation_dependencies :: "record_ref set"
  generation_evidence :: "record_ref set"

record live_state =
  heads :: "locus_ref ⇒ generation_ref option"
  retained :: "generation_ref ⇒ generation option"

definition live_state_formed :: "live_state ⇒ bool" where
  "live_state_formed S ⟷
     finite {l. heads S l ≠ None} ∧ finite {r. retained S r ≠ None} ∧
     (∀l r. heads S l=Some r ⟶
       (∃G. retained S r=Some G ∧ generation_locus G=l)) ∧
     (∀r G p. retained S r=Some G ∧ p∈predecessors G ⟶ retained S p≠None) ∧
     acyclic {(p,r). ∃G. retained S r=Some G ∧ p∈predecessors G}"

record next_generation =
  next_payload :: record_ref
  next_dependencies :: "record_ref set"
  next_evidence :: "record_ref set"
  additional_predecessors :: "generation_ref set"

record transaction =
  tx_compare :: "locus_ref ⇒ generation_ref option option"
  tx_write :: "locus_ref ⇒ next_generation option"

definition transaction_formed :: "transaction ⇒ bool" where
  "transaction_formed T ⟷
     finite {l. tx_compare T l ≠ None} ∧ finite {l. tx_write T l ≠ None} ∧
     {l. tx_write T l ≠ None} ⊆ {l. tx_compare T l ≠ None}"

definition compare_passes :: "live_state ⇒ transaction ⇒ bool" where
  "compare_passes S T ⟷
     (∀l expected. tx_compare T l=Some expected ⟶ heads S l=expected)"

record publication =
  published_heads :: "(locus_ref × generation_ref) set"
  published_protocols :: "record_ref set"
  published_executions :: "record_ref set"
  published_checker_runs :: "record_ref set"
  published_trust_decisions :: "record_ref set"
  published_policies :: "record_ref set"
  published_dependencies :: "record_ref set"
  published_evidence :: "record_ref set"
  published_provenance :: "record_ref set"

end
