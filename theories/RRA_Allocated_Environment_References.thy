theory RRA_Allocated_Environment_References
  imports RRA_Allocated_Environment_Projection
begin

type_synonym allocated_update_subject = "allocated_environment_store option\<times>allocated_environment_update"
type_synonym allocated_update_value = "(nat\<times>local_address option finite_artifact_environment) option"

definition allocated_update_relation :: "allocated_update_subject\<Rightarrow>allocated_update_value\<Rightarrow>bool" where
  "allocated_update_relation X result=(case X of (input,op) \<Rightarrow>
    case input of None \<Rightarrow> False | Some q \<Rightarrow>
    let raw=raw_allocated_environment q;n=fst raw;E=indexed_environment_view (snd raw);
      original=decode_finite_environment E;update=allocated_environment_update_at n op
    in case result of None \<Rightarrow> \<not>original_environment_update_ready original update
      | Some (n',F) \<Rightarrow> original_environment_update_ready original update \<and>
        n'=allocated_environment_next_head n op \<and>
        decode_finite_environment F=original_environment_update_body original update)"

definition allocated_update_reference_option where
  "allocated_update_reference_option q op=(let raw=raw_allocated_environment q;
    n=fst raw;E=indexed_environment_view (snd raw);update=allocated_environment_update_at n op in
      if finite_environment_update_ready E update
        then Some (allocated_environment_next_head n op,finite_environment_update_body E update) else None)"

definition allocated_update_reference where
  "allocated_update_reference X=(case X of (input,op) \<Rightarrow>
    case input of None \<Rightarrow> {||} | Some q \<Rightarrow> {|allocated_update_reference_option q op|})"

theorem allocated_update_reference_exact:
  "result |\<in>| allocated_update_reference X \<longleftrightarrow> allocated_update_relation X result"
  by (cases X; cases result)
    (auto simp: allocated_update_reference_def allocated_update_reference_option_def
      allocated_update_relation_def Let_def finite_environment_update_ready_exact
      finite_environment_update_body_exact[symmetric] decode_finite_environment_injective
      split: option.splits if_splits)

lemma allocated_update_typed_exact:
  "map_option (\<lambda>following. allocated_environment_view (raw_allocated_environment following))
      (allocated_environment_update_typed q op)=allocated_update_reference_option q op"
proof -
  have projected: "map_option (\<lambda>following. allocated_environment_view (raw_allocated_environment following))
      (allocated_environment_update_typed q op)=
    map_option allocated_environment_view (map_option raw_allocated_environment (allocated_environment_update_typed q op))"
    by (simp only: option.map_comp comp_def)
  show ?thesis by (simp only: projected allocated_environment_update_projection
    allocated_environment_update_view[OF allocated_environment_valid] allocated_update_reference_option_def Let_def)
qed

text \<open>
  The original environment readiness and complete constructor determine the
  result. Unavailable prepared input has no result row; a prepared input whose
  new operation fails has one explicit absent-result row. The complete returned
  head and environment remain observable, independently of invariant validity.
\<close>

end
