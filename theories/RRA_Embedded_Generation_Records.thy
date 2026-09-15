theory RRA_Embedded_Generation_Records
  imports RRA_Fresh_Generation_Frames RRA_Generation_Record_Recovery
begin

definition embedded_generation_record_environment where
  "embedded_generation_record_environment h E u l p c as v=
    embedded_graft_environment h (fresh_generation_predecessor_environment E u l p c as v)
      (literal_environment (generation_record_frame l p c as) (generation_record_literals l p c))"

locale embedded_generation_record = fresh_generation_frame E u l p c as v
  for E :: "local_address option artifact_environment" and u :: "local_address option"
    and l p c :: exact_target and as :: "(exact_artifact\<times>local_address) list"
    and v :: "nat\<Rightarrow>local_address option" +
  fixes h :: "local_address option\<Rightarrow>local_address option"
  assumes embedding: "boundary_use_embedding
    (environment_uses (fresh_generation_predecessor_environment E u l p c as v)) u h"
begin

abbreviation H where "H\<equiv>embedded_generation_record_environment h E u l p c as v"

sublocale embedded: embedded_literal_extension F u R L h
  by (unfold_locales) (rule embedding)

lemma result_same: "H=embedded.result" by (simp only: embedded_generation_record_environment_def)
lemma formed: "environment_formed H" by (simp only: result_same; rule embedded.result_formed)
lemma included: "environment_included E H"
  by (simp only: result_same; rule environment_included_trans[OF predecessor_included embedded.result_includes_original])
lemma source: "artifact_at H u frame.framed"
  using embedded.result_source by (simp only: result_same frame_same)

lemma field_values:
  "external_slot_values H u (syntax_branch 0 [4])={target_artifact l}"
  "external_slot_values H u (syntax_branch 2 [4])={target_artifact p}"
  "external_slot_values H u (syntax_branch 3 [4])={target_artifact c}"
  by (simp only: result_same; rule embedded.result_literal_singleton;
    simp add: generation_record_literals_def)+

lemma fields: "generation_fields_at H u [] l (generation_frame_members n) p c"
proof -
  have locus: "anchored_at H u (syntax_branch 0 []) l"
    by (rule anchored_atI[OF source frame.locus_citation
      literal_citation_mapped_interpretation[where f="syntax_branch 0", OF lf field_values(1)]])
  have payload: "anchored_at H u (syntax_branch 2 []) p"
    by (rule anchored_atI[OF source frame.payload_citation
      literal_citation_mapped_interpretation[where f="syntax_branch 2", OF pf field_values(2)]])
  have cause: "anchored_at H u (syntax_branch 3 []) c"
    by (rule anchored_atI[OF source frame.cause_citation
      literal_citation_mapped_interpretation[where f="syntax_branch 3", OF cf field_values(3)]])
  show ?thesis by (rule generation_fields_atI[OF formed source frame.fields
    frame.predecessor_family locus payload cause])
qed

lemma locations:
  assumes index: "i<n"
  shows "located_at H u (generation_predecessor_node i) (v i) (snd (as!i))"
proof -
  have bound: "binds_slot H u (generation_predecessor_slot i) (v i)"
    by (simp only: result_same; rule included_binding[OF embedded.result_includes_original predecessor_at[OF index]])
  have original: "artifact_at E (v i) (fst (as!i))"
    and anchor: "anchor_formed (fst (as!i),snd (as!i))" using chosen index by auto
  have target: "artifact_at H (v i) (fst (as!i))" by (rule included_artifact[OF included original])
  have loc: "citation_location H u (External (generation_predecessor_slot i) (snd (as!i))) (v i) (snd (as!i))"
    using bound target anchor by auto
  show ?thesis using source frame.predecessor_citation[OF index] loc
    unfolding located_at_def by blast
qed

sublocale recovery: generation_record_recovery E H u l p c as v
  by (rule generation_record_recovery.intro[OF formed included fields]) (use locations in blast)

theorem old_artifacts:
  "w\<in>environment_uses E \<Longrightarrow> artifact_at H w T \<longleftrightarrow> artifact_at E w T"
  by (rule included_existing_artifact[OF included formed])

theorem bindings:
  "binds_slot H w k z \<longleftrightarrow> binds_slot E w k z \<or>
    (w=u \<and> ((k,z)\<in>D \<or> (k\<in>rel_dom L \<and> z=h (Some k))))"
  by (simp only: result_same embedded.result_bindings predecessor_bindings) blast

theorem old_bindings:
  "w\<in>environment_uses E \<Longrightarrow> binds_slot H w k z \<longleftrightarrow> binds_slot E w k z"
  using fresh by (auto simp: bindings)

end

context generation_record_construction
begin

sublocale embedded: embedded_generation_record E record_use l p c as v
    "fresh_use_map (environment_uses fresh_frame.F) record_use"
  by (unfold_locales)
    (rule original_boundary_embedding[OF environment_uses_finite[OF fresh_frame.predecessor_formed]])

lemma original_embedded_generation_instance: "installed=embedded.H"
  by (simp only: generation_record_environment_def original_predecessor_instance
    embedded_generation_record_environment_def generation_record_literals_def Let_def
    embedded_graft_environment_def graft_environment_def)

end

text \<open>
  Every admitted embedding produces the complete original fields and exact
  predecessor locations, and preserves all old artifacts and bindings.
  Recursive recovery instantiates the installation-independent contract.
  The original environment constructor is equal to its explicit instance.
  These results do not establish cause truth or historical permission.
\<close>

end
