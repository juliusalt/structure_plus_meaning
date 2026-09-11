theory Factor_Instantiated_Premises
  imports Factor_Executable_Schemas
begin

section \<open>One complete premise relation from the original schema\<close>

definition finite_instantiated_premises ::
  "('a,'s,'d) finite_factor_schema \<Rightarrow> ('a \<times> finite_factor_term) fset \<Rightarrow>
    ('s \<times> ('d \<times> finite_factor_term)) fset" where
  "finite_instantiated_premises S V = ffUnion (fimage (\<lambda>(s,d,p).
    fimage (\<lambda>t. (s,d,t)) (finite_pattern_instances V p)) (finite_schema_premises S))"

lemma finite_instantiated_premises_member:
  "(s,d,t) |\<in>| finite_instantiated_premises S V \<longleftrightarrow>
    (\<exists>p. (s,d,p) |\<in>| finite_schema_premises S \<and> t |\<in>| finite_pattern_instances V p)"
  by (auto simp: finite_instantiated_premises_def fimage.rep_eq ffUnion.rep_eq split: prod.splits; force)

lemma finite_instantiated_premises_decode:
  "(s,d,t) \<in> decode_finite_premises (finite_instantiated_premises S V) \<longleftrightarrow>
    (\<exists>p. (s,d,p) \<in> schema_premises (decode_finite_schema S) \<and>
      pattern_instance (decode_finite_term_bindings V) p t)"
  by (auto simp: decode_finite_premises_def decode_finite_call_term_def decode_finite_call_pattern_def
      finite_instantiated_premises_member finite_pattern_instances_complete; blast)

lemma finite_instantiated_premises_correct:
  assumes "schema_instance (decode_finite_schema S) (decode_finite_term_bindings V) t Q"
  shows "decode_finite_premises (finite_instantiated_premises S V) = Q"
  using schema_instance_premise_iff[OF assms] finite_instantiated_premises_decode[of _ _ _ S V]
  by (auto simp: set_eq_iff split_paired_All)

lemma finite_schema_instance_premise_iff:
  assumes inst: "finite_schema_instance S V t H"
  shows "(s,d,u) |\<in>| H \<longleftrightarrow>
    (\<exists>p. (s,d,p) |\<in>| finite_schema_premises S \<and> finite_pattern_instance V p u)"
proof -
  have native: "schema_instance (decode_finite_schema S) (decode_finite_term_bindings V)
    (decode_finite_term t) (decode_finite_premises H)"
    using inst by (simp only: finite_schema_instance_correct)
  show ?thesis
    using schema_instance_premise_iff[OF native, of s d "decode_finite_term u"]
    by (auto simp: decode_finite_premises_def decode_finite_call_pattern_def
      decode_finite_call_term_def map_relation_values_def finite_pattern_instance_correct
      image_iff Bex_def split_paired_Ex)
qed

lemma finite_instantiated_premises_exact:
  fixes S :: "('a,'s,'d) finite_factor_schema"
  assumes inst: "finite_schema_instance S V t H"
  shows "finite_instantiated_premises S V=H"
proof (rule fset_inject[THEN iffD1], rule set_eqI)
  fix z :: "'s\<times>'d\<times>finite_factor_term"
  obtain s d x where shape: "z=(s,d,x)" by (cases z) auto
  show "z\<in>fset (finite_instantiated_premises S V) \<longleftrightarrow> z\<in>fset H"
    by (simp only: shape finite_instantiated_premises_member finite_pattern_instances_member finite_schema_instance_premise_iff[OF inst])
qed

end
