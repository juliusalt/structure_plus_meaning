theory Factor_Matching_Instances
  imports Factor_Executable_Matching
begin

section \<open>Instances determine their complete used bindings\<close>

lemma finite_matching_complete_scope:
  fixes p :: "'a finite_term_pattern"
  assumes bindings: "finite_term_bindings_formed (finite_pattern_variables p) V"
    and inst: "finite_pattern_instance V p t"
  shows "finite_matching_bindings p t=V"
proof -
  let ?M="finite_matching_bindings p t"
  let ?D="decode_finite_term_bindings"
  have native: "pattern_instance (?D V) (decode_finite_pattern p) (decode_finite_term t)"
    using inst by (simp only: finite_pattern_instance_correct)
  have subset: "?D ?M\<subseteq>?D V"
    and domain: "rel_dom (?D ?M)=pattern_variables (decode_finite_pattern p)"
    using finite_matching_bindings_complete[OF native] by blast+
  have formed: "term_bindings_formed (pattern_variables (decode_finite_pattern p)) (?D V)"
    using bindings by (simp only: finite_term_bindings_formed_correct finite_pattern_variables_correct)
  have reverse: "?D V\<subseteq>?D ?M"
  proof
    fix z assume member: "z\<in>?D V"
    obtain a x where shape: "z=(a,x)" by (cases z) auto
    have in_domain: "a\<in>rel_dom (?D ?M)"
      using member formed domain by (auto simp: shape term_bindings_formed_def rel_dom_def)
    obtain y where recovered: "(a,y)\<in>?D ?M" using in_domain by (auto simp: rel_dom_def)
    have same: "x=y"
      using subset recovered member formed
      by (auto simp: shape term_bindings_formed_def single_valued_def)
    show "z\<in>?D ?M" using recovered by (simp only: shape same)
  qed
  have equal: "?D ?M=?D V" using subset reverse by blast
  show ?thesis
  proof (rule fset_inject[THEN iffD1], rule set_eqI)
    fix z :: "'a\<times>finite_factor_term"
    obtain a x where shape: "z=(a,x)" by (cases z) auto
    show "z\<in>fset ?M \<longleftrightarrow> z\<in>fset V"
      by (simp only: shape decode_finite_term_binding[symmetric] equal)
  qed
qed

lemma finite_pattern_instance_accepted:
  assumes bindings: "finite_term_bindings_formed B V" and inst: "finite_pattern_instance V p t"
  shows "finite_pattern_accepts p t"
proof -
  have native_bindings: "term_bindings_formed (fset B) (decode_finite_term_bindings V)"
    using bindings by (simp only: finite_term_bindings_formed_correct)
  have native_instance: "pattern_instance (decode_finite_term_bindings V)
    (decode_finite_pattern p) (decode_finite_term t)"
    using inst by (simp only: finite_pattern_instance_correct)
  have formed: "term_formed (decode_finite_term t)"
    by (rule pattern_instance_formed_term[OF native_bindings native_instance])
  have recovered: "pattern_instance (decode_finite_term_bindings (finite_matching_bindings p t))
    (decode_finite_pattern p) (decode_finite_term t)"
    using finite_matching_bindings_complete[OF native_instance] by blast
  have scoped: "term_bindings_formed (pattern_variables (decode_finite_pattern p))
    (decode_finite_term_bindings (finite_matching_bindings p t))"
    by (rule finite_matching_bindings_formed[OF native_bindings native_instance])
  show ?thesis using formed recovered scoped
    by (simp only: finite_pattern_accepts_def finite_term_formed_correct
      finite_term_bindings_formed_correct finite_pattern_variables_correct finite_pattern_instance_correct)
qed

end
