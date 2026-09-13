theory Factor_Interface_Construction
  imports Factor_Reference_Tables
begin

section \<open>Scoped interface code in any actual destination environment\<close>

locale interface_syntax_construction =
  fixes p :: "'a term_pattern" and f :: "'a\<Rightarrow>local_address"
    and b r s t :: local_address
  assumes pattern: "pattern_formed p" and addressing: "binder_addressing (pattern_variables p) f"
    and positions: "distinct [b,r,s,t]"
      "{b,r,s,t}\<inter>rra_carrier (object_structure (pattern_syntax f p))={}"
      "\<forall>a\<in>{b,r,s,t}. octets_formed a"
begin

abbreviation body where "body \<equiv> pattern_syntax f p"
abbreviation variables where "variables \<equiv> f ` pattern_variables p"
abbreviation literals where "literals \<equiv> pattern_literal_bindings p"
abbreviation framed where "framed \<equiv> scope_wrapper body variables b r s t"

lemma body_formed: "exact_formed body" by (rule pattern_syntax_formed[OF pattern addressing])

lemma carrier: "rra_carrier (object_structure body)=pattern_syntax_interior p\<union>rel_dom literals\<union>variables"
  by (rule pattern_syntax_carrier[OF addressing])

lemma variables_inside: "variables\<subseteq>rra_carrier (object_structure body)" using carrier by blast

lemma formed: "exact_formed framed"
  by (rule scope_wrapper_formed[OF body_formed pattern_syntax_root variables_inside positions(3)])

lemma injective: "inj_on f (pattern_variables p)"
  using addressing by (simp add: binder_addressing_def finite_addressing_def)

lemma profile: "reference_table_formed literals {}"
  by (rule reference_table_literals[OF pattern_literal_bindings_finite
    pattern_literal_bindings_functional pattern_literal_bindings_formed[OF pattern]])

lemma bounds: "rel_dom literals\<subseteq>rra_carrier (object_structure framed)"
  using carrier by (auto simp: scope_wrapper_def)

lemma counts: "bag_count (object_data framed)=(\<lambda>_. 0)" by (simp add: scope_wrapper_def)
lemma root: "r\<in>rra_carrier (object_structure framed)" by (simp add: scope_wrapper_def)

lemma recover:
  assumes ef: "environment_formed E" and source: "artifact_at E u framed"
    and refs: "syntax_references E u literals {}"
  shows "\<exists>I K. scoped_pattern_at E u r (rename_pattern f p) I K \<and>
    rra_carrier (object_structure framed)=I\<union>K"
proof -
  have literal_values: "\<forall>k\<in>rel_dom literals. external_slot_values E u k={R. (k,R)\<in>literals}"
    by (intro ballI) (rule reference_literal_values[OF refs pattern_literal_bindings_functional]; assumption)
  show ?thesis using scoped_pattern_syntax_recovers[OF pattern addressing positions ef source literal_values] by blast
qed

end

theorem interface_syntax_total:
  assumes formed: "pattern_formed p"
  shows "\<exists>R r f L. exact_formed R \<and> inj_on f (pattern_variables p) \<and>
    reference_table_formed L {} \<and> rel_dom L \<subseteq> rra_carrier (object_structure R) \<and>
    bag_count (object_data R) = (\<lambda>_. 0) \<and> r \<in> rra_carrier (object_structure R) \<and>
    (\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow>
      syntax_references E u L {} \<longrightarrow>
      (\<exists>I K. scoped_pattern_at E u r (rename_pattern f p) I K \<and>
        rra_carrier (object_structure R) = I \<union> K))"
proof -
  obtain f where addressing: "binder_addressing (pattern_variables p) f"
    using binder_addressing_exists[OF pattern_variables_finite, of p] by blast
  have rf: "exact_formed (pattern_syntax f p)" by (rule pattern_syntax_formed[OF formed addressing])
  have fin: "finite (rra_carrier (object_structure (pattern_syntax f p)))"
    using rf by (simp add: exact_formed_def object_formed_def rra_formed_def)
  obtain b r s t where positions: "distinct [b,r,s,t]"
    "{b,r,s,t}\<inter>rra_carrier (object_structure (pattern_syntax f p))={}"
    "\<forall>a\<in>{b,r,s,t}. octets_formed a"
    using fresh_four_addresses[OF fin] by metis
  interpret code: interface_syntax_construction p f b r s t
    by (rule interface_syntax_construction.intro[OF formed addressing positions])
  show ?thesis by (rule exI[of _ code.framed], rule exI[of _ r], rule exI[of _ f], rule exI[of _ code.literals])
    (use code.formed code.injective code.profile code.bounds code.counts code.root code.recover in blast)
qed

text \<open>
  Every formed interface pattern has a finite scoped code block. Its complete
  variable family is derived from the actual pattern. The native reader
  recovers that pattern in any formed destination supplying the code and its
  literal references. The carrier is exactly the recovered interior and slots.
  This theorem supplies construction facts for enclosing whole definitions;
  no new semantic condition is imposed on the interface language.
\<close>

end
