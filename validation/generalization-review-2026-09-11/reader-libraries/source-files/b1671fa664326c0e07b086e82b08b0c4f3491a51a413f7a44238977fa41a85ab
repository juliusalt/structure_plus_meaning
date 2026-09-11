theory Factor_Library_Compilation
  imports Factor_Learned_Investigation Finite_Functional_Enumeration
begin

section \<open>A schema supplies its own complete premise enumeration\<close>

definition finite_compiled_library ::
  "('d\<times>('a,'s::linorder,'d) finite_factor_schema) list \<Rightarrow>
    ('d\<times>('a,'s,'d) finite_factor_schema\<times>('s\<times>'d\<times>'a finite_term_pattern) list) list" where
  "finite_compiled_library sources=map (\<lambda>(d,S).
    (d,S,finite_functional_rows (finite_schema_premises S))) sources"

lemma finite_compiled_library_member:
  "(d,S,ps)\<in>set (finite_compiled_library sources) \<longleftrightarrow>
    (d,S)\<in>set sources \<and> ps=finite_functional_rows (finite_schema_premises S)"
  by (auto simp: finite_compiled_library_def)

lemma finite_compiled_schema_enumeration:
  assumes formed: "finite_schema_formed S"
  shows "set (finite_functional_rows (finite_schema_premises S))=fset (finite_schema_premises S)"
  by (rule finite_functional_rows_exact) (use formed in \<open>simp add: finite_schema_formed_def\<close>)

theorem finite_compiled_library_formed:
  "finite_schema_library_formed (finite_compiled_library sources) \<longleftrightarrow>
    (\<forall>(d,S)\<in>set sources. finite_schema_formed S)"
proof
  assume checked: "finite_schema_library_formed (finite_compiled_library sources)"
  have formed: "finite_schema_formed S" if "(d,S)\<in>set sources" for d S
  proof -
    have member: "(d,S,finite_functional_rows (finite_schema_premises S))\<in>set (finite_compiled_library sources)"
      using that by (simp only: finite_compiled_library_member)
    show ?thesis using checked member by (auto simp: finite_schema_library_formed_def)
  qed
  show "\<forall>(d,S)\<in>set sources. finite_schema_formed S" using formed by auto
next
  assume source_formed: "\<forall>(d,S)\<in>set sources. finite_schema_formed S"
  have complete: "finite_schema_formed S \<and> set ps=fset (finite_schema_premises S)"
    if "(d,S,ps)\<in>set (finite_compiled_library sources)" for d S ps
  proof -
    have source: "(d,S)\<in>set sources"
      using that by (simp only: finite_compiled_library_member; blast)
    have enumeration: "ps=finite_functional_rows (finite_schema_premises S)"
      using that by (simp only: finite_compiled_library_member; blast)
    have formed: "finite_schema_formed S" using source_formed source by auto
    show ?thesis using formed finite_compiled_schema_enumeration[OF formed] by (simp only: enumeration)
  qed
  show "finite_schema_library_formed (finite_compiled_library sources)"
    using complete by (auto simp: finite_schema_library_formed_def)
qed

definition natural_compiled_library where
  "natural_compiled_library (sources::(nat\<times>(nat,nat,nat) finite_factor_schema) list)=
    finite_compiled_library sources"

section \<open>Closed native clause syntax reduces to the existing finite representation\<close>

lemma finite_set_empty_encoding [simp]: "Abs_fset {}={||}"
  by (rule fset_inject[THEN iffD1]) (simp add: Abs_fset_inverse)

lemma finite_set_insert_encoding [simp]:
  "finite A \<Longrightarrow> Abs_fset (insert a A)=finsert a (Abs_fset A)"
  by (rule fset_inject[THEN iffD1]) (simp add: Abs_fset_inverse)

text \<open>
  The original schema is retained even when malformed, so the whole library
  formation gate still rejects it. A valid schema generates its enumeration
  from the actual complete premise family. The finite representation theorem
  then permits native clauses to be compiled without restating their fields.
\<close>

end
