theory Finite_Relation_Functionality_Execution
  imports RRA_Finite_Artifacts
begin

fun relation_rows_functional :: "('a \<times> 'b) list \<Rightarrow> bool" where
  "relation_rows_functional []=True"
| "relation_rows_functional ((a,b)#xs)=
    (list_all (\<lambda>(c,d). a=c \<longrightarrow> b=d) xs \<and> relation_rows_functional xs)"

lemma single_valued_insert_row:
  "single_valued (insert (a,b) R) \<longleftrightarrow>
    ((\<forall>q\<in>R. a=fst q \<longrightarrow> b=snd q) \<and> single_valued R)"
  by (auto simp: single_valued_def)

theorem relation_rows_functional_exact:
  "relation_rows_functional xs \<longleftrightarrow> single_valued (set xs)"
proof (induction xs)
  case Nil
  then show ?case by (simp add: single_valued_def)
next
  case (Cons x xs)
  then show ?case by (cases x)
    (auto simp: single_valued_insert_row list_all_iff case_prod_unfold)
qed

lemma single_valued_rows_code [code]:
  "single_valued (set xs)=relation_rows_functional xs"
  by (simp only: relation_rows_functional_exact)

declare finite_relation_functional_def[code del]

lemma finite_relation_functional_rows_code [code]:
  "finite_relation_functional F=single_valued (fset F)"
  by (rule finite_relation_functional_correct)

export_code finite_relation_functional checking SML

text \<open>The list traversal compares each row only with following rows.
  Reflexivity supplies the diagonal cases and equality symmetry supplies the
  reverse comparisons. Repeated equal rows are allowed and conflicting values
  at the same key are rejected exactly as before. This matters when values are
  complete large artifacts: proving a table functional does not require
  repeatedly comparing each artifact with itself. No ordering assumption or
  supplied validity flag is introduced.\<close>

end
