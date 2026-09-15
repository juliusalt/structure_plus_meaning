theory Finite_Reader_Identity_Maps
  imports Finite_Relation_Reader_Assessments Finite_Set_Composition
begin

lemma optional_identity_map_injective:
  assumes each: "\<And>x y. encode x=encode y \<longleftrightarrow> x=y"
  shows "map_option encode x=map_option encode y \<longleftrightarrow> x=y"
  by (cases x; cases y) (simp_all add: each)

lemma finite_reader_inspect_identity_map:
  assumes each: "\<And>x y. encode x=encode y \<longleftrightarrow> x=y"
  shows "finite_reader_inspect (fimage encode result,fimage encode reference) f=
    finite_reader_inspect (result,reference) f"
  by (auto simp: finite_reader_inspect_def Ball_def fimage.rep_eq each)

text \<open>
  Injective value presentation preserves both complete reader conditions for
  arbitrary candidate and reference families. The map does not establish the
  reference relation or any candidate's satisfaction; their original exact
  contracts remain the premises of a subject assessment.
\<close>

end
