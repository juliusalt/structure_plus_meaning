theory Finite_Inspection_Rows
  imports Finite_Set_Composition
begin

definition finite_inspection_rows where
  "finite_inspection_rows inspect X=fimage (\<lambda>x. (x,inspect x)) X"

lemma finite_inspection_row_exact:
  "(x,b) |\<in>| finite_inspection_rows inspect X \<longleftrightarrow> x |\<in>| X \<and> b=inspect x"
  by (auto simp: finite_inspection_rows_def)

lemma finite_inspection_rows_domain:
  "fimage fst (finite_inspection_rows inspect X)=X"
  by (simp add: finite_inspection_rows_def fimage_fimage comp_def)

definition finite_inspection_rows_hold where
  "finite_inspection_rows_hold R=fBall R snd"

lemma finite_inspection_rows_hold_exact:
  "finite_inspection_rows_hold (finite_inspection_rows inspect X)=fBall X inspect"
  by (auto simp: finite_inspection_rows_hold_def finite_inspection_rows_def Ball_def)

export_code finite_inspection_rows finite_inspection_rows_hold checking SML

text \<open>
  Every actual subject and its computed observation are retained together.
  The projection preserves the complete subject family, and the aggregate
  observation is exactly the conjunction over that family's actual members.
  An arbitrary supplied row family is not identified with this construction.
\<close>

end
