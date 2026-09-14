theory Finite_Map_Observations
  imports Finite_Assessment_Reports
begin

definition finite_map_rows where
  "finite_map_rows A h=fimage (\<lambda>x. (x,h x)) A"

definition finite_map_injective where
  "finite_map_injective rows=fBall rows (\<lambda>(x,a).
    fBall rows (\<lambda>(y,b). a=b \<longrightarrow> x=y))"

definition finite_map_preserves where
  "finite_map_preserves rows P=fBall rows (\<lambda>(x,y). P x y)"

lemma finite_map_injective_exact:
  "finite_map_injective (finite_map_rows A h)=inj_on h (fset A)"
  by (auto simp: finite_map_injective_def finite_map_rows_def fimage.rep_eq inj_on_def Ball_def)

lemma finite_map_preserves_exact:
  "finite_map_preserves (finite_map_rows A h) P=(\<forall>x\<in>fset A. P x (h x))"
  by (auto simp: finite_map_preserves_def finite_map_rows_def fimage.rep_eq Ball_def)

definition list_suffix_check where
  "list_suffix_check a b=(length a\<le>length b \<and> drop (length b-length a) b=a)"

lemma list_suffix_check_exact:
  "list_suffix_check a b \<longleftrightarrow> (\<exists>p. b=p@a)"
proof
  assume check: "list_suffix_check a b"
  have "b=take (length b-length a) b@a"
    using check append_take_drop_id[of "length b-length a" b]
    by (auto simp only: list_suffix_check_def)
  then show "\<exists>p. b=p@a" by blast
next
  assume "\<exists>p. b=p@a"
  then show "list_suffix_check a b" by (auto simp: list_suffix_check_def)
qed

text \<open>
  Actual function graphs determine finite injectivity and preservation of an
  independently supplied input/output relation. No observation cell is supplied.
  The suffix operation checks precisely existence of an unchanged suffix.
\<close>

end
