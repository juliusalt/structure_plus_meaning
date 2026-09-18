theory Finite_Presented_Enumeration
  imports Finite_Presented_Collections Finite_Functional_Enumeration
begin

definition finite_presented_enumeration where
  "finite_presented_enumeration encode A =
    map snd (finite_functional_rows (fimage (\<lambda>a. (Ordered_Factor_Term (encode a),a)) A))"

theorem finite_presented_enumeration_exact:
  assumes injective: "inj encode"
  shows "set (finite_presented_enumeration encode A)=fset A"
proof -
  let ?R="fimage (\<lambda>a. (Ordered_Factor_Term (encode a),a)) A"
  have functional: "finite_relation_functional ?R"
    using injective by (auto simp: finite_relation_functional_correct single_valued_def
      inj_def split: prod.splits)
  show ?thesis
    by (simp add: finite_presented_enumeration_def finite_functional_rows_exact[OF functional]
      fimage.rep_eq image_image)
qed

text \<open>The existing structural term order supplies presentation keys; the
  existing guarded functional enumeration returns the original values. An
  injective complete presentation preserves every member. This ordering is
  transport only and supplies no choice between inequivalent answers.\<close>

ML \<open>val _ = (writeln "Finite_Presented_Enumeration_JOIN_BEGIN";
  Thm.consolidate @{thms finite_presented_enumeration_exact};
  writeln "Finite_Presented_Enumeration_JOIN_END");\<close>

end
