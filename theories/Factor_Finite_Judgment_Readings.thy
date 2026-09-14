theory Factor_Finite_Judgment_Readings
  imports Factor_Finite_Complete_Data_Readings Factor_Finite_Judgment_Value_Readers
begin

definition finite_judgment_value_readings where
  "finite_judgment_value_readings C r=ffUnion (fimage
    (\<lambda>t. case finite_judgment_value_read t of None \<Rightarrow> {||} | Some j \<Rightarrow> {|j|})
      (finite_complete_data_readings C r))"

lemma finite_judgment_value_readings_member:
  "j |\<in>| finite_judgment_value_readings C r \<longleftrightarrow>
    (\<exists>t. t |\<in>| finite_complete_data_readings C r \<and> finite_judgment_value_read t=Some j)"
  by (simp only: finite_judgment_value_readings_def finite_union_image_member finite_optional_value_member)

theorem finite_judgment_value_readings_exact:
  "(E,pu,pr,au,ar) |\<in>| finite_judgment_value_readings C r \<longleftrightarrow>
    judgment_value_quoted_at (decode_finite_object C) r (decode_finite_environment E) pu pr au ar"
proof
  assume member: "(E,pu,pr,au,ar) |\<in>| finite_judgment_value_readings C r"
  then show "judgment_value_quoted_at (decode_finite_object C) r (decode_finite_environment E) pu pr au ar"
    by (auto simp: finite_judgment_value_readings_member finite_judgment_value_read_exact
      finite_complete_data_readings_exact judgment_value_quoted_at_def)
next
  assume quoted: "judgment_value_quoted_at (decode_finite_object C) r (decode_finite_environment E) pu pr au ar"
  obtain t where present: "judgment_value_presents (decode_finite_environment E) pu pr au ar t"
    and quote: "complete_data_quoted_at (decode_finite_object C) r t"
    using quoted unfolding judgment_value_quoted_at_def by blast
  obtain T where member: "T |\<in>| finite_complete_data_readings C r" and decode: "decode_finite_term T=t"
    using finite_complete_data_readings_complete[OF quote] by blast
  have recovered: "finite_judgment_value_read T=Some (E,pu,pr,au,ar)"
    using present decode by (simp only: finite_judgment_value_read_exact)
  show "(E,pu,pr,au,ar) |\<in>| finite_judgment_value_readings C r"
    using member recovered by (auto simp: finite_judgment_value_readings_member)
qed

export_code finite_judgment_value_readings checking SML

text \<open>
  Every returned judgment comes from the actual complete quotation. The original
  value relation admits all distinct collection orders and preserves the whole
  environment and both sites. Quotation alone does not establish least scope,
  an admitted program, an actual application, or the truth of the judgment.
\<close>

end
