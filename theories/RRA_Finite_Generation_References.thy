theory RRA_Finite_Generation_References
  imports RRA_Finite_Generation_Readings RRA_Generation_References
begin

definition finite_generation_predecessor_references where
  "finite_generation_predecessor_references E u r l p c=ffUnion (fimage (\<lambda>(l',M,p',c').
    if l=l' \<and> p=p' \<and> c=c' then
      ffUnion (fimage (\<lambda>(s,d). finite_located_values E u d) M) else {||})
      (finite_generation_field_readings E u r))"

lemma finite_generation_predecessor_references_member:
  "(v,a) |\<in>| finite_generation_predecessor_references E u r l p c \<longleftrightarrow>
    (\<exists>M s d. (l,M,p,c) |\<in>| finite_generation_field_readings E u r \<and>
      (s,d) |\<in>| M \<and> (v,a) |\<in>| finite_located_values E u d)"
  by (auto simp: finite_generation_predecessor_references_def finite_union_image_member
    split_paired_Ex split: if_splits)

theorem finite_generation_predecessor_references_correct:
  fixes E :: "'u finite_artifact_environment"
  shows "fset (finite_generation_predecessor_references E u r l p c)=
    generation_predecessor_references (decode_finite_environment E) u r
      (decode_finite_target l) (decode_finite_target p) (decode_finite_target c)"
proof (rule set_eqI)
  fix z :: "'u\<times>local_address"
  obtain v a where z: "z=(v,a)" by (cases z) auto
  show "z\<in>fset (finite_generation_predecessor_references E u r l p c) \<longleftrightarrow>
    z\<in>generation_predecessor_references (decode_finite_environment E) u r
      (decode_finite_target l) (decode_finite_target p) (decode_finite_target c)"
  proof
    assume "z\<in>fset (finite_generation_predecessor_references E u r l p c)"
    then show "z\<in>generation_predecessor_references (decode_finite_environment E) u r
      (decode_finite_target l) (decode_finite_target p) (decode_finite_target c)"
      by (auto simp: z finite_generation_predecessor_references_member
        generation_predecessor_references_member finite_generation_field_readings_correct
        finite_located_values_correct)
  next
    assume "z\<in>generation_predecessor_references (decode_finite_environment E) u r
      (decode_finite_target l) (decode_finite_target p) (decode_finite_target c)"
    then obtain M s d where fields: "generation_fields_at (decode_finite_environment E) u r
      (decode_finite_target l) M (decode_finite_target p) (decode_finite_target c)"
      and row: "(s,d)\<in>M" and location: "located_at (decode_finite_environment E) u d v a"
      by (simp only: z generation_predecessor_references_member; blast)
    have finite: "finite M" using generation_fields_formed[OF fields] by blast
    have represented: "fset (Abs_fset M)=M" by (rule Abs_fset_inverse) (simp add: finite)
    have native: "(l,Abs_fset M,p,c) |\<in>| finite_generation_field_readings E u r"
      by (simp only: finite_generation_field_readings_correct represented; rule fields)
    have finite_row: "(s,d) |\<in>| Abs_fset M" using row by (simp only: represented)
    have finite_location: "(v,a) |\<in>| finite_located_values E u d"
      using location by (simp only: finite_located_values_correct fst_conv snd_conv)
    show "z\<in>fset (finite_generation_predecessor_references E u r l p c)"
      using native finite_row finite_location
      by (simp only: z finite_generation_predecessor_references_member; blast)
  qed
qed

export_code finite_generation_predecessor_references checking SML

end
