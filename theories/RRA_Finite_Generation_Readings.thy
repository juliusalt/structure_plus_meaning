theory RRA_Finite_Generation_Readings
  imports RRA_Finite_Generations Factor_Executable_Packages
begin

definition finite_anchored_targets where
  "finite_anchored_targets E u r=ffUnion (fimage (\<lambda>C.
    ffUnion (fimage (\<lambda>(c,I). finite_citation_targets E u c)
      (finite_citation_candidates C r))) (finite_artifacts_at E u))"

lemma finite_anchored_targets_member:
  "t |\<in>| finite_anchored_targets E u r \<longleftrightarrow>
    (\<exists>C c I. C |\<in>| finite_artifacts_at E u \<and>
      (c,I) |\<in>| finite_citation_candidates C r \<and>
      t |\<in>| finite_citation_targets E u c)"
  by (auto simp: finite_anchored_targets_def finite_union_image_member split_paired_Ex)

theorem finite_anchored_targets_correct:
  "t |\<in>| finite_anchored_targets E u r \<longleftrightarrow>
    anchored_at (decode_finite_environment E) u r (decode_finite_target t)"
proof
  assume member: "t |\<in>| finite_anchored_targets E u r"
  then show "anchored_at (decode_finite_environment E) u r (decode_finite_target t)"
    by (auto simp: finite_anchored_targets_member finite_artifacts_at_member
      finite_citation_candidates_correct finite_citation_targets_member anchored_at_def)
next
  assume anchored: "anchored_at (decode_finite_environment E) u r (decode_finite_target t)"
  obtain C c I where source: "C |\<in>| finite_artifacts_at E u"
    and citation: "citation_at (decode_finite_object C) r c I"
    and target: "interpret_citation (decode_finite_environment E) u c (decode_finite_target t)"
    using anchored by (auto simp: anchored_at_def finite_artifacts_at_complete finite_artifacts_at_member)
  obtain F where read: "(c,F) |\<in>| finite_citation_candidates C r"
    using finite_citation_candidates_complete[OF citation] by blast
  show "t |\<in>| finite_anchored_targets E u r"
    using source read target by (simp only: finite_anchored_targets_member
      finite_citation_targets_member; blast)
qed

lemma length_four_decomposition:
  "length xs=4 \<longleftrightarrow> (\<exists>a b c d. xs=[a,b,c,d])"
  by (simp add: eval_nat_numeral length_Suc_conv; blast)

definition finite_generation_field_readings where
  "finite_generation_field_readings E u r=(if finite_environment_formed E then
    ffUnion (fimage (\<lambda>C. ffUnion (fimage (\<lambda>(ps,xs).
      if length xs=4 then let lr=xs!0; pr=xs!1; payr=xs!2; cr=xs!3 in
        ffUnion (fimage (\<lambda>l. ffUnion (fimage (\<lambda>M.
          ffUnion (fimage (\<lambda>p. fimage (\<lambda>c. (l,M,p,c))
            (finite_anchored_targets E u cr)) (finite_anchored_targets E u payr)))
          (finite_family_candidates C pr))) (finite_anchored_targets E u lr))
      else {||}) (finite_record_candidates C r 4)))
      (finite_artifacts_at E u)) else {||})"

lemma finite_generation_field_readings_member:
  "(l,M,p,c) |\<in>| finite_generation_field_readings E u r \<longleftrightarrow>
    finite_environment_formed E \<and> (\<exists>C ps lr pr payr cr.
      C |\<in>| finite_artifacts_at E u \<and>
      (ps,[lr,pr,payr,cr]) |\<in>| finite_record_candidates C r 4 \<and>
      M |\<in>| finite_family_candidates C pr \<and>
      l |\<in>| finite_anchored_targets E u lr \<and>
      p |\<in>| finite_anchored_targets E u payr \<and>
      c |\<in>| finite_anchored_targets E u cr)"
  by (auto simp: finite_generation_field_readings_def finite_union_image_member
    finite_image_member length_four_decomposition Let_def split_paired_Ex split: if_splits; force)

theorem finite_generation_field_readings_correct:
  "(l,M,p,c) |\<in>| finite_generation_field_readings E u r \<longleftrightarrow>
    generation_fields_at (decode_finite_environment E) u r
      (decode_finite_target l) (fset M) (decode_finite_target p) (decode_finite_target c)"
  by (auto simp: finite_generation_field_readings_member generation_fields_at_def
    finite_environment_formed_correct finite_artifacts_at_complete finite_artifacts_at_member finite_record_candidates_correct
    finite_family_candidates_correct finite_anchored_targets_correct; force)

lemma finite_generation_field_readings_unique:
  assumes "(l,M,p,c) |\<in>| finite_generation_field_readings E u r"
    "(l',M',p',c') |\<in>| finite_generation_field_readings E u r"
  shows "l=l' \<and> M=M' \<and> p=p' \<and> c=c'"
  using generation_fields_unique[OF assms[unfolded finite_generation_field_readings_correct]]
  by (simp add: fset_inject)

export_code finite_anchored_targets finite_generation_field_readings checking SML

text \<open>
  The four field roles and complete predecessor socket family come from the
  actual record incidence. Every target follows the original citation and its
  actual environment binding. Reading these fields does not check recursive
  predecessors or interpret the cause target as permission.
\<close>

end
