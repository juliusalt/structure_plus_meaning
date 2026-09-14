theory RRA_Finite_Generation_Checking
  imports RRA_Finite_Generation_Readings RRA_Generation_Child_Assignments
begin

definition finite_generation_child_rows where
  "finite_generation_child_rows E u M checks=ffUnion (fimage (\<lambda>(G,check).
    fimage (\<lambda>(s,d). (s,G)) (ffilter (\<lambda>(s,d).
      fBex (finite_located_values E u d) (\<lambda>(v,a). check E v a)) M)) checks)"

lemma finite_generation_child_rows_member:
  "(s,G) |\<in>| finite_generation_child_rows E u M (fimage (\<lambda>H. (H,check H)) P) \<longleftrightarrow>
    G |\<in>| P \<and> (\<exists>d. (s,d) |\<in>| M \<and>
      (\<exists>v a. (v,a) |\<in>| finite_located_values E u d \<and> check G E v a))"
  by (auto simp: finite_generation_child_rows_def finite_union_image_member
    finite_image_member split_paired_Ex split: prod.splits; force)

lemma finite_generation_child_rows_relation:
  "fset (finite_generation_child_rows E u M (fimage (\<lambda>H. (H,check H)) P))=
    child_assignment_relation (fset M) (fset P)
      (\<lambda>d H. \<exists>v a. (v,a) |\<in>| finite_located_values E u d \<and> check H E v a)"
  by (rule set_eqI; rename_tac row; case_tac row;
    simp only: finite_generation_child_rows_member child_assignment_relation_member)

function (sequential) finite_check_generation :: "finite_generation\<Rightarrow>'u finite_artifact_environment\<Rightarrow>
    'u\<Rightarrow>local_address\<Rightarrow>bool" where
  "finite_check_generation (Generation l P p c) E u r=
    fBex (finite_generation_field_readings E u r) (\<lambda>(l',M,p',c').
      l=l' \<and> p=p' \<and> c=c' \<and>
      finite_bijective_relation (fimage fst M) P
        (finite_generation_child_rows E u M (fimage (\<lambda>H. (H,finite_check_generation H)) P)))"

  by pat_completeness auto

termination
  apply (relation "measure (size \<circ> fst)")
   apply (rule wf_measure)
  apply (simp only: in_measure comp_apply fst_conv)
  apply (rule predecessor_size_decreases)
  apply (simp add: predecessor_edges_def)
  done

lemma finite_check_generation_node:
  "finite_check_generation (Generation l P p c) E u r \<longleftrightarrow>
    (\<exists>M. (l,M,p,c) |\<in>| finite_generation_field_readings E u r \<and>
      finite_bijective_relation (fimage fst M) P
        (finite_generation_child_rows E u M (fimage (\<lambda>H. (H,finite_check_generation H)) P)))"
  by (auto simp: Bex_def split_paired_Ex)

theorem finite_check_generation_exact:
  "finite_check_generation G E u r \<longleftrightarrow>
    generation_at (decode_finite_environment E) u r (decode_finite_generation G)"
proof (induction G arbitrary: E u r)
  case (Generation l P p c)
  let ?D="decode_finite_generation"
  let ?F="decode_finite_environment E"
  let ?Ps="fimage ?D P"
  let ?rows="\<lambda>M. finite_generation_child_rows E u M
    (fimage (\<lambda>H. (H,finite_check_generation H)) P)"
  have recursive: "finite_check_generation H E v a=generation_at ?F v a (?D H)"
    if "H |\<in>| P" for H v a using Generation.IH that by blast
  have relation: "fset (fimage (map_prod id ?D) (?rows M))=
    child_assignment_relation (fset M) (fset ?Ps)
      (\<lambda>d H. \<exists>v a. located_at ?F u d v a \<and> generation_at ?F v a H)" for M
  proof -
    have related: "(\<exists>v a. (v,a) |\<in>| finite_located_values E u d \<and> finite_check_generation H E v a)=
      (\<exists>v a. located_at ?F u d v a \<and> generation_at ?F v a (?D H))"
      if "H\<in>fset P" for d H
      by (simp only: finite_located_values_correct fst_conv snd_conv recursive[OF that])
    show ?thesis
      apply (subst finite_value_image_relation)
      apply (subst finite_generation_child_rows_relation)
      apply (simp only: fimage.rep_eq)
      apply (rule child_assignment_relation_image)
      apply (rule related)
      apply assumption
      done
  qed
  have injective: "inj ?D" by (simp add: inj_def)
  have each: "finite_bijective_relation (fimage fst M) P (?rows M) \<longleftrightarrow>
    generation_at ?F u r (Generation (decode_finite_target l) ?Ps
      (decode_finite_target p) (decode_finite_target c))"
    if field: "(l,M,p,c) |\<in>| finite_generation_field_readings E u r" for M
  proof -
    have original: "generation_fields_at ?F u r (decode_finite_target l) (fset M)
      (decode_finite_target p) (decode_finite_target c)"
      using field by (simp only: finite_generation_field_readings_correct)
    show ?thesis
      apply (subst finite_bijective_relation_value_map[OF injective, symmetric])
      apply (simp only: finite_bijective_relation_graph)
      apply (subst relation)
      by (simp only: generation_at_child_relation[OF original]
        rel_dom_image fimage.rep_eq)
  qed
  show ?case
  proof
    assume checked: "finite_check_generation (Generation l P p c) E u r"
    show "generation_at ?F u r (?D (Generation l P p c))"
      using checked each by (simp only: finite_check_generation_node decode_finite_generation_node; blast)
  next
    assume native: "generation_at ?F u r (?D (Generation l P p c))"
    obtain M where original: "generation_fields_at ?F u r (decode_finite_target l) M
      (decode_finite_target p) (decode_finite_target c)"
      using native by (cases rule: generation_at.cases) (auto simp: decode_finite_generation_node)
    have finite: "finite M" using generation_fields_formed[OF original] by blast
    have represented: "fset (Abs_fset M)=M" by (rule Abs_fset_inverse) (simp add: finite)
    have field: "(l,Abs_fset M,p,c) |\<in>| finite_generation_field_readings E u r"
      by (simp only: finite_generation_field_readings_correct represented; rule original)
    show "finite_check_generation (Generation l P p c) E u r"
      using native field each[OF field]
      by (simp only: finite_check_generation_node decode_finite_generation_node; blast)
  qed
qed

corollary finite_check_generation_unique:
  assumes "finite_check_generation G E u r" "finite_check_generation H E u r"
  shows "G=H"
  using generation_at_unique[OF assms[unfolded finite_check_generation_exact]] by simp

corollary finite_check_generation_formed:
  "finite_check_generation G E u r \<Longrightarrow> finite_generation_formed G"
  using generation_at_formed by (simp only: finite_check_generation_exact finite_generation_formed_correct)

corollary finite_check_generation_position:
  assumes checked: "finite_check_generation G E u r"
  shows "(u,r) |\<in>| finite_environment_positions E"
  using generation_at_has_anchor[OF checked[unfolded finite_check_generation_exact]]
  by (auto simp: finite_environment_positions_correct environment_positions_def anchor_formed_def)

export_code finite_check_generation checking SML

text \<open>
  The checker reads the actual source fields and resolves every predecessor
  citation. Recursive checks follow the supplied complete finite core; all
  required sockets and exactly the distinct predecessor values must match.
  The condition is the original RRA generation reading on every input. No
  supplied satisfaction table, cause-validity claim or historical permission
  enters the calculation.
\<close>

end
