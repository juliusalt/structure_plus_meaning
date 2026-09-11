theory Factor_Executable_Metadata
  imports Factor_Executable_Tables Factor_Executable_Definitions Factor_Executable_Graphs
begin

type_synonym 'u finite_native_node_metadata =
  "('u definition_site,'u definition_site) finite_schema_graph_node \<times>
    ('u definition_site \<times> 'u definition_site) fset"

section \<open>Inference records recover three complete metadata fields\<close>

definition finite_proof_inference_readings ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    local_address list \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow>
    'u finite_native_node_metadata finite_syntax_reading fset" where
  "finite_proof_inference_readings E u r ps c b p =
    ffUnion (fimage (\<lambda>(d,C,A). ffUnion (fimage (\<lambda>(V,B,L).
      ffUnion (fimage (\<lambda>(D,J,W).
        let I=finsert r (fset_of_list ps |\<union>| C |\<union>| B |\<union>| J);
            K=A |\<union>| L |\<union>| W in
        if finsert r (fset_of_list ps) |\<inter>| (C |\<union>| B |\<union>| J)={||} \<and>
          C |\<inter>| B={||} \<and> C |\<inter>| J={||} \<and> B |\<inter>| J={||} \<and>
          I |\<inter>| K={||}
        then {|((Finite_Inference d V,D),I,K)|} else {||})
        (finite_discharge_table_readings E u p))) (finite_binding_table_readings E u b)))
      (finite_site_citation_readings E u c))"

lemma finite_proof_inference_readings_step:
  "((N,D),I,K) |\<in>| finite_proof_inference_readings E u r ps c b p \<longleftrightarrow>
    (\<exists>d V C A B L J W. (d,C,A) |\<in>| finite_site_citation_readings E u c \<and>
      (V,B,L) |\<in>| finite_binding_table_readings E u b \<and>
      (D,J,W) |\<in>| finite_discharge_table_readings E u p \<and> N=Finite_Inference d V \<and>
      finsert r (fset_of_list ps) |\<inter>| (C |\<union>| B |\<union>| J)={||} \<and>
      C |\<inter>| B={||} \<and> C |\<inter>| J={||} \<and> B |\<inter>| J={||} \<and>
      I=finsert r (fset_of_list ps |\<union>| C |\<union>| B |\<union>| J) \<and>
      K=A |\<union>| L |\<union>| W \<and> I |\<inter>| K={||})"
proof
  assume member: "((N,D),I,K) |\<in>| finite_proof_inference_readings E u r ps c b p"
  obtain d C A V B L F J W where citation: "(d,C,A) |\<in>| finite_site_citation_readings E u c"
    and binding: "(V,B,L) |\<in>| finite_binding_table_readings E u b"
    and premise: "(F,J,W) |\<in>| finite_discharge_table_readings E u p"
    and result_shape: "N=Finite_Inference d V" "D=F"
      "I=finsert r (fset_of_list ps |\<union>| C |\<union>| B |\<union>| J)" "K=A |\<union>| L |\<union>| W"
    and geometry: "finsert r (fset_of_list ps) |\<inter>| (C |\<union>| B |\<union>| J)={||}"
      "C |\<inter>| B={||}" "C |\<inter>| J={||}" "B |\<inter>| J={||}"
      "finsert r (fset_of_list ps |\<union>| C |\<union>| B |\<union>| J) |\<inter>| (A |\<union>| L |\<union>| W)={||}"
    using member by (simp only: finite_proof_inference_readings_def finite_union_image_member
        split_paired_Ex prod.case Let_def finite_singleton_when_member prod.inject; auto)
  show "\<exists>d V C A B L J W. (d,C,A) |\<in>| finite_site_citation_readings E u c \<and>
      (V,B,L) |\<in>| finite_binding_table_readings E u b \<and>
      (D,J,W) |\<in>| finite_discharge_table_readings E u p \<and> N=Finite_Inference d V \<and>
      finsert r (fset_of_list ps) |\<inter>| (C |\<union>| B |\<union>| J)={||} \<and>
      C |\<inter>| B={||} \<and> C |\<inter>| J={||} \<and> B |\<inter>| J={||} \<and>
      I=finsert r (fset_of_list ps |\<union>| C |\<union>| B |\<union>| J) \<and>
      K=A |\<union>| L |\<union>| W \<and> I |\<inter>| K={||}"
    apply (rule exI[of _ d], rule exI[of _ V], rule exI[of _ C], rule exI[of _ A])
    apply (rule exI[of _ B], rule exI[of _ L], rule exI[of _ J], rule exI[of _ W])
    using citation binding premise result_shape geometry by simp
next
  assume reading: "\<exists>d V C A B L J W. (d,C,A) |\<in>| finite_site_citation_readings E u c \<and>
      (V,B,L) |\<in>| finite_binding_table_readings E u b \<and>
      (D,J,W) |\<in>| finite_discharge_table_readings E u p \<and> N=Finite_Inference d V \<and>
      finsert r (fset_of_list ps) |\<inter>| (C |\<union>| B |\<union>| J)={||} \<and>
      C |\<inter>| B={||} \<and> C |\<inter>| J={||} \<and> B |\<inter>| J={||} \<and>
      I=finsert r (fset_of_list ps |\<union>| C |\<union>| B |\<union>| J) \<and>
      K=A |\<union>| L |\<union>| W \<and> I |\<inter>| K={||}"
  obtain d V C A B L J W where citation: "(d,C,A) |\<in>| finite_site_citation_readings E u c"
    and binding: "(V,B,L) |\<in>| finite_binding_table_readings E u b"
    and premise: "(D,J,W) |\<in>| finite_discharge_table_readings E u p"
    and result_shape: "N=Finite_Inference d V"
      "I=finsert r (fset_of_list ps |\<union>| C |\<union>| B |\<union>| J)" "K=A |\<union>| L |\<union>| W"
    and geometry: "finsert r (fset_of_list ps) |\<inter>| (C |\<union>| B |\<union>| J)={||}"
      "C |\<inter>| B={||}" "C |\<inter>| J={||}" "B |\<inter>| J={||}" "I |\<inter>| K={||}"
    using reading by auto
  show "((N,D),I,K) |\<in>| finite_proof_inference_readings E u r ps c b p"
    unfolding finite_proof_inference_readings_def finite_union_image_member
    apply (rule exI[of _ "(d,C,A)"])
    apply (simp only: prod.case, rule conjI[OF citation])
    apply (rule iffD2[OF finite_union_image_member], rule exI[of _ "(V,B,L)"])
    apply (simp only: prod.case, rule conjI[OF binding])
    apply (rule iffD2[OF finite_union_image_member], rule exI[of _ "(D,J,W)"])
    apply (simp only: prod.case, rule conjI[OF premise])
    using result_shape geometry by (simp add: Let_def)
qed

lemma finite_proof_inference_readings_sound:
  assumes ef: "environment_formed (decode_finite_environment E)"
    and art: "artifact_at (decode_finite_environment E) u R"
    and rec: "record_at R r ps [c,b,p]"
    and member: "((N,D),I,K) |\<in>| finite_proof_inference_readings E u r ps c b p"
  shows "native_proof_node_at (decode_finite_environment E) u r
    (decode_finite_graph_node N) (fset D) (fset I) (fset K)"
proof -
  obtain d V C A B L J W where citation: "(d,C,A) |\<in>| finite_site_citation_readings E u c"
    and binding: "(V,B,L) |\<in>| finite_binding_table_readings E u b"
    and premise: "(D,J,W) |\<in>| finite_discharge_table_readings E u p"
    and node: "N=Finite_Inference d V"
    and geometry: "finsert r (fset_of_list ps) |\<inter>| (C |\<union>| B |\<union>| J)={||}"
      "C |\<inter>| B={||}" "C |\<inter>| J={||}" "B |\<inter>| J={||}"
      "I=finsert r (fset_of_list ps |\<union>| C |\<union>| B |\<union>| J)"
      "K=A |\<union>| L |\<union>| W" "I |\<inter>| K={||}"
    using member by (simp only: finite_proof_inference_readings_step; auto)
  have citation': "site_citation_at (decode_finite_environment E) u c d (fset C) (fset A)"
    using citation by (simp add: finite_site_citation_readings_correct)
  have binding': "native_binding_table_at (decode_finite_environment E) u b
      (fset (decode_finite_binding_set V)) (fset B) (fset L)"
    using binding by (simp add: finite_binding_table_readings_correct)
  have premise': "native_discharge_table_at (decode_finite_environment E) u p (fset D) (fset J) (fset W)"
    using premise by (simp add: finite_discharge_table_readings_correct)
  have physical: "insert r (set ps) \<inter> (fset C \<union> fset B \<union> fset J)={}"
    "fset C \<inter> fset B={}" "fset C \<inter> fset J={}" "fset B \<inter> fset J={}"
    "insert r (set ps \<union> fset C \<union> fset B \<union> fset J) \<inter>
      (fset A \<union> fset L \<union> fset W)={}"
    using geometry by (simp_all add: fset_inject[symmetric] fset_of_list.rep_eq)
  have recovered: "native_proof_node_at (decode_finite_environment E) u r
      (Schema_Inference d (decode_finite_binding_set V)) (fset D)
      (insert r (set ps \<union> fset C \<union> fset B \<union> fset J)) (fset A \<union> fset L \<union> fset W)"
    by (rule native_proof_node_at.inference[OF ef art rec citation' binding' premise' physical])
  show ?thesis using recovered node geometry(5,6) by (simp add: fset_of_list.rep_eq)
qed

section \<open>Assertions and inferences are read from their actual records\<close>

definition finite_proof_node_readings ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u finite_native_node_metadata finite_syntax_reading fset" where
  "finite_proof_node_readings E u r = (if finite_environment_formed E then
    ffUnion (fimage (\<lambda>C.
      (if ([],[]) |\<in>| finite_record_candidates C r 0
       then {|((Finite_Assertion,{||}),{|r|},{||})|} else {||}) |\<union>|
      finite_three_field_record C r (finite_proof_inference_readings E u r))
      (finite_artifacts_at E u)) else {||})"

lemma finite_proof_node_readings_step:
  "((N,D),I,K) |\<in>| finite_proof_node_readings E u r \<longleftrightarrow>
    finite_environment_formed E \<and> (\<exists>C. C |\<in>| finite_artifacts_at E u \<and>
      ((record_at (decode_finite_object C) r [] [] \<and>
        N=Finite_Assertion \<and> D={||} \<and> I={|r|} \<and> K={||}) \<or>
       (\<exists>ps c b p. record_at (decode_finite_object C) r ps [c,b,p] \<and>
        ((N,D),I,K) |\<in>| finite_proof_inference_readings E u r ps c b p)))"
  by (auto simp: finite_proof_node_readings_def finite_union_image_member
      finite_singleton_when_member finite_three_field_record_member finite_record_candidates_correct
      split: if_splits)

theorem finite_proof_node_readings_sound:
  assumes member: "((N,D),I,K) |\<in>| finite_proof_node_readings E u r"
  shows "native_proof_node_at (decode_finite_environment E) u r
    (decode_finite_graph_node N) (fset D) (fset I) (fset K)"
proof -
  obtain C where formed: "finite_environment_formed E" and source: "C |\<in>| finite_artifacts_at E u"
    and branch: "(record_at (decode_finite_object C) r [] [] \<and>
        N=Finite_Assertion \<and> D={||} \<and> I={|r|} \<and> K={||}) \<or>
       (\<exists>ps c b p. record_at (decode_finite_object C) r ps [c,b,p] \<and>
        ((N,D),I,K) |\<in>| finite_proof_inference_readings E u r ps c b p)"
    using member by (simp only: finite_proof_node_readings_step; blast)
  have ef: "environment_formed (decode_finite_environment E)"
    using formed by (simp add: finite_environment_formed_correct)
  have art: "artifact_at (decode_finite_environment E) u (decode_finite_object C)"
    using source by (simp add: finite_artifacts_at_member)
  consider (assertion) "record_at (decode_finite_object C) r [] []"
      "N=Finite_Assertion" "D={||}" "I={|r|}" "K={||}"
    | (inference) ps c b p where "record_at (decode_finite_object C) r ps [c,b,p]"
      "((N,D),I,K) |\<in>| finite_proof_inference_readings E u r ps c b p"
    using branch by blast
  then show ?thesis
  proof cases
    case assertion
    show ?thesis using native_proof_node_at.assertion[OF ef art assertion(1)] assertion(2-5) by simp
  next
    case (inference ps c b p)
    show ?thesis by (rule finite_proof_inference_readings_sound[OF ef art inference])
  qed
qed

theorem finite_proof_node_readings_complete:
  assumes read: "native_proof_node_at (decode_finite_environment E) u r N D I K"
  shows "\<exists>M F J A. ((M,F),J,A) |\<in>| finite_proof_node_readings E u r \<and>
    decode_finite_graph_node M=N \<and> fset F=D \<and> fset J=I \<and> fset A=K"
proof (cases rule: native_proof_node_at.cases[OF read, case_names assertion inference])
  case (assertion R)
  have ef: "finite_environment_formed E"
    using assertion by (simp add: finite_environment_formed_correct)
  obtain C where source: "C |\<in>| finite_artifacts_at E u" and represented: "decode_finite_object C=R"
    using assertion by (auto simp: finite_artifacts_at_member)
  have rec: "record_at (decode_finite_object C) r [] []" using assertion represented by simp
  have member: "((Finite_Assertion,{||}),{|r|},{||}) |\<in>| finite_proof_node_readings E u r"
    unfolding finite_proof_node_readings_step
    apply (rule conjI[OF ef], rule exI[of _ C], rule conjI[OF source], rule disjI1)
    using rec by simp
  show ?thesis
    by (rule exI[of _ Finite_Assertion], rule exI[of _ "{||}"],
        rule exI[of _ "{|r|}"], rule exI[of _ "{||}"])
       (use member assertion in simp)
next
  case (inference R ps c b p d C A V B L D' J W)
  have ef: "finite_environment_formed E"
    using inference by (simp add: finite_environment_formed_correct)
  obtain T where source: "T |\<in>| finite_artifacts_at E u" and represented: "decode_finite_object T=R"
    using inference by (auto simp: finite_artifacts_at_member)
  have rec: "record_at (decode_finite_object T) r ps [c,b,p]" using inference represented by simp
  have citation: "site_citation_at (decode_finite_environment E) u c d C A"
    and binding: "native_binding_table_at (decode_finite_environment E) u b (fset V) B L"
    and premise: "native_discharge_table_at (decode_finite_environment E) u p D' J W"
    using inference by auto
  obtain CF AF where cite: "(d,CF,AF) |\<in>| finite_site_citation_readings E u c"
    and cite_boundary: "fset CF=C" "fset AF=A"
    using finite_site_citation_readings_complete[OF citation] by blast
  obtain VF BF LF where bind: "(VF,BF,LF) |\<in>| finite_binding_table_readings E u b"
    and bind_boundary: "decode_finite_term_bindings VF=fset V" "fset BF=B" "fset LF=L"
    using finite_binding_table_readings_complete[OF binding] by blast
  obtain DF JF WF where prem: "(DF,JF,WF) |\<in>| finite_discharge_table_readings E u p"
    and prem_boundary: "fset DF=D'" "fset JF=J" "fset WF=W"
    using finite_discharge_table_readings_complete[OF premise] by blast
  let ?I = "finsert r (fset_of_list ps |\<union>| CF |\<union>| BF |\<union>| JF)"
  let ?K = "AF |\<union>| LF |\<union>| WF"
  have physical: "finsert r (fset_of_list ps) |\<inter>| (CF |\<union>| BF |\<union>| JF)={||}"
    "CF |\<inter>| BF={||}" "CF |\<inter>| JF={||}" "BF |\<inter>| JF={||}" "?I |\<inter>| ?K={||}"
    using inference cite_boundary bind_boundary prem_boundary
    by (simp_all add: fset_inject[symmetric] fset_of_list.rep_eq)
  have body: "((Finite_Inference d VF,DF),?I,?K) |\<in>| finite_proof_inference_readings E u r ps c b p"
    unfolding finite_proof_inference_readings_step
    apply (rule exI[of _ d], rule exI[of _ VF], rule exI[of _ CF], rule exI[of _ AF])
    apply (rule exI[of _ BF], rule exI[of _ LF], rule exI[of _ JF], rule exI[of _ WF])
    using cite bind prem physical by simp
  have member: "((Finite_Inference d VF,DF),?I,?K) |\<in>| finite_proof_node_readings E u r"
    unfolding finite_proof_node_readings_step
    apply (rule conjI[OF ef], rule exI[of _ T], rule conjI[OF source], rule disjI2)
    apply (rule exI[of _ ps], rule exI[of _ c], rule exI[of _ b], rule exI[of _ p])
    using rec body by simp
  have bindings: "decode_finite_binding_set VF=V"
    using bind_boundary(1) by (simp add: fset_inject[symmetric])
  show ?thesis
    by (rule exI[of _ "Finite_Inference d VF"], rule exI[of _ DF],
        rule exI[of _ ?I], rule exI[of _ ?K])
       (use member inference cite_boundary bind_boundary prem_boundary bindings
        in \<open>simp add: fset_of_list.rep_eq\<close>)
qed

theorem finite_proof_node_readings_correct:
  "((N,D),I,K) |\<in>| finite_proof_node_readings E u r \<longleftrightarrow>
    native_proof_node_at (decode_finite_environment E) u r
      (decode_finite_graph_node N) (fset D) (fset I) (fset K)"
proof
  assume "((N,D),I,K) |\<in>| finite_proof_node_readings E u r"
  then show "native_proof_node_at (decode_finite_environment E) u r
      (decode_finite_graph_node N) (fset D) (fset I) (fset K)"
    by (rule finite_proof_node_readings_sound)
next
  assume read: "native_proof_node_at (decode_finite_environment E) u r
    (decode_finite_graph_node N) (fset D) (fset I) (fset K)"
  show "((N,D),I,K) |\<in>| finite_proof_node_readings E u r"
    using finite_proof_node_readings_complete[OF read] by (auto simp: fset_inject)
qed

corollary finite_proof_node_readings_unique:
  assumes "((N,D),I,K) |\<in>| finite_proof_node_readings E u r"
    "((M,F),J,A) |\<in>| finite_proof_node_readings E u r"
  shows "N=M \<and> D=F \<and> I=J \<and> K=A"
proof -
  have first: "native_proof_node_at (decode_finite_environment E) u r
      (decode_finite_graph_node N) (fset D) (fset I) (fset K)"
    and second: "native_proof_node_at (decode_finite_environment E) u r
      (decode_finite_graph_node M) (fset F) (fset J) (fset A)"
    using assms by (simp_all add: finite_proof_node_readings_correct)
  show ?thesis using native_proof_node_unique[OF first second] by (simp add: fset_inject)
qed

export_code finite_proof_node_readings checking SML

text \<open>
  The empty assertion record and the three-field inference record are recovered
  with their complete metadata. Inferences retain the actual clause site, every
  binding, and every premise link. The record frame, field interiors, and external
  slots satisfy exactly the native geometry. Reading this metadata does not
  establish the claimed inference; the program and its exact premises determine
  that check.
\<close>

end
