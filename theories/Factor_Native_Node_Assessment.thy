theory Factor_Native_Node_Assessment
  imports Factor_Native_Node_Cases Finite_Unique_Inspections
begin

definition native_node_ready :: "native_node_problem\<Rightarrow>bool" where
  "native_node_ready X=(case X of (E,N,D) \<Rightarrow> finite_proof_node_installable E N D)"

definition native_node_ready_condition :: "native_node_problem\<Rightarrow>bool" where
  "native_node_ready_condition X=(case X of (E,N,D) \<Rightarrow>
    environment_formed (decode_finite_environment E) \<and>
    graph_node_inputs_at (decode_finite_environment E) (fset D) (decode_finite_graph_node N) \<and>
    single_valued (fset D) \<and> (\<forall>s n. (s,n)\<in>fset D \<longrightarrow> octets_formed (snd n)) \<and>
    rel_ran (fset D)\<subseteq>environment_positions (decode_finite_environment E))"

lemma native_node_ready_exact:
  "native_node_ready X=native_node_ready_condition X"
  by (simp add: native_node_ready_def native_node_ready_condition_def finite_proof_node_installable_def
    finite_proof_node_ready_exact less_eq_fset.rep_eq fimage.rep_eq rel_ran_image
    finite_environment_positions_correct split: prod.splits)

definition native_node_reading_field where
  "native_node_reading_field (f::nat) N D readings=fBex readings (\<lambda>((M,T),I,K).
    if f=1 then M=N else T=D)"

definition native_node_reading_condition where
  "native_node_reading_condition (f::nat) N D F u=(\<exists>M T I K.
    native_proof_node_at (decode_finite_environment F) u [] (decode_finite_graph_node M)
      (fset T) (fset I) (fset K) \<and> (if f=1 then M=N else T=D))"

lemma native_node_reading_field_exact:
  "native_node_reading_field f N D (finite_proof_node_readings F u [])=
    native_node_reading_condition f N D F u"
  by (simp only: native_node_reading_field_def native_node_reading_condition_def
    Bex_def split_paired_Ex case_prod_conv finite_proof_node_readings_correct)

lemma native_node_reading_fields_complete:
  "native_node_reading_field 1 N D (finite_proof_node_readings F u []) \<and>
    native_node_reading_field 2 N D (finite_proof_node_readings F u []) \<longleftrightarrow>
      (\<exists>I K. ((N,D),I,K) |\<in>| finite_proof_node_readings F u [])"
proof -
  have unique: "x=y" if "x |\<in>| finite_proof_node_readings F u []"
    "y |\<in>| finite_proof_node_readings F u []" for x y
    using that by (cases x; cases y) (auto dest: finite_proof_node_readings_unique)
  have combined: "fBex (finite_proof_node_readings F u []) (\<lambda>((M,T),I,K). M=N) \<and>
      fBex (finite_proof_node_readings F u []) (\<lambda>((M,T),I,K). T=D) \<longleftrightarrow>
    fBex (finite_proof_node_readings F u []) (\<lambda>x.
      (case x of ((M,T),I,K) \<Rightarrow> M=N) \<and> (case x of ((M,T),I,K) \<Rightarrow> T=D))"
    using finite_unique_inspection_conjunction[where R="finite_proof_node_readings F u []"
      and P="\<lambda>x. fst (fst x)=N" and Q="\<lambda>x. snd (fst x)=D", OF unique]
    by (simp only: split_def)
  show ?thesis using combined by (auto simp: native_node_reading_field_def Bex_def split_paired_Ex case_prod_conv)
qed

definition native_node_result_condition :: "nat\<Rightarrow>native_node_problem\<Rightarrow>native_node_result\<Rightarrow>bool" where
  "native_node_result_condition (f::nat) X result=(case X of (E,N,D) \<Rightarrow>
    case result of None \<Rightarrow> False | Some (F,u) \<Rightarrow>
      if f=0 then environment_formed (decode_finite_environment F)
      else if f=1 \<or> f=2 then native_node_reading_condition f N D F u
      else if f=3 then environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
        (\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
          artifact_at (decode_finite_environment E) w A \<longleftrightarrow> artifact_at (decode_finite_environment F) w A) \<and>
        (\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
          binds_slot (decode_finite_environment E) w k v \<longleftrightarrow> binds_slot (decode_finite_environment F) w k v)
      else if f=4 then u\<notin>environment_uses (decode_finite_environment E) else False)"

definition native_node_condition ::
    "nat\<Rightarrow>(native_node_problem\<Rightarrow>native_node_result)\<Rightarrow>native_node_problem\<Rightarrow>bool" where
  "native_node_condition (f::nat) method X=(if f=5 then
    (\<not>native_node_ready_condition X \<longrightarrow> method X=None)
    else if f<5 then (native_node_ready_condition X \<longrightarrow> native_node_result_condition f X (method X)) else False)"

definition native_node_assessment where
  "native_node_assessment X result=(case X of (E,N,D) \<Rightarrow>
    (native_node_ready X,map_option (\<lambda>(F,u). let readings=finite_proof_node_readings F u [] in
      (readings,finite_environment_formed F,native_node_reading_field 1 N D readings,
        native_node_reading_field 2 N D readings,
        finite_environment_included E F \<and> finite_environment_agrees_on E F (finite_environment_uses E),
        u |\<notin>| finite_environment_uses E)) result,result=None))"

definition native_node_inspect where
  "native_node_inspect A (f::nat)=(case A of (ready,body,rejected) \<Rightarrow>
    if f=5 then (\<not>ready \<longrightarrow> rejected) else if f<5 then (ready \<longrightarrow>
      (case body of None \<Rightarrow> False | Some (readings,formed,node,targets,source,fresh) \<Rightarrow>
        if f=0 then formed else if f=1 then node else if f=2 then targets else if f=3 then source else fresh)) else False)"

theorem native_node_assessment_exact:
  "native_node_inspect (native_node_assessment X (method X)) f=native_node_condition f method X"
  by (auto simp: native_node_assessment_def native_node_inspect_def native_node_condition_def
    native_node_ready_exact native_node_result_condition_def native_node_reading_field_exact
    finite_environment_formed_correct finite_environment_included_correct finite_environment_agrees_on_correct
    finite_environment_uses_correct Let_def split: prod.splits option.splits if_splits; arith)

export_code native_node_assessment native_node_inspect checking SML

text \<open>
  The actual returned environment supplies every finite native reading. The
  node and discharge inspections preserve distinct complete fields of those
  readings. Formation, source inclusion and complete preservation, freshness,
  availability and refusal retain their independent original conditions.
  A smaller comparison basis cannot remove an adequacy requirement.
  Reading a node's metadata does not establish its inference or mathematical
  validity; the universal compiler contract and later proof checks remain
  separate requirements.
\<close>

end
