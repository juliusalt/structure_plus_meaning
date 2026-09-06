theory Factor_Executable_Tables
  imports Factor_Executable_References Factor_Executable_Families Factor_Proof_Metadata
begin

section \<open>Finite rows retain their values and physical boundaries\<close>

definition decode_finite_reading ::
  "('a \<Rightarrow> 'b) \<Rightarrow> 'a finite_syntax_reading \<Rightarrow>
    'b \<times> local_address set \<times> local_address set" where
  "decode_finite_reading D x = (D (fst x), fset (fst (snd x)), fset (snd (snd x)))"

lemma decode_finite_reading_tuple [simp]:
  "decode_finite_reading D (q,I,K) = (D q,fset I,fset K)"
  by (simp add: decode_finite_reading_def)

lemma decode_finite_reading_inj:
  assumes "inj D"
  shows "inj (decode_finite_reading D)"
  using assms by (auto simp: inj_def decode_finite_reading_def fset_inject
      split: prod.splits)

lemma decoded_finite_row_member:
  "(s,q,J,A) \<in> map_relation_values (decode_finite_reading D) (fset H) \<longleftrightarrow>
    (\<exists>p I K. (s,p,I,K) |\<in>| H \<and> q=D p \<and> J=fset I \<and> A=fset K)"
  by (simp only: map_relation_values_member split_paired_Ex
      decode_finite_reading_tuple prod.inject; blast)

lemma decoded_finite_rowI:
  assumes "(s,q,I,K) |\<in>| H"
  shows "(s,D q,fset I,fset K) \<in> map_relation_values (decode_finite_reading D) (fset H)"
  by (rule iffD2[OF map_relation_values_member], rule exI[of _ "(q,I,K)"])
     (simp add: assms)

definition finite_row_values :: "('s \<times> 'q finite_syntax_reading) fset \<Rightarrow> 'q fset" where
  "finite_row_values H = fimage (fst \<circ> snd) H"

definition finite_row_interiors ::
  "('s \<times> 'q finite_syntax_reading) fset \<Rightarrow> local_address fset" where
  "finite_row_interiors H = ffUnion (fimage (fst \<circ> snd \<circ> snd) H)"

definition finite_row_slots ::
  "('s \<times> 'q finite_syntax_reading) fset \<Rightarrow> local_address fset" where
  "finite_row_slots H = ffUnion (fimage (snd \<circ> snd \<circ> snd) H)"

lemma finite_row_values_member:
  "q |\<in>| finite_row_values H \<longleftrightarrow> (\<exists>s I K. (s,q,I,K) |\<in>| H)"
  by (simp only: finite_row_values_def finite_image_member split_paired_Ex
      o_apply fst_conv snd_conv; blast)

lemma finite_row_interiors_member:
  "a |\<in>| finite_row_interiors H \<longleftrightarrow>
    (\<exists>s q I K. (s,q,I,K) |\<in>| H \<and> a |\<in>| I)"
  by (simp only: finite_row_interiors_def finite_union_image_member split_paired_Ex
      o_apply fst_conv snd_conv; blast)

lemma finite_row_slots_member:
  "a |\<in>| finite_row_slots H \<longleftrightarrow>
    (\<exists>s q I K. (s,q,I,K) |\<in>| H \<and> a |\<in>| K)"
  by (simp only: finite_row_slots_def finite_union_image_member split_paired_Ex
      o_apply fst_conv snd_conv; blast)

lemma finite_rows_decoded:
  "D ` fset (finite_row_values H) =
    native_row_values (map_relation_values (decode_finite_reading D) (fset H))"
  "fset (finite_row_interiors H) =
    native_row_interiors (map_relation_values (decode_finite_reading D) (fset H))"
  "fset (finite_row_slots H) =
    native_row_slots (map_relation_values (decode_finite_reading D) (fset H))"
proof -
  show "D ` fset (finite_row_values H) =
    native_row_values (map_relation_values (decode_finite_reading D) (fset H))"
    by (rule set_eqI; simp only: image_iff Bex_def native_row_value_member
        decoded_finite_row_member finite_row_values_member; blast)
  show "fset (finite_row_interiors H) =
    native_row_interiors (map_relation_values (decode_finite_reading D) (fset H))"
    by (rule set_eqI; simp only: native_row_interior_member
        decoded_finite_row_member finite_row_interiors_member; blast)
  show "fset (finite_row_slots H) =
    native_row_slots (map_relation_values (decode_finite_reading D) (fset H))"
    by (rule set_eqI; simp only: native_row_slot_member
        decoded_finite_row_member finite_row_slots_member; blast)
qed

lemma finite_socket_rows_decoded:
  assumes correct: "\<And>a q I K. (q,I,K) |\<in>| reads a \<longleftrightarrow> R a (D q) (fset I) (fset K)"
    and complete: "\<And>a q I K. R a q I K \<Longrightarrow>
      \<exists>p J A. (p,J,A) |\<in>| reads a \<and> D p=q \<and> fset J=I \<and> fset A=K"
  shows "map_relation_values (decode_finite_reading D) (fset (finite_socket_rows M reads)) =
    native_table_rows (fset M) R"
proof -
  have member: "(s,q,I,K) \<in>
      map_relation_values (decode_finite_reading D) (fset (finite_socket_rows M reads)) \<longleftrightarrow>
      (s,q,I,K) \<in> native_table_rows (fset M) R" for s q I K
  proof
    assume member: "(s,q,I,K) \<in>
      map_relation_values (decode_finite_reading D) (fset (finite_socket_rows M reads))"
    obtain p J A where row: "(s,p,J,A) |\<in>| finite_socket_rows M reads"
      and represented: "q=D p" "I=fset J" "K=fset A"
      using member by (simp only: decoded_finite_row_member; blast)
    obtain a where socket: "(s,a) |\<in>| M" and read: "(p,J,A) |\<in>| reads a"
      using row by (simp only: finite_socket_rows_member; blast)
    have "R a q I K" using read by (simp only: correct represented)
    then show "(s,q,I,K) \<in> native_table_rows (fset M) R"
      using socket by (simp only: native_table_rows_member; blast)
  next
    assume member: "(s,q,I,K) \<in> native_table_rows (fset M) R"
    obtain a where socket: "(s,a) |\<in>| M" and read: "R a q I K"
      using member by (simp only: native_table_rows_member; blast)
    obtain p J A where recovered: "(p,J,A) |\<in>| reads a"
      and represented: "D p=q" "fset J=I" "fset A=K"
      using complete[OF read] by blast
    have row: "(s,p,J,A) |\<in>| finite_socket_rows M reads"
      using socket recovered by (simp only: finite_socket_rows_member; blast)
    show "(s,q,I,K) \<in>
      map_relation_values (decode_finite_reading D) (fset (finite_socket_rows M reads))"
      using decoded_finite_rowI[OF row, of D] represented by simp
  qed
  show ?thesis by (rule set_eqI) (use member in \<open>auto simp: split_paired_All\<close>)
qed

section \<open>Key uniqueness is checked across actual row occurrences\<close>

lemma native_row_keys_injective_iff:
  assumes sv: "single_valued H"
  shows "inj_on (native_row_keys H) (rel_dom H) \<longleftrightarrow>
    (\<forall>s q I K t z J A. (s,q,I,K) \<in> H \<longrightarrow> (t,z,J,A) \<in> H \<longrightarrow>
      fst q=fst z \<longrightarrow> s=t)"
proof -
  have key: "native_row_keys H s=fst q" if "(s,q,I,K) \<in> H" for s q I K
    using rel_value_eq[OF sv that] by (simp add: native_row_keys_def)
  show ?thesis
  proof
    assume injective: "inj_on (native_row_keys H) (rel_dom H)"
    show "\<forall>s q I K t z J A. (s,q,I,K) \<in> H \<longrightarrow> (t,z,J,A) \<in> H \<longrightarrow>
      fst q=fst z \<longrightarrow> s=t"
      using injective key by (auto simp: inj_on_def rel_dom_def; blast)
  next
    assume unique: "\<forall>s q I K t z J A. (s,q,I,K) \<in> H \<longrightarrow> (t,z,J,A) \<in> H \<longrightarrow>
      fst q=fst z \<longrightarrow> s=t"
    show "inj_on (native_row_keys H) (rel_dom H)"
    proof (rule inj_onI)
      fix s t assume sd: "s \<in> rel_dom H" and td: "t \<in> rel_dom H"
        and same: "native_row_keys H s=native_row_keys H t"
      obtain q I K where first: "(s,q,I,K) \<in> H" using sd by (auto simp: rel_dom_def)
      obtain z J A where second: "(t,z,J,A) \<in> H" using td by (auto simp: rel_dom_def)
      have "fst q=fst z" using same key[OF first] key[OF second] by simp
      then show "s=t" using unique first second by blast
    qed
  qed
qed

definition finite_row_keys_injective ::
  "('s \<times> ('k \<times> 'v) finite_syntax_reading) fset \<Rightarrow> bool" where
  "finite_row_keys_injective H \<longleftrightarrow>
    fBall H (\<lambda>(s,q,I,K). fBall H (\<lambda>(t,z,J,A). fst q=fst z \<longrightarrow> s=t))"

definition finite_row_interiors_disjoint ::
  "('s \<times> 'q finite_syntax_reading) fset \<Rightarrow> bool" where
  "finite_row_interiors_disjoint H \<longleftrightarrow>
    fBall H (\<lambda>(s,q,I,K). fBall H (\<lambda>(t,z,J,A). s\<noteq>t \<longrightarrow> I |\<inter>| J={||}))"

lemma finite_row_keys_injective_correct:
  assumes sv: "single_valued (map_relation_values (decode_finite_reading D) (fset H))"
    and keys: "\<And>q. fst (D q)=fst q"
  shows "finite_row_keys_injective H \<longleftrightarrow>
    inj_on (native_row_keys (map_relation_values (decode_finite_reading D) (fset H)))
      (rel_dom (map_relation_values (decode_finite_reading D) (fset H)))"
proof -
  let ?G = "map_relation_values (decode_finite_reading D) (fset H)"
  have finite: "finite_row_keys_injective H \<longleftrightarrow>
      (\<forall>s q I K t z J A. (s,q,I,K) |\<in>| H \<longrightarrow> (t,z,J,A) |\<in>| H \<longrightarrow>
        fst q=fst z \<longrightarrow> s=t)"
    by (simp add: finite_row_keys_injective_def Ball_def split_paired_All)
  have equivalent: "finite_row_keys_injective H \<longleftrightarrow>
      (\<forall>s q I K t z J A. (s,q,I,K) \<in> ?G \<longrightarrow> (t,z,J,A) \<in> ?G \<longrightarrow>
        fst q=fst z \<longrightarrow> s=t)"
  proof
    assume guard: "finite_row_keys_injective H"
    show "\<forall>s q I K t z J A. (s,q,I,K) \<in> ?G \<longrightarrow> (t,z,J,A) \<in> ?G \<longrightarrow>
      fst q=fst z \<longrightarrow> s=t"
    proof (intro allI impI)
      fix s q I K t z J A
      assume first: "(s,q,I,K) \<in> ?G" and second: "(t,z,J,A) \<in> ?G" and same: "fst q=fst z"
      obtain p F W where left: "(s,p,F,W) |\<in>| H" "q=D p"
        using first by (simp only: decoded_finite_row_member; blast)
      obtain v L B where right: "(t,v,L,B) |\<in>| H" "z=D v"
        using second by (simp only: decoded_finite_row_member; blast)
      have "fst p=fst v" using same by (simp only: left(2) right(2) keys)
      then show "s=t" using guard left(1) right(1) finite by blast
    qed
  next
    assume guard: "\<forall>s q I K t z J A. (s,q,I,K) \<in> ?G \<longrightarrow> (t,z,J,A) \<in> ?G \<longrightarrow>
      fst q=fst z \<longrightarrow> s=t"
    show "finite_row_keys_injective H"
      unfolding finite
    proof (intro allI impI)
      fix s q I K t z J A
      assume first: "(s,q,I,K) |\<in>| H" and second: "(t,z,J,A) |\<in>| H" and same: "fst q=fst z"
      have "fst (D q)=fst (D z)" using same by (simp only: keys)
      then show "s=t"
        using guard decoded_finite_rowI[OF first, of D] decoded_finite_rowI[OF second, of D] by blast
    qed
  qed
  show ?thesis by (simp only: equivalent native_row_keys_injective_iff[OF sv])
qed

lemma finite_row_interiors_disjoint_correct:
  "finite_row_interiors_disjoint H \<longleftrightarrow>
    (\<forall>s q I K t z J A.
      (s,q,I,K) \<in> map_relation_values (decode_finite_reading D) (fset H) \<longrightarrow>
      (t,z,J,A) \<in> map_relation_values (decode_finite_reading D) (fset H) \<longrightarrow>
      s\<noteq>t \<longrightarrow> I \<inter> J={})"
proof -
  let ?G = "map_relation_values (decode_finite_reading D) (fset H)"
  have finite: "finite_row_interiors_disjoint H \<longleftrightarrow>
      (\<forall>s q I K t z J A. (s,q,I,K) |\<in>| H \<longrightarrow> (t,z,J,A) |\<in>| H \<longrightarrow>
        s\<noteq>t \<longrightarrow> I |\<inter>| J={||})"
    by (simp add: finite_row_interiors_disjoint_def Ball_def split_paired_All)
  show ?thesis
  proof
    assume guard: "finite_row_interiors_disjoint H"
    show "\<forall>s q I K t z J A. (s,q,I,K) \<in> ?G \<longrightarrow> (t,z,J,A) \<in> ?G \<longrightarrow>
      s\<noteq>t \<longrightarrow> I \<inter> J={}"
    proof (intro allI impI)
      fix s q I K t z J A
      assume first: "(s,q,I,K) \<in> ?G" and second: "(t,z,J,A) \<in> ?G" and distinct: "s\<noteq>t"
      obtain p F W where left: "(s,p,F,W) |\<in>| H" "I=fset F"
        using first by (simp only: decoded_finite_row_member; blast)
      obtain v L B where right: "(t,v,L,B) |\<in>| H" "J=fset L"
        using second by (simp only: decoded_finite_row_member; blast)
      have "F |\<inter>| L={||}" using guard left(1) right(1) distinct finite by blast
      then show "I \<inter> J={}" using left(2) right(2) by (simp add: fset_inject[symmetric])
    qed
  next
    assume guard: "\<forall>s q I K t z J A. (s,q,I,K) \<in> ?G \<longrightarrow> (t,z,J,A) \<in> ?G \<longrightarrow>
      s\<noteq>t \<longrightarrow> I \<inter> J={}"
    show "finite_row_interiors_disjoint H"
      unfolding finite
    proof (intro allI impI)
      fix s q I K t z J A
      assume first: "(s,q,I,K) |\<in>| H" and second: "(t,z,J,A) |\<in>| H" and distinct: "s\<noteq>t"
      have "fset I \<inter> fset J={}"
        using guard decoded_finite_rowI[OF first, of D] decoded_finite_rowI[OF second, of D] distinct by blast
      then show "I |\<inter>| J={||}" by (simp add: fset_inject[symmetric])
    qed
  qed
qed

section \<open>Complete native tables have finite recovery\<close>

definition finite_native_table_body ::
  "local_address \<Rightarrow> (local_address \<times> local_address) fset \<Rightarrow>
    (local_address \<times> ('k \<times> 'v) finite_syntax_reading) fset \<Rightarrow>
    ('k \<times> 'v) fset finite_syntax_reading fset" where
  "finite_native_table_body r M H =
    (let I=finsert r (fimage fst M |\<union>| finite_row_interiors H); K=finite_row_slots H in
     if finite_relation_functional H \<and> fimage fst H=fimage fst M \<and>
       finite_row_keys_injective H \<and> finite_row_interiors_disjoint H \<and>
       finsert r (fimage fst M) |\<inter>| finite_row_interiors H={||} \<and> I |\<inter>| K={||}
     then {|(finite_row_values H,I,K)|} else {||})"

lemma finite_native_table_body_correct:
  assumes injective: "inj D" and keys: "\<And>q. fst (D q)=fst q"
  shows "(Q,I,K) |\<in>| finite_native_table_body r M H \<longleftrightarrow>
    (let G=map_relation_values (decode_finite_reading D) (fset H) in
      single_valued G \<and> rel_dom G=rel_dom (fset M) \<and>
      inj_on (native_row_keys G) (rel_dom G) \<and>
      (\<forall>s q J A t z L B. (s,q,J,A) \<in> G \<longrightarrow> (t,z,L,B) \<in> G \<longrightarrow>
        s\<noteq>t \<longrightarrow> J \<inter> L={}) \<and>
      insert r (rel_dom (fset M)) \<inter> native_row_interiors G={} \<and>
      D ` fset Q=native_row_values G \<and>
      fset I=insert r (rel_dom (fset M) \<union> native_row_interiors G) \<and>
      fset K=native_row_slots G \<and> fset I \<inter> fset K={})"
proof -
  let ?G = "map_relation_values (decode_finite_reading D) (fset H)"
  have inj: "inj (decode_finite_reading D)" by (rule decode_finite_reading_inj[OF injective])
  have sv: "single_valued ?G \<longleftrightarrow> finite_relation_functional H"
    by (simp add: map_relation_values_functional[OF inj] finite_relation_functional_correct)
  have key: "finite_relation_functional H \<Longrightarrow>
      finite_row_keys_injective H \<longleftrightarrow> inj_on (native_row_keys ?G) (rel_dom ?G)"
    by (rule finite_row_keys_injective_correct[OF _ keys]) (simp add: sv)
  have decoded_values: "D ` fset Q=native_row_values ?G \<longleftrightarrow> Q=finite_row_values H"
    by (simp only: finite_rows_decoded(1)[symmetric] inj_image_eq_iff[OF injective] fset_inject)
  have domain: "rel_dom ?G=rel_dom (fset M) \<longleftrightarrow> fimage fst H=fimage fst M"
    by (simp add: rel_dom_image fimage.rep_eq fset_inject[symmetric])
  have disjoint: "(\<forall>s q J A t z L B. (s,q,J,A) \<in> ?G \<longrightarrow> (t,z,L,B) \<in> ?G \<longrightarrow>
      s\<noteq>t \<longrightarrow> J \<inter> L={}) \<longleftrightarrow> finite_row_interiors_disjoint H"
    by (rule finite_row_interiors_disjoint_correct[symmetric])
  have frame: "insert r (rel_dom (fset M)) \<inter> native_row_interiors ?G={} \<longleftrightarrow>
      finsert r (fimage fst M) |\<inter>| finite_row_interiors H={||}"
    by (simp add: finite_rows_decoded(2)[symmetric] rel_dom_image
        fimage.rep_eq fset_inject[symmetric])
  have interior: "fset I=insert r (rel_dom (fset M) \<union> native_row_interiors ?G) \<longleftrightarrow>
      I=finsert r (fimage fst M |\<union>| finite_row_interiors H)"
    by (simp add: finite_rows_decoded(2)[symmetric] rel_dom_image
        fimage.rep_eq fset_inject[symmetric])
  have slots: "fset K=native_row_slots ?G \<longleftrightarrow> K=finite_row_slots H"
    by (simp only: finite_rows_decoded(3)[symmetric] fset_inject)
  have separation: "fset I \<inter> fset K={} \<longleftrightarrow> I |\<inter>| K={||}"
    by (simp add: fset_inject[symmetric])
  show ?thesis
  proof (cases "finite_relation_functional H")
    case True
    show ?thesis
      by (simp only: finite_native_table_body_def Let_def finite_singleton_when_member prod.inject
          sv domain key[OF True] disjoint frame decoded_values interior slots separation)
         auto
  next
    case False
    then show ?thesis by (simp add: finite_native_table_body_def Let_def sv)
  qed
qed

definition finite_native_table_readings ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    (local_address \<Rightarrow> ('k \<times> 'v) finite_syntax_reading fset) \<Rightarrow>
    ('k \<times> 'v) fset finite_syntax_reading fset" where
  "finite_native_table_readings E u r reads = (if finite_environment_formed E then
    ffUnion (fimage (\<lambda>C. ffUnion (fimage (\<lambda>M.
      finite_native_table_body r M (finite_socket_rows M reads))
      (finite_family_candidates C r))) (finite_artifacts_at E u)) else {||})"

lemma finite_native_table_readings_step:
  "(Q,I,K) |\<in>| finite_native_table_readings E u r reads \<longleftrightarrow>
    finite_environment_formed E \<and> (\<exists>C M. C |\<in>| finite_artifacts_at E u \<and>
      family_at (decode_finite_object C) r (fset M) \<and>
      (Q,I,K) |\<in>| finite_native_table_body r M (finite_socket_rows M reads))"
  by (auto simp: finite_native_table_readings_def finite_union_image_member
      finite_family_candidates_correct split: if_splits)

theorem finite_native_table_readings_correct:
  assumes injective: "inj D" and keys: "\<And>q. fst (D q)=fst q"
    and correct: "\<And>a q I K. (q,I,K) |\<in>| reads a \<longleftrightarrow> R a (D q) (fset I) (fset K)"
    and complete: "\<And>a q I K. R a q I K \<Longrightarrow>
      \<exists>p J A. (p,J,A) |\<in>| reads a \<and> D p=q \<and> fset J=I \<and> fset A=K"
  shows "(Q,I,K) |\<in>| finite_native_table_readings E u r reads \<longleftrightarrow>
    native_table_at (decode_finite_environment E) u r R (D ` fset Q) (fset I) (fset K)"
proof -
  have body: "(Q,I,K) |\<in>| finite_native_table_body r M (finite_socket_rows M reads) \<longleftrightarrow>
      (let H=native_table_rows (fset M) R in
       single_valued H \<and> rel_dom H=rel_dom (fset M) \<and>
       inj_on (native_row_keys H) (rel_dom H) \<and>
       (\<forall>s q J A t z L B. (s,q,J,A) \<in> H \<longrightarrow> (t,z,L,B) \<in> H \<longrightarrow>
         s\<noteq>t \<longrightarrow> J \<inter> L={}) \<and>
       insert r (rel_dom (fset M)) \<inter> native_row_interiors H={} \<and>
       D ` fset Q=native_row_values H \<and>
       fset I=insert r (rel_dom (fset M) \<union> native_row_interiors H) \<and>
       fset K=native_row_slots H \<and> fset I \<inter> fset K={})" for M
    by (simp only: finite_native_table_body_correct[OF injective keys]
        finite_socket_rows_decoded[OF correct complete])
  show ?thesis
  proof
    assume member: "(Q,I,K) |\<in>| finite_native_table_readings E u r reads"
    obtain C M where ef: "finite_environment_formed E"
      and source: "C |\<in>| finite_artifacts_at E u"
      and family: "family_at (decode_finite_object C) r (fset M)"
      and reading: "(Q,I,K) |\<in>| finite_native_table_body r M (finite_socket_rows M reads)"
      using member by (auto simp: finite_native_table_readings_step)
    show "native_table_at (decode_finite_environment E) u r R (D ` fset Q) (fset I) (fset K)"
      unfolding native_table_at_def
      apply (rule conjI)
       apply (use ef in \<open>simp add: finite_environment_formed_correct\<close>)
      apply (rule exI[of _ "decode_finite_object C"], rule exI[of _ "fset M"])
      using source family reading by (simp add: body finite_artifacts_at_member)
  next
    assume reading: "native_table_at (decode_finite_environment E) u r R (D ` fset Q) (fset I) (fset K)"
    obtain C M where ef: "environment_formed (decode_finite_environment E)"
      and source: "C |\<in>| finite_artifacts_at E u"
      and family: "family_at (decode_finite_object C) r M"
      and fields: "(let H=native_table_rows M R in
       single_valued H \<and> rel_dom H=rel_dom M \<and>
       inj_on (native_row_keys H) (rel_dom H) \<and>
       (\<forall>s q J A t z L B. (s,q,J,A) \<in> H \<longrightarrow> (t,z,L,B) \<in> H \<longrightarrow>
         s\<noteq>t \<longrightarrow> J \<inter> L={}) \<and>
       insert r (rel_dom M) \<inter> native_row_interiors H={} \<and>
       D ` fset Q=native_row_values H \<and>
       fset I=insert r (rel_dom M \<union> native_row_interiors H) \<and>
       fset K=native_row_slots H \<and> fset I \<inter> fset K={})"
      using reading by (auto simp: native_table_at_def finite_artifacts_at_member)
    obtain F where candidate: "F |\<in>| finite_family_candidates C r" and represented: "fset F=M"
      using finite_family_candidates_complete[OF family] by blast
    have recovered: "(Q,I,K) |\<in>| finite_native_table_body r F (finite_socket_rows F reads)"
      using fields represented by (simp add: body)
    show "(Q,I,K) |\<in>| finite_native_table_readings E u r reads"
      unfolding finite_native_table_readings_step
      apply (rule conjI)
       apply (use ef in \<open>simp add: finite_environment_formed_correct\<close>)
      apply (rule exI[of _ C], rule exI[of _ F])
      using source family represented recovered by simp
  qed
qed

section \<open>Bindings and premise links share the proved table reader\<close>

definition finite_binding_table_readings ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    ('u definition_site \<times> finite_factor_term) fset finite_syntax_reading fset" where
  "finite_binding_table_readings E u r =
    finite_native_table_readings E u r (finite_application_readings E u)"

definition finite_discharge_table_readings ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    ('u definition_site \<times> 'u definition_site) fset finite_syntax_reading fset" where
  "finite_discharge_table_readings E u r =
    finite_native_table_readings E u r (finite_site_link_readings E u)"

theorem finite_binding_table_readings_correct:
  "(V,I,K) |\<in>| finite_binding_table_readings E u r \<longleftrightarrow>
    native_binding_table_at (decode_finite_environment E) u r
      (decode_finite_term_bindings V) (fset I) (fset K)"
proof -
  let ?D = "map_prod id decode_finite_term"
  let ?R = "\<lambda>a q J A. native_application_at (decode_finite_environment E) u a (fst q) (snd q) J A"
  have injective: "inj ?D" by (auto simp: inj_def map_prod_def)
  have keys: "fst (?D q)=fst q" for q by (cases q) simp
  have correct: "(q,J,A) |\<in>| finite_application_readings E u a \<longleftrightarrow>
      ?R a (?D q) (fset J) (fset A)" for a q J A
    by (cases q) (simp add: finite_application_readings_correct)
  have complete: "\<exists>p F W. (p,F,W) |\<in>| finite_application_readings E u a \<and>
      ?D p=q \<and> fset F=J \<and> fset W=A" if "?R a q J A" for a q J A
    using finite_application_readings_complete[OF that]
    by (cases q) (auto simp: map_prod_def; blast)
  have decoded_values: "?D ` fset V=decode_finite_term_bindings V"
    by (auto simp: decode_finite_term_bindings_def map_relation_values_def map_prod_def)
  show ?thesis
    by (simp only: finite_binding_table_readings_def
        finite_native_table_readings_correct[OF injective keys correct complete] decoded_values)
qed

theorem finite_discharge_table_readings_correct:
  "(D,I,K) |\<in>| finite_discharge_table_readings E u r \<longleftrightarrow>
    native_discharge_table_at (decode_finite_environment E) u r (fset D) (fset I) (fset K)"
proof -
  let ?R = "\<lambda>a q J A. native_site_link_at (decode_finite_environment E) u a (fst q) (snd q) J A"
  have keys: "fst (id q)=fst q" for q by simp
  have correct: "(q,J,A) |\<in>| finite_site_link_readings E u a \<longleftrightarrow>
      ?R a (id q) (fset J) (fset A)" for a q J A
    by (cases q) (simp add: finite_site_link_readings_correct)
  have complete: "\<exists>p F W. (p,F,W) |\<in>| finite_site_link_readings E u a \<and>
      id p=q \<and> fset F=J \<and> fset W=A" if "?R a q J A" for a q J A
    using finite_site_link_readings_complete[OF that] by (cases q) auto
  show ?thesis
    by (simp only: finite_discharge_table_readings_def
        finite_native_table_readings_correct[OF inj_on_id keys correct complete] image_id id_apply image_ident)
qed

theorem finite_binding_table_readings_complete:
  assumes read: "native_binding_table_at (decode_finite_environment E) u r V I K"
  shows "\<exists>F J A. (F,J,A) |\<in>| finite_binding_table_readings E u r \<and>
    decode_finite_term_bindings F=V \<and> fset J=I \<and> fset A=K"
proof -
  have finite: "finite V" "finite I" "finite K"
    using native_binding_table_properties(1,4,5)[OF read] by blast+
  have inverse: "decode_finite_term (finite_term_of t)=t" if "(a,t) \<in> V" for a t
    by (rule decode_finite_term_of) (use native_binding_table_properties(7)[OF read] that in blast)
  have representation: "\<exists>F. map_relation_values decode_finite_term (fset F)=V"
    by (rule finite_relation_value_representation[OF finite(1)], rule inverse)
  obtain F where decoded_values: "map_relation_values decode_finite_term (fset F)=V"
    using representation by blast
  have interior: "fset (Abs_fset I)=I" by (rule Abs_fset_inverse) (simp add: finite)
  have slots: "fset (Abs_fset K)=K" by (rule Abs_fset_inverse) (simp add: finite)
  have member: "(F,Abs_fset I,Abs_fset K) |\<in>| finite_binding_table_readings E u r"
    using read decoded_values interior slots
    by (simp add: finite_binding_table_readings_correct decode_finite_term_bindings_def)
  show ?thesis using member decoded_values interior slots by (auto simp: decode_finite_term_bindings_def)
qed

theorem finite_discharge_table_readings_complete:
  assumes read: "native_discharge_table_at (decode_finite_environment E) u r D I K"
  shows "\<exists>F J A. (F,J,A) |\<in>| finite_discharge_table_readings E u r \<and>
    fset F=D \<and> fset J=I \<and> fset A=K"
proof -
  have finite: "finite D" "finite I" "finite K"
    using native_discharge_table_properties(1,4,5)[OF read] by blast+
  have decoded_values: "fset (Abs_fset D)=D" by (rule Abs_fset_inverse) (simp add: finite)
  have interior: "fset (Abs_fset I)=I" by (rule Abs_fset_inverse) (simp add: finite)
  have slots: "fset (Abs_fset K)=K" by (rule Abs_fset_inverse) (simp add: finite)
  have member: "(Abs_fset D,Abs_fset I,Abs_fset K) |\<in>| finite_discharge_table_readings E u r"
    using read decoded_values interior slots by (simp add: finite_discharge_table_readings_correct)
  show ?thesis using member decoded_values interior slots by blast
qed

corollary finite_binding_table_readings_unique:
  assumes "(V,I,K) |\<in>| finite_binding_table_readings E u r"
    "(W,J,A) |\<in>| finite_binding_table_readings E u r"
  shows "V=W \<and> I=J \<and> K=A"
proof -
  have first: "native_binding_table_at (decode_finite_environment E) u r
      (decode_finite_term_bindings V) (fset I) (fset K)"
    and second: "native_binding_table_at (decode_finite_environment E) u r
      (decode_finite_term_bindings W) (fset J) (fset A)"
    using assms by (simp_all add: finite_binding_table_readings_correct)
  have injective: "inj decode_finite_term" by (auto simp: inj_def)
  show ?thesis using native_table_unique[OF first second]
    by (simp add: decode_finite_term_bindings_def map_relation_values_injective[OF injective] fset_inject)
qed

corollary finite_discharge_table_readings_unique:
  assumes "(D,I,K) |\<in>| finite_discharge_table_readings E u r"
    "(F,J,A) |\<in>| finite_discharge_table_readings E u r"
  shows "D=F \<and> I=J \<and> K=A"
proof -
  have first: "native_discharge_table_at (decode_finite_environment E) u r (fset D) (fset I) (fset K)"
    and second: "native_discharge_table_at (decode_finite_environment E) u r (fset F) (fset J) (fset A)"
    using assms by (simp_all add: finite_discharge_table_readings_correct)
  show ?thesis using native_table_unique[OF first second] by (simp add: fset_inject)
qed

export_code finite_native_table_readings finite_binding_table_readings
  finite_discharge_table_readings checking SML

text \<open>
  Recovery computes all readings at every actual socket. It checks that the
  resulting row relation is functional and has the complete socket domain.
  Distinct row occurrences must have distinct keys, even when their values
  coincide. The enclosing family and all row interiors are disjoint in the
  required places, and the complete interior is separate from external slots.
  Binding and premise tables use this same geometry. These readers recover
  metadata; inference validity is checked against the independently recovered
  program and claims.
\<close>

end
