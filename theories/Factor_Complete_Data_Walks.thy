theory Factor_Complete_Data_Walks
  imports Factor_Finite_Prepared_Data_Readings RRA_Executable_Records Finite_Sorted_Set_Execution
    "HOL-Library.List_Lexorder" "HOL-Library.Product_Lexorder"
begin

section \<open>A formed data reading is a walk over unique leaves and records\<close>

definition finite_data_leaf_values :: "finite_exact_artifact \<Rightarrow> local_address \<Rightarrow> octets fset" where
  "finite_data_leaf_values C r=ffilter (finite_payload_leaf_body C r) (finite_payload_values C r)"

lemma finite_data_leaf_values_unique:
  assumes "v |\<in>| finite_data_leaf_values C r" "w |\<in>| finite_data_leaf_values C r"
  shows "v=w"
proof -
  have "payload_at (decode_finite_object C) r v" "payload_at (decode_finite_object C) r w"
    using assms by (simp_all add: finite_data_leaf_values_def finite_payload_leaf_body_def finite_payload_at_correct)
  then show ?thesis by (rule payload_at_unique)
qed

lemma finite_data_leaf_values_cases:
  "finite_data_leaf_values C r={||} \<or> (\<exists>v. finite_data_leaf_values C r={|v|})"
proof (cases "finite_data_leaf_values C r={||}")
  case False
  then obtain v where member: "v |\<in>| finite_data_leaf_values C r" by auto
  have "finite_data_leaf_values C r={|v|}"
  proof (rule fset_eqI)
    fix w
    show "w |\<in>| finite_data_leaf_values C r \<longleftrightarrow> w |\<in>| {|v|}"
      using finite_data_leaf_values_unique[OF _ member, of w] member by blast
  qed
  then show ?thesis by blast
qed simp

lemma finite_data_leaf_excludes_record:
  assumes "v |\<in>| finite_data_leaf_values C r"
  shows "finite_record_body_candidates C r 2={||}"
proof -
  have "finite_headed_incidence (finite_structure C) r={||}"
    using assms by (simp add: finite_data_leaf_values_def finite_payload_leaf_body_def)
  then show ?thesis by (simp add: finite_record_body_candidates_def Let_def fcard.rep_eq)
qed

lemma finite_data_record_cases:
  assumes object: "finite_object_formed C"
  shows "finite_record_body_candidates C r 2={||} \<or>
    (\<exists>ps l q. finite_record_body_candidates C r 2={|(ps,[l,q])|} \<and> distinct ps \<and> r\<notin>set ps)"
proof (cases "finite_record_body_candidates C r 2={||}")
  case False
  then obtain ps xs where member: "(ps,xs) |\<in>| finite_record_body_candidates C r 2" by auto
  have candidate: "(ps,xs) |\<in>| finite_record_candidates C r 2"
    using member by (simp add: finite_record_body_candidates_exact[OF object])
  have read: "record_at (decode_finite_object C) r ps xs" and length: "length xs=2"
    using candidate by (simp_all add: finite_record_candidates_correct)
  obtain l q where fields: "xs=[l,q]"
    using length by (cases xs rule: list.exhaust; cases "tl xs" rule: list.exhaust) auto
  have sockets: "distinct ps" "r\<notin>set ps"
    using record_at_preserves_socket_occurrences[OF read] by simp_all
  have only: "finite_record_body_candidates C r 2={|(ps,xs)|}"
  proof (rule fset_eqI)
    fix c
    show "c |\<in>| finite_record_body_candidates C r 2 \<longleftrightarrow> c |\<in>| {|(ps,xs)|}"
    proof
      assume "c |\<in>| finite_record_body_candidates C r 2"
      then obtain qs ys where c: "c=(qs,ys)" and other: "(qs,ys) |\<in>| finite_record_candidates C r 2"
        by (cases c) (simp add: finite_record_body_candidates_exact[OF object])
      show "c |\<in>| {|(ps,xs)|}"
        using finite_record_candidates_unique[OF candidate other] c by simp
    qed (use member in simp)
  qed
  show ?thesis using only fields sockets by blast
qed simp

lemma finite_singleton_listing [simp]: "sorted_list_of_fset {|x|}=[x]"
  by (simp add: sorted_list_of_fset.rep_eq)

lemma finite_empty_listing [simp]: "sorted_list_of_fset {||}=[]"
  by (simp add: sorted_list_of_fset.rep_eq)

fun finite_data_walk :: "nat \<Rightarrow> finite_exact_artifact \<Rightarrow> local_address \<Rightarrow>
    (finite_factor_term \<times> local_address list) option" where
  "finite_data_walk 0 C r=None"
| "finite_data_walk (Suc n) C r=(case sorted_list_of_fset (finite_data_leaf_values C r) of
      v#vs \<Rightarrow> Some (Finite_Payload v,[r])
    | [] \<Rightarrow> (case sorted_list_of_fset (finite_record_body_candidates C r 2) of
        (ps,xs)#rest \<Rightarrow> (case xs of
            [l,q] \<Rightarrow> (case finite_data_walk n C l of None \<Rightarrow> None
              | Some (x,ls) \<Rightarrow> (case finite_data_walk n C q of None \<Rightarrow> None
                | Some (y,qs) \<Rightarrow> Some (Finite_Pair x y,r#ps@ls@qs)))
          | _ \<Rightarrow> None)
      | [] \<Rightarrow> None))"

definition finite_walk_readings ::
  "(finite_factor_term \<times> local_address list) option \<Rightarrow> finite_factor_term finite_syntax_reading fset" where
  "finite_walk_readings w=(case w of None \<Rightarrow> {||}
    | Some (t,zs) \<Rightarrow> if distinct zs then {|(t,fset_of_list zs,{||})|} else {||})"

lemma finite_walk_join:
  assumes sockets: "distinct ps" "r\<notin>set ps"
  shows "finite_join_readings Finite_Pair {||} r ps (finite_walk_readings (Some (x,ls)))
      (finite_walk_readings (Some (y,qs)))=finite_walk_readings (Some (Finite_Pair x y,r#ps@ls@qs))"
proof (cases "distinct ls \<and> distinct qs")
  case True
  have disjoint: "finsert r (fset_of_list ps) |\<inter>| (fset_of_list ls |\<union>| fset_of_list qs)={||} \<and>
      fset_of_list ls |\<inter>| fset_of_list qs={||} \<longleftrightarrow> distinct (r#ps@ls@qs)"
    using True sockets by (auto simp: fset_eq_iff fset_of_list_elem)
  have interior: "finsert r (fset_of_list ps) |\<union>| fset_of_list ls |\<union>| fset_of_list qs=fset_of_list (r#ps@ls@qs)"
    by (auto simp: fset_eq_iff fset_of_list_elem)
  have join: "finite_join_readings Finite_Pair {||} r ps (finite_walk_readings (Some (x,ls)))
      (finite_walk_readings (Some (y,qs)))=
    (if finsert r (fset_of_list ps) |\<inter>| (fset_of_list ls |\<union>| fset_of_list qs)={||} \<and>
        fset_of_list ls |\<inter>| fset_of_list qs={||}
      then {|(Finite_Pair x y,finsert r (fset_of_list ps) |\<union>| fset_of_list ls |\<union>| fset_of_list qs,{||})|}
      else {||})"
    using True by (simp add: finite_walk_readings_def finite_join_readings_def Let_def)
  show ?thesis
    unfolding join disjoint interior by (simp add: finite_walk_readings_def)
next
  case False
  then show ?thesis by (auto simp: finite_walk_readings_def finite_join_readings_def)
qed

theorem finite_data_walk_readings:
  assumes formed: "finite_exact_formed C"
  shows "finite_data_body_readings n C r=finite_walk_readings (finite_data_walk n C r)"
proof (induction n arbitrary: r)
  case 0
  then show ?case by (simp add: finite_walk_readings_def)
next
  case (Suc n)
  have object: "finite_object_formed C" using formed by (simp add: finite_exact_formed_def)
  have readings: "finite_data_body_readings (Suc n) C r=
      fimage (\<lambda>v. (Finite_Payload v,{|r|},{||})) (finite_data_leaf_values C r) |\<union>|
      ffUnion (fimage (\<lambda>(ps,xs). case xs of [l,q] \<Rightarrow>
        finite_join_readings Finite_Pair {||} r ps (finite_walk_readings (finite_data_walk n C l))
          (finite_walk_readings (finite_data_walk n C q)) | _ \<Rightarrow> {||})
        (finite_record_body_candidates C r 2))"
  proof -
    have previous: "finite_data_body_readings n C=(\<lambda>q. finite_walk_readings (finite_data_walk n C q))"
      by (rule ext) (rule Suc.IH)
    show ?thesis
      by (simp only: finite_data_body_readings.simps finite_payload_body_readings_def
        finite_record_body_readings_def finite_data_leaf_values_def previous)
  qed
  have claim: "fimage (\<lambda>v. (Finite_Payload v,{|r|},{||})) (finite_data_leaf_values C r) |\<union>|
      ffUnion (fimage (\<lambda>(ps,xs). case xs of [l,q] \<Rightarrow>
        finite_join_readings Finite_Pair {||} r ps (finite_walk_readings (finite_data_walk n C l))
          (finite_walk_readings (finite_data_walk n C q)) | _ \<Rightarrow> {||})
        (finite_record_body_candidates C r 2))=finite_walk_readings (finite_data_walk (Suc n) C r)"
  proof (cases "finite_data_leaf_values C r={||}")
    case False
    then obtain v where leaf: "finite_data_leaf_values C r={|v|}"
      using finite_data_leaf_values_cases by blast
    have none: "finite_record_body_candidates C r 2={||}"
      by (rule finite_data_leaf_excludes_record[of v]) (simp add: leaf)
    show ?thesis by (simp add: leaf none finite_walk_readings_def)
  next
    case True
    note empty_leaf=True
    show ?thesis
    proof (cases "finite_record_body_candidates C r 2={||}")
      case True
      then show ?thesis using empty_leaf by (simp add: finite_walk_readings_def)
    next
      case False
      then obtain ps l q where candidate: "finite_record_body_candidates C r 2={|(ps,[l,q])|}"
        and sockets: "distinct ps" "r\<notin>set ps"
        using finite_data_record_cases[OF object] by blast
      show ?thesis
      proof (cases "finite_data_walk n C l")
        case None
        then show ?thesis
          using empty_leaf by (simp add: candidate finite_walk_readings_def finite_join_readings_def)
      next
        case (Some left)
        obtain x ls where left: "finite_data_walk n C l=Some (x,ls)" using Some by (cases left) auto
        show ?thesis
        proof (cases "finite_data_walk n C q")
          case None
          then show ?thesis
            using empty_leaf left by (simp add: candidate finite_walk_readings_def finite_join_readings_def)
        next
          case (Some right)
          obtain y qs where right: "finite_data_walk n C q=Some (y,qs)" using Some by (cases right) auto
          show ?thesis
            using empty_leaf left right finite_walk_join[OF sockets, of x ls y qs]
            by (simp add: candidate)
        qed
      qed
    qed
  qed
  show ?case by (simp only: readings claim)
qed

section \<open>A complete data reading checks its walk once\<close>

lemma finite_listing_distinct_carrier:
  "distinct zs \<and> fset_of_list zs=A \<longleftrightarrow> (let s=sort zs in ascending_listing s \<and> s=sorted_list_of_fset A)"
proof
  assume walk: "distinct zs \<and> fset_of_list zs=A"
  have ascending: "ascending_listing (sort zs)"
    using walk by (simp add: ascending_listing_exact)
  have carrier: "A=fset_of_list zs" using walk by simp
  have listing: "sort zs=sorted_list_of_fset A"
  proof (rule sorted_distinct_set_unique)
    show "sorted (sort zs)" by simp
    show "distinct (sort zs)" using walk by simp
    show "sorted (sorted_list_of_fset A)" by (simp add: sorted_list_of_fset.rep_eq)
    show "distinct (sorted_list_of_fset A)" by (simp add: sorted_list_of_fset.rep_eq)
    show "set (sort zs)=set (sorted_list_of_fset A)"
      by (simp add: carrier sorted_list_of_fset.rep_eq fset_of_list.rep_eq)
  qed
  show "let s=sort zs in ascending_listing s \<and> s=sorted_list_of_fset A"
    using ascending listing by (simp add: Let_def)
next
  assume listed: "let s=sort zs in ascending_listing s \<and> s=sorted_list_of_fset A"
  have ascending: "ascending_listing (sort zs)" using listed unfolding Let_def by blast
  have listing: "sort zs=sorted_list_of_fset A" using listed unfolding Let_def by blast
  have "distinct zs" using ascending by (simp add: ascending_listing_exact)
  moreover have "fset_of_list zs=A"
    using arg_cong[OF listing, of set] by (simp add: fset_eq_iff fset_of_list.rep_eq sorted_list_of_fset.rep_eq)
  ultimately show "distinct zs \<and> fset_of_list zs=A" by simp
qed

lemma finite_card_listing: "fcard A=length (sorted_list_of_fset A)"
  by (simp add: fcard.rep_eq sorted_list_of_fset.rep_eq)

declare finite_complete_data_readings_prepared_def[code del]

theorem finite_complete_data_readings_walk_code [code]:
  "finite_complete_data_readings_prepared C r=(if finite_exact_formed C \<and> r |\<in>| finite_carrier (finite_structure C) then
    (let carrier=sorted_list_of_fset (finite_carrier (finite_structure C)) in
      case finite_data_walk (length carrier) C r of None \<Rightarrow> {||}
      | Some (t,zs) \<Rightarrow> (let s=sort zs in if ascending_listing s \<and> s=carrier then {|t|} else {||}))
    else {||})"
proof (cases "finite_exact_formed C \<and> r |\<in>| finite_carrier (finite_structure C)")
  case True
  then have formed: "finite_exact_formed C" by simp
  have body_values: "finite_complete_data_body_values C r=(case finite_data_walk (fcard (finite_carrier (finite_structure C))) C r of
      None \<Rightarrow> {||} | Some (t,zs) \<Rightarrow> if distinct zs \<and> fset_of_list zs=finite_carrier (finite_structure C) then {|t|} else {||})"
    by (auto simp: finite_complete_data_body_values_def finite_data_walk_readings[OF formed]
      finite_walk_readings_def fset_eq_iff split: option.splits)
  show ?thesis
    using True by (simp add: finite_complete_data_readings_prepared_def body_values finite_card_listing
      finite_listing_distinct_carrier Let_def split: option.splits)
next
  case False
  then show ?thesis by (simp only: finite_complete_data_readings_prepared_def if_False)
qed

text \<open>
  In a formed artifact a node has at most one payload leaf value and at most one
  two-field record, and never both. Reading its data therefore follows one walk
  that lists the root, record ports and child walks, and the original pairwise
  interior conditions hold exactly when that listing has no repetition. A
  complete reading sorts the listing once and compares it with the canonical
  carrier, so node interiors are no longer joined at every record. Every
  original leaf, record, refusal and complete term is unchanged.
\<close>

end
