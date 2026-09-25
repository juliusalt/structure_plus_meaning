theory Factor_Package_Reader_Counterparts
  imports Factor_Additions_Counterparts Factor_Package_Closure_Admission Factor_Root_Family_Reading
    Factor_Package_Membership Factor_Package_Retention_Admission Factor_Executable_Dependencies
begin

text \<open>
  The counterparts of the package readers 77 (package closure admission), 79 (root family reading),
  83 (package membership) and 122 (package retention admission), build C4 of DECISIONS.md "The native
  evaluator evaluates above an implemented base: the given's readers enter through counterparts exact to
  their native definitions". Each is a function on finite terms: it reads its reader's argument back
  through the finite readers of C1 and C2, each exact to its notion, is false on every term not of that
  shape, and decides on what it read by finite operations already exact to their notions. Each is exact at
  every finite term to its reader's result relation, and so to the site's positive meaning in its reader's
  own system. The native definitions stay normative: the exactness is the proof.
\<close>

section \<open>A list of definition sites, and an environment beside a use, read back\<close>

theorem finite_site_list_read_exact:
  "finite_sequence_read finite_site_value_read t=Some ds \<longleftrightarrow>
    decode_finite_term t=data_list_term (map (\<lambda>d. definition_site_value d) ds)"
proof -
  have site: "finite_reads finite_site_value_read finite_site_data"
  proof (rule finite_readsI)
    fix v and x :: "local_address option definition_site"
    obtain u r where x: "x=(u,r)" by (cases x)
    have eq: "site_data_term u r=decode_finite_term (finite_site_data (u,r))" by simp
    show "finite_site_value_read v=Some x \<longleftrightarrow> v=finite_site_data x"
      by (simp only: x finite_site_value_read_exact eq decode_finite_term_injective)
  qed
  have decode: "decode_finite_term (finite_sequence_presentation finite_site_data xs)=
      data_list_term (map (\<lambda>d. definition_site_value d) xs)" for xs
    by (induction xs) simp_all
  have "finite_sequence_read finite_site_value_read t=Some ds \<longleftrightarrow> t=finite_sequence_presentation finite_site_data ds"
    using finite_sequence_reads[OF site] by (simp add: finite_reads_def)
  also have "\<dots> \<longleftrightarrow> decode_finite_term t=data_list_term (map (\<lambda>d. definition_site_value d) ds)"
    by (simp only: decode[symmetric] decode_finite_term_injective)
  finally show ?thesis .
qed

lemma finite_environment_use_read_exact:
  "finite_pair_read finite_environment_value_read finite_use_value_read v=Some z \<longleftrightarrow>
    (\<exists>e. decode_finite_term v=Pair_Term e (use_data_term (snd z)) \<and>
      environment_value_presents (decode_finite_environment (fst z)) e)"
proof -
  obtain F w where z: "z=(F,w)" by (cases z)
  show ?thesis
    by (auto simp: z finite_pair_read_present[where P="\<lambda>E e. environment_value_presents (decode_finite_environment E) e"
      and Q="\<lambda>u w. w=use_data_term u", OF finite_environment_value_read_exact finite_use_value_read_exact])
qed

section \<open>The counterpart of package closure admission (77)\<close>

text \<open>
  The argument is an environment value beside the data list of the supplied root sites. The counterpart
  asks the finite package formation (@{thm [source] finite_native_package_formed_correct}) of the root set.
\<close>

definition finite_closure_argument_read :: "finite_factor_term \<Rightarrow>
    (local_address option finite_artifact_environment\<times>local_address option definition_site list) option" where
  "finite_closure_argument_read=finite_pair_read finite_environment_value_read (finite_sequence_read finite_site_value_read)"

theorem finite_closure_argument_read_exact:
  "finite_closure_argument_read t=Some (E,rs) \<longleftrightarrow> (\<exists>e.
    decode_finite_term t=Pair_Term e (data_list_term (map (\<lambda>d. definition_site_value d) rs)) \<and>
    environment_value_presents (decode_finite_environment E) e)"
  unfolding finite_closure_argument_read_def
  by (auto simp: finite_pair_read_present[where P="\<lambda>E e. environment_value_presents (decode_finite_environment E) e"
    and Q="\<lambda>rs w. w=data_list_term (map (\<lambda>d. definition_site_value d) rs)",
    OF finite_environment_value_read_exact finite_site_list_read_exact])

definition finite_package_closure_admission_decision :: "finite_factor_term \<Rightarrow> bool" where
  "finite_package_closure_admission_decision t=(case finite_closure_argument_read t of None \<Rightarrow> False
    | Some (E,rs) \<Rightarrow> finite_native_package_formed E (fset_of_list rs))"

theorem finite_package_closure_admission_decision_exact:
  "finite_package_closure_admission_decision t \<longleftrightarrow> package_closure_admission_result (decode_finite_term t)"
proof
  assume holds: "finite_package_closure_admission_decision t"
  obtain E rs where read: "finite_closure_argument_read t=Some (E,rs)"
    using holds by (cases "finite_closure_argument_read t")
      (auto simp: finite_package_closure_admission_decision_def split: prod.splits)
  have formed: "finite_native_package_formed E (fset_of_list rs)"
    using holds read by (simp add: finite_package_closure_admission_decision_def)
  obtain e where z: "decode_finite_term t=Pair_Term e (data_list_term (map (\<lambda>d. definition_site_value d) rs))"
    and pe: "environment_value_presents (decode_finite_environment E) e"
    using read by (auto simp: finite_closure_argument_read_exact)
  have "native_package_formed (decode_finite_environment E) (set rs)"
    using formed by (simp add: finite_native_package_formed_correct fset_of_list.rep_eq)
  then show "package_closure_admission_result (decode_finite_term t)" using z pe by blast
next
  assume "package_closure_admission_result (decode_finite_term t)"
  then obtain E e rs where z: "decode_finite_term t=Pair_Term e (data_list_term (map (\<lambda>d. definition_site_value d) rs))"
    and pe: "environment_value_presents E e" and formed: "native_package_formed E (set rs)"
    by blast
  obtain C where c: "decode_finite_environment C=E" by (rule environment_value_presents_finite[OF pe])
  have read: "finite_closure_argument_read t=Some (C,rs)"
    using z pe by (auto simp: finite_closure_argument_read_exact c)
  have "finite_native_package_formed C (fset_of_list rs)"
    using formed by (simp add: finite_native_package_formed_correct fset_of_list.rep_eq c)
  then show "finite_package_closure_admission_decision t"
    using read by (simp add: finite_package_closure_admission_decision_def)
qed

corollary finite_package_closure_admission_decision_meaning:
  "finite_package_closure_admission_decision t \<longleftrightarrow>
    (77,decode_finite_term t)\<in>positive_meaning package_closure_admission_system"
  by (simp only: finite_package_closure_admission_decision_exact package_closure_admission_exact)

section \<open>The counterpart of root family reading (79)\<close>

text \<open>
  The argument is an environment value and a use, beside an address and the data list of destination
  sites. The reading holds exactly when the list is the value list of an enumeration of the root family
  read at the use and address, with its keys distinct (@{thm [source] native_root_family_from_list},
  @{thm [source] root_family_reading_listed}). The counterpart takes the family from the finite root family
  reading and asks whether the list enumerates its values: a value list enumerates a finite relation when
  its head is the value of a member whose key no other member has, and its tail enumerates the rest.
\<close>

primrec finite_listed_values :: "('k\<times>'v) fset \<Rightarrow> 'v list \<Rightarrow> bool" where
  "finite_listed_values Q []=(Q={||})"
| "finite_listed_values Q (d#ds)=fBex Q (\<lambda>x. snd x=d \<and> fBall Q (\<lambda>y. fst y=fst x \<longrightarrow> y=x) \<and>
    finite_listed_values (Q |-| {|x|}) ds)"

lemma finite_listed_values_exact:
  "finite_listed_values Q ds \<longleftrightarrow> (\<exists>ks. distinct ks \<and> length ks=length ds \<and> fset Q=set (zip ks ds))"
proof (induction ds arbitrary: Q)
  case Nil
  have "Q={||} \<longleftrightarrow> fset Q={}" by (metis bot_fset.rep_eq fset_inject)
  then show ?case by simp
next
  case (Cons d ds)
  show ?case
  proof
    assume "finite_listed_values Q (d#ds)"
    then obtain x where member: "x |\<in>| Q" and head_value: "snd x=d"
      and unique: "fBall Q (\<lambda>y. fst y=fst x \<longrightarrow> y=x)" and rest: "finite_listed_values (Q |-| {|x|}) ds"
      by (auto elim: fBexE)
    obtain ks where ks: "distinct ks" "length ks=length ds" "fset (Q |-| {|x|})=set (zip ks ds)"
      using rest Cons.IH by blast
    have minus: "fset (Q |-| {|x|})=fset Q-{x}" by (simp add: minus_fset.rep_eq)
    have outside: "fst x\<notin>set ks"
    proof
      assume "fst x\<in>set ks"
      then obtain v where zipped: "(fst x,v)\<in>set (zip ks ds)" using in_set_impl_in_set_zip1[OF ks(2)] by blast
      then have other: "(fst x,v) |\<in>| Q" "(fst x,v)\<noteq>x" using ks(3) minus by auto
      show False using fbspec[OF unique other(1)] other(2) by simp
    qed
    have whole: "fset Q=set (zip (fst x#ks) (d#ds))"
      using member head_value ks(3) minus by (cases x) auto
    show "\<exists>ks. distinct ks \<and> length ks=length (d#ds) \<and> fset Q=set (zip ks (d#ds))"
      using ks(1,2) outside whole by (intro exI[of _ "fst x#ks"]) simp
  next
    assume "\<exists>ks. distinct ks \<and> length ks=length (d#ds) \<and> fset Q=set (zip ks (d#ds))"
    then obtain ks0 where ks0: "distinct ks0" "length ks0=length (d#ds)" "fset Q=set (zip ks0 (d#ds))" by blast
    then obtain k ks where k: "ks0=k#ks" by (cases ks0) auto
    have ks: "distinct (k#ks)" "length ks=length ds" "fset Q=insert (k,d) (set (zip ks ds))"
      using ks0 k by simp_all
    have fresh: "(k,d)\<notin>set (zip ks ds)" using ks(1) by (auto dest: set_zip_leftD)
    have rest: "fset (Q |-| {|(k,d)|})=set (zip ks ds)" using ks(3) fresh by (auto simp: minus_fset.rep_eq)
    have listed: "finite_listed_values (Q |-| {|(k,d)|}) ds" using Cons.IH ks(1,2) rest by auto
    have unique: "fBall Q (\<lambda>y. fst y=fst (k,d) \<longrightarrow> y=(k,d))"
    proof (rule fBallI)
      fix y assume "y |\<in>| Q"
      then show "fst y=fst (k,d) \<longrightarrow> y=(k,d)" using ks(1,3) by (cases y) (auto dest: set_zip_leftD)
    qed
    have member: "(k,d) |\<in>| Q" using ks(3) by simp
    have head: "snd (k,d)=d" by simp
    have "snd (k,d)=d \<and> fBall Q (\<lambda>y. fst y=fst (k,d) \<longrightarrow> y=(k,d)) \<and>
        finite_listed_values (Q |-| {|(k,d)|}) ds"
      by (rule conjI[OF head conjI[OF unique listed]])
    then show "finite_listed_values Q (d#ds)"
      unfolding finite_listed_values.simps by (rule fBexI[OF _ member])
  qed
qed

lemma root_family_listed_keys:
  assumes formed: "environment_formed E"
  shows "(\<exists>R xs. artifact_at E u R \<and> distinct xs \<and> family_at R r (set xs) \<and>
      list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds) \<longleftrightarrow>
    (\<exists>ks. distinct ks \<and> length ks=length ds \<and> native_root_family_at E u r (set (zip ks ds)))"
proof
  assume "\<exists>R xs. artifact_at E u R \<and> distinct xs \<and> family_at R r (set xs) \<and>
      list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds"
  then obtain R xs where parts: "artifact_at E u R" "distinct xs" "family_at R r (set xs)"
      "list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds"
    by blast
  have keys: "distinct (map fst xs)" using parts(2,3) by (simp add: distinct_keys_iff family_at_def)
  have len: "length (map fst xs)=length ds" using list_all2_lengthD[OF parts(4)] by simp
  show "\<exists>ks. distinct ks \<and> length ks=length ds \<and> native_root_family_at E u r (set (zip ks ds))"
    using keys len native_root_family_from_list(1)[OF formed parts(1) parts(3) parts(2) parts(4)] by blast
next
  assume "\<exists>ks. distinct ks \<and> length ks=length ds \<and> native_root_family_at E u r (set (zip ks ds))"
  then obtain ks where keys: "distinct ks" and len: "length ks=length ds"
    and raw: "native_root_family_at E u r (set (zip ks ds))" by blast
  show "\<exists>R xs. artifact_at E u R \<and> distinct xs \<and> family_at R r (set xs) \<and>
      list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds"
    by (rule root_family_reading_listed[OF raw keys len])
qed

lemma finite_root_family_listed:
  "fBex (finite_native_root_family_readings E u r) (\<lambda>Q. finite_listed_values Q ds) \<longleftrightarrow>
    (\<exists>ks. distinct ks \<and> length ks=length ds \<and>
      native_root_family_at (decode_finite_environment E) u r (set (zip ks ds)))"
proof
  assume "fBex (finite_native_root_family_readings E u r) (\<lambda>Q. finite_listed_values Q ds)"
  then obtain Q where member: "Q |\<in>| finite_native_root_family_readings E u r"
    and listed: "finite_listed_values Q ds" by (auto elim: fBexE)
  obtain ks where ks: "distinct ks" "length ks=length ds" "fset Q=set (zip ks ds)"
    using listed by (auto simp: finite_listed_values_exact)
  show "\<exists>ks. distinct ks \<and> length ks=length ds \<and>
      native_root_family_at (decode_finite_environment E) u r (set (zip ks ds))"
    using member ks by (metis finite_native_root_family_readings_correct)
next
  assume "\<exists>ks. distinct ks \<and> length ks=length ds \<and>
      native_root_family_at (decode_finite_environment E) u r (set (zip ks ds))"
  then obtain ks where ks: "distinct ks" "length ks=length ds"
      "native_root_family_at (decode_finite_environment E) u r (set (zip ks ds))" by blast
  obtain F where member: "F |\<in>| finite_native_root_family_readings E u r" and set: "fset F=set (zip ks ds)"
    using finite_native_root_family_readings_complete[OF ks(3)] by blast
  have "finite_listed_values F ds" using ks set by (auto simp: finite_listed_values_exact)
  then show "fBex (finite_native_root_family_readings E u r) (\<lambda>Q. finite_listed_values Q ds)"
    by (rule fBexI[OF _ member])
qed

definition finite_root_family_argument_read :: "finite_factor_term \<Rightarrow>
    ((local_address option finite_artifact_environment\<times>local_address option)\<times>
      (local_address\<times>local_address option definition_site list)) option" where
  "finite_root_family_argument_read=finite_pair_read
    (finite_pair_read finite_environment_value_read finite_use_value_read)
    (finite_pair_read finite_payload_value_read (finite_sequence_read finite_site_value_read))"

theorem finite_root_family_argument_read_exact:
  "finite_root_family_argument_read t=Some ((E,u),(r,ds)) \<longleftrightarrow> (\<exists>e.
    decode_finite_term t=citation_observation_argument e (use_data_term u) (Payload_Term r)
      (data_list_term (map (\<lambda>d. definition_site_value d) ds)) \<and>
    environment_value_presents (decode_finite_environment E) e)"
proof -
  have right: "finite_pair_read finite_payload_value_read (finite_sequence_read finite_site_value_read) v=Some y \<longleftrightarrow>
      decode_finite_term v=Pair_Term (Payload_Term (fst y)) (data_list_term (map (\<lambda>d. definition_site_value d) (snd y)))"
    for v y
  proof -
    obtain a bs where y: "y=(a,bs)" by (cases y)
    show ?thesis
      by (auto simp: y finite_pair_read_present[where P="\<lambda>r w. w=Payload_Term r"
        and Q="\<lambda>ds w. w=data_list_term (map (\<lambda>d. definition_site_value d) ds)",
        OF finite_payload_value_read_exact finite_site_list_read_exact])
  qed
  show ?thesis
    by (auto simp: finite_root_family_argument_read_def finite_pair_read_present[where
      P="\<lambda>z v. \<exists>e. v=Pair_Term e (use_data_term (snd z)) \<and>
        environment_value_presents (decode_finite_environment (fst z)) e"
      and Q="\<lambda>y w. w=Pair_Term (Payload_Term (fst y)) (data_list_term (map (\<lambda>d. definition_site_value d) (snd y)))",
      OF finite_environment_use_read_exact right])
qed

definition finite_root_family_reading_decision :: "finite_factor_term \<Rightarrow> bool" where
  "finite_root_family_reading_decision t=(case finite_root_family_argument_read t of None \<Rightarrow> False
    | Some ((E,u),(r,ds)) \<Rightarrow> fBex (finite_native_root_family_readings E u r) (\<lambda>Q. finite_listed_values Q ds))"

theorem finite_root_family_reading_decision_exact:
  "finite_root_family_reading_decision t \<longleftrightarrow> root_family_reading_result (decode_finite_term t)"
proof
  assume holds: "finite_root_family_reading_decision t"
  obtain E u r ds where read: "finite_root_family_argument_read t=Some ((E,u),(r,ds))"
    using holds by (cases "finite_root_family_argument_read t")
      (auto simp: finite_root_family_reading_decision_def split: prod.splits)
  have listed: "fBex (finite_native_root_family_readings E u r) (\<lambda>Q. finite_listed_values Q ds)"
    using holds read by (simp add: finite_root_family_reading_decision_def)
  obtain e where z: "decode_finite_term t=citation_observation_argument e (use_data_term u) (Payload_Term r)
      (data_list_term (map (\<lambda>d. definition_site_value d) ds))"
    and pe: "environment_value_presents (decode_finite_environment E) e"
    using read by (auto simp: finite_root_family_argument_read_exact)
  have formed: "environment_formed (decode_finite_environment E)"
    using environment_value_presents_formed[OF pe] by blast
  obtain R xs where "artifact_at (decode_finite_environment E) u R" "distinct xs" "family_at R r (set xs)"
      "list_all2 (\<lambda>a d. located_at (decode_finite_environment E) u a (fst d) (snd d)) (map snd xs) ds"
    using listed by (simp only: finite_root_family_listed root_family_listed_keys[OF formed, symmetric]) blast
  then show "root_family_reading_result (decode_finite_term t)" using z pe by blast
next
  assume "root_family_reading_result (decode_finite_term t)"
  then obtain E e u r R xs ds where z: "decode_finite_term t=citation_observation_argument e (use_data_term u)
      (Payload_Term r) (data_list_term (map (\<lambda>d. definition_site_value d) ds))"
    and pe: "environment_value_presents E e" and parts: "artifact_at E u R" "distinct xs" "family_at R r (set xs)"
      "list_all2 (\<lambda>a d. located_at E u a (fst d) (snd d)) (map snd xs) ds"
    by blast
  obtain C where c: "decode_finite_environment C=E" by (rule environment_value_presents_finite[OF pe])
  have formed: "environment_formed E" using environment_value_presents_formed[OF pe] by blast
  have read: "finite_root_family_argument_read t=Some ((C,u),(r,ds))"
    using z pe by (auto simp: finite_root_family_argument_read_exact c)
  have "\<exists>ks. distinct ks \<and> length ks=length ds \<and> native_root_family_at E u r (set (zip ks ds))"
    using parts by (simp only: root_family_listed_keys[OF formed, symmetric]) blast
  then have "fBex (finite_native_root_family_readings C u r) (\<lambda>Q. finite_listed_values Q ds)"
    by (simp only: finite_root_family_listed c)
  then show "finite_root_family_reading_decision t"
    using read by (simp add: finite_root_family_reading_decision_def)
qed

corollary finite_root_family_reading_decision_meaning:
  "finite_root_family_reading_decision t \<longleftrightarrow>
    (79,decode_finite_term t)\<in>positive_meaning root_family_reading_system"
  by (simp only: finite_root_family_reading_decision_exact root_family_reading_exact)

section \<open>The counterpart of package membership (83)\<close>

text \<open>
  The argument is a source-root argument beside a member's site value. The counterpart reads the package at
  the source (@{const finite_native_source}) and asks whether the site is one of its definitions, the
  membership @{thm [source] finite_given_member} states.
\<close>

definition finite_package_subject_read :: "finite_factor_term \<Rightarrow>
    (((local_address option finite_artifact_environment\<times>local_address option)\<times>local_address)\<times>
      local_address option definition_site) option" where
  "finite_package_subject_read=finite_pair_read finite_source_root_read finite_site_value_read"

theorem finite_package_subject_read_exact:
  "finite_package_subject_read t=Some (((E,u),r),d) \<longleftrightarrow> (\<exists>e.
    decode_finite_term t=package_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value d) \<and>
    environment_value_presents (decode_finite_environment E) e)"
proof -
  have source: "finite_source_root_read v=Some z \<longleftrightarrow> (\<exists>e. decode_finite_term v=
      source_root_argument e (use_data_term (snd (fst z))) (Payload_Term (snd z)) \<and>
      environment_value_presents (decode_finite_environment (fst (fst z))) e)" for v z
  proof -
    obtain F w a where z: "z=((F,w),a)" by (metis prod.collapse)
    show ?thesis by (simp only: z finite_source_root_read_exact fst_conv snd_conv)
  qed
  have site: "finite_site_value_read v=Some x \<longleftrightarrow> decode_finite_term v=definition_site_value x" for v x
    by (cases x) (simp only: finite_site_value_read_exact fst_conv snd_conv)
  show ?thesis
    by (auto simp: finite_package_subject_read_def finite_pair_read_present[where
      P="\<lambda>z v. \<exists>e. v=source_root_argument e (use_data_term (snd (fst z))) (Payload_Term (snd z)) \<and>
        environment_value_presents (decode_finite_environment (fst (fst z))) e"
      and Q="\<lambda>x w. w=definition_site_value x", OF source site])
qed

definition finite_package_membership_decision :: "finite_factor_term \<Rightarrow> bool" where
  "finite_package_membership_decision t=(case finite_package_subject_read t of None \<Rightarrow> False
    | Some (((E,u),r),d) \<Rightarrow>
      (case finite_native_source E u r of None \<Rightarrow> False | Some P \<Rightarrow> d |\<in>| finite_system_definitions P))"

theorem finite_package_membership_decision_exact:
  "finite_package_membership_decision t \<longleftrightarrow> package_membership_result (decode_finite_term t)"
proof
  assume holds: "finite_package_membership_decision t"
  obtain E u r d where read: "finite_package_subject_read t=Some (((E,u),r),d)"
    using holds by (cases "finite_package_subject_read t")
      (auto simp: finite_package_membership_decision_def split: prod.splits)
  have member: "(case finite_native_source E u r of None \<Rightarrow> False | Some P \<Rightarrow> d |\<in>| finite_system_definitions P)"
    using holds read by (simp add: finite_package_membership_decision_def)
  obtain e where z: "decode_finite_term t=package_subject_argument e (use_data_term u) (Payload_Term r)
      (definition_site_value d)"
    and pe: "environment_value_presents (decode_finite_environment E) e"
    using read by (auto simp: finite_package_subject_read_exact)
  obtain P where "native_package_at (decode_finite_environment E) u r P" "d\<in>system_definitions P"
    using member by (auto simp: finite_given_member)
  then show "package_membership_result (decode_finite_term t)" using z pe by blast
next
  assume "package_membership_result (decode_finite_term t)"
  then obtain E e u r d P where z: "decode_finite_term t=package_subject_argument e (use_data_term u)
      (Payload_Term r) (definition_site_value d)"
    and pe: "environment_value_presents E e" and package: "native_package_at E u r P"
    and member: "d\<in>system_definitions P"
    by blast
  obtain C where c: "decode_finite_environment C=E" by (rule environment_value_presents_finite[OF pe])
  have read: "finite_package_subject_read t=Some (((C,u),r),d)"
    using z pe by (auto simp: finite_package_subject_read_exact c)
  have "(case finite_native_source C u r of None \<Rightarrow> False | Some Q \<Rightarrow> d |\<in>| finite_system_definitions Q)"
    using package member by (auto simp: finite_given_member c)
  then show "finite_package_membership_decision t"
    using read by (simp add: finite_package_membership_decision_def)
qed

corollary finite_package_membership_decision_meaning:
  "finite_package_membership_decision t \<longleftrightarrow>
    (83,decode_finite_term t)\<in>positive_meaning package_membership_system"
  by (simp only: finite_package_membership_decision_exact package_membership_exact)

section \<open>The counterpart of package retention admission (122)\<close>

text \<open>
  The argument is a site value (@{const finite_site_read}). A closed package is a package whose environment
  is closed from its use over the package's demands (@{const closed_native_package_at}); the counterpart asks
  the package reading and the finite closure (@{thm [source] finite_environment_closed_correct}) over the
  finite package demands (@{thm [source] finite_native_package_demands_correct}).
\<close>

lemma finite_closed_package:
  "(finite_native_source E u r\<noteq>None \<and> finite_environment_closed E {|u|} (finite_native_package_demands E u r)) \<longleftrightarrow>
    (\<exists>P. closed_native_package_at (decode_finite_environment E) u r P)"
  by (auto simp: finite_native_source_absent finite_environment_closed_correct
    finite_native_package_demands_correct closed_native_package_at_def)

definition finite_package_retention_admission_decision :: "finite_factor_term \<Rightarrow> bool" where
  "finite_package_retention_admission_decision t=(case finite_site_read t of None \<Rightarrow> False
    | Some (E,u,r) \<Rightarrow> finite_native_source E u r\<noteq>None \<and>
      finite_environment_closed E {|u|} (finite_native_package_demands E u r))"

theorem finite_package_retention_admission_decision_exact:
  "finite_package_retention_admission_decision t \<longleftrightarrow> package_retention_admission_result (decode_finite_term t)"
proof
  assume holds: "finite_package_retention_admission_decision t"
  obtain E u r where read: "finite_site_read t=Some (E,u,r)"
    using holds by (cases "finite_site_read t")
      (auto simp: finite_package_retention_admission_decision_def split: prod.splits)
  have closed: "finite_native_source E u r\<noteq>None \<and> finite_environment_closed E {|u|} (finite_native_package_demands E u r)"
    using holds read by (simp add: finite_package_retention_admission_decision_def)
  have present: "site_value_presents (decode_finite_environment E) u r (decode_finite_term t)"
    using read by (simp add: finite_site_read_exact)
  have ex: "\<exists>P. closed_native_package_at (decode_finite_environment E) u r P"
    using closed by (simp only: finite_closed_package)
  show "package_retention_admission_result (decode_finite_term t)" using present ex by blast
next
  assume "package_retention_admission_result (decode_finite_term t)"
  then obtain E u r P where present: "site_value_presents E u r (decode_finite_term t)"
    and closed: "closed_native_package_at E u r P"
    by blast
  have c: "decode_finite_environment (finite_environment_of E)=E"
    using site_value_presents_formed[OF present] by (simp add: decode_finite_environment_of)
  have read: "finite_site_read t=Some (finite_environment_of E,u,r)"
    using present by (simp add: finite_site_read_exact c)
  have "\<exists>P. closed_native_package_at (decode_finite_environment (finite_environment_of E)) u r P"
    using closed by (simp only: c) blast
  then have "finite_native_source (finite_environment_of E) u r\<noteq>None \<and>
      finite_environment_closed (finite_environment_of E) {|u|} (finite_native_package_demands (finite_environment_of E) u r)"
    by (simp only: finite_closed_package)
  then show "finite_package_retention_admission_decision t"
    using read by (simp add: finite_package_retention_admission_decision_def)
qed

corollary finite_package_retention_admission_decision_meaning:
  "finite_package_retention_admission_decision t \<longleftrightarrow>
    (122,decode_finite_term t)\<in>positive_meaning package_retention_admission_system"
  by (simp only: finite_package_retention_admission_decision_exact package_retention_admission_exact)

section \<open>Controls\<close>

text \<open>
  The equality program's artifact at the use @{term None} (@{const additions_control_environment}): its package
  at the address [0] holds one definition, at the address [1]; nothing is defined at [2], and the address [99]
  is outside the artifact. A second environment adds C1's one-atom artifact at the use @{term "Some [5]"},
  which no binding reaches. Each control is executed, and its relation's outcome follows beside it from the
  exactness above.
\<close>

abbreviation reader_control_environment :: "local_address option finite_artifact_environment" where
  "reader_control_environment\<equiv>additions_control_environment None"

definition reader_control_larger :: "local_address option finite_artifact_environment" where
  "reader_control_larger=finite_enumerated_environment
    [(None,finite_equality_artifact),(Some [5],counterpart_control_artifact)] []"

abbreviation reader_control_sites :: "local_address option definition_site list \<Rightarrow> finite_factor_term" where
  "reader_control_sites ds\<equiv>finite_sequence_presentation finite_site_data ds"

abbreviation reader_control_closure where
  "reader_control_closure ds\<equiv>Finite_Pair (finite_environment_value reader_control_environment) (reader_control_sites ds)"

abbreviation reader_control_family where
  "reader_control_family r ds\<equiv>Finite_Pair (Finite_Pair (finite_environment_value reader_control_environment)
    (finite_use_data None)) (Finite_Pair (Finite_Payload r) (reader_control_sites ds))"

abbreviation reader_control_member where
  "reader_control_member d\<equiv>Finite_Pair (Finite_Pair (Finite_Pair (finite_environment_value reader_control_environment)
    (finite_use_data None)) (Finite_Payload [0])) (finite_site_data d)"

text \<open>
  The controls are executed together, in one evaluation: 77 at a closed bound and at a bound holding a site
  with no definition; 79 at the root family, at the root family's address with a list omitting its site, and at
  an address holding no family; 83 at a member of the package and at a definition outside it; 122 at the
  package's least scope and at an environment holding more; and every counterpart at a term of another shape.
\<close>

lemma reader_controls:
  "finite_package_closure_admission_decision (reader_control_closure [(None,[1])]) \<and>
    \<not>finite_package_closure_admission_decision (reader_control_closure [(None,[99])]) \<and>
    finite_root_family_reading_decision (reader_control_family [0] [(None,[1])]) \<and>
    \<not>finite_root_family_reading_decision (reader_control_family [0] []) \<and>
    \<not>finite_root_family_reading_decision (reader_control_family [99] []) \<and>
    finite_package_membership_decision (reader_control_member (None,[1])) \<and>
    \<not>finite_package_membership_decision (reader_control_member (None,[2])) \<and>
    finite_package_retention_admission_decision (finite_site_presented reader_control_environment None [0]) \<and>
    \<not>finite_package_retention_admission_decision (finite_site_presented reader_control_larger None [0]) \<and>
    \<not>finite_package_closure_admission_decision (Finite_Payload []) \<and>
    \<not>finite_root_family_reading_decision (Finite_Payload []) \<and>
    \<not>finite_package_membership_decision (Finite_Payload []) \<and>
    \<not>finite_package_retention_admission_decision (Finite_Payload [])"
  by eval

lemma reader_control_closed_bound: "finite_package_closure_admission_decision (reader_control_closure [(None,[1])])"
  using reader_controls by blast

lemma reader_control_unclosed_bound: "\<not>finite_package_closure_admission_decision (reader_control_closure [(None,[99])])"
  using reader_controls by blast

lemma reader_control_family_read: "finite_root_family_reading_decision (reader_control_family [0] [(None,[1])])"
  using reader_controls by blast

lemma reader_control_family_incomplete: "\<not>finite_root_family_reading_decision (reader_control_family [0] [])"
  using reader_controls by blast

lemma reader_control_family_absent: "\<not>finite_root_family_reading_decision (reader_control_family [99] [])"
  using reader_controls by blast

lemma reader_control_member_in: "finite_package_membership_decision (reader_control_member (None,[1]))"
  using reader_controls by blast

lemma reader_control_member_out: "\<not>finite_package_membership_decision (reader_control_member (None,[2]))"
  using reader_controls by blast

lemma reader_control_least_scope:
  "finite_package_retention_admission_decision (finite_site_presented reader_control_environment None [0])"
  using reader_controls by blast

lemma reader_control_larger_scope:
  "\<not>finite_package_retention_admission_decision (finite_site_presented reader_control_larger None [0])"
  using reader_controls by blast

lemma reader_control_other:
  "\<not>finite_package_closure_admission_decision (Finite_Payload [])"
  "\<not>finite_root_family_reading_decision (Finite_Payload [])"
  "\<not>finite_package_membership_decision (Finite_Payload [])"
  "\<not>finite_package_retention_admission_decision (Finite_Payload [])"
  using reader_controls by blast+

lemmas reader_control_relations=
  reader_control_closed_bound[unfolded finite_package_closure_admission_decision_meaning]
  reader_control_unclosed_bound[unfolded finite_package_closure_admission_decision_meaning]
  reader_control_family_read[unfolded finite_root_family_reading_decision_meaning]
  reader_control_family_incomplete[unfolded finite_root_family_reading_decision_meaning]
  reader_control_family_absent[unfolded finite_root_family_reading_decision_meaning]
  reader_control_member_in[unfolded finite_package_membership_decision_meaning]
  reader_control_member_out[unfolded finite_package_membership_decision_meaning]
  reader_control_least_scope[unfolded finite_package_retention_admission_decision_meaning]
  reader_control_larger_scope[unfolded finite_package_retention_admission_decision_meaning]

end
