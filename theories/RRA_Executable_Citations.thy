theory RRA_Executable_Citations
  imports RRA_Executable_Syntax
begin

section \<open>Citation forms are recovered from actual incidence and payloads\<close>

definition finite_payload_values ::
  "('a,'v) finite_structured_object \<Rightarrow> 'a \<Rightarrow> 'v fset" where
  "finite_payload_values C a =
    fimage snd (ffilter (\<lambda>(b,v). b=a) (finite_bindings (finite_data C)))"

lemma finite_payload_values_member:
  "v |\<in>| finite_payload_values C a \<longleftrightarrow> (a,v) |\<in>| finite_bindings (finite_data C)"
  by (auto simp: finite_payload_values_def fimage.rep_eq split: prod.splits intro: rev_image_eqI; force)

lemma finite_payload_at_has_value:
  assumes "finite_payload_at C a v"
  shows "v |\<in>| finite_payload_values C a"
  using payload_at_binding[OF assms[unfolded finite_payload_at_correct]]
  by (simp add: finite_payload_values_member decode_finite_basis_def)

fun finite_raw_citation_at ::
  "finite_exact_artifact \<Rightarrow> local_address \<Rightarrow> citation \<Rightarrow> local_address fset \<Rightarrow> bool" where
  "finite_raw_citation_at C r (Local a) I \<longleftrightarrow>
    finite_headed_incidence (finite_structure C) r={|(r,a)|} \<and> I={|r|}"
| "finite_raw_citation_at C r Local_Whole I \<longleftrightarrow>
    finite_headed_incidence (finite_structure C) r={||} \<and> I={|r|}"
| "finite_raw_citation_at C r (External_Whole k) I \<longleftrightarrow>
    r\<noteq>k \<and> finite_headed_incidence (finite_structure C) r={|(k,k)|} \<and> I={|r|}"
| "finite_raw_citation_at C r (External k a) I \<longleftrightarrow>
    fBex (finite_headed_incidence (finite_structure C) r) (\<lambda>(p,d).
      p=k \<and> distinct [r,k,d] \<and>
      finite_headed_incidence (finite_structure C) r={|(r,k),(k,d)|} \<and>
      finite_headed_incidence (finite_structure C) d={||} \<and>
      finite_payload_at C d a \<and> I={|r,d|})"

lemma raw_local_citation_iff:
  "raw_citation_at R r (Local a) I \<longleftrightarrow> headed_incidence (object_structure R) r={(r,a)} \<and> I={r}"
proof
  assume read: "raw_citation_at R r (Local a) I"
  show "headed_incidence (object_structure R) r={(r,a)} \<and> I={r}"
    using read by (cases rule: raw_citation_at.cases) auto
next
  assume "headed_incidence (object_structure R) r={(r,a)} \<and> I={r}"
  then show "raw_citation_at R r (Local a) I" by (auto intro: raw_citation_at.local)
qed

lemma raw_local_whole_citation_iff:
  "raw_citation_at R r Local_Whole I \<longleftrightarrow> headed_incidence (object_structure R) r={} \<and> I={r}"
proof
  assume read: "raw_citation_at R r Local_Whole I"
  show "headed_incidence (object_structure R) r={} \<and> I={r}"
    using read by (cases rule: raw_citation_at.cases) auto
next
  assume "headed_incidence (object_structure R) r={} \<and> I={r}"
  then show "raw_citation_at R r Local_Whole I" by (auto intro: raw_citation_at.local_whole)
qed

lemma raw_external_whole_citation_iff:
  "raw_citation_at R r (External_Whole k) I \<longleftrightarrow>
    r\<noteq>k \<and> headed_incidence (object_structure R) r={(k,k)} \<and> I={r}"
proof
  assume read: "raw_citation_at R r (External_Whole k) I"
  show "r\<noteq>k \<and> headed_incidence (object_structure R) r={(k,k)} \<and> I={r}"
    using read by (cases rule: raw_citation_at.cases) auto
next
  assume "r\<noteq>k \<and> headed_incidence (object_structure R) r={(k,k)} \<and> I={r}"
  then show "raw_citation_at R r (External_Whole k) I" by (auto intro: raw_citation_at.external_whole)
qed

lemma raw_external_citation_iff:
  "raw_citation_at R r (External k a) I \<longleftrightarrow>
    (\<exists>d. distinct [r,k,d] \<and> headed_incidence (object_structure R) r={(r,k),(k,d)} \<and>
      headed_incidence (object_structure R) d={} \<and> payload_at R d a \<and> I={r,d})"
proof
  assume read: "raw_citation_at R r (External k a) I"
  show "\<exists>d. distinct [r,k,d] \<and> headed_incidence (object_structure R) r={(r,k),(k,d)} \<and>
      headed_incidence (object_structure R) d={} \<and> payload_at R d a \<and> I={r,d}"
    using read by (cases rule: raw_citation_at.cases) auto
next
  assume supplied: "\<exists>d. distinct [r,k,d] \<and> headed_incidence (object_structure R) r={(r,k),(k,d)} \<and>
      headed_incidence (object_structure R) d={} \<and> payload_at R d a \<and> I={r,d}"
  obtain d where separate: "distinct [r,k,d]" and head: "headed_incidence (object_structure R) r={(r,k),(k,d)}"
    and leaf: "headed_incidence (object_structure R) d={}" and payload: "payload_at R d a" and interior: "I={r,d}"
    using supplied by blast
  have read: "raw_citation_at R r (External k a) {r,d}"
    by (rule raw_citation_at.external[OF separate head leaf payload])
  show "raw_citation_at R r (External k a) I" using read interior by simp
qed

lemma finite_raw_citation_at_correct:
  "finite_raw_citation_at C r c I \<longleftrightarrow> raw_citation_at (decode_finite_object C) r c (fset I)"
proof -
  have external: "\<And>k a. finite_raw_citation_at C r (External k a) I \<longleftrightarrow>
      (\<exists>d. distinct [r,k,d] \<and> finite_headed_incidence (finite_structure C) r={|(r,k),(k,d)|} \<and>
        finite_headed_incidence (finite_structure C) d={||} \<and> finite_payload_at C d a \<and> I={|r,d|})"
    by (auto simp: Bex_def split_paired_Ex)
  show ?thesis
  proof (cases c)
    case (Local a)
    show ?thesis by (simp add: Local raw_local_citation_iff fset_inject[symmetric] finite_headed_incidence_correct)
  next
    case (External k a)
    show ?thesis
      by (simp only: External external raw_external_citation_iff)
         (simp add: finite_payload_at_correct fset_inject[symmetric] finite_headed_incidence_correct)
  next
    case Local_Whole
    show ?thesis by (simp add: Local_Whole raw_local_whole_citation_iff fset_inject[symmetric] finite_headed_incidence_correct)
  next
    case (External_Whole k)
    show ?thesis by (simp add: External_Whole raw_external_whole_citation_iff fset_inject[symmetric] finite_headed_incidence_correct)
  qed
qed

definition finite_citation_at ::
  "finite_exact_artifact \<Rightarrow> local_address \<Rightarrow> citation \<Rightarrow> local_address fset \<Rightarrow> bool" where
  "finite_citation_at C r c I \<longleftrightarrow>
    finite_exact_formed C \<and> r |\<in>| finite_carrier (finite_structure C) \<and>
    finite_data_empty_on C {|r|} \<and> finite_raw_citation_at C r c I"

lemma finite_citation_at_correct:
  "finite_citation_at C r c I \<longleftrightarrow> citation_at (decode_finite_object C) r c (fset I)"
  by (simp add: finite_citation_at_def citation_at_def finite_exact_formed_correct
      finite_data_empty_on_correct finite_raw_citation_at_correct)

definition finite_citation_choices ::
  "finite_exact_artifact \<Rightarrow> local_address \<Rightarrow> (citation \<times> local_address fset) fset" where
  "finite_citation_choices C r =
    {|(Local_Whole,{|r|})|} |\<union>|
    fimage (\<lambda>(p,a). (Local a,{|r|})) (finite_headed_incidence (finite_structure C) r) |\<union>|
    fimage (\<lambda>(k,x). (External_Whole k,{|r|})) (finite_headed_incidence (finite_structure C) r) |\<union>|
    ffUnion (fimage (\<lambda>(k,d). fimage (\<lambda>a. (External k a,{|r,d|})) (finite_payload_values C d))
      (finite_headed_incidence (finite_structure C) r))"

lemma finite_citation_choices_complete:
  assumes "finite_raw_citation_at C r c I"
  shows "(c,I) |\<in>| finite_citation_choices C r"
proof (cases c)
  case (Local a)
  then show ?thesis using assms by (simp add: finite_citation_choices_def)
next
  case (External k a)
  obtain d where head: "finite_headed_incidence (finite_structure C) r={|(r,k),(k,d)|}"
    and payload: "finite_payload_at C d a" and interior: "I={|r,d|}"
    using assms External by auto
  have member: "a |\<in>| finite_payload_values C d" by (rule finite_payload_at_has_value[OF payload])
  show ?thesis using member
    by (auto simp: External interior finite_citation_choices_def head fimage.rep_eq ffUnion.rep_eq
        split: prod.splits intro: rev_image_eqI)
next
  case Local_Whole
  then show ?thesis using assms by (simp add: finite_citation_choices_def)
next
  case (External_Whole k)
  then show ?thesis using assms by (simp add: finite_citation_choices_def)
qed

definition finite_citation_candidates ::
  "finite_exact_artifact \<Rightarrow> local_address \<Rightarrow> (citation \<times> local_address fset) fset" where
  "finite_citation_candidates C r =
    ffilter (\<lambda>(c,I). finite_citation_at C r c I) (finite_citation_choices C r)"

theorem finite_citation_candidates_correct:
  "(c,I) |\<in>| finite_citation_candidates C r \<longleftrightarrow>
    citation_at (decode_finite_object C) r c (fset I)"
  using finite_citation_choices_complete[of C r c I]
  by (auto simp: finite_citation_candidates_def finite_citation_at_correct[symmetric] finite_citation_at_def)

lemma finite_citation_candidates_complete:
  assumes read: "citation_at (decode_finite_object C) r c I"
  shows "\<exists>F. (c,F) |\<in>| finite_citation_candidates C r \<and> fset F=I"
proof -
  have raw: "raw_citation_at (decode_finite_object C) r c I" using read by (simp add: citation_at_def)
  have finite: "finite I" by (rule raw_citation_interior(1)[OF raw])
  have represented: "fset (Abs_fset I)=I" by (rule Abs_fset_inverse) (simp add: finite)
  have member: "(c,Abs_fset I) |\<in>| finite_citation_candidates C r"
    using read represented by (simp add: finite_citation_candidates_correct)
  show ?thesis using represented member by blast
qed

corollary finite_citation_candidates_unique:
  assumes "(c,I) |\<in>| finite_citation_candidates C r" "(d,J) |\<in>| finite_citation_candidates C r"
  shows "c=d \<and> I=J"
proof -
  have first: "citation_at (decode_finite_object C) r c (fset I)"
    and second: "citation_at (decode_finite_object C) r d (fset J)"
    using assms by (simp_all add: finite_citation_candidates_correct)
  show ?thesis using citation_at_unique[OF first second] by (simp add: fset_inject)
qed

section \<open>Environment lookup preserves the exact supplied artifact values\<close>

definition finite_artifacts_at :: "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> finite_exact_artifact fset" where
  "finite_artifacts_at E u =
    fimage snd (ffilter (\<lambda>(v,C). v=u) (finite_environment_artifacts E))"

lemma finite_artifacts_at_member:
  "C |\<in>| finite_artifacts_at E u \<longleftrightarrow> (u,C) |\<in>| finite_environment_artifacts E"
  by (auto simp: finite_artifacts_at_def fimage.rep_eq split: prod.splits intro: rev_image_eqI; force)

lemma finite_artifacts_at_complete:
  "artifact_at (decode_finite_environment E) u R \<longleftrightarrow>
    (\<exists>C\<in>fset (finite_artifacts_at E u). decode_finite_object C=R)"
  by (auto simp: finite_artifacts_at_member)

definition finite_bound_artifacts ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> finite_exact_artifact fset" where
  "finite_bound_artifacts E u k = ffUnion (fimage (\<lambda>((v,l),w).
    if v=u \<and> l=k then finite_artifacts_at E w else {||}) (finite_environment_bindings E))"

lemma finite_bound_artifacts_member:
  "C |\<in>| finite_bound_artifacts E u k \<longleftrightarrow>
    (\<exists>v. ((u,k),v) |\<in>| finite_environment_bindings E \<and> C |\<in>| finite_artifacts_at E v)"
  by (auto simp: finite_bound_artifacts_def fimage.rep_eq ffUnion.rep_eq split: prod.splits if_splits; force)

lemma finite_bound_artifacts_complete:
  "(\<exists>v. binds_slot (decode_finite_environment E) u k v \<and> artifact_at (decode_finite_environment E) v R) \<longleftrightarrow>
    (\<exists>C\<in>fset (finite_bound_artifacts E u k). decode_finite_object C=R)"
  by (auto simp: binds_slot_def finite_bound_artifacts_member finite_artifacts_at_member)

fun finite_citation_targets ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> citation \<Rightarrow> finite_exact_target fset" where
  "finite_citation_targets E u (Local a) =
    fimage (\<lambda>C. Finite_Anchor C a)
      (ffilter (\<lambda>C. finite_target_formed (Finite_Anchor C a)) (finite_artifacts_at E u))"
| "finite_citation_targets E u (External k a) =
    fimage (\<lambda>C. Finite_Anchor C a)
      (ffilter (\<lambda>C. finite_target_formed (Finite_Anchor C a)) (finite_bound_artifacts E u k))"
| "finite_citation_targets E u Local_Whole =
    fimage Finite_Whole (ffilter finite_exact_formed (finite_artifacts_at E u))"
| "finite_citation_targets E u (External_Whole k) =
    fimage Finite_Whole (ffilter finite_exact_formed (finite_bound_artifacts E u k))"

theorem finite_citation_targets_complete:
  "interpret_citation (decode_finite_environment E) u c t \<longleftrightarrow>
    (\<exists>T\<in>fset (finite_citation_targets E u c). decode_finite_target T=t)"
  by (cases c; auto simp: finite_bound_artifacts_member finite_artifacts_at_member binds_slot_def
      fimage.rep_eq finite_exact_formed_correct anchor_formed_def Bex_def; blast)

lemma finite_citation_targets_member:
  "T |\<in>| finite_citation_targets E u c \<longleftrightarrow>
    interpret_citation (decode_finite_environment E) u c (decode_finite_target T)"
  by (simp add: finite_citation_targets_complete)

fun finite_citation_locations ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> citation \<Rightarrow> ('u \<times> local_address) fset" where
  "finite_citation_locations E u (Local a) =
    (if fBex (finite_artifacts_at E u) (\<lambda>C. finite_target_formed (Finite_Anchor C a))
     then {|(u,a)|} else {||})"
| "finite_citation_locations E u (External k a) =
    fimage (\<lambda>((v,l),w). (w,a)) (ffilter (\<lambda>((v,l),w). v=u \<and> l=k \<and>
      fBex (finite_artifacts_at E w) (\<lambda>C. finite_target_formed (Finite_Anchor C a)))
      (finite_environment_bindings E))"
| "finite_citation_locations E u Local_Whole = {||}"
| "finite_citation_locations E u (External_Whole k) = {||}"

theorem finite_citation_locations_correct:
  "(v,a) |\<in>| finite_citation_locations E u c \<longleftrightarrow>
    citation_location (decode_finite_environment E) u c v a"
proof -
  have available: "\<And>v a. fBex (finite_artifacts_at E v) (\<lambda>C. finite_target_formed (Finite_Anchor C a)) \<longleftrightarrow>
      (\<exists>R. artifact_at (decode_finite_environment E) v R \<and> anchor_formed (R,a))"
    by (auto simp: finite_artifacts_at_member finite_exact_formed_correct anchor_formed_def Bex_def; blast)
  show ?thesis
    by (cases c; simp only: finite_citation_locations.simps citation_location.simps available;
        auto simp: binds_slot_def fimage.rep_eq split: prod.splits if_splits intro: rev_image_eqI; force)
qed

fun finite_citation_slots :: "citation \<Rightarrow> local_address fset" where
  "finite_citation_slots (Local a)={||}"
| "finite_citation_slots Local_Whole={||}"
| "finite_citation_slots (External k a)={|k|}"
| "finite_citation_slots (External_Whole k)={|k|}"

lemma finite_citation_slots_correct:
  "fset (finite_citation_slots c)=citation_slots c"
  by (cases c) simp_all

export_code finite_citation_candidates finite_citation_targets finite_citation_locations finite_citation_slots checking SML

text \<open>
  Citation recognition recovers the structural form and its exact interior.
  Target recovery follows only the supplied environment bindings and retains
  the complete target artifact. Location recovery keeps the target use occurrence
  as a separate projection. Equal artifact values at different uses therefore
  remain distinct locations. No ambient resolver participates.
\<close>

end
