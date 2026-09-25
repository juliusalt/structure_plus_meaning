theory Factor_Inclusion_Admission_Counterparts
  imports Finite_Presentation_Readers Factor_Finite_Environment_Value_Readers RRA_Finite_Inclusion
    Factor_Finite_Native_Sources Factor_Environment_Inclusion Factor_Package_Admission
    Factor_Executable_Environment_Values_Base
begin

section \<open>The two argument shapes\<close>

text \<open>
  A pair of environment values, each component read by the environment value reader; and a
  source-root argument, an environment value beside a use's data term, beside an address payload.
  Each reader is exact at every term to the presentation relation of its shape.
\<close>

definition finite_environment_pair_read :: "finite_factor_term \<Rightarrow>
    (local_address option finite_artifact_environment\<times>local_address option finite_artifact_environment) option" where
  "finite_environment_pair_read=finite_pair_read finite_environment_value_read finite_environment_value_read"

theorem finite_environment_pair_read_exact:
  "finite_environment_pair_read t=Some (E,F) \<longleftrightarrow> (\<exists>e f. decode_finite_term t=Pair_Term e f \<and>
    environment_value_presents (decode_finite_environment E) e \<and>
    environment_value_presents (decode_finite_environment F) f)"
  unfolding finite_environment_pair_read_def
  by (rule finite_pair_read_present[where P="\<lambda>E e. environment_value_presents (decode_finite_environment E) e"
    and Q="\<lambda>E e. environment_value_presents (decode_finite_environment E) e",
    OF finite_environment_value_read_exact finite_environment_value_read_exact])

definition finite_source_root_read :: "finite_factor_term \<Rightarrow>
    ((local_address option finite_artifact_environment\<times>local_address option)\<times>local_address) option" where
  "finite_source_root_read=
    finite_pair_read (finite_pair_read finite_environment_value_read finite_use_value_read) finite_payload_value_read"

theorem finite_source_root_read_exact:
  "finite_source_root_read t=Some ((E,u),r) \<longleftrightarrow> (\<exists>e.
    decode_finite_term t=source_root_argument e (use_data_term u) (Payload_Term r) \<and>
    environment_value_presents (decode_finite_environment E) e)"
proof -
  have inner: "\<And>v z. finite_pair_read finite_environment_value_read finite_use_value_read v=Some z \<longleftrightarrow>
      (\<exists>e. decode_finite_term v=Pair_Term e (use_data_term (snd z)) \<and>
        environment_value_presents (decode_finite_environment (fst z)) e)"
  proof -
    fix v and z :: "local_address option finite_artifact_environment\<times>local_address option"
    obtain F w where z: "z=(F,w)" by (cases z)
    show "finite_pair_read finite_environment_value_read finite_use_value_read v=Some z \<longleftrightarrow>
      (\<exists>e. decode_finite_term v=Pair_Term e (use_data_term (snd z)) \<and>
        environment_value_presents (decode_finite_environment (fst z)) e)"
      by (auto simp: z finite_pair_read_present[where P="\<lambda>E e. environment_value_presents (decode_finite_environment E) e"
        and Q="\<lambda>u w. w=use_data_term u", OF finite_environment_value_read_exact finite_use_value_read_exact])
  qed
  show ?thesis
    by (auto simp: finite_source_root_read_def finite_pair_read_present[where
      P="\<lambda>z v. \<exists>e. v=Pair_Term e (use_data_term (snd z)) \<and>
        environment_value_presents (decode_finite_environment (fst z)) e"
      and Q="\<lambda>r w. w=Payload_Term r", OF inner finite_payload_value_read_exact])
qed


section \<open>A site value, read back and presented\<close>

text \<open>
  A site value is an environment value beside a site's data term, the site a position of the environment
  (@{const site_value_presents}). Its reader reads the environment and the site by their own readers, as a pair
  (@{thm [source] finite_pair_read_present}), and keeps the reading only when the site is a position of the
  environment read; every other term is read as nothing. A site value has one presentation for every enumeration
  of its environment's tables, so the reader is exact in the relational form of @{const finite_reads}: a term is
  read as an environment, a use and an address exactly when it presents them.
\<close>

definition finite_site_read :: "finite_factor_term \<Rightarrow>
    (local_address option finite_artifact_environment\<times>local_address option\<times>local_address) option" where
  "finite_site_read t=(case finite_pair_read finite_environment_value_read finite_site_value_read t of
    None \<Rightarrow> None
  | Some (E,u,r) \<Rightarrow> if (u,r) |\<in>| finite_environment_positions E then Some (E,u,r) else None)"

theorem finite_site_read_exact:
  "finite_site_read t=Some (E,u,r) \<longleftrightarrow>
    site_value_presents (decode_finite_environment E) u r (decode_finite_term t)"
proof -
  have site: "finite_site_value_read v=Some y \<longleftrightarrow> decode_finite_term v=site_data_term (fst y) (snd y)" for v y
    by (cases y) (simp only: finite_site_value_read_exact fst_conv snd_conv)
  have pair: "finite_pair_read finite_environment_value_read finite_site_value_read t=Some (E,(u,r)) \<longleftrightarrow>
      (\<exists>e q. decode_finite_term t=Pair_Term e q \<and> environment_value_presents (decode_finite_environment E) e \<and>
        q=site_data_term u r)"
    using finite_pair_read_present[where P="\<lambda>E e. environment_value_presents (decode_finite_environment E) e"
      and Q="\<lambda>y q. q=site_data_term (fst y) (snd y)", OF finite_environment_value_read_exact site, of t E "(u,r)"]
    by simp
  have "finite_site_read t=Some (E,u,r) \<longleftrightarrow>
      finite_pair_read finite_environment_value_read finite_site_value_read t=Some (E,(u,r)) \<and>
      (u,r) |\<in>| finite_environment_positions E"
    by (auto simp: finite_site_read_def split: option.splits prod.splits if_splits)
  then show ?thesis
    by (auto simp: pair site_value_presents_def finite_environment_positions_correct[symmetric])
qed

text \<open>
  The presenter of a site value: the environment's complete value beside the site's data. At a formed
  environment and one of its positions it presents that site value, and the reader reads it back as exactly the
  environment and the site it presents.
\<close>

definition finite_site_presented :: "local_address option finite_artifact_environment \<Rightarrow> local_address option \<Rightarrow>
    local_address \<Rightarrow> finite_factor_term" where
  "finite_site_presented E u r=Finite_Pair (finite_environment_value E) (finite_site_data (u,r))"

theorem finite_site_presented_presents:
  assumes formed: "environment_formed (decode_finite_environment E)"
    and site: "(u,r)\<in>environment_positions (decode_finite_environment E)"
  shows "site_value_presents (decode_finite_environment E) u r (decode_finite_term (finite_site_presented E u r))"
proof -
  have environment: "environment_value_presents (decode_finite_environment E) (decode_finite_term (finite_environment_value E))"
    using formed by (simp only: finite_environment_value_exact finite_environment_formed_correct simp_thms)
  show ?thesis unfolding site_value_presents_def finite_site_presented_def using site environment by simp
qed

corollary finite_site_presented_read:
  assumes "environment_formed (decode_finite_environment E)" "(u,r)\<in>environment_positions (decode_finite_environment E)"
  shows "finite_site_read (finite_site_presented E u r)=Some (E,u,r)"
  by (simp only: finite_site_read_exact finite_site_presented_presents[OF assms])

section \<open>The counterpart of environment inclusion (113)\<close>

text \<open>
  On a term read as a pair of environment values the counterpart compares the two finite
  environments' complete tables; every other term it refuses. It is exact at every finite term to
  the result relation of inclusion, and so to the positive meaning of site 113 in inclusion's own
  system: it decides nothing that relation does not state.
\<close>

definition finite_environment_inclusion_decision :: "finite_factor_term \<Rightarrow> bool" where
  "finite_environment_inclusion_decision t=(case finite_environment_pair_read t of None \<Rightarrow> False
    | Some (E,F) \<Rightarrow> finite_environment_included E F)"

theorem finite_environment_inclusion_decision_exact:
  "finite_environment_inclusion_decision t \<longleftrightarrow> environment_inclusion_result (decode_finite_term t)"
proof
  assume "finite_environment_inclusion_decision t"
  then obtain E F where read: "finite_environment_pair_read t=Some (E,F)"
    and included: "finite_environment_included E F"
    by (auto simp: finite_environment_inclusion_decision_def split: option.splits)
  from read obtain e f where "decode_finite_term t=Pair_Term e f"
    "environment_value_presents (decode_finite_environment E) e"
    "environment_value_presents (decode_finite_environment F) f"
    by (auto simp: finite_environment_pair_read_exact)
  with included show "environment_inclusion_result (decode_finite_term t)"
    by (auto simp: finite_environment_included_correct)
next
  assume "environment_inclusion_result (decode_finite_term t)"
  then obtain E F e f where z: "decode_finite_term t=Pair_Term e f" and pe: "environment_value_presents E e"
    and pf: "environment_value_presents F f" and included: "environment_included E F"
    by blast
  obtain C where c: "decode_finite_environment C=E" by (rule environment_value_presents_finite[OF pe])
  obtain D where d: "decode_finite_environment D=F" by (rule environment_value_presents_finite[OF pf])
  have "finite_environment_pair_read t=Some (C,D)"
    using z pe pf by (auto simp: finite_environment_pair_read_exact c d)
  then show "finite_environment_inclusion_decision t"
    using included by (simp add: finite_environment_inclusion_decision_def finite_environment_included_correct c d)
qed

corollary finite_environment_inclusion_decision_meaning:
  "finite_environment_inclusion_decision t \<longleftrightarrow>
    (113,decode_finite_term t)\<in>positive_meaning environment_inclusion_system"
  by (simp only: finite_environment_inclusion_decision_exact environment_inclusion_exact)

section \<open>The counterpart of package admission (80)\<close>

text \<open>
  On a term read as a source-root argument the counterpart asks whether the complete native source
  reader returns a program at the argument's use and address; every other term it refuses. It is
  exact at every finite term to package admission's result relation, and so to the positive meaning
  of site 80 in package admission's own system.
\<close>

definition finite_package_admission_decision :: "finite_factor_term \<Rightarrow> bool" where
  "finite_package_admission_decision t=(case finite_source_root_read t of None \<Rightarrow> False
    | Some ((E,u),r) \<Rightarrow> finite_native_source E u r\<noteq>None)"

theorem finite_package_admission_decision_exact:
  "finite_package_admission_decision t \<longleftrightarrow> package_admission_result (decode_finite_term t)"
proof
  assume "finite_package_admission_decision t"
  then obtain E u r where read: "finite_source_root_read t=Some ((E,u),r)"
    and source: "finite_native_source E u r\<noteq>None"
    by (auto simp: finite_package_admission_decision_def split: option.splits)
  from read obtain e where "decode_finite_term t=source_root_argument e (use_data_term u) (Payload_Term r)"
    "environment_value_presents (decode_finite_environment E) e"
    by (auto simp: finite_source_root_read_exact)
  moreover from source obtain N where "native_package_at (decode_finite_environment E) u r N"
    by (auto simp: finite_native_source_absent)
  ultimately show "package_admission_result (decode_finite_term t)" by blast
next
  assume "package_admission_result (decode_finite_term t)"
  then obtain E e u r N where z: "decode_finite_term t=source_root_argument e (use_data_term u) (Payload_Term r)"
    and pe: "environment_value_presents E e" and package: "native_package_at E u r N"
    by blast
  obtain C where c: "decode_finite_environment C=E" by (rule environment_value_presents_finite[OF pe])
  have "finite_source_root_read t=Some ((C,u),r)"
    using z pe by (auto simp: finite_source_root_read_exact c)
  moreover have "finite_native_source C u r\<noteq>None"
    using package by (auto simp: finite_native_source_absent c)
  ultimately show "finite_package_admission_decision t"
    by (simp add: finite_package_admission_decision_def)
qed

corollary finite_package_admission_decision_meaning:
  "finite_package_admission_decision t \<longleftrightarrow>
    (80,decode_finite_term t)\<in>positive_meaning package_admission_system"
  by (simp only: finite_package_admission_decision_exact package_admission_exact)

section \<open>Controls\<close>

text \<open>
  Two environments: the empty one (@{const finite_empty_environment}), and one holding a single
  artifact at the use @{term None} whose
  carrier is the empty address alone, with no incidence and no data. The empty address of that
  artifact holds the empty root family, so the empty package; the address [1] is outside its
  carrier and holds none. Each control is executed, and its relation's outcome follows beside it
  from the exactness above.
\<close>

abbreviation counterpart_control_empty :: "local_address option finite_artifact_environment" where
  "counterpart_control_empty\<equiv>finite_empty_environment"

definition counterpart_control_artifact :: finite_exact_artifact where
  "counterpart_control_artifact=\<lparr>finite_structure=\<lparr>finite_carrier={|[]|},finite_incidence={||}\<rparr>,
    finite_data=\<lparr>finite_bag={#},finite_bindings={||}\<rparr>\<rparr>"

definition counterpart_control_rooted :: "local_address option finite_artifact_environment" where
  "counterpart_control_rooted=\<lparr>finite_environment_artifacts={|(None,counterpart_control_artifact)|},
    finite_environment_bindings={||}\<rparr>"

abbreviation counterpart_control_pair where
  "counterpart_control_pair E F\<equiv>Finite_Pair (finite_environment_value E) (finite_environment_value F)"

abbreviation counterpart_control_source where
  "counterpart_control_source r\<equiv>
    Finite_Pair (Finite_Pair (finite_environment_value counterpart_control_rooted) (Finite_Payload [])) (Finite_Payload r)"

text \<open>The readers at a presented and at a malformed term.\<close>

lemma counterpart_control_pair_read:
  "finite_environment_pair_read (counterpart_control_pair counterpart_control_empty counterpart_control_rooted)=
    Some (counterpart_control_empty,counterpart_control_rooted)"
  by eval

lemma counterpart_control_pair_read_malformed:
  "finite_environment_pair_read (Finite_Pair (finite_environment_value counterpart_control_empty) (Finite_Payload [1]))=None"
  by eval

lemma counterpart_control_source_read:
  "finite_source_root_read (counterpart_control_source [])=Some ((counterpart_control_rooted,None),[])"
  by eval

lemma counterpart_control_source_read_malformed:
  "finite_source_root_read (Finite_Pair (Finite_Pair (finite_environment_value counterpart_control_rooted)
    (Finite_Payload [1])) (Finite_Payload []))=None"
  by eval

text \<open>Inclusion at an included and at a non-included pair, and at a term of another shape.\<close>

lemma counterpart_control_included:
  "finite_environment_inclusion_decision (counterpart_control_pair counterpart_control_empty counterpart_control_rooted)"
  by eval

lemma counterpart_control_not_included:
  "\<not>finite_environment_inclusion_decision (counterpart_control_pair counterpart_control_rooted counterpart_control_empty)"
  by eval

lemma counterpart_control_inclusion_other:
  "\<not>finite_environment_inclusion_decision (Finite_Payload [])"
  by eval

lemmas counterpart_control_inclusion_relations=
  counterpart_control_included[unfolded finite_environment_inclusion_decision_meaning]
  counterpart_control_not_included[unfolded finite_environment_inclusion_decision_meaning]
  counterpart_control_inclusion_other[unfolded finite_environment_inclusion_decision_meaning]

text \<open>Package admission at an address holding a package, at one holding none, and at a term of another shape.\<close>

lemma counterpart_control_admitted:
  "finite_package_admission_decision (counterpart_control_source [])"
  by eval

lemma counterpart_control_not_admitted:
  "\<not>finite_package_admission_decision (counterpart_control_source [1])"
  by eval

lemma counterpart_control_admission_other:
  "\<not>finite_package_admission_decision (Finite_Payload [])"
  by eval

lemmas counterpart_control_admission_relations=
  counterpart_control_admitted[unfolded finite_package_admission_decision_meaning]
  counterpart_control_not_admitted[unfolded finite_package_admission_decision_meaning]
  counterpart_control_admission_other[unfolded finite_package_admission_decision_meaning]

end
