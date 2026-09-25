theory Development_First_Problem
  imports Development_First_Problem_Asked Development_Native_State
begin

text \<open>
  The native loop's first problem posed in its least form (DECISIONS.md "The native loop's first problem is what a
  problem is; the problem of Q2, second, exercises its answer", "The least established outside the loop to pose it"):
  an asked relation, the installed guard's entry read at the pair of a given and a candidate
  (\<open>Development_First_Problem_Asked\<close>), and a given, the native state's given (\<open>Development_Native_State\<close>). Nothing
  else is built or read: no kind, locus of a kind, key, status, origin tag or row. The posing is a generation whose
  payload presents the pair of the asked relation's program entry value and the given's site value, recorded by the
  bounded recording at the index of its own payload in the environment of the owner record of 2026-09-24 18:53, that
  record its only predecessor.

  The posing's origin is that owner record, owner-level. Its native statement, the guard with its four requirements
  and their encoding, is generated until the owner authorizes it (Q23 (a), (b)), and the least form itself is a
  residual that the first problem's admitted answer supersedes. The given is held in two payloads of the route, the
  native state's first generation's and the posing's, each recorded once: which predecessor would be the given is a
  distinction the least form does not have.
\<close>

section \<open>A program entry value, presented\<close>

text \<open>
  A program entry value is a site value beside the entry's site (@{const program_entry_value_presents}); its finite
  term is the site value presenter's term beside the entry's site data.
\<close>

definition finite_program_entry_presented :: "local_address option finite_artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option definition_site \<Rightarrow> finite_factor_term" where
  "finite_program_entry_presented E u r d=Finite_Pair (finite_site_presented E u r) (finite_site_data d)"

theorem finite_program_entry_presented_presents:
  assumes formed: "environment_formed (decode_finite_environment E)"
    and site: "(u,r)\<in>environment_positions (decode_finite_environment E)"
    and entry: "d\<in>environment_positions (decode_finite_environment E)"
  shows "program_entry_value_presents (decode_finite_environment E) u r d
    (decode_finite_term (finite_program_entry_presented E u r d))"
  unfolding program_entry_value_presents_def finite_program_entry_presented_def
  using entry finite_site_presented_presents[OF formed site] by simp

section \<open>The payload: the asked relation's program entry and the given\<close>

definition development_asked_value :: finite_factor_term where
  "development_asked_value=finite_program_entry_presented asked_environment asked_use [] asked_entry"

lemma development_asked_value_presents:
  "program_entry_value_presents (decode_finite_environment asked_environment) asked_use [] asked_entry
    (decode_finite_term development_asked_value)"
proof -
  have formed: "environment_formed (decode_finite_environment asked_environment)"
    using asked_installation(1) by (simp only: finite_environment_formed_correct)
  show ?thesis unfolding development_asked_value_def
    by (rule finite_program_entry_presented_presents[OF formed asked_entry_positions])
qed

definition development_first_problem_payload :: finite_factor_term where
  "development_first_problem_payload=Finite_Pair development_asked_value development_given_value"

theorem development_first_problem_payload_presents:
  "decode_finite_term development_first_problem_payload=
    Pair_Term (decode_finite_term development_asked_value) (decode_finite_term development_given_value)"
  "program_entry_value_presents (decode_finite_environment asked_environment) asked_use [] asked_entry
    (decode_finite_term development_asked_value)"
  "site_value_presents (decode_finite_environment given_environment) given_use [] (decode_finite_term development_given_value)"
  "term_formed (decode_finite_term development_first_problem_payload) \<and>
    self_contained_term (decode_finite_term development_first_problem_payload)"
  using asked_entry_term(3)[OF development_asked_value_presents] development_given_value_formed
  by (simp_all add: development_first_problem_payload_def development_asked_value_presents
    development_given_value_presents)

text \<open>The payload recovers both subjects: the asked relation's installation and entry, and the given's environment and site.\<close>

theorem development_first_problem_payload_recovers:
  assumes payload: "decode_finite_term development_first_problem_payload=Pair_Term t w"
    and asked: "program_entry_value_presents F v s e t" and given: "site_value_presents E u r w"
  shows "F=decode_finite_environment asked_environment \<and> v=asked_use \<and> s=[] \<and> e=asked_entry \<and>
    E=decode_finite_environment given_environment \<and> u=given_use \<and> r=[]"
proof -
  have "t=decode_finite_term development_asked_value" "w=decode_finite_term development_given_value"
    using payload development_first_problem_payload_presents(1) by simp_all
  then show ?thesis
    using program_entry_value_presents_unique[OF development_asked_value_presents, of F v s e]
      site_value_presents_unique[OF development_given_value_presents, of E u r] asked given by auto
qed

section \<open>A generation citing one recorded generation, in its environment\<close>

text \<open>
  A generation of the route is recorded in the environment of the generation it cites, that generation its only
  predecessor, by the bounded recording at the index of its own payload (@{const development_indexed_generation}). The
  premises of the recording's contract, the environment's formation and the cited row's reading, are the cited
  generation's own recorded facts, and the recorded generation's are again such facts, so a chain of citing
  generations discharges each premise from the step before.
\<close>

definition development_citing_generation ::
    "finite_factor_term \<Rightarrow> local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_citing_generation t r=(case r of (H,v,A) \<Rightarrow> development_indexed_generation t H [((v,[]),A)])"

lemma development_citing_generation_recorded:
  assumes built: "development_citing_generation t (H,v,A)=Some (B,u,G)"
    and formed: "finite_environment_formed H" and cited: "finite_check_generation A H v []"
  shows "finite_environment_formed B" "finite_environment_included H B" "finite_check_generation G B u []"
    "finite_check_generation A B v []"
proof -
  have indexed: "development_indexed_generation t H [((v,[]),A)]=Some (B,u,G)"
    using built by (simp add: development_citing_generation_def)
  have rows: "list_all (\<lambda>(d,G). finite_check_generation G H (fst d) (snd d)) [((v,[]),A)]"
    using cited by simp
  have recorded: "finite_environment_formed B" "finite_environment_included H B" "finite_check_generation G B u []"
    using development_indexed_generation_recorded[OF indexed formed rows] by blast+
  show "finite_environment_formed B" by (rule recorded(1))
  show "finite_environment_included H B" by (rule recorded(2))
  show "finite_check_generation G B u []" by (rule recorded(3))
  show "finite_check_generation A B v []"
    using development_rows_carried[OF rows recorded(2) recorded(1)] by simp
qed

theorem development_citing_generation_certified:
  assumes built: "development_citing_generation t (H,v,A)=Some (B,u,G)"
    and formed: "finite_environment_formed H" and cited: "finite_check_generation A H v []"
  obtains R d K pu E root where "generation_predecessors G={|A|}" "finite_check_generation A B v []"
    "development_data_target t=Some (generation_payload G)"
    "generation_locus G=generation_payload G" "generation_payload G=Finite_Whole R"
    "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    "bounded_certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    "finite_check_generation G B u []"
    "environment_included (decode_finite_environment H) (decode_finite_environment B)"
proof -
  have indexed: "development_indexed_generation t H [((v,[]),A)]=Some (B,u,G)"
    using built by (simp add: development_citing_generation_def)
  have rows: "list_all (\<lambda>(d,G). finite_check_generation G H (fst d) (snd d)) [((v,[]),A)]"
    using cited by simp
  show ?thesis
    by (rule development_indexed_generation_certified[OF indexed formed rows],
      rule that[OF _ development_citing_generation_recorded(4)[OF built formed cited]], simp, assumption+)
qed

section \<open>The posing\<close>

definition development_first_problem_posing ::
    "(local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_first_problem_posing=
    Option.bind development_owner_record_1853 (development_citing_generation development_first_problem_payload)"

text \<open>
  The contract is the citing generation's at the owner record of 18:53, whose premises that record's own recording
  discharges (@{thm [source] development_base_generation_recorded}).
\<close>

lemma development_first_problem_posing_cited:
  assumes posed: "development_first_problem_posing=Some (B,u,G)"
  obtains H v A where "development_owner_record_1853=Some (H,v,A)"
    "development_citing_generation development_first_problem_payload (H,v,A)=Some (B,u,G)"
    "finite_environment_formed H" "finite_check_generation A H v []"
proof -
  obtain z where record0: "development_owner_record_1853=Some z"
    and built0: "development_citing_generation development_first_problem_payload z=Some (B,u,G)"
    using posed unfolding development_first_problem_posing_def bind_eq_Some_conv by blast
  obtain H v A where z: "z=(H,v,A)" by (metis prod_cases3)
  have owner: "development_owner_record_1853=Some (H,v,A)"
    and built: "development_citing_generation development_first_problem_payload (H,v,A)=Some (B,u,G)"
    using record0 built0 unfolding z by blast+
  have base: "development_base_generation development_owner_direction_1853=Some (H,v,A)"
    using owner by (simp only: development_owner_record_1853_def development_owner_record_def)
  show ?thesis
    by (rule that[OF owner built development_base_generation_recorded(1)[OF base]
      development_base_generation_recorded(3)[OF base]])
qed

theorem development_first_problem_posing_certified:
  assumes posed: "development_first_problem_posing=Some (B,u,G)"
  obtains H v A R d K pu E root where "development_owner_record_1853=Some (H,v,A)"
    "generation_predecessors G={|A|}" "finite_check_generation A B v []"
    "development_data_target development_first_problem_payload=Some (generation_payload G)"
    "generation_locus G=generation_payload G" "generation_payload G=Finite_Whole R"
    "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    "bounded_certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    "finite_check_generation G B u []"
    "environment_included (decode_finite_environment H) (decode_finite_environment B)"
proof -
  obtain H v A where owner: "development_owner_record_1853=Some (H,v,A)"
    and built: "development_citing_generation development_first_problem_payload (H,v,A)=Some (B,u,G)"
    and formed: "finite_environment_formed H" and cited: "finite_check_generation A H v []"
    by (rule development_first_problem_posing_cited[OF posed])
  show ?thesis
    by (rule development_citing_generation_certified[OF built formed cited]) (rule that[OF owner], assumption+)
qed

corollary development_first_problem_posing_recorded:
  assumes posed: "development_first_problem_posing=Some (B,u,G)"
  shows "finite_environment_formed B" "finite_check_generation G B u []"
proof -
  obtain H v A where built: "development_citing_generation development_first_problem_payload (H,v,A)=Some (B,u,G)"
    and formed: "finite_environment_formed H" and cited: "finite_check_generation A H v []"
    by (rule development_first_problem_posing_cited[OF posed])
  show "finite_environment_formed B" "finite_check_generation G B u []"
    using development_citing_generation_recorded(1,3)[OF built formed cited] by blast+
qed

section \<open>The posing's meaning\<close>

text \<open>
  For every candidate site value, the asked relation holds of the pair of the given and the candidate exactly when
  @{const asked_relation} holds of their site contexts: the installed guard's contract at the given.
\<close>

theorem development_first_problem_meaning:
  assumes candidate: "site_value_presents F v s w"
  shows "(asked_entry,Pair_Term (decode_finite_term development_given_value) w)\<in>positive_meaning asked_program \<longleftrightarrow>
    asked_relation ((decode_finite_environment given_environment,given_use,[]),(F,v,s))"
  by (rule asked_entry_on_values[OF development_given_value_presents candidate])

end
