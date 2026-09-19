theory Development_Certified_Generations
  imports Development_Publication Development_Policy Factor_Certificate_Policy_Readiness
    Factor_Finite_Native_Proof_Construction
begin

section \<open>A policy's judgment of a payload\<close>

text \<open>
  A policy admits a payload when its entry holds of the whole payload. The judgment is made
  natively. The policy's program is read back from its source once, certificates are constructed for
  the demand of every definition of that program on the payload (the policy's entry calls the listing
  entry on the same payload, so the demand of the entry alone is not closed), and the certificate of
  the entry's call is selected; a missing or ambiguous certificate judges nothing. The certificate is
  replayed in the least environment that retains the program, the call and the proof, the replayed
  scope is quoted, and the quoted scope is checked to be the policy's own call. The judgment depends on
  the listed presentations and the payload alone, not on any environment of generations, so one
  judgment serves every generation recorded with that payload.
\<close>

definition development_policy_certificate ::
    "local_address option finite_artifact_environment \<Rightarrow> local_address option \<Rightarrow>
      local_address option definition_site \<Rightarrow> finite_exact_artifact \<Rightarrow>
      (local_address,local_address,local_address,finite_factor_term) inference_proof option" where
  "development_policy_certificate K pu d R=(let t=Finite_Target (Finite_Whole R) in
     case finite_source_computation K pu [] (\<lambda>Q. finite_program_proofs Q (finite_program_term_demand Q {|t|})) of
       None \<Rightarrow> None
     | Some (P,A,T) \<Rightarrow> map_option snd (finite_singleton_option (ffilter (\<lambda>((e,v),p). e=d \<and> v=t) T)))"

type_synonym development_policy_judgment = "local_address option definition_site\<times>
  local_address option finite_artifact_environment\<times>local_address option\<times>
  local_address option finite_artifact_environment\<times>local_address option\<times>local_address option definition_site\<times>
  local_address option finite_artifact_environment\<times>finite_exact_artifact"

definition development_policy_judgment ::
    "finite_factor_term list \<Rightarrow> finite_exact_artifact \<Rightarrow> development_policy_judgment option" where
  "development_policy_judgment xs R=(case development_policy_source_with xs of
     None \<Rightarrow> None
   | Some (d,K,pu) \<Rightarrow> Option.bind (development_policy_certificate K pu d R) (\<lambda>p.
       case finite_native_certificate_replay K pu [] p d (Finite_Target (Finite_Whole R)) of
         None \<Rightarrow> None
       | Some (A,M,root,G,au,I,W,B) \<Rightarrow> (case finite_native_judgment_quote B pu [] au [] of
           None \<Rightarrow> None
         | Some (J,C) \<Rightarrow> if replay_policy_condition K pu [] d R J pu [] au []
             then Some (d,K,pu,B,au,root,J,C) else None)))"

section \<open>Recording a judgment as a generation\<close>

text \<open>
  A generation is recorded in an environment of generations beside the predecessors it cites: its
  payload is the judged artifact and its cause is the quotation of the judgment's replayed scope.
  Recording a judgment and then recording the generation is the existing certificate-to-policy
  composition (\<open>certificate_policy_record\<close>), whose check of the policy consumes the known-scope
  contract of the replay instead of reading the recorded cause back
  (\<open>development_certified_generation_route\<close>); every contract of that composition therefore holds
  of the recorded generation.
\<close>

definition development_recorded_generation ::
    "development_policy_judgment \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow> finite_exact_target \<Rightarrow>
      ((local_address option\<times>local_address)\<times>finite_generation) list \<Rightarrow> finite_exact_artifact \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_recorded_generation j H l rows R=(case j of (d,K,pu,B,au,root,J,C) \<Rightarrow>
     finite_construct_generation_record H l (Finite_Whole R) (Finite_Whole C) rows)"

definition development_certified_generation ::
    "finite_factor_term list \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow> finite_exact_target \<Rightarrow>
      ((local_address option\<times>local_address)\<times>finite_generation) list \<Rightarrow> finite_exact_artifact \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_certified_generation xs H l rows R=Option.bind (development_policy_judgment xs R)
     (\<lambda>j. development_recorded_generation j H l rows R)"

theorem development_certified_generation_route:
  "development_certified_generation xs H l rows R=(case development_policy_source_with xs of
     None \<Rightarrow> None
   | Some (d,K,pu) \<Rightarrow> Option.bind (development_policy_certificate K pu d R)
       (\<lambda>p. map_option snd (certificate_policy_record K pu d p R H l rows)))"
proof (cases "development_policy_source_with xs")
  case None
  then show ?thesis by (simp add: development_certified_generation_def development_policy_judgment_def)
next
  case (Some policy)
  note policy_found=this
  obtain d K pu where policy: "policy=(d,K,pu)" by (cases policy) auto
  show ?thesis
  proof (cases "development_policy_certificate K pu d R")
    case None
    then show ?thesis
      by (simp add: development_certified_generation_def development_policy_judgment_def policy_found policy)
  next
    case (Some p)
    note certificate=this
    show ?thesis
    proof (cases "finite_native_certificate_replay K pu [] p d (Finite_Target (Finite_Whole R))")
      case None
      then show ?thesis
        by (simp add: development_certified_generation_def development_policy_judgment_def policy_found policy
          certificate certificate_policy_record_def)
    next
      case (Some replay)
      note replayed=this
      obtain A M root G au I W B where shape: "replay=(A,M,root,G,au,I,W,B)" by (cases replay) auto
      have ready: "finite_literal_replay_ready B pu [] au [] root R"
        by (rule certificate_replay_literal_ready[OF replayed[unfolded shape]])
      show ?thesis
      proof (cases "finite_native_judgment_quote B pu [] au []")
        case None
        then show ?thesis
          by (simp add: development_certified_generation_def development_policy_judgment_def policy_found policy
            certificate replayed shape certificate_policy_record_def policy_record_replay_from_source_factored
            ready quoted_policy_attempt_def)
      next
        case (Some quoted)
        note quotation=this
        obtain J C where pair: "quoted=(J,C)" by (cases quoted) auto
        show ?thesis
          by (simp add: development_certified_generation_def development_policy_judgment_def policy_found policy
            certificate replayed shape certificate_policy_record_def policy_record_replay_from_source_factored
            ready quoted_policy_attempt_def quotation pair development_recorded_generation_def
            option.map_comp comp_def option.map_ident split: option.splits)
      qed
    qed
  qed
qed

theorem development_certified_generation_certified:
  assumes built: "development_certified_generation xs H l rows R=Some (B,u,G)"
  obtains d K pu E root where "development_policy_source_with xs=Some (d,K,pu)"
    "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    "generation_locus G=l" "generation_predecessors G=fset_of_list (map snd rows)"
    "generation_payload G=Finite_Whole R"
    "finite_check_generation G B u []"
    "environment_included (decode_finite_environment H) (decode_finite_environment B)"
    "u\<notin>fset (finite_environment_uses H)"
proof -
  have routed: "(case development_policy_source_with xs of
     None \<Rightarrow> None
   | Some (d,K,pu) \<Rightarrow> Option.bind (development_policy_certificate K pu d R)
       (\<lambda>p. map_option snd (certificate_policy_record K pu d p R H l rows)))=Some (B,u,G)"
    using built by (simp only: development_certified_generation_route)
  obtain d K pu where policy: "development_policy_source_with xs=Some (d,K,pu)"
    using routed by (auto split: option.splits)
  have "\<exists>p replay. certificate_policy_record K pu d p R H l rows=Some (replay,(B,u,G))"
    using routed policy by (fastforce simp: bind_eq_Some_conv)
  then obtain p replay where recording: "certificate_policy_record K pu d p R H l rows=Some (replay,(B,u,G))"
    by blast
  obtain A M root G' au I W E where shape: "replay=(A,M,root,G',au,I,W,E)" by (cases replay) auto
  have result: "certificate_policy_record K pu d p R H l rows=Some ((A,M,root,G',au,I,W,E),(B,u,G))"
    using recording shape by simp
  have cause: "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    by (rule certificate_policy_record_original_cause[OF result])
  have composed: "policy_record_replay_with id finite_construct_generation_record K pu d H l rows E pu [] au [] root R=
      Some (B,u,G)"
    using result by (simp only: certificate_policy_record_fields; blast)
  obtain J C where replayed: "record_native_replay_with finite_construct_generation_record H l rows E pu [] au [] root R=
      Some (B,u,G,J,C)"
    using composed by (simp only: policy_record_replay_with_result; blast)
  have generated: "finite_construct_generation_record H l (Finite_Whole R) (Finite_Whole C) rows=Some (B,u,G)"
    using replayed by (simp only: record_native_replay_with_result; blast)
  note constructed=finite_construct_generation_record_correct[OF generated]
  show thesis
  proof (rule that[OF policy cause])
    show "generation_locus G=l" "generation_predecessors G=fset_of_list (map snd rows)"
      "generation_payload G=Finite_Whole R"
      using constructed(2) by (simp_all add: finite_generation_record_core_def)
    show "finite_check_generation G B u []" by (rule constructed(6))
    show "environment_included (decode_finite_environment H) (decode_finite_environment B)" by (rule constructed(4))
    show "u\<notin>fset (finite_environment_uses H)" by (rule constructed(7))
  qed
qed

text \<open>
  What the certified cause establishes is the policy's contract: the policy's entry holds of the
  payload, so the payload is one of the listed presentations. Nothing else can be recorded under it.
\<close>

theorem development_certified_generation_listed:
  assumes built: "development_certified_generation xs H l rows R=Some (B,u,G)"
  shows "Finite_Target (Finite_Whole R)\<in>set xs"
proof -
  obtain d K pu E root where policy: "development_policy_source_with xs=Some (d,K,pu)"
    and cause: "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    by (rule development_certified_generation_certified[OF built]) blast
  obtain T where package: "native_package_at (decode_finite_environment K) pu [] T"
    by (rule development_policy_with_package[OF policy])
  have call: "(d,Target_Term (Whole_Artifact (decode_finite_object R)))\<in>positive_meaning T"
    by (rule certified_policy_cause_sound[OF package cause])
  have "Target_Term (Whole_Artifact (decode_finite_object R))\<in>decode_finite_term ` set xs"
    using call by (simp only: development_policy_with_exact[OF policy package])
  then obtain x where member: "x\<in>set xs"
    and same: "Target_Term (Whole_Artifact (decode_finite_object R))=decode_finite_term x" by blast
  have "decode_finite_term x=decode_finite_term (Finite_Target (Finite_Whole R))" using same by simp
  then have "x=Finite_Target (Finite_Whole R)" by (simp only: decode_finite_term_injective)
  then show ?thesis using member by simp
qed

section \<open>A family is admitted under the policy of its acceptance\<close>

text \<open>
  The policy of a family lists exactly the family's complete data quotation, presented with the names
  it uses, and it is constructed only when every entity of the family is an entity of the checked
  context: the rule the policy states is Isabelle's acceptance of the checked context, instantiated at
  the one family a generation records. The recorded cause carries the policy, which lists the family,
  but not the checked context; that the family is accepted is this constructor's contract, and a
  reader of the generation alone does not see it. Listing the one family bounds the policy, and so
  every cause, by the family recorded; a policy listing every family of a state would make each cause
  quote all of them.

  The family's presentation with its names is the key of its judgment: the judgment is a function
  of that presentation, so a judgment is made once for each presented family however many generations
  record it.
\<close>

definition development_family_key :: "isabelle_context \<Rightarrow> isabelle_entity list \<Rightarrow> finite_factor_term option" where
  "development_family_key C es=(if set es\<subseteq>set (snd C)
     then Some (isabelle_context_data (isabelle_local_entities (fst C) es)) else None)"

definition development_payload_judgment ::
    "finite_factor_term \<Rightarrow> (finite_exact_artifact\<times>development_policy_judgment) option" where
  "development_payload_judgment t=(case finite_data_syntax (decode_finite_term t) of
     None \<Rightarrow> None
   | Some R \<Rightarrow> map_option (Pair R) (development_policy_judgment [Finite_Target (Finite_Whole R)] R))"

definition development_judged_generation ::
    "(finite_exact_artifact\<times>development_policy_judgment) \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow>
      finite_exact_target \<Rightarrow> ((local_address option\<times>local_address)\<times>finite_generation) list \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_judged_generation judged H l rows=(case judged of (R,j) \<Rightarrow> development_recorded_generation j H l rows R)"

lemma development_payload_judgment_certified:
  assumes "finite_data_syntax (decode_finite_term t)=Some R"
  shows "Option.bind (development_payload_judgment t) (\<lambda>judged. development_judged_generation judged H l rows)=
    development_certified_generation [Finite_Target (Finite_Whole R)] H l rows R"
  using assms by (cases "development_policy_judgment [Finite_Target (Finite_Whole R)] R")
    (simp_all add: development_payload_judgment_def development_judged_generation_def
      development_certified_generation_def)

definition development_family_generation ::
    "isabelle_context \<Rightarrow> isabelle_entity list \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow>
      finite_exact_target \<Rightarrow> ((local_address option\<times>local_address)\<times>finite_generation) list \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_family_generation C es H l rows=Option.bind (development_family_key C es)
     (\<lambda>t. Option.bind (development_payload_judgment t) (\<lambda>judged. development_judged_generation judged H l rows))"

theorem development_family_generation_certified:
  assumes built: "development_family_generation C es H l rows=Some (B,u,G)"
  obtains R d K pu E root where "set es\<subseteq>set (snd C)"
    "development_data_target (isabelle_context_data (isabelle_local_entities (fst C) es))=Some (generation_payload G)"
    "generation_payload G=Finite_Whole R"
    "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    "generation_locus G=l" "generation_predecessors G=fset_of_list (map snd rows)"
    "finite_check_generation G B u []"
    "environment_included (decode_finite_environment H) (decode_finite_environment B)"
proof -
  have accepted: "set es\<subseteq>set (snd C)"
    using built by (simp add: development_family_generation_def development_family_key_def split: if_splits)
  let ?t="isabelle_context_data (isabelle_local_entities (fst C) es)"
  have judged: "Option.bind (development_payload_judgment ?t)
      (\<lambda>judged. development_judged_generation judged H l rows)=Some (B,u,G)"
    using built accepted by (simp add: development_family_generation_def development_family_key_def)
  obtain R where quoted: "finite_data_syntax (decode_finite_term ?t)=Some R"
    using judged by (cases "finite_data_syntax (decode_finite_term ?t)") (simp_all add: development_payload_judgment_def)
  have certified: "development_certified_generation [Finite_Target (Finite_Whole R)] H l rows R=Some (B,u,G)"
    using judged by (simp only: development_payload_judgment_certified[OF quoted])
  obtain d K pu E root where policy: "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    and cause: "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    and fields: "generation_locus G=l" "generation_predecessors G=fset_of_list (map snd rows)"
      "generation_payload G=Finite_Whole R" "finite_check_generation G B u []"
      "environment_included (decode_finite_environment H) (decode_finite_environment B)"
    by (rule development_certified_generation_certified[OF certified]) blast
  have target: "development_data_target ?t=Some (generation_payload G)"
    using quoted fields(3) by (simp add: development_data_target_def)
  show thesis by (rule that[OF accepted target fields(3) policy cause fields(1,2,4,5)])
qed

section \<open>Incumbents and answers are admitted as certified generations\<close>

text \<open>
  The incumbent of a problem is its base generation: the family of code equations of the problem's
  subject, recorded at the problem's locus with no predecessor. Having no predecessor, it is recorded
  in an environment of its own, so the incumbents of independent problems are recorded independently.
  An admitted answer is recorded in the environment of the incumbent it was judged against and cites
  the incumbents at its problem's locus. Its family is the subject's equations in the answer state; it
  is recorded only when the verdict accepted it, which is the condition of the answer's generation in
  the history, and its cause certifies the family's acceptance by the answer's checked context. A
  generation read in another environment is the same core, so the environment it is recorded in
  bounds only what recording it costs.

  Each is stated through the judgment of its family's key, which a use supplies: the certified
  incumbent and answer judge with \<open>development_payload_judgment\<close> itself, and any function equal to it
  judges the same.
\<close>

type_synonym development_generation_row = "(local_address option\<times>local_address)\<times>finite_generation"

type_synonym development_payload_judge = "finite_factor_term \<Rightarrow> (finite_exact_artifact\<times>development_policy_judgment) option"

definition development_incumbent_key ::
    "isabelle_rooted_context \<Rightarrow> development_problem \<Rightarrow> (finite_exact_target\<times>finite_factor_term) option" where
  "development_incumbent_key S p=Option.bind (development_data_target (development_problem_locus (fst (snd S)) p))
     (\<lambda>l. map_option (Pair l) (development_family_key (snd S) (development_answer_equations (snd S) (problem_subject p))))"

definition development_incumbent_with ::
    "development_payload_judge \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_problem \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_incumbent_with judge S p=Option.bind (development_incumbent_key S p)
     (\<lambda>(l,t). Option.bind (judge t) (\<lambda>judged. development_judged_generation judged (finite_enumerated_environment [] []) l []))"

definition development_certified_incumbent ::
    "isabelle_rooted_context \<Rightarrow> development_problem \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_certified_incumbent=development_incumbent_with development_payload_judgment"

lemma development_certified_incumbent_family:
  "development_certified_incumbent S p=Option.bind (development_data_target (development_problem_locus (fst (snd S)) p))
     (\<lambda>l. development_family_generation (snd S) (development_answer_equations (snd S) (problem_subject p))
        (finite_enumerated_environment [] []) l [])"
  by (cases "development_data_target (development_problem_locus (fst (snd S)) p)")
    (simp_all add: development_certified_incumbent_def development_incumbent_with_def development_incumbent_key_def
      development_family_generation_def bind_eq_Some_conv Option.bind_map_option comp_def)

theorem development_certified_incumbent_base:
  assumes built: "development_certified_incumbent S p=Some (B,u,G)"
  obtains l where "development_data_target (development_problem_locus (fst (snd S)) p)=Some l"
    "development_family_generation (snd S) (development_answer_equations (snd S) (problem_subject p))
      (finite_enumerated_environment [] []) l []=Some (B,u,G)"
    "generation_locus G=l" "generation_predecessors G={||}"
proof -
  obtain l where locus: "development_data_target (development_problem_locus (fst (snd S)) p)=Some l"
    and family: "development_family_generation (snd S) (development_answer_equations (snd S) (problem_subject p))
      (finite_enumerated_environment [] []) l []=Some (B,u,G)"
    using built by (auto simp: development_certified_incumbent_family bind_eq_Some_conv)
  have fields: "generation_locus G=l" "generation_predecessors G={||}"
    by (rule development_family_generation_certified[OF family], simp)+
  show thesis by (rule that[OF locus family fields])
qed

definition development_answer_key ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow>
      (finite_exact_target\<times>finite_factor_term) option" where
  "development_answer_key S r S'=(case development_answer_generation S r S' of
     None \<Rightarrow> None
   | Some (p,E,payload,v) \<Rightarrow> Option.bind (development_data_target (development_problem_locus (fst (snd S)) p))
       (\<lambda>l. map_option (Pair l) (development_family_key (snd S') payload)))"

definition development_answer_with ::
    "development_payload_judge \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow>
      local_address option finite_artifact_environment \<Rightarrow> development_generation_row list \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_answer_with judge S r S' H rows=Option.bind (development_answer_key S r S')
     (\<lambda>(l,t). Option.bind (judge t) (\<lambda>judged. development_judged_generation judged H l
        (filter (\<lambda>(d,G). generation_locus G=l) rows)))"

definition development_certified_answer ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow>
      local_address option finite_artifact_environment \<Rightarrow> development_generation_row list \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_certified_answer=development_answer_with development_payload_judgment"

lemma development_certified_answer_family:
  "development_certified_answer S r S' H rows=(case development_answer_generation S r S' of
     None \<Rightarrow> None
   | Some (p,E,payload,v) \<Rightarrow> Option.bind (development_data_target (development_problem_locus (fst (snd S)) p))
       (\<lambda>l. development_family_generation (snd S') payload H l (filter (\<lambda>(d,G). generation_locus G=l) rows)))"
proof (cases "development_answer_generation S r S'")
  case None
  then show ?thesis by (simp add: development_certified_answer_def development_answer_with_def development_answer_key_def)
next
  case (Some generation)
  obtain p E payload v where shape: "generation=(p,E,payload,v)" by (cases generation) auto
  show ?thesis
    by (cases "development_data_target (development_problem_locus (fst (snd S)) p)")
      (simp_all add: Some shape development_certified_answer_def development_answer_with_def development_answer_key_def
        development_family_generation_def Option.bind_map_option comp_def)
qed

theorem development_certified_answer_accepted:
  assumes built: "development_certified_answer S r S' H rows=Some (B,u,G)"
  obtains p E payload v l where "development_answer_generation S r S'=Some (p,E,payload,v)"
    "development_refinement_accepted v" "p=fst r"
    "development_data_target (development_problem_locus (fst (snd S)) p)=Some l"
    "development_family_generation (snd S') payload H l (filter (\<lambda>(d,G). generation_locus G=l) rows)=Some (B,u,G)"
proof -
  obtain p E payload v where generation: "development_answer_generation S r S'=Some (p,E,payload,v)"
    using built by (auto simp: development_certified_answer_family split: option.splits)
  obtain l where locus: "development_data_target (development_problem_locus (fst (snd S)) p)=Some l"
    and family: "development_family_generation (snd S') payload H l (filter (\<lambda>(d,G). generation_locus G=l) rows)=Some (B,u,G)"
    using built generation by (auto simp: development_certified_answer_family bind_eq_Some_conv)
  have accepted: "development_refinement_accepted v"
    by (rule development_answer_generation_payload(1)[OF generation])
  have problem: "p=fst r"
    using generation by (auto simp: development_answer_generation_def Let_def split: prod.splits if_splits)
  show thesis by (rule that[OF generation accepted problem locus family])
qed

end
