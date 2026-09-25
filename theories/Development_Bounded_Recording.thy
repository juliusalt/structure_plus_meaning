theory Development_Bounded_Recording
  imports Development_Certified_Generations Factor_Bounded_Generation_Scopes
begin

section \<open>The finite fill\<close>

text \<open>
  The finite fill replaces the artifact at every use of a finite set of uses by one artifact and keeps
  every binding; it decodes exactly to the fill of @{text Factor_Bounded_Generation_Scopes}.
\<close>

definition finite_payload_fill ::
    "'u finite_artifact_environment \<Rightarrow> 'u fset \<Rightarrow> finite_exact_artifact \<Rightarrow> 'u finite_artifact_environment" where
  "finite_payload_fill F0 V R=
    \<lparr>finite_environment_artifacts=(\<lambda>(u,S). (u,if u |\<in>| V then R else S)) |`| finite_environment_artifacts F0,
     finite_environment_bindings=finite_environment_bindings F0\<rparr>"

theorem decode_finite_payload_fill:
  "decode_finite_environment (finite_payload_fill F0 V R)=
    payload_fill (decode_finite_environment F0) (fset V) (decode_finite_object R)"
  by (simp add: decode_finite_environment_def finite_payload_fill_def payload_fill_def map_relation_values_def
    fimage.rep_eq image_image split_def if_distrib[of decode_finite_object] cong: if_cong)

lemma payload_fill_twice:
  "payload_fill (payload_fill F V X) V Y=payload_fill F V Y"
  by (simp add: payload_fill_def image_image split_def cong: if_cong)

lemma payload_fill_same:
  assumes same: "\<And>u S. u\<in>V \<Longrightarrow> artifact_at F u S \<Longrightarrow> S=R"
  shows "payload_fill F V R=F"
proof -
  have each: "(\<lambda>(u,S). (u,if u\<in>V then R else S)) x=x" if member: "x\<in>environment_artifacts F" for x
  proof -
    obtain u S where x: "x=(u,S)" by (cases x)
    have "u\<in>V \<Longrightarrow> S=R" using same member unfolding x artifact_at_def by blast
    then show ?thesis unfolding x by simp
  qed
  have "(\<lambda>(u,S). (u,if u\<in>V then R else S)) ` environment_artifacts F=id ` environment_artifacts F"
    by (rule image_cong) (simp_all add: each)
  then show ?thesis by (cases F) (simp add: payload_fill_def)
qed

text \<open>
  The uses of an environment holding an artifact, compared by value as artifact identity decides.
\<close>

definition finite_payload_uses :: "'u finite_artifact_environment \<Rightarrow> finite_exact_artifact \<Rightarrow> 'u fset" where
  "finite_payload_uses J R=fst |`| ffilter (\<lambda>z. snd z=R) (finite_environment_artifacts J)"

lemma finite_payload_uses_member:
  "u |\<in>| finite_payload_uses J R \<longleftrightarrow> (u,R) |\<in>| finite_environment_artifacts J"
  by (force simp: finite_payload_uses_def fimage_iff ffmember_filter)

section \<open>The bounded quotation\<close>

text \<open>
  The bounded quotation computes the least judgment environment J of a replay as
  @{const finite_native_judgment_quote} does, without that quotation's data syntax; V is the uses of J
  holding the payload, F0 is J with the empty artifact at V, and the cause is the complete data syntax of
  the bounded value, the judgment value of F0 at its two sites beside the data list of V. There is no
  quotation unless F0 is formed and holds both sites, which the grammar gives: the payload is complete
  data syntax, cited only as a whole target, so no binding of J has its source at a use holding it.
\<close>

definition finite_bounded_scope_term ::
    "local_address option finite_artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
      local_address option \<Rightarrow> local_address \<Rightarrow> local_address option fset \<Rightarrow> factor_term" where
  "finite_bounded_scope_term F0 pu pr au ar V=Pair_Term (finite_judgment_term F0 pu pr au ar)
     (data_list_term (map use_data_term (sorted_list_of_fset V)))"

lemma finite_bounded_scope_term_presents:
  assumes formed: "finite_environment_formed F0"
    and positions: "(pu,pr) |\<in>| finite_environment_positions F0" "(au,ar) |\<in>| finite_environment_positions F0"
  shows "bounded_scope_value_presents (decode_finite_environment F0) pu pr au ar (fset V)
    (finite_bounded_scope_term F0 pu pr au ar V)"
proof -
  have valued: "judgment_value_presents (decode_finite_environment F0) pu pr au ar
      (finite_judgment_term F0 pu pr au ar)"
    using formed positions by (simp add: finite_judgment_term_exact)
  have uses: "data_collection_presents (\<lambda>u v. v=use_data_term u) (fset V)
      (data_list_term (map use_data_term (sorted_list_of_fset V)))"
    unfolding data_collection_presents_def
    by (rule exI[of _ "sorted_list_of_fset V"], rule exI[of _ "map use_data_term (sorted_list_of_fset V)"])
      (simp add: list_all2_function)
  show ?thesis unfolding bounded_scope_value_presents_def finite_bounded_scope_term_def
    using valued uses by blast
qed

definition finite_bounded_judgment_quote ::
    "local_address option finite_artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
      local_address option \<Rightarrow> local_address \<Rightarrow> finite_exact_artifact \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option finite_artifact_environment\<times>
        local_address option fset\<times>finite_exact_artifact) option" where
  "finite_bounded_judgment_quote E pu pr au ar R=(if finite_native_judgment_ready E pu pr au ar then
     let J=finite_native_judgment_environment E pu pr au ar; V=finite_payload_uses J R;
       F0=finite_payload_fill J V finite_empty_artifact in
     if finite_environment_formed F0 \<and> (pu,pr) |\<in>| finite_environment_positions F0 \<and>
       (au,ar) |\<in>| finite_environment_positions F0
     then map_option (\<lambda>C. (J,F0,V,C)) (finite_data_syntax (finite_bounded_scope_term F0 pu pr au ar V))
     else None
   else None)"

lemma finite_bounded_judgment_quote_result:
  "finite_bounded_judgment_quote E pu pr au ar R=Some (J,F0,V,C) \<longleftrightarrow>
    finite_native_judgment_ready E pu pr au ar \<and> J=finite_native_judgment_environment E pu pr au ar \<and>
    V=finite_payload_uses J R \<and> F0=finite_payload_fill J V finite_empty_artifact \<and>
    finite_environment_formed F0 \<and> (pu,pr) |\<in>| finite_environment_positions F0 \<and>
    (au,ar) |\<in>| finite_environment_positions F0 \<and>
    finite_data_syntax (finite_bounded_scope_term F0 pu pr au ar V)=Some C"
  by (auto simp: finite_bounded_judgment_quote_def Let_def split: if_splits)

theorem finite_bounded_judgment_quote_correct:
  assumes result: "finite_bounded_judgment_quote E pu pr au ar R=Some (J,F0,V,C)"
  shows "bounded_scope_quoted_at (decode_finite_object C) [] (decode_finite_environment F0) pu pr au ar (fset V)"
    "\<forall>u\<in>fset V. artifact_at (decode_finite_environment F0) u empty_artifact"
    "payload_fill (decode_finite_environment F0) (fset V) (decode_finite_object R)=decode_finite_environment J"
    "decode_finite_environment J=native_judgment_environment (decode_finite_environment E) pu pr au ar"
    "decode_finite_environment J=native_judgment_environment (decode_finite_environment J) pu pr au ar"
    "environment_included (decode_finite_environment J) (decode_finite_environment E)"
    "native_package_environment (decode_finite_environment J) pu pr=
      native_package_environment (decode_finite_environment E) pu pr"
    "finite_exact_formed C"
proof -
  have ready: "finite_native_judgment_ready E pu pr au ar"
    and scoped: "J=finite_native_judgment_environment E pu pr au ar"
    and uses: "V=finite_payload_uses J R"
    and placed: "F0=finite_payload_fill J V finite_empty_artifact"
    and formed0: "finite_environment_formed F0"
    and positions: "(pu,pr) |\<in>| finite_environment_positions F0" "(au,ar) |\<in>| finite_environment_positions F0"
    and built: "finite_data_syntax (finite_bounded_scope_term F0 pu pr au ar V)=Some C"
    using result by (simp only: finite_bounded_judgment_quote_result; blast)+
  obtain P d t I K where package: "native_package_at (decode_finite_environment E) pu pr P"
    and app: "native_application_at (decode_finite_environment E) au ar d t I K"
    using ready by (simp only: finite_native_judgment_ready_correct; blast)
  have actual: "decode_finite_environment J=native_judgment_environment (decode_finite_environment E) pu pr au ar"
    by (simp only: scoped finite_native_judgment_environment_correct)
  have formed: "environment_formed (decode_finite_environment J)"
    using native_judgment_environment_recovers(3)[OF package app] by (simp only: actual)
  have held: "artifact_at (decode_finite_environment J) u (decode_finite_object R)" if member: "u\<in>fset V" for u
  proof -
    have "(u,R) |\<in>| finite_environment_artifacts J" using member by (simp only: uses finite_payload_uses_member)
    then show ?thesis by (auto simp: artifact_at_def decode_finite_environment_def)
  qed
  have decoded0: "decode_finite_environment F0=payload_fill (decode_finite_environment J) (fset V) empty_artifact"
    by (simp only: placed decode_finite_payload_fill decode_finite_empty_artifact)
  show "\<forall>u\<in>fset V. artifact_at (decode_finite_environment F0) u empty_artifact"
  proof
    fix u assume member: "u\<in>fset V"
    show "artifact_at (decode_finite_environment F0) u empty_artifact"
      using held[OF member] member by (simp add: decoded0 artifact_at_payload_fill; blast)
  qed
  have same: "S=decode_finite_object R" if "u\<in>fset V" "artifact_at (decode_finite_environment J) u S" for u S
    using environment_artifact_unique[OF formed that(2) held[OF that(1)]] .
  show "payload_fill (decode_finite_environment F0) (fset V) (decode_finite_object R)=decode_finite_environment J"
    by (simp only: decoded0 payload_fill_twice) (rule payload_fill_same[OF same])
  have presented: "bounded_scope_value_presents (decode_finite_environment F0) pu pr au ar (fset V)
      (finite_bounded_scope_term F0 pu pr au ar V)"
    by (rule finite_bounded_scope_term_presents[OF formed0 positions])
  have term_formed: "term_formed (finite_bounded_scope_term F0 pu pr au ar V)"
    using bounded_scope_value_presents_formed[OF presented] by blast
  have quote: "complete_data_quoted_at (decode_finite_object C) [] (finite_bounded_scope_term F0 pu pr au ar V)"
    by (rule finite_data_syntax_complete_quotation[OF term_formed built])
  show "bounded_scope_quoted_at (decode_finite_object C) [] (decode_finite_environment F0) pu pr au ar (fset V)"
    unfolding bounded_scope_quoted_at_def using presented quote by blast
  show "finite_exact_formed C"
    using complete_data_quotation_formed[OF quote] by (simp only: finite_exact_formed_correct; blast)
  show "decode_finite_environment J=native_judgment_environment (decode_finite_environment E) pu pr au ar"
    by (rule actual)
  show "decode_finite_environment J=native_judgment_environment (decode_finite_environment J) pu pr au ar"
    using native_judgment_environment_idempotent[OF package app] by (simp only: actual)
  show "environment_included (decode_finite_environment J) (decode_finite_environment E)"
    by (simp only: actual; rule native_judgment_environment_included)
  show "native_package_environment (decode_finite_environment J) pu pr=
    native_package_environment (decode_finite_environment E) pu pr"
    by (simp only: actual; rule native_judgment_program_environment[OF package app])
qed

section \<open>The bounded judgment\<close>

text \<open>
  The bounded judgment keeps the calls of @{const development_policy_judgment}: the listing policy, its
  certificate, its replay and the condition at the least judgment environment, unchanged; only the cause
  is the bounded quotation.
\<close>

definition development_bounded_policy_judgment ::
    "finite_factor_term list \<Rightarrow> finite_exact_artifact \<Rightarrow> development_policy_judgment option" where
  "development_bounded_policy_judgment xs R=(case development_policy_source_with xs of
     None \<Rightarrow> None
   | Some (d,K,pu) \<Rightarrow> Option.bind (development_policy_certificate K pu d R) (\<lambda>p.
       case finite_native_certificate_replay K pu [] p d (Finite_Target (Finite_Whole R)) of
         None \<Rightarrow> None
       | Some (A,M,root,G,au,I,W,B) \<Rightarrow> (case finite_bounded_judgment_quote B pu [] au [] R of
           None \<Rightarrow> None
         | Some (J,F0,V,C) \<Rightarrow> if replay_policy_condition K pu [] d R J pu [] au []
             then Some (d,K,pu,B,au,root,J,C) else None)))"

lemma development_bounded_policy_judgment_result:
  assumes judged: "development_bounded_policy_judgment xs R=Some (d,K,pu,B,au,root,J,C)"
  obtains p A M G I W F0 V where "development_policy_source_with xs=Some (d,K,pu)"
    "development_policy_certificate K pu d R=Some p"
    "finite_native_certificate_replay K pu [] p d (Finite_Target (Finite_Whole R))=Some (A,M,root,G,au,I,W,B)"
    "finite_bounded_judgment_quote B pu [] au [] R=Some (J,F0,V,C)"
    "replay_policy_condition K pu [] d R J pu [] au []"
proof -
  obtain policy where found: "development_policy_source_with xs=Some policy"
    using judged by (cases "development_policy_source_with xs") (auto simp: development_bounded_policy_judgment_def)
  obtain d' K' pu' where shape0: "policy=(d',K',pu')" by (cases policy) auto
  obtain p where certificate: "development_policy_certificate K' pu' d' R=Some p"
    using judged by (cases "development_policy_certificate K' pu' d' R")
      (auto simp: development_bounded_policy_judgment_def found shape0)
  obtain replay where replayed: "finite_native_certificate_replay K' pu' [] p d' (Finite_Target (Finite_Whole R))=
      Some replay"
    using judged by (cases "finite_native_certificate_replay K' pu' [] p d' (Finite_Target (Finite_Whole R))")
      (auto simp: development_bounded_policy_judgment_def found shape0 certificate)
  obtain A M root' G au' I W B' where shape1: "replay=(A,M,root',G,au',I,W,B')" by (cases replay) auto
  obtain quoted where bounded: "finite_bounded_judgment_quote B' pu' [] au' [] R=Some quoted"
    using judged by (cases "finite_bounded_judgment_quote B' pu' [] au' [] R")
      (auto simp: development_bounded_policy_judgment_def found shape0 certificate replayed shape1)
  obtain J' F0 V C' where shape2: "quoted=(J',F0,V,C')" by (cases quoted) auto
  have decided: "(if replay_policy_condition K' pu' [] d' R J' pu' [] au' [] then Some (d',K',pu',B',au',root',J',C')
      else None)=Some (d,K,pu,B,au,root,J,C)"
    using judged by (simp add: development_bounded_policy_judgment_def found shape0 certificate replayed shape1
      bounded shape2)
  have condition: "replay_policy_condition K' pu' [] d' R J' pu' [] au' []"
    and same: "d'=d" "K'=K" "pu'=pu" "B'=B" "au'=au" "root'=root" "J'=J" "C'=C"
    using decided by (simp_all split: if_splits)
  show thesis by (rule that[of p A M G I W F0 V])
    (use found shape0 certificate replayed shape1 bounded shape2 condition same in simp_all)
qed

text \<open>
  The bounded judgment judges where the original does, at the same least judgment environment: the
  original quotation of that environment always exists, the judgment term being self-contained.
\<close>

theorem development_bounded_policy_judgment_original:
  assumes judged: "development_bounded_policy_judgment xs R=Some (d,K,pu,B,au,root,J,C)"
  shows "\<exists>C'. development_policy_judgment xs R=Some (d,K,pu,B,au,root,J,C')"
proof -
  obtain p A M G I W F0 V where policy: "development_policy_source_with xs=Some (d,K,pu)"
    and certificate: "development_policy_certificate K pu d R=Some p"
    and replayed: "finite_native_certificate_replay K pu [] p d (Finite_Target (Finite_Whole R))=
      Some (A,M,root,G,au,I,W,B)"
    and bounded: "finite_bounded_judgment_quote B pu [] au [] R=Some (J,F0,V,C)"
    and condition: "replay_policy_condition K pu [] d R J pu [] au []"
    by (rule development_bounded_policy_judgment_result[OF judged])
  have ready: "finite_native_judgment_ready B pu [] au []"
    and scoped: "J=finite_native_judgment_environment B pu [] au []"
    using bounded by (simp_all only: finite_bounded_judgment_quote_result)
  obtain C' where built_syntax: "finite_data_syntax (finite_judgment_term J pu [] au [])=Some C'"
    using finite_data_syntax_domain[of "finite_judgment_term J pu [] au []"] by fastforce
  have quoted: "finite_native_judgment_quote B pu [] au []=Some (J,C')"
    using ready scoped built_syntax by (simp only: finite_native_judgment_quote_result; blast)
  show ?thesis using condition
    by (simp add: development_policy_judgment_def policy certificate replayed quoted)
qed

section \<open>The bounded recording\<close>

text \<open>
  The payload is made once, the complete data syntax of the decoded term, and is the locus and the
  payload alike; the judgment is the bounded one, and the generation is recorded by the constructor that
  does not check the cause's formation, which the bounded quotation's contract establishes.
\<close>

definition development_bounded_generation ::
    "finite_factor_term \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow> development_generation_row list \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_bounded_generation t H rows=(case finite_data_syntax (decode_finite_term t) of
     None \<Rightarrow> None
   | Some R \<Rightarrow> Option.bind (development_bounded_policy_judgment [Finite_Target (Finite_Whole R)] R)
       (\<lambda>(d,K,pu,B,au,root,J,C). finite_construct_formed_cause_generation H (Finite_Whole R) (Finite_Whole R)
          (Finite_Whole C) rows))"

lemma development_bounded_generation_result:
  assumes built: "development_bounded_generation t H rows=Some (B,u,G)"
  obtains R d K pu B0 au root J C where "finite_data_syntax (decode_finite_term t)=Some R"
    "development_bounded_policy_judgment [Finite_Target (Finite_Whole R)] R=Some (d,K,pu,B0,au,root,J,C)"
    "finite_construct_formed_cause_generation H (Finite_Whole R) (Finite_Whole R) (Finite_Whole C) rows=Some (B,u,G)"
  using built by (auto simp: development_bounded_generation_def bind_eq_Some_conv split: option.splits prod.splits)

text \<open>
  Where the environment recorded in is formed and every cited row reads back at its site, the
  constructor is the library's record constructor.
\<close>

lemma development_bounded_generation_constructed:
  assumes built: "development_bounded_generation t H rows=Some (B,u,G)"
    and formed: "finite_environment_formed H"
    and rows: "list_all (\<lambda>(d,G). finite_check_generation G H (fst d) (snd d)) rows"
  obtains R d K pu B0 au root J C where "finite_data_syntax (decode_finite_term t)=Some R"
    "development_bounded_policy_judgment [Finite_Target (Finite_Whole R)] R=Some (d,K,pu,B0,au,root,J,C)"
    "finite_construct_generation_record H (Finite_Whole R) (Finite_Whole R) (Finite_Whole C) rows=Some (B,u,G)"
proof -
  obtain R d K pu B0 au root J C where quoted: "finite_data_syntax (decode_finite_term t)=Some R"
    and judged: "development_bounded_policy_judgment [Finite_Target (Finite_Whole R)] R=Some (d,K,pu,B0,au,root,J,C)"
    and generated: "finite_construct_formed_cause_generation H (Finite_Whole R) (Finite_Whole R)
      (Finite_Whole C) rows=Some (B,u,G)"
    by (rule development_bounded_generation_result[OF built])
  obtain p A M Gr I W F0 V where bounded: "finite_bounded_judgment_quote B0 pu [] au [] R=Some (J,F0,V,C)"
    by (rule development_bounded_policy_judgment_result[OF judged])
  have "finite_target_formed (Finite_Whole C)"
    using finite_bounded_judgment_quote_correct(8)[OF bounded] by simp
  then have "finite_construct_known_original_generation H (Finite_Whole R) (Finite_Whole R) (Finite_Whole C)=
      finite_construct_formed_cause_generation H (Finite_Whole R) (Finite_Whole R) (Finite_Whole C)"
    by (rule established_premise.exact[OF finite_construct_formed_cause_generation_established])
  then have known: "finite_construct_known_original_generation H (Finite_Whole R) (Finite_Whole R) (Finite_Whole C) rows=
      Some (B,u,G)"
    using generated by simp
  have "finite_construct_generation_record H (Finite_Whole R) (Finite_Whole R) (Finite_Whole C) rows=Some (B,u,G)"
    using known by (simp only: finite_construct_known_original_generation_exact[OF formed rows])
  then show thesis by (rule that[OF quoted judged])
qed

theorem development_bounded_generation_certified:
  assumes built: "development_bounded_generation t H rows=Some (B,u,G)"
    and formed: "finite_environment_formed H"
    and rows: "list_all (\<lambda>(d,G). finite_check_generation G H (fst d) (snd d)) rows"
  obtains R d K pu E root where "development_data_target t=Some (generation_payload G)"
    "generation_locus G=generation_payload G" "generation_payload G=Finite_Whole R"
    "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    "bounded_certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    "generation_predecessors G=fset_of_list (map snd rows)"
    "finite_check_generation G B u []"
    "environment_included (decode_finite_environment H) (decode_finite_environment B)"
proof -
  obtain R d K pu B0 au root J C where quoted: "finite_data_syntax (decode_finite_term t)=Some R"
    and judged: "development_bounded_policy_judgment [Finite_Target (Finite_Whole R)] R=Some (d,K,pu,B0,au,root,J,C)"
    and generated: "finite_construct_generation_record H (Finite_Whole R) (Finite_Whole R) (Finite_Whole C) rows=
      Some (B,u,G)"
    by (rule development_bounded_generation_constructed[OF built formed rows])
  obtain p A M Gr I W F0 V where policy: "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    and replayed: "finite_native_certificate_replay K pu [] p d (Finite_Target (Finite_Whole R))=
      Some (A,M,root,Gr,au,I,W,B0)"
    and bounded: "finite_bounded_judgment_quote B0 pu [] au [] R=Some (J,F0,V,C)"
    and condition: "replay_policy_condition K pu [] d R J pu [] au []"
    by (rule development_bounded_policy_judgment_result[OF judged])
  note scope=finite_bounded_judgment_quote_correct[OF bounded]
  note constructed=finite_construct_generation_record_correct[OF generated]
  have core: "G=Generation (Finite_Whole R) (fset_of_list (map snd rows)) (Finite_Whole R) (Finite_Whole C)"
    using constructed(2) by (simp only: finite_generation_record_core_def)
  have ready: "finite_literal_replay_ready B0 pu [] au [] root R"
    by (rule certificate_replay_literal_ready[OF replayed])
  have replay: "native_replay_at (decode_finite_environment B0) pu [] au [] root {}"
    using ready by (simp only: finite_literal_replay_ready_at; blast)
  obtain Pb d0 t0 I0 K0 where package0: "native_package_at (decode_finite_environment B0) pu [] Pb"
    and app0: "native_application_at (decode_finite_environment B0) au [] d0 t0 I0 K0"
    using replay unfolding native_replay_at_def by blast
  have kept: "native_package_at (decode_finite_environment J) pu [] Pb"
    using native_judgment_environment_recovers(1)[OF package0 app0] by (simp only: scope(4))
  have available: "\<exists>P. native_package_at (decode_finite_environment K) pu [] P"
    using condition unfolding replay_policy_condition_def finite_policy_package_available by blast
  have aligned: "native_package_environment (decode_finite_environment J) pu []=
      native_package_environment (decode_finite_environment K) pu []"
    "\<exists>I A. native_application_at (decode_finite_environment J) au [] d
      (Target_Term (Whole_Artifact (decode_finite_object R))) I A"
    using condition unfolding replay_policy_condition_def finite_policy_cause_alignment_exact by blast+
  obtain Ia Aa where appJ: "native_application_at (decode_finite_environment J) au [] d
      (Target_Term (Whole_Artifact (decode_finite_object R))) Ia Aa"
    using aligned(2) by blast
  have gen: "generation_at (decode_finite_environment B) u [] (decode_finite_generation G)"
    using constructed(6) by (simp only: finite_check_generation_exact)
  have payload: "generation_payload (decode_finite_generation G)=Whole_Artifact (decode_finite_object R)"
    and cause: "generation_cause (decode_finite_generation G)=Whole_Artifact (decode_finite_object C)"
    by (simp_all add: core decode_finite_generation_node)
  have bscope: "generation_bounded_scope_at (decode_finite_environment B) u [] (decode_finite_generation G)
      (decode_finite_environment J) pu [] au []"
    using generation_bounded_scope_from_core[OF gen cause scope(1) payload scope(2)] by (simp only: scope(3))
  have base: "scope_certified_base_cause_at generation_bounded_scope_at (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment B0) root (decode_finite_object R)"
    unfolding scope_certified_base_cause_at_def
    using bscope scope(5) payload kept appJ scope(6) replay by blast
  have certified: "bounded_certified_policy_cause_at (decode_finite_environment K) pu [] d
      (decode_finite_environment B) u [] (decode_finite_generation G) (decode_finite_environment B0) root
      (decode_finite_object R)"
    unfolding bounded_certified_policy_cause_at_def scope_certified_policy_cause_at_def
    using available base bscope aligned(1) appJ by blast
  have target: "development_data_target t=Some (generation_payload G)"
    using quoted by (simp add: development_data_target_def core)
  have fields: "generation_locus G=generation_payload G" "generation_payload G=Finite_Whole R"
    "generation_predecessors G=fset_of_list (map snd rows)"
    by (simp_all add: core)
  show thesis by (rule that[OF target fields(1,2) policy certified fields(3) constructed(6,4)])
qed

lemma development_bounded_generation_recorded:
  assumes built: "development_bounded_generation t H rows=Some (B,u,G)"
    and formed: "finite_environment_formed H"
    and rows: "list_all (\<lambda>(d,G). finite_check_generation G H (fst d) (snd d)) rows"
  shows "finite_environment_formed B" "finite_environment_included H B" "finite_check_generation G B u []"
    "finite_generation_formed G"
proof -
  obtain R d K pu B0 au root J C where generated: "finite_construct_generation_record H (Finite_Whole R) (Finite_Whole R)
      (Finite_Whole C) rows=Some (B,u,G)"
    by (rule development_bounded_generation_constructed[OF built formed rows])
  note correct=finite_construct_generation_record_correct[OF generated]
  show "finite_environment_formed B" by (rule correct(3))
  show "finite_environment_included H B" using correct(4) by (simp only: finite_environment_included_correct)
  show "finite_check_generation G B u []" by (rule correct(6))
  show "finite_generation_formed G" by (rule finite_check_generation_formed[OF correct(6)])
qed

end
