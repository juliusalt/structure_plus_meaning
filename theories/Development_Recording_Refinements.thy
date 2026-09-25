theory Development_Recording_Refinements
  imports Development_Bounded_Recording Established_Premises Factor_Checked_Certificate_Premises
    Factor_Formed_Inner_Readings Factor_Shared_Package_Readings
begin

text \<open>
  The recording's refinement collection (DECISIONS.md, task 482's entry, its (4) R): each refinement of the
  bounded recording is a new constant beside the original with its exactness under the premise the recording
  establishes, and the code equations of the recording's own constants that call it. No library theory imports
  this theory, and no theory a recorded state's definition imports; execution theories do.
\<close>

section \<open>Where the recording's premises are established\<close>

text \<open>
  The recording records at locus and payload @{term "Finite_Whole R"}, where R is the payload's complete data
  quotation, and every premise its refinements take is established on its path, never checked again inside:
  R's formation by the formation of the quoted term, a walk of the term, from which the quotation forms R
  (@{text finite_data_syntax_quotation_formed}); the formation of each environment the path builds by the
  contract of the constructor that returned it (the requirements installation's K, the certificate graph's F, the
  application's A, the replay environment B, J and the package environments restrictions of formed environments);
  the policy package P by its one reading at K, each later reading of the same package at an environment including
  K's package being that program by the contracts named. Where the original is called, as in the recording of a
  term that is not formed, the checks it makes stay.

  @{const finite_construct_formed_cause_generation} checks the formation of both targets, two walks of R. Under
  their formation it is the constructor below, which keeps the check of the cited rows' distinctness: the first
  notion of @{text Established_Premises}, its premise established where R's formation is.
\<close>

definition finite_construct_quoted_generation :: development_constructor where
  "finite_construct_quoted_generation E l p c rows=(if distinct (map snd rows) then
    map_option (finite_generation_record_body E l p c rows) (keyed_option_map (finite_anchor_artifact E) (map fst rows))
    else None)"

lemma finite_construct_quoted_generation_exact:
  assumes "finite_target_formed l" "finite_target_formed p"
  shows "finite_construct_formed_cause_generation E l p c rows=finite_construct_quoted_generation E l p c rows"
  using assms by (simp add: finite_construct_formed_cause_generation_def finite_construct_quoted_generation_def)

lemma finite_construct_quoted_generation_established:
  "established_premise (\<lambda>(l,p). finite_construct_formed_cause_generation E l p)
    (\<lambda>(l,p). finite_target_formed l \<and> finite_target_formed p) (\<lambda>(l,p). finite_construct_quoted_generation E l p)"
  by (rule established_premise.intro) (auto intro!: ext simp: finite_construct_quoted_generation_exact)

lemma finite_construct_quoted_generation_whole:
  assumes "finite_exact_formed R"
  shows "finite_construct_formed_cause_generation E (Finite_Whole R) (Finite_Whole R) c rows=
    finite_construct_quoted_generation E (Finite_Whole R) (Finite_Whole R) c rows"
  using assms by (simp add: finite_construct_quoted_generation_exact)

text \<open>
  The payload's quotation forms R from the term's formation. The listing policy's source is constructed only
  over formed presentations, so a judgment of R under the original is made only of a formed R: the fact the
  recording of a term that is not formed rests on, whose check that recording keeps.
\<close>

lemma finite_data_syntax_quotation_formed:
  assumes "term_formed t" "finite_data_syntax t=Some R"
  shows "finite_exact_formed R"
  using complete_data_quotation_formed[OF finite_data_syntax_complete_quotation[OF assms]]
  by (simp add: finite_exact_formed_correct)

lemma development_policy_source_with_formed:
  assumes policy: "development_policy_source_with xs=Some s"
  shows "list_all finite_term_formed xs"
proof -
  obtain d F u where "finite_ground_source xs=Some (d,F,u)"
    using policy by (cases "finite_ground_source xs") (auto simp: development_policy_source_with_def)
  then show ?thesis using finite_ground_source_total by blast
qed

lemma development_bounded_policy_judgment_formed:
  assumes judged: "development_bounded_policy_judgment [Finite_Target (Finite_Whole R)] R=Some j"
  shows "finite_exact_formed R"
proof -
  obtain d K pu B au root J C where j: "j=(d,K,pu,B,au,root,J,C)" by (metis prod.collapse)
  obtain p A M G I W F0 V where policy: "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    and "development_policy_certificate K pu d R=Some p"
    and "finite_native_certificate_replay K pu [] p d (Finite_Target (Finite_Whole R))=Some (A,M,root,G,au,I,W,B)"
    and "finite_bounded_judgment_quote B pu [] au [] R=Some (J,F0,V,C)"
    and "replay_policy_condition K pu [] d R J pu [] au []"
    by (rule development_bounded_policy_judgment_result[OF judged[unfolded j]])
  show ?thesis using development_policy_source_with_formed[OF policy] by simp
qed

section \<open>The listing policy's source over formed presentations\<close>

text \<open>
  The ground source checks the formation of every listed presentation, for the recording a walk of R; it is an
  instance of the first notion of @{text Established_Premises} checked at its entry.
\<close>

definition finite_ground_source_body where
  "finite_ground_source_body xs=finite_install_source_entry (finite_guard_source True) None [0] (finite_ground_program xs)
    (Some [],[])"

lemma finite_ground_source_checked_premise:
  "checked_premise finite_ground_source (list_all finite_term_formed) finite_ground_source_body (\<lambda>xs. None)"
  by unfold_locales (simp_all add: finite_ground_source_def finite_ground_source_body_def)

definition development_read_policy_source where
  "development_read_policy_source xs=(case finite_ground_source_body xs of None \<Rightarrow> None
    | Some (d,F,u) \<Rightarrow> finite_construct_source_requirements F u [] [Existing_Admission d])"

lemma development_read_policy_source_exact:
  assumes "list_all finite_term_formed xs"
  shows "development_read_policy_source xs=development_policy_source_with xs"
  using assms by (simp add: development_read_policy_source_def development_policy_source_with_def
    finite_ground_source_def finite_ground_source_body_def)

lemma development_policy_source_with_environment:
  assumes policy: "development_policy_source_with xs=Some (d,K,pu)"
  shows "finite_environment_formed K"
proof -
  obtain g where g: "finite_ground_source xs=Some g"
    using policy by (cases "finite_ground_source xs") (simp_all add: development_policy_source_with_def)
  obtain d0 F u where g0: "g=(d0,F,u)" by (cases g) blast
  have "finite_construct_source_requirements F u [] [Existing_Admission d0]=Some (d,K,pu)"
    using policy g g0 by (simp add: development_policy_source_with_def)
  then show ?thesis using finite_construct_source_requirements_correct by blast
qed

section \<open>The policy package read once, through formed bodies\<close>

text \<open>
  The package reader's formed body with every definition read through the formed bodies of
  @{text Factor_Formed_Inner_Readings}: at a formed environment it is the package reader.
\<close>

definition finite_native_package_readings_inner ::
    "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u finite_native_system fset" where
  "finite_native_package_readings_inner E u r=ffUnion (fimage (\<lambda>Q.
    case finite_demanded_readings (\<lambda>d. finite_native_definition_readings_inner E (fst d) (snd d))
        finite_definition_dependencies (fimage snd Q) of
      None \<Rightarrow> {||}
    | Some (S,G) \<Rightarrow> (if S |\<subseteq>| fimage fst G then
        {|\<lparr>finite_system_interfaces=fimage (\<lambda>(d,p,F). (d,p)) G,
          finite_system_clauses=ffUnion (fimage (\<lambda>(d,p,F). fimage (\<lambda>(c,S). ((d,c),S)) F) G)\<rparr>|}
        else {||})) (finite_family_readings_formed E u r (finite_located_values E u)))"

lemma finite_native_package_readings_inner_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_package_readings E u r=finite_native_package_readings_inner E u r"
proof -
  have site: "finite_definition_site_reading_formed E=(\<lambda>d. finite_native_definition_readings_inner E (fst d) (snd d))"
    by (rule ext) (simp only: finite_definition_site_reading_formed_def finite_native_definition_readings_inner_exact[OF formed])
  have roots: "finite_native_root_family_readings E u r=finite_family_readings_formed E u r (finite_located_values E u)"
    by (simp only: finite_native_root_family_readings_def finite_family_readings_formed_exact[OF formed])
  show ?thesis
    by (simp only: checked_premise.checked_at_entry[OF finite_native_package_readings_checked_premise] formed if_True
      site roots finite_native_package_readings_inner_def)
qed

definition finite_native_source_inner ::
    "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u finite_native_system option" where
  "finite_native_source_inner E u r=finite_singleton_option (finite_native_package_readings_inner E u r)"

lemma finite_native_source_inner_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_source E u r=finite_native_source_inner E u r"
  by (simp only: finite_native_source_def finite_native_source_inner_def finite_native_package_readings_inner_exact[OF formed])

text \<open>A package read at an environment has the read program's definitions as its sites.\<close>

lemma finite_native_package_sites_program:
  assumes package: "P |\<in>| finite_native_package_readings E u r"
  shows "finite_native_package_sites E u r=finite_system_definitions P"
proof -
  have "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    using package by (simp only: finite_native_package_readings_correct)
  then have "system_definitions (decode_finite_system P)=native_package_sites (decode_finite_environment E) u r"
    by (rule native_package_projection(3))
  then have "fset (finite_native_package_sites E u r)=fset (finite_system_definitions P)"
    by (simp only: finite_native_package_sites_correct finite_system_definitions_correct)
  then show ?thesis by (simp only: fset_inject)
qed

section \<open>The slots a package demands, read through formed bodies\<close>

text \<open>
  The formed body of a definition's slots still read the formation of every target a citation reaches, through
  the pattern and premise readings: stated over the formed targets (#535's follow-up 3), it checks nothing.
\<close>

lemma finite_pattern_readings_carrier_targeted:
  assumes formed: "finite_environment_formed E"
  shows "finite_pattern_readings_carrier_formed E u V r=
    targeted_sized_pattern_readings (finite_citation_targets_formed E u) (artifact_readings_at E u) V r"
  by (simp only: finite_pattern_readings_carrier_formed_read_code read_sized_pattern_readings_targeted
      finite_citation_targets_formed_exact[OF formed])

lemma finite_native_premise_readings_targeted:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_premise_readings_formed E u V r=
    targeted_premise_readings (finite_citation_targets_formed E u) E u (artifact_readings_at E u) V r"
  by (simp only: finite_native_premise_readings_formed_read_code read_premise_readings_targeted
      finite_citation_targets_formed_exact[OF formed])

lemma finite_scoped_pattern_readings_targeted:
  assumes formed: "finite_environment_formed E"
  shows "finite_scoped_pattern_readings_formed E u r=
    targeted_scoped_pattern_readings (finite_citation_targets_formed E u) (artifact_readings_at E u) r"
  by (simp only: finite_scoped_pattern_readings_formed_read_code read_scoped_pattern_readings_targeted
      finite_citation_targets_formed_exact[OF formed])

definition finite_native_schema_slots_inner ::
    "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address fset" where
  "finite_native_schema_slots_inner E u r=ffUnion (fimage (\<lambda>C.
    finite_three_field_record_formed C r (\<lambda>ps b c m. ffUnion (fimage (\<lambda>V.
      finite_reading_slots (targeted_sized_pattern_readings (finite_citation_targets_formed E u) (artifact_readings_at E u) V c) |\<union>|
      ffUnion (fimage (\<lambda>a. finite_reading_slots
        (targeted_premise_readings (finite_citation_targets_formed E u) E u (artifact_readings_at E u) V a))
        (finite_family_endpoints_formed E u m))) (finite_binder_scope_body_candidates C b))))
    (finite_artifacts_at E u))"

lemma finite_native_schema_slots_inner_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_schema_slots_formed E=finite_native_schema_slots_inner E"
  by (intro ext) (simp only: finite_native_schema_slots_formed_def finite_native_schema_slots_inner_def
      finite_native_premise_family_slots_formed_def finite_pattern_readings_carrier_targeted[OF formed]
      finite_native_premise_readings_targeted[OF formed])

definition finite_native_definition_slots_inner ::
    "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address fset" where
  "finite_native_definition_slots_inner E u r=ffUnion (fimage (\<lambda>C.
    finite_two_field_record_formed C r (\<lambda>ps i m.
      finite_reading_slots (targeted_scoped_pattern_readings (finite_citation_targets_formed E u) (artifact_readings_at E u) i) |\<union>|
      ffUnion (fimage (finite_native_schema_slots_inner E u) (finite_family_endpoints_formed E u m))))
    (finite_artifacts_at E u))"

lemma finite_native_definition_slots_inner_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_definition_slots_formed E=finite_native_definition_slots_inner E"
  by (intro ext) (simp only: finite_native_definition_slots_formed_def finite_native_definition_slots_inner_def
      finite_scoped_pattern_readings_targeted[OF formed] finite_native_schema_slots_inner_exact[OF formed])

definition finite_native_package_demands_inner ::
    "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u definition_site fset \<Rightarrow> ('u\<times>local_address) fset" where
  "finite_native_package_demands_inner E u r S=finite_requested_slots E (fimage (Pair u) (finite_family_endpoints_formed E u r)) |\<union>|
    ffUnion (fimage (\<lambda>(v,a). fimage (Pair v) (finite_native_definition_slots_inner E v a)) S)"

lemma finite_native_package_demands_inner_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_package_demands_over E u r S=finite_native_package_demands_inner E u r S"
  by (simp only: finite_native_package_demands_over_def formed if_True finite_native_root_requests_def
      finite_family_endpoints_formed_exact[OF formed] finite_native_definition_slots_inner_exact[OF formed]
      finite_native_package_demands_inner_def)

section \<open>The least environments at the read program\<close>

text \<open>
  A judgment's least environment and a replay's read the package's sites for their sources and their demands:
  at an environment whose package is the read program P they are P's definitions, and every reading under them
  is a formed body.
\<close>

definition finite_judgment_environment_at ::
    "'u finite_native_system \<Rightarrow> 'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
      'u finite_artifact_environment" where
  "finite_judgment_environment_at P E pu pr au ar=(let S=finite_system_definitions P in
    finite_read_environment E (finsert pu (fimage fst S) |\<union>| {|au|})
      (finite_native_package_demands_inner E pu pr S |\<union>|
        fimage (Pair au) (finite_reading_slots (finite_application_readings_inner E au ar))))"

lemma finite_judgment_environment_at_exact:
  assumes formed: "finite_environment_formed E" and package: "P |\<in>| finite_native_package_readings E pu pr"
  shows "finite_native_judgment_environment E pu pr au ar=finite_judgment_environment_at P E pu pr au ar"
  by (simp only: finite_native_judgment_environment_shared_code finite_native_package_sites_program[OF package]
      finite_native_package_demands_inner_exact[OF formed] finite_native_application_demands_def
      finite_application_readings_inner_exact[OF formed] finite_judgment_environment_at_def)

definition finite_replay_environment_at ::
    "'u finite_native_system \<Rightarrow> 'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
      'u finite_native_derivation_graph \<Rightarrow> 'u finite_artifact_environment" where
  "finite_replay_environment_at P E pu pr au ar G=(let S=finite_system_definitions P in
    finite_read_environment E ((finsert pu (fimage fst S) |\<union>| {|au|}) |\<union>| finite_native_graph_sources G)
      ((finite_native_package_demands_inner E pu pr S |\<union>|
        fimage (Pair au) (finite_reading_slots (finite_application_readings_inner E au ar))) |\<union>|
        ffUnion (fimage (\<lambda>(n,N). fimage (Pair (fst n)) (finite_native_node_slots_inner E n N (finite_graph_premises G n)))
          (finite_graph_inferences G))))"

lemma finite_replay_environment_at_exact:
  assumes formed: "finite_environment_formed E" and package: "P |\<in>| finite_native_package_readings E pu pr"
  shows "finite_native_replay_environment E pu pr au ar G=finite_replay_environment_at P E pu pr au ar G"
  by (simp only: finite_native_replay_environment_shared_code finite_native_package_sites_program[OF package]
      finite_native_package_demands_inner_exact[OF formed] finite_native_application_demands_def
      finite_application_readings_inner_exact[OF formed] finite_native_graph_demands_inner_code formed if_True
      finite_replay_environment_at_def)

section \<open>The certificate and its replay at the read program\<close>

definition development_policy_certificate_at ::
    "local_address option finite_native_system \<Rightarrow> local_address option definition_site \<Rightarrow> finite_exact_artifact \<Rightarrow>
      (local_address,local_address,local_address,finite_factor_term) inference_proof option" where
  "development_policy_certificate_at P d R=(case finite_program_proofs P
       (finite_program_term_demand P {|Finite_Target (Finite_Whole R)|}) of
     None \<Rightarrow> None
   | Some (A,T) \<Rightarrow> map_option snd (finite_singleton_option
       (ffilter (\<lambda>((e,v),p). e=d \<and> v=Finite_Target (Finite_Whole R)) T)))"

lemma development_policy_certificate_at_exact:
  assumes source: "finite_native_source K u []=Some P"
  shows "development_policy_certificate K u d R=development_policy_certificate_at P d R"
  by (simp add: development_policy_certificate_def development_policy_certificate_at_def finite_source_computation_def
    source split: option.splits prod.splits)

text \<open>
  The application at a formed environment and a formed term: its readiness is the position of the called site
  alone.
\<close>

definition finite_extend_application_formed where
  "finite_extend_application_formed E d t=(if d |\<in>| finite_environment_positions E then
    map_option (\<lambda>R. let q=Finite_Pair (Finite_Target (Finite_Anchor R (snd d))) t in
      (finite_future_call_environment E (fst d) R (snd d) t,finite_future_call_use E (fst d),
        finite_term_syntax_interior q,fimage fst (finite_term_literal_bindings q)))
      (finite_anchor_artifact E d) else None)"

lemma finite_extend_application_formed_exact:
  assumes "finite_environment_formed E" "finite_term_formed t"
  shows "finite_extend_native_application E d t=finite_extend_application_formed E d t"
  using assms by (simp add: finite_extend_native_application_def finite_extend_application_formed_def
    finite_application_ready_def)

text \<open>
  The replay at the read program: the certificate graph at its body, both its premises established (the program
  by its reading, the call term by R's formation), the application at the graph's formed environment, and the
  replay environment at the read program.
\<close>

definition finite_certificate_replay_at where
  "finite_certificate_replay_at K P u p d t=(case finite_certificate_graph_body K P p d t of None \<Rightarrow> None
    | Some (F,M,root,G) \<Rightarrow> map_option (\<lambda>(A,au,I,W).
      (A,M,root,G,au,I,W,finite_replay_environment_at P A u [] au [] G))
      (finite_extend_application_formed F d t))"

lemma finite_certificate_replay_at_exact:
  assumes source: "finite_native_source K u []=Some P" and called: "finite_term_formed t"
  shows "finite_native_certificate_replay K u [] p d t=finite_certificate_replay_at K P u p d t"
proof -
  have graph: "finite_native_certificate_graph K u [] p d t=finite_certificate_graph_body K P p d t"
    by (simp add: finite_native_certificate_graph_premises source
      checked_premise.checked_at_entry[OF finite_certificate_graph_checked] called)
  show ?thesis
  proof (cases "finite_certificate_graph_body K P p d t")
    case None
    then show ?thesis by (simp add: finite_native_certificate_replay_def finite_certificate_replay_at_def graph)
  next
    case (Some g)
    note body=Some
    obtain F M root G where g: "g=(F,M,root,G)" by (cases g) blast
    have orig_graph: "finite_native_certificate_graph K u [] p d t=Some (F,M,root,G)" using graph body g by simp
    have F: "finite_environment_formed F" by (rule finite_native_certificate_graph_correct(2)[OF orig_graph source])
    have app: "finite_extend_native_application F d t=finite_extend_application_formed F d t"
      by (rule finite_extend_application_formed_exact[OF F called])
    show ?thesis
    proof (cases "finite_extend_application_formed F d t")
      case None
      then show ?thesis
        by (simp add: finite_native_certificate_replay_def finite_certificate_replay_at_def orig_graph app body g)
    next
      case (Some e)
      note extended=Some
      obtain A au I W where e: "e=(A,au,I,W)" by (cases e) blast
      have orig: "finite_native_certificate_replay K u [] p d t=
          Some (A,M,root,G,au,I,W,finite_native_replay_environment A u [] au [] G)"
        using orig_graph app extended e by (simp add: finite_native_certificate_replay_def)
      have A: "finite_environment_formed A" by (rule finite_native_certificate_replay_correct(1)[OF orig source])
      have AP: "P |\<in>| finite_native_package_readings A u []"
        using finite_native_certificate_replay_correct(4)[OF orig source] by (simp only: finite_native_source_member)
      have env: "finite_native_replay_environment A u [] au [] G=finite_replay_environment_at P A u [] au [] G"
        by (rule finite_replay_environment_at_exact[OF A AP])
      show ?thesis using orig body g extended e by (simp add: env finite_certificate_replay_at_def)
    qed
  qed
qed

section \<open>The judgment's quotation and condition, established by the replay's contract\<close>

text \<open>
  The replay's contract states that its environment B is formed, reads the program P and reads the call: the
  judgment's readiness at B holds, and its least environment is the one at P.
\<close>

definition finite_bounded_quote_at where
  "finite_bounded_quote_at P E pu au R=(let J=finite_judgment_environment_at P E pu [] au [];
     V=finite_payload_uses J R; F0=finite_payload_fill J V finite_empty_artifact in
     if finite_environment_formed F0 \<and> (pu,[]) |\<in>| finite_environment_positions F0 \<and>
       (au,[]) |\<in>| finite_environment_positions F0
     then map_option (\<lambda>C. (J,F0,V,C)) (finite_data_syntax (finite_bounded_scope_term F0 pu [] au [] V))
     else None)"

lemma finite_bounded_quote_at_exact:
  assumes formed: "finite_environment_formed E" and package: "P |\<in>| finite_native_package_readings E pu []"
    and app: "x |\<in>| finite_application_readings E au []"
  shows "finite_bounded_judgment_quote E pu [] au [] R=finite_bounded_quote_at P E pu au R"
proof -
  have ready: "finite_native_judgment_ready E pu [] au []"
    using package app by (auto simp: finite_native_judgment_ready_def)
  show ?thesis
    by (simp add: finite_bounded_judgment_quote_def finite_ready_judgment_environment_def ready
      finite_judgment_environment_at_exact[OF formed package] finite_bounded_quote_at_def Let_def)
qed

text \<open>
  The condition is established by the contracts of the path: the policy package is read at K; the package
  environments of K and J are equal, J's being B's (the bounded quotation's contract) and both K's and B's
  being A's (a package's environment is kept in a formed environment including it); the call is read at J
  (the least judgment environment keeps it). No reading of the condition is computed.
\<close>

lemma development_bounded_condition_established:
  assumes source: "finite_native_source K u []=Some P"
    and replay: "finite_native_certificate_replay K u [] p d (Finite_Target (Finite_Whole R))=Some (A,M,root,G,au,I,W,B)"
    and quote: "finite_bounded_judgment_quote B u [] au [] R=Some (J,F0,V,C)"
  shows "replay_policy_condition K u [] d R J u [] au []"
proof -
  note facts=finite_native_certificate_replay_correct[OF replay source]
  have KP: "P |\<in>| finite_native_package_readings K u []" using source by (simp only: finite_native_source_member)
  have K: "native_package_at (decode_finite_environment K) u [] (decode_finite_system P)"
    using source by (simp only: finite_native_source_correct)
  have B: "native_package_at (decode_finite_environment B) u [] (decode_finite_system P)"
    using facts(12) by (simp only: finite_native_package_readings_correct)
  have A: "environment_formed (decode_finite_environment A)"
    using facts(1) by (simp only: finite_environment_formed_correct)
  have eqK: "native_package_environment (decode_finite_environment A) u []=
      native_package_environment (decode_finite_environment K) u []"
    by (rule native_package_environment_extension[OF K facts(2) A])
  have eqB: "native_package_environment (decode_finite_environment A) u []=
      native_package_environment (decode_finite_environment B) u []"
    by (rule native_package_environment_extension[OF B facts(11) A])
  have eqJ: "native_package_environment (decode_finite_environment J) u []=
      native_package_environment (decode_finite_environment B) u []"
    by (rule finite_bounded_judgment_quote_correct(7)[OF quote])
  have "decode_finite_environment (finite_native_package_environment J u [])=
      decode_finite_environment (finite_native_package_environment K u [])"
    using eqK eqB eqJ by (simp only: finite_native_package_environment_correct)
  then have environments: "finite_native_package_environment J u []=finite_native_package_environment K u []"
    by (simp only: decode_finite_environment_injective)
  have J: "J=finite_native_judgment_environment B u [] au []"
    using finite_bounded_judgment_quote_result[THEN iffD1, OF quote] by blast
  have "((d,Finite_Target (Finite_Whole R)),I,W) |\<in>| finite_application_readings J au []"
    unfolding J by (rule finite_native_judgment_environment_recovers(2)[OF facts(12) facts(14)])
  then have call_ready: "finite_application_value_ready J au [] d (Finite_Target (Finite_Whole R))"
    by (auto simp: finite_application_value_ready_def)
  show ?thesis
    using KP environments call_ready by (auto simp: replay_policy_condition_def finite_policy_cause_alignment_def)
qed

section \<open>The bounded judgment over formed presentations of a formed payload\<close>

definition development_read_policy_judgment ::
    "finite_factor_term list \<Rightarrow> finite_exact_artifact \<Rightarrow> development_policy_judgment option" where
  "development_read_policy_judgment xs R=(case development_read_policy_source xs of
     None \<Rightarrow> None
   | Some (d,K,pu) \<Rightarrow> (case finite_native_source_inner K pu [] of
       None \<Rightarrow> None
     | Some P \<Rightarrow> Option.bind (development_policy_certificate_at P d R) (\<lambda>p.
         case finite_certificate_replay_at K P pu p d (Finite_Target (Finite_Whole R)) of
           None \<Rightarrow> None
         | Some (A,M,root,G,au,I,W,B) \<Rightarrow>
             map_option (\<lambda>(J,F0,V,C). (d,K,pu,B,au,root,J,C)) (finite_bounded_quote_at P B pu au R))))"

theorem development_read_policy_judgment_exact:
  assumes listed: "list_all finite_term_formed xs" and payload: "finite_exact_formed R"
  shows "development_read_policy_judgment xs R=development_bounded_policy_judgment xs R"
proof (cases "development_policy_source_with xs")
  case None
  then show ?thesis
    by (simp add: development_read_policy_judgment_def development_bounded_policy_judgment_def
      development_read_policy_source_exact[OF listed])
next
  case (Some s)
  obtain d K pu where s: "s=(d,K,pu)" by (cases s) blast
  have policy: "development_policy_source_with xs=Some (d,K,pu)" using Some s by simp
  have K: "finite_environment_formed K" by (rule development_policy_source_with_environment[OF policy])
  have called: "finite_term_formed (Finite_Target (Finite_Whole R))" using payload by simp
  note judgment_defs=development_read_policy_judgment_def development_bounded_policy_judgment_def
    development_read_policy_source_exact[OF listed] policy finite_native_source_inner_exact[OF K, symmetric]
  show ?thesis
  proof (cases "finite_native_source K pu []")
    case None
    then show ?thesis by (simp add: judgment_defs development_policy_certificate_def finite_source_computation_def)
  next
    case (Some P)
    note source=Some
    have certificate: "development_policy_certificate K pu d R=development_policy_certificate_at P d R"
      by (rule development_policy_certificate_at_exact[OF source])
    show ?thesis
    proof (cases "development_policy_certificate_at P d R")
      case None
      then show ?thesis by (simp add: judgment_defs source certificate)
    next
      case (Some p)
      note found=Some
      have replay_eq: "finite_native_certificate_replay K pu [] p d (Finite_Target (Finite_Whole R))=
          finite_certificate_replay_at K P pu p d (Finite_Target (Finite_Whole R))"
        by (rule finite_certificate_replay_at_exact[OF source called])
      show ?thesis
      proof (cases "finite_native_certificate_replay K pu [] p d (Finite_Target (Finite_Whole R))")
        case None
        then show ?thesis using replay_eq by (simp add: judgment_defs source certificate found)
      next
        case (Some y)
        obtain A M root G au I W B where y: "y=(A,M,root,G,au,I,W,B)" by (metis prod.collapse)
        have replay: "finite_native_certificate_replay K pu [] p d (Finite_Target (Finite_Whole R))=
            Some (A,M,root,G,au,I,W,B)" using Some y by simp
        have at_replay: "finite_certificate_replay_at K P pu p d (Finite_Target (Finite_Whole R))=
            Some (A,M,root,G,au,I,W,B)" using replay replay_eq by simp
        note facts=finite_native_certificate_replay_correct[OF replay source]
        have quote_eq: "finite_bounded_judgment_quote B pu [] au [] R=finite_bounded_quote_at P B pu au R"
          by (rule finite_bounded_quote_at_exact[OF facts(10) facts(12) facts(14)])
        show ?thesis
        proof (cases "finite_bounded_judgment_quote B pu [] au [] R")
          case None
          then show ?thesis using replay at_replay quote_eq by (simp add: judgment_defs source certificate found)
        next
          case (Some q)
          obtain J F0 V C where q: "q=(J,F0,V,C)" by (metis prod.collapse)
          have quote: "finite_bounded_judgment_quote B pu [] au [] R=Some (J,F0,V,C)" using Some q by simp
          have condition: "replay_policy_condition K pu [] d R J pu [] au []"
            by (rule development_bounded_condition_established[OF source replay quote])
          have at_quote: "finite_bounded_quote_at P B pu au R=Some (J,F0,V,C)" using quote quote_eq by simp
          show ?thesis using replay at_replay quote at_quote condition
            by (simp add: judgment_defs source certificate found)
        qed
      qed
    qed
  qed
qed

text \<open>
  Outside its premise the original refuses: a presentation that is not formed refuses the policy's ground source,
  and a payload that is not formed refuses the certificate graph, whose checked certificate has a formed call
  term (@{thm [source] finite_checked_certificate_formed}).
\<close>

lemma development_bounded_policy_judgment_unformed:
  assumes unformed: "\<not>finite_exact_formed R"
  shows "development_bounded_policy_judgment xs R=None"
proof (rule ccontr)
  assume "development_bounded_policy_judgment xs R\<noteq>None"
  then obtain j where "development_bounded_policy_judgment xs R=Some j" by blast
  moreover obtain d K pu B au root J C where "j=(d,K,pu,B,au,root,J,C)" by (metis prod.collapse)
  ultimately have judged: "development_bounded_policy_judgment xs R=Some (d,K,pu,B,au,root,J,C)" by simp
  obtain p A M G I W F0 V where
    replay: "finite_native_certificate_replay K pu [] p d (Finite_Target (Finite_Whole R))=Some (A,M,root,G,au,I,W,B)"
    by (rule development_bounded_policy_judgment_result[OF judged])
  from replay obtain F where
    graph: "finite_native_certificate_graph K pu [] p d (Finite_Target (Finite_Whole R))=Some (F,M,root,G)"
    unfolding finite_native_certificate_replay_result by blast
  from graph obtain P where checked: "finite_checks_schema_proof P p d (Finite_Target (Finite_Whole R))"
    unfolding finite_native_certificate_graph_result by blast
  have "finite_term_formed (Finite_Target (Finite_Whole R))" by (rule finite_checked_certificate_formed(2)[OF checked])
  then show False using unformed by simp
qed

lemma development_bounded_policy_judgment_checked_premise:
  "checked_premise (development_bounded_policy_judgment xs) (\<lambda>R. list_all finite_term_formed xs \<and> finite_exact_formed R)
    (development_read_policy_judgment xs) (\<lambda>R. None)"
proof unfold_locales
  fix R assume "list_all finite_term_formed xs \<and> finite_exact_formed R"
  then show "development_bounded_policy_judgment xs R=development_read_policy_judgment xs R"
    by (simp add: development_read_policy_judgment_exact)
next
  fix R assume premise: "\<not>(list_all finite_term_formed xs \<and> finite_exact_formed R)"
  show "development_bounded_policy_judgment xs R=None"
  proof (cases "list_all finite_term_formed xs")
    case True
    then show ?thesis using premise development_bounded_policy_judgment_unformed by blast
  next
    case False
    then have "finite_ground_source xs=None" by (simp add: finite_ground_source_def)
    then show ?thesis by (simp add: development_bounded_policy_judgment_def development_policy_source_with_def)
  qed
qed

section \<open>The ready judgment environment, checked once at its entry\<close>

text \<open>
  The ready judgment environment reads the package and the call of an environment no constructor established:
  its formation is checked once, at the entry, and the package is read once, its sites the read program's.
\<close>

lemma finite_ready_judgment_environment_checked_premise:
  "checked_premise finite_ready_judgment_environment finite_environment_formed
    (\<lambda>E pu pr au ar. case finite_native_source_inner E pu pr of
       None \<Rightarrow> None
     | Some P \<Rightarrow> if finite_application_readings_inner E au ar\<noteq>{||}
         then Some (finite_judgment_environment_at P E pu pr au ar) else None)
    (\<lambda>E pu pr au ar. None)"
proof unfold_locales
  fix E :: "'u finite_artifact_environment" assume formed: "finite_environment_formed E"
  show "finite_ready_judgment_environment E=(\<lambda>pu pr au ar. case finite_native_source_inner E pu pr of
       None \<Rightarrow> None
     | Some P \<Rightarrow> if finite_application_readings_inner E au ar\<noteq>{||}
         then Some (finite_judgment_environment_at P E pu pr au ar) else None)"
  proof (intro ext)
    fix pu pr au ar
    have apps: "finite_application_readings E au ar=finite_application_readings_inner E au ar"
      by (simp only: finite_application_readings_inner_exact[OF formed])
    show "finite_ready_judgment_environment E pu pr au ar=(case finite_native_source_inner E pu pr of
       None \<Rightarrow> None
     | Some P \<Rightarrow> if finite_application_readings_inner E au ar\<noteq>{||}
         then Some (finite_judgment_environment_at P E pu pr au ar) else None)"
    proof (cases "finite_native_source E pu pr")
      case None
      have empty: "finite_native_package_readings E pu pr={||}"
      proof (rule ccontr)
        assume "finite_native_package_readings E pu pr\<noteq>{||}"
        then obtain P where "P |\<in>| finite_native_package_readings E pu pr" by (auto simp: fset_eq_iff)
        then have "finite_native_source E pu pr=Some P" by (simp only: finite_native_source_member)
        then show False using None by simp
      qed
      show ?thesis using None empty
        by (simp add: finite_ready_judgment_environment_def finite_native_judgment_ready_def
          finite_native_source_inner_exact[OF formed, symmetric])
    next
      case (Some P)
      have package: "P |\<in>| finite_native_package_readings E pu pr" using Some by (simp only: finite_native_source_member)
      then have nonempty: "finite_native_package_readings E pu pr\<noteq>{||}" by auto
      show ?thesis using Some nonempty
        by (simp add: finite_ready_judgment_environment_def finite_native_judgment_ready_def apps
          finite_native_source_inner_exact[OF formed, symmetric] finite_judgment_environment_at_exact[OF formed package])
    qed
  qed
next
  fix E :: "'u finite_artifact_environment" assume unformed: "\<not>finite_environment_formed E"
  have "finite_native_package_readings E=(\<lambda>u r. {||})"
    by (rule checked_premise.refused[OF finite_native_package_readings_checked_premise unformed])
  then show "finite_ready_judgment_environment E=(\<lambda>pu pr au ar. None)"
    by (intro ext) (simp add: finite_ready_judgment_environment_def finite_native_judgment_ready_def)
qed

declare finite_ready_judgment_environment_def [code del]

lemma finite_ready_judgment_environment_read [code]:
  "finite_ready_judgment_environment E=(if finite_environment_formed E
    then (\<lambda>pu pr au ar. case finite_native_source_inner E pu pr of
       None \<Rightarrow> None
     | Some P \<Rightarrow> if finite_application_readings_inner E au ar\<noteq>{||}
         then Some (finite_judgment_environment_at P E pu pr au ar) else None)
    else (\<lambda>pu pr au ar. None))"
  by (rule checked_premise.checked_at_entry[OF finite_ready_judgment_environment_checked_premise])

section \<open>The code equations of the bounded judgment and of the recording\<close>

declare development_bounded_policy_judgment_def [code del]

lemma development_bounded_policy_judgment_read [code]:
  "development_bounded_policy_judgment xs R=(if list_all finite_term_formed xs \<and> finite_exact_formed R
    then development_read_policy_judgment xs R else None)"
  by (rule checked_premise.checked_at_entry[OF development_bounded_policy_judgment_checked_premise])

text \<open>
  The recording at its payload's index. The recording of a term that is not formed calls the bounded judgment,
  whose checks stay, and records by the constructor that makes neither target formation, R's formation resting
  on the judgment's policy source (@{thm [source] development_bounded_policy_judgment_formed}). The recording of a
  formed term establishes R's formation by the term's, and calls the judgment over formed presentations.
\<close>

declare development_indexed_generation_def [code del]

lemma development_indexed_generation_quoted:
  "development_indexed_generation t H rows=(case finite_data_syntax (decode_finite_term t) of
     None \<Rightarrow> None
   | Some R \<Rightarrow> Option.bind (development_bounded_policy_judgment [Finite_Target (Finite_Whole R)] R)
       (\<lambda>(d,K,pu,B,au,root,J,C). finite_construct_quoted_generation H (Finite_Whole R) (Finite_Whole R)
          (Finite_Whole C) rows))"
proof (cases "finite_data_syntax (decode_finite_term t)")
  case None
  then show ?thesis by (simp add: development_indexed_generation_def)
next
  case (Some R)
  note quoted=this
  show ?thesis
  proof (cases "development_bounded_policy_judgment [Finite_Target (Finite_Whole R)] R")
    case None
    then show ?thesis using quoted by (simp add: development_indexed_generation_def)
  next
    case (Some j)
    have formed: "finite_exact_formed R" by (rule development_bounded_policy_judgment_formed[OF Some])
    show ?thesis using quoted Some
      by (simp add: development_indexed_generation_def finite_construct_quoted_generation_whole[OF formed]
        split: prod.splits)
  qed
qed

lemma development_indexed_generation_read [code]:
  "development_indexed_generation t H rows=(case finite_data_syntax (decode_finite_term t) of
     None \<Rightarrow> None
   | Some R \<Rightarrow> Option.bind (if finite_term_formed t then development_read_policy_judgment [Finite_Target (Finite_Whole R)] R
         else development_bounded_policy_judgment [Finite_Target (Finite_Whole R)] R)
       (\<lambda>(d,K,pu,B,au,root,J,C). finite_construct_quoted_generation H (Finite_Whole R) (Finite_Whole R)
          (Finite_Whole C) rows))"
proof (cases "finite_data_syntax (decode_finite_term t)")
  case None
  then show ?thesis by (simp add: development_indexed_generation_def)
next
  case (Some R)
  note quoted=Some
  show ?thesis
  proof (cases "finite_term_formed t")
    case True
    have "term_formed (decode_finite_term t)" using True by (simp only: finite_term_formed_correct)
    then have formed: "finite_exact_formed R" by (rule finite_data_syntax_quotation_formed[OF _ quoted])
    have same_judgment: "development_read_policy_judgment [Finite_Target (Finite_Whole R)] R=
        development_bounded_policy_judgment [Finite_Target (Finite_Whole R)] R"
      using formed by (simp add: development_read_policy_judgment_exact)
    show ?thesis using quoted True
      by (simp add: development_indexed_generation_def same_judgment finite_construct_quoted_generation_whole[OF formed])
  next
    case False
    show ?thesis using quoted False by (simp add: development_indexed_generation_quoted)
  qed
qed

end
