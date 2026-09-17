theory Factor_Parametric_Generation_Replay
  imports RRA_Generation_Record_Backends Factor_Replay_Generation_Certification
    Factor_Finite_Generation_Replay_Completion Optional_Transition_Sequences
begin

definition record_native_replay_with where
  "record_native_replay_with construct H l rows E pu pr au ar root R=(
    if finite_literal_replay_ready E pu pr au ar root R then
      (case finite_native_judgment_quote E pu pr au ar of None \<Rightarrow> None
      | Some (J,C) \<Rightarrow> map_option (\<lambda>(A,u,G). (A,u,G,J,C))
          (construct H l (Finite_Whole R) (Finite_Whole C) rows))
    else None)"

lemma record_native_replay_with_result:
  "record_native_replay_with construct H l rows E pu pr au ar root R=Some (A,u,G,J,C) \<longleftrightarrow>
    finite_literal_replay_ready E pu pr au ar root R \<and>
    finite_native_judgment_quote E pu pr au ar=Some (J,C) \<and>
    construct H l (Finite_Whole R) (Finite_Whole C) rows=Some (A,u,G)"
  by (auto simp: record_native_replay_with_def split: option.splits prod.splits if_splits)

theorem original_record_replay_instance:
  "record_native_replay_with finite_construct_generation_record=finite_record_native_replay"
  by (simp only: record_native_replay_with_def[abs_def] finite_record_native_replay_def[abs_def])

theorem record_native_replay_with_projection:
  assumes each: "\<And>q l p c rows. map_option (\<lambda>(following,u,G). (project following,u,G))
    (construct q l p c rows)=original (project q) l p c rows"
  shows "map_option (\<lambda>(following,u,G,J,C). (project following,u,G,J,C))
      (record_native_replay_with construct q l rows E pu pr au ar root R)=
    record_native_replay_with original (project q) l rows E pu pr au ar root R"
  by (cases "finite_literal_replay_ready E pu pr au ar root R";
      cases "finite_native_judgment_quote E pu pr au ar")
    (simp_all add: record_native_replay_with_def each[symmetric] option.map_comp comp_def
      case_prod_unfold split: prod.splits)

context generation_record_backend
begin

theorem record_replay_certified:
  assumes result: "record_native_replay_with construct H l rows E pu pr au ar root R=Some (A,u,G,J,C)"
  shows "certified_base_cause_at (decode_finite_environment (read_environment A)) u []
    (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
proof -
  have ready: "finite_literal_replay_ready E pu pr au ar root R"
    and quoted: "finite_native_judgment_quote E pu pr au ar=Some (J,C)"
    and generated: "construct H l (Finite_Whole R) (Finite_Whole C) rows=Some (A,u,G)"
    using result by (simp only: record_native_replay_with_result; blast)+
  have actual: "generation_at (decode_finite_environment (read_environment A)) u [] (decode_finite_generation G)"
    using generation[OF generated] by (simp only: finite_check_generation_exact)
  have payload: "generation_payload (decode_finite_generation G)=Whole_Artifact (decode_finite_object R)"
    and cause: "generation_cause (decode_finite_generation G)=Whole_Artifact (decode_finite_object C)"
    by (simp_all add: core[OF generated] finite_generation_record_core_def decode_finite_generation_node)
  show ?thesis by (rule finite_literal_replay_generation_certified[OF ready quoted actual payload cause])
qed

theorem record_replay_preserves_material:
  assumes result: "record_native_replay_with construct H l rows E pu pr au ar root R=Some (A,u,G,J,C)"
  shows "finite_environment_agrees_on (read_environment H) (read_environment A)
      (finite_environment_uses (read_environment H))"
    "finite_environment_formed (read_environment A)"
    "finite_environment_included (read_environment H) (read_environment A)"
    "finite_generation_predecessor_references (read_environment A) u [] l (Finite_Whole R) (Finite_Whole C)=
      fset_of_list (map fst rows)"
proof -
  have generated: "construct H l (Finite_Whole R) (Finite_Whole C) rows=Some (A,u,G)"
    using result by (simp only: record_native_replay_with_result; blast)
  show "finite_environment_agrees_on (read_environment H) (read_environment A)
      (finite_environment_uses (read_environment H))" by (rule agreement[OF generated])
  show "finite_environment_formed (read_environment A)" by (rule result_formed[OF generated])
  show "finite_environment_included (read_environment H) (read_environment A)" by (rule result_included[OF generated])
  show "finite_generation_predecessor_references (read_environment A) u [] l (Finite_Whole R) (Finite_Whole C)=
      fset_of_list (map fst rows)" by (rule references[OF generated])
qed

lemma record_replay_domain:
  "record_native_replay_with construct H l rows E pu pr au ar root R\<noteq>None \<longleftrightarrow>
    finite_environment_formed (read_environment H) \<and> finite_target_formed l \<and> distinct (map snd rows) \<and>
    list_all (\<lambda>(d,G). finite_check_generation G (read_environment H) (fst d) (snd d)) rows \<and>
    finite_literal_replay_ready E pu pr au ar root R"
proof
  assume available: "record_native_replay_with construct H l rows E pu pr au ar root R\<noteq>None"
  obtain A u G J C where result: "record_native_replay_with construct H l rows E pu pr au ar root R=Some (A,u,G,J,C)"
    using available by (cases "record_native_replay_with construct H l rows E pu pr au ar root R") auto
  have generated: "construct H l (Finite_Whole R) (Finite_Whole C) rows=Some (A,u,G)"
    and ready: "finite_literal_replay_ready E pu pr au ar root R"
    using result by (simp only: record_native_replay_with_result; blast)+
  show "finite_environment_formed (read_environment H) \<and> finite_target_formed l \<and> distinct (map snd rows) \<and>
    list_all (\<lambda>(d,G). finite_check_generation G (read_environment H) (fst d) (snd d)) rows \<and>
    finite_literal_replay_ready E pu pr au ar root R"
    using result_ready[OF generated] ready by (simp only: finite_generation_record_ready_def; blast)
next
  assume context_ready: "finite_environment_formed (read_environment H) \<and> finite_target_formed l \<and> distinct (map snd rows) \<and>
    list_all (\<lambda>(d,G). finite_check_generation G (read_environment H) (fst d) (snd d)) rows \<and>
    finite_literal_replay_ready E pu pr au ar root R"
  have ready: "finite_literal_replay_ready E pu pr au ar root R" using context_ready by blast
  have judgment_ready: "finite_native_judgment_ready E pu pr au ar" and payload: "finite_exact_formed R"
    by (rule finite_literal_replay_ready_properties[OF ready])+
  obtain J C where quoted: "finite_native_judgment_quote E pu pr au ar=Some (J,C)"
    using judgment_ready by (simp only: finite_native_judgment_quote_domain[symmetric]; blast)
  have cause: "finite_exact_formed C" by (rule finite_native_judgment_quote_formed[OF quoted])
  have record_ready: "finite_generation_record_ready (read_environment H) l (Finite_Whole R) (Finite_Whole C) rows"
    using context_ready payload cause by (simp add: finite_generation_record_ready_def)
  have generated: "construct H l (Finite_Whole R) (Finite_Whole C) rows\<noteq>None"
    by (simp only: domain record_ready)
  show "record_native_replay_with construct H l rows E pu pr au ar root R\<noteq>None"
    using generated by (simp add: record_native_replay_with_def ready quoted split: option.splits)
qed

end

corollary original_replay_certification_instance:
  "finite_record_native_replay H l rows E pu pr au ar root R=Some (A,u,G,J,C) \<Longrightarrow>
    certified_base_cause_at (decode_finite_environment A) u [] (decode_finite_generation G)
      (decode_finite_environment E) root (decode_finite_object R)"
  using original_generation_backend.record_replay_certified
  by (simp only: original_record_replay_instance id_apply)

text \<open>
  The actual replay guard and judgment quotation are independent of the state
  backend. A successful builder result retains its whole state, generation and
  quote. Complete optional projection composes without deleting failed paths.
  Certification and material preservation instantiate one semantic backend
  contract. The original operation is an equal instance; another backend must
  prove that same contract before its results acquire these conclusions.
\<close>

end
