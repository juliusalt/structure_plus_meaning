theory Factor_Digit_Generation_Replay
  imports RRA_Digit_Generation_Backend Factor_Parametric_Generation_Replay
begin

definition digit_record_native_replay where
  "digit_record_native_replay=record_native_replay_with digit_construct_generation"

lemmas digit_record_native_replay_result =
  record_native_replay_with_result[where construct=digit_construct_generation,
    folded digit_record_native_replay_def]

lemmas digit_record_native_replay_certified =
  generation_record_backend.record_replay_certified
    [OF digit_generation_backend.generation_record_backend_axioms, folded digit_record_native_replay_def]

lemmas digit_record_native_replay_material =
  generation_record_backend.record_replay_preserves_material
    [OF digit_generation_backend.generation_record_backend_axioms, folded digit_record_native_replay_def]

lemmas digit_record_native_replay_domain =
  generation_record_backend.record_replay_domain
    [OF digit_generation_backend.generation_record_backend_axioms, folded digit_record_native_replay_def]

theorem digit_record_native_replay_projection:
  "map_option (\<lambda>(following,u,G,J,C). (digit_allocated_view following,u,G,J,C))
      (digit_record_native_replay q l rows E pu pr au ar root R)=
    record_native_replay_with finite_construct_bounded_generation
      (digit_allocated_view q) l rows E pu pr au ar root R"
  unfolding digit_record_native_replay_def
  by (rule record_native_replay_with_projection[where project=digit_allocated_view
    and original=finite_construct_bounded_generation]; rule digit_construct_generation_projection)

export_code digit_record_native_replay checking SML

text \<open>
  Replay recording now has an actual digit constructor instance. The full
  optional state, generation, judgment environment and quotation equal the
  independently established bounded replay operation. Original generation
  certification and material preservation instantiate the backend proof.
  Allocation choices can change uses and material while preserving those
  original meanings; equality to the old allocator is not assumed. Policy,
  history admission and physical cost require their own actual contracts.
\<close>

end
