theory Factor_Digit_Replay_Variants
  imports Factor_Digit_Replay_Reports
begin

definition digit_replay_quote_variant where
  "digit_replay_quote_variant (m::nat) q l rows X=(case X of (E,pu,pr,au,ar,root,R) \<Rightarrow>
    if m=3 \<or> finite_literal_replay_ready E pu pr au ar root R then
      (case finite_native_judgment_quote E pu pr au ar of None \<Rightarrow> None
      | Some (J,C) \<Rightarrow> Option.bind
          (if m=4 then Some (finite_payload_syntax [63])
           else if m=5 then finite_data_syntax (finite_judgment_term E pu pr au ar)
           else if m=6 then finite_data_syntax (reversed_judgment_term J pu pr au ar)
           else Some C)
          (\<lambda>D. map_option (\<lambda>(A,u,G). (A,u,G,J,D))
            (digit_construct_generation q l (Finite_Whole R) (Finite_Whole D) rows)))
    else None)"

definition digit_replay_variant_key :: "nat\<Rightarrow>nat" where
  "digit_replay_variant_key m=(if m\<in>{1,2,3,4,5,6} then m else 0)"

definition digit_replay_variant where
  "digit_replay_variant (m::nat) X=(if m=1 then digit_replay_reference X
    else if m=0 then digit_replay_typed X else
    case X of (input,l,rows,replay) \<Rightarrow> finite_prepared_results (\<lambda>q.
      if m=2 then map_option (\<lambda>(A,u,G,J,C).
        ((Suc (Suc (fst (digit_allocated_view q))),A),u,G,J,C))
          (record_replay_subject_with finite_construct_generation_record (snd (digit_allocated_view q)) l rows replay)
      else map_option (\<lambda>(following,u,G,J,C). (digit_allocated_view following,u,G,J,C))
        (digit_replay_quote_variant m q l rows replay)) input)"

definition digit_replay_changed_result :: "nat\<Rightarrow>digit_replay_subject\<Rightarrow>
    (bounded_replay_value)\<Rightarrow>bounded_replay_value" where
  "digit_replay_changed_result m X result=(case X of (input,l,rows,E,pu,pr,au,ar,root,R) \<Rightarrow>
    case input of None \<Rightarrow> result | Some q \<Rightarrow>
    map_option (\<lambda>((n,A),u,G,J,C).
      ((if m=7 then fst (digit_allocated_view q) else n,
        if m=8 then A\<lparr>finite_environment_bindings:={||}\<rparr>
        else if m=15 then snd (digit_allocated_view q) else A),
       if m=9 then None else u,G,if m=10 then E else J,
       if m=11 then finite_payload_syntax [63] else C)) result)"

definition digit_replay_mutation where
  "digit_replay_mutation (m::nat) X results=(if m=13 then {||}
    else if m=14 \<and> fst X=None then {|None|}
    else if m=12 then fimage (\<lambda>result. None) results
    else if m\<in>{7,8,9,10,11,15} then fimage (digit_replay_changed_result m X) results
    else results)"

definition digit_replay_method where
  "digit_replay_method m X=digit_replay_mutation m X (digit_replay_variant (digit_replay_variant_key m) X)"

theorem digit_replay_correct_methods:
  "m\<in>{0,1} \<Longrightarrow> digit_replay_method m X=digit_replay_reference X"
  by (auto simp: digit_replay_method_def digit_replay_mutation_def digit_replay_variant_key_def
    digit_replay_variant_def digit_replay_typed_exact)

text \<open>
  Actual alternate constructors omit replay admission or construct generations
  from a dummy, enlarged or reordered cause quotation. The old allocator remains
  a complete alternate operation. Other controls change returned counters,
  material, uses, judgment environments or quotation values, or remove result
  availability. The original certified-cause report determines which changes
  preserve cause meaning independently of complete operation equality.
\<close>

end
