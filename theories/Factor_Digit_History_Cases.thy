theory Factor_Digit_History_Cases
  imports Factor_Digit_History_Methods History_Input_Transitions Factor_Required_History_Cases
begin

definition digit_history_source_index :: "nat\<Rightarrow>nat" where
  "digit_history_source_index w=(if w<12 then w else 0)"

definition digit_history_chain_length :: "nat\<Rightarrow>nat" where
  "digit_history_chain_length w=(if w<12 then 0 else w-11)"

definition digit_history_case where
  "digit_history_case w=fimage (\<lambda>(key,input). (key,
    history_input_chain digit_history_apply (\<lambda>q. digit_history_ledger (raw_digit_required_history q))
      (digit_history_chain_length w) (Option.bind input digit_history_initial_subject)))
        (required_history_case (digit_history_source_index w))"

definition bounded_history_case where
  "bounded_history_case w=fimage (\<lambda>(key,input). (key,
    history_input_chain bounded_history_apply (\<lambda>state. required_history_members (snd state))
      (digit_history_chain_length w) (Option.bind input bounded_history_initial_subject)))
        (required_history_case (digit_history_source_index w))"

lemma digit_history_initial_bind_projection:
  "map_option (history_subject_map digit_history_base) (Option.bind input digit_history_initial_subject)=
    Option.bind input bounded_history_initial_subject"
proof (rule optional_bind_projection[where project=id])
  show "map_option id input=input" by (cases input) simp_all
next
  fix q
  show "map_option (history_subject_map digit_history_base) (digit_history_initial_subject q)=
    bounded_history_initial_subject (id q)"
    by (simp only: id_apply digit_history_initial_subject_projection)
qed

theorem digit_history_case_base_projection:
  "fimage (\<lambda>(key,input). (key,map_option (history_subject_map digit_history_base) input))
      (digit_history_case w)=bounded_history_case w"
  by (simp add: digit_history_case_def bounded_history_case_def fimage_fimage comp_def case_prod_unfold
    history_input_chain_projection[where project=digit_history_base and step=digit_history_apply
      and original_step=bounded_history_apply and read_members="\<lambda>q. digit_history_ledger (raw_digit_required_history q)"
      and original_members="\<lambda>state. required_history_members (snd state)",
      OF digit_history_apply_base digit_history_members_base]
    digit_history_initial_bind_projection)

definition digit_history_subject_view where
  "digit_history_subject_view X=(digit_history_view (fst X),snd X)"

definition bounded_history_subject_view where
  "bounded_history_subject_view X=(bounded_history_result_view (fst X),snd X)"

lemma digit_history_subject_view_exact:
  "digit_history_subject_view X=bounded_history_subject_view (history_subject_map digit_history_base X)"
proof -
  have cache: "history_member_index_exact (digit_history_index (raw_digit_required_history (fst X)))
    (digit_history_ledger (raw_digit_required_history (fst X)))"
    using digit_required_history_valid[of "fst X"] by (simp only: digit_required_history_valid_def; blast)
  show ?thesis by (simp only: digit_history_subject_view_def bounded_history_subject_view_def history_subject_map_def
    fst_conv snd_conv digit_history_view_def digit_history_base_def digit_history_state_view_cache[OF cache])
qed

definition digit_history_source_equal ::
  "(required_history_certificate option\<times>digit_history_subject option) fset\<Rightarrow>
    (required_history_certificate option\<times>bounded_history_subject option) fset\<Rightarrow>bool" where
  "digit_history_source_equal subjects original=(fimage (\<lambda>(key,input).
    (key,map_option digit_history_subject_view input)) subjects=
    fimage (\<lambda>(key,input). (key,map_option bounded_history_subject_view input)) original)"

theorem digit_history_case_projection:
  "digit_history_source_equal (digit_history_case w) (bounded_history_case w)"
proof -
  have view: "digit_history_subject_view=bounded_history_subject_view \<circ> history_subject_map digit_history_base"
    by (rule ext; simp only: comp_apply digit_history_subject_view_exact)
  show ?thesis
    by (simp only: digit_history_source_equal_def digit_history_case_base_projection[symmetric];
        simp add: fimage_fimage option.map_comp comp_def case_prod_unfold view)
qed

definition digit_history_indices :: "nat list" where
  "digit_history_indices=[0..<16]"

text \<open>
  All twelve original required-history inputs remain complete sources. Four
  further cases apply one, two, three and four actual digit history steps,
  carrying each returned state and full ordered ledger into the next request.
  Complete input correspondence retains every original field, actual bound and
  cache relation. Original non-reachable invariant fixtures keep that status;
  reading retained material does not replace ledger admission.
\<close>

end
