theory Factor_Committing_Query_Parameters
  imports Factor_Varied_Narrowed_Transfer Factor_Least_Witness_Registrations Factor_Resolution_Modes
    Factor_Framed_Commitment_Index
begin

section \<open>A committing instance of W2's query parameters\<close>

text \<open>
  VK2 (task 918's decision 5). A committing instance of W5's query parameters over a program P with a produced record D
  and its frames \<Phi>: the ground part is the record's narrowed commitment at a table, with the moded priority at
  modes M, as the check forms use them; the lifted part is the record and frames varied along the query program's left
  injection (@{const finite_query_program}), its commitment the root-kept restriction (@{const finite_root_kept}) of the
  varied record's narrowed commitment, the moded priority reading that commitment, at a table of its own. The
  restriction is chosen at the query search alone: at every ground root it is the narrowed commitment
  (@{thm [source] finite_root_kept_ground_in}), so no verdict or check form reads it.
\<close>

text \<open>
  The committing instance's tests are the narrowed commitment's, at the ground and lifted parts alike; their code reads
  the framed test at a goal's raising socket through the index @{text Factor_Framed_Commitment_Index} builds once per
  record and frames (@{thm [source] finite_framed_commitment_indexed}, @{thm [source] finite_narrowed_commitment_under}),
  so the moded priority's framed test at a goal's parent focus does not run over every socket view and frame choice
  (task 966: the edge query of 77's registration at n=40, 3.76 s without that code, 0.17 s with it).
\<close>

definition committing_parameters ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'r) produced_declarations \<Rightarrow>
      ('a,'s,'d) resolution_frames \<Rightarrow> 'd resolution_modes \<Rightarrow> ('a,'s,'d,'c) resolution_table \<Rightarrow>
      ('a,'s,'d,'c) resolution_parameters" where
  "committing_parameters P m D \<Phi> M \<Theta> = \<lparr>parameter_table=\<Theta>,
    parameter_priority=finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) (resolution_declarations.truncate D) M,
    parameter_commitment=finite_narrowed_commitment P m D \<Phi>\<rparr>"

definition lifted_committing_parameters ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'r) produced_declarations \<Rightarrow>
      ('a,'s,'d) resolution_frames \<Rightarrow> 'd resolution_modes \<Rightarrow> ('a+'v,'s,'d,'c) resolution_table \<Rightarrow>
      ('a+'v,'s,'d,'c) resolution_parameters" where
  "lifted_committing_parameters P m D \<Phi> M \<Theta> = (let N = (finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system);
      K = finite_root_kept (finite_narrowed_commitment N m (produced_declarations_varied P N D) (frames_varied P N \<Phi>)) in
    \<lparr>parameter_table=\<Theta>,
     parameter_priority=finite_moded_priority K (resolution_declarations.truncate (produced_declarations_varied P N D)) M,
     parameter_commitment=K\<rparr>)"

definition committing_query_parameters ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'r) produced_declarations \<Rightarrow>
      ('a,'s,'d) resolution_frames \<Rightarrow> 'd resolution_modes \<Rightarrow> ('a,'s,'d,'c) resolution_table \<Rightarrow>
      ('a+'v,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s,'d,'c,'v) query_parameters" where
  "committing_query_parameters P m D \<Phi> M \<Theta> \<Theta>' =
    (committing_parameters P m D \<Phi> M \<Theta>, lifted_committing_parameters P m D \<Phi> M \<Theta>')"

lemma committing_query_parameters_fields:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  defines "N \<equiv> finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system"
  shows "parameter_table (fst (committing_query_parameters P m D \<Phi> M \<Theta> \<Theta>' :: ('a,'s,'d,'c,'v) query_parameters)) = \<Theta>"
    "parameter_commitment (fst (committing_query_parameters P m D \<Phi> M \<Theta> \<Theta>' :: ('a,'s,'d,'c,'v) query_parameters)) =
      finite_narrowed_commitment P m D \<Phi>"
    "parameter_table (snd (committing_query_parameters P m D \<Phi> M \<Theta> \<Theta>' :: ('a,'s,'d,'c,'v) query_parameters)) = \<Theta>'"
    "parameter_commitment (snd (committing_query_parameters P m D \<Phi> M \<Theta> \<Theta>' :: ('a,'s,'d,'c,'v) query_parameters)) =
      finite_root_kept (finite_narrowed_commitment N m (produced_declarations_varied P N D) (frames_varied P N \<Phi>))"
  by (simp_all add: committing_query_parameters_def committing_parameters_def lifted_committing_parameters_def
    Let_def N_def)

section \<open>W5's named premise at a committing instance\<close>

text \<open>
  Where the record, carried along the query program's left injection, stays discharged there
  (@{text varied_narrowed_record}), GT2b's valued exchange of the carried record's narrowed commitment holds at the
  query program at any true table and formed selection; its root-kept restriction keeps it
  (@{thm [source] finite_root_kept_exchanges_valued_by_in}) and is apart at the top focus
  (@{thm [source] finite_root_kept_apart}), so the query search keeps the root value of every true instance
  (@{thm [source] finite_query_search_keeps_apart_in}). The ground part is exact at a true table from GT2b's composed
  forms (@{thm [source] finite_narrowed_exact_premises_by_in}).
\<close>

theorem committing_query_search_keeps:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and D :: "('a,'s,'d,'r) produced_declarations"
  assumes varied_record: "varied_narrowed_record P (finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system) D corr \<Phi> m m"
    and true': "finite_table_true (finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system) \<Theta>'"
  shows "finite_query_search_keeps (committing_query_parameters P m D \<Phi> M \<Theta> \<Theta>' :: ('a,'s,'d,'c,'v) query_parameters) P n"
proof -
  let ?N = "finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system"
  let ?\<Xi> = "committing_query_parameters P m D \<Phi> M \<Theta> \<Theta>' :: ('a,'s,'d,'c,'v) query_parameters"
  let ?sel = "finite_parameters_select (snd ?\<Xi>) ?N"
  interpret carried: varied_narrowed_record P ?N D corr \<Phi> m m by (rule varied_record)
  have formed: "finite_selection_formed no_witness_construction ?N ?sel"
    unfolding finite_parameters_select_def by (rule finite_resolution_select_formed_in)
  have narrowed: "finite_commitment_exchanges_valued_by_in \<Theta>' ?sel
      (\<lambda>z. snd z |\<notin>| finite_program_variables ?N) no_witness_construction
      (finite_narrowed_commitment ?N m (produced_declarations_varied P ?N D) (frames_varied P ?N \<Phi>)) ?N"
    by (rule finite_narrowed_commitment_exchanges_in[OF no_witness_construction_formed formed true'
      carried.discharged_varied carried.frames_varied_at carried.productions_varied_at carried.declared'
      finite_registrations_premise_only_none])
  have valued: "finite_commitment_exchanges_valued_by_in (parameter_table (snd ?\<Xi>)) ?sel
      (\<lambda>z. snd z |\<notin>| finite_program_variables ?N) no_witness_construction (parameter_commitment (snd ?\<Xi>)) ?N"
    unfolding committing_query_parameters_fields by (rule finite_root_kept_exchanges_valued_by_in[OF narrowed])
  have apart: "finite_commits_apart (parameter_commitment (snd ?\<Xi>))"
    unfolding committing_query_parameters_fields by (rule finite_root_kept_apart)
  show ?thesis by (rule finite_query_search_keeps_apart_in[OF valued apart])
qed

theorem committing_query_exact:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and D :: "('a,'s,'d,'r) produced_declarations"
  assumes varied_record: "varied_narrowed_record P (finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system) D corr \<Phi> m m"
    and declared: "narrowed_productions_declared D"
    and true: "finite_table_true P \<Theta>"
    and true': "finite_table_true (finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system) \<Theta>'"
  shows "finite_query_exact (committing_query_parameters P m D \<Phi> M \<Theta> \<Theta>' :: ('a,'s,'d,'c,'v) query_parameters) P n"
proof -
  let ?\<Xi> = "committing_query_parameters P m D \<Phi> M \<Theta> \<Theta>' :: ('a,'s,'d,'c,'v) query_parameters"
  let ?sel = "finite_parameters_select (fst ?\<Xi>) P"
  interpret carried: varied_narrowed_record P "finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system"
    D corr \<Phi> m m by (rule varied_record)
  have formed: "finite_selection_formed no_witness_construction P ?sel"
    unfolding finite_parameters_select_def by (rule finite_resolution_select_formed_in)
  have ground: "finite_committed_exact_premises_in (parameter_table (fst ?\<Xi>))
      (\<lambda>d t s. resolution_invariant_in \<Theta> P d t s \<and> resolution_registrations_held no_witness_construction s) ?sel
      no_witness_construction (parameter_commitment (fst ?\<Xi>)) P"
    unfolding committing_query_parameters_fields
    by (rule finite_narrowed_exact_premises_by_in[OF no_witness_construction_formed formed true carried.discharged
      carried.frames carried.productions declared finite_registrations_premise_only_none finite_construction_lifts_none_in])
  show ?thesis
    unfolding finite_query_exact_def
    using finite_parameters_refutes_exact_committed[OF ground] committing_query_search_keeps[OF varied_record true'] by blast
qed

end
