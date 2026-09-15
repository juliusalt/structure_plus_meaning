theory RRA_Generation_Record_Backends
  imports RRA_Complete_Environment_Agreement RRA_Finite_Generation_Reference_Construction
begin

locale generation_record_backend =
  fixes read_environment :: "'state\<Rightarrow>local_address option finite_artifact_environment"
    and construct :: "'state\<Rightarrow>finite_exact_target\<Rightarrow>finite_exact_target\<Rightarrow>finite_exact_target\<Rightarrow>
      (local_address option definition_site\<times>finite_generation) list\<Rightarrow>
      ('state\<times>local_address option\<times>finite_generation) option"
  assumes domain: "\<And>q l p c rows. construct q l p c rows\<noteq>None \<longleftrightarrow>
      finite_generation_record_ready (read_environment q) l p c rows"
    and core: "\<And>q l p c rows following u G. construct q l p c rows=Some (following,u,G) \<Longrightarrow>
      G=finite_generation_record_core l p c rows"
    and generation: "\<And>q l p c rows following u G. construct q l p c rows=Some (following,u,G) \<Longrightarrow>
      finite_check_generation G (read_environment following) u []"
    and agreement: "\<And>q l p c rows following u G. construct q l p c rows=Some (following,u,G) \<Longrightarrow>
      finite_environment_agrees_on (read_environment q) (read_environment following)
        (finite_environment_uses (read_environment q))"
    and references: "\<And>q l p c rows following u G. construct q l p c rows=Some (following,u,G) \<Longrightarrow>
      finite_generation_predecessor_references (read_environment following) u [] l p c=fset_of_list (map fst rows)"
begin

lemma result_ready:
  "construct q l p c rows=Some (following,u,G) \<Longrightarrow>
    finite_generation_record_ready (read_environment q) l p c rows"
  using domain by fastforce

lemma original_formed:
  "construct q l p c rows=Some (following,u,G) \<Longrightarrow> finite_environment_formed (read_environment q)"
  using result_ready by (simp only: finite_generation_record_ready_def; blast)

lemma result_formed:
  assumes result: "construct q l p c rows=Some (following,u,G)"
  shows "finite_environment_formed (read_environment following)"
  using generation_at_environment_formed[OF generation[OF result, unfolded finite_check_generation_exact]]
  by (simp only: finite_environment_formed_correct)

lemma result_included:
  "construct q l p c rows=Some (following,u,G) \<Longrightarrow>
    finite_environment_included (read_environment q) (read_environment following)"
  by (rule finite_environment_agreement_included[OF original_formed agreement])

end

interpretation original_generation_backend: generation_record_backend id finite_construct_generation_record
proof (unfold_locales)
  show "finite_construct_generation_record E l p c rows\<noteq>None \<longleftrightarrow>
    finite_generation_record_ready (id E) l p c rows" for E l p c rows
    using finite_construct_generation_record_domain[of E l p c rows]
    by (cases "finite_construct_generation_record E l p c rows") auto
  show "finite_construct_generation_record E l p c rows=Some (F,u,G) \<Longrightarrow>
    G=finite_generation_record_core l p c rows" for E l p c rows F u G
    by (rule finite_construct_generation_record_correct(2))
  show "finite_construct_generation_record E l p c rows=Some (F,u,G) \<Longrightarrow>
    finite_check_generation G (id F) u []" for E l p c rows F u G
    by (simp only: id_apply; rule finite_construct_generation_record_correct(6))
  show "finite_construct_generation_record E l p c rows=Some (F,u,G) \<Longrightarrow>
    finite_environment_agrees_on (id E) (id F) (finite_environment_uses (id E))" for E l p c rows F u G
    by (simp only: id_apply; rule finite_construct_generation_record_correct(5))
  show "finite_construct_generation_record E l p c rows=Some (F,u,G) \<Longrightarrow>
    finite_generation_predecessor_references (id F) u [] l p c=fset_of_list (map fst rows)" for E l p c rows F u G
    by (simp only: id_apply; rule finite_construct_generation_record_original_references)
qed

text \<open>
  The backend boundary retains actual readiness, complete generation identity,
  its reading, every old artifact and binding, and every original predecessor
  site. Source and result formation and original inclusion are derived. The
  state itself remains in the output; this semantic contract does not prescribe
  one allocation policy or assert equality of different complete operations.
\<close>

end
