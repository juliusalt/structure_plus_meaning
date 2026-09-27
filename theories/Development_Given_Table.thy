theory Development_Given_Table
  imports Development_Installed_Presentations Development_Native_State Factor_Resolution_Checks
begin

text \<open>
  GT5 of DECISIONS.md, task 495's entry, the section "The given's calls are decided once": the given's table as a
  notion. Its calls are a function of the given's value, computed here from @{const given_environment} and
  @{const development_given_value} through their presenters, never supplied beside them, in the order the production
  takes them (bottom-up: 11 at the given's artifacts by ascending size, 7 and 12 at each with itself, the environment
  admission's list traversals from the shortest suffix up and 26 at the environment value, 156 at the site value, the
  package's readers 79, 77, 80, 82 and 83 at the given's package, the guard's four sockets and 526 at (g, g)). Which
  calls a judgment meets is observed by GT6 and R7, not proved here: a call the table lacks costs its derivation, never
  a verdict. The table's validity is GT6's retained outcome and enters as a premise; it is carried by GT2c's transfers
  (@{text Factor_Resolution_Checks}): its calls true at every numbered program agreeing with the rooted readers on their
  callee closure, and, relocated by an installation's placement, at the installed presentation. No second production
  and no second check (decision 5). Nothing is evaluated here.
\<close>

section \<open>The given's data, read through its presenters\<close>

text \<open>A self-contained term's finite value: the presenters of the given's values are payload-and-pair data.\<close>

definition given_table_data :: "factor_term \<Rightarrow> finite_factor_term" where
  "given_table_data t=the (finite_self_contained_term t)"

definition given_artifact_rows :: "(local_address option\<times>artifact_value_rows) list" where
  "given_artifact_rows=finite_environment_artifact_rows given_environment"

definition given_binding_rows :: "((local_address option\<times>local_address)\<times>local_address option) list" where
  "given_binding_rows=sorted_list_of_fset (finite_environment_bindings given_environment)"

text \<open>R, the given's artifact row count, and B, its binding count.\<close>

definition given_row_count :: nat where
  "given_row_count=length given_artifact_rows"

definition given_binding_count :: nat where
  "given_binding_count=length given_binding_rows"

definition given_rows_term :: factor_term where
  "given_rows_term=data_list_term (map environment_artifact_rows_term given_artifact_rows)"

definition given_bindings_term :: factor_term where
  "given_bindings_term=data_list_term (map binding_data given_binding_rows)"

lemma given_environment_presented:
  "finite_environment_value given_environment=given_table_data (Pair_Term given_rows_term given_bindings_term)"
  by (simp add: finite_environment_value_def finite_environment_term_def given_table_data_def given_rows_term_def
    given_bindings_term_def given_artifact_rows_def given_binding_rows_def)

text \<open>The given's artifacts, each once, by ascending number of addresses: the fit is tested at the smallest first.\<close>

definition given_artifacts :: "artifact_value_rows list" where
  "given_artifacts=sort_key (\<lambda>q. length (fst q)) (remdups (map snd given_artifact_rows))"

definition given_artifact_value :: "artifact_value_rows \<Rightarrow> finite_factor_term" where
  "given_artifact_value q=given_table_data (artifact_rows_term q)"

lemma given_artifact_value_finite: "given_artifact_value (finite_artifact_rows C)=finite_artifact_value C"
  by (simp add: given_artifact_value_def given_table_data_def finite_artifact_value_def)

section \<open>The families of the given's calls\<close>

definition given_artifact_calls :: "(nat\<times>finite_factor_term) list" where
  "given_artifact_calls=map (\<lambda>q. (11,given_artifact_value q)) given_artifacts"

definition given_identity_calls :: "(nat\<times>finite_factor_term) list" where
  "given_identity_calls=concat (map (\<lambda>q. [(7,Finite_Pair (given_artifact_value q) (given_artifact_value q)),
    (12,Finite_Pair (given_artifact_value q) (given_artifact_value q))]) given_artifacts)"

text \<open>
  26's clause calls 23 and 21 at the artifact rows and 25 at the rows paired with the bindings and 21 at the bindings;
  the list traversals call 23 and 21 at every suffix of the rows and 22 at each row, 25 at the rows paired with every
  suffix of the bindings, 24 at the rows paired with each binding and 21 at every suffix of the bindings. The shortest
  suffix comes first, 26 last.
\<close>

definition given_environment_calls :: "(nat\<times>finite_factor_term) list" where
  "given_environment_calls=
    concat (map (\<lambda>i. let s=drop i given_artifact_rows in
        (if s=[] then [] else [(22,given_table_data (environment_artifact_rows_term (hd s)))]) @
        [(23,given_table_data (data_list_term (map environment_artifact_rows_term s))),
         (21,given_table_data (data_list_term (map environment_artifact_rows_term s)))])
      (rev [0..<Suc given_row_count])) @
    concat (map (\<lambda>i. let s=drop i given_binding_rows in
        (if s=[] then [] else [(24,given_table_data (Pair_Term given_rows_term (binding_data (hd s))))]) @
        [(25,given_table_data (Pair_Term given_rows_term (data_list_term (map binding_data s)))),
         (21,given_table_data (data_list_term (map binding_data s)))])
      (rev [0..<Suc given_binding_count])) @
    [(26,finite_environment_value given_environment)]"

text \<open>
  The given's package, read from its site by the native package reader: 79 at its root family, 77 at its roots (the
  bound at the given handed in), 80 at its site, 82 at each of its definition edges and 83 at each of its definitions,
  the calls 83's two clauses make.
\<close>

definition given_package_calls :: "(nat\<times>finite_factor_term) list" where
  "given_package_calls=(case finite_native_source given_environment given_use [] of None \<Rightarrow> []
    | Some P \<Rightarrow> let e=finite_environment_term given_environment; u=use_data_term given_use; r=Payload_Term [];
        roots=data_list_term (map definition_site_value given_roots) in
      [(79,given_table_data (citation_observation_argument e u r roots)),
       (77,given_table_data (Pair_Term e roots)),
       (80,given_table_data (source_root_argument e u r))] @
      map (\<lambda>(d,f). (82,given_table_data (Pair_Term e (Pair_Term (definition_site_value d) (definition_site_value f)))))
        (sorted_list_of_fset (finite_dependency_edges P)) @
      map (\<lambda>d. (83,given_table_data (package_subject_argument e u r (definition_site_value d))))
        (sorted_list_of_fset (finite_system_definitions P)))"

text \<open>The guard's four sockets, by socket, and 526, each at the pair (g, g): the guard hands its whole subject to each.\<close>

definition given_guard_calls :: "(nat\<times>finite_factor_term) list" where
  "given_guard_calls=map (\<lambda>(s,d). (d,Finite_Pair development_given_value development_given_value))
      (sorted_list_of_set first_problem_requirements) @
    [(526,Finite_Pair development_given_value development_given_value)]"

text \<open>
  The readers' part, at the sites of the given's readers, and the table's calls. The guard's sockets 520, 521 and 525
  and 526 are the asked program's, not the readers': a table valid at the rooted readers holds none of them, and those
  entries are certified at the asked program.
\<close>

definition given_reader_calls :: "(nat\<times>finite_factor_term) list" where
  "given_reader_calls=given_artifact_calls @ given_identity_calls @ given_environment_calls @
    [(156,development_given_value)] @ given_package_calls"

definition given_table_calls :: "(nat\<times>finite_factor_term) list" where
  "given_table_calls=given_reader_calls @ given_guard_calls"

section \<open>The table at the numbered programs\<close>

text \<open>A table whose calls are true at a program calls only its definitions.\<close>

lemma finite_table_true_sites:
  assumes true: "finite_table_true P \<Theta>"
  shows "fst ` finite_table_calls \<Theta>\<subseteq>system_definitions (decode_finite_system P)"
proof
  fix d assume "d\<in>fst ` finite_table_calls \<Theta>"
  then obtain t c where "resolution_table_lookup \<Theta> (d,t)=Some c" by (auto simp: finite_table_calls_def)
  then have "(d,decode_finite_term t)\<in>positive_meaning (decode_finite_system P)"
    using true by (auto simp: finite_table_true_def)
  then show "d\<in>system_definitions (decode_finite_system P)" by (rule positive_meaning_site)
qed

lemma given_rooted_closed:
  "system_dependency_closed given_rooted_readers_system (system_definitions given_rooted_readers_system)"
  using systems_agree_on_intersection_closed[OF given_rooted_readers_formed given_rooted_readers_formed]
  by (simp add: systems_agree_on_def)


text \<open>
  The table valid at the rooted readers has its calls true at every numbered program agreeing with them on its calls'
  sites and their callee closure, and there the certified table of its calls is valid (GT2c's agreement transfer).
\<close>

theorem given_table_true_agreement:
  assumes valid: "finite_table_valid finite_rooted_given_readers \<Theta>"
    and Qf: "finite_system_formed Q"
    and agree: "systems_agree_on given_rooted_readers_system (decode_finite_system Q)
      (system_definition_closure given_rooted_readers_system (fst ` finite_table_calls \<Theta>))"
  shows "finite_table_true Q \<Theta>" "finite_table_valid Q (finite_table_certified Q \<Theta>)"
    "finite_table_calls (finite_table_certified Q \<Theta>)=finite_table_calls \<Theta>"
proof -
  have qf: "schema_system_formed (decode_finite_system Q)" using Qf by (simp only: finite_system_formed_correct)
  have sites: "\<And>d t. (d,t)\<in>finite_table_calls \<Theta> \<Longrightarrow>
      d\<in>system_definition_closure given_rooted_readers_system (fst ` finite_table_calls \<Theta>)"
    by (rule subsetD[OF system_definition_closure_roots]) force
  note r=finite_table_valid_agreement[OF valid, unfolded finite_rooted_given_readers_exact,
    OF given_rooted_readers_formed qf agree system_definition_closure_closed sites]
  show "finite_table_true Q \<Theta>" by (rule r(1))
  show "finite_table_valid Q (finite_table_certified Q \<Theta>)" by (rule r(2))
  show "finite_table_calls (finite_table_certified Q \<Theta>)=finite_table_calls \<Theta>" by (rule r(3))
qed

section \<open>The table at a program extending the given's readers, and at its installation\<close>

text \<open>
  A table's calls relocated by a placement: each call's site mapped, its term unchanged.
\<close>

definition relocated_given_calls :: "(nat \<Rightarrow> 'd) \<Rightarrow> (nat\<times>finite_factor_term) list \<Rightarrow> ('d\<times>finite_factor_term) list" where
  "relocated_given_calls g cs=map (\<lambda>(d,t). (g d,t)) cs"

lemma relocated_given_calls_relocates:
  assumes "finite_table_calls \<Theta>=set cs" and "finite_table_calls \<Theta>'=set (relocated_given_calls g cs)"
  shows "finite_table_relocates g \<Theta> \<Theta>'"
  using assms by (simp add: finite_table_relocates_def relocated_given_calls_def)

context given_readers_extension
begin

text \<open>The numbered table at the program: it agrees with the rooted readers on all their definitions.\<close>

theorem readers_table_true:
  assumes valid: "finite_table_valid finite_rooted_given_readers \<Theta>"
  shows "finite_table_true Q \<Theta>" "finite_table_valid Q (finite_table_certified Q \<Theta>)"
    "finite_table_calls (finite_table_certified Q \<Theta>)=finite_table_calls \<Theta>"
proof -
  have sites: "\<And>d t. (d,t)\<in>finite_table_calls \<Theta> \<Longrightarrow> d\<in>system_definitions given_rooted_readers_system"
    using finite_table_true_sites[OF finite_table_valid_true[OF valid]]
    by (force simp: finite_rooted_given_readers_exact)
  note r=finite_table_valid_agreement[OF valid, unfolded finite_rooted_given_readers_exact,
    OF given_rooted_readers_formed target_formed agreement given_rooted_closed sites]
  show "finite_table_true Q \<Theta>" by (rule r(1))
  show "finite_table_valid Q (finite_table_certified Q \<Theta>)" by (rule r(2))
  show "finite_table_calls (finite_table_certified Q \<Theta>)=finite_table_calls \<Theta>" by (rule r(3))
qed

text \<open>
  A table whose calls are true at the program, relocated by the installation's placement, has its calls true at the
  placed program and at the installed presentation the native package reader returns, an alpha variant of it (V3's
  @{text installed_presentation_variant}), at any table of those calls there: GT2c's relocation, with no second
  production and no second check.
\<close>

theorem installed_table_true_at:
  assumes true: "finite_table_true Q \<Theta>" and relocates: "finite_table_relocates installed_placement \<Theta> \<Theta>'"
    and calls: "finite_table_calls \<Theta>''=finite_table_calls \<Theta>'"
  shows "finite_table_true (finite_rename_system installed_placement Q) \<Theta>'"
    "finite_table_true installed_presentation \<Theta>''"
proof -
  note r=install.mapped_installed_table_true[folded installed_placement_def, OF installed_built
    installed_presentation_read true relocates finite_table_true_sites[OF true] calls]
  show "finite_table_true (finite_rename_system installed_placement Q) \<Theta>'" by (rule r(1))
  show "finite_table_true installed_presentation \<Theta>''" by (rule r(2))
qed

corollary installed_given_table_true:
  assumes valid: "finite_table_valid finite_rooted_given_readers \<Theta>"
    and relocates: "finite_table_relocates installed_placement \<Theta> \<Theta>'"
    and calls: "finite_table_calls \<Theta>''=finite_table_calls \<Theta>'"
  shows "finite_table_true (finite_rename_system installed_placement Q) \<Theta>'"
    "finite_table_true installed_presentation \<Theta>''"
  by (rule installed_table_true_at[OF readers_table_true(1)[OF valid] relocates calls])+

end

section \<open>The asked program and the first request's program\<close>

text \<open>
  The instances at the asked relation's program (@{const asked_program_system}, presented by
  @{const finite_asked_program}) and the first request's (@{const first_request_program_system}), and at their
  installations. The guard's part, certified at the asked program, reaches the asked installation through
  @{text asked_installed_table_true_at} from its validity there (@{thm [source] finite_table_valid_true}).
\<close>

lemmas asked_readers_table_true=given_readers_extension.readers_table_true[OF asked_extension.readers_extension]
lemmas asked_installed_table_true_at=given_readers_extension.installed_table_true_at[OF asked_extension.readers_extension,
  folded asked_installed_presentation_def]
lemmas asked_installed_given_table_true=
  given_readers_extension.installed_given_table_true[OF asked_extension.readers_extension,
  folded asked_installed_presentation_def]

lemmas first_request_readers_table_true=
  given_readers_extension.readers_table_true[OF first_request_extension.readers_extension]
lemmas first_request_installed_table_true_at=
  given_readers_extension.installed_table_true_at[OF first_request_extension.readers_extension,
  folded first_request_installed_presentation_def]
lemmas first_request_installed_given_table_true=
  given_readers_extension.installed_given_table_true[OF first_request_extension.readers_extension,
  folded first_request_installed_presentation_def]

end
