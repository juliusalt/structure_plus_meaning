theory Development_First_Problem_Additions_Fixtures
  imports Development_First_Problem Development_Given_Execution_Fixtures
begin

text \<open>
  The fixtures of the controls of the asked relation over additions (task 938, AX3b), in a theory that evaluates
  nothing and imports no refinement collection, so that the controls theories import it and none imports another.
  A small given: one definition, a fact stating the empty payload, installed over the empty selection, its
  package at the installed use. Its extensions are installed over it by the mapped extension, as every extension of
  a package is (@{const finite_extend_mapped_native}); a candidate is presented by its additions over the given,
  the rows the extension adds and the candidate's site (@{const additions_value_presents}'s form). Eight cases: no
  additions (the given as its own candidate); one added definition; an added definition calling an added one and a
  given one; that candidate with the called added definition removed (a missing callee); an added definition calling
  a given definition outside the given's package; an added definition stating a payload other than the empty one; an
  added use the given holds; an added binding whose target no use holds.
\<close>

section \<open>Small programs, installed\<close>

definition additions_fixture_fact :: "octets \<Rightarrow> (nat,nat,nat) finite_factor_schema" where
  "additions_fixture_fact p=\<lparr>finite_schema_conclusion=Finite_Pattern_Payload p, finite_schema_premises={||},
    finite_schema_materials={||}\<rparr>"

definition additions_fixture_calls :: "nat list \<Rightarrow> (nat,nat,nat) finite_factor_schema" where
  "additions_fixture_calls ds=\<lparr>finite_schema_conclusion=Finite_Variable 0,
    finite_schema_premises=fset_of_list (map (\<lambda>i. (i,(ds!i,Finite_Variable 0))) [0..<length ds]),
    finite_schema_materials={||}\<rparr>"

definition additions_fixture_program ::
    "(nat\<times>(nat,nat,nat) finite_factor_schema) list \<Rightarrow> (nat,nat,nat,nat) finite_schema_system" where
  "additions_fixture_program cs=\<lparr>finite_system_interfaces=fset_of_list (map (\<lambda>(d,S). (d,Finite_Variable 0)) cs),
    finite_system_clauses=fset_of_list (map (\<lambda>(d,S). ((d,0),S)) cs)\<rparr>"

definition additions_fixture_given_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "additions_fixture_given_program=additions_fixture_program [(0,additions_fixture_fact [])]"

definition additions_fixture_one :: "(nat,nat,nat,nat) finite_schema_system" where
  "additions_fixture_one=additions_fixture_program [(0,additions_fixture_fact []),(1,additions_fixture_fact [])]"

definition additions_fixture_calling :: "(nat,nat,nat,nat) finite_schema_system" where
  "additions_fixture_calling=additions_fixture_program
    [(0,additions_fixture_fact []),(1,additions_fixture_fact []),(2,additions_fixture_calls [1,0])]"

definition additions_fixture_payload :: "(nat,nat,nat,nat) finite_schema_system" where
  "additions_fixture_payload=additions_fixture_program [(0,additions_fixture_fact []),(1,additions_fixture_fact [1])]"

definition additions_fixture_side_calling :: "(nat,nat,nat,nat) finite_schema_system" where
  "additions_fixture_side_calling=additions_fixture_program
    [(0,additions_fixture_fact []),(1,additions_fixture_fact []),(2,additions_fixture_calls [1])]"

text \<open>An installation, its placement, and the rows an extension adds.\<close>

definition additions_fixture_install ::
    "local_address option finite_artifact_environment \<Rightarrow> (nat,nat,nat,nat) finite_schema_system \<Rightarrow>
      (nat \<Rightarrow> local_address option definition_site) \<Rightarrow> (nat,nat,nat,nat) finite_schema_system \<Rightarrow>
      local_address option finite_artifact_environment\<times>local_address option" where
  "additions_fixture_install E P p Q=(case finite_extend_mapped_native E P Q p of Some z \<Rightarrow> z
    | None \<Rightarrow> (finite_empty_environment,None))"

definition additions_fixture_placement ::
    "local_address option finite_artifact_environment \<Rightarrow> (nat,nat,nat,nat) finite_schema_system \<Rightarrow>
      (nat \<Rightarrow> local_address option definition_site) \<Rightarrow> (nat,nat,nat,nat) finite_schema_system \<Rightarrow>
      nat \<Rightarrow> local_address option definition_site" where
  "additions_fixture_placement E P p Q=finite_program_coordinates E (finite_system_definitions P)
    (finite_system_definitions Q) p"

definition additions_fixture_rows ::
    "local_address option finite_artifact_environment \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow>
      local_address option finite_artifact_environment" where
  "additions_fixture_rows E F=\<lparr>finite_environment_artifacts=finite_environment_artifacts F |-| finite_environment_artifacts E,
    finite_environment_bindings=finite_environment_bindings F |-| finite_environment_bindings E\<rparr>"

definition additions_fixture_merge ::
    "local_address option finite_artifact_environment \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow>
      local_address option finite_artifact_environment" where
  "additions_fixture_merge E A=\<lparr>finite_environment_artifacts=finite_environment_artifacts E |\<union>| finite_environment_artifacts A,
    finite_environment_bindings=finite_environment_bindings E |\<union>| finite_environment_bindings A\<rparr>"

text \<open>The additions value: the added rows as an environment's rows, beside the candidate's site.\<close>

definition additions_fixture_value ::
    "local_address option finite_artifact_environment \<Rightarrow> local_address option definition_site \<Rightarrow> finite_factor_term" where
  "additions_fixture_value A s=Finite_Pair (finite_environment_value A) (finite_site_data s)"

section \<open>The given and its extensions\<close>

definition additions_fixture_given :: "local_address option finite_artifact_environment\<times>local_address option" where
  "additions_fixture_given=additions_fixture_install (fst empty_package_selection) empty_installation_program
    (\<lambda>_. (None,[])) additions_fixture_given_program"

definition additions_fixture_given_placement :: "nat \<Rightarrow> local_address option definition_site" where
  "additions_fixture_given_placement=additions_fixture_placement (fst empty_package_selection)
    empty_installation_program (\<lambda>_. (None,[])) additions_fixture_given_program"

definition additions_fixture_extension ::
    "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> local_address option finite_artifact_environment\<times>local_address option" where
  "additions_fixture_extension Q=additions_fixture_install (fst additions_fixture_given) additions_fixture_given_program
    additions_fixture_given_placement Q"

definition additions_fixture_extension_placement :: "(nat,nat,nat,nat) finite_schema_system \<Rightarrow>
    nat \<Rightarrow> local_address option definition_site" where
  "additions_fixture_extension_placement Q=additions_fixture_placement (fst additions_fixture_given)
    additions_fixture_given_program additions_fixture_given_placement Q"

text \<open>
  A case: the given's site value, the additions value, and the candidate's site value in its whole environment, at
  which the guard over site values judges the same candidate.
\<close>

type_synonym additions_fixture_case = "finite_factor_term\<times>finite_factor_term\<times>finite_factor_term"

definition additions_fixture_case ::
    "local_address option finite_artifact_environment\<times>local_address option \<Rightarrow>
      local_address option finite_artifact_environment \<Rightarrow> local_address option \<Rightarrow> additions_fixture_case" where
  "additions_fixture_case g A v=(finite_site_presented (fst g) (snd g) [],additions_fixture_value A (v,[]),
    finite_site_presented (additions_fixture_merge (fst g) A) v [])"

definition additions_fixture_extended :: "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> additions_fixture_case" where
  "additions_fixture_extended Q=(let F=additions_fixture_extension Q in
    additions_fixture_case additions_fixture_given (additions_fixture_rows (fst additions_fixture_given) (fst F)) (snd F))"

definition additions_fixture_missing :: additions_fixture_case where
  "additions_fixture_missing=(let F=additions_fixture_extension additions_fixture_calling;
    x=fst (additions_fixture_extension_placement additions_fixture_calling 1);
    A=additions_fixture_rows (fst additions_fixture_given) (fst F) in
    additions_fixture_case additions_fixture_given
      \<lparr>finite_environment_artifacts=ffilter (\<lambda>(u,R). u\<noteq>x) (finite_environment_artifacts A),
        finite_environment_bindings=ffilter (\<lambda>((s,k),t). s\<noteq>x \<and> t\<noteq>x) (finite_environment_bindings A)\<rparr> (snd F))"

definition additions_fixture_outside :: additions_fixture_case where
  "additions_fixture_outside=(let S=additions_fixture_extension additions_fixture_one;
    g=(fst S,snd additions_fixture_given);
    F=additions_fixture_install (fst S) additions_fixture_one (additions_fixture_extension_placement additions_fixture_one)
      additions_fixture_side_calling in
    additions_fixture_case g (additions_fixture_rows (fst S) (fst F)) (snd F))"

definition additions_fixture_held_use :: additions_fixture_case where
  "additions_fixture_held_use=additions_fixture_case additions_fixture_given
    \<lparr>finite_environment_artifacts={|(snd additions_fixture_given,finite_empty_artifact)|},
      finite_environment_bindings={||}\<rparr> (snd additions_fixture_given)"

definition additions_fixture_absent_target :: additions_fixture_case where
  "additions_fixture_absent_target=(let F=additions_fixture_extension additions_fixture_one;
    x=fst (additions_fixture_extension_placement additions_fixture_one 1);
    A=additions_fixture_rows (fst additions_fixture_given) (fst F) in
    additions_fixture_case additions_fixture_given
      \<lparr>finite_environment_artifacts=finite_environment_artifacts A,
        finite_environment_bindings=fimage (\<lambda>((s,k),t). ((s,k),if t=x then Some [7,7,7] else t))
          (finite_environment_bindings A)\<rparr> (snd F))"

definition additions_fixture_cases :: "(String.literal\<times>additions_fixture_case) list" where
  "additions_fixture_cases=[
    (STR ''no additions'',additions_fixture_case additions_fixture_given finite_empty_environment
      (snd additions_fixture_given)),
    (STR ''one added definition'',additions_fixture_extended additions_fixture_one),
    (STR ''an added definition calling an added and a given one'',additions_fixture_extended additions_fixture_calling),
    (STR ''a missing callee'',additions_fixture_missing),
    (STR ''a given callee outside the given package'',additions_fixture_outside),
    (STR ''a payload other than the empty one'',additions_fixture_extended additions_fixture_payload),
    (STR ''an added use the given holds'',additions_fixture_held_use),
    (STR ''an added binding whose target no use holds'',additions_fixture_absent_target)]"

end
