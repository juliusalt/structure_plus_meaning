theory Retained_Clause_Execution
  imports Finite_Retained_Clause_Admission Factor_Finite_Equality_Source
begin

section \<open>Actual finite source changes keep their complete material\<close>

definition finite_variable_artifact :: finite_exact_artifact where
  "finite_variable_artifact=finite_equality_artifact\<lparr>finite_structure:=
    (finite_structure finite_equality_artifact)\<lparr>finite_incidence:=
      ffilter (\<lambda>(r,s,t). r\<noteq>[11]) (finite_incidence (finite_structure finite_equality_artifact))
        |\<union>| {|([11],[11],[10])|}\<rparr>\<rparr>"

definition finite_variable_schema :: "local_address option finite_native_schema" where
  "finite_variable_schema=finite_equality_schema\<lparr>finite_schema_conclusion:=Finite_Variable [10]\<rparr>"

definition finite_guard_artifact :: finite_exact_artifact where
  "finite_guard_artifact=finite_variable_artifact\<lparr>
    finite_structure:=(finite_structure finite_variable_artifact)\<lparr>
      finite_carrier:=finite_carrier (finite_structure finite_variable_artifact) |\<union>|
        fset_of_list (map (\<lambda>n. [n]) [26..<34]),
      finite_incidence:=finite_incidence (finite_structure finite_variable_artifact) |\<union>|
        fset_of_list (map (\<lambda>(r,s,t). ([r],[s],[t]))
          [(14,26,27),(27,28,30),(27,29,31),(28,28,29),(30,30,32),(30,32,33),(31,31,10)])\<rparr>,
    finite_data:=(finite_data finite_variable_artifact)\<lparr>finite_bindings:={|([33],[1])|}\<rparr>\<rparr>"

definition finite_guard_schema :: "local_address option finite_native_schema" where
  "finite_guard_schema=finite_variable_schema\<lparr>
    finite_schema_premises:={|([26],(None,[1]),Finite_Variable [10])|}\<rparr>"

definition finite_guard_source :: "bool \<Rightarrow> local_address option finite_artifact_environment" where
  "finite_guard_source b=finite_enumerated_environment
    [(None,if b then finite_variable_artifact else finite_equality_artifact)] []"

definition finite_guard_environment :: "bool \<Rightarrow> local_address option finite_artifact_environment" where
  "finite_guard_environment b=finite_enumerated_environment
    [(None,if b then finite_variable_artifact else finite_equality_artifact),(Some [1],finite_guard_artifact)]
    [((Some [1],[32]),None)]"

definition finite_equality_extension :: "bool \<Rightarrow> local_address option finite_artifact_environment" where
  "finite_equality_extension b=finite_enumerated_environment
    [(None,finite_equality_artifact),(Some [9],finite_enumerated_artifact [[]] [] [] [])]
    (if b then [((Some [9],[]),None)] else [])"

definition finite_equality_changed_source :: "bool \<Rightarrow> local_address option finite_artifact_environment" where
  "finite_equality_changed_source malformed=finite_enumerated_environment
    [(None,finite_equality_artifact\<lparr>finite_structure:=(finite_structure finite_equality_artifact)\<lparr>
      finite_carrier:=(if malformed then finite_carrier (finite_structure finite_equality_artifact) |-| {|[10]|}
        else finsert [26] (finite_carrier (finite_structure finite_equality_artifact)))\<rparr>\<rparr>)] []"

type_synonym retained_clause_control =
  "local_address option finite_artifact_environment \<times> local_address option finite_native_schema \<times>
    local_address option finite_artifact_environment \<times> local_address option \<times> local_address \<times>
    local_address option definition_site"

definition retained_clause_control :: "nat \<Rightarrow> retained_clause_control" where
  "retained_clause_control n=(let C=finite_equality_environment; S=finite_equality_schema in
    if n=0 then (C,S,C,None,[0],(None,[1])) else
    if n=1 then (C,S,finite_equality_extension False,None,[0],(None,[1])) else
    if n=2 then (C,S,finite_equality_changed_source False,None,[0],(None,[1])) else
    if n=3 then (C,finite_variable_schema,C,None,[0],(None,[1])) else
    if n=4 then (C,S,C,None,[0],(None,[8])) else
    if n=5 then (C,S,C,None,[6],(None,[1])) else
    if n=6 then (C,S,finite_enumerated_environment [] [],None,[0],(None,[1])) else
    if n=7 then (C,S,finite_equality_changed_source True,None,[0],(None,[1])) else
    if n=8 then (finite_equality_extension False,S,C,None,[0],(None,[1])) else
    if n=9 then (finite_equality_extension True,S,finite_equality_extension True,None,[0],(None,[1])) else
    if n=10 then (finite_equality_extension True,S,finite_equality_extension False,None,[0],(None,[1])) else
    if n=11 then (C,finite_guard_schema,C,None,[0],(None,[1])) else
    if n=12 then (C,finite_guard_schema,finite_guard_environment False,Some [1],[0],(Some [1],[1])) else
    if n=13 then (C,finite_guard_schema,finite_guard_environment True,Some [1],[0],(Some [1],[1])) else
      (finite_guard_source True,finite_guard_schema,finite_guard_environment True,Some [1],[0],(Some [1],[1])))"

definition finite_retained_clause_observations where
  "finite_retained_clause_observations C S D u r d=(let
    source=finite_environment_formed C; target=finite_environment_formed D;
    included=finite_environment_included C D;
    programs=finite_native_package_readings D u r;
    member=fBex programs (\<lambda>P. d |\<in>| finite_system_definitions P);
    clause=finite_single_clause_at D (fst d) (snd d) S in
    (sorted_list_of_fset (fimage (\<lambda>P. sorted_list_of_fset (finite_system_definitions P)) programs),
      [source,target,included,member,clause,source \<and> included \<and> member \<and> clause]))"

lemma finite_retained_clause_observation_equation:
  "snd (finite_retained_clause_observations C S D u r d)=
    [finite_environment_formed C,finite_environment_formed D,finite_environment_included C D,
      finite_package_member D u r d,finite_single_clause_at D (fst d) (snd d) S,
      finite_retained_clause_admitted C S D u r d]"
  by (simp add: finite_retained_clause_observations_def finite_package_member_def finite_retained_clause_admitted_def Let_def)

definition retained_clause_control_report where
  "retained_clause_control_report n=(case retained_clause_control n of (C,S,D,u,r,d) \<Rightarrow>
    ((finite_environment_artifact_rows C,sorted_list_of_fset (finite_environment_bindings C)),S,
      (finite_environment_artifact_rows D,sorted_list_of_fset (finite_environment_bindings D)),u,r,d,
      finite_retained_clause_observations C S D u r d))"

export_code retained_clause_control_report finite_schema_conclusion finite_schema_premises finite_schema_materials
  Finite_Variable Finite_Pattern_Payload Finite_Pattern_Pair Finite_Pattern_Target
  fset set nat_of_integer integer_of_nat in SML module_name Retained_Clause_Execution file_prefix retained_clause_execution

text \<open>
  The input index selects the complete source, expected schema, candidate
  environment, package root, and definition site through the displayed map.
  Every reported condition is computed by its proved finite operation. The
  report retains both complete environment tables and the recovered domain.

  The last three controls use one unchanged guard calling the actual source
  at None,[1]. Only that source clause changes between equality and acceptance
  of every formed argument. The original source is required by control 13;
  control 14 independently declares the changed source instead.
\<close>

end
