theory Development_Given_Readers
  imports Development_First_Problem_Guard Native_Control_Quotation_Code Bootstrap_Finite_Closure
begin

section \<open>The readers of the given's sockets and of the native request, as one numbered program\<close>

text \<open>
  The given of the native loop's first problem holds the closed packages of the Factor readers its
  guard's four sockets and the native request at a package call. They are one numbered program, the
  guard's own @{const guard_readers_system}: the union of the package additions' system, whose lineage
  holds every reader but the audit and ends in the callee boundary (390--393), and the payload audit's
  (500--505, over definition admission), joined where they agree (@{thm [source] readers_agreement}).
  Every reader stands at the number its theory gives it. The program is the union, not the rooted
  closure of its entries: the closure is a reflexive-transitive closure, for which the finite
  presentation below derives no code. The definitions outside the entries' closure are computed at the
  end of this theory.
\<close>

subsection \<open>Each reader's system agrees with the additions' system on its whole domain\<close>

lemma given_root_membership_agreement:
  "systems_agree_on root_family_reading_system package_membership_system
    (system_definitions root_family_reading_system)"
  by (simp add: systems_agree_on_added package_membership_system_def definition_edge_reading_system_def
    definition_clause_reading_system_def package_admission_system_def)

lemma given_clause_membership_agreement:
  "systems_agree_on definition_clause_reading_system package_membership_system
    (system_definitions definition_clause_reading_system)"
  by (simp add: systems_agree_on_added package_membership_system_def definition_edge_reading_system_def)

lemma given_edge_membership_agreement:
  "systems_agree_on definition_edge_reading_system package_membership_system
    (system_definitions definition_edge_reading_system)"
  by (simp add: systems_agree_on_added package_membership_system_def)

lemma given_retention_complete_agreement:
  "systems_agree_on package_retention_admission_system complete_data_admission_system
    (system_definitions package_retention_admission_system)"
  by (simp add: systems_agree_on_added complete_data_admission_system_def)

lemmas given_membership_agreement =
  whole_agreement_transitive[OF membership_complete_data_agreement complete_data_additions_agreement]

lemmas given_reader_agreements =
  whole_agreement_transitive[OF call_admission_complete_data_agreement complete_data_additions_agreement]
  whole_agreement_transitive[OF closure_complete_data_agreement complete_data_additions_agreement]
  whole_agreement_transitive[OF given_root_membership_agreement given_membership_agreement]
  admission_additions_agreement
  whole_agreement_transitive[OF given_clause_membership_agreement given_membership_agreement]
  whole_agreement_transitive[OF given_edge_membership_agreement given_membership_agreement]
  given_membership_agreement
  inclusion_additions_agreement
  whole_agreement_transitive[OF given_retention_complete_agreement complete_data_additions_agreement]

subsection \<open>Each reader means in the program what it means in its own system\<close>

text \<open>
  A reader's system that agrees with the additions' system on its whole domain means at the program
  what it means alone: the program means what the additions' system means at its definitions
  (@{thm [source] guard_readers_left}), and the additions' system what the reader's system means
  (@{thm [source] whole_system_agreement_meaning}). Instantiated once per reader's system; each reader's
  exact contract is then an instance at the program, read through that lemma, none proved again.
\<close>

lemma given_reader_meaning:
  assumes formed: "schema_system_formed S"
    and agreement: "systems_agree_on S use_additions_system (system_definitions S)"
    and member: "d\<in>system_definitions S"
  shows "(d,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (d,t)\<in>positive_meaning S"
proof -
  have "d\<in>system_definitions use_additions_system"
    using whole_agreement_definitions[OF agreement] member by blast
  then show ?thesis
    using guard_readers_left[of d t] whole_system_agreement_meaning[OF formed use_additions_system_formed
      agreement member, of t] by simp
qed

lemmas given_call_meaning = given_reader_meaning[OF definition_call_admission_system_formed given_reader_agreements(1)]
lemmas given_closure_meaning = given_reader_meaning[OF package_closure_admission_system_formed given_reader_agreements(2)]
lemmas given_root_meaning = given_reader_meaning[OF root_family_reading_system_formed given_reader_agreements(3)]
lemmas given_admission_meaning = given_reader_meaning[OF package_admission_system_formed given_reader_agreements(4)]
lemmas given_clause_meaning = given_reader_meaning[OF definition_clause_reading_system_formed given_reader_agreements(5)]
lemmas given_edge_meaning = given_reader_meaning[OF definition_edge_reading_system_formed given_reader_agreements(6)]
lemmas given_membership_meaning = given_reader_meaning[OF package_membership_system_formed given_reader_agreements(7)]
lemmas given_inclusion_meaning = given_reader_meaning[OF environment_inclusion_system_formed given_reader_agreements(8)]
lemmas given_retention_meaning =
  given_reader_meaning[OF package_retention_admission_system_formed given_reader_agreements(9)]

lemma given_entry_members:
  "72\<in>system_definitions definition_call_admission_system"
  "77\<in>system_definitions package_closure_admission_system"
  "79\<in>system_definitions root_family_reading_system"
  "80\<in>system_definitions package_admission_system"
  "81\<in>system_definitions definition_clause_reading_system"
  "82\<in>system_definitions definition_edge_reading_system"
  "83\<in>system_definitions package_membership_system"
  "113\<in>system_definitions environment_inclusion_system"
  "122\<in>system_definitions package_retention_admission_system"
  "392\<in>system_definitions use_additions_system"
  "393\<in>system_definitions use_additions_system"
  "505\<in>system_definitions payload_audit_system"
  by simp_all

text \<open>G1: environment inclusion. G2: package admission, with the root family and edge readings.\<close>

lemmas given_environment_inclusion_exact =
  environment_inclusion_exact[unfolded given_inclusion_meaning[OF given_entry_members(8), symmetric]]
lemmas given_package_admission_exact =
  package_admission_exact[unfolded given_admission_meaning[OF given_entry_members(4), symmetric]]
lemmas given_root_family_reading_exact =
  root_family_reading_exact[unfolded given_root_meaning[OF given_entry_members(3), symmetric]]
lemmas given_definition_edge_reading_exact =
  definition_edge_reading_exact[unfolded given_edge_meaning[OF given_entry_members(6), symmetric]]

text \<open>
  G3: package membership, the closure bound with the callee lists it calls, and the callee boundary with
  the reader projecting the given's uses (390--393): key absence (20) over data inequality (3).
\<close>

lemmas given_package_membership_exact =
  package_membership_exact[unfolded given_membership_meaning[OF given_entry_members(7), symmetric]]
lemmas given_package_closure_admission_exact =
  package_closure_admission_exact[unfolded given_closure_meaning[OF given_entry_members(2), symmetric]]

lemma given_package_closure_operations_exact:
  assumes "d\<in>{73,74,75,76,77}"
  shows "(d,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> package_closure_operation_result d t"
proof -
  have "d\<in>system_definitions package_closure_admission_system" using assms by auto
  then show ?thesis by (simp only: given_closure_meaning package_closure_operations_exact[OF assms])
qed

lemmas given_use_additions_on_values =
  use_additions_on_values[unfolded guard_readers_left[OF given_entry_members(10), symmetric]]
lemmas given_use_absence_exact =
  use_absence_exact[unfolded guard_readers_left[OF given_entry_members(11), symmetric]]

lemma given_key_absence:
  "(20,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (20,t)\<in>positive_meaning keyed_list_system"
  "(3,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (3,t)\<in>positive_meaning complete_data_admission_system"
  using guard_readers_left[of 20 t] guard_readers_left[of 3 t] use_additions_components(6)[of t]
    whole_system_agreement_meaning[OF complete_data_admission_system_formed use_additions_system_formed
      complete_data_additions_agreement, of 3 t]
  by simp_all

text \<open>G4: the payload audit, with the readers it calls.\<close>

lemmas given_payload_audit_exact =
  payload_audit_exact[unfolded guard_readers_right[OF given_entry_members(12), symmetric]]
lemmas given_definition_call_admission_exact =
  definition_call_admission_exact[unfolded given_call_meaning[OF given_entry_members(1), symmetric]]
lemmas given_definition_clause_reading_exact =
  definition_clause_reading_exact[unfolded given_clause_meaning[OF given_entry_members(5), symmetric]]

lemma given_audit_callees:
  "(37,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(34,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (34,t)\<in>positive_meaning record_admission_system"
  "(32,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (32,t)\<in>positive_meaning family_admission_system"
  "(59,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (59,t)\<in>positive_meaning row_values_system"
  "(500,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (500,t)\<in>positive_meaning empty_payloads_system"
  "(504,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (504,t)\<in>positive_meaning clause_family_payloads_system"
  "(65,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (65,t)\<in>positive_meaning schema_instantiation_system"
  "(45,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (45,t)\<in>positive_meaning target_projection_system"
  using payload_audit_components guard_readers_right[of 37 t] guard_readers_right[of 34 t]
    guard_readers_right[of 32 t] guard_readers_right[of 59 t] guard_readers_right[of 500 t]
    guard_readers_right[of 504 t] guard_readers_right[of 65 t] payload_audit_old_meaning[of 65 t]
    clause_family_payloads_old_meaning[of 65 t] clause_payloads_components(1)[of t]
    given_call_meaning[of 45 t] audit_target_meaning[of t] by simp_all

text \<open>The native request at a package: membership, the root family reading, retention admission, inclusion.\<close>

lemmas given_package_retention_admission_exact =
  package_retention_admission_exact[unfolded given_retention_meaning[OF given_entry_members(9), symmetric]]

section \<open>The program's finite presentation\<close>

text \<open>
  The site context's base is a rooted restriction of the lineage the complete data admission already
  holds whole, so the scope reading is that system joined with the site context's own group; the code
  of the presentation is derived through this form, whose every constant is a finite definition.
\<close>

lemma given_scope_components:
  "scope_reading_components_system=system_union complete_data_admission_system context_definition_group"
proof -
  have inside: "system_definitions context_base_system\<subseteq>system_definitions complete_data_admission_system"
    by (rule order.trans[OF context_base_subdomain]) simp
  have sub: "system_definitions context_base_system\<subseteq>
      system_definitions complete_data_admission_system\<inter>system_definitions context_admission_system"
    using inside unfolding context_admission_definitions by blast
  have agree_on: "systems_agree_on complete_data_admission_system context_admission_system
      (system_definitions context_base_system)"
    by (rule systems_agree_on_subdomain[OF scope_context_agreement sub])
  have agree_interfaces: "\<And>d p. d\<in>system_definitions context_base_system \<Longrightarrow>
      (d,p)\<in>system_interfaces complete_data_admission_system \<longleftrightarrow>
        (d,p)\<in>system_interfaces context_admission_system"
    using agree_on unfolding systems_agree_on_def by blast
  have agree_clauses: "\<And>d c S. d\<in>system_definitions context_base_system \<Longrightarrow>
      ((d,c),S)\<in>system_clauses complete_data_admission_system \<longleftrightarrow>
        ((d,c),S)\<in>system_clauses context_admission_system"
    using agree_on unfolding systems_agree_on_def by blast
  have interfaces: "system_interfaces context_base_system\<subseteq>system_interfaces complete_data_admission_system"
  proof
    fix x assume row: "x\<in>system_interfaces context_base_system"
    obtain d p where x: "x=(d,p)" by (cases x)
    have member: "d\<in>system_definitions context_base_system"
      using row x by (auto simp: system_definitions_def rel_dom_def)
    have "(d,p)\<in>system_interfaces context_admission_system"
      using row x by (simp add: context_admission_system_def system_union_def)
    then show "x\<in>system_interfaces complete_data_admission_system"
      by (simp only: x agree_interfaces[OF member])
  qed
  have clauses: "system_clauses context_base_system\<subseteq>system_clauses complete_data_admission_system"
  proof
    fix x assume row: "x\<in>system_clauses context_base_system"
    obtain d c S where x: "x=((d,c),S)" by (cases x) auto
    have member: "d\<in>system_definitions context_base_system"
      using context_base_formed row x unfolding schema_system_formed_def by blast
    have "((d,c),S)\<in>system_clauses context_admission_system"
      using row x by (simp add: context_admission_system_def system_union_def)
    then show "x\<in>system_clauses complete_data_admission_system"
      by (simp only: x agree_clauses[OF member])
  qed
  have interfaces_union: "system_interfaces complete_data_admission_system\<union>
      (system_interfaces context_base_system\<union>system_interfaces context_definition_group)=
    system_interfaces complete_data_admission_system\<union>system_interfaces context_definition_group"
    using interfaces by blast
  have clauses_union: "system_clauses complete_data_admission_system\<union>
      (system_clauses context_base_system\<union>system_clauses context_definition_group)=
    system_clauses complete_data_admission_system\<union>system_clauses context_definition_group"
    using clauses by blast
  show ?thesis
    unfolding scope_reading_components_system_def context_admission_system_def system_union_def
    by (simp only: schema_system.select_convs interfaces_union clauses_union)
qed

lemma given_readers_components:
  "guard_readers_system=system_union (add_view_definition (add_view_definition (add_view_definition
    (add_view_definition (system_union complete_data_admission_system context_definition_group)
      393 data_x {(0,use_absence_schema)}) 390 data_x (addition_element_clauses 393))
      391 data_x (context_list_clauses 390 391)) 392 data_x {(0,package_additions_schema 391)})
    payload_audit_system"
  by (simp only: guard_readers_system_def use_additions_system_def addition_list_system_def
    addition_element_system_def use_absence_system_def given_scope_components)

definition finite_given_readers :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_given_readers=finite_system_of guard_readers_system"

lemma finite_given_readers_exact:
  "decode_finite_system finite_given_readers=guard_readers_system"
  unfolding finite_given_readers_def
  by (rule decode_finite_system_of[OF guard_readers_formed])

lemma finite_given_readers_formed:
  "finite_system_formed finite_given_readers"
  by (simp only: finite_system_formed_correct finite_given_readers_exact guard_readers_formed)

local_setup \<open>Native_Finite_Equations.note @{binding finite_given_readers_code}
  @{thm finite_given_readers_def[unfolded given_readers_components]}\<close>

export_code finite_given_readers finite_system_formed fcard finite_system_definitions finite_system_payloads
  checking SML

value "finite_system_formed finite_given_readers"
value "fcard (finite_system_definitions finite_given_readers)"

section \<open>The readers' payloads\<close>

lemmas given_readers_payloads_exact =
  finite_system_payloads_exact[of finite_given_readers, unfolded finite_given_readers_exact]

lemmas given_readers_payloads_audited =
  finite_system_payloads_audited[of finite_given_readers, unfolded finite_given_readers_exact,
    OF guard_readers_formed]

value "finite_system_payloads finite_given_readers"

value "ffilter (\<lambda>z. snd z\<noteq>{||}) (fimage (\<lambda>(d,p). (d,finite_pattern_payloads p|-|{|[]|}))
  (finite_system_interfaces finite_given_readers))"

value "ffilter (\<lambda>z. snd z\<noteq>{||}) (fimage (\<lambda>((d,c),S). ((d,c),finite_schema_payloads S|-|{|[]|}))
  (finite_system_clauses finite_given_readers))"

text \<open>
  The definitions outside the rooted closure of the entries, the definitions with material premises, and,
  for each entry, those its closure reaches.
\<close>

value "let E=ffUnion (fimage (\<lambda>((d,c),S). fimage (Pair d) (finite_schema_dependencies S))
    (finite_system_clauses finite_given_readers));
  K=finite_edge_closure E;
  R={|72,77,79,80,81,82,83,113,122,392,393,505::nat|};
  C=R|\<union>|fimage snd (ffilter (\<lambda>z. fst z|\<in>|R) K);
  M=fimage (\<lambda>((d,c),S). d) (ffilter (\<lambda>((d,c),S). finite_schema_materials S\<noteq>{||})
    (finite_system_clauses finite_given_readers))
  in (sorted_list_of_fset (finite_system_definitions finite_given_readers|-|C),
    sorted_list_of_fset M,
    map (\<lambda>r. (r,sorted_list_of_fset (M|\<inter>|finsert r (fimage snd (ffilter (\<lambda>z. fst z=r) K)))))
      (sorted_list_of_fset R))"

end
