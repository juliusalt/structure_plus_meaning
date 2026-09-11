theory Factor_Transition_Construction_Examples
  imports Factor_Dependency_Evidence_Examples Factor_Construction_Reuse
    Factor_Current_Entry_Publications RRA_Replacement
begin

lemma constant_entry_construction_invariant:
  assumes every: "\<And>t. term_formed t \<Longrightarrow>
    schema_call_formed P d t \<and> ((d,t)\<in>positive_meaning P\<longleftrightarrow>b)"
  shows "construction_permission_invariant P d"
  unfolding construction_permission_invariant_def
proof (intro allI impI)
  fix xs B W R t v assume built: "source_constructs xs B W R"
    and coordinates: "construction_coordinates_formed B W"
    and first: "construction_claim_presents xs B W R t"
    and second: "construction_claim_presents xs B W R v"
  have tf: "term_formed t" and vf: "term_formed v"
    using construction_claim_presents_formed[OF built coordinates first]
      construction_claim_presents_formed[OF built coordinates second] by blast+
  show "(schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d v) \<and>
    ((d,t)\<in>positive_meaning P\<longleftrightarrow>(d,v)\<in>positive_meaning P)"
    using every[OF tf] every[OF vf] by blast
qed

section \<open>Constructing the candidate, evidence, publication, and accepted material together\<close>

theorem universal_current_program_successor_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and invariant: "amendment_permission_invariant P d"
    and every: "\<And>t. term_formed t \<Longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P"
    and candidate: "closed_native_package_at E' qu qr Q" and member: "e\<in>system_definitions Q"
    and authority: "target_formed A'"
    and remainder: "environment_formed L" "(lu,lr)\<in>environment_positions L"
  shows "\<exists>Z R H Rs S U X z N v V J ju bu D M B K F au R' N' root.
    program_scope_quoted_at Z [] E' qu qr Q \<and>
    predecessor_assembly_certificate C q C q R [] H [Z] {} (whole_source_construction Z) Z \<and>
    generation_predecessors H={|G|} \<and> generation_locus H=l \<and> G\<noteq>H \<and>
    amendment_dependency_evidence C q H C q Rs \<and>
    (\<forall>Q\<in>Rs. \<not>amendment_dependency_evidence C q H C q (Rs-{Q})) \<and>
    current_entry_scope_quoted_at X [] A' l H z E' qu qr Q e \<and>
    current_scope_quoted_at X [] J ju [] bu [] A' N v [] l H z \<and>
    publication_environment_closed N v [] V \<and> publication_snapshot V=U \<and>
    publication_evidence V=Abs_fset (image Whole_Artifact (insert R Rs)) \<and>
    publication_dependencies V={||} \<and>
    current_snapshot_at C q S \<and> current_snapshot_at X [] U \<and>
    transact S (replacement_transaction G H) (Applied U) \<and> U\<noteq>S \<and>
    (\<forall>m. m\<noteq>l \<longrightarrow> snapshot_lookup U m=snapshot_lookup S m) \<and>
    dependency_support_at D None [] C Rs L lu lr \<and>
    assembly_support_at M None [] C R D None [] \<and> successor_material_at B None [] X M None [] \<and>
    continuation_envelope C q K S (replacement_transaction G H) U B None [] \<and>
    current_transition_dependencies_at C q F au [] H K X \<and> certified_transition_dependencies C q R' [] H K X \<and>
    replay_scope_quoted_at R' [] N' pu pr au [] root {} \<and>
    native_package_environment F pu pr=E \<and> native_package_environment N' pu pr=E \<and>
    native_judgment_environment N' pu pr au []=native_judgment_environment F pu pr au []"
proof -
  have package: "native_package_at E' qu qr Q" using candidate by (simp add: closed_native_package_at_def)
  have fixed: "native_package_environment E' qu qr=E'"
    by (rule native_package_closed_environment_fixed[OF candidate])
  obtain Z where payload: "exact_formed Z" "program_scope_quoted_at Z [] E' qu qr Q"
    using program_scope_quoted_total[OF package] fixed by auto
  let ?W="whole_source_construction Z"
  let ?t="construction_claim_term [Z] {} ?W Z"
  have built: "source_constructs [Z] {} ?W Z" by (rule whole_source_constructs[OF payload(1)])
  have coordinates: "construction_coordinates_formed {} ?W" by (rule whole_source_coordinates)
  have present: "construction_claim_presents [Z] {} ?W Z ?t" by (rule construction_claim_term_presents[OF built])
  have tf: "term_formed ?t" by (rule construction_claim_presents_formed[OF built coordinates present])
  have ci: "construction_permission_invariant P d"
    by (rule constant_entry_construction_invariant[where b=True]) (use every in auto)
  have permitted: "factor_constructs P d [Z] {} ?W Z"
    using every[OF tf] by (simp only: factor_construction_at_presentation[OF built coordinates ci present])
  obtain R where certificate: "current_construction_certificate C q R [] [Z] {} ?W Z"
    using current_construction_certificate_presentation_total[OF current permitted present] by blast
  have companion: "current_companion C q C q" by (rule current_companion_reflexive[OF current])
  obtain J0 ju0 jr0 bu0 br0 N0 v0 root0 where old:
    "current_scope_quoted_at C q J0 ju0 jr0 bu0 br0 A N0 v0 root0 l G p"
    using current_entry_scope_frame[OF current] by blast
  have gf: "generation_formed G" and old_locus: "generation_locus G=l"
    using current_scope_quoted_formed[OF old] by auto
  have locus: "target_formed l" using generation_formed_fields[OF gf] old_locus by auto
  have predecessors: "\<forall>H\<in>fset {|G|}. generation_formed H" using gf by simp
  obtain H where assembly: "predecessor_assembly_certificate C q C q R [] H [Z] {} ?W Z"
    and history: "generation_predecessors H={|G|}" and new_locus: "generation_locus H=l"
    and output_payload: "generation_payload H=Whole_Artifact Z"
    using predecessor_assembly_candidate_total[OF current companion certificate locus predecessors] by blast
  have hf: "generation_formed H" using predecessor_assembly_certificate_account[OF assembly] by blast
  have edge: "G\<in>fset (generation_predecessors H)" using history by simp
  have strict: "G\<noteq>H"
    using predecessor_size_decreases[of G H] edge by (auto simp: predecessor_edges_def)
  have program: "generation_program_scope H E' qu qr Q"
    by (rule generation_program_scope_from_payload[OF hf output_payload payload(2)])
  obtain U0 where subjects: "amendment_dependency_subjects C q H U0"
    using amendment_dependency_subjects_total[OF current program] by blast
  obtain Rs where evidence: "amendment_dependency_evidence C q H C q Rs"
    and needed: "\<forall>Q\<in>Rs. \<not>amendment_dependency_evidence C q H C q (Rs-{Q})"
    using universal_current_dependency_evidence[OF current subjects every] by blast
  have rsf: "finite Rs" "\<forall>Q\<in>Rs. exact_formed Q"
    using amendment_dependency_evidence_formed[OF evidence] by auto
  obtain F0 au0 ar0 root1 where recorded: "replay_scope_quoted_at R [] F0 pu pr au0 ar0 root1 {}"
    using current_construction_certificate_program[OF current certificate] by blast
  have rf: "exact_formed R" using replay_scope_formed[OF recorded] by blast
  obtain S where before: "current_snapshot_at C q S" and sf: "snapshot_formed S"
    and selected: "snapshot_lookup S l=Some G"
    using current_entry_snapshot_total[OF current] by blast
  let ?U="replace_snapshot S {|H|} {||}"
  let ?T="replacement_transaction G H"
  have expected: "snapshot_lookup S (generation_locus G)=Some G" using selected old_locus by simp
  have same_locus: "generation_locus H=generation_locus G" using new_locus old_locus by simp
  have trans: "transact S ?T (Applied ?U)"
    by (rule selected_generation_replacement[OF sf expected hf same_locus])
  have uf: "snapshot_formed ?U" by (rule successful_transaction_formed[OF trans])
  have chosen: "snapshot_lookup ?U (generation_locus H)=Some H" by (rule replacement_result(1)[OF trans])
  have changed: "?U\<noteq>S" by (rule replacement_result(3)[OF trans strict])
  have outside: "\<forall>m. m\<noteq>l \<longrightarrow> snapshot_lookup ?U m=snapshot_lookup S m"
    using replacement_result(2)[OF trans] new_locus by blast
  let ?V="\<lparr>publication_snapshot=?U, publication_dependencies={||},
    publication_evidence=Abs_fset (image Whole_Artifact (insert R Rs))\<rparr>"
  have finite: "finite (image Whole_Artifact (insert R Rs))" using rsf(1) by simp
  have publication: "publication_formed ?V"
    using uf rf rsf finite by (auto simp: publication_formed_def Abs_fset_inverse)
  obtain X z J ju bu N v where successor:
    "current_entry_scope_quoted_at X [] A' (generation_locus H) H z E' qu qr Q e"
    "current_scope_quoted_at X [] J ju [] bu [] A' N v [] (generation_locus H) H z"
    "publication_environment_closed N v [] ?V" "current_snapshot_at X [] ?U"
    using current_entry_publication_total[OF program member authority publication] chosen by auto
  have entry: "current_entry_scope_quoted_at X [] A' l H z E' qu qr Q e"
    and current_scope: "current_scope_quoted_at X [] J ju [] bu [] A' N v [] l H z"
    using successor(1,2) new_locus by simp_all
  obtain D where dependency: "dependency_support_at D None [] C Rs L lu lr"
    and valid: "amendment_dependency_evidence_at C q H D None []"
    using amendment_dependency_material_total[OF evidence remainder] by blast
  have df: "environment_formed D" and site: "(None,[])\<in>environment_positions D"
    using amendment_dependency_evidence_at_formed[OF valid] by auto
  obtain M B K F au R' N' root where actual:
    "assembly_support_at M None [] C R D None []" "successor_material_at B None [] X M None []"
    "continuation_envelope C q K S ?T ?U B None []"
    "current_transition_account_at C q F au [] H K X" "certified_transition_account C q R' [] H K X"
    "replay_scope_quoted_at R' [] N' pu pr au [] root {}"
    "native_package_environment F pu pr=E" "native_package_environment N' pu pr=E"
    "native_judgment_environment N' pu pr au []=native_judgment_environment F pu pr au []"
    using universal_current_account_total[
      OF current entry before successor(4) trans edge assembly invariant every df site] by blast
  have account: "transition_account_certificate C q K H X"
    and accepted: "current_accepts_at C q F au [] H (Whole_Artifact K)"
    using actual(4) by (auto simp: current_transition_account_at_def)
  have complete: "transition_dependency_certificate C q K H X"
    using account valid by (simp only: transition_dependency_with_material[OF actual(3,2,1)])
  have transition: "current_transition_dependencies_at C q F au [] H K X"
    using accepted complete by (simp add: current_transition_dependencies_at_def)
  have retained: "current_acceptance_certificate C q R' [] H (Whole_Artifact K)"
    using actual(5) by (simp add: certified_transition_account_def)
  have certified: "certified_transition_dependencies C q R' [] H K X"
    using retained complete by (simp add: certified_transition_dependencies_def)
  show ?thesis
    by (rule exI[of _ Z], rule exI[of _ R], rule exI[of _ H], rule exI[of _ Rs],
        rule exI[of _ S], rule exI[of _ ?U], rule exI[of _ X], rule exI[of _ z],
        rule exI[of _ N], rule exI[of _ v], rule exI[of _ ?V], rule exI[of _ J],
        rule exI[of _ ju], rule exI[of _ bu], rule exI[of _ D], rule exI[of _ M],
        rule exI[of _ B], rule exI[of _ K], rule exI[of _ F], rule exI[of _ au],
        rule exI[of _ R'], rule exI[of _ N'], rule exI[of _ root])
       (use payload(2) assembly history new_locus strict evidence needed entry current_scope
         successor(3,4) before trans changed outside dependency actual(1-3,6-9) transition certified in simp)
qed

section \<open>One actual predecessor program serves every future closed candidate program\<close>

theorem fixed_current_program_constructs_every_future_program:
  assumes authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C G p E pu P d.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and>
    (\<forall>E' qu qr Q e A'.
      closed_native_package_at E' qu qr Q \<longrightarrow> e\<in>system_definitions Q \<longrightarrow>
      target_formed A' \<longrightarrow>
      (\<exists>H X z K F au R. generation_predecessors H={|G|} \<and> G\<noteq>H \<and>
        current_entry_scope_quoted_at X [] A' l H z E' qu qr Q e \<and>
        current_transition_dependencies_at C [] F au [] H K X \<and>
        certified_transition_dependencies C [] R [] H K X \<and> native_package_environment F pu []=E))"
proof -
  obtain C G p E pu P d where current: "current_entry_scope_quoted_at C [] A l G p E pu [] P d"
    and invariant: "amendment_permission_invariant P d"
    and every: "\<forall>t. term_formed t \<longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P"
    using fixed_current_selection_accepts_every_formed_material[OF authority locus] by blast
  have package: "native_package_at E pu [] P"
    using current_entry_scope_closed[OF current] by (simp add: closed_native_package_at_def)
  have ef: "environment_formed E" using native_package_projection(1)[OF package]
    by (simp add: native_package_formed_def)
  have site: "(pu,[])\<in>environment_positions E" by (rule native_package_root_position[OF package])
  have future: "\<forall>E' qu qr Q e A'.
      closed_native_package_at E' qu qr Q \<longrightarrow> e\<in>system_definitions Q \<longrightarrow>
      target_formed A' \<longrightarrow>
      (\<exists>H X z K F au R. generation_predecessors H={|G|} \<and> G\<noteq>H \<and>
        current_entry_scope_quoted_at X [] A' l H z E' qu qr Q e \<and>
        current_transition_dependencies_at C [] F au [] H K X \<and>
        certified_transition_dependencies C [] R [] H K X \<and> native_package_environment F pu []=E)"
  proof (intro allI impI)
    fix E' :: "local_address option artifact_environment"
    fix qu qr Q e A'
    assume candidate: "closed_native_package_at E' qu qr Q" and member: "e\<in>system_definitions Q"
      and owner: "target_formed A'"
    show "\<exists>H X z K F au R. generation_predecessors H={|G|} \<and> G\<noteq>H \<and>
        current_entry_scope_quoted_at X [] A' l H z E' qu qr Q e \<and>
        current_transition_dependencies_at C [] F au [] H K X \<and>
        certified_transition_dependencies C [] R [] H K X \<and> native_package_environment F pu []=E"
      using universal_current_program_successor_total[
        OF current invariant every[rule_format] candidate member owner ef site] by blast
  qed
  show ?thesis using current future by blast
qed

section \<open>Complete component evidence can accompany a different program with no true calls\<close>

lemma single_refusing_native_program:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q e.
    closed_native_package_at E pu [] Q \<and> system_definitions Q={e} \<and> positive_meaning Q={} \<and>
    (\<forall>t. schema_call_formed Q e t\<longleftrightarrow>term_formed t)"
proof -
  let ?P="\<lparr>system_interfaces={((),Pattern_Variable (0::nat))},system_clauses={}\<rparr>
    :: (nat,unit,unit,unit) schema_system"
  have formed: "schema_system_formed ?P"
    by (auto simp: schema_system_formed_def single_valued_def)
  have definitions: "system_definitions ?P={()}" by (auto simp: system_definitions_def rel_dom_def)
  have member: "()\<in>system_definitions ?P" by (simp add: definitions)
  have empty: "positive_meaning ?P={}"
    by (subst positive_meaning_unfold) (auto simp: schema_consequences_def admitted_schema_instance_def)
  obtain g :: "unit\<Rightarrow>local_address option definition_site" and E pu Q where compiled:
    "inj_on g (system_definitions ?P)" "closed_native_package_at E pu [] Q"
    "system_alpha_variant (rename_system g ?P) Q"
    "positive_meaning Q=image (map_prod g id) (positive_meaning ?P)"
    using program_compilation_total[OF formed] by blast
  have base_call: "\<And>t. schema_call_formed ?P () t\<longleftrightarrow>term_formed t"
    by (simp add: schema_call_formed_def formed)
  have boundary: "\<And>t. schema_call_formed Q (g ()) t\<longleftrightarrow>term_formed t"
    using compiled_system_call_boundary[OF formed compiled(1,3) member] by (simp only: base_call)
  have only: "system_definitions Q={g ()}"
    using compiled(3) by (simp add: system_alpha_variant_def renamed_system_definitions definitions)
  have refusal: "positive_meaning Q={}" using compiled(4) empty by simp
  show ?thesis using compiled(2) only boundary refusal by blast
qed

theorem constructed_successor_may_replace_program_by_refusal:
  assumes authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C G p E pu P d H X z E' qu Q e K F au R.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and>
    current_entry_scope_quoted_at X [] A l H z E' qu [] Q e \<and>
    generation_predecessors H={|G|} \<and> G\<noteq>H \<and> P\<noteq>Q \<and>
    (\<forall>t. term_formed t \<longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P) \<and>
    positive_meaning Q={} \<and> (\<forall>t. schema_call_formed Q e t\<longleftrightarrow>term_formed t) \<and>
    current_transition_dependencies_at C [] F au [] H K X \<and>
    certified_transition_dependencies C [] R [] H K X \<and> native_package_environment F pu []=E"
proof -
  obtain g :: "bool\<Rightarrow>local_address option definition_site" and E pu P where program:
    "inj g" "closed_native_package_at E pu [] P"
    "\<forall>b. g b\<in>system_definitions P \<and> amendment_permission_invariant P (g b) \<and>
      (\<forall>t. term_formed t \<longrightarrow> schema_call_formed P (g b) t \<and>
        ((g b,t)\<in>positive_meaning P\<longleftrightarrow>b))"
    using entry_choice_native_program by blast
  have members: "g True\<in>system_definitions P" "g False\<in>system_definitions P"
    and invariant: "amendment_permission_invariant P (g True)" using program(3) by blast+
  have different: "g True\<noteq>g False" using program(1) by (auto dest: injD)
  have every: "\<And>t. term_formed t \<Longrightarrow>
    schema_call_formed P (g True) t \<and> (g True,t)\<in>positive_meaning P"
    using program(3)[rule_format, of True] by blast
  obtain C G p where current: "current_entry_scope_quoted_at C [] A l G p E pu [] P (g True)"
    using current_entry_scope_construction[OF program(2) members(1) authority locus] by blast
  obtain E' :: "local_address option artifact_environment" and qu Q e
    where candidate: "closed_native_package_at E' qu [] Q"
    and only: "system_definitions Q={e}" and empty: "positive_meaning Q={}"
    and boundary: "\<forall>t. schema_call_formed Q e t\<longleftrightarrow>term_formed t"
    using single_refusing_native_program by blast
  have member: "e\<in>system_definitions Q" using only by simp
  have unequal: "P\<noteq>Q" using members different only by auto
  have package: "native_package_at E pu [] P" using program(2) by (simp add: closed_native_package_at_def)
  have ef: "environment_formed E" using native_package_projection(1)[OF package]
    by (simp add: native_package_formed_def)
  have site: "(pu,[])\<in>environment_positions E" by (rule native_package_root_position[OF package])
  obtain H X z K F au R where result:
    "generation_predecessors H={|G|}" "G\<noteq>H"
    "current_entry_scope_quoted_at X [] A l H z E' qu [] Q e"
    "current_transition_dependencies_at C [] F au [] H K X"
    "certified_transition_dependencies C [] R [] H K X" "native_package_environment F pu []=E"
    using universal_current_program_successor_total[
      OF current invariant every candidate member authority ef site] by blast
  show ?thesis using current result unequal every empty boundary by blast
qed

text \<open>
  The old current program is fixed before any future closed candidate program
  is supplied. The candidate's complete program quotation is a declared input
  to exact whole-source reuse. An old-program construction proof then gives
  the candidate its recorded cause and direct historical predecessor.

  Dependency permission records are obtained from that candidate before its
  publication is built. The publication selects the new generation and cites
  exactly the construction record and dependency records as whole targets.
  Its extra dependency selection is empty: the program dependencies already
  occur in the complete payload and permission subjects. The same records
  occur in the bound supporting material, and every dependency record is
  needed for its coverage. The exact publication belongs to the successor's
  actual currentness frame. It need not contain either later continuation or
  acceptance proof.

  The replacement changes the selected generation at its existing locus and
  preserves all other selections. Remaining formed material is included before
  continuation and acceptance are proved under the original program. Both
  complete old program identity and the original minimal acceptance scope
  survive certification.

  These are jointly inhabited components under an ordinary permissive policy.
  They even allow a different complete successor program whose interfaces
  admit every formed term while its meaning is empty. Their validity therefore
  proves neither semantic preservation nor adequate comparison, interpretation,
  or genesis checking. Those independent obligations remain necessary.
\<close>

end
