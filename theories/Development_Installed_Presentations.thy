theory Development_Installed_Presentations
  imports Development_Given_Extensions Factor_Varied_Constructions Development_Rooted_Registrations
begin

text \<open>
  V3 of DECISIONS.md "A checker does not produce", its addition "Registrations and declarations reach an installed
  package by matching its clauses against the placed ones" (task 642), its general part (task 653): for every program
  extending the given's readers (@{text given_readers_extension}), the finite program the native package reader
  returns at the installed environment and site (@{const finite_native_package_readings}), which is the program the
  machinery evaluates there. The installed program is read, never written beside it: the presentation is the reader's
  output, decoding to the installed package (@{text installed_presentation_exact}). A construction complete at the
  numbered program is relocated to the placed program by the installation's placement and varied to the presentation
  by matching clauses (V1), and is complete there; completeness is discharged at the numbered program from its
  meanings and carried only by relocation and variation. The installation's alpha variance, proved once, is consumed
  as the verification that the placed and the installed presentations agree, never in place of evaluating the
  installed one: the native exact form resolves the presentation itself.
\<close>

context given_readers_extension
begin

section \<open>The installed package as the native reader returns it\<close>

definition installed_presentation :: "local_address option finite_native_system" where
  "installed_presentation=(THE R. R |\<in>| finite_native_package_readings installed_environment installed_use [])"

text \<open>The installation's result, at the installed environment and site.\<close>

lemma installed_built:
  "finite_extend_mapped_native given_environment finite_rooted_given_readers Q given_readers_placement=
    Some (installed_environment,installed_use)"
  using built unfolding installed_environment_def installed_use_def by simp

theorem installed_presentation_exact:
  "installed_presentation |\<in>| finite_native_package_readings installed_environment installed_use []"
  "\<And>R. R |\<in>| finite_native_package_readings installed_environment installed_use [] \<Longrightarrow> R=installed_presentation"
  "decode_finite_system installed_presentation=installed_program"
proof -
  obtain F where F: "F |\<in>| finite_native_package_readings installed_environment installed_use []"
      "decode_finite_system F=installed_program"
    using finite_native_package_readings_complete[OF installation(6)] by blast
  have unique: "\<And>R. R |\<in>| finite_native_package_readings installed_environment installed_use [] \<Longrightarrow> R=F"
    by (rule finite_native_package_readings_unique[OF _ F(1)])
  have same: "installed_presentation=F" unfolding installed_presentation_def
    by (rule the_equality[where P="\<lambda>R. R |\<in>| finite_native_package_readings installed_environment installed_use []",
      OF F(1) unique])
  show "installed_presentation |\<in>| finite_native_package_readings installed_environment installed_use []"
    using F(1) same by simp
  show "\<And>R. R |\<in>| finite_native_package_readings installed_environment installed_use [] \<Longrightarrow> R=installed_presentation"
    using unique same by simp
  show "decode_finite_system installed_presentation=installed_program" using F(2) same by simp
qed

lemma installed_presentation_read:
  "native_package_at (decode_finite_environment installed_environment) installed_use []
    (decode_finite_system installed_presentation)"
  using installation(6) by (simp only: installed_presentation_exact(3))

lemma installed_presentation_variant:
  "system_alpha_variant (decode_finite_system (finite_rename_system installed_placement Q))
    (decode_finite_system installed_presentation)"
  by (rule install.installed_variant[OF installed_built installed_presentation_read, folded installed_placement_def])

lemma installed_presentation_formed:
  "finite_system_formed installed_presentation"
  "finite_system_formed (finite_rename_system installed_placement Q)"
  using installed_presentation_variant unfolding system_alpha_variant_def finite_system_formed_correct by simp_all

section \<open>A complete construction, relocated and varied to the presentation\<close>

text \<open>
  A construction over the numbered program is relocated by the installation's placement (the relocated
  construction's own site map, @{const finite_relocated_construction}) and varied from the placed program to the
  presentation (@{const finite_varied_construction}): its values are produced over the placed program and checked by
  the installed clauses.
\<close>

definition installed_construction ::
    "(nat,nat,nat,nat) finite_witness_construction \<Rightarrow>
      (local_address,local_address,local_address option definition_site,local_address) finite_witness_construction" where
  "installed_construction \<kappa>=finite_varied_construction (finite_rename_system installed_placement Q)
    installed_presentation (finite_relocated_construction installed_placement Q \<kappa>)"

lemma installed_construction_formed:
  assumes "finite_witness_construction_formed \<kappa>"
  shows "finite_witness_construction_formed (installed_construction \<kappa>)"
  unfolding installed_construction_def
  by (rule finite_varied_construction_formed[OF finite_relocated_construction_formed[OF assms]])

theorem installed_construction_complete:
  assumes complete: "finite_construction_complete \<kappa> Q"
  shows "finite_construction_complete (installed_construction \<kappa>) installed_presentation"
  unfolding installed_construction_def
  by (rule install.varied_relocated_complete[OF installed_built installed_presentation_read complete,
    folded installed_placement_def])

text \<open>
  Every variable a relocated registration names within its placed clause's scope is registered at an installed
  clause at the same site, the one the match sends the placed clause to, at its image under the match's binder map.
\<close>

theorem installed_registration_reaches:
  assumes clause: "((d,c),S) |\<in>| finite_system_clauses (finite_rename_system installed_placement Q)"
    and registered: "x |\<in>| witness_registered (finite_relocated_construction installed_placement Q \<kappa>) d S"
      "x |\<in>| finite_schema_variables S"
  shows "\<exists>c' T f h. ((d,c'),T) |\<in>| finite_system_clauses installed_presentation \<and> finite_schema_match S T=Some (f,h) \<and>
    f x |\<in>| witness_registered (installed_construction \<kappa>) d T"
proof -
  note variant=installed_presentation_variant
  have family: "(c,decode_finite_schema S)\<in>system_clause_family (decode_finite_system
      (finite_rename_system installed_placement Q)) d"
    using clause by (auto simp del: finite_rename_system_correct)
  then have member: "((d,c),decode_finite_schema S)\<in>system_clauses (decode_finite_system
      (finite_rename_system installed_placement Q))"
    unfolding system_clause_family_def by (auto simp del: finite_rename_system_correct)
  have defined: "d\<in>system_definitions (decode_finite_system (finite_rename_system installed_placement Q))"
    using variant member unfolding system_alpha_variant_def schema_system_formed_def by blast
  obtain k where k: "schema_family_variant k
      (system_clause_family (decode_finite_system (finite_rename_system installed_placement Q)) d)
      (system_clause_family (decode_finite_system installed_presentation) d)"
    using variant defined unfolding system_alpha_variant_def by blast
  show ?thesis unfolding installed_construction_def
    by (rule finite_varied_registered_variant[OF installed_presentation_formed(2,1) k clause registered])
qed

section \<open>The native exact form at the presentation\<close>

text \<open>
  R5's committed resolution at no commitment over the installed construction and the presentation: every requested
  call is answered, a resolved call holds in the installed program with checked certificates, a refuted one does
  not, and a demand's answer is exactly the requested calls the installed program holds.
\<close>

theorem installed_resolution_exact:
  assumes formed: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> Q"
    and result: "native_committed_resolution (installed_construction \<kappa>) no_commitment installed_presentation R n=(T,A)"
  shows "fimage fst T=R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C\<noteq>{||} \<and>
      fBall C (\<lambda>p. finite_checks_schema_proof installed_presentation p (fst q) (snd q)) \<and>
      decode_finite_call_term q\<in>positive_meaning installed_program"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow> decode_finite_call_term q\<notin>positive_meaning installed_program"
    and "A=Some B \<Longrightarrow> schema_system_formed installed_program \<and>
      fset B={q\<in>fset R. decode_finite_call_term q\<in>positive_meaning installed_program}"
proof -
  note e=install.native_varied_relocated_resolution_exact[OF formed installed_built installed_presentation_read complete,
    folded installed_placement_def, OF result[unfolded installed_construction_def], unfolded installed_presentation_exact(3)]
  show "fimage fst T=R" by (rule e(1))
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C\<noteq>{||} \<and>
      fBall C (\<lambda>p. finite_checks_schema_proof installed_presentation p (fst q) (snd q)) \<and>
      decode_finite_call_term q\<in>positive_meaning installed_program"
    by (rule e(2))
  show "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow> decode_finite_call_term q\<notin>positive_meaning installed_program"
    by (rule e(3))
  show "A=Some B \<Longrightarrow> schema_system_formed installed_program \<and>
      fset B={q\<in>fset R. decode_finite_call_term q\<in>positive_meaning installed_program}"
    by (rule e(4))
qed

text \<open>
  At an installed entry, the placement of a definition of the numbered program, the answer is that definition's
  meaning in the numbered program (@{thm [source] installed_meaning}).
\<close>

corollary installed_entry_exact:
  assumes formed: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> Q"
    and result: "native_committed_resolution (installed_construction \<kappa>) no_commitment installed_presentation R n=(T,A)"
    and defined: "d\<in>system_definitions (decode_finite_system Q)"
  shows "((installed_placement d,t),Finite_Resolved C) |\<in>| T \<Longrightarrow>
      (d,decode_finite_term t)\<in>positive_meaning (decode_finite_system Q)"
    and "((installed_placement d,t),r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      (d,decode_finite_term t)\<notin>positive_meaning (decode_finite_system Q)"
proof -
  have call: "decode_finite_call_term (installed_placement d,t)=(installed_placement d,decode_finite_term t)"
    by (simp add: decode_finite_call_term_fields)
  show "((installed_placement d,t),Finite_Resolved C) |\<in>| T \<Longrightarrow>
      (d,decode_finite_term t)\<in>positive_meaning (decode_finite_system Q)"
    using installed_resolution_exact(2)[OF formed complete result] installed_meaning[OF defined] call by metis
  show "((installed_placement d,t),r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      (d,decode_finite_term t)\<notin>positive_meaning (decode_finite_system Q)"
    using installed_resolution_exact(3)[OF formed complete result] installed_meaning[OF defined] call by metis
qed

end

section \<open>The given's own installation\<close>

text \<open>
  V3's given part (task 655): the given's readers' own installation is the closed installation of the rooted readers
  over the empty package (@{text given_installation}, a @{text closed_program_installation}), whose mapped extension
  (@{text given_installation.install}) places them by @{const given_readers_placement}. Its presentation is the program
  the native package reader returns at @{const given_readers_installed}, decoding to @{const given_readers_program}.
  The construction complete at the rooted readers (@{thm [source] given_rooted_construction_complete}, discharged there
  from their meanings) is relocated by the placement and varied to that presentation, and is complete there: nothing
  is proved again at the placed or the installed program.
\<close>

lemma given_readers_built_pair:
  "finite_extend_mapped_native (fst given_readers_source) empty_installation_program finite_rooted_given_readers
    (\<lambda>_. (None,[]))=Some (fst given_readers_installed,snd given_readers_installed)"
  using given_readers_built by simp

text \<open>
  The installation's mapped extension, as @{text closed_program_installation} proves it at the given's installation
  (@{text given_installation.install}); the facts the varied constructions add to that locale are taken through it.
\<close>

lemma given_readers_mapped_extension:
  "finite_mapped_native_extension (fst given_readers_source) empty_installation_program finite_rooted_given_readers
    (snd given_readers_source) [] \<lparr>system_interfaces={},system_clauses={}\<rparr> (\<lambda>_. (None,[]))"
  by (rule given_installation.install.finite_mapped_native_extension_axioms)

lemma given_install_placement:
  "finite_program_coordinates (fst given_readers_source) (finite_system_definitions empty_installation_program)
    (finite_system_definitions finite_rooted_given_readers) (\<lambda>_. (None,[]))=given_readers_placement"
  by (simp add: given_readers_placement_def)

definition given_installed_presentation :: "local_address option finite_native_system" where
  "given_installed_presentation=(THE R. R |\<in>| finite_native_package_readings (fst given_readers_installed)
    (snd given_readers_installed) [])"

theorem given_installed_presentation_exact:
  "given_installed_presentation |\<in>| finite_native_package_readings (fst given_readers_installed)
    (snd given_readers_installed) []"
  "\<And>R. R |\<in>| finite_native_package_readings (fst given_readers_installed) (snd given_readers_installed) [] \<Longrightarrow>
    R=given_installed_presentation"
  "decode_finite_system given_installed_presentation=given_readers_program"
proof -
  obtain F where F: "F |\<in>| finite_native_package_readings (fst given_readers_installed) (snd given_readers_installed) []"
      "decode_finite_system F=given_readers_program"
    using finite_native_package_readings_complete[OF given_readers_compilation(1)] by blast
  have unique: "\<And>R. R |\<in>| finite_native_package_readings (fst given_readers_installed) (snd given_readers_installed) [] \<Longrightarrow>
      R=F"
    by (rule finite_native_package_readings_unique[OF _ F(1)])
  have same: "given_installed_presentation=F" unfolding given_installed_presentation_def
    by (rule the_equality[where P="\<lambda>R. R |\<in>| finite_native_package_readings (fst given_readers_installed)
      (snd given_readers_installed) []", OF F(1) unique])
  show "given_installed_presentation |\<in>| finite_native_package_readings (fst given_readers_installed)
      (snd given_readers_installed) []"
    using F(1) same by simp
  show "\<And>R. R |\<in>| finite_native_package_readings (fst given_readers_installed) (snd given_readers_installed) [] \<Longrightarrow>
      R=given_installed_presentation"
    using unique same by simp
  show "decode_finite_system given_installed_presentation=given_readers_program" using F(2) same by simp
qed

lemma given_installed_presentation_read:
  "native_package_at (decode_finite_environment (fst given_readers_installed)) (snd given_readers_installed) []
    (decode_finite_system given_installed_presentation)"
  using given_readers_compilation(1) by (simp only: given_installed_presentation_exact(3))

lemma given_installed_presentation_variant:
  "system_alpha_variant (decode_finite_system (finite_rename_system given_readers_placement finite_rooted_given_readers))
    (decode_finite_system given_installed_presentation)"
  by (rule finite_mapped_native_extension.installed_variant[OF given_readers_mapped_extension given_readers_built_pair
    given_installed_presentation_read, unfolded given_install_placement])

lemma given_installed_presentation_formed:
  "finite_system_formed given_installed_presentation"
  "finite_system_formed (finite_rename_system given_readers_placement finite_rooted_given_readers)"
  using given_installed_presentation_variant unfolding system_alpha_variant_def finite_system_formed_correct by simp_all

section \<open>The given's construction, relocated and varied to its presentation\<close>

definition given_installed_construction where
  "given_installed_construction n=finite_varied_construction
    (finite_rename_system given_readers_placement finite_rooted_given_readers) given_installed_presentation
    (finite_relocated_construction given_readers_placement finite_rooted_given_readers
      (finite_collection_construction given_witness_registrations n))"

lemma given_installed_construction_formed:
  "finite_witness_construction_formed (given_installed_construction n)"
  unfolding given_installed_construction_def
  by (rule finite_varied_construction_formed[OF finite_relocated_construction_formed[OF
    finite_collection_construction_formed]])

theorem given_installed_construction_complete:
  "finite_construction_complete (given_installed_construction n) given_installed_presentation"
  unfolding given_installed_construction_def
  by (rule finite_mapped_native_extension.varied_relocated_complete[OF given_readers_mapped_extension
    given_readers_built_pair given_installed_presentation_read given_rooted_construction_complete,
    unfolded given_install_placement])

section \<open>The native exact form at the given's presentation\<close>

theorem given_installed_resolution_exact:
  assumes result: "native_committed_resolution (given_installed_construction n) no_commitment given_installed_presentation
      R m=(T,A)"
  shows "fimage fst T=R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C\<noteq>{||} \<and>
      fBall C (\<lambda>p. finite_checks_schema_proof given_installed_presentation p (fst q) (snd q)) \<and>
      decode_finite_call_term q\<in>positive_meaning given_readers_program"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q\<notin>positive_meaning given_readers_program"
    and "A=Some B \<Longrightarrow> schema_system_formed given_readers_program \<and>
      fset B={q\<in>fset R. decode_finite_call_term q\<in>positive_meaning given_readers_program}"
proof -
  note e=finite_mapped_native_extension.native_varied_relocated_resolution_exact[OF given_readers_mapped_extension
    finite_collection_construction_formed given_readers_built_pair given_installed_presentation_read given_rooted_construction_complete,
    unfolded given_install_placement, OF result[unfolded given_installed_construction_def],
    unfolded given_installed_presentation_exact(3)]
  show "fimage fst T=R" by (rule e(1))
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C\<noteq>{||} \<and>
      fBall C (\<lambda>p. finite_checks_schema_proof given_installed_presentation p (fst q) (snd q)) \<and>
      decode_finite_call_term q\<in>positive_meaning given_readers_program"
    by (rule e(2))
  show "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q\<notin>positive_meaning given_readers_program"
    by (rule e(3))
  show "A=Some B \<Longrightarrow> schema_system_formed given_readers_program \<and>
      fset B={q\<in>fset R. decode_finite_call_term q\<in>positive_meaning given_readers_program}"
    by (rule e(4))
qed

text \<open>
  At an installed reader, the placement of a rooted reader d, the answer is d's meaning in the rooted readers
  (@{thm [source] given_installed_meaning}); at an entry, its meaning in the joined program
  (@{thm [source] given_installed_entry_meaning}).
\<close>

corollary given_installed_exact:
  assumes result: "native_committed_resolution (given_installed_construction n) no_commitment given_installed_presentation
      R m=(T,A)"
    and defined: "d\<in>system_definitions given_rooted_readers_system"
  shows "((given_readers_placement d,t),Finite_Resolved C) |\<in>| T \<Longrightarrow>
      (d,decode_finite_term t)\<in>positive_meaning given_rooted_readers_system"
    and "((given_readers_placement d,t),r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      (d,decode_finite_term t)\<notin>positive_meaning given_rooted_readers_system"
proof -
  have call: "decode_finite_call_term (given_readers_placement d,t)=(given_readers_placement d,decode_finite_term t)"
    by (simp add: decode_finite_call_term_fields)
  show "((given_readers_placement d,t),Finite_Resolved C) |\<in>| T \<Longrightarrow>
      (d,decode_finite_term t)\<in>positive_meaning given_rooted_readers_system"
    using given_installed_resolution_exact(2)[OF result] given_installed_meaning[OF defined] call by metis
  show "((given_readers_placement d,t),r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      (d,decode_finite_term t)\<notin>positive_meaning given_rooted_readers_system"
    using given_installed_resolution_exact(3)[OF result] given_installed_meaning[OF defined] call by metis
qed

corollary given_installed_entry_exact:
  assumes result: "native_committed_resolution (given_installed_construction n) no_commitment given_installed_presentation
      R m=(T,A)"
    and entry: "d|\<in>|given_reader_entries"
  shows "((given_readers_placement d,t),Finite_Resolved C) |\<in>| T \<Longrightarrow>
      (d,decode_finite_term t)\<in>positive_meaning given_program_system"
    and "((given_readers_placement d,t),r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      (d,decode_finite_term t)\<notin>positive_meaning given_program_system"
  using given_installed_exact[OF result given_entry_rooted[OF entry]]
    given_installed_meaning[OF given_entry_rooted[OF entry]] given_installed_entry_meaning[OF entry] by blast+

end
