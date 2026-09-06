theory Factor_Proof_Table_Copy
  imports Factor_Table_Copy Factor_Proof_Tables
begin

section \<open>Physical table copies with unchanged metadata sites\<close>

lemma copy_fixed_binding_table:
  fixes E F :: "'u artifact_environment"
  assumes copy: "native_syntax_copy E u R F w S f g"
    and table: "native_binding_table_at E u r V I K"
    and fixed: "\<And>d. d\<in>rel_dom V \<Longrightarrow> g d=d"
  shows "native_binding_table_at F w (f r) V (image f I) (image f K)"
proof (rule native_syntax_copy.copy_fixed_table[OF copy table])
  fix a q J A assume row: "native_application_at E u a (fst q) (snd q) J A" and entry: "q\<in>V"
  have key: "fst q\<in>rel_dom V" using entry by (cases q) auto
  show "native_application_at F w (f a) (fst q) (snd q) (image f J) (image f A)"
    using native_syntax_copy.copy_application[OF copy row] fixed[OF key] by simp
next
  fix a q J A z L B
  assume first: "native_application_at F w a (fst q) (snd q) J A"
    and second: "native_application_at F w a (fst z) (snd z) L B"
  show "q=z \<and> J=L \<and> A=B"
    using native_application_unique[OF first second] by (auto intro: prod_eqI)
qed

lemma copy_fixed_discharge_table:
  fixes E F :: "'u artifact_environment"
  assumes copy: "native_syntax_copy E u R F w S f g"
    and table: "native_discharge_table_at E u r D I K"
    and fixed: "\<And>d. d\<in>rel_dom D\<union>rel_ran D \<Longrightarrow> g d=d"
  shows "native_discharge_table_at F w (f r) D (image f I) (image f K)"
proof (rule native_syntax_copy.copy_fixed_table[OF copy table])
  fix a q J A assume row: "native_site_link_at E u a (fst q) (snd q) J A" and entry: "q\<in>D"
  have key: "fst q\<in>rel_dom D\<union>rel_ran D" using entry by (cases q) auto
  have target: "snd q\<in>rel_dom D\<union>rel_ran D" using entry by (cases q) auto
  show "native_site_link_at F w (f a) (fst q) (snd q) (image f J) (image f A)"
    using native_syntax_copy.copy_site_link[OF copy row] fixed[OF key] fixed[OF target] by simp
next
  fix a q J A z L B
  assume first: "native_site_link_at F w a (fst q) (snd q) J A"
    and second: "native_site_link_at F w a (fst z) (snd z) L B"
  show "q=z \<and> J=L \<and> A=B"
    using native_site_link_unique[OF first second] by (auto intro: prod_eqI)
qed

section \<open>Compiled metadata tables recover inside larger records\<close>

lemma compiled_binding_table_embedded:
  fixes E :: "local_address option artifact_environment"
  assumes rf: "exact_formed R"
    and bounds: "rel_dom L\<union>rel_dom C \<subseteq> rra_carrier (object_structure R)"
    and recover: "\<And>F z. environment_formed F \<Longrightarrow> artifact_at F z R \<Longrightarrow>
      syntax_references F z L C \<Longrightarrow> native_binding_table_at F z r V I K"
    and dependencies: "rel_dom V\<subseteq>rel_ran C"
    and ef: "environment_formed E" and target: "artifact_at E u S" and injective: "inj f"
    and addressing: "finite_addressing (rra_carrier (object_structure R)) f"
    and reads: "object_reads_agree (push_object f R) S (image f (rra_carrier (object_structure R)))"
    and refs: "syntax_references E u (map_slot_keys f L) (map_slot_keys f C)"
  shows "native_binding_table_at E u (f r) V (image f I) (image f K)"
proof -
  let ?z = "clone_source_use E u"
  let ?F = "clone_source_environment E u R f ?z"
  have fresh: "?z\<notin>environment_uses E" by (rule clone_source_use_fresh[OF ef])
  have ff: "environment_formed ?F" by (rule clone_environment_formed[OF ef rf fresh])
  have source: "artifact_at ?F ?z R" by (simp add: clone_artifact_iff)
  have clone_refs: "syntax_references ?F ?z L C" by (rule cloned_syntax_references[OF ef fresh bounds refs])
  have original: "native_binding_table_at ?F ?z r V I K" by (rule recover[OF ff source clone_refs])
  have copy: "native_syntax_copy ?F ?z R E u S f (relocated_site ?z u f)"
    by (rule clone_environment_is_native_copy[OF ef rf fresh target injective addressing reads])
  have fixed: "\<And>d. d\<in>rel_dom V \<Longrightarrow> relocated_site ?z u f d=d"
  proof -
    fix d assume key: "d\<in>rel_dom V"
    have dependency: "d\<in>rel_ran C" using dependencies key by blast
    then obtain k where entry: "(k,d)\<in>C" by (auto simp: rel_ran_def)
    have outside: "fst d\<noteq>?z" by (rule cloned_reference_site_outside[OF ef fresh clone_refs entry])
    show "relocated_site ?z u f d=d" using outside by (cases d) simp
  qed
  show ?thesis by (rule copy_fixed_binding_table[OF copy original fixed])
qed

lemma compiled_discharge_table_embedded:
  fixes E :: "local_address option artifact_environment"
  assumes rf: "exact_formed R"
    and bounds: "rel_dom L\<union>rel_dom C \<subseteq> rra_carrier (object_structure R)"
    and recover: "\<And>F z. environment_formed F \<Longrightarrow> artifact_at F z R \<Longrightarrow>
      syntax_references F z L C \<Longrightarrow> native_discharge_table_at F z r D I K"
    and dependencies: "rel_dom D\<union>rel_ran D\<subseteq>rel_ran C"
    and ef: "environment_formed E" and target: "artifact_at E u S" and injective: "inj f"
    and addressing: "finite_addressing (rra_carrier (object_structure R)) f"
    and reads: "object_reads_agree (push_object f R) S (image f (rra_carrier (object_structure R)))"
    and refs: "syntax_references E u (map_slot_keys f L) (map_slot_keys f C)"
  shows "native_discharge_table_at E u (f r) D (image f I) (image f K)"
proof -
  let ?z = "clone_source_use E u"
  let ?F = "clone_source_environment E u R f ?z"
  have fresh: "?z\<notin>environment_uses E" by (rule clone_source_use_fresh[OF ef])
  have ff: "environment_formed ?F" by (rule clone_environment_formed[OF ef rf fresh])
  have source: "artifact_at ?F ?z R" by (simp add: clone_artifact_iff)
  have clone_refs: "syntax_references ?F ?z L C" by (rule cloned_syntax_references[OF ef fresh bounds refs])
  have original: "native_discharge_table_at ?F ?z r D I K" by (rule recover[OF ff source clone_refs])
  have copy: "native_syntax_copy ?F ?z R E u S f (relocated_site ?z u f)"
    by (rule clone_environment_is_native_copy[OF ef rf fresh target injective addressing reads])
  have fixed: "\<And>d. d\<in>rel_dom D\<union>rel_ran D \<Longrightarrow> relocated_site ?z u f d=d"
  proof -
    fix d assume key: "d\<in>rel_dom D\<union>rel_ran D"
    have dependency: "d\<in>rel_ran C" using dependencies key by blast
    then obtain k where entry: "(k,d)\<in>C" by (auto simp: rel_ran_def)
    have outside: "fst d\<noteq>?z" by (rule cloned_reference_site_outside[OF ef fresh clone_refs entry])
    show "relocated_site ?z u f d=d" using outside by (cases d) simp
  qed
  show ?thesis by (rule copy_fixed_discharge_table[OF copy original fixed])
qed

text \<open>
  Both metadata tables preserve their exact decoded relations under a private
  physical embedding. The destination's actual references establish that every
  metadata endpoint lies outside the temporary source use. Thus copying changes
  no binder site, term value, premise socket, or proof target. Formation and
  complete recovery remain independent of proof validity.
\<close>

end
