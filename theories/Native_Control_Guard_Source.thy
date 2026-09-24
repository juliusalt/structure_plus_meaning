theory Native_Control_Guard_Source
  imports Native_Control_Installed_Guard Factor_Finite_Native_Sources
begin

definition guard_installation_coordinates where
  "guard_installation_coordinates E xs =
    finite_program_coordinates (fst (finite_select_roots E []))
      (finite_system_definitions (empty_installation_program::(nat,nat,nat,nat) finite_schema_system))
      (finite_system_definitions (finite_guard_constructor xs)) (\<lambda>_. (None,[]))"

theorem finite_install_quoted_guard_transport:
  assumes installed: "finite_install_quoted_guard E xs=Some (d,K,v)"
  obtains P where "finite_native_source K v []=Some P"
    "d=guard_installation_coordinates E xs 369"
    "inj_on (guard_installation_coordinates E xs)
      (fset (finite_system_definitions (finite_guard_constructor xs)))"
    "system_alpha_variant
      (rename_system (guard_installation_coordinates E xs)
        (decode_finite_system (finite_guard_constructor xs))) (decode_finite_system P)"
proof -
  obtain F u where selected: "finite_select_roots E []=(F,u)"
    by (cases "finite_select_roots E []") auto
  have environment: "finite_environment_formed E"
    and rows: "list_all finite_term_formed xs"
    and entry: "d=guard_installation_coordinates E xs 369"
    and built: "finite_extend_mapped_native F empty_installation_program
      (finite_guard_constructor xs) (\<lambda>_. (None,[]))=Some (K,v)"
    using installed by (auto simp: finite_install_quoted_guard_def
      guard_installation_coordinates_def selected Let_def split: if_splits option.splits)
  interpret install: finite_guard_installation xs E F u
    by (unfold_locales) (rule rows, rule environment, rule selected)
  have built': "finite_extend_mapped_native F empty_installation_program
      (finite_quoted_judgment xs) (\<lambda>_. (None,[]))=Some (K,v)"
    using built by (simp only: install.finite_guard_constructor_representation)
  obtain T where native: "native_package_at (decode_finite_environment K) v [] T"
    and injective: "inj_on install.placement (system_definitions install.artifact_system)"
    and variant: "system_alpha_variant (rename_system install.placement install.artifact_system) T"
    by (rule install.installed_guard[OF built']) blast
  have available: "finite_native_source K v []\<noteq>None"
    using native by (simp only: finite_native_source_absent) blast
  obtain P where source: "finite_native_source K v []=Some P"
    using available by (cases "finite_native_source K v []") auto
  have package: "native_package_at (decode_finite_environment K) v [] (decode_finite_system P)"
    using source by (simp only: finite_native_source_correct)
  have same: "T=decode_finite_system P"
    by (rule native_package_unique[OF native package])
  have coordinates: "guard_installation_coordinates E xs=install.placement"
    by (simp only: guard_installation_coordinates_def selected fst_conv
      install.finite_guard_constructor_representation)
  have program: "decode_finite_system (finite_guard_constructor xs)=install.artifact_system"
    by (rule finite_guard_constructor_exact)
  have transported_injection: "inj_on (guard_installation_coordinates E xs)
      (fset (finite_system_definitions (finite_guard_constructor xs)))"
    using injective by (simp only: coordinates finite_system_definitions_correct program)
  have transported_variant: "system_alpha_variant
      (rename_system (guard_installation_coordinates E xs)
        (decode_finite_system (finite_guard_constructor xs))) (decode_finite_system P)"
    using variant by (simp only: coordinates program same)
  show thesis by (rule that[OF source entry transported_injection transported_variant])
qed

ML \<open>val _ = (writeln "SOURCE_TRANSPORT_JOIN_BEGIN";
  Thm.consolidate [@{thm finite_install_quoted_guard_transport}];
  writeln "SOURCE_TRANSPORT_JOIN_END");\<close>

definition finite_install_quoted_guard_source where
  "finite_install_quoted_guard_source E xs =
    (case finite_install_quoted_guard E xs of None \<Rightarrow> None
    | Some (d,K,v) \<Rightarrow> map_option (\<lambda>P. (d,K,v,P)) (finite_native_source K v []))"

lemma finite_install_quoted_guard_source_fields:
  "finite_install_quoted_guard_source E xs=Some (d,K,v,P) \<longleftrightarrow>
    finite_install_quoted_guard E xs=Some (d,K,v) \<and> finite_native_source K v []=Some P"
  by (auto simp: finite_install_quoted_guard_source_def split: option.splits prod.splits)

ML \<open>val _ = (writeln "SOURCE_FIELDS_JOIN_BEGIN";
  Thm.consolidate [@{thm finite_install_quoted_guard_source_fields}];
  writeln "SOURCE_FIELDS_JOIN_END");\<close>

theorem finite_install_quoted_guard_source_total:
  assumes installed: "finite_install_quoted_guard E xs=Some (d,K,v)"
  shows "\<exists>P. finite_install_quoted_guard_source E xs=Some (d,K,v,P)"
  by (rule finite_install_quoted_guard_transport[OF installed])
    (use installed in \<open>auto simp only: finite_install_quoted_guard_source_fields\<close>)

ML \<open>val _ = (writeln "SOURCE_TOTAL_JOIN_BEGIN";
  Thm.consolidate [@{thm finite_install_quoted_guard_source_total}];
  writeln "SOURCE_TOTAL_JOIN_END");\<close>

text \<open>The original reader returns the complete actual installed source.
  The injection concerns definition sites. The source is an alpha variant of the
  renamed original target; natural clause, variable and socket coordinates are
  not thereby native coordinates. Proof-tree transport is a separate obligation.
  No source value is supplied by an existence flag or a digest.\<close>

end
