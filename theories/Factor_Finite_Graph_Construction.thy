theory Factor_Finite_Graph_Construction
  imports Factor_Finite_Graph_Installation
begin

definition finite_extend_native_graph where
  "finite_extend_native_graph E G root=(if finite_graph_construction_ready E G root then
    (let h=finite_graph_coordinates E G; H=finite_rename_graph h G in
      map_option (\<lambda>rows. (finite_install_graph_codes E rows,
        fimage (\<lambda>n. (n,h n)) (finite_graph_nodes G),h root,H)) (finite_compile_graph_nodes E H))
    else None)"

locale finite_graph_construction =
  fixes E :: "local_address option finite_artifact_environment"
    and G :: "(local_address option definition_site,local_address option definition_site,
      local_address option definition_site,'n::linorder) finite_derivation_graph"
    and root :: 'n
  assumes ready: "finite_graph_construction_ready E G root"
begin

abbreviation h where "h \<equiv> finite_graph_coordinates E G"
abbreviation placed where "placed \<equiv> finite_rename_graph h G"

lemma environment: "finite_environment_formed E"
  using ready by (simp only: finite_graph_construction_ready_def; blast)

lemma injective: "inj_on h (fset (finite_graph_nodes G))"
  by (rule finite_graph_coordinates_properties(1)[OF environment])

lemma placed_ready: "finite_graph_construction_ready E placed (h root)"
  by (rule finite_graph_coordinates_ready[OF ready])

lemma roots: "\<forall>n\<in>fset (finite_graph_nodes placed). snd n=[]"
  using finite_graph_coordinates_properties(2)[OF environment, of G]
  by (auto simp: finite_graph_renamed_nodes)

lemma fresh:
  "image fst (fset (finite_graph_nodes placed))\<inter>fset (finite_environment_uses E)={}"
  by (simp only: finite_graph_renamed_nodes fimage.rep_eq;
    rule finite_graph_coordinates_properties(3)[OF environment])

lemma codes_available: "\<exists>rows. finite_compile_graph_nodes E placed=Some rows"
  by (rule finite_compile_graph_nodes_total[OF placed_ready roots])

lemma installed:
  assumes compiled: "finite_compile_graph_nodes E placed=Some rows"
  shows "let F=finite_install_graph_codes E rows in
    finite_environment_formed F \<and>
    environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
    finite_environment_agrees_on E F (finite_environment_uses E) \<and>
    placed |\<in>| finite_native_graph_readings F (h root)"
  by (rule finite_install_graph_codes_correct[OF placed_ready roots fresh compiled])

end

theorem finite_extend_native_graph_domain:
  "(\<exists>F M r H. finite_extend_native_graph E G root=Some (F,M,r,H)) \<longleftrightarrow>
    finite_graph_construction_ready E G root"
proof
  assume "\<exists>F M r H. finite_extend_native_graph E G root=Some (F,M,r,H)"
  then show "finite_graph_construction_ready E G root"
    by (auto simp: finite_extend_native_graph_def split: if_splits)
next
  assume ready: "finite_graph_construction_ready E G root"
  interpret construction: finite_graph_construction E G root
    by (rule finite_graph_construction.intro[OF ready])
  obtain rows where compiled: "finite_compile_graph_nodes E construction.placed=Some rows"
    using construction.codes_available by blast
  show "\<exists>F M r H. finite_extend_native_graph E G root=Some (F,M,r,H)"
    by (simp add: finite_extend_native_graph_def ready Let_def compiled)
qed

theorem finite_extend_native_graph_correct:
  assumes extended: "finite_extend_native_graph E G root=Some (F,M,r,H)"
  shows "finite_graph_construction_ready E G root"
    "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "finite_environment_agrees_on E F (finite_environment_uses E)"
    "M=fimage (\<lambda>n. (n,finite_graph_coordinates E G n)) (finite_graph_nodes G)"
    "r=finite_graph_coordinates E G root"
    "H=finite_rename_graph (finite_graph_coordinates E G) G"
    "inj_on (finite_graph_coordinates E G) (fset (finite_graph_nodes G))"
    "image fst (fset (finite_graph_nodes H))\<inter>fset (finite_environment_uses E)={}"
    "H |\<in>| finite_native_graph_readings F r"
proof -
  have ready: "finite_graph_construction_ready E G root"
    using extended finite_extend_native_graph_domain[of E G root] by blast
  interpret construction: finite_graph_construction E G root
    by (rule finite_graph_construction.intro[OF ready])
  obtain rows where compiled: "finite_compile_graph_nodes E construction.placed=Some rows"
    and fields: "F=finite_install_graph_codes E rows"
      "M=fimage (\<lambda>n. (n,construction.h n)) (finite_graph_nodes G)"
      "r=construction.h root" "H=construction.placed"
    using extended by (auto simp: finite_extend_native_graph_def ready Let_def split: option.splits)
  show "finite_graph_construction_ready E G root" by (rule ready)
  show "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "finite_environment_agrees_on E F (finite_environment_uses E)"
    "H |\<in>| finite_native_graph_readings F r"
    using construction.installed[OF compiled] by (simp only: Let_def fields; blast)+
  show "M=fimage (\<lambda>n. (n,finite_graph_coordinates E G n)) (finite_graph_nodes G)"
    "r=finite_graph_coordinates E G root" "H=finite_rename_graph (finite_graph_coordinates E G) G"
    using fields by blast+
  show "inj_on (finite_graph_coordinates E G) (fset (finite_graph_nodes G))"
    by (rule construction.injective)
  show "image fst (fset (finite_graph_nodes H))\<inter>fset (finite_environment_uses E)={}"
    by (simp only: fields; rule construction.fresh)
qed

text \<open>
  The complete original source and graph determine availability. Every source
  node receives an explicit distinct fresh position, and the returned finite
  map retains that correspondence. The compiler and whole-family installer
  construct an actual extending environment whose native reader recovers the
  complete renamed graph. Unsupported original inputs return None.
  This constructs graph realization and does not establish inference claims,
  mathematical-proof admission, physical cost adequacy or genesis.
\<close>

end
