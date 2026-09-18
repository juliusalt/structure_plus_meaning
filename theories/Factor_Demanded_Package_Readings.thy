theory Factor_Demanded_Package_Readings
  imports Finite_Demanded_Closures Factor_Recovered_Graph_Sharing Factor_Formation_Once_Definitions
begin

section \<open>A package reads a definition only where its roots demand one\<close>

text \<open>
  A native package is the definitions its root family reaches through the callees of their
  clauses. Both readings of it, the reached sites and the graph of their definitions, were
  computed from the rows of the whole environment: a definition was read at every position
  of every artifact, including every address of a literal target that carries no definition
  at all. The cost of reading one package therefore grew with the material beside it, which
  is what made reading a recorded cause back superlinear in the size of its payload.

  The traversal of Finite_Demanded_Closures reads a definition only at a site a root
  reaches. Its premise here is that a site with a definition reading is a position of the
  environment, which the existing definition grammar already establishes: a definition is
  read from a record of the artifact at its use, so its root address belongs to that
  artifact's carrier. Both readings keep their original values.
\<close>

definition finite_definition_site_reading ::
  "'u finite_artifact_environment \<Rightarrow> 'u definition_site \<Rightarrow> 'u finite_native_definition fset" where
  "finite_definition_site_reading E d=finite_native_definition_readings E (fst d) (snd d)"

definition finite_definition_dependencies ::
  "'u finite_native_definition \<Rightarrow> 'u definition_site fset" where
  "finite_definition_dependencies q=
    ffUnion (fimage (\<lambda>(c,S). finite_schema_dependencies S) (snd q))"

lemma finite_definition_dependencies_member:
  "e |\<in>| finite_definition_dependencies (p,F) \<longleftrightarrow>
    (\<exists>c S. (c,S) |\<in>| F \<and> e |\<in>| finite_schema_dependencies S)"
  by (auto simp: finite_definition_dependencies_def finite_union_image_member
      split_paired_Ex prod.case_eq_if; force)

lemma finite_definition_reading_position:
  assumes reading: "x |\<in>| finite_definition_site_reading E d"
  shows "d |\<in>| finite_environment_positions E"
proof -
  obtain q F where shape: "x=(q,F)" by (cases x) auto
  have member: "(q,F) |\<in>| finite_native_definition_readings E (fst d) (snd d)"
    using reading shape by (simp add: finite_definition_site_reading_def)
  have read: "native_definition_at (decode_finite_environment E) (fst d) (snd d)
      (decode_finite_pattern q) (map_relation_values decode_finite_schema (fset F))"
    using member by (simp add: finite_native_definition_readings_correct)
  have position: "(fst d,snd d) \<in> environment_positions (decode_finite_environment E)"
    by (rule native_definition_position[OF read])
  show ?thesis using position by (simp add: finite_environment_positions_correct)
qed

lemma finite_definition_reading_universe:
  "finite_definition_site_reading E d \<noteq> {||} \<Longrightarrow> d |\<in>| finite_environment_positions E"
  using finite_definition_reading_position by (metis all_not_fin_conv)

lemma finite_native_definition_rows_site_rows:
  "finite_native_definition_rows E=
    finite_site_rows (finite_definition_site_reading E) (finite_environment_positions E)"
  by (simp only: finite_native_definition_rows_def finite_site_rows_def
      finite_definition_site_reading_def)

lemma finite_native_definition_edges_row_edges:
  fixes E :: "'u finite_artifact_environment"
  shows "finite_native_definition_edges E=
    finite_row_edges (finite_definition_site_reading E) finite_definition_dependencies
      (finite_environment_positions E)"
proof (rule fset_eqI)
  fix z :: "'u definition_site \<times> 'u definition_site"
  obtain d e where shape: "z=(d,e)" by (cases z) auto
  have left: "(d,e) |\<in>| finite_native_definition_edges E \<longleftrightarrow>
      (\<exists>p F c S. (d,p,F) |\<in>| finite_native_definition_rows E \<and>
        (c,S) |\<in>| F \<and> e |\<in>| finite_schema_dependencies S)"
    by (rule finite_native_definition_edges_member)
  have right: "(d,e) |\<in>| finite_row_edges (finite_definition_site_reading E)
        finite_definition_dependencies (finite_environment_positions E) \<longleftrightarrow>
      (\<exists>x. d |\<in>| finite_environment_positions E \<and> x |\<in>| finite_definition_site_reading E d \<and>
        e |\<in>| finite_definition_dependencies x)"
    by (rule finite_row_edges_member)
  show "z |\<in>| finite_native_definition_edges E \<longleftrightarrow>
      z |\<in>| finite_row_edges (finite_definition_site_reading E) finite_definition_dependencies
        (finite_environment_positions E)"
    using finite_definition_reading_position
    by (auto simp: shape left right finite_native_definition_rows_site_rows
        finite_site_rows_member finite_definition_dependencies_member split_paired_Ex)
qed

lemma finite_definition_rows_at_sites:
  fixes E :: "'u finite_artifact_environment"
  shows "ffilter (\<lambda>(d,p,F). d |\<in>| sites) (finite_native_definition_rows E)=
    finite_site_rows (finite_definition_site_reading E) sites"
proof (rule fset_eqI)
  fix z :: "'u definition_site \<times> 'u finite_native_definition"
  obtain d q F where shape: "z=(d,q,F)" by (cases z) auto
  have position: "d |\<in>| finite_environment_positions E"
    if "(q,F) |\<in>| finite_definition_site_reading E d"
    by (rule finite_definition_reading_position[OF that])
  show "z |\<in>| ffilter (\<lambda>(d,p,F). d |\<in>| sites) (finite_native_definition_rows E) \<longleftrightarrow>
      z |\<in>| finite_site_rows (finite_definition_site_reading E) sites"
    using position
    by (auto simp: shape finite_native_definition_rows_site_rows finite_site_rows_member)
qed

section \<open>The demanded traversal returns both readings unchanged\<close>

lemma finite_demanded_definition_readings:
  "finite_demanded_readings (finite_definition_site_reading E) finite_definition_dependencies roots=
    Some (finite_native_definition_sites E roots,finite_native_definition_graph E roots)"
proof -
  let ?read="finite_definition_site_reading E"
  let ?succ="finite_definition_dependencies"
  let ?U="finite_environment_positions E"
  have sites: "finite_rooted_sites ?read ?succ ?U roots=finite_native_definition_sites E roots"
    by (simp only: finite_rooted_sites_def finite_native_definition_sites_def
        finite_native_definition_edges_row_edges)
  have graph: "finite_site_rows ?read (finite_native_definition_sites E roots)=
      finite_native_definition_graph E roots"
    by (simp only: finite_native_definition_graph_def finite_definition_rows_at_sites)
  have run: "finite_demanded_readings ?read ?succ roots=
      Some (finite_rooted_sites ?read ?succ ?U roots,
        finite_site_rows ?read (finite_rooted_sites ?read ?succ ?U roots))"
    by (rule finite_demanded_readings_exact[OF finite_definition_reading_universe])
  show ?thesis using run by (simp only: sites graph)
qed

text \<open>
  A formed environment has formed artifacts, so the readings of a site consume the
  formation-free bodies of Factor_Formation_Once_Definitions. The traversal
  checks the environment once, where the universe formulation checked it once for the
  whole row table; checking it at every site read would restore the growth with the
  material beside the package. An unformed environment reads nothing, so its package is
  its roots and its graph is empty.
\<close>

definition finite_definition_site_reading_formed ::
  "'u finite_artifact_environment \<Rightarrow> 'u definition_site \<Rightarrow> 'u finite_native_definition fset" where
  "finite_definition_site_reading_formed E d=finite_native_definition_readings_formed E (fst d) (snd d)"

lemma finite_definition_site_reading_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_definition_site_reading_formed E=finite_definition_site_reading E"
  by (rule ext)
    (simp add: finite_definition_site_reading_formed_def finite_definition_site_reading_def
      finite_native_definition_readings_formed_exact[OF formed])

lemma finite_demanded_definition_readings_formed:
  assumes formed: "finite_environment_formed E"
  shows "finite_demanded_readings (finite_definition_site_reading_formed E)
      finite_definition_dependencies roots=
    Some (finite_native_definition_sites E roots,finite_native_definition_graph E roots)"
  by (simp only: finite_definition_site_reading_formed_exact[OF formed]
      finite_demanded_definition_readings)

lemma finite_native_definition_rows_unformed:
  assumes unformed: "\<not> finite_environment_formed E"
  shows "finite_native_definition_rows E={||}"
  using unformed by (simp add: finite_native_definition_rows_formed_definitions_code)

lemma finite_native_definition_sites_unformed:
  assumes unformed: "\<not> finite_environment_formed E"
  shows "finite_native_definition_sites E roots=roots"
proof -
  have edges: "finite_native_definition_edges E={||}"
    by (simp add: finite_native_definition_edges_def finite_native_definition_rows_unformed[OF unformed])
  show ?thesis
    by (auto simp: finite_native_definition_sites_def edges fset_eq_iff ffilter.rep_eq
        fimage.rep_eq bot_fset.rep_eq sup_fset.rep_eq)
qed

lemma finite_native_definition_graph_unformed:
  assumes unformed: "\<not> finite_environment_formed E"
  shows "finite_native_definition_graph E roots={||}"
  by (auto simp: finite_native_definition_graph_def fset_eq_iff ffilter.rep_eq bot_fset.rep_eq
      finite_native_definition_rows_unformed[OF unformed])

declare finite_native_definition_sites_def[code del]
declare Factor_Recovered_Graph_Sharing.finite_native_definition_graph_shared_code[code del]

lemma finite_native_definition_sites_demanded_code [code]:
  "finite_native_definition_sites E roots=(if finite_environment_formed E
    then fst (the (finite_demanded_readings (finite_definition_site_reading_formed E)
      finite_definition_dependencies roots))
    else roots)"
proof (cases "finite_environment_formed E")
  case True
  show ?thesis by (simp add: True finite_demanded_definition_readings_formed[OF True])
next
  case False
  show ?thesis by (simp add: False finite_native_definition_sites_unformed[OF False])
qed

lemma finite_native_definition_graph_demanded_code [code]:
  "finite_native_definition_graph E roots=(if finite_environment_formed E
    then snd (the (finite_demanded_readings (finite_definition_site_reading_formed E)
      finite_definition_dependencies roots))
    else {||})"
proof (cases "finite_environment_formed E")
  case True
  show ?thesis by (simp add: True finite_demanded_definition_readings_formed[OF True])
next
  case False
  show ?thesis by (simp add: False finite_native_definition_graph_unformed[OF False])
qed

text \<open>
  Both equations return the original readings: the sites a root reaches through the actual
  callees of the definitions read, and the rows at exactly those sites. A site the roots do
  not reach is no longer read, and a position that carries no definition is read at most
  once, when a callee names it. Package formation, the recovered program and every reading
  built on them keep their values; only the material read to obtain them changes.
\<close>

end
