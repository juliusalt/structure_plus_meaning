theory Factor_Shared_Package_Readings
  imports Factor_Demanded_Package_Readings
begin

section \<open>A native package is read once, and each site is read once in its traversal\<close>

text \<open>
  The package reader read every definition five times: the traversal of the demanded sites read the
  sites of its frontier once for their rows and again for their successors; package formation took the
  sites from one traversal and read every site again; the program took its graph from a second
  traversal. Each reading of a definition is one reading of the index of the artifact at its use, so
  the reader paid its whole syntax five times, a constant factor. A value computed twice is computed once by
  HOL's @{text Let}: a step of the traversal reads its frontier once and takes the successors from those
  rows, and the package reader takes its sites and its graph from one traversal. It checks that every site
  has a reading from the graph's rows, which are exactly the rows of the sites
  (@{thm [source] finite_demanded_readings_exact}, through @{text finite_native_definition_graph_rows}).
  The formation check at the entry is the existing one (@{text finite_native_package_formed_once_code})
  carried over. Every result is the original result.
\<close>

lemma finite_demanded_step_shared_code [code]:
  "finite_demanded_step read succ q=(case q of (S,T,A) \<Rightarrow>
    (let visited=S |\<union>| T; rows=finite_site_rows read T in
      (visited,ffUnion (fimage (\<lambda>(d,x). succ x) rows) |-| visited,A |\<union>| rows)))"
  by (simp only: finite_demanded_step_def finite_row_successors_def Let_def)

lemma finite_native_definition_graph_rows:
  assumes formed: "finite_environment_formed E"
  shows "finite_native_definition_graph E roots=
    finite_site_rows (finite_definition_site_reading_formed E) (finite_native_definition_sites E roots)"
proof -
  have exact: "finite_demanded_readings (finite_definition_site_reading_formed E) finite_definition_dependencies roots=
      Some (finite_rooted_sites (finite_definition_site_reading_formed E) finite_definition_dependencies
          (finite_environment_positions E) roots,
        finite_site_rows (finite_definition_site_reading_formed E)
          (finite_rooted_sites (finite_definition_site_reading_formed E) finite_definition_dependencies
            (finite_environment_positions E) roots))"
    by (rule finite_demanded_readings_exact)
      (simp only: finite_definition_site_reading_formed_exact[OF formed], rule finite_definition_reading_universe)
  show ?thesis using exact finite_demanded_definition_readings_formed[OF formed, of roots] by simp
qed

lemma finite_native_package_sites_read:
  assumes formed: "finite_environment_formed E"
  shows "fBall (finite_native_definition_sites E roots)
      (\<lambda>d. finite_native_definition_readings_formed E (fst d) (snd d) \<noteq> {||}) \<longleftrightarrow>
    finite_native_definition_sites E roots |\<subseteq>| fimage fst (finite_native_definition_graph E roots)"
proof
  assume all: "fBall (finite_native_definition_sites E roots)
      (\<lambda>d. finite_native_definition_readings_formed E (fst d) (snd d) \<noteq> {||})"
  show "finite_native_definition_sites E roots |\<subseteq>| fimage fst (finite_native_definition_graph E roots)"
  proof
    fix d assume d: "d |\<in>| finite_native_definition_sites E roots"
    have "finite_native_definition_readings_formed E (fst d) (snd d) \<noteq> {||}" using all d by blast
    then obtain y where y: "y |\<in>| finite_native_definition_readings_formed E (fst d) (snd d)"
      by (auto simp: fset_eq_iff)
    have "(d,y) |\<in>| finite_native_definition_graph E roots"
      using d y by (simp add: finite_native_definition_graph_rows[OF formed] finite_site_rows_member
        finite_definition_site_reading_formed_def)
    then show "d |\<in>| fimage fst (finite_native_definition_graph E roots)" by force
  qed
next
  assume sub: "finite_native_definition_sites E roots |\<subseteq>| fimage fst (finite_native_definition_graph E roots)"
  show "fBall (finite_native_definition_sites E roots)
      (\<lambda>d. finite_native_definition_readings_formed E (fst d) (snd d) \<noteq> {||})"
    using sub by (fastforce simp: finite_native_definition_graph_rows[OF formed] finite_site_rows_member
      finite_definition_site_reading_formed_def)
qed

lemma finite_native_package_readings_shared_code [code]:
  "finite_native_package_readings E u r=(if finite_environment_formed E then
    ffUnion (fimage (\<lambda>Q. case finite_demanded_readings (finite_definition_site_reading_formed E)
        finite_definition_dependencies (fimage snd Q) of
      None \<Rightarrow> {||}
    | Some (S,G) \<Rightarrow> (if S |\<subseteq>| fimage fst G then
        {|\<lparr>finite_system_interfaces=fimage (\<lambda>(d,p,F). (d,p)) G,
          finite_system_clauses=ffUnion (fimage (\<lambda>(d,p,F). fimage (\<lambda>(c,S). ((d,c),S)) F) G)\<rparr>|}
        else {||})) (finite_native_root_family_readings E u r))
    else {||})"
proof (cases "finite_environment_formed E")
  case True
  show ?thesis
    unfolding finite_native_package_readings_def finite_native_program_def Let_def
    by (simp add: True finite_native_package_formed_once_code finite_native_package_sites_read[OF True]
      finite_demanded_definition_readings_formed[OF True])
next
  case False
  show ?thesis unfolding fset_eq_iff
    by (simp add: False finite_native_package_readings_step finite_native_package_formed_once_code)
qed

end
