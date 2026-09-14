theory Factor_Finite_Graph_Coordinates
  imports Factor_Finite_Graph_Inputs Factor_Finite_Program_Coordinates
begin

definition finite_graph_coordinates :: "local_address option finite_artifact_environment\<Rightarrow>
    ('a,'s,'c,'n::linorder) finite_derivation_graph\<Rightarrow>'n\<Rightarrow>local_address option definition_site" where
  "finite_graph_coordinates E G=finite_program_coordinates E {||} (finite_graph_nodes G) (\<lambda>_. (None,[]))"

theorem finite_graph_coordinates_properties:
  assumes environment: "finite_environment_formed E"
  shows "inj_on (finite_graph_coordinates E G) (fset (finite_graph_nodes G))"
    "\<forall>n\<in>fset (finite_graph_nodes G). snd (finite_graph_coordinates E G n)=[]"
    "image fst (image (finite_graph_coordinates E G) (fset (finite_graph_nodes G)))\<inter>
      fset (finite_environment_uses E)={}"
proof -
  have empty_injective: "inj_on (\<lambda>_. (None,[])) (fset {||})" by simp
  have empty_positions: "image (\<lambda>_. (None,[])) (fset {||})\<subseteq>
    environment_positions (decode_finite_environment E)" by simp
  note coordinates=finite_program_coordinates_properties[where E=E and U="{||}"
    and V="finite_graph_nodes G" and g="\<lambda>_. (None,[])", OF environment empty_injective empty_positions]
  show "inj_on (finite_graph_coordinates E G) (fset (finite_graph_nodes G))"
    "\<forall>n\<in>fset (finite_graph_nodes G). snd (finite_graph_coordinates E G n)=[]"
    "image fst (image (finite_graph_coordinates E G) (fset (finite_graph_nodes G)))\<inter>
      fset (finite_environment_uses E)={}"
    using coordinates by (simp add: finite_graph_coordinates_def Let_def)+
qed

theorem finite_graph_coordinates_ready:
  assumes ready: "finite_graph_construction_ready E G root"
  shows "finite_graph_construction_ready E (finite_rename_graph (finite_graph_coordinates E G) G)
    (finite_graph_coordinates E G root)"
proof -
  have ef: "finite_environment_formed E" and gf: "finite_graph_formed G root"
    and metadata: "finite_graph_metadata_at E G"
    using ready by (simp only: finite_graph_construction_ready_def; blast)+
  have injective: "inj_on (finite_graph_coordinates E G) (fset (finite_graph_nodes G))"
    by (rule finite_graph_coordinates_properties(1)[OF ef])
  show ?thesis using ef finite_graph_renamed_formed[OF gf injective]
    finite_graph_metadata_rename[OF metadata gf injective]
    by (simp only: finite_graph_construction_ready_def; blast)
qed

export_code finite_graph_coordinates checking SML

text \<open>
  The existing finite coordinate extension is instantiated with an empty
  retained domain. Every original graph node receives a distinct fresh use,
  at its artifact root. No original node identity or source metadata is lost.
  The complete graph and its actual source requirements remain available for
  the separate artifact-family compiler and installer.
\<close>

end
