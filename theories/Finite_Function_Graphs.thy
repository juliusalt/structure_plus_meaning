theory Finite_Function_Graphs
  imports Bootstrap_Relations "HOL-Library.FSet"
begin

lemma graph_map_source_image:
  "graph_map (f ` A) g=map_prod f id ` graph_map A (g\<circ>f)"
  by (auto simp: graph_map_def map_prod_def comp_def; force)

lemma finite_function_graph:
  "fset (fimage (\<lambda>i. (i,S i)) I)=graph_map (fset I) S"
  by (auto simp: fimage.rep_eq graph_map_def)

lemma finite_function_graph_member:
  "(i,s) |\<in>| fimage (\<lambda>j. (j,S j)) I \<longleftrightarrow> i |\<in>| I \<and> s=S i"
  by (simp only: finite_function_graph graph_map_member)

lemma finite_function_graph_all:
  "(\<forall>(i,s)\<in>fset (fimage (\<lambda>j. (j,S j)) I). P i s) \<longleftrightarrow>
    (\<forall>i\<in>fset I. P i (S i))"
  by (auto simp: fimage.rep_eq)

lemma graph_map_converse_functional:
  "single_valued ((graph_map A f)\<inverse>) \<longleftrightarrow> inj_on f A"
  by (auto simp: single_valued_def graph_map_member inj_on_def)

lemma relation_swap_image:
  "prod.swap ` M=M\<inverse>"
  by (auto simp: prod.swap_def intro: rev_image_eqI)

lemma finite_relation_converse:
  "fset (fimage prod.swap M)=(fset M)\<inverse>"
  by (simp only: fimage.rep_eq relation_swap_image)

end
