theory Finite_Observation_Tables
  imports Finite_Investigation
begin

section \<open>Every declared key has its complete computed value\<close>

definition finite_profile_table where
  "finite_profile_table C F T=fimage (\<lambda>c. (c,finite_candidate_profile F T c)) C"

definition finite_loss_table where
  "finite_loss_table C F T=ffUnion (fimage (\<lambda>c.
    fimage (\<lambda>d. ((c,d),finite_candidate_losses F T c d)) C) C)"

lemma finite_profile_table_at:
  "(c,V)\<in>fset (finite_profile_table C F T) \<longleftrightarrow>
    c\<in>fset C \<and> V=finite_candidate_profile F T c"
  by (auto simp: finite_profile_table_def fimage.rep_eq)

lemma finite_loss_table_at:
  "((c,d),V)\<in>fset (finite_loss_table C F T) \<longleftrightarrow>
    c\<in>fset C \<and> d\<in>fset C \<and> V=finite_candidate_losses F T c d"
  by (auto simp: finite_loss_table_def ffUnion.rep_eq fimage.rep_eq)

lemma finite_profile_table_keys:
  "rel_dom (fset (finite_profile_table C F T))=fset C"
  by (auto simp: rel_dom_def finite_profile_table_at)

lemma finite_loss_table_keys:
  "rel_dom (fset (finite_loss_table C F T))=fset C\<times>fset C"
  by (auto simp: rel_dom_def finite_loss_table_at)

lemma finite_profile_table_functional:
  "single_valued (fset (finite_profile_table C F T))"
  by (auto simp: single_valued_def finite_profile_table_at)

lemma finite_loss_table_functional:
  "single_valued (fset (finite_loss_table C F T))"
  by (auto simp: single_valued_def finite_loss_table_at split: prod.splits)

lemma finite_loss_table_self:
  "((c,c),{||})\<in>fset (finite_loss_table C F T) \<longleftrightarrow> c\<in>fset C"
  by (simp only: finite_loss_table_at) (simp add: finite_candidate_losses_def fset_eq_iff)

lemma finite_profile_table_enumeration:
  "finite_profile_table (fset_of_list cs) F T=fset_of_list (map (\<lambda>c. (c,finite_candidate_profile F T c)) cs)"
  by (simp only: finite_profile_table_def fset_of_list_map)

lemma finite_loss_table_enumeration:
  "finite_loss_table (fset_of_list cs) F T=fset_of_list
    (map (\<lambda>(c,d). ((c,d),finite_candidate_losses F T c d)) (List.product cs cs))"
  by (rule fset_inject[THEN iffD1])
    (auto simp: finite_loss_table_def ffUnion.rep_eq fimage.rep_eq fset_of_list.rep_eq
      set_product image_iff)

text \<open>
  These finite graphs retain every declared candidate and every ordered
  candidate pair. Each key has the value supplied by its existing profile
  or loss function. Empty values therefore remain rows, including every
  self pair. Functionality follows from calculation; it is not an added
  primitive restriction on the complete collection presentation classes.
\<close>

end
