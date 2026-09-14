theory Indexed_Relation_Families
  imports Bootstrap_Relations
begin

definition indexed_relation_family :: "'n set\<Rightarrow>('n\<Rightarrow>('s\<times>'m) set)\<Rightarrow>(('n\<times>'s)\<times>'m) set" where
  "indexed_relation_family N R=(\<Union>n\<in>N. (\<lambda>(s,m). ((n,s),m)) ` R n)"

lemma indexed_relation_family_member:
  "((n,s),m)\<in>indexed_relation_family N R \<longleftrightarrow> n\<in>N \<and> (s,m)\<in>R n"
  by (auto simp: indexed_relation_family_def)

lemma indexed_relation_family_finite:
  assumes nodes: "finite N" and rows: "\<And>n. n\<in>N \<Longrightarrow> finite (R n)"
  shows "finite (indexed_relation_family N R)"
  unfolding indexed_relation_family_def
  by (rule finite_UN_I[OF nodes]) (use rows in simp)

theorem indexed_relation_family_image:
  assumes rows: "\<And>n. n\<in>N \<Longrightarrow> S (f n)=map_prod id g ` R n"
  shows "map_prod (map_prod f id) g ` indexed_relation_family N R=
    indexed_relation_family (f ` N) S"
proof -
  have point:
    "map_prod (map_prod f id) g ` ((\<lambda>(s,m). ((n,s),m)) ` R n)=
      (\<lambda>(s,m). ((f n,s),m)) ` S (f n)" if "n\<in>N" for n
    by (simp add: rows[OF that] image_image map_prod_def case_prod_unfold)
  show ?thesis
    unfolding indexed_relation_family_def
    apply (simp only: image_UN UN_simps(10))
    by (rule arg_cong[where f=Union], rule image_cong[OF refl], rule point; assumption)
qed

text \<open>
  The complete family preserves each owner's middle index and every target.
  Exact row correspondence transports the whole family. Distinct owners may
  have the same image only when the supplied complete row equations agree;
  injectivity is a separate requirement for uses that preserve owner identity.
\<close>

end
