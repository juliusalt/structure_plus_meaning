theory RRA_Boundary_Use_Embeddings
  imports RRA_Finite_Compact_Uses
begin

definition boundary_use_embedding where
  "boundary_use_embedding U u h \<longleftrightarrow> inj h \<and> h None=u \<and>
    (\<forall>a. h (Some a)\<notin>insert u U)"

lemma boundary_embedding_origin:
  "boundary_use_embedding U u h \<Longrightarrow> v\<in>U \<Longrightarrow> h x=v \<Longrightarrow> x=None \<and> v=u"
  by (cases x) (auto simp: boundary_use_embedding_def)

lemma prefix_boundary_embedding:
  "prefix_avoids_uses U u prefix \<Longrightarrow> boundary_use_embedding U u (prefix_use_map prefix u)"
  using prefix_use_map_injective prefix_use_map_outside by (auto simp: boundary_use_embedding_def)

lemma original_boundary_embedding:
  "finite U \<Longrightarrow> boundary_use_embedding U u (fresh_use_map U u)"
  by (simp only: original_fresh_use_prefix; rule prefix_boundary_embedding; rule original_prefix_avoids_uses)

lemma compact_boundary_embedding:
  "finite U \<Longrightarrow> boundary_use_embedding U u (compact_use_map U u)"
  by (simp only: compact_use_map_def; rule prefix_boundary_embedding; rule compact_use_prefix_avoids)

text \<open>
  A complete mapping preserves the designated shared use and every distinction,
  while all present imported uses avoid the original reserved set and boundary.
  Original and compact prefix maps instantiate this contract. The origin law
  identifies the only imported occurrence that can meet an original use.
\<close>

end
