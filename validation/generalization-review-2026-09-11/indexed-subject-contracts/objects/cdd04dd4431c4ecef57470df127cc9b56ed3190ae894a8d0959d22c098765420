theory RRA_Collection_Frames
  imports RRA_Syntax_Records
begin

section \<open>Records whose fields are complete families of citations\<close>

lemma syntax_branch_eq_iff:
  "syntax_branch i a=syntax_branch j b\<longleftrightarrow>i=j \<and> a=b"
proof (cases "i=j")
  case True then show ?thesis using syntax_branch_injective[of i] by (auto simp: inj_def)
next
  case False
  have disjoint: "range (syntax_branch i)\<inter>range (syntax_branch j)={}"
    by (rule syntax_branch_disjoint[OF False])
  show ?thesis using disjoint False by blast
qed

definition collection_members :: "nat \<Rightarrow> (local_address\<times>local_address) set" where
  "collection_members n=image (\<lambda>i. (family_ports n!i,syntax_branch i [])) {..<n}"

lemma collection_members_zip:
  "collection_members n=set (zip (family_ports n) (map (\<lambda>i. syntax_branch i []) [0..<n]))"
proof (rule set_eqI)
  fix z :: "local_address\<times>local_address"
  obtain s d where pair: "z=(s,d)" by (cases z) auto
  show "z\<in>collection_members n\<longleftrightarrow>
      z\<in>set (zip (family_ports n) (map (\<lambda>i. syntax_branch i []) [0..<n]))"
    by (auto simp: pair collection_members_def in_set_zip)
qed

definition collection_family_syntax :: "exact_target list \<Rightarrow> exact_artifact" where
  "collection_family_syntax ts=
    family_wrapper (syntax_forest (map literal_syntax ts)) [] (collection_members (length ts))"

definition collection_record_syntax :: "exact_target list list \<Rightarrow> exact_artifact" where
  "collection_record_syntax xss=
    record_wrapper (syntax_forest (map collection_family_syntax xss)) []
      (family_ports (length xss)) (map (\<lambda>j. syntax_branch j []) [0..<length xss])"

definition collection_field_socket :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> local_address" where
  "collection_field_socket j n i=syntax_branch j (family_ports n!i)"

definition collection_field_node :: "nat \<Rightarrow> nat \<Rightarrow> local_address" where
  "collection_field_node j i=syntax_branch j (syntax_branch i [])"

definition collection_field_slot :: "nat \<Rightarrow> nat \<Rightarrow> local_address" where
  "collection_field_slot j i=syntax_branch j (syntax_branch i [4])"

definition collection_field_members :: "nat \<Rightarrow> nat \<Rightarrow> (local_address\<times>local_address) set" where
  "collection_field_members j n=
    image (\<lambda>i. (collection_field_socket j n i,collection_field_node j i)) {..<n}"

lemma collection_field_member:
  "(s,d)\<in>collection_field_members j n\<longleftrightarrow>
    (\<exists>i<n. s=collection_field_socket j n i \<and> d=collection_field_node j i)"
  by (auto simp: collection_field_members_def)

lemma collection_field_domain:
  "rel_dom (collection_field_members j n)=image (collection_field_socket j n) {..<n}"
  by (auto simp: collection_field_members_def rel_dom_def)

lemma collection_field_members_map:
  "collection_field_members j n=image (map_prod (syntax_branch j) (syntax_branch j)) (collection_members n)"
  by (auto simp: collection_members_def collection_field_members_def
      collection_field_socket_def collection_field_node_def)

lemma collection_field_sockets_injective:
  "inj_on (collection_field_socket j n) {..<n}"
proof (rule inj_onI)
  fix i k assume i: "i\<in>{..<n}" and k: "k\<in>{..<n}"
    and same: "collection_field_socket j n i=collection_field_socket j n k"
  have eq: "family_ports n!i=family_ports n!k"
    using same by (simp add: collection_field_socket_def syntax_branch_eq_iff)
  have ib: "i<length (family_ports n)" and kb: "k<length (family_ports n)" using i k by simp_all
  show "i=k" using nth_eq_iff_index_eq[OF family_ports_distinct[of n] ib kb] eq by simp
qed

lemma collection_field_assignment:
  assumes injective: "inj_on g {..<n}"
  shows "\<exists>h. inj_on h (rel_dom (collection_field_members j n)) \<and>
    (\<forall>i<n. h (collection_field_socket j n i)=g i) \<and>
    image h (rel_dom (collection_field_members j n))=image g {..<n}"
proof -
  let ?s="collection_field_socket j n"
  let ?h="\<lambda>s. g (inv_into {..<n} ?s s)"
  have at: "\<And>i. i<n \<Longrightarrow> ?h (?s i)=g i"
  proof -
    fix i assume index: "i<n"
    have inside: "i\<in>{..<n}" using index by simp
    have inverse: "inv_into {..<n} ?s (?s i)=i"
      by (rule inv_into_f_f[OF collection_field_sockets_injective inside])
    show "?h (?s i)=g i" by (simp only: inverse)
  qed
  have inj: "inj_on ?h (rel_dom (collection_field_members j n))"
  proof (rule inj_onI)
    fix s t assume s: "s\<in>rel_dom (collection_field_members j n)"
      and t: "t\<in>rel_dom (collection_field_members j n)" and eq: "?h s=?h t"
    obtain i where i: "i<n" "s=?s i" using s by (auto simp: collection_field_domain)
    obtain k where k: "k<n" "t=?s k" using t by (auto simp: collection_field_domain)
    have same: "g i=g k" using eq i k at[OF i(1)] at[OF k(1)] by simp
    have "i=k" by (rule inj_onD[OF injective same]) (use i k in auto)
    then show "s=t" using i k by simp
  qed
  have image: "image ?h (rel_dom (collection_field_members j n))=image g {..<n}"
    unfolding collection_field_domain image_image
    by (rule image_cong[OF refl]) (use at in simp)
  show ?thesis using inj at image by blast
qed

lemma collection_field_slot_eq:
  "collection_field_slot j i=collection_field_slot k m\<longleftrightarrow>j=k \<and> i=m"
  by (simp add: collection_field_slot_def syntax_branch_eq_iff)

definition collection_indices :: "'a list list \<Rightarrow> (nat\<times>nat) set" where
  "collection_indices xss=Sigma {..<length xss} (\<lambda>j. {..<length (xss!j)})"

lemma collection_index [simp]:
  "(j,i)\<in>collection_indices xss\<longleftrightarrow>j<length xss \<and> i<length (xss!j)"
  by (simp add: collection_indices_def)

lemma collection_indices_finite [simp]: "finite (collection_indices xss)"
  by (simp add: collection_indices_def)

locale literal_collection =
  fixes ts :: "exact_target list"
  assumes targets_formed: "\<forall>t\<in>set ts. target_formed t"
begin

sublocale children: syntax_family_construction "map literal_syntax ts"
proof
  show "\<forall>R\<in>set (map literal_syntax ts). exact_formed R"
    using targets_formed literal_syntax_formed by auto
  show "\<forall>R\<in>set (map literal_syntax ts). bag_count (object_data R)=(\<lambda>_. 0)"
    using literal_syntax_properties(4) by auto
  show "\<forall>R\<in>set (map literal_syntax ts). []\<in>rra_carrier (object_structure R)"
    using literal_syntax_properties(1,2) by auto
qed

lemma layout: "collection_family_syntax ts=children.framed"
  by (simp add: collection_family_syntax_def collection_members_zip)

lemma formed: "exact_formed (collection_family_syntax ts)"
  using children.formed by (simp only: layout)

lemma root: "[]\<in>rra_carrier (object_structure (collection_family_syntax ts))"
  using children.root by (simp only: layout)

lemma counts: "bag_count (object_data (collection_family_syntax ts))=(\<lambda>_. 0)"
  using children.counts by (simp only: layout)

lemma family: "family_at (collection_family_syntax ts) [] (collection_members (length ts))"
  using children.family_read by (simp add: layout collection_members_zip)

lemma citation:
  assumes index: "i<length ts"
  shows "citation_at (collection_family_syntax ts) (syntax_branch i [])
    (map_citation_positions (syntax_branch i) (literal_citation (ts!i)))
    (image (syntax_branch i) (literal_interior (ts!i)))"
proof -
  have tf: "target_formed (ts!i)" using targets_formed nth_mem[OF index] by blast
  have at: "i<length (map literal_syntax ts)" using index by simp
  have cite: "citation_at ((map literal_syntax ts)!i) [] (literal_citation (ts!i)) (literal_interior (ts!i))"
    using literal_syntax_citation[OF tf] index by simp
  show ?thesis using children.child_citation[OF at cite] by (simp only: layout)
qed

end

locale collection_record_frame =
  fixes xss :: "exact_target list list"
  assumes fields_formed: "\<forall>ts\<in>set xss. \<forall>t\<in>set ts. target_formed t"
begin

abbreviation children where "children \<equiv> map collection_family_syntax xss"

lemma children_properties:
  "\<forall>R\<in>set children. exact_formed R \<and> bag_count (object_data R)=(\<lambda>_. 0) \<and>
    []\<in>rra_carrier (object_structure R)"
proof (intro ballI)
  fix R assume "R\<in>set children"
  then obtain ts where member: "ts\<in>set xss" and same: "R=collection_family_syntax ts" by auto
  interpret child: literal_collection ts
    by (rule literal_collection.intro) (use fields_formed member in blast)
  show "exact_formed R \<and> bag_count (object_data R)=(\<lambda>_. 0) \<and>
      []\<in>rra_carrier (object_structure R)"
    using child.formed child.counts child.root same by simp
qed

sublocale outer: syntax_family_construction children
proof
  show "\<forall>R\<in>set children. exact_formed R" using children_properties by blast
  show "\<forall>R\<in>set children. bag_count (object_data R)=(\<lambda>_. 0)" using children_properties by blast
  show "\<forall>R\<in>set children. []\<in>rra_carrier (object_structure R)" using children_properties by blast
qed

lemma layout: "collection_record_syntax xss=outer.record_framed"
  by (simp add: collection_record_syntax_def)

lemma formed: "exact_formed (collection_record_syntax xss)"
  using outer.record_formed by (simp only: layout)

lemma fields:
  "record_at (collection_record_syntax xss) [] (family_ports (length xss))
    (map (\<lambda>j. syntax_branch j []) [0..<length xss])"
  using outer.record_read by (simp add: layout)

lemma field_family:
  assumes index: "j<length xss"
  shows "family_at (collection_record_syntax xss) (syntax_branch j [])
    (collection_field_members j (length (xss!j)))"
proof -
  have field: "xss!j\<in>set xss" by (rule nth_mem[OF index])
  interpret child: literal_collection "xss!j"
    by (rule literal_collection.intro) (use fields_formed field in blast)
  let ?f="syntax_branch j"
  let ?R="collection_family_syntax (xss!j)"
  let ?M="collection_members (length (xss!j))"
  let ?N="image (map_prod ?f ?f) ?M"
  have injective: "inj_on ?f (rra_carrier (object_structure ?R))"
    using syntax_branch_injective[of j] by (simp add: inj_on_def inj_def)
  have moved: "family_at (push_object ?f ?R) (?f []) ?N"
    using family_at_push[OF child.family injective] by (simp add: map_prod_def)
  have reads: "object_reads_agree (push_object ?f ?R) (collection_record_syntax xss)
    (image ?f (rra_carrier (object_structure ?R)))"
    using outer.record_child_reads[of j] index by (simp add: layout)
  have bounds: "insert [] (rel_dom ?M)\<subseteq>rra_carrier (object_structure ?R)"
    by (rule family_interior_in_carrier[OF child.family])
  have image_bounds: "image ?f (insert [] (rel_dom ?M))\<subseteq>
      image ?f (rra_carrier (object_structure ?R))"
    by (rule image_mono[OF bounds])
  have inside: "insert (?f []) (rel_dom ?N)\<subseteq>image ?f (rra_carrier (object_structure ?R))"
    using image_bounds by (simp add: map_prod_def pair_image_domain)
  have obj: "object_formed (collection_record_syntax xss)" using formed by (simp add: exact_formed_def)
  show ?thesis using family_at_read_transport[OF moved obj reads inside]
    by (simp only: collection_field_members_map)
qed

lemma citation:
  assumes field: "j<length xss" and index: "i<length (xss!j)"
  shows "citation_at (collection_record_syntax xss) (collection_field_node j i)
    (map_citation_positions (syntax_branch j \<circ> syntax_branch i) (literal_citation (xss!j!i)))
    (image (syntax_branch j \<circ> syntax_branch i) (literal_interior (xss!j!i)))"
proof -
  have member: "xss!j\<in>set xss" by (rule nth_mem[OF field])
  interpret child: literal_collection "xss!j"
    by (rule literal_collection.intro) (use fields_formed member in blast)
  have at: "j<length children" using field by simp
  have cite: "citation_at (children!j) (syntax_branch i [])
    (map_citation_positions (syntax_branch i) (literal_citation (xss!j!i)))
    (image (syntax_branch i) (literal_interior (xss!j!i)))"
    using child.citation[OF index] field by simp
  have composed: "\<And>f g c. map_citation_positions f (map_citation_positions g c)=map_citation_positions (f \<circ> g) c"
    by (case_tac c) auto
  show ?thesis using outer.record_child_citation[OF at cite]
    by (simp add: layout collection_field_node_def composed image_image)
qed

lemma slots_inside:
  assumes field: "j<length xss" and index: "i<length (xss!j)"
  shows "collection_field_slot j i\<in>rra_carrier (object_structure (collection_record_syntax xss))"
proof -
  have slots: "\<And>f t. citation_slots (map_citation_positions f (literal_citation t))={f [4]}"
    by (case_tac t) (auto split: prod.splits)
  show ?thesis using citation_slots_in_carrier[OF citation[OF field index]]
    by (simp add: slots collection_field_slot_def)
qed

end

text \<open>
  The record order is explicit successor incidence between its field sockets.
  Each field is a complete unordered family with one citation occurrence per
  supplied entry. The lists choose a construction witness; readers recover the
  resulting fields and family sockets from incidence. No selected enumeration
  is imposed on the meaning of a represented collection.
\<close>

end
