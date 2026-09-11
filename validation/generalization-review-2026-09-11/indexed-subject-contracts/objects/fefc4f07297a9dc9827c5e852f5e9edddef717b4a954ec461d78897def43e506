theory RRA_Generation_Frames
  imports RRA_Syntax_Records RRA_Generation
begin

section \<open>Actual record and predecessor-family geometry\<close>

definition generation_predecessor_socket :: "nat \<Rightarrow> nat \<Rightarrow> local_address" where
  "generation_predecessor_socket n i = syntax_branch 1 (family_ports n!i)"

definition generation_predecessor_node :: "nat \<Rightarrow> local_address" where
  "generation_predecessor_node i = syntax_branch 1 (syntax_branch i [])"

definition generation_predecessor_slot :: "nat \<Rightarrow> local_address" where
  "generation_predecessor_slot i = syntax_branch 1 (syntax_branch i [4])"

definition generation_frame_members :: "nat \<Rightarrow> (local_address \<times> local_address) set" where
  "generation_frame_members n =
    (\<lambda>i. (generation_predecessor_socket n i,generation_predecessor_node i)) ` {..<n}"

lemma generation_frame_member:
  "(s,d) \<in> generation_frame_members n \<longleftrightarrow>
    (\<exists>i<n. s=generation_predecessor_socket n i \<and> d=generation_predecessor_node i)"
  by (auto simp: generation_frame_members_def)

lemma generation_frame_domain:
  "rel_dom (generation_frame_members n) = generation_predecessor_socket n ` {..<n}"
  by (auto simp: rel_dom_def generation_frame_members_def)

lemma generation_predecessor_sockets_injective:
  "inj_on (generation_predecessor_socket n) {..<n}"
proof (rule inj_onI)
  fix i j assume i: "i \<in> {..<n}" and j: "j \<in> {..<n}"
    and eq: "generation_predecessor_socket n i = generation_predecessor_socket n j"
  have same: "family_ports n!i = family_ports n!j"
    using eq syntax_branch_injective[of 1] by (auto simp: generation_predecessor_socket_def inj_def)
  have ib: "i<length (family_ports n)" and jb: "j<length (family_ports n)" using i j by simp_all
  show "i=j" using nth_eq_iff_index_eq[OF family_ports_distinct[of n] ib jb] same by simp
qed

lemma generation_predecessor_assignment:
  assumes injective: "inj_on g {..<n}"
  shows "\<exists>h. inj_on h (rel_dom (generation_frame_members n)) \<and>
    (\<forall>i<n. h (generation_predecessor_socket n i)=g i) \<and>
    h ` rel_dom (generation_frame_members n) = g ` {..<n}"
proof -
  let ?s = "generation_predecessor_socket n"
  let ?h = "\<lambda>s. g (inv_into {..<n} ?s s)"
  have at: "\<And>i. i<n \<Longrightarrow> ?h (?s i)=g i"
    using inv_into_f_f[OF generation_predecessor_sockets_injective, of _ n] by simp
  have inj: "inj_on ?h (rel_dom (generation_frame_members n))"
  proof (rule inj_onI)
    fix s t assume s: "s \<in> rel_dom (generation_frame_members n)"
      and t: "t \<in> rel_dom (generation_frame_members n)" and eq: "?h s=?h t"
    obtain i where i: "i<n" "s=?s i" using s by (auto simp: generation_frame_domain)
    obtain j where j: "j<n" "t=?s j" using t by (auto simp: generation_frame_domain)
    have same: "g i=g j" using eq i j at[OF i(1)] at[OF j(1)] by simp
    have "i=j" by (rule inj_onD[OF injective same]) (use i j in auto)
    then show "s=t" using i j by simp
  qed
  have image: "?h ` rel_dom (generation_frame_members n) = g ` {..<n}"
    unfolding generation_frame_domain image_image
    by (rule image_cong[OF refl]) (use at in simp)
  show ?thesis using inj at image by blast
qed

lemma generation_predecessor_slots_injective:
  "inj generation_predecessor_slot"
proof (rule injI)
  fix i j assume eq: "generation_predecessor_slot i = generation_predecessor_slot j"
  have same: "syntax_branch i [4] = syntax_branch j [4]"
    using eq syntax_branch_injective[of 1] by (auto simp: generation_predecessor_slot_def inj_def)
  show "i=j"
  proof (rule ccontr)
    assume different: "i \<noteq> j"
    have empty: "range (syntax_branch i) \<inter> range (syntax_branch j) = {}"
      by (rule syntax_branch_disjoint[OF different])
    show False using empty same by blast
  qed
qed

lemma generation_predecessor_slots_separate:
  assumes "j \<noteq> 1"
  shows "generation_predecessor_slot i \<noteq> syntax_branch j k"
  using syntax_branch_disjoint[OF assms] by (auto simp: generation_predecessor_slot_def)

locale generation_frame =
  fixes l p c :: exact_target and as :: "(exact_artifact \<times> local_address) list"
  assumes locus_formed: "target_formed l" and payload_formed: "target_formed p"
    and cause_formed: "target_formed c"
    and predecessors_formed: "\<forall>a\<in>set as. anchor_formed a"
begin

abbreviation predecessor_children where
  "predecessor_children \<equiv> map (\<lambda>a. literal_syntax (Occurrence_Anchor a)) as"

sublocale predecessors: syntax_family_construction predecessor_children
proof
  show "\<forall>R\<in>set predecessor_children. exact_formed R"
    using predecessors_formed literal_syntax_formed by auto
  show "\<forall>R\<in>set predecessor_children. bag_count (object_data R)=(\<lambda>_. 0)"
    using literal_syntax_properties(4) by auto
  show "\<forall>R\<in>set predecessor_children. []\<in>rra_carrier (object_structure R)"
    using literal_syntax_properties(1,2) by auto
qed

abbreviation children where
  "children \<equiv> [literal_syntax l,predecessors.framed,literal_syntax p,literal_syntax c]"

sublocale outer: syntax_family_construction children
proof
  show "\<forall>R\<in>set children. exact_formed R"
    using literal_syntax_formed[OF locus_formed] literal_syntax_formed[OF payload_formed]
      literal_syntax_formed[OF cause_formed] predecessors.formed by simp
  show "\<forall>R\<in>set children. bag_count (object_data R)=(\<lambda>_. 0)"
    using literal_syntax_properties(4)[of l] literal_syntax_properties(4)[of p]
      literal_syntax_properties(4)[of c] predecessors.counts
    by (simp only: set_simps ball_simps; blast)
  show "\<forall>R\<in>set children. []\<in>rra_carrier (object_structure R)"
    using literal_syntax_properties(1,2)[of l] literal_syntax_properties(1,2)[of p]
      literal_syntax_properties(1,2)[of c] predecessors.root by auto
qed

abbreviation framed where "framed \<equiv> outer.record_framed"

lemma formed: "exact_formed framed" by (rule outer.record_formed)

lemma fields:
  "record_at framed [] (family_ports 4)
    [syntax_branch 0 [],syntax_branch 1 [],syntax_branch 2 [],syntax_branch 3 []]"
  using outer.record_read by (simp add: eval_nat_numeral)

lemma predecessor_members:
  "(\<lambda>(s,d). (syntax_branch 1 s,syntax_branch 1 d)) ` predecessors.members =
    generation_frame_members (length as)"
proof (rule set_eqI, rule iffI)
  fix z assume member: "z \<in> (\<lambda>(s,d). (syntax_branch 1 s,syntax_branch 1 d)) ` predecessors.members"
  obtain s d where pair: "(s,d) \<in> predecessors.members"
    and z: "z=(syntax_branch 1 s,syntax_branch 1 d)" using member by auto
  obtain i where at: "i<length as" "s=family_ports (length as)!i" "d=syntax_branch i []"
    using pair by (auto simp: in_set_zip)
  show "z \<in> generation_frame_members (length as)"
    unfolding generation_frame_members_def
    by (rule image_eqI[where x=i])
       (use at z in \<open>auto simp: generation_predecessor_socket_def generation_predecessor_node_def\<close>)
next
  fix z assume member: "z \<in> generation_frame_members (length as)"
  obtain i where at: "i<length as"
    and z: "z=(generation_predecessor_socket (length as) i,generation_predecessor_node i)"
    using member by (auto simp: generation_frame_members_def)
  have bound: "i<length (zip predecessors.ports predecessors.nodes)" using at by simp
  have pair: "(family_ports (length as)!i,syntax_branch i []) \<in> predecessors.members"
    using nth_mem[OF bound] at by (simp add: nth_zip)
  show "z \<in> (\<lambda>(s,d). (syntax_branch 1 s,syntax_branch 1 d)) ` predecessors.members"
    by (rule image_eqI[where x="(family_ports (length as)!i,syntax_branch i [])"])
       (use z pair in \<open>auto simp: generation_predecessor_socket_def generation_predecessor_node_def\<close>)
qed

lemma predecessor_family:
  "family_at framed (syntax_branch 1 []) (generation_frame_members (length as))"
proof -
  let ?f = "syntax_branch 1"
  let ?M = "(\<lambda>(s,d). (?f s,?f d)) ` predecessors.members"
  have injective: "inj_on ?f (rra_carrier (object_structure predecessors.framed))"
    using syntax_branch_injective[of 1] by (simp add: inj_on_def inj_def)
  have copied: "family_at (push_object ?f predecessors.framed) (?f []) ?M"
    by (rule family_at_push[OF predecessors.family_read injective])
  have reads: "object_reads_agree (push_object ?f predecessors.framed) framed
    (?f ` rra_carrier (object_structure predecessors.framed))"
    using outer.record_child_reads[of 1] by simp
  have inside: "insert (?f []) (rel_dom ?M) \<subseteq>
    ?f ` rra_carrier (object_structure predecessors.framed)"
  proof -
    have bounds: "insert [] (rel_dom predecessors.members) \<subseteq>
      rra_carrier (object_structure predecessors.framed)"
      using predecessors.carrier by blast
    have moved: "?f ` insert [] (rel_dom predecessors.members) \<subseteq>
      ?f ` rra_carrier (object_structure predecessors.framed)"
      by (rule image_mono[OF bounds])
    show ?thesis using moved by (simp only: pair_image_domain image_insert)
  qed
  have obj: "object_formed framed" using formed by (simp add: exact_formed_def)
  show ?thesis using family_at_read_transport[OF copied obj reads inside]
    by (simp only: predecessor_members)
qed

lemma field_citation:
  assumes index: "i<4" and child: "children!i=literal_syntax t" and tf: "target_formed t"
  shows "citation_at framed (syntax_branch i []) (map_citation_positions (syntax_branch i) (literal_citation t))
    (syntax_branch i ` literal_interior t)"
proof -
  have at: "i<length children" using index by simp
  have cite: "citation_at (children!i) [] (literal_citation t) (literal_interior t)"
    using literal_syntax_citation[OF tf] child by simp
  show ?thesis by (rule outer.record_child_citation[OF at cite])
qed

lemma locus_citation:
  "citation_at framed (syntax_branch 0 []) (map_citation_positions (syntax_branch 0) (literal_citation l))
    (syntax_branch 0 ` literal_interior l)"
  by (rule field_citation[OF _ _ locus_formed]) simp_all

lemma payload_citation:
  "citation_at framed (syntax_branch 2 []) (map_citation_positions (syntax_branch 2) (literal_citation p))
    (syntax_branch 2 ` literal_interior p)"
  by (rule field_citation[OF _ _ payload_formed]) simp_all

lemma cause_citation:
  "citation_at framed (syntax_branch 3 []) (map_citation_positions (syntax_branch 3) (literal_citation c))
    (syntax_branch 3 ` literal_interior c)"
  by (rule field_citation[OF _ _ cause_formed]) simp_all

lemma predecessor_citation:
  assumes index: "i<length as"
  shows "citation_at framed (generation_predecessor_node i)
    (External (generation_predecessor_slot i) (snd (as!i)))
    (syntax_branch 1 ` (syntax_branch i ` literal_interior (Occurrence_Anchor (as!i))))"
proof -
  have anchor: "anchor_formed (as!i)" using predecessors_formed nth_mem[OF index] by blast
  have cite: "citation_at (predecessor_children!i) []
    (literal_citation (Occurrence_Anchor (as!i))) (literal_interior (Occurrence_Anchor (as!i)))"
    using literal_syntax_citation[of "Occurrence_Anchor (as!i)"] anchor index by simp
  have at: "i<length predecessor_children" using index by simp
  have copied: "citation_at (children!1) (syntax_branch i [])
    (map_citation_positions (syntax_branch i) (literal_citation (Occurrence_Anchor (as!i))))
    (syntax_branch i ` literal_interior (Occurrence_Anchor (as!i)))"
    using predecessors.child_citation[OF at cite] by simp
  have position: "1<length children" by simp
  obtain R a where pair: "as!i=(R,a)" by (cases "as!i")
  show ?thesis using outer.record_child_citation[OF position copied]
    by (simp add: pair generation_predecessor_node_def generation_predecessor_slot_def)
qed

lemma predecessor_slots_inside:
  assumes "i<length as"
  shows "generation_predecessor_slot i \<in> rra_carrier (object_structure framed)"
  using citation_slots_in_carrier[OF predecessor_citation[OF assms]] by simp

lemma literal_slots_inside:
  "{syntax_branch 0 [4],syntax_branch 2 [4],syntax_branch 3 [4]}
    \<subseteq> rra_carrier (object_structure framed)"
proof -
  have slots: "\<And>f t. citation_slots (map_citation_positions f (literal_citation t)) = {f [4]}"
    by (case_tac t) (auto split: prod.splits)
  show ?thesis using citation_slots_in_carrier[OF locus_citation]
      citation_slots_in_carrier[OF payload_citation] citation_slots_in_carrier[OF cause_citation]
    by (simp only: slots) blast
qed

end

text \<open>
  The four field roles are recovered from explicit record incidence. Direct
  predecessor sockets form an unordered family, each with its own actual
  occurrence citation and external slot. The layout above is a construction
  witness; the generation reader accepts every presentation satisfying its
  structural grammar. Binding these slots to actual uses is a separate step.
\<close>

end
