theory Factor_Complete_Data_Recognition
  imports Factor_Complete_Data_Quotation
begin

section \<open>The empty slot boundary determines the data profile\<close>

lemma term_quotation_empty_slots_iff:
  assumes quote: "term_quoted_at E u r t I K"
  shows "K={} \<longleftrightarrow> self_contained_term t"
  using quote by (induction rule: term_quoted_at.induct) auto

lemma payload_leaves_reads_agree:
  assumes "payload_leaf_at R r v" "payload_leaf_at S r v"
  shows "object_reads_agree R S {r}"
  using assms payload_leaf_carrier[OF assms(1)] payload_leaf_carrier[OF assms(2)]
  by (auto simp: object_reads_agree_def payload_leaf_at_def payload_at_def)

lemma pair_records_reads_agree:
  assumes "record_at R r [a,b] [l,q]" "record_at S r [a,b] [l,q]"
  shows "object_reads_agree R S {r,a,b}"
  using assms record_interior_in_carrier[OF assms(1)] record_interior_in_carrier[OF assms(2)]
  by (auto simp: object_reads_agree_def record_at_def raw_record_at_def record_path_cons_iff)

section \<open>A native data reading determines an injective syntax copy\<close>

theorem self_contained_quotation_copy:
  assumes quote: "term_quoted_at E u r t I K" and closed: "self_contained_term t"
    and source: "artifact_at E u C"
  shows "\<exists>f. finite_addressing (rra_carrier (object_structure (term_syntax t))) f \<and>
    r=f [] \<and> I=image f (rra_carrier (object_structure (term_syntax t))) \<and>
    object_reads_agree (push_object f (term_syntax t)) C I"
  using quote closed source
proof (induction arbitrary: C rule: term_quoted_at.induct)
  case (target u R r c I t)
  then show ?case by simp
next
  case (pair u R r ps l q x L A y Q B)
  let ?X="term_syntax x"
  let ?Y="term_syntax y"
  let ?U="rra_carrier (object_structure ?X)"
  let ?V="rra_carrier (object_structure ?Y)"
  let ?S="pair_syntax ?X ?Y"
  let ?W="rra_carrier (object_structure ?S)"
  have xc: "self_contained_term x" and yc: "self_contained_term y"
    using pair.prems(1) by auto
  obtain f where left: "finite_addressing ?U f" "l=f []" "L=image f ?U"
    "object_reads_agree (push_object f ?X) C L"
    using pair.IH(1)[OF xc pair.prems(2)] by blast
  obtain g where right: "finite_addressing ?V g" "q=g []" "Q=image g ?V"
    "object_reads_agree (push_object g ?Y) C Q"
    using pair.IH(2)[OF yc pair.prems(2)] by blast
  have same: "R=C" by (rule environment_artifact_unique[OF pair.hyps(1,2) pair.prems(2)])
  have rec: "record_at C r ps [l,q]" using pair.hyps(3) same by simp
  have ports: "distinct ps" "r\<notin>set ps" "length ps=2"
    using record_at_preserves_socket_occurrences[OF rec] by auto
  obtain a b where ps: "ps=[a,b]"
    using ports(3) by (auto simp: numeral_2_eq_2 length_Suc_conv)
  have finj: "inj_on f ?U" and ginj: "inj_on g ?V"
    using left(1) right(1) by (auto simp: finite_addressing_def)
  let ?h="\<lambda>p::local_address. if p=[] then r else if p=[0] then a else if p=[1] then b
    else if hd p=2 then f (tl p) else g (tl p)"
  have roots [simp]: "?h []=r" "?h [0]=a" "?h [1]=b"
    and branches [simp]: "\<And>p. ?h (2#p)=f p" "\<And>p. ?h (3#p)=g p"
    by simp_all
  let ?H="{[],[0],[1]}"
  let ?X2="image (Cons 2) ?U"
  let ?Y3="image (Cons 3) ?V"
  have header_injective: "inj_on ?h ?H"
    using ports(1,2) by (auto simp: inj_on_def ps)
  have left_injective: "inj_on ?h ?X2"
    using finj by (auto simp: inj_on_def)
  have right_injective: "inj_on ?h ?Y3"
    using ginj by (auto simp: inj_on_def)
  have left_image: "image ?h ?X2=L" and right_image: "image ?h ?Y3=Q"
    by (simp_all only: image_image comp_def branches left(3) right(3))
  have combine: "inj_on k (S\<union>T)"
    if "inj_on k S" "inj_on k T" "image k S\<inter>image k T={}"
    for k :: "local_address\<Rightarrow>local_address" and S T
    using that by (auto simp: inj_on_Un)
  have children: "inj_on ?h (?X2\<union>?Y3)"
    by (rule combine[OF left_injective right_injective])
      (simp only: left_image right_image pair.hyps(7))
  have header_image: "image ?h ?H={r,a,b}"
    by (simp only: image_insert image_empty roots)
  have separate: "image ?h ?H\<inter>image ?h (?X2\<union>?Y3)={}"
    using pair.hyps(6) by (simp only: image_Un header_image left_image right_image; simp add: ps)
  have assembled: "inj_on ?h (?H\<union>(?X2\<union>?Y3))"
    by (rule combine[OF header_injective children separate])
  have injective: "inj_on ?h ?W"
    using assembled by (simp only: pair_syntax_carrier Un_assoc)
  have image: "image ?h ?W=insert r (set ps\<union>L\<union>Q)"
    by (simp only: pair_syntax_carrier image_Un header_image left_image right_image; simp add: ps)
  have xf: "exact_formed ?X" and yf: "exact_formed ?Y"
    by (rule term_syntax_formed[OF term_quoted_formed[OF pair.hyps(4)]],
        rule term_syntax_formed[OF term_quoted_formed[OF pair.hyps(5)]])
  have sf: "exact_formed ?S" by (rule pair_syntax_formed[OF xf yf]) simp_all
  have xof: "object_formed ?X" and yof: "object_formed ?Y" and sof: "object_formed ?S"
    using xf yf sf by (auto simp: exact_formed_def)
  have positions: "\<forall>p\<in>image ?h ?W. octets_formed p"
    using term_quoted_addresses_formed[OF term_quoted_at.pair[OF pair.hyps]]
    by (simp only: image; blast)
  have mapped_formed: "octets_formed (?h p)" if "p\<in>?W" for p
    by (rule positions[rule_format]) (rule imageI[OF that])
  have address: "finite_addressing ?W ?h"
    using injective mapped_formed by (simp only: finite_addressing_def; blast)
  have base: "record_at ?S [] [[0],[1]] [[2],[3]]" by (rule pair_syntax_record[OF sf])
  have copied_record: "record_at (push_object ?h ?S) r [a,b] [l,q]"
    using record_at_push[OF base injective] left(2) right(2) by simp
  have actual_record: "record_at C r [a,b] [l,q]" using rec ps by simp
  have header: "object_reads_agree (push_object ?h ?S) C {r,a,b}"
    by (rule pair_records_reads_agree[OF copied_record actual_record])
  have xcopy: "object_formed (push_object (Cons 2) ?X)"
    using object_push_isomorphism[OF xof, of "Cons 2"]
    by (auto simp: object_isomorphism_def inj_on_def)
  have ycopy: "object_formed (push_object (Cons 3) ?Y)"
    using object_push_isomorphism[OF yof, of "Cons 3"]
    by (auto simp: object_isomorphism_def inj_on_def)
  have xinj: "inj_on ?h (rra_carrier (object_structure (push_object (Cons 2) ?X)))"
    by (rule inj_on_subset[OF injective]) (auto simp: push_object_def pair_syntax_carrier)
  have yinj: "inj_on ?h (rra_carrier (object_structure (push_object (Cons 3) ?Y)))"
    by (rule inj_on_subset[OF injective]) (auto simp: push_object_def pair_syntax_carrier)
  have xread: "object_reads_agree (push_object (Cons 2) ?X) ?S (image (Cons 2) ?U)"
    by (rule pair_syntax_reads_left) simp
  have yread: "object_reads_agree (push_object (Cons 3) ?Y) ?S (image (Cons 3) ?V)"
    by (rule pair_syntax_reads_right) simp
  have xpush: "object_reads_agree (push_object ?h (push_object (Cons 2) ?X))
      (push_object ?h ?S) (image ?h (image (Cons 2) ?U))"
    by (rule object_reads_agree_push_on[OF xcopy sof xinj injective xread])
  have ypush: "object_reads_agree (push_object ?h (push_object (Cons 3) ?Y))
      (push_object ?h ?S) (image ?h (image (Cons 3) ?V))"
    by (rule object_reads_agree_push_on[OF ycopy sof yinj injective yread])
  have xfactor: "push_object ?h (push_object (Cons 2) ?X)=push_object f ?X"
    unfolding push_object_composes[OF xof]
    by (rule push_object_cong[OF xof]) simp
  have yfactor: "push_object ?h (push_object (Cons 3) ?Y)=push_object g ?Y"
    unfolding push_object_composes[OF yof]
    by (rule push_object_cong[OF yof]) simp
  have xinto: "object_reads_agree (push_object f ?X) (push_object ?h ?S) L"
    using xpush by (simp only: xfactor left_image)
  have yinto: "object_reads_agree (push_object g ?Y) (push_object ?h ?S) Q"
    using ypush by (simp only: yfactor right_image)
  have xactual: "object_reads_agree (push_object ?h ?S) C L"
    by (rule object_reads_agree_trans[OF _ left(4)])
      (use xinto in \<open>simp add: object_reads_agree_symmetric\<close>)
  have yactual: "object_reads_agree (push_object ?h ?S) C Q"
    by (rule object_reads_agree_trans[OF _ right(4)])
      (use yinto in \<open>simp add: object_reads_agree_symmetric\<close>)
  have together: "object_reads_agree (push_object ?h ?S) C (insert r (set ps\<union>L\<union>Q))"
    using object_reads_agree_union[OF object_reads_agree_union[OF header xactual] yactual]
    by (simp add: ps Un_assoc)
  show ?case by (rule exI[of _ ?h])
    (use address image together in \<open>simp only: term_syntax.simps roots; blast\<close>)
next
  case (payload u R r v)
  have same: "R=C" by (rule environment_artifact_unique[OF payload.hyps(1,2) payload.prems(2)])
  have leaf: "payload_leaf_at C r v" using payload.hyps(3) same by simp
  have cf: "exact_formed C" using payload.hyps(1) payload.prems(2)
    by (simp add: environment_formed_def)
  have member: "r\<in>rra_carrier (object_structure C)" by (rule payload_leaf_carrier[OF leaf])
  have octets: "octets_formed r" using cf member by (auto simp: exact_formed_def)
  let ?f="\<lambda>p::local_address. r"
  have injective: "inj_on ?f (rra_carrier (object_structure (payload_syntax v)))"
    by (simp add: inj_on_def)
  have address: "finite_addressing (rra_carrier (object_structure (payload_syntax v))) ?f"
    using octets injective by (simp add: finite_addressing_def)
  have copied: "payload_leaf_at (push_object ?f (payload_syntax v)) r v"
    using payload_leaf_push[OF payload_syntax_recovers injective] by simp
  have reads: "object_reads_agree (push_object ?f (payload_syntax v)) C {r}"
    by (rule payload_leaves_reads_agree[OF copied leaf])
  show ?case by (rule exI[of _ ?f]) (use address reads in simp)
qed

section \<open>Complete native reading is exactly a complete data copy\<close>

theorem complete_data_quotation_native_iff:
  "complete_data_quoted_at C r t \<longleftrightarrow>
    self_contained_quoted_at C r t (rra_carrier (object_structure C))"
proof
  assume "complete_data_quoted_at C r t"
  then show "self_contained_quoted_at C r t (rra_carrier (object_structure C))"
    by (rule complete_data_quotation_native)
next
  assume read: "self_contained_quoted_at C r t (rra_carrier (object_structure C))"
  let ?U="rra_carrier (object_structure C)"
  let ?S="term_syntax t"
  have quote: "term_quoted_at (singleton_environment C) () r t ?U {}"
    and closed: "self_contained_term t"
    using read by (simp_all add: self_contained_quoted_at_def)
  have source: "artifact_at (singleton_environment C) () C"
    by (simp add: singleton_environment_def artifact_at_def)
  obtain f where copy: "finite_addressing (rra_carrier (object_structure ?S)) f"
    "r=f []" "?U=image f (rra_carrier (object_structure ?S))"
    "object_reads_agree (push_object f ?S) C ?U"
    using self_contained_quotation_copy[OF quote closed source] by blast
  have cf: "exact_formed C" and tf: "term_formed t"
    using self_contained_quoted_formed[OF read] by auto
  have sf: "exact_formed ?S" by (rule term_syntax_formed[OF tf])
  have copied_formed: "object_formed (push_object f ?S)"
    using exact_push_formed[OF sf copy(1)] by (simp add: exact_formed_def)
  have original_formed: "object_formed C" using cf by (simp add: exact_formed_def)
  have carrier: "rra_carrier (object_structure (push_object f ?S))=?U"
    using copy(3) by (simp add: push_object_def)
  have reads: "object_reads_agree (push_object f ?S) C
    (rra_carrier (object_structure (push_object f ?S)))"
    using copy(4) carrier by simp
  have same: "push_object f ?S=C"
    by (rule object_reads_agree_complete[OF copied_formed original_formed carrier reads])
  show "complete_data_quoted_at C r t"
    using tf closed copy(1,2) same unfolding complete_data_quoted_at_def by blast
qed

theorem complete_data_quotation_at_source:
  assumes formed: "environment_formed E" and source: "artifact_at E u C"
  shows "complete_data_quoted_at C r t \<longleftrightarrow>
    term_quoted_at E u r t (rra_carrier (object_structure C)) {}"
proof
  assume "complete_data_quoted_at C r t"
  have read: "self_contained_quoted_at C r t (rra_carrier (object_structure C))"
    by (rule complete_data_quotation_native[OF \<open>complete_data_quoted_at C r t\<close>])
  show "term_quoted_at E u r t (rra_carrier (object_structure C)) {}"
    by (rule self_contained_quoted_in_environment[OF read formed source])
next
  assume quote: "term_quoted_at E u r t (rra_carrier (object_structure C)) {}"
  have closed: "self_contained_term t"
    using term_quotation_empty_slots_iff[OF quote] by simp
  have cf: "exact_formed C" using formed source by (simp add: environment_formed_def)
  have target: "environment_formed (singleton_environment C)"
    using singleton_environment_closed[OF cf] by (simp add: environment_closed_def)
  have destination: "artifact_at (singleton_environment C) () C"
    by (simp add: singleton_environment_def artifact_at_def)
  have native: "term_quoted_at (singleton_environment C) () r t
    (rra_carrier (object_structure C)) {}"
    by (rule self_contained_quotation_transfer[OF quote closed source target destination])
  show "complete_data_quoted_at C r t"
    by (simp only: complete_data_quotation_native_iff self_contained_quoted_at_def)
      (use closed native in blast)
qed

theorem whole_term_quotation_is_complete_data:
  assumes quote: "term_quoted_at E u r t (rra_carrier (object_structure C)) K"
    and source: "artifact_at E u C"
  shows "K={} \<and> complete_data_quoted_at C r t"
proof -
  have empty: "K={}"
    using term_quoted_carrier[OF quote source] term_quoted_slots_outside[OF quote] by blast
  have formed: "environment_formed E" by (rule term_quoted_environment_formed[OF quote])
  show ?thesis using quote empty by (simp only: complete_data_quotation_at_source[OF formed source]; blast)
qed

text \<open>
  The empty external-slot boundary forces a quotation to contain only payloads
  and pairs. Each such native reading supplies an injective copy of the
  concrete syntax on precisely its read interior. Pair headers and both child
  interiors stay disjoint; incoming structure from a containing artifact is
  allowed outside the read heads.

  When the interior is the complete carrier, equality of all read heads and
  the complete data basis gives exact object equality. Thus the existing
  whole-copy profile is equivalent to ordinary native reading of the complete
  artifact. Formation excludes attachments outside its carrier. Neither
  unused positions nor additional local data can be ignored.

  This proves recognition of the complete data profile and its link to the
  native term reader. Distinct addressed artifacts remain distinct exact values.
  The equivalence gives no intrinsic privilege to this presentation topology.
\<close>

end
