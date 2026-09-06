theory Factor_Construction_Recovery
  imports Factor_Construction_Presentations
begin

section \<open>No loss of a source choice or an origin edge\<close>

lemma construction_selection_table_exact:
  assumes first: "construction_selection_formed xs B W"
    and second: "construction_selection_formed ys C X"
  shows "finite_table_term Payload_Term construction_selection_term (construction_selections W) =
    finite_table_term Payload_Term construction_selection_term (construction_selections X)
    \<longleftrightarrow> construction_selections W = construction_selections X"
proof -
  let ?A = "construction_selections W"
  let ?D = "construction_selections X"
  have af: "finite ?A" and asv: "single_valued ?A"
    and df: "finite ?D" and dsv: "single_valued ?D"
    using first second by (auto simp: construction_selection_formed_def)
  have sets_finite: "\<And>z. z \<in> rel_ran ?A \<union> rel_ran ?D \<Longrightarrow> finite (snd z)"
    using first second
    by (auto simp: rel_ran_def construction_selection_formed_def source_selection_valid_def)
  have vals: "inj_on construction_selection_term (rel_ran ?A \<union> rel_ran ?D)"
  proof (rule inj_onI)
    fix z w assume zm: "z \<in> rel_ran ?A \<union> rel_ran ?D"
      and wm: "w \<in> rel_ran ?A \<union> rel_ran ?D"
      and same: "construction_selection_term z = construction_selection_term w"
    obtain j A where zp: "z=(j,A)" by (cases z) auto
    obtain k D where wp: "w=(k,D)" by (cases w) auto
    have afin: "finite A" using sets_finite[OF zm] zp by simp
    have dfin: "finite D" using sets_finite[OF wm] wp by simp
    show "z=w" using same zp wp construction_selection_term_exact[OF afin dfin] by simp
  qed
  show ?thesis
    by (rule finite_table_term_exact[OF af asv df dsv payload_term_injective vals])
qed

theorem construction_claim_exact:
  assumes first: "source_constructs xs B W R" and second: "source_constructs ys C X S"
  shows "construction_claim_term xs B W R = construction_claim_term ys C X S \<longleftrightarrow>
    xs=ys \<and> B=C \<and> W=X \<and> R=S"
proof
  assume same: "construction_claim_term xs B W R = construction_claim_term ys C X S"
  have inputs: "artifact_list_term xs = artifact_list_term ys"
    and bases: "finite_table_term Payload_Term (Target_Term \<circ> Whole_Artifact) B =
      finite_table_term Payload_Term (Target_Term \<circ> Whole_Artifact) C"
    and choices: "finite_table_term Payload_Term construction_selection_term (construction_selections W) =
      finite_table_term Payload_Term construction_selection_term (construction_selections X)"
    and origins: "finite_table_term construction_atom_term Payload_Term (construction_origins W) =
      finite_table_term construction_atom_term Payload_Term (construction_origins X)"
    and result_eq: "R=S"
    using same by (auto simp: construction_claim_term_def enumeration_term_injective)
  have input_eq: "xs=ys" using inputs by (simp add: artifact_list_term_exact)
  have bv: "inj_on (Target_Term \<circ> Whole_Artifact) (rel_ran B \<union> rel_ran C)"
    by (rule inj_onI) simp
  have base_eq: "B=C"
    using bases finite_table_term_exact[
      OF source_construction_finite(1,2)[OF first] source_construction_finite(1,2)[OF second]
        payload_term_injective bv] by blast
  have wf: "construction_selection_formed xs B W"
    and xf: "construction_selection_formed ys C X"
    using first second by (auto simp: source_constructs_def)
  have selection_eq: "construction_selections W = construction_selections X"
    using choices construction_selection_table_exact[OF wf xf] by blast
  have ov: "inj_on Payload_Term (rel_ran (construction_origins W) \<union> rel_ran (construction_origins X))"
    by (rule inj_onI) simp
  have origin_eq: "construction_origins W = construction_origins X"
    using origins finite_table_term_exact[
      OF source_construction_finite(5,6)[OF first] source_construction_finite(5,6)[OF second]
        construction_atom_term_injective ov] by blast
  have wx: "W=X" using selection_eq origin_eq by (cases W; cases X) auto
  show "xs=ys \<and> B=C \<and> W=X \<and> R=S" using input_eq base_eq wx result_eq by blast
next
  assume "xs=ys \<and> B=C \<and> W=X \<and> R=S"
  then show "construction_claim_term xs B W R = construction_claim_term ys C X S" by simp
qed

theorem native_construction_claim_unique:
  assumes first: "native_construction_claim_at E u r xs B W R I K"
    and second: "native_construction_claim_at E u r ys C X S J L"
  shows "xs=ys \<and> B=C \<and> W=X \<and> R=S \<and> I=J \<and> K=L"
proof -
  obtain t v where left: "construction_claim_presents xs B W R t" "term_quoted_at E u r t I K"
    and right: "construction_claim_presents ys C X S v" "term_quoted_at E u r v J L"
    using first second by (auto simp: native_construction_claim_at_def)
  have same: "t=v" and bounds: "I=J" "K=L"
    using term_quoted_unique[OF left(2) right(2)] by auto
  have other: "construction_claim_presents ys C X S t" using right(1) same by simp
  show ?thesis using construction_claim_presents_unique[OF left(1) other] bounds by blast
qed

theorem native_construction_changed_account_rejected:
  assumes "native_construction_claim_at E u r xs B W R I K"
    "xs \<noteq> ys \<or> B \<noteq> C \<or> W \<noteq> X \<or> R \<noteq> S \<or> I \<noteq> J \<or> K \<noteq> L"
  shows "\<not> native_construction_claim_at E u r ys C X S J L"
  using native_construction_claim_unique[OF assms(1)] assms(2) by blast

text \<open>
  A native claim recovers the complete construction account and both quotation
  boundaries. Equal piece material does not erase different source selections.
  Equal output artifacts do not erase different origin graphs. Changing any
  input occurrence, base entry, selected fragment, origin edge, or output
  changes the checked argument.
\<close>

end
