theory Factor_Generation_Presentations
  imports Factor_Generation_Values Factor_Judgment_Presentations RRA_Generation_Construction
begin

section \<open>The actual source context determines the complete generation\<close>

type_synonym generation_source = "site_context\<times>generation_core"
type_synonym generation_predecessor_row =
  "local_address\<times>(local_address\<times>(local_address option definition_site\<times>generation_core))"

abbreviation generation_at_context :: "site_context \<Rightarrow> generation_core \<Rightarrow> bool" where
  "generation_at_context z G \<equiv> generation_at (fst z) (fst (snd z)) (snd (snd z)) G"

lemma generation_context_formed:
  assumes "generation_at E u r G"
  shows "environment_formed E \<and> (u,r)\<in>environment_positions E"
  using generation_at_environment_formed[OF assms] generation_at_has_anchor[OF assms]
  by (auto simp: anchor_formed_def)

definition generation_source_presents :: "generation_source \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_source_presents z t \<longleftrightarrow>
    source_root_presents (fst z) t \<and> generation_at_context (fst z) (snd z)"

theorem generation_source_presentation_class:
  "presentation_class generation_source_presents
    (\<lambda>z. generation_at_context (fst z) (snd z))
    (\<lambda>t. \<exists>z. generation_source_presents z t)"
proof -
  have unique: "generation_at_context z G \<Longrightarrow> generation_at_context z H \<Longrightarrow> G=H" for z G H
    by (rule generation_at_unique)
  have determined: "presentation_class
      (\<lambda>z t. source_root_presents (fst z) t \<and> generation_at_context (fst z) (snd z))
      (\<lambda>z. site_context_formed (fst z) \<and> generation_at_context (fst z) (snd z))
      (\<lambda>t. \<exists>z G. source_root_presents z t \<and> generation_at_context z G)"
    by (rule presentation_class_determined[OF source_root_presentation_class unique])
  have formed: "site_context_formed z" if read: "generation_at_context z G" for z G
    using generation_context_formed[OF read] by simp
  have domain: "(site_context_formed z \<and> generation_at_context z G) \<longleftrightarrow> generation_at_context z G" for z G
    using formed by blast
  have admission: "(\<exists>z G. source_root_presents z t \<and> generation_at_context z G) \<longleftrightarrow>
      (\<exists>z. generation_source_presents z t)" for t
    by (auto simp: generation_source_presents_def; metis fst_conv snd_conv)
  show ?thesis using determined
    by (simp only: presentation_class_def generation_source_presents_def domain admission)
qed

interpretation generation_sources: presentation_class generation_source_presents
  "\<lambda>z. generation_at_context (fst z) (snd z)" "\<lambda>t. \<exists>z. generation_source_presents z t"
  by (rule generation_source_presentation_class)

lemma generation_source_presents_formed:
  assumes presented: "generation_source_presents z t"
  shows "term_formed t \<and> self_contained_term t"
proof -
  obtain E u r G where shape: "z=((E,(u,r)),G)"
    by (rule that[of "fst (fst z)" "fst (snd (fst z))" "snd (snd (fst z))" "snd z"]) simp
  have source: "source_root_presents (E,(u,r)) t"
    using presented shape by (simp add: generation_source_presents_def)
  show ?thesis by (rule source_root_presents_formed[OF source])
qed

theorem generation_source_presentation_total:
  assumes source: "generation_at E u r G"
  shows "\<exists>t. generation_source_presents ((E,(u,r)),G) t \<and> term_formed t \<and> self_contained_term t"
proof -
  have domain: "generation_at_context (fst ((E,(u,r)),G)) (snd ((E,(u,r)),G))" using source by simp
  obtain t where presented: "generation_source_presents ((E,(u,r)),G) t"
    using generation_sources.total[OF domain] by blast
  show ?thesis using presented generation_source_presents_formed[OF presented] by blast
qed

definition generation_core_source_presents :: "generation_core \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_core_source_presents G t \<longleftrightarrow> (\<exists>z. generation_source_presents z t \<and> snd z=G)"

theorem generation_core_source_presentation_class:
  "presentation_class generation_core_source_presents generation_formed
    (\<lambda>t. \<exists>z. generation_source_presents z t)"
proof -
  have projected: "presentation_class (\<lambda>G t. \<exists>z. generation_source_presents z t \<and> snd z=G)
      generation_formed (\<lambda>t. \<exists>z. generation_source_presents z t)"
  proof (rule presentation_class_image[OF generation_source_presentation_class])
    fix z assume "generation_at_context (fst z) (snd z)"
    then show "generation_formed (snd z)" by (rule generation_at_formed)
  next
    fix G assume "generation_formed G"
    then obtain E :: "local_address option artifact_environment" and u where read: "generation_at E u [] G"
      using generation_presentation_total by blast
    show "\<exists>z. generation_at_context (fst z) (snd z) \<and> snd z=G"
      by (rule exI[of _ "((E,(u,[])),G)"]) (use read in simp)
  qed
  show ?thesis using projected by (simp only: presentation_class_def generation_core_source_presents_def)
qed

theorem generation_source_quotation_presentation_class:
  "presentation_class
    (composed_presentation generation_source_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. generation_at_context (fst z) (snd z))
    (\<lambda>p. \<exists>t. (\<exists>z. generation_source_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF generation_source_presentation_class])
    (use generation_source_presents_formed in blast)

section \<open>A report must present the core read from its actual source\<close>

definition generation_report_presents :: "generation_source \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_report_presents z t \<longleftrightarrow> generation_at_context (fst z) (snd z) \<and>
    factor_pair_presents source_root_presents generation_value_presents z t"

theorem generation_report_presentation_class:
  "presentation_class generation_report_presents (\<lambda>z. generation_at_context (fst z) (snd z))
    (\<lambda>t. \<exists>z. generation_report_presents z t)"
proof -
  let ?D="\<lambda>z. site_context_formed (fst z) \<and> generation_formed (snd z)"
  let ?A="\<lambda>t. \<exists>p q. (\<exists>z. source_root_presents z p) \<and>
    (\<exists>G. generation_value_presents G q) \<and> t=Pair_Term p q"
  have raw: "presentation_class (factor_pair_presents source_root_presents generation_value_presents) ?D ?A"
    by (rule factor_pair_class[OF source_root_presentation_class generation_value_presentation_class])
  have restricted: "presentation_class
      (\<lambda>z t. generation_at_context (fst z) (snd z) \<and>
        factor_pair_presents source_root_presents generation_value_presents z t)
      (\<lambda>z. generation_at_context (fst z) (snd z))
      (\<lambda>t. \<exists>z. generation_at_context (fst z) (snd z) \<and>
        factor_pair_presents source_root_presents generation_value_presents z t)"
  proof (rule presentation_class_subdomain[OF raw])
    fix z assume actual: "generation_at_context (fst z) (snd z)"
    show "?D z" using generation_context_formed[OF actual] generation_at_formed[OF actual] by simp
  qed
  show ?thesis using restricted by (simp only: presentation_class_def generation_report_presents_def)
qed

theorem generation_report_relation:
  "(\<exists>z. generation_report_presents z (Pair_Term p q)) \<longleftrightarrow>
    presented_relation source_root_presents generation_value_presents generation_at_context p q"
  by (auto simp: generation_report_presents_def factor_pair_presents_def presented_relation_def;
    metis fst_conv snd_conv)

corollary generation_report_at_presentations:
  assumes context_value: "source_root_presents z p" and core_value: "generation_value_presents G q"
  shows "(\<exists>w. generation_report_presents w (Pair_Term p q)) \<longleftrightarrow> generation_at_context z G"
  by (simp only: generation_report_relation
    presented_relation_at[OF source_root_presentation_class generation_value_presentation_class assms])

lemma generation_report_presents_formed:
  assumes "generation_report_presents z t"
  shows "term_formed t \<and> self_contained_term t"
proof -
  obtain p q where shape: "t=Pair_Term p q"
    and fields: "source_root_presents (fst z) p" "generation_value_presents (snd z) q"
    using assms by (auto simp: generation_report_presents_def factor_pair_presents_def)
  obtain E u r where source_shape: "fst z=(E,(u,r))"
    by (rule that[of "fst (fst z)" "fst (snd (fst z))" "snd (snd (fst z))"]) simp
  have source: "source_root_presents (E,(u,r)) p" using fields(1) source_shape by simp
  show ?thesis using source_root_presents_formed[OF source]
    generation_value_presents_formed[OF fields(2)] shape by simp
qed

theorem generation_report_quotation_presentation_class:
  "presentation_class
    (composed_presentation generation_report_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. generation_at_context (fst z) (snd z))
    (\<lambda>p. \<exists>t. (\<exists>z. generation_report_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF generation_report_presentation_class])
    (use generation_report_presents_formed in blast)

theorem generation_presented_fields:
  assumes "generation_source_presents ((E,(u,r)),G) t"
  shows "\<exists>R lr M payr cr. artifact_at E u R \<and> generation_syntax_at R r lr M payr cr \<and>
    anchored_at E u lr (generation_locus G) \<and>
    anchored_at E u payr (generation_payload G) \<and> anchored_at E u cr (generation_cause G)"
proof -
  have source: "generation_at E u r G" using assms by (simp add: generation_source_presents_def)
  obtain l M p c g where fields: "generation_fields_at E u r l M p c"
    and core: "G=Generation l (Abs_fset (image g (rel_dom M))) p c"
    using source by (cases rule: generation_at.cases) blast
  show ?thesis using generation_fields_syntax[OF fields] core by (auto; blast)
qed

section \<open>Every predecessor row retains its actual socket and cited site\<close>

definition generation_predecessor_rows ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    (local_address\<times>(local_address\<times>(('u\<times>local_address)\<times>generation_core))) set" where
  "generation_predecessor_rows E u r =
    {(s,(d,(z,H))). \<exists>l M p c. generation_fields_at E u r l M p c \<and>
      (s,d)\<in>M \<and> located_at E u d (fst z) (snd z) \<and>
      generation_at E (fst z) (snd z) H}"

lemma generation_predecessor_rows_at_fields:
  assumes fields: "generation_fields_at E u r l M p c"
    and assigned: "\<forall>s d. (s,d)\<in>M \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
  shows "(s,(d,(z,H)))\<in>generation_predecessor_rows E u r \<longleftrightarrow>
    (s,d)\<in>M \<and> located_at E u d (fst z) (snd z) \<and> H=g s"
proof -
  have ef: "environment_formed E" using generation_fields_formed[OF fields] by blast
  show ?thesis
  proof
    assume member: "(s,(d,(z,H)))\<in>generation_predecessor_rows E u r"
    obtain l' M' p' c' where other: "generation_fields_at E u r l' M' p' c'"
      and parts: "(s,d)\<in>M'" "located_at E u d (fst z) (snd z)"
        "generation_at E (fst z) (snd z) H"
      using member by (auto simp: generation_predecessor_rows_def)
    have same: "M=M'" using generation_fields_unique[OF fields other] by blast
    have edge: "(s,d)\<in>M" using parts(1) same by simp
    obtain v a where loc: "located_at E u d v a" and read: "generation_at E v a (g s)"
      using assigned edge by blast
    have site: "fst z=v \<and> snd z=a" by (rule located_at_unique[OF ef parts(2) loc])
    have child: "generation_at E (fst z) (snd z) (g s)" using read site by simp
    have core: "H=g s" by (rule generation_at_unique[OF parts(3) child])
    show "(s,d)\<in>M \<and> located_at E u d (fst z) (snd z) \<and> H=g s"
      using edge parts(2) core by blast
  next
    assume parts: "(s,d)\<in>M \<and> located_at E u d (fst z) (snd z) \<and> H=g s"
    obtain v a where loc: "located_at E u d v a" and read: "generation_at E v a (g s)"
      using assigned parts by blast
    have site: "fst z=v \<and> snd z=a" by (rule located_at_unique[OF ef conjunct1[OF conjunct2[OF parts]] loc])
    have child: "generation_at E (fst z) (snd z) H" using read site parts by simp
    show "(s,(d,(z,H)))\<in>generation_predecessor_rows E u r"
      using fields parts child by (auto simp: generation_predecessor_rows_def)
  qed
qed

lemma generation_predecessor_rows_fields:
  assumes fields: "generation_fields_at E u r l M p c"
    and assigned: "\<forall>s d. (s,d)\<in>M \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
  shows "rel_dom (generation_predecessor_rows E u r)=rel_dom M"
    and "single_valued (generation_predecessor_rows E u r)"
    and "finite (generation_predecessor_rows E u r)"
proof -
  let ?L="generation_predecessor_rows E u r"
  have ef: "environment_formed E" and finite: "finite M"
    using generation_fields_formed[OF fields] by blast+
  have functional: "single_valued M" using fields
    by (auto simp: generation_fields_at_def family_at_def)
  have entries: "(s,(d,(z,H)))\<in>?L \<longleftrightarrow>
      (s,d)\<in>M \<and> located_at E u d (fst z) (snd z) \<and> H=g s" for s d z H
    by (rule generation_predecessor_rows_at_fields[OF fields assigned])
  have domain: "rel_dom ?L=rel_dom M"
  proof (rule set_eqI)
    fix s
    show "s\<in>rel_dom ?L \<longleftrightarrow> s\<in>rel_dom M"
    proof
      assume "s\<in>rel_dom ?L"
      then obtain d z H where "(s,(d,(z,H)))\<in>?L" by (auto simp: rel_dom_def)
      then show "s\<in>rel_dom M" by (auto simp: entries rel_dom_def)
    next
      assume "s\<in>rel_dom M"
      then obtain d where edge: "(s,d)\<in>M" by (auto simp: rel_dom_def)
      obtain v a where loc: "located_at E u d v a" using assigned edge by blast
      have "(s,(d,((v,a),g s)))\<in>?L" using edge loc by (simp only: entries fst_conv snd_conv; blast)
      then show "s\<in>rel_dom ?L" by (auto simp: rel_dom_def)
    qed
  qed
  have unique: "single_valued ?L"
  proof (unfold single_valued_def, intro allI impI)
    fix s x y assume both: "(s,x)\<in>?L" "(s,y)\<in>?L"
    obtain d z H where x: "x=(d,(z,H))"
      by (rule that[of "fst x" "fst (snd x)" "snd (snd x)"]) simp
    obtain e w K where y: "y=(e,(w,K))"
      by (rule that[of "fst y" "fst (snd y)" "snd (snd y)"]) simp
    have left: "(s,d)\<in>M" "located_at E u d (fst z) (snd z)" "H=g s"
      and right: "(s,e)\<in>M" "located_at E u e (fst w) (snd w)" "K=g s"
      using both x y by (auto simp: entries)
    have endpoints: "d=e" using functional left(1) right(1) by (auto simp: single_valued_def)
    have other: "located_at E u d (fst w) (snd w)" using right(2) endpoints by simp
    have coordinates: "fst z=fst w \<and> snd z=snd w"
      by (rule located_at_unique[OF ef left(2) other])
    have sites: "z=w" using coordinates by (simp add: prod_eq_iff)
    show "x=y" using x y endpoints sites left(3) right(3) by simp
  qed
  show "rel_dom ?L=rel_dom M" by (rule domain)
  show "single_valued ?L" by (rule unique)
  have finite_domain: "finite (rel_dom ?L)" using finite_rel_dom[OF finite] domain by simp
  show "finite ?L" by (rule finite_single_valued[OF finite_domain unique])
qed

theorem generation_predecessor_rows_complete:
  assumes source: "generation_at E u r G"
  shows "finite (generation_predecessor_rows E u r)"
    and "single_valued (generation_predecessor_rows E u r)"
    and "bij_betw (\<lambda>row. snd (snd (snd row))) (generation_predecessor_rows E u r)
      (fset (generation_predecessors G))"
proof -
  obtain l M p c g where fields: "generation_fields_at E u r l M p c"
    and injective: "inj_on g (rel_dom M)"
    and assigned: "\<forall>s d. (s,d)\<in>M \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
    and core: "G=Generation l (Abs_fset (image g (rel_dom M))) p c"
    using source by (cases rule: generation_at.cases) blast
  let ?L="generation_predecessor_rows E u r"
  let ?last="\<lambda>row. snd (snd (snd row))"
  have functional: "single_valued ?L" and finite: "finite ?L"
    using generation_predecessor_rows_fields(2,3)[OF fields assigned] by blast+
  have entries: "(s,(d,(z,H)))\<in>?L \<longleftrightarrow>
      (s,d)\<in>M \<and> located_at E u d (fst z) (snd z) \<and> H=g s" for s d z H
    by (rule generation_predecessor_rows_at_fields[OF fields assigned])
  have finite_image: "finite (image g (rel_dom M))"
    using generation_fields_formed[OF fields] finite_rel_dom by blast
  have predecessors: "fset (generation_predecessors G)=image g (rel_dom M)"
    using finite_image by (simp add: core Abs_fset_inverse)
  have range: "image ?last ?L=image g (rel_dom M)"
  proof (rule set_eqI)
    fix H
    show "H\<in>image ?last ?L \<longleftrightarrow> H\<in>image g (rel_dom M)"
    proof
      assume "H\<in>image ?last ?L"
      then obtain row where member: "row\<in>?L" and core_value: "H=?last row" by blast
      obtain s d z K where shape: "row=(s,(d,(z,K)))"
        by (rule that[of "fst row" "fst (snd row)" "fst (snd (snd row))" "snd (snd (snd row))"]) simp
      have edge: "(s,d)\<in>M" and child: "K=g s" using member shape by (auto simp: entries)
      show "H\<in>image g (rel_dom M)" using edge child core_value shape by (auto simp: rel_dom_def)
    next
      assume "H\<in>image g (rel_dom M)"
      then obtain s d where edge: "(s,d)\<in>M" and child: "H=g s" by (auto simp: rel_dom_def)
      obtain v a where loc: "located_at E u d v a" using assigned edge by blast
      have member: "(s,(d,((v,a),H)))\<in>?L" using edge loc child by (simp only: entries fst_conv snd_conv; blast)
      show "H\<in>image ?last ?L" by (rule image_eqI[where x="(s,(d,((v,a),H)))"]) (use member in auto)
    qed
  qed
  have distinct: "inj_on ?last ?L"
  proof (rule inj_onI)
    fix x y assume members: "x\<in>?L" "y\<in>?L" and same: "?last x=?last y"
    obtain s d z H where x: "x=(s,(d,(z,H)))"
      by (rule that[of "fst x" "fst (snd x)" "fst (snd (snd x))" "snd (snd (snd x))"]) simp
    obtain a e w K where y: "y=(a,(e,(w,K)))"
      by (rule that[of "fst y" "fst (snd y)" "fst (snd (snd y))" "snd (snd (snd y))"]) simp
    have left: "(s,d)\<in>M" "H=g s" and right: "(a,e)\<in>M" "K=g a"
      using members x y by (auto simp: entries)
    have keys: "s=a" using injective left right same x y by (auto simp: inj_on_def rel_dom_def)
    have one: "(s,(d,(z,H)))\<in>?L" using members(1) x by simp
    have two: "(s,(e,(w,K)))\<in>?L" using members(2) y keys by simp
    have same_row: "(d,(z,H))=(e,(w,K))"
      by (rule single_valued_outputs[OF functional one two])
    show "x=y" using x y keys same_row by simp
  qed
  show "finite ?L" by (rule finite)
  show "single_valued ?L" by (rule functional)
  show "bij_betw ?last ?L (fset (generation_predecessors G))"
    using distinct range predecessors by (simp only: bij_betw_def)
qed

lemma generation_predecessor_row_reads:
  assumes "(s,(d,(z,H)))\<in>generation_predecessor_rows E u r"
  shows "located_at E u d (fst z) (snd z) \<and> generation_at E (fst z) (snd z) H"
  using assms by (auto simp: generation_predecessor_rows_def)

corollary generation_predecessor_rows_recover_members:
  assumes source: "generation_at E u r G"
  shows "H\<in>fset (generation_predecessors G) \<longleftrightarrow>
    (\<exists>s d z. (s,(d,(z,H)))\<in>generation_predecessor_rows E u r)"
proof -
  let ?L="generation_predecessor_rows E u r"
  let ?last="\<lambda>row. snd (snd (snd row))"
  have range: "fset (generation_predecessors G)=image ?last ?L"
    using generation_predecessor_rows_complete(3)[OF source]
    by (simp only: bij_betw_def; blast)
  show ?thesis
  proof
    assume member: "H\<in>fset (generation_predecessors G)"
    have in_image: "H\<in>image ?last ?L" using member by (simp only: range)
    obtain row where child: "H=?last row" and row: "row\<in>?L"
      using in_image by (rule imageE)
    have shape: "row=(fst row,(fst (snd row),(fst (snd (snd row)),H)))"
      using child by (simp add: prod_eq_iff)
    have complete: "(fst row,(fst (snd row),(fst (snd (snd row)),H)))\<in>?L"
      using row by (simp only: shape[symmetric])
    show "\<exists>s d z. (s,(d,(z,H)))\<in>?L"
      by (rule exI[of _ "fst row"], rule exI[of _ "fst (snd row)"],
        rule exI[of _ "fst (snd (snd row))"], rule complete)
  next
    assume "\<exists>s d z. (s,(d,(z,H)))\<in>?L"
    then obtain s d z where row: "(s,(d,(z,H)))\<in>?L" by blast
    have "H\<in>image ?last ?L"
      by (rule image_eqI[where x="(s,(d,(z,H)))"]) (use row in auto)
    then show "H\<in>fset (generation_predecessors G)" using range by simp
  qed
qed

theorem generation_predecessor_request_relation:
  assumes source: "generation_at E u r G"
  shows "((u,r),(v,a))\<in>generation_request_edges E \<longleftrightarrow>
    (\<exists>s d H. (s,(d,((v,a),H)))\<in>generation_predecessor_rows E u r)"
proof -
  have ef: "environment_formed E" by (rule generation_at_environment_formed[OF source])
  obtain l M p c g where fields: "generation_fields_at E u r l M p c"
    and assigned: "\<forall>s d. (s,d)\<in>M \<longrightarrow>
      (\<exists>w b. located_at E u d w b \<and> generation_at E w b (g s))"
    using source by (cases rule: generation_at.cases) blast
  obtain R lr payr cr where art: "artifact_at E u R" and layout: "generation_syntax_at R r lr M payr cr"
    using generation_fields_syntax[OF fields] by blast
  have roots: "generation_predecessor_roots R r=rel_ran M"
    by (rule generation_roots_from_syntax(2)[OF layout])
  have entries: "(s,(d,(z,H)))\<in>generation_predecessor_rows E u r \<longleftrightarrow>
      (s,d)\<in>M \<and> located_at E u d (fst z) (snd z) \<and> H=g s" for s d z H
    by (rule generation_predecessor_rows_at_fields[OF fields assigned])
  show ?thesis
  proof
    assume "((u,r),(v,a))\<in>generation_request_edges E"
    then obtain S d where other: "artifact_at E u S" "d\<in>generation_predecessor_roots S r"
      and loc: "located_at E u d v a" by (auto simp: generation_request_edges_def)
    have same: "R=S" by (rule environment_artifact_unique[OF ef art other(1)])
    obtain s where edge: "(s,d)\<in>M" using other(2) same roots by (auto simp: rel_ran_def)
    have "(s,(d,((v,a),g s)))\<in>generation_predecessor_rows E u r"
      using edge loc by (simp only: entries fst_conv snd_conv; blast)
    then show "\<exists>s d H. (s,(d,((v,a),H)))\<in>generation_predecessor_rows E u r" by blast
  next
    assume "\<exists>s d H. (s,(d,((v,a),H)))\<in>generation_predecessor_rows E u r"
    then obtain s d H where member: "(s,(d,((v,a),H)))\<in>generation_predecessor_rows E u r" by blast
    have edge: "(s,d)\<in>M" and loc: "located_at E u d v a" using member by (auto simp: entries)
    have predecessor: "d\<in>generation_predecessor_roots R r" using edge roots by (auto simp: rel_ran_def)
    show "((u,r),(v,a))\<in>generation_request_edges E"
      using art predecessor loc by (auto simp: generation_request_edges_def)
  qed
qed

corollary generation_request_decreases_core:
  assumes parent: "generation_at E u r G" and edge: "((u,r),(v,a))\<in>generation_request_edges E"
    and child: "generation_at E v a H"
  shows "H\<in>fset (generation_predecessors G) \<and> size H<size G"
proof -
  obtain s d K where row: "(s,(d,((v,a),K)))\<in>generation_predecessor_rows E u r"
    using edge by (simp only: generation_predecessor_request_relation[OF parent]) blast
  have read: "generation_at E v a K" using generation_predecessor_row_reads[OF row] by simp
  have same: "K=H" by (rule generation_at_unique[OF read child])
  have member: "H\<in>fset (generation_predecessors G)"
    using row same by (simp only: generation_predecessor_rows_recover_members[OF parent]; blast)
  have decreased: "size H<size G"
    by (rule predecessor_size_decreases) (use member in \<open>simp add: predecessor_edges_def\<close>)
  show ?thesis using member decreased by blast
qed

theorem generation_read_sites_well_founded:
  assumes roots: "\<forall>u r. (u,r)\<in>roots \<longrightarrow> (\<exists>G. generation_at E u r G)"
  shows "wf {(v,u). u\<in>generation_read_sites E roots \<and> (u,v)\<in>generation_request_edges E}"
proof -
  let ?core="\<lambda>s. THE G. generation_at E (fst s) (snd s) G"
  have recovered: "?core s=G" if read: "generation_at E (fst s) (snd s) G" for s G
  proof (rule the_equality[where P="\<lambda>H. generation_at E (fst s) (snd s) H" and a=G])
    show "generation_at E (fst s) (snd s) G" by (rule read)
  next
    fix H assume other: "generation_at E (fst s) (snd s) H"
    show "H=G" by (rule generation_at_unique[OF other read])
  qed
  have decrease: "{(v,u). u\<in>generation_read_sites E roots \<and> (u,v)\<in>generation_request_edges E}
      \<subseteq>measure (\<lambda>s. size (?core s))"
  proof
    fix edge assume member: "edge\<in>{(v,u). u\<in>generation_read_sites E roots \<and> (u,v)\<in>generation_request_edges E}"
    obtain u r v a where shape: "edge=((v,a),(u,r))"
      and site: "(u,r)\<in>generation_read_sites E roots"
      and link: "((u,r),(v,a))\<in>generation_request_edges E"
      using member by (auto split: prod.splits)
    obtain G where parent: "generation_at E u r G" using generation_read_sites_have_cores[OF roots site] by blast
    obtain H where child: "generation_at E v a H" using generation_request_edge_has_core[OF parent link] by blast
    have smaller: "size H<size G" using generation_request_decreases_core[OF parent link child] by blast
    have left: "?core (u,r)=G" and right: "?core (v,a)=H"
      using recovered[of "(u,r)" G] recovered[of "(v,a)" H] parent child by simp_all
    show "edge\<in>measure (\<lambda>s. size (?core s))" using shape smaller left right by simp
  qed
  show ?thesis by (rule wf_subset[OF wf_measure decrease])
qed

section \<open>Every successful retained reading preserves the same predecessor rows\<close>

lemma generation_predecessor_rows_included:
  assumes included: "environment_included F E" and formed: "environment_formed E"
  shows "generation_predecessor_rows F u r\<subseteq>generation_predecessor_rows E u r"
proof
  fix row assume member: "row\<in>generation_predecessor_rows F u r"
  obtain s d z H where shape: "row=(s,(d,(z,H)))"
    by (rule that[of "fst row" "fst (snd row)" "fst (snd (snd row))" "snd (snd (snd row))"]) simp
  obtain l M p c where fields: "generation_fields_at F u r l M p c"
    and edge: "(s,d)\<in>M" and loc: "located_at F u d (fst z) (snd z)"
    and child: "generation_at F (fst z) (snd z) H"
    using member shape by (auto simp: generation_predecessor_rows_def)
  have larger_fields: "generation_fields_at E u r l M p c"
    by (rule generation_fields_included[OF included formed fields])
  have larger_location: "located_at E u d (fst z) (snd z)"
    by (rule included_located[OF included loc])
  have larger_child: "generation_at E (fst z) (snd z) H"
    by (rule generation_at_included[OF child included formed])
  show "row\<in>generation_predecessor_rows E u r"
    using larger_fields edge larger_location larger_child
    by (auto simp: shape generation_predecessor_rows_def)
qed

theorem generation_predecessor_rows_extension:
  assumes source: "generation_at F u r G" and included: "environment_included F E"
    and formed: "environment_formed E"
  shows "generation_predecessor_rows E u r=generation_predecessor_rows F u r"
proof -
  obtain l M p c g where fields: "generation_fields_at F u r l M p c"
    and assigned: "\<forall>s d. (s,d)\<in>M \<longrightarrow>
      (\<exists>v a. located_at F u d v a \<and> generation_at F v a (g s))"
    using source by (cases rule: generation_at.cases) blast
  have larger: "generation_fields_at E u r l M p c"
    by (rule generation_fields_included[OF included formed fields])
  have assignments: "\<forall>s d. (s,d)\<in>M \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
    using assigned included formed by (meson included_located generation_at_included)
  have upper: "generation_predecessor_rows E u r\<subseteq>generation_predecessor_rows F u r"
  proof
    fix row assume member: "row\<in>generation_predecessor_rows E u r"
    obtain s d z H where shape: "row=(s,(d,(z,H)))"
      by (rule that[of "fst row" "fst (snd row)" "fst (snd (snd row))" "snd (snd (snd row))"]) simp
    have edge: "(s,d)\<in>M" and loc: "located_at E u d (fst z) (snd z)" and child: "H=g s"
      using member shape by (auto simp: generation_predecessor_rows_at_fields[OF larger assignments])
    obtain v a where actual: "located_at F u d v a" "generation_at F v a (g s)" using assigned edge by blast
    have copied: "located_at E u d v a" by (rule included_located[OF included actual(1)])
    have site: "fst z=v \<and> snd z=a" by (rule located_at_unique[OF formed loc copied])
    have location: "located_at F u d (fst z) (snd z)" using actual(1) site by simp
    show "row\<in>generation_predecessor_rows F u r"
      using edge location child by (simp only: shape generation_predecessor_rows_at_fields[OF fields assigned]; blast)
  qed
  have lower: "generation_predecessor_rows F u r\<subseteq>generation_predecessor_rows E u r"
    by (rule generation_predecessor_rows_included[OF included formed])
  show ?thesis using upper lower by blast
qed

definition generation_source_environment ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u artifact_environment" where
  "generation_source_environment E u r=request_environment E (generation_requests E {(u,r)})"

theorem generation_source_environment_reading:
  assumes formed: "environment_formed E"
  shows "generation_at (generation_source_environment E u r) u r G \<longleftrightarrow> generation_at E u r G"
proof
  assume read: "generation_at (generation_source_environment E u r) u r G"
  have included: "environment_included (generation_source_environment E u r) E"
    by (simp only: generation_source_environment_def) (rule request_environment_included)
  show "generation_at E u r G" by (rule generation_at_included[OF read included formed])
next
  assume read: "generation_at E u r G"
  have roots: "\<forall>v a. (v,a)\<in>{(u,r)} \<longrightarrow> (\<exists>H. generation_at E v a H)" using read by auto
  have site: "(u,r)\<in>generation_read_sites E {(u,r)}" using generation_read_sites_roots[of "{(u,r)}" E] by blast
  show "generation_at (generation_source_environment E u r) u r G"
    unfolding generation_source_environment_def by (rule generation_at_request_restriction[OF formed roots read site])
qed

theorem generation_source_environment_properties:
  assumes source: "generation_at E u r G"
  shows "environment_formed (generation_source_environment E u r)"
    and "generation_at (generation_source_environment E u r) u r G"
    and "generation_environment_closed (generation_source_environment E u r) {(u,r)}"
    and "generation_read_sites (generation_source_environment E u r) {(u,r)}=generation_read_sites E {(u,r)}"
    and "generation_requests (generation_source_environment E u r) {(u,r)}=generation_requests E {(u,r)}"
    and "generation_source_environment (generation_source_environment E u r) u r=generation_source_environment E u r"
    and "\<forall>v a. (v,a)\<in>generation_read_sites E {(u,r)} \<longrightarrow>
      generation_predecessor_rows (generation_source_environment E u r) v a=generation_predecessor_rows E v a"
proof -
  let ?Q="generation_requests E {(u,r)}"
  let ?R="generation_source_environment E u r"
  have ef: "environment_formed E" by (rule generation_at_environment_formed[OF source])
  have roots: "\<forall>v a. (v,a)\<in>{(u,r)} \<longrightarrow> (\<exists>H. generation_at E v a H)" using source by auto
  have requests_formed: "citation_requests_formed E ?Q" by (rule generation_requests_formed[OF ef roots])
  have requests: "generation_requests ?R {(u,r)}=?Q"
    unfolding generation_source_environment_def by (rule generation_requests_restricted[OF requests_formed])
  show "environment_formed ?R"
    unfolding generation_source_environment_def by (rule request_environment_formed[OF requests_formed])
  show "generation_at ?R u r G" using source by (simp only: generation_source_environment_reading[OF ef])
  show "generation_environment_closed ?R {(u,r)}"
    unfolding generation_source_environment_def by (rule generation_closed_restriction[OF ef roots])
  show "generation_read_sites ?R {(u,r)}=generation_read_sites E {(u,r)}"
    unfolding generation_source_environment_def by (rule generation_read_sites_restricted[OF requests_formed])
  show "generation_requests ?R {(u,r)}=?Q" by (rule requests)
  have once: "generation_source_environment ?R u r=request_environment ?R ?Q"
    using requests by (simp only: generation_source_environment_def[of ?R u r])
  have idempotent: "request_environment ?R ?Q=?R"
    unfolding generation_source_environment_def by (rule request_environment_idempotent)
  show "generation_source_environment ?R u r=?R" by (rule trans[OF once idempotent])
  show "\<forall>v a. (v,a)\<in>generation_read_sites E {(u,r)} \<longrightarrow>
      generation_predecessor_rows ?R v a=generation_predecessor_rows E v a"
  proof (intro allI impI)
    fix v a assume site: "(v,a)\<in>generation_read_sites E {(u,r)}"
    obtain H where read: "generation_at E v a H" using generation_read_sites_have_cores[OF roots site] by blast
    have retained: "generation_at ?R v a H"
      unfolding generation_source_environment_def by (rule generation_at_request_restriction[OF ef roots read site])
    have included: "environment_included ?R E"
      unfolding generation_source_environment_def by (rule request_environment_included)
    show "generation_predecessor_rows ?R v a=generation_predecessor_rows E v a"
      using generation_predecessor_rows_extension[OF retained included ef] by simp
  qed
qed

theorem generation_source_environment_least:
  assumes formed: "environment_formed E" and read: "generation_at F u r H"
    and included: "environment_included F E"
  shows "environment_included (generation_source_environment E u r) F"
proof -
  have roots: "\<forall>v a. (v,a)\<in>{(u,r)} \<longrightarrow> (\<exists>G. generation_at F v a G)" using read by auto
  have ff: "environment_formed F" by (rule generation_at_environment_formed[OF read])
  show ?thesis unfolding generation_source_environment_def
    by (rule generation_successful_reading_requires_dependencies[OF roots included formed ff])
qed

theorem generation_source_environment_fixed:
  assumes closed: "generation_environment_closed E {(u,r)}"
  shows "generation_source_environment E u r=E"
proof -
  let ?Q="generation_requests E {(u,r)}"
  have uses: "environment_uses E=environment_reachable E {u}"
    and slots: "rel_dom (environment_bindings E)=requested_slots E ?Q"
    using closed by (auto simp: generation_environment_closed_def environment_closed_def)
  obtain G where read: "generation_at E u r G" using closed by (auto simp: generation_environment_closed_def)
  have site: "(u,r)\<in>generation_read_sites E {(u,r)}" using generation_read_sites_roots[of "{(u,r)}" E] by blast
  have source: "u\<in>image fst ?Q" by (rule generation_site_has_request[OF read site])
  have root: "{u}\<subseteq>requested_uses E ?Q" using source by (auto simp: requested_uses_def)
  have edge_closed: "environment_edge_closed E (requested_uses E ?Q)"
    using slots by (auto simp: environment_edge_closed_def requested_uses_def rel_dom_def binds_slot_def)
  have coverage: "environment_uses E\<subseteq>requested_uses E ?Q"
    using environment_reachable_least[OF root edge_closed] uses by simp
  show ?thesis unfolding generation_source_environment_def
    by (rule request_environment_fixed_coverage[OF coverage]) (use slots in simp)
qed

definition generation_retention_presents ::
  "(generation_source\<times>local_address option artifact_environment) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_retention_presents z t \<longleftrightarrow> generation_source_presents (fst z) t \<and>
    snd z=generation_source_environment (fst (fst (fst z))) (fst (snd (fst (fst z)))) (snd (snd (fst (fst z))))"

theorem generation_retention_presentation_class:
  "presentation_class generation_retention_presents
    (\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and>
      snd z=generation_source_environment (fst (fst (fst z))) (fst (snd (fst (fst z)))) (snd (snd (fst (fst z)))))
    (\<lambda>t. \<exists>z. generation_source_presents z t)"
proof -
  let ?scope="\<lambda>z::generation_source.
    generation_source_environment (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z)))"
  have functional: "F=?scope z \<Longrightarrow> H=?scope z \<Longrightarrow> F=H" for z F H by simp
  have result: "presentation_class (\<lambda>z t. generation_source_presents (fst z) t \<and> snd z=?scope (fst z))
      (\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and> snd z=?scope (fst z))
      (\<lambda>t. \<exists>z F. generation_source_presents z t \<and> F=?scope z)"
    by (rule presentation_class_determined[OF generation_source_presentation_class functional])
  have reading: "generation_retention_presents =
      (\<lambda>z t. generation_source_presents (fst z) t \<and> snd z=?scope (fst z))"
    by (rule ext)+ (simp only: generation_retention_presents_def)
  have admission: "(\<lambda>t. \<exists>z F. generation_source_presents z t \<and> F=?scope z) =
      (\<lambda>t. \<exists>z. generation_source_presents z t)"
    by (rule ext) simp
  show ?thesis using result by (simp only: reading admission)
qed

theorem generation_presented_retention:
  assumes presented: "generation_retention_presents (((E,(u,r)),G),F) t"
  shows "generation_at F u r G"
    and "generation_environment_closed F {(u,r)}"
    and "generation_predecessor_rows F u r=generation_predecessor_rows E u r"
    and "\<forall>v A. artifact_at F v A \<longleftrightarrow> v\<in>requested_uses E (generation_requests E {(u,r)}) \<and> artifact_at E v A"
    and "\<forall>v s w. binds_slot F v s w \<longleftrightarrow>
      (v,s)\<in>requested_slots E (generation_requests E {(u,r)}) \<and> binds_slot E v s w"
proof -
  have source: "generation_at E u r G" and retained: "F=generation_source_environment E u r"
    using presented by (auto simp: generation_retention_presents_def generation_source_presents_def)
  show "generation_at F u r G" "generation_environment_closed F {(u,r)}"
    using generation_source_environment_properties(2,3)[OF source] retained by auto
  have site: "(u,r)\<in>generation_read_sites E {(u,r)}" using generation_read_sites_roots[of "{(u,r)}" E] by blast
  show "generation_predecessor_rows F u r=generation_predecessor_rows E u r"
    using generation_source_environment_properties(7)[OF source] retained site by blast
  show "\<forall>v A. artifact_at F v A \<longleftrightarrow> v\<in>requested_uses E (generation_requests E {(u,r)}) \<and> artifact_at E v A"
    by (simp only: retained generation_source_environment_def artifact_at_request_environment; simp)
  show "\<forall>v s w. binds_slot F v s w \<longleftrightarrow>
      (v,s)\<in>requested_slots E (generation_requests E {(u,r)}) \<and> binds_slot E v s w"
    by (simp only: retained generation_source_environment_def binds_slot_request_environment; simp)
qed

section \<open>Complete row values preserve every predecessor coordinate\<close>

definition generation_predecessor_row_formed :: "generation_predecessor_row \<Rightarrow> bool" where
  "generation_predecessor_row_formed row \<longleftrightarrow>
    octets_formed (fst row) \<and> octets_formed (fst (snd row)) \<and>
    octets_formed (snd (fst (snd (snd row)))) \<and> generation_formed (snd (snd (snd row)))"

definition generation_predecessor_row_presents :: "generation_predecessor_row \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_predecessor_row_presents row t \<longleftrightarrow> generation_predecessor_row_formed row \<and>
    factor_pair_presents (\<lambda>a p. p=Payload_Term a)
      (factor_pair_presents (\<lambda>a p. p=Payload_Term a)
        (factor_pair_presents site_coordinate_presents generation_value_presents)) row t"

theorem generation_predecessor_row_presentation_class:
  "presentation_class generation_predecessor_row_presents generation_predecessor_row_formed
    (\<lambda>t. \<exists>row. generation_predecessor_row_presents row t)"
proof -
  let ?P="\<lambda>t. \<exists>a. t=Payload_Term a"
  let ?S="\<lambda>t. \<exists>z. site_coordinate_presents z t"
  let ?G="\<lambda>t. \<exists>H. generation_value_presents H t"
  let ?tail="\<lambda>t. \<exists>p q. ?S p \<and> ?G q \<and> t=Pair_Term p q"
  let ?middle="\<lambda>t. \<exists>p q. ?P p \<and> ?tail q \<and> t=Pair_Term p q"
  let ?A="\<lambda>t. \<exists>p q. ?P p \<and> ?middle q \<and> t=Pair_Term p q"
  let ?R="factor_pair_presents (\<lambda>a p. p=Payload_Term a)
    (factor_pair_presents (\<lambda>a p. p=Payload_Term a)
      (factor_pair_presents site_coordinate_presents generation_value_presents))"
  have raw: "presentation_class ?R (\<lambda>row. generation_formed (snd (snd (snd row)))) ?A"
    using factor_pair_class[OF address_coordinate_presentation
      factor_pair_class[OF address_coordinate_presentation
        factor_pair_class[OF site_coordinate_presentation generation_value_presentation_class]]] by simp
  have restricted: "presentation_class (\<lambda>row t. generation_predecessor_row_formed row \<and> ?R row t)
      generation_predecessor_row_formed (\<lambda>t. \<exists>row. generation_predecessor_row_formed row \<and> ?R row t)"
    by (rule presentation_class_subdomain[OF raw]) (simp add: generation_predecessor_row_formed_def)
  show ?thesis using restricted by (simp only: presentation_class_def generation_predecessor_row_presents_def)
qed

lemma generation_predecessor_row_value_formed:
  assumes presented: "generation_predecessor_row_presents row t"
  shows "term_formed t \<and> self_contained_term t"
proof -
  obtain s d z H where shape: "row=(s,(d,(z,H)))"
    by (rule that[of "fst row" "fst (snd row)" "fst (snd (snd row))" "snd (snd (snd row))"]) simp
  obtain v where encoded: "t=Pair_Term (Payload_Term s) (Pair_Term (Payload_Term d)
      (Pair_Term (site_data_term (fst z) (snd z)) v))"
    and core: "generation_value_presents H v"
    using presented shape by (auto simp: generation_predecessor_row_presents_def factor_pair_presents_def)
  have coordinates: "octets_formed s" "octets_formed d" "octets_formed (snd z)"
    using presented shape by (auto simp: generation_predecessor_row_presents_def generation_predecessor_row_formed_def)
  show ?thesis using generation_value_presents_formed[OF core] coordinates encoded by simp
qed

lemma generation_predecessor_rows_formed:
  assumes member: "row\<in>generation_predecessor_rows E u r"
  shows "generation_predecessor_row_formed row"
proof -
  obtain s d z H where shape: "row=(s,(d,(z,H)))"
    by (rule that[of "fst row" "fst (snd row)" "fst (snd (snd row))" "snd (snd (snd row))"]) simp
  obtain l M p c where fields: "generation_fields_at E u r l M p c"
    and edge: "(s,d)\<in>M" and child: "generation_at E (fst z) (snd z) H"
    using member shape by (auto simp: generation_predecessor_rows_def)
  obtain R pr where formed: "environment_formed E" and art: "artifact_at E u R" and family: "family_at R pr M"
    using fields by (auto simp: generation_fields_at_def)
  have exact: "exact_formed R" using formed art by (auto simp: environment_formed_def)
  have positions: "s\<in>rra_carrier (object_structure R)" "d\<in>rra_carrier (object_structure R)"
    using family edge by (auto simp: family_at_def headed_incidence_def object_formed_def rra_formed_def)
  have source_addresses: "octets_formed s" "octets_formed d" using exact positions by (auto simp: exact_formed_def)
  have site: "z\<in>environment_positions E" using generation_context_formed[OF child] by simp
  have address: "octets_formed (snd z)" by (rule environment_position_address[OF formed site])
  have core: "generation_formed H" by (rule generation_at_formed[OF child])
  show ?thesis using shape source_addresses address core by (simp add: generation_predecessor_row_formed_def)
qed

interpretation generation_predecessor_collections: presentation_class
  "data_collection_presents generation_predecessor_row_presents"
  "\<lambda>L. finite L \<and> (\<forall>row\<in>L. generation_predecessor_row_formed row)"
  "presented_predicate (data_sequence_presents generation_predecessor_row_presents) distinct"
  by (rule data_collection_presentation_class[OF generation_predecessor_row_presentation_class])

definition generation_predecessor_report_presents ::
  "(generation_source\<times>generation_predecessor_row set) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_predecessor_report_presents z t \<longleftrightarrow>
    snd z=generation_predecessor_rows (fst (fst (fst z))) (fst (snd (fst (fst z)))) (snd (snd (fst (fst z)))) \<and>
    factor_pair_presents generation_source_presents
      (data_collection_presents generation_predecessor_row_presents) z t"

theorem generation_predecessor_report_presentation_class:
  "presentation_class generation_predecessor_report_presents
    (\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and>
      snd z=generation_predecessor_rows (fst (fst (fst z))) (fst (snd (fst (fst z)))) (snd (snd (fst (fst z)))))
    (\<lambda>t. \<exists>z. generation_predecessor_report_presents z t)"
proof -
  let ?rows="\<lambda>z::generation_source.
    generation_predecessor_rows (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z)))"
  let ?R="factor_pair_presents generation_source_presents (data_collection_presents generation_predecessor_row_presents)"
  let ?D="\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and> snd z=?rows (fst z)"
  let ?raw="\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and>
    (finite (snd z) \<and> (\<forall>row\<in>snd z. generation_predecessor_row_formed row))"
  let ?A="\<lambda>t. \<exists>p q. (\<exists>z. generation_source_presents z p) \<and>
    presented_predicate (data_sequence_presents generation_predecessor_row_presents) distinct q \<and> t=Pair_Term p q"
  have fields: "presentation_class ?R ?raw ?A"
    by (rule factor_pair_class[OF generation_source_presentation_class
      generation_predecessor_collections.presentation_class_axioms])
  have restricted: "presentation_class (\<lambda>z t. ?D z \<and> ?R z t) ?D (\<lambda>t. \<exists>z. ?D z \<and> ?R z t)"
  proof (rule presentation_class_subdomain[OF fields])
    fix z assume domain: "?D z"
    have native: "generation_at_context (fst (fst z)) (snd (fst z))" using domain by blast
    have finite: "finite (?rows (fst z))" by (rule generation_predecessor_rows_complete(1)[OF native])
    have each: "\<forall>row\<in>?rows (fst z). generation_predecessor_row_formed row"
      by (blast intro: generation_predecessor_rows_formed)
    show "?raw z" using domain finite each by simp
  qed
  have reading: "(?D z \<and> ?R z t) \<longleftrightarrow> generation_predecessor_report_presents z t" for z t
    using generation_sources.subject_boundary
    by (auto simp: generation_predecessor_report_presents_def factor_pair_presents_def)
  show ?thesis using restricted by (simp only: reading)
qed

theorem generation_predecessor_report_relation:
  "(\<exists>z. generation_predecessor_report_presents z (Pair_Term p q)) \<longleftrightarrow>
    presented_relation generation_source_presents (data_collection_presents generation_predecessor_row_presents)
      (\<lambda>z L. L=generation_predecessor_rows (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z)))) p q"
  by (auto simp: generation_predecessor_report_presents_def factor_pair_presents_def presented_relation_def;
    metis fst_conv snd_conv)

corollary generation_predecessor_report_at_presentations:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and rows: "data_collection_presents generation_predecessor_row_presents L q"
  shows "(\<exists>z. generation_predecessor_report_presents z (Pair_Term p q)) \<longleftrightarrow>
    L=generation_predecessor_rows E u r"
  by (simp only: generation_predecessor_report_relation
    presented_relation_at[OF generation_source_presentation_class
      generation_predecessor_collections.presentation_class_axioms assms] fst_conv snd_conv)

lemma generation_predecessor_report_formed:
  assumes "generation_predecessor_report_presents z t"
  shows "term_formed t \<and> self_contained_term t"
proof -
  obtain p q where source: "generation_source_presents (fst z) p"
    and rows: "data_collection_presents generation_predecessor_row_presents (snd z) q"
    and shape: "t=Pair_Term p q"
    using assms by (auto simp: generation_predecessor_report_presents_def factor_pair_presents_def)
  have first: "term_formed p \<and> self_contained_term p" by (rule generation_source_presents_formed[OF source])
  have formed: "term_formed q" by (rule data_collection_presents_formed[OF rows])
    (use generation_predecessor_row_value_formed in blast)
  have closed: "self_contained_term q" by (rule data_collection_presents_self_contained[OF rows])
    (use generation_predecessor_row_value_formed in blast)
  show ?thesis using first formed closed shape by simp
qed

theorem generation_predecessor_report_quotation_class:
  "presentation_class
    (composed_presentation generation_predecessor_report_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and>
      snd z=generation_predecessor_rows (fst (fst (fst z))) (fst (snd (fst (fst z)))) (snd (snd (fst (fst z)))))
    (\<lambda>p. \<exists>t. (\<exists>z. generation_predecessor_report_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF generation_predecessor_report_presentation_class])
    (use generation_predecessor_report_formed in blast)

theorem generation_predecessor_report_total:
  assumes source: "generation_at E u r G"
  shows "\<exists>p q. generation_source_presents ((E,(u,r)),G) p \<and>
    data_collection_presents generation_predecessor_row_presents (generation_predecessor_rows E u r) q \<and>
    generation_predecessor_report_presents (((E,(u,r)),G),generation_predecessor_rows E u r) (Pair_Term p q) \<and>
    complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q)"
proof -
  obtain p where source_value: "generation_source_presents ((E,(u,r)),G) p"
    using generation_source_presentation_total[OF source] by blast
  have domain: "finite (generation_predecessor_rows E u r) \<and>
      (\<forall>row\<in>generation_predecessor_rows E u r. generation_predecessor_row_formed row)"
    using generation_predecessor_rows_complete(1)[OF source] generation_predecessor_rows_formed by blast
  obtain q where rows: "data_collection_presents generation_predecessor_row_presents (generation_predecessor_rows E u r) q"
    using generation_predecessor_collections.total[OF domain] by blast
  have report: "generation_predecessor_report_presents
      (((E,(u,r)),G),generation_predecessor_rows E u r) (Pair_Term p q)"
    using source_value rows by (simp add: generation_predecessor_report_presents_def)
  have formed: "term_formed (Pair_Term p q)" and closed: "self_contained_term (Pair_Term p q)"
    using generation_predecessor_report_formed[OF report] by blast+
  have quote: "complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q)"
    by (rule complete_data_quotation_total[OF formed closed])
  show ?thesis using source_value rows report quote by blast
qed

corollary generation_predecessor_report_retention:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and retained: "generation_source_presents ((generation_source_environment E u r,(u,r)),G) p'"
    and rows: "data_collection_presents generation_predecessor_row_presents L q"
  shows "(\<exists>z. generation_predecessor_report_presents z (Pair_Term p' q)) \<longleftrightarrow>
    (\<exists>z. generation_predecessor_report_presents z (Pair_Term p q))"
proof -
  have actual: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have site: "(u,r)\<in>generation_read_sites E {(u,r)}" using generation_read_sites_roots[of "{(u,r)}" E] by blast
  have same: "generation_predecessor_rows (generation_source_environment E u r) u r=generation_predecessor_rows E u r"
    using generation_source_environment_properties(7)[OF actual] site by blast
  show ?thesis by (simp only: generation_predecessor_report_at_presentations[OF retained rows]
    generation_predecessor_report_at_presentations[OF source rows] same)
qed

text \<open>
  The source class retains its actual environment and selected site. The core
  is recovered by the existing generation reading. Its covered image includes
  every formed finite core, while the complete source remains recoverable from
  each presentation. A core report is compatible only when it presents the
  core actually read from that same source.

  Predecessor rows retain the socket, citation endpoint, actual destination
  use and address, and exact child core. Their domain is the complete native
  socket domain. Each predecessor core occurs once. Every row in this native
  collection recovers a real recursive reading at its stated site. The
  request-edge equation preserves and reflects those actual sites. A different presentation of an
  equal child core does not thereby become the cited destination.

  The recovered core strictly decreases along every readable predecessor
  edge. This proves well-foundedness on the complete set of recursively read
  sites. The source restriction preserves all those rows, read sites, and
  citation requests. It is closed, idempotent, and included in every retained
  subenvironment that can still read the generation. Its artifact and binding
  equations account for every retained item.

  The row-report class uses products and complete collections, constrained by
  that actual native relation. Every valid generation has such a report and
  a complete quotation. All collection orders and member presentations remain
  available. The explicit relation and retention equations establish joint
  compatibility; separate class recovery is not substituted for those proofs.

  These class and relation theorems do not add a native admission clause.
  Native checking of the remaining recursive generation and higher protocol
  relations still requires an ordinary program with its own exact contract.
\<close>

end
