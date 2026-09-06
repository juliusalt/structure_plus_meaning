theory RRA_Assembly
  imports RRA_Fragment
begin

section \<open>Exact piece occurrences\<close>

record 's exact_piece_family =
  piece_graph :: "('s \<times> exact_artifact) set"

definition piece_family_formed :: "'s exact_piece_family \<Rightarrow> bool" where
  "piece_family_formed P \<longleftrightarrow>
     finite (piece_graph P) \<and>
     single_valued (piece_graph P) \<and>
     (\<forall>s R. (s,R) \<in> piece_graph P \<longrightarrow> exact_formed R)"

definition piece_slots :: "'s exact_piece_family \<Rightarrow> 's set" where
  "piece_slots P = rel_dom (piece_graph P)"

definition piece_at :: "'s exact_piece_family \<Rightarrow> 's \<Rightarrow> exact_artifact" where
  "piece_at P s = rel_value (piece_graph P) s"

definition copied_carrier ::
  "'s exact_piece_family \<Rightarrow> ('s \<times> local_address) set" where
  "copied_carrier P =
     {(s,a). s \<in> piece_slots P \<and>
             a \<in> rra_carrier (object_structure (piece_at P s))}"

definition copied_incidence ::
  "'s exact_piece_family \<Rightarrow>
   (('s \<times> local_address) \<times> ('s \<times> local_address) \<times>
    ('s \<times> local_address)) set" where
  "copied_incidence P =
     {((s,r),(s,p),(s,x)) |s r p x.
        s \<in> piece_slots P \<and>
        (r,p,x) \<in> rra_incidence (object_structure (piece_at P s))}"

section \<open>Copied data in the general basis\<close>

definition copied_basis :: "'s exact_piece_family \<Rightarrow> ('s \<times> local_address,octets) opaque_basis" where
  "copied_basis P =
    \<lparr>bag_count = (\<lambda>((s,a),v).
       if s \<in> piece_slots P then bag_count (object_data (piece_at P s)) (a,v) else 0),
     functional_bindings =
       {((s,a),v). s \<in> piece_slots P \<and> (a,v) \<in> functional_bindings (object_data (piece_at P s))}\<rparr>"

lemma piece_slots_finite:
  assumes "piece_family_formed P"
  shows "finite (piece_slots P)"
proof -
  have "piece_slots P = fst ` piece_graph P"
    by (auto simp: piece_slots_def rel_dom_def intro: rev_image_eqI)
  with assms show ?thesis by (simp add: piece_family_formed_def)
qed

lemma piece_at_formed:
  assumes "piece_family_formed P" "s \<in> piece_slots P"
  shows "exact_formed (piece_at P s)"
proof -
  obtain R where pair: "(s,R) \<in> piece_graph P"
    using assms(2) by (auto simp: piece_slots_def rel_dom_def)
  have sv: "single_valued (piece_graph P)"
    using assms(1) by (simp add: piece_family_formed_def)
  have "piece_at P s = R"
    using rel_value_eq[OF sv pair] by (simp add: piece_at_def)
  with pair assms(1) show ?thesis by (auto simp: piece_family_formed_def)
qed

lemma copied_carrier_finite:
  assumes "piece_family_formed P"
  shows "finite (copied_carrier P)"
proof -
  have eq: "copied_carrier P =
    Sigma (piece_slots P) (\<lambda>s. rra_carrier (object_structure (piece_at P s)))"
    by (auto simp: copied_carrier_def)
  show ?thesis unfolding eq
    by (rule finite_SigmaI[OF piece_slots_finite[OF assms]])
       (use piece_at_formed[OF assms] in \<open>auto simp: exact_formed_def object_formed_def rra_formed_def\<close>)
qed

lemma copied_incidence_union:
  "copied_incidence P = (\<Union>s\<in>piece_slots P.
    (\<lambda>(r,p,x). ((s,r),(s,p),(s,x))) ` rra_incidence (object_structure (piece_at P s)))"
  by (auto simp: copied_incidence_def intro: rev_image_eqI)

lemma copied_structure_formed:
  assumes "piece_family_formed P"
  shows "rra_formed \<lparr>rra_carrier = copied_carrier P, rra_incidence = copied_incidence P\<rparr>"
proof -
  have fin: "finite (copied_incidence P)"
    unfolding copied_incidence_union
    by (rule finite_UN_I[OF piece_slots_finite[OF assms]])
       (use piece_at_formed[OF assms] in \<open>auto simp: exact_formed_def object_formed_def rra_formed_def\<close>)
  show ?thesis
    using copied_carrier_finite[OF assms] fin piece_at_formed[OF assms]
    by (auto simp: rra_formed_def copied_incidence_def copied_carrier_def
      exact_formed_def object_formed_def)
qed

lemma copied_bag_support:
  "bag_support (copied_basis P) = (\<Union>s\<in>piece_slots P.
    (\<lambda>(a,v). ((s,a),v)) ` bag_support (object_data (piece_at P s)))"
  by (auto simp: bag_support_def copied_basis_def image_iff split: if_splits)

lemma copied_functional_bindings:
  "functional_bindings (copied_basis P) = (\<Union>s\<in>piece_slots P.
    (\<lambda>(a,v). ((s,a),v)) ` functional_bindings (object_data (piece_at P s)))"
  by (auto simp: copied_basis_def intro: rev_image_eqI)

lemma copied_basis_formed:
  assumes "piece_family_formed P"
  shows "basis_formed (copied_carrier P) (copied_basis P)"
proof -
  have pf: "\<And>s. s \<in> piece_slots P \<Longrightarrow>
    basis_formed (rra_carrier (object_structure (piece_at P s))) (object_data (piece_at P s))"
    using piece_at_formed[OF assms] by (simp add: exact_formed_def object_formed_def)
  have bs: "finite (bag_support (copied_basis P))"
    unfolding copied_bag_support
    by (rule finite_UN_I[OF piece_slots_finite[OF assms]])
       (use pf in \<open>auto simp: basis_formed_def\<close>)
  have fs: "finite (functional_bindings (copied_basis P))"
    unfolding copied_functional_bindings
    by (rule finite_UN_I[OF piece_slots_finite[OF assms]])
       (use pf in \<open>auto simp: basis_formed_def\<close>)
  show ?thesis using bs fs pf
    by (auto simp: basis_formed_def copied_basis_def copied_carrier_def
      bag_support_def single_valued_def split: if_splits; fastforce)
qed

lemma copied_values_formed:
  assumes "piece_family_formed P" "v \<in> basis_values (copied_basis P)"
  shows "octets_formed v"
proof -
  from assms(2) obtain s where slot: "s \<in> piece_slots P"
    and val: "v \<in> basis_values (object_data (piece_at P s))"
    by (force simp: basis_values_def copied_bag_support copied_functional_bindings image_iff)
  show ?thesis
    using piece_at_formed[OF assms(1) slot] val by (auto simp: exact_formed_def)
qed

section \<open>One complete assembly account\<close>

record 's assembly_witness =
  assembly_pieces :: "'s exact_piece_family"
  assembly_origin :: "(('s \<times> local_address) \<times> local_address) set"

definition expected_incidence ::
  "'s exact_piece_family \<Rightarrow>
   ((('s \<times> local_address) \<times> local_address) set) \<Rightarrow>
   (local_address \<times> local_address \<times> local_address) set" where
  "expected_incidence P q = ternary_image q (copied_incidence P)"

definition assembled_data ::
  "'s exact_piece_family \<Rightarrow> ((('s \<times> local_address) \<times> local_address) set) \<Rightarrow>
   (local_address,octets) opaque_basis \<Rightarrow> bool" where
  "assembled_data P q D \<longleftrightarrow>
    D = push_basis (copied_carrier P) (rel_value q) (copied_basis P)"

definition assembled_output ::
  "'s exact_piece_family \<Rightarrow>
   ((('s \<times> local_address) \<times> local_address) set) \<Rightarrow> exact_artifact" where
  "assembled_output P q =
    \<lparr>object_structure =
       \<lparr>rra_carrier = rel_ran q, rra_incidence = expected_incidence P q\<rparr>,
     object_data = push_basis (copied_carrier P) (rel_value q) (copied_basis P)\<rparr>"

definition assembly_output :: "'s assembly_witness \<Rightarrow> exact_artifact" where
  "assembly_output W = assembled_output (assembly_pieces W) (assembly_origin W)"

definition assembly_relation ::
  "'s exact_piece_family \<Rightarrow>
   ((('s \<times> local_address) \<times> local_address) set) \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "assembly_relation P q R \<longleftrightarrow>
     piece_family_formed P \<and> exact_formed R \<and>
     exact_map (copied_carrier P) (rra_carrier (object_structure R)) q \<and>
     rra_incidence (object_structure R) = expected_incidence P q \<and>
     assembled_data P q (object_data R)"

lemma assembly_relation_determines_output:
  assumes "assembly_relation P q R"
  shows "R = assembled_output P q"
  using assms
  by (auto simp: assembly_relation_def assembled_output_def assembled_data_def
    exact_map_def exact_identity_iff rra_identity)

definition K2 :: "'s assembly_witness \<Rightarrow> bool" where
  "K2 W \<longleftrightarrow>
     piece_family_formed (assembly_pieces W) \<and>
     exact_formed (assembly_output W) \<and>
     exact_map (copied_carrier (assembly_pieces W))
               (rra_carrier (object_structure (assembly_output W)))
               (assembly_origin W) \<and>
     rra_incidence (object_structure (assembly_output W)) =
       expected_incidence (assembly_pieces W) (assembly_origin W) \<and>
     assembled_data (assembly_pieces W) (assembly_origin W)
                    (object_data (assembly_output W))"

lemma K2_output_determined:
  assumes "assembly_pieces W = assembly_pieces V"
    "assembly_origin W = assembly_origin V"
  shows "assembly_output W = assembly_output V"
  using assms by (simp add: assembly_output_def)

lemma assembly_relation_iff:
  "assembly_relation (assembly_pieces W) (assembly_origin W) R \<longleftrightarrow>
    K2 W \<and> R = assembly_output W"
  using assembly_relation_determines_output[
    of "assembly_pieces W" "assembly_origin W" R]
  by (auto simp: K2_def assembly_relation_def assembly_output_def)

lemma assembled_output_formed:
  assumes pieces: "piece_family_formed P"
    and mapping: "exact_map (copied_carrier P) (rel_ran q) q"
    and compatible: "basis_compatible (rel_value q) (copied_basis P)"
    and addresses: "\<forall>a\<in>rel_ran q. octets_formed a"
  shows "exact_formed (assembled_output P q)"
proof -
  let ?S = "\<lparr>rra_carrier = copied_carrier P, rra_incidence = copied_incidence P\<rparr>"
  have range: "rel_value q ` copied_carrier P = rel_ran q"
    by (rule exact_map_value_image[OF mapping])
  have seq: "object_structure (assembled_output P q) = push_structure (rel_value q) ?S"
    using range
    by (auto simp: assembled_output_def expected_incidence_def ternary_image_def
      push_structure_def rra_identity intro: rev_image_eqI; blast)
  have sf: "rra_formed (object_structure (assembled_output P q))"
    unfolding seq by (rule push_structure_formed[OF copied_structure_formed[OF pieces]])
  have df: "basis_formed (rel_ran q)
      (push_basis (copied_carrier P) (rel_value q) (copied_basis P))"
    using push_basis_formed_iff[OF copied_basis_formed[OF pieces], where f="rel_value q"]
      compatible range by simp
  have vals: "\<forall>v\<in>basis_values (object_data (assembled_output P q)). octets_formed v"
    using pushed_basis_values[of "copied_carrier P" "rel_value q" "copied_basis P"]
      copied_values_formed[OF pieces]
    by (auto simp: assembled_output_def)
  show ?thesis
    using sf df vals addresses
    by (simp add: exact_formed_def object_formed_def assembled_output_def)
qed

lemma K2_iff_complete_compatible_origins:
  "K2 W \<longleftrightarrow>
    piece_family_formed (assembly_pieces W) \<and>
    exact_map (copied_carrier (assembly_pieces W)) (rel_ran (assembly_origin W))
      (assembly_origin W) \<and>
    basis_compatible (rel_value (assembly_origin W)) (copied_basis (assembly_pieces W)) \<and>
    (\<forall>a\<in>rel_ran (assembly_origin W). octets_formed a)"
proof
  assume k: "K2 W"
  have sv: "single_valued (functional_bindings (object_data (assembly_output W)))"
    using k by (simp add: K2_def exact_formed_def object_formed_def basis_formed_def)
  have compatible: "basis_compatible (rel_value (assembly_origin W)) (copied_basis (assembly_pieces W))"
    using sv by (simp add: assembly_output_def assembled_output_def pushed_functional_single_valued)
  show "piece_family_formed (assembly_pieces W) \<and>
    exact_map (copied_carrier (assembly_pieces W)) (rel_ran (assembly_origin W)) (assembly_origin W) \<and>
    basis_compatible (rel_value (assembly_origin W)) (copied_basis (assembly_pieces W)) \<and>
    (\<forall>a\<in>rel_ran (assembly_origin W). octets_formed a)"
    using k compatible
    by (auto simp: K2_def exact_formed_def assembly_output_def assembled_output_def)
next
  assume c: "piece_family_formed (assembly_pieces W) \<and>
    exact_map (copied_carrier (assembly_pieces W)) (rel_ran (assembly_origin W)) (assembly_origin W) \<and>
    basis_compatible (rel_value (assembly_origin W)) (copied_basis (assembly_pieces W)) \<and>
    (\<forall>a\<in>rel_ran (assembly_origin W). octets_formed a)"
  have "exact_formed (assembly_output W)"
    unfolding assembly_output_def by (rule assembled_output_formed) (use c in auto)
  with c show "K2 W"
    by (simp add: K2_def assembly_output_def assembled_output_def assembled_data_def)
qed

lemma K2_finite_compatibility_check:
  assumes "set entries = functional_bindings (copied_basis (assembly_pieces W))"
  shows "K2 W \<longleftrightarrow>
    piece_family_formed (assembly_pieces W) \<and>
    exact_map (copied_carrier (assembly_pieces W)) (rel_ran (assembly_origin W)) (assembly_origin W) \<and>
    compatible_bindings (rel_value (assembly_origin W)) entries \<and>
    (\<forall>a\<in>rel_ran (assembly_origin W). octets_formed a)"
  using basis_compatibility_finite_check[OF assms, where f="rel_value (assembly_origin W)"]
  by (simp add: K2_iff_complete_compatible_origins)

lemma assembly_functional_entries_exist:
  assumes "piece_family_formed P"
  shows "\<exists>entries. set entries = functional_bindings (copied_basis P)"
proof -
  have "finite (functional_bindings (copied_basis P))"
    using copied_basis_formed[OF assms] by (simp add: basis_formed_def)
  then show ?thesis by (rule finite_list)
qed

lemma piece_family_has_assembly:
  assumes pieces: "piece_family_formed P"
  shows "\<exists>W. assembly_pieces W = P \<and> K2 W"
proof -
  obtain f where f: "finite_addressing (copied_carrier P) f"
    using finite_addressing_exists[OF copied_carrier_finite[OF pieces]] by blast
  let ?q = "graph_map (copied_carrier P) f"
  let ?W = "\<lparr>assembly_pieces = P, assembly_origin = ?q\<rparr>"
  have mapping: "exact_map (copied_carrier P) (rel_ran ?q) ?q"
    using graph_map_exact[OF copied_carrier_finite[OF pieces], where f=f]
    by (simp add: graph_map_ran)
  have inj: "inj_on (rel_value ?q) (copied_carrier P)"
    using f by (auto simp: finite_addressing_def inj_on_def rel_value_graph_map)
  have compatible: "basis_compatible (rel_value ?q) (copied_basis P)"
    by (rule injective_gluing_compatible[OF copied_basis_formed[OF pieces] inj])
  have "K2 ?W"
    using pieces mapping compatible f
    by (simp add: K2_iff_complete_compatible_origins graph_map_ran finite_addressing_def)
  then show ?thesis by (rule_tac x="?W" in exI) simp
qed

lemma empty_family_basis:
  assumes "piece_graph P = {}"
  shows "copied_basis P = empty_basis" "copied_carrier P = {}"
  using assms
  by (auto simp: copied_basis_def copied_carrier_def piece_slots_def rel_dom_def
    basis_identity empty_basis_def fun_eq_iff)

lemma empty_family_data_determined:
  assumes "piece_graph P = {}" "assembled_data P q D"
  shows "D = empty_basis"
  using assms empty_family_basis[OF assms(1)]
  by (simp add: assembled_data_def)

lemma empty_family_assembly:
  assumes "piece_graph P = {}"
  shows "K2 \<lparr>assembly_pieces = P, assembly_origin = {}\<rparr>"
  using assms empty_family_basis[OF assms]
  by (simp add: K2_iff_complete_compatible_origins piece_family_formed_def
    exact_map_def single_valued_def rel_dom_def rel_ran_def)

lemma empty_family_output:
  assumes "piece_graph P = {}" "K2 W" "assembly_pieces W = P"
  shows "assembly_origin W = {}"
    and "assembly_output W =
      \<lparr>object_structure = \<lparr>rra_carrier = {}, rra_incidence = {}\<rparr>,
       object_data = empty_basis\<rparr>"
proof -
  show origin: "assembly_origin W = {}"
    using assms empty_family_basis[OF assms(1)]
    by (auto simp: K2_iff_complete_compatible_origins exact_map_def rel_dom_def)
  show "assembly_output W =
      \<lparr>object_structure = \<lparr>rra_carrier = {}, rra_incidence = {}\<rparr>,
       object_data = empty_basis\<rparr>"
    using assms(1,3) empty_family_basis[OF assms(1)]
    by (simp add: assembly_output_def assembled_output_def origin expected_incidence_def
      copied_incidence_def piece_slots_def rel_dom_def rel_ran_def ternary_image_def)
qed

lemma K2_no_unexplained_output_atom:
  assumes "K2 W"
      and "a \<in> rra_carrier (object_structure (assembly_output W))"
  shows "\<exists>c \<in> copied_carrier (assembly_pieces W).
           (c,a) \<in> assembly_origin W"
proof -
  have mapping: "exact_map (copied_carrier (assembly_pieces W))
      (rra_carrier (object_structure (assembly_output W))) (assembly_origin W)"
    using assms(1) by (simp add: K2_def)
  show ?thesis by (rule exact_map_surjective[OF mapping assms(2)])
qed

lemma K2_origin_is_single_valued:
  assumes "K2 W"
  shows "single_valued (assembly_origin W)"
  using assms by (simp add: K2_def exact_map_def)

lemma K2_glued_iff_same_output:
  assumes "K2 W"
      and "c \<in> copied_carrier (assembly_pieces W)"
      and "d \<in> copied_carrier (assembly_pieces W)"
  shows "rel_value (assembly_origin W) c = rel_value (assembly_origin W) d \<longleftrightarrow>
         (\<exists>a. (c,a) \<in> assembly_origin W \<and>
              (d,a) \<in> assembly_origin W)"
proof
  assume eq: "rel_value (assembly_origin W) c =
              rel_value (assembly_origin W) d"
  have ca: "(c,rel_value (assembly_origin W) c) \<in> assembly_origin W"
    using exact_map_value assms by (auto simp: K2_def)
  have da: "(d,rel_value (assembly_origin W) d) \<in> assembly_origin W"
    using exact_map_value assms by (auto simp: K2_def)
  show "\<exists>a. (c,a) \<in> assembly_origin W \<and> (d,a) \<in> assembly_origin W"
    by (rule exI[of _ "rel_value (assembly_origin W) c"])
       (use ca da eq in simp)
next
  assume "\<exists>a. (c,a) \<in> assembly_origin W \<and> (d,a) \<in> assembly_origin W"
  then obtain a where ca: "(c,a) \<in> assembly_origin W"
                    and da: "(d,a) \<in> assembly_origin W" by blast
  from assms have sv: "single_valued (assembly_origin W)"
    by (simp add: K2_def exact_map_def)
  have "rel_value (assembly_origin W) c = a"
    by (rule rel_value_eq[OF sv ca])
  moreover have "rel_value (assembly_origin W) d = a"
    by (rule rel_value_eq[OF sv da])
  ultimately show "rel_value (assembly_origin W) c =
                   rel_value (assembly_origin W) d"
    by simp
qed

lemma K2_output_incidence_has_origin:
  assumes "K2 W"
      and "(r,p,x) \<in> rra_incidence (object_structure (assembly_output W))"
  shows "\<exists>cr cp cx.
           (cr,cp,cx) \<in> copied_incidence (assembly_pieces W) \<and>
           rel_value (assembly_origin W) cr = r \<and>
           rel_value (assembly_origin W) cp = p \<and>
           rel_value (assembly_origin W) cx = x"
  using assms
  by (auto simp: K2_def expected_incidence_def ternary_image_def; blast)

text \<open>
  K2 contains no semantic premise.  It verifies only exact reuse, identity
  gluing, incidence transport, and data transport.  Whether
  a program is permitted to select or glue the pieces is a later Factor fact.
\<close>

end
