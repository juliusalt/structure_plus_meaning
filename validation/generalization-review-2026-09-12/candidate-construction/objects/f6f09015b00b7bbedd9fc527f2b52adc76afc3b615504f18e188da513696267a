theory Factor_Assembly_Enumerations
  imports Factor_Assembly_Presentations RRA_Data_Enumerations
begin

section \<open>Every piece occurrence carries one complete artifact enumeration\<close>

definition piece_family_enumeration ::
  "'s exact_piece_family \<Rightarrow> 's list \<Rightarrow> ('s\<Rightarrow>local_address list) \<Rightarrow>
    ('s\<Rightarrow>(local_address\<times>local_address\<times>local_address) list) \<Rightarrow>
    ('s\<Rightarrow>(local_address\<times>octets) list) \<Rightarrow>
    ('s\<Rightarrow>(local_address\<times>octets) list) \<Rightarrow> bool" where
  "piece_family_enumeration P ss A E B F \<longleftrightarrow>
    piece_family_formed P \<and> distinct ss \<and> set ss=piece_slots P \<and>
    (\<forall>s\<in>set ss. artifact_enumeration (piece_at P s) (A s) (E s) (B s) (F s))"

theorem piece_family_enumeration_at_slots:
  assumes pieces: "piece_family_formed P" and slots: "distinct ss" "set ss=piece_slots P"
  shows "\<exists>A E B F. piece_family_enumeration P ss A E B F"
proof -
  have each: "\<exists>a e b f. artifact_enumeration (piece_at P s) a e b f"
    if "s\<in>set ss" for s
    using artifact_enumeration_exists[OF piece_at_formed[OF pieces]] that slots(2) by blast
  have choices: "\<forall>s. \<exists>z. s\<in>set ss \<longrightarrow>
      artifact_enumeration (piece_at P s) (fst z) (fst (snd z)) (fst (snd (snd z))) (snd (snd (snd z)))"
    using each by auto
  obtain Z where chosen: "\<forall>s. s\<in>set ss \<longrightarrow>
      artifact_enumeration (piece_at P s) (fst (Z s)) (fst (snd (Z s)))
        (fst (snd (snd (Z s)))) (snd (snd (snd (Z s))))"
    using choice[OF choices] by blast
  show ?thesis
    by (intro exI[of _ "\<lambda>s. fst (Z s)"] exI[of _ "\<lambda>s. fst (snd (Z s))"]
      exI[of _ "\<lambda>s. fst (snd (snd (Z s)))"] exI[of _ "\<lambda>s. snd (snd (snd (Z s)))"])
      (use pieces slots chosen in \<open>simp add: piece_family_enumeration_def\<close>)
qed

theorem piece_family_enumeration_exists:
  assumes "piece_family_formed P"
  shows "\<exists>ss A E B F. piece_family_enumeration P ss A E B F"
  using finite_distinct_list[OF piece_slots_finite[OF assms]] piece_family_enumeration_at_slots[OF assms]
  by blast

lemma piece_family_enumeration_order:
  assumes "distinct ss" "distinct ts" "set ss=set ts"
  shows "piece_family_enumeration P ss A E B F \<longleftrightarrow> piece_family_enumeration P ts A E B F"
  using assms by (simp add: piece_family_enumeration_def)

section \<open>Occurrence keys keep the complete copied fields separate\<close>

abbreviation tagged_atom_list :: "'s list \<Rightarrow> ('s\<Rightarrow>'a list) \<Rightarrow> ('s\<times>'a) list" where
  "tagged_atom_list ss A \<equiv> concat (map (\<lambda>s. map (Pair s) (A s)) ss)"

abbreviation tagged_incidence_list ::
  "'s list \<Rightarrow> ('s\<Rightarrow>('a\<times>'a\<times>'a) list) \<Rightarrow>
    (('s\<times>'a)\<times>('s\<times>'a)\<times>('s\<times>'a)) list" where
  "tagged_incidence_list ss E \<equiv>
    concat (map (\<lambda>s. map (\<lambda>(r,p,x). ((s,r),(s,p),(s,x))) (E s)) ss)"

abbreviation tagged_attachment_list ::
  "'s list \<Rightarrow> ('s\<Rightarrow>('a\<times>'v) list) \<Rightarrow> (('s\<times>'a)\<times>'v) list" where
  "tagged_attachment_list ss B \<equiv>
    concat (map (\<lambda>s. map (\<lambda>(a,v). ((s,a),v)) (B s)) ss)"

lemma tagged_atom_list_distinct:
  assumes "distinct ss" "\<And>s. s\<in>set ss \<Longrightarrow> distinct (A s)"
  shows "distinct (tagged_atom_list ss A)"
  using assms by (induction ss) (auto simp: distinct_map inj_on_def)

lemma tagged_attachment_count:
  "count_list (map (\<lambda>(a,v). ((s,a),v)) B) ((t,a),v)=
    (if s=t then count_list B (a,v) else 0)"
  by (induction B) (auto split: prod.splits)

lemma tagged_attachment_list_count:
  assumes "distinct ss"
  shows "count_list (tagged_attachment_list ss B) ((s,a),v)=
    (if s\<in>set ss then count_list (B s) (a,v) else 0)"
  using assms by (induction ss) (auto simp: tagged_attachment_count)

locale enumerated_piece_family =
  fixes P :: "'s exact_piece_family" and ss :: "'s list"
    and A :: "'s\<Rightarrow>local_address list"
    and E :: "'s\<Rightarrow>(local_address\<times>local_address\<times>local_address) list"
    and B F :: "'s\<Rightarrow>(local_address\<times>octets) list"
  assumes enumeration: "piece_family_enumeration P ss A E B F"
begin

lemma pieces: "piece_family_formed P"
  using enumeration by (simp add: piece_family_enumeration_def)

lemma slots: "distinct ss" "set ss=piece_slots P"
  using enumeration by (auto simp: piece_family_enumeration_def)

lemma component:
  assumes "s\<in>set ss"
  shows "artifact_enumeration (piece_at P s) (A s) (E s) (B s) (F s)"
  using enumeration assms by (simp add: piece_family_enumeration_def)

lemma component_material:
  assumes "s\<in>set ss"
  shows "set (A s)=rra_carrier (object_structure (piece_at P s))"
    "set (E s)=rra_incidence (object_structure (piece_at P s))"
    "count_list (B s)=bag_count (object_data (piece_at P s))"
    "set (F s)=functional_bindings (object_data (piece_at P s))"
  using artifact_enumeration_material[OF component[OF assms]] by auto

theorem copied_atoms:
  "set (tagged_atom_list ss A)=copied_carrier P"
  using component_material(1) by (auto simp: copied_carrier_def slots(2))

theorem copied_atoms_distinct:
  "distinct (tagged_atom_list ss A)"
  by (rule tagged_atom_list_distinct[OF slots(1)])
    (use artifact_enumeration_no_repeated_set_entry[OF component] in auto)

theorem copied_edges:
  "set (tagged_incidence_list ss E)=copied_incidence P"
proof -
  let ?tag="\<lambda>s. \<lambda>(r,p,x). ((s,r),(s,p),(s,x))"
  have lists: "set (tagged_incidence_list ss E)=(\<Union>s\<in>set ss. ?tag s ` set (E s))"
    by auto
  have components: "(\<Union>s\<in>set ss. ?tag s ` set (E s))=
      (\<Union>s\<in>piece_slots P. ?tag s ` rra_incidence (object_structure (piece_at P s)))"
  proof (rule SUP_cong[OF slots(2)])
    fix s assume member: "s\<in>piece_slots P"
    have inside: "s\<in>set ss" using member slots(2) by simp
    show "?tag s ` set (E s)=?tag s ` rra_incidence (object_structure (piece_at P s))"
      by (simp only: component_material(2)[OF inside])
  qed
  show ?thesis by (simp only: lists components copied_incidence_union)
qed

theorem copied_counts:
  "count_list (tagged_attachment_list ss B)=bag_count (copied_basis P)"
proof (rule ext)
  fix z :: "('s\<times>local_address)\<times>octets"
  obtain s a v where row: "z=((s,a),v)" by (cases z) auto
  show "count_list (tagged_attachment_list ss B) z=bag_count (copied_basis P) z"
    using component_material(3)[of s]
    by (simp add: row tagged_attachment_list_count[OF slots(1)] copied_basis_def slots(2))
qed

theorem copied_bindings:
  "set (tagged_attachment_list ss F)=functional_bindings (copied_basis P)"
  using component_material(4)
  by (auto simp: copied_basis_def slots(2) image_iff; blast)

section \<open>Gluing maps every copied occurrence before comparing fields\<close>

theorem pushed_basis:
  "push_basis (copied_carrier P) f (copied_basis P)=\<lparr>
    bag_count=count_list (pushed_attachment_list f (tagged_attachment_list ss B)),
    functional_bindings=set (pushed_attachment_list f (tagged_attachment_list ss F))\<rparr>"
  by (rule push_basis_enumeration[OF copied_carrier_finite[OF pieces]
    copied_basis_formed[OF pieces] copied_counts copied_bindings])

theorem pushed_edges:
  "set (map (\<lambda>(r,p,x). (rel_value q r,rel_value q p,rel_value q x))
    (tagged_incidence_list ss E))=expected_incidence P q"
  by (simp only: set_map copied_edges) (force simp: expected_incidence_def ternary_image_def image_iff)

theorem compatibility:
  "single_valued (set (pushed_attachment_list f (tagged_attachment_list ss F))) \<longleftrightarrow>
    basis_compatible f (copied_basis P)"
  by (rule enumerated_functional_compatibility[OF copied_bindings])

theorem assembly_relation_at_enumeration:
  assumes origin: "finite q" "single_valued q"
    and target: "artifact_enumeration R A' E' B' F'"
  shows "assembly_relation P q R \<longleftrightarrow>
    rel_dom q=set (tagged_atom_list ss A) \<and> rel_ran q=set A' \<and>
    set E'=set (map (\<lambda>(r,p,x). (rel_value q r,rel_value q p,rel_value q x))
      (tagged_incidence_list ss E)) \<and>
    count_list B'=count_list (pushed_attachment_list (rel_value q) (tagged_attachment_list ss B)) \<and>
    set F'=set (pushed_attachment_list (rel_value q) (tagged_attachment_list ss F))"
proof -
  have result: "exact_formed R" and atoms: "set A'=rra_carrier (object_structure R)"
    and edges: "set E'=rra_incidence (object_structure R)"
    and counts: "count_list B'=bag_count (object_data R)"
    and bindings: "set F'=functional_bindings (object_data R)"
    using artifact_enumeration_material[OF target] by auto
  have mapping: "exact_map (copied_carrier P) (rra_carrier (object_structure R)) q \<longleftrightarrow>
      rel_dom q=set (tagged_atom_list ss A) \<and> rel_ran q=set A'"
    using origin by (simp add: exact_map_def atoms[symmetric] copied_atoms[symmetric])
  have data: "assembled_data P q (object_data R) \<longleftrightarrow>
      count_list B'=count_list (pushed_attachment_list (rel_value q) (tagged_attachment_list ss B)) \<and>
      set F'=set (pushed_attachment_list (rel_value q) (tagged_attachment_list ss F))"
    by (simp add: assembled_data_def pushed_basis basis_identity counts bindings)
  show ?thesis by (simp only: assembly_relation_def pieces result mapping data
    pushed_edges edges simp_thms conj_assoc)
qed

theorem assembly_output_enumeration:
  assumes assembled: "assembly_relation P q R"
  shows "artifact_enumeration R
    (remdups (map (rel_value q) (tagged_atom_list ss A)))
    (remdups (map (\<lambda>(r,p,x). (rel_value q r,rel_value q p,rel_value q x))
      (tagged_incidence_list ss E)))
    (pushed_attachment_list (rel_value q) (tagged_attachment_list ss B))
    (remdups (pushed_attachment_list (rel_value q) (tagged_attachment_list ss F)))"
proof -
  have formed: "exact_formed R"
    and mapping: "exact_map (copied_carrier P) (rra_carrier (object_structure R)) q"
    using assembled by (auto simp: assembly_relation_def)
  have carrier: "rel_value q ` copied_carrier P=rel_ran q"
    using exact_map_value_image[OF mapping] mapping by (simp add: exact_map_def)
  have atoms: "set (remdups (map (rel_value q) (tagged_atom_list ss A)))=rel_ran q"
    by (simp only: set_remdups set_map copied_atoms carrier)
  have edges: "set (remdups (map (\<lambda>(r,p,x). (rel_value q r,rel_value q p,rel_value q x))
      (tagged_incidence_list ss E)))=expected_incidence P q"
    by (simp only: set_remdups pushed_edges)
  have recovered: "R=enumerated_artifact
      (remdups (map (rel_value q) (tagged_atom_list ss A)))
      (remdups (map (\<lambda>(r,p,x). (rel_value q r,rel_value q p,rel_value q x))
        (tagged_incidence_list ss E)))
      (pushed_attachment_list (rel_value q) (tagged_attachment_list ss B))
      (remdups (pushed_attachment_list (rel_value q) (tagged_attachment_list ss F)))"
    using assembly_relation_determines_output[OF assembled]
    by (simp only: assembled_output_def enumerated_artifact_def set_remdups
      atoms[simplified set_remdups] edges[simplified set_remdups] pushed_basis)
  show ?thesis using formed recovered by (simp add: artifact_enumeration_def)
qed

end

text \<open>
  Every formed piece family has these complete finite enumerations, in every
  supplied order of its occurrence keys. Equal artifacts at different keys
  contribute separately. Values of the indexing functions outside the listed
  slots do not enter any copied field.

  The finite assembly criterion checks the entire origin domain and range,
  the complete incidence image, every attachment count, and the complete
  functional image. Its target is any complete artifact enumeration. Shared
  destinations are allowed; functional conflicts remain excluded by the
  target's original formation condition.

  Removing duplicates from the three set fields gives one output witness.
  The counted list is never deduplicated. This construction chooses no order
  for an artifact and restricts no other complete presentation. It supplies
  the mathematical correspondence needed by ordinary finite gluing checks;
  it does not itself add an assembly clause or a permission judgment.
\<close>

end
