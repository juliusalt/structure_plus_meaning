theory RRA_Representation_Audit
  imports RRA_Exact
begin

section \<open>Reversibility does not determine primitive orientation\<close>

fun rotate_triple :: "'a \<times> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a" where
  "rotate_triple (r,p,x) = (p,x,r)"

lemma rotate_triple_cycle [simp]:
  "rotate_triple (rotate_triple (rotate_triple t)) = t"
  by (cases t) auto

lemma rotate_triple_injective:
  "inj rotate_triple"
proof (rule injI)
  fix x y
  assume "rotate_triple x = rotate_triple y"
  then have "rotate_triple (rotate_triple (rotate_triple x)) =
    rotate_triple (rotate_triple (rotate_triple y))" by simp
  then show "x = y" by simp
qed

definition rotate_structure :: "'a rra_structure \<Rightarrow> 'a rra_structure" where
  "rotate_structure S =
    \<lparr>rra_carrier = rra_carrier S,
     rra_incidence = rotate_triple ` rra_incidence S\<rparr>"

lemma rotate_structure_carrier [simp]:
  "rra_carrier (rotate_structure S) = rra_carrier S"
  by (simp add: rotate_structure_def)

lemma rotate_structure_cycle [simp]:
  "rotate_structure (rotate_structure (rotate_structure S)) = S"
  by (cases S) (simp add: rotate_structure_def image_image)

lemma rotate_structure_formed:
  assumes "rra_formed S"
  shows "rra_formed (rotate_structure S)"
  using assms by (auto simp: rra_formed_def rotate_structure_def)

lemma rotation_has_one_origin_per_incidence:
  "bij_betw rotate_triple (rra_incidence S) (rra_incidence (rotate_structure S))"
  using rotate_triple_injective
  by (auto simp: bij_betw_def rotate_structure_def inj_def inj_on_def)

definition rotate_object :: "('a,'v) structured_object \<Rightarrow> ('a,'v) structured_object" where
  "rotate_object obj =
    \<lparr>object_structure = rotate_structure (object_structure obj), object_data = object_data obj\<rparr>"

lemma rotate_object_cycle [simp]:
  "rotate_object (rotate_object (rotate_object obj)) = obj"
  by (simp add: rotate_object_def object_identity)

lemma rotate_object_formed:
  assumes "object_formed obj"
  shows "object_formed (rotate_object obj)"
proof -
  have sf: "rra_formed (object_structure obj)" using assms by (simp add: object_formed_def)
  show ?thesis using assms rotate_structure_formed[OF sf]
    by (simp add: object_formed_def rotate_object_def)
qed

lemma rotate_exact_formed:
  assumes "exact_formed R"
  shows "exact_formed (rotate_object R)"
  using assms rotate_object_formed[of R]
  by (auto simp: exact_formed_def rotate_object_def)

definition rotate_bounded ::
  "('k,'a,'v) bounded_object \<Rightarrow> ('k,'a,'v) bounded_object" where
  "rotate_bounded V =
    \<lparr>bounded_content = rotate_object (bounded_content V), object_boundary = object_boundary V\<rparr>"

lemma rotate_bounded_cycle [simp]:
  "rotate_bounded (rotate_bounded (rotate_bounded V)) = V"
  by (cases V) (simp add: rotate_bounded_def)

lemma rotate_bounded_formed:
  assumes "bounded_object_formed V"
  shows "bounded_object_formed (rotate_bounded V)"
  using assms rotate_object_formed[of "bounded_content V"]
  by (auto simp: bounded_object_formed_def rotate_bounded_def rotate_object_def)

lemma rotation_preserves_carrier_data_and_boundary:
  "rra_carrier (object_structure (bounded_content (rotate_bounded V))) =
    rra_carrier (object_structure (bounded_content V))"
  "object_data (bounded_content (rotate_bounded V)) = object_data (bounded_content V)"
  "object_boundary (rotate_bounded V) = object_boundary V"
  by (simp_all add: rotate_bounded_def rotate_object_def)

lemma recoverable_encodings_need_not_be_isomorphic:
  "\<exists>V :: (bool,local_address,octets) bounded_object.
    bounded_object_formed V \<and> exact_formed (bounded_content V) \<and>
    bounded_object_formed (rotate_bounded V) \<and> exact_formed (bounded_content (rotate_bounded V)) \<and>
    rotate_bounded (rotate_bounded (rotate_bounded V)) = V \<and>
    rra_carrier (object_structure (bounded_content (rotate_bounded V))) =
      rra_carrier (object_structure (bounded_content V)) \<and>
    object_data (bounded_content (rotate_bounded V)) = object_data (bounded_content V) \<and>
    object_boundary (rotate_bounded V) = object_boundary V \<and>
    \<not> bounded_objects_isomorphic V (rotate_bounded V)"
proof -
  let ?R = "\<lparr>object_structure =
    \<lparr>rra_carrier = {[],[0]}, rra_incidence = {([],[],[0])}\<rparr>,
    object_data = empty_basis\<rparr> :: exact_artifact"
  let ?V = "\<lparr>bounded_content = ?R, object_boundary = {(False,[]),(True,[0])}\<rparr>"
  have rf: "exact_formed ?R"
    by (simp add: exact_formed_def object_formed_def rra_formed_def octets_formed_def)
  have vf: "bounded_object_formed ?V"
    using rf
    by (auto simp: bounded_object_formed_def exact_formed_def single_valued_def rel_ran_def)
  have not_iso: "\<not> bounded_objects_isomorphic ?V (rotate_bounded ?V)"
  proof
    assume "bounded_objects_isomorphic ?V (rotate_bounded ?V)"
    then obtain f where iso: "bounded_object_isomorphism f ?V (rotate_bounded ?V)"
      by (auto simp: bounded_objects_isomorphic_def)
    have eq: "push_structure f (object_structure ?R) = rotate_structure (object_structure ?R)"
      using iso
      by (simp add: bounded_object_isomorphism_def object_isomorphism_def
        rra_isomorphism_def rotate_bounded_def rotate_object_def)
    have "rra_incidence (push_structure f (object_structure ?R)) =
      rra_incidence (rotate_structure (object_structure ?R))"
      using eq by simp
    then show False by (auto simp: push_structure_def rotate_structure_def)
  qed
  have rotated_exact: "exact_formed (bounded_content (rotate_bounded ?V))"
    using rotate_exact_formed[OF rf] by (simp add: rotate_bounded_def)
  show ?thesis
    by (rule exI[of _ ?V])
       (use vf rf rotate_bounded_formed[OF vf] rotated_exact not_iso
         rotation_preserves_carrier_data_and_boundary[of ?V] in simp)
qed

text \<open>
  Identity and coordinate rotation both admit total recovery on formed finite
  objects. Rotation changes no atom, attachment, or exposed boundary binding,
  and its incidence map is bijective. Nevertheless the exhibited outputs are
  not related by an atom isomorphism: equality of the first two positions in a
  tuple is preserved by atom renaming and changed by this encoding.

  Recovery and absence of additional material therefore do not by themselves
  justify a claim that arbitrary encoding grammars are isomorphic. A quotation
  discipline preserving the primitive coordinates is a stronger, stated
  condition. The bounded-copy theorems prove determination under that condition;
  this audit does not equate it with the weaker requirements.
\<close>

end
