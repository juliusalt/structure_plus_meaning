theory RRA_Core
  imports Bootstrap_Relations
begin

section \<open>The sole structural universe\<close>

record 'a rra_structure =
  rra_carrier :: "'a set"
  rra_incidence :: "('a \<times> 'a \<times> 'a) set"

lemma rra_identity:
  fixes S T :: "'a rra_structure"
  shows "S = T \<longleftrightarrow> rra_carrier S = rra_carrier T \<and> rra_incidence S = rra_incidence T"
  by (cases S; cases T) auto

definition rra_formed :: "'a rra_structure \<Rightarrow> bool" where
  "rra_formed S \<longleftrightarrow>
     finite (rra_carrier S) \<and>
     finite (rra_incidence S) \<and>
     (\<forall>r p x. (r,p,x) \<in> rra_incidence S \<longrightarrow>
        r \<in> rra_carrier S \<and> p \<in> rra_carrier S \<and> x \<in> rra_carrier S)"

definition relation_occurrences :: "'a rra_structure \<Rightarrow> 'a set" where
  "relation_occurrences S = {r. \<exists>p x. (r,p,x) \<in> rra_incidence S}"

definition participation_occurrences :: "'a rra_structure \<Rightarrow> 'a set" where
  "participation_occurrences S = {p. \<exists>r x. (r,p,x) \<in> rra_incidence S}"

definition reached_occurrences :: "'a rra_structure \<Rightarrow> 'a set" where
  "reached_occurrences S = {x. \<exists>r p. (r,p,x) \<in> rra_incidence S}"

text \<open>
  These three sets are projections of tuple positions.  They are not sorts and
  need not be disjoint.  An occurrence may occupy any combination of positions.
\<close>

lemma role_occurrences_in_carrier:
  assumes "rra_formed S"
  shows "relation_occurrences S \<subseteq> rra_carrier S"
    and "participation_occurrences S \<subseteq> rra_carrier S"
    and "reached_occurrences S \<subseteq> rra_carrier S"
  using assms
  by (auto simp: rra_formed_def relation_occurrences_def
      participation_occurrences_def reached_occurrences_def)

definition touching_incidence ::
  "'a rra_structure \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a \<times> 'a) set" where
  "touching_incidence S A =
     {(r,p,x) \<in> rra_incidence S. r \<in> A \<or> p \<in> A \<or> x \<in> A}"

definition internal_incidence ::
  "'a rra_structure \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a \<times> 'a) set" where
  "internal_incidence S A =
     {(r,p,x) \<in> rra_incidence S. r \<in> A \<and> p \<in> A \<and> x \<in> A}"

definition crossing_incidence ::
  "'a rra_structure \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a \<times> 'a) set" where
  "crossing_incidence S A = touching_incidence S A - internal_incidence S A"

definition restrict_structure :: "'a rra_structure \<Rightarrow> 'a set \<Rightarrow> 'a rra_structure" where
  "restrict_structure S A =
     \<lparr> rra_carrier = rra_carrier S \<inter> A,
       rra_incidence = internal_incidence S (rra_carrier S \<inter> A) \<rparr>"

lemma restrict_structure_formed:
  assumes "rra_formed S"
  shows "rra_formed (restrict_structure S A)"
proof -
  have sub: "internal_incidence S (rra_carrier S \<inter> A) \<subseteq> rra_incidence S"
    by (auto simp: internal_incidence_def)
  have fin: "finite (internal_incidence S (rra_carrier S \<inter> A))"
    using finite_subset[OF sub] assms by (auto simp: rra_formed_def)
  show ?thesis
    using assms fin
    by (auto simp: rra_formed_def restrict_structure_def internal_incidence_def)
qed

section \<open>Renaming\<close>

definition push_structure :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a rra_structure \<Rightarrow> 'b rra_structure" where
  "push_structure f S =
     \<lparr> rra_carrier = f ` rra_carrier S,
       rra_incidence =
         (\<lambda>(r,p,x). (f r,f p,f x)) ` rra_incidence S \<rparr>"

lemma push_structure_carrier [simp]:
  "rra_carrier (push_structure f S) = f ` rra_carrier S"
  by (simp add: push_structure_def)

lemma push_structure_incidence_member:
  assumes edge: "(r,p,x)\<in>rra_incidence S"
  shows "(f r,f p,f x)\<in>rra_incidence (push_structure f S)"
proof -
  let ?map="\<lambda>(r,p,x). (f r,f p,f x)"
  have "?map (r,p,x)\<in>?map ` rra_incidence S" by (rule imageI[OF edge])
  then show ?thesis by (simp add: push_structure_def)
qed

lemma participation_occurrences_push:
  "participation_occurrences (push_structure f S) = f ` participation_occurrences S"
proof (rule equalityI)
  show "participation_occurrences (push_structure f S) \<subseteq> f ` participation_occurrences S"
    by (auto simp: participation_occurrences_def push_structure_def)
  show "f ` participation_occurrences S \<subseteq> participation_occurrences (push_structure f S)"
  proof
    fix a assume "a\<in>f ` participation_occurrences S"
    then obtain r p x where edge: "(r,p,x)\<in>rra_incidence S" and position: "a=f p"
      by (auto simp: participation_occurrences_def)
    have "(f r,f p,f x)\<in>rra_incidence (push_structure f S)"
      by (rule push_structure_incidence_member[OF edge])
    then show "a\<in>participation_occurrences (push_structure f S)"
      using position by (auto simp: participation_occurrences_def)
  qed
qed

lemma reached_occurrences_push:
  "reached_occurrences (push_structure f S) = f ` reached_occurrences S"
proof (rule equalityI)
  show "reached_occurrences (push_structure f S) \<subseteq> f ` reached_occurrences S"
    by (auto simp: reached_occurrences_def push_structure_def)
  show "f ` reached_occurrences S \<subseteq> reached_occurrences (push_structure f S)"
  proof
    fix a assume "a\<in>f ` reached_occurrences S"
    then obtain r p x where edge: "(r,p,x)\<in>rra_incidence S" and position: "a=f x"
      by (auto simp: reached_occurrences_def)
    have "(f r,f p,f x)\<in>rra_incidence (push_structure f S)"
      by (rule push_structure_incidence_member[OF edge])
    then show "a\<in>reached_occurrences (push_structure f S)"
      using position by (auto simp: reached_occurrences_def)
  qed
qed

lemma push_structure_identity [simp]:
  "push_structure id S = S"
  by (cases S) (auto simp: push_structure_def)

lemma push_structure_composes:
  "push_structure g (push_structure f S) = push_structure (g \<circ> f) S"
  by (auto simp: push_structure_def image_image intro: rev_image_eqI)

lemma push_structure_cong:
  assumes formed: "rra_formed S" and agree: "\<And>a. a \<in> rra_carrier S \<Longrightarrow> f a = g a"
  shows "push_structure f S = push_structure g S"
proof -
  have carrier: "f ` rra_carrier S = g ` rra_carrier S" using agree by auto
  have incidence: "(\<lambda>(r,p,x). (f r,f p,f x)) ` rra_incidence S =
    (\<lambda>(r,p,x). (g r,g p,g x)) ` rra_incidence S"
    by (rule image_cong[OF refl])
       (use formed agree in \<open>auto simp: rra_formed_def\<close>)
  show ?thesis using carrier incidence by (simp add: push_structure_def)
qed

lemma push_structure_left_inverse:
  assumes formed: "rra_formed S"
    and inverse: "\<And>a. a \<in> rra_carrier S \<Longrightarrow> g (f a) = a"
  shows "push_structure g (push_structure f S) = S"
proof -
  have "push_structure (g \<circ> f) S = push_structure id S"
    by (rule push_structure_cong[OF formed]) (use inverse in auto)
  then show ?thesis by (simp add: push_structure_composes)
qed

definition rra_isomorphism ::
  "('a \<Rightarrow> 'b) \<Rightarrow> 'a rra_structure \<Rightarrow> 'b rra_structure \<Rightarrow> bool" where
  "rra_isomorphism f S T \<longleftrightarrow>
     rra_formed S \<and> bij_betw f (rra_carrier S) (rra_carrier T) \<and>
     push_structure f S = T"

definition rra_isomorphic :: "'a rra_structure \<Rightarrow> 'b rra_structure \<Rightarrow> bool" where
  "rra_isomorphic S T \<longleftrightarrow> (\<exists>f. rra_isomorphism f S T)"

lemma push_structure_formed:
  assumes "rra_formed S"
  shows "rra_formed (push_structure f S)"
  using assms by (auto simp: rra_formed_def push_structure_def)

lemma push_structure_iso:
  assumes "rra_formed S" "inj_on f (rra_carrier S)"
  shows "rra_isomorphism f S (push_structure f S)"
  using assms
  by (auto simp: rra_isomorphism_def push_structure_def bij_betw_def inj_on_def)

lemma rra_isomorphic_refl:
  assumes "rra_formed S"
  shows "rra_isomorphic S S"
proof -
  have "rra_isomorphism id S S"
    using assms by (simp add: rra_isomorphism_def bij_betw_def)
  then show ?thesis unfolding rra_isomorphic_def by blast
qed

lemma rra_isomorphism_target_formed:
  assumes "rra_isomorphism f S T"
  shows "rra_formed T"
  using assms push_structure_formed[of S f] by (auto simp: rra_isomorphism_def)

lemma rra_isomorphism_composes:
  assumes first: "rra_isomorphism f S T" and second: "rra_isomorphism g T V"
  shows "rra_isomorphism (g \<circ> f) S V"
proof -
  have fb: "bij_betw f (rra_carrier S) (rra_carrier T)"
    and gb: "bij_betw g (rra_carrier T) (rra_carrier V)"
    using first second by (auto simp: rra_isomorphism_def)
  have bij: "bij_betw (g \<circ> f) (rra_carrier S) (rra_carrier V)"
    by (rule bij_betw_trans[OF fb gb])
  show ?thesis
    using first second bij
    by (simp add: rra_isomorphism_def push_structure_composes[symmetric])
qed

lemma rra_isomorphism_inverse:
  assumes iso: "rra_isomorphism f S T"
  shows "rra_isomorphism (inv_into (rra_carrier S) f) T S"
proof -
  let ?g = "inv_into (rra_carrier S) f"
  have sf: "rra_formed S" and bij: "bij_betw f (rra_carrier S) (rra_carrier T)"
    and target: "T = push_structure f S"
    using iso by (auto simp: rra_isomorphism_def)
  have tf: "rra_formed T" by (rule rra_isomorphism_target_formed[OF iso])
  have gb: "bij_betw ?g (rra_carrier T) (rra_carrier S)"
    by (rule bij_betw_inv_into[OF bij])
  have inverse: "\<And>a. a \<in> rra_carrier S \<Longrightarrow> ?g (f a) = a"
    by (rule bij_betw_inv_into_left[OF bij])
  have recovered: "push_structure ?g T = S"
    unfolding target by (rule push_structure_left_inverse[where f=f and g="?g", OF sf inverse])
  show ?thesis using tf gb recovered by (simp add: rra_isomorphism_def)
qed

lemma rra_isomorphic_symmetric:
  assumes "rra_isomorphic S T"
  shows "rra_isomorphic T S"
  using assms rra_isomorphism_inverse unfolding rra_isomorphic_def by blast

lemma rra_isomorphic_transitive:
  assumes "rra_isomorphic S T" "rra_isomorphic T V"
  shows "rra_isomorphic S V"
  using assms rra_isomorphism_composes unfolding rra_isomorphic_def by blast

section \<open>Externally bounded views\<close>

record ('k,'a) bounded_view =
  bounded_structure :: "'a rra_structure"
  boundary_graph :: "('k \<times> 'a) set"

definition boundary_formed :: "('k,'a) bounded_view \<Rightarrow> bool" where
  "boundary_formed V \<longleftrightarrow>
     rra_formed (bounded_structure V) \<and>
     finite (boundary_graph V) \<and>
     single_valued (boundary_graph V) \<and>
     rel_ran (boundary_graph V) \<subseteq> rra_carrier (bounded_structure V)"

definition bounded_isomorphism ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('k,'a) bounded_view \<Rightarrow> ('k,'b) bounded_view \<Rightarrow> bool" where
  "bounded_isomorphism f V W \<longleftrightarrow>
     rra_isomorphism f (bounded_structure V) (bounded_structure W) \<and>
     rel_dom (boundary_graph V) = rel_dom (boundary_graph W) \<and>
     boundary_graph W = {(k,f a) |k a. (k,a) \<in> boundary_graph V}"

lemma bounded_isomorphism_preserves_keys:
  assumes "bounded_isomorphism f V W"
  shows "rel_dom (boundary_graph V) = rel_dom (boundary_graph W)"
  using assms by (simp add: bounded_isomorphism_def)

lemma boundary_does_not_change_structure:
  assumes "bounded_structure V = bounded_structure W"
  shows "rra_incidence (bounded_structure V) = rra_incidence (bounded_structure W)"
  using assms by simp

text \<open>
  A boundary key belongs to the supplied view.  No predicate in this theory
  turns a key into a property, kind, or stored name of the reached occurrence.
\<close>

section \<open>Rooted connectivity\<close>

definition incidence_step ::
  "'a rra_structure \<Rightarrow> ('a \<times> 'a) set" where
  "incidence_step S =
     {(a,b). \<exists>r p x.
        (r,p,x) \<in> rra_incidence S \<and>
        a \<in> {r,p,x} \<and> b \<in> {r,p,x} \<and> a \<noteq> b}"

definition rooted_connected :: "'a rra_structure \<Rightarrow> 'a \<Rightarrow> bool" where
  "rooted_connected S root \<longleftrightarrow>
     root \<in> rra_carrier S \<and>
     rra_carrier S = {root} \<union> {x. (root,x) \<in> (incidence_step S)\<^sup>+}"

end
