theory RRA_Prescribed_Addresses
  imports RRA_Exact
begin

section \<open>Extending finite prescribed injections\<close>

lemma finite_injection_extends:
  fixes p :: "'a \<Rightarrow> 'a"
  assumes finite: "finite A" and prescribed: "inj_on p A"
  shows "\<exists>g. inj g \<and> (\<forall>a\<in>A. g a=p a)"
  using finite prescribed
proof (induction A arbitrary: p rule: finite_induct)
  case empty
  show ?case by (rule exI[of _ id]) simp
next
  case (insert a A)
  have pinj: "inj_on p A" by (rule inj_on_subset[OF insert.prems]) blast
  obtain g where old: "inj g" "\<forall>x\<in>A. g x=p x" using insert.IH[OF pinj] by blast
  let ?t="\<lambda>y. if y=g a then p a else if y=p a then g a else y"
  have tinj: "inj ?t" by (rule injI) (auto split: if_splits)
  have ginj: "inj (?t \<circ> g)" by (rule inj_compose[OF tinj old(1)])
  have fixed: "?t (g x)=p x" if member: "x\<in>A" for x
  proof -
    have different: "x\<noteq>a" using member insert.hyps(2) by blast
    have ga: "g x\<noteq>g a" using old(1) different by (auto simp: inj_eq)
    have pa: "p x\<noteq>p a" using insert.prems member different by (auto simp: inj_on_def)
    show ?thesis using ga pa old(2) member by simp
  qed
  show ?case by (rule exI[of _ "?t \<circ> g"], rule conjI[OF ginj]) (use fixed in auto)
qed

lemma long_address_outside:
  assumes finite: "finite W" and long: "Max (length ` W)<length a"
  shows "a\<notin>W"
proof
  assume member: "a\<in>W"
  have "length a\<le>Max (length ` W)"
    by (rule Max_ge) (use finite member in auto)
  then show False using long by simp
qed

theorem finite_addressing_avoiding:
  assumes domain: "finite U" and forbidden: "finite W"
  shows "\<exists>f. finite_addressing U f \<and> f ` U \<inter> W={}"
proof -
  obtain g where old: "finite_addressing U g"
    using finite_addressing_exists[OF domain] by blast
  let ?f="\<lambda>a. fresh_address W @ g a"
  have injective: "inj_on ?f U" using old by (auto simp: finite_addressing_def inj_on_def)
  have formed: "\<forall>a\<in>U. octets_formed (?f a)"
    using old fresh_address_formed[of W] by (auto simp: finite_addressing_def octets_formed_def)
  have outside: "?f a\<notin>W" for a
    by (rule long_address_outside[OF forbidden]) (simp add: fresh_address_def)
  show ?thesis by (rule exI[of _ ?f])
    (use injective formed outside in \<open>auto simp: finite_addressing_def\<close>)
qed

theorem prescribed_addressing_extension:
  fixes U :: "local_address set"
  assumes domain: "finite U" and boundary: "A\<subseteq>U"
    and prescribed: "finite_addressing A p" and forbidden: "finite W"
  shows "\<exists>g. inj g \<and> finite_addressing U g \<and>
    (\<forall>a\<in>A. g a=p a) \<and> g ` (U-A) \<inter> W={}"
proof -
  have afinite: "finite A" by (rule finite_subset[OF boundary domain])
  have finite_new: "finite (U-A)" using domain by simp
  have finite_avoid: "finite (p ` A \<union> W)" using afinite forbidden by simp
  obtain j where fresh: "finite_addressing (U-A) j" "j ` (U-A) \<inter> (p ` A \<union> W)={}"
    using finite_addressing_avoiding[OF finite_new finite_avoid] by blast
  let ?q="\<lambda>a. if a\<in>A then p a else j a"
  have qinj: "inj_on ?q U"
    using prescribed fresh by (auto simp: finite_addressing_def inj_on_def split: if_splits; blast)
  have qformed: "\<forall>a\<in>U. octets_formed (?q a)"
    using prescribed fresh(1) by (auto simp: finite_addressing_def)
  obtain g where extension: "inj g" "\<forall>a\<in>U. g a=?q a"
    using finite_injection_extends[OF domain qinj] by blast
  have local_injective: "inj_on g U" by (rule inj_on_subset[OF extension(1) subset_UNIV])
  have outputs: "\<forall>a\<in>U. octets_formed (g a)"
  proof (intro ballI)
    fix a assume member: "a\<in>U"
    have agreement: "g a=?q a" using extension(2) member by blast
    show "octets_formed (g a)" using qformed member by (simp only: agreement; blast)
  qed
  have addressing: "finite_addressing U g"
    using local_injective outputs by (simp only: finite_addressing_def)
  have agreement: "\<forall>a\<in>A. g a=p a" using extension(2) boundary by auto
  have outside: "g ` (U-A) \<inter> W={}" using extension(2) fresh(2) by auto
  show ?thesis by (rule exI[of _ g]) (use extension(1) addressing agreement outside in blast)
qed

text \<open>
  A finite injective prescription fixes the coordinates that a later
  construction must retain. The remaining finite positions receive formed
  addresses outside any supplied finite set. The complete map is injective,
  as required by the existing native copy theorems. Its action outside the
  artifact carrier is only an extension witness; readers never inspect it.
\<close>

end
