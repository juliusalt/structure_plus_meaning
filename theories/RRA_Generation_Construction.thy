theory RRA_Generation_Construction
  imports RRA_Generation_Record_Construction
begin

section \<open>Installing a generation record with references to existing uses\<close>

theorem generation_record_extension:
  fixes E :: "local_address option artifact_environment" and n :: nat
  assumes ef: "environment_formed E"
    and lf: "target_formed l" and pf: "target_formed p" and cf: "target_formed c"
    and distinct: "inj_on g {..<n}"
    and predecessors: "\<forall>i<n. generation_at E (v i) (a i) (g i)"
  shows "\<exists>H u. environment_formed H \<and> environment_included E H \<and>
    generation_at H u [] (Generation l (Abs_fset (g ` {..<n})) p c)"
proof -
  have targets: "\<forall>i\<in>{..<n}. \<exists>R. artifact_at E (v i) R \<and> anchor_formed (R,a i)"
  proof (intro ballI)
    fix i assume index: "i\<in>{..<n}"
    have original: "generation_at E (v i) (a i) (g i)" using predecessors index by simp
    show "\<exists>R. artifact_at E (v i) R \<and> anchor_formed (R,a i)"
      by (rule generation_at_has_anchor[OF original])
  qed
  obtain T where chosen: "\<forall>i\<in>{..<n}. artifact_at E (v i) (T i) \<and> anchor_formed (T i,a i)"
    using bchoice[OF targets] by blast
  let ?as="map (\<lambda>i. (T i,a i)) [0..<n]"
  interpret construction: generation_record_construction E l p c ?as v
    by (rule generation_record_construction.intro[OF ef lf pf cf])
      (use chosen in auto)
  have injective: "inj_on g {..<length ?as}" using distinct by simp
  have original: "\<forall>i<length ?as. generation_at E (v i) (snd (?as!i)) (g i)"
    using predecessors by simp
  have gen: "generation_at construction.installed construction.record_use []
    (Generation l (Abs_fset (g ` {..<n})) p c)"
    using construction.recovers[OF injective original] by simp
  show ?thesis using construction.properties(1,2) gen by blast
qed

section \<open>Every formed finite core has an actual presentation\<close>

theorem generation_presentation_total:
  assumes "generation_formed G"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>u. generation_at E u [] G"
  using assms
proof (induction G rule: generation_structure.induct)
  case (Generation l P p c)
  have parts: "target_formed l" "target_formed p" "target_formed c"
    "\<forall>H\<in>fset P. generation_formed H"
    using generation_formed_fields[OF Generation.prems] by simp_all
  have each: "\<forall>H\<in>fset P. \<exists>E :: local_address option artifact_environment.
    \<exists>u r. generation_at E u r H" using Generation.IH parts(4) by blast
  obtain E :: "local_address option artifact_environment" where ef: "environment_formed E"
    and all: "\<forall>H\<in>fset P. \<exists>u r. generation_at E u r H"
    using finite_generation_presentations_together[OF finite_fset each] by blast
  obtain Gs where listed: "set Gs=fset P" and different: "distinct Gs"
    using finite_distinct_list[OF finite_fset[of P]] by blast
  let ?n = "length Gs"
  let ?g = "\<lambda>i. Gs!i"
  have sites: "\<forall>i\<in>{..<?n}. \<exists>s. generation_at E (fst s) (snd s) (?g i)"
  proof (intro ballI)
    fix i assume index: "i \<in> {..<?n}"
    have bound: "i<length Gs" using index by simp
    have member: "Gs!i \<in> fset P" using nth_mem[OF bound] listed by simp
    obtain u r where gen: "generation_at E u r (Gs!i)" using all member by blast
    show "\<exists>s. generation_at E (fst s) (snd s) (?g i)"
      by (rule exI[of _ "(u,r)"]) (use gen in simp)
  qed
  obtain s where chosen: "\<forall>i\<in>{..<?n}. generation_at E (fst (s i)) (snd (s i)) (?g i)"
    using bchoice[OF sites] by blast
  have distinct: "inj_on ?g {..<?n}" by (rule inj_on_nth[OF different]) simp
  have reads: "\<forall>i<?n. generation_at E (fst (s i)) (snd (s i)) (?g i)" using chosen by simp
  obtain H :: "local_address option artifact_environment" and u
    where gen: "generation_at H u [] (Generation l (Abs_fset (?g ` {..<?n})) p c)"
    using generation_record_extension[OF ef parts(1-3) distinct reads] by blast
  have members: "?g ` {..<?n}=fset P" using listed by (auto simp: set_conv_nth)
  have same: "Abs_fset (?g ` {..<?n})=P"
    by (rule fset_inject[THEN iffD1]) (simp add: members Abs_fset_inverse)
  show ?case using gen same by blast
qed

corollary closed_generation_presentation_total:
  assumes formed: "generation_formed G"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>u.
    generation_at E u [] G \<and> generation_environment_closed E {(u,[])}"
proof -
  obtain E :: "local_address option artifact_environment" and u
    where gen: "generation_at E u [] G" using generation_presentation_total[OF formed] by blast
  have ef: "environment_formed E" by (rule generation_at_environment_formed[OF gen])
  have roots: "\<forall>v r. (v,r) \<in> {(u,[])} \<longrightarrow> (\<exists>H. generation_at E v r H)"
    using gen by auto
  let ?F = "request_environment E (generation_requests E {(u,[])})"
  have closed: "generation_environment_closed ?F {(u,[])}"
    by (rule generation_closed_restriction[OF ef roots])
  have site: "(u,[]) \<in> generation_read_sites E {(u,[])}"
    using generation_read_sites_roots[of "{(u,[])}" E] by blast
  have retained: "generation_at ?F u [] G"
    by (rule generation_at_request_restriction[OF ef roots gen site])
  show ?thesis using closed retained by blast
qed

text \<open>
  The extension retains every old artifact use and binding. Each predecessor
  reference targets its supplied use and address, and the recovered predecessor
  set is exactly the finite injective family. The three other fields receive
  explicit literal bindings. No cause validity or authority premise is used.

  Totality follows by constructing each finite predecessor family, placing its
  presentations at disjoint uses, and adding the parent record. Empty
  predecessor sets use the same construction. Generation formation and actual
  presentation are thereby connected without making formation validate a cause.
\<close>

end
