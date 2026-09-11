theory Factor_Table_Copy
  imports Factor_Proof_Copy Factor_Native_Tables
begin

section \<open>Physical copies of complete row occurrences\<close>

definition copy_native_rows where
  "copy_native_rows f H = (\<lambda>(s,q,I,K). (f s,q,f ` I,f ` K)) ` H"

lemma copy_native_rowI:
  assumes "(s,q,I,K) \<in> H"
  shows "(f s,q,f ` I,f ` K) \<in> copy_native_rows f H"
  using imageI[OF assms, of "\<lambda>(s,q,I,K). (f s,q,f ` I,f ` K)"]
  by (simp add: copy_native_rows_def)

lemma copy_native_row_member:
  "(s,q,I,K) \<in> copy_native_rows f H \<longleftrightarrow>
    (\<exists>t J A. (t,q,J,A) \<in> H \<and> s=f t \<and> I=f ` J \<and> K=f ` A)"
proof
  assume "(s,q,I,K) \<in> copy_native_rows f H"
  then show "\<exists>t J A. (t,q,J,A) \<in> H \<and> s=f t \<and> I=f ` J \<and> K=f ` A"
    by (auto simp: copy_native_rows_def)
next
  assume "\<exists>t J A. (t,q,J,A) \<in> H \<and> s=f t \<and> I=f ` J \<and> K=f ` A"
  then obtain t J A where original: "(t,q,J,A) \<in> H" "s=f t" "I=f ` J" "K=f ` A" by blast
  have copied: "(f t,q,f ` J,f ` A) \<in> copy_native_rows f H" by (rule copy_native_rowI[OF original(1)])
  show "(s,q,I,K) \<in> copy_native_rows f H" using copied original(2-4) by simp
qed

lemma copy_native_row_domain:
  "rel_dom (copy_native_rows f H)=f ` rel_dom H"
  by (auto simp: copy_native_row_member rel_dom_def)

lemma copy_native_row_values:
  "native_row_values (copy_native_rows f H)=native_row_values H"
  by (auto simp: native_row_value_member copy_native_row_member)

lemma copy_native_row_interiors:
  "native_row_interiors (copy_native_rows f H)=f ` native_row_interiors H"
proof (rule set_eqI, rule iffI)
  fix a assume member: "a \<in> native_row_interiors (copy_native_rows f H)"
  obtain s q I K where row: "(s,q,I,K) \<in> copy_native_rows f H" and inside: "a \<in> I"
    using member by (auto simp: native_row_interior_member)
  obtain t J A where old: "(t,q,J,A) \<in> H" "I=f ` J" using row by (auto simp: copy_native_row_member)
  have "J \<subseteq> native_row_interiors H" by (rule native_row_interiors_contains[OF old(1)])
  then show "a \<in> f ` native_row_interiors H" using inside old(2) by blast
next
  fix a assume member: "a \<in> f ` native_row_interiors H"
  obtain b where old: "b \<in> native_row_interiors H" "a=f b" using member by blast
  obtain s q I K where row: "(s,q,I,K) \<in> H" and inside: "b \<in> I"
    using old(1) by (auto simp: native_row_interior_member)
  have copied: "(f s,q,f ` I,f ` K) \<in> copy_native_rows f H" by (rule copy_native_rowI[OF row])
  show "a \<in> native_row_interiors (copy_native_rows f H)"
    using native_row_interiors_contains[OF copied] inside old(2) by blast
qed

lemma copy_native_row_slots:
  "native_row_slots (copy_native_rows f H)=f ` native_row_slots H"
proof (rule set_eqI, rule iffI)
  fix a assume member: "a \<in> native_row_slots (copy_native_rows f H)"
  obtain s q I K where row: "(s,q,I,K) \<in> copy_native_rows f H" and inside: "a \<in> K"
    using member by (auto simp: native_row_slot_member)
  obtain t J A where old: "(t,q,J,A) \<in> H" "K=f ` A" using row by (auto simp: copy_native_row_member)
  have "A \<subseteq> native_row_slots H" by (rule native_row_slots_contains[OF old(1)])
  then show "a \<in> f ` native_row_slots H" using inside old(2) by blast
next
  fix a assume member: "a \<in> f ` native_row_slots H"
  obtain b where old: "b \<in> native_row_slots H" "a=f b" using member by blast
  obtain s q I K where row: "(s,q,I,K) \<in> H" and inside: "b \<in> K"
    using old(1) by (auto simp: native_row_slot_member)
  have copied: "(f s,q,f ` I,f ` K) \<in> copy_native_rows f H" by (rule copy_native_rowI[OF row])
  show "a \<in> native_row_slots (copy_native_rows f H)"
    using native_row_slots_contains[OF copied] inside old(2) by blast
qed

lemma copy_native_rows_functional:
  assumes sv: "single_valued H" and injective: "inj f"
  shows "single_valued (copy_native_rows f H)"
  using assms by (auto simp: single_valued_def copy_native_row_member inj_def; blast)

lemma copy_native_row_key:
  assumes sv: "single_valued H" and injective: "inj f" and key: "s \<in> rel_dom H"
  shows "native_row_keys (copy_native_rows f H) (f s)=native_row_keys H s"
proof -
  obtain q I K where row: "(s,q,I,K) \<in> H" using key by (auto simp: rel_dom_def)
  have copied: "(f s,q,f ` I,f ` K) \<in> copy_native_rows f H"
    using row by (auto simp: copy_native_row_member)
  show ?thesis using rel_value_eq[OF sv row]
    rel_value_eq[OF copy_native_rows_functional[OF sv injective] copied]
    by (simp add: native_row_keys_def)
qed

lemma copy_native_row_keys_injective:
  assumes sv: "single_valued H" and injective: "inj f" and keys: "inj_on (native_row_keys H) (rel_dom H)"
  shows "inj_on (native_row_keys (copy_native_rows f H)) (rel_dom (copy_native_rows f H))"
proof (rule inj_onI)
  fix s t assume sd: "s \<in> rel_dom (copy_native_rows f H)" and td: "t \<in> rel_dom (copy_native_rows f H)"
    and equal: "native_row_keys (copy_native_rows f H) s=native_row_keys (copy_native_rows f H) t"
  obtain a where sa: "a \<in> rel_dom H" "s=f a" using sd by (auto simp: copy_native_row_domain)
  obtain b where tb: "b \<in> rel_dom H" "t=f b" using td by (auto simp: copy_native_row_domain)
  have same: "native_row_keys H a=native_row_keys H b"
    using equal copy_native_row_key[OF sv injective sa(1)] copy_native_row_key[OF sv injective tb(1)]
      sa(2) tb(2) by simp
  have "a=b" by (rule inj_onD[OF keys same sa(1) tb(1)])
  then show "s=t" using sa(2) tb(2) by simp
qed

context native_syntax_copy
begin

theorem copy_fixed_table:
  fixes read :: "local_address \<Rightarrow> ('key \<times> 'val) \<Rightarrow> local_address set \<Rightarrow> local_address set \<Rightarrow> bool"
  assumes table: "native_table_at E u r read Q I K"
    and row_copy: "\<And>a q J A. read a q J A \<Longrightarrow> q \<in> Q \<Longrightarrow> other (f a) q (f ` J) (f ` A)"
    and unique: "\<And>a q J A z L B. other a q J A \<Longrightarrow> other a z L B \<Longrightarrow> q=z \<and> J=L \<and> A=B"
  shows "native_table_at F w (f r) other Q (f ` I) (f ` K)"
proof -
  obtain T M where parts: "artifact_at E u T" "family_at T r M"
    "single_valued (native_table_rows M read)" "rel_dom (native_table_rows M read)=rel_dom M"
    "inj_on (native_row_keys (native_table_rows M read)) (rel_dom (native_table_rows M read))"
    "\<forall>s q J A t z L B. (s,q,J,A) \<in> native_table_rows M read \<longrightarrow>
      (t,z,L,B) \<in> native_table_rows M read \<longrightarrow> s\<noteq>t \<longrightarrow> J \<inter> L = {}"
    "insert r (rel_dom M) \<inter> native_row_interiors (native_table_rows M read) = {}"
    "Q=native_row_values (native_table_rows M read)"
    "I=insert r (rel_dom M \<union> native_row_interiors (native_table_rows M read))"
    "K=native_row_slots (native_table_rows M read)" "I \<inter> K = {}"
    using table by (auto simp: native_table_at_def Let_def)
  have same: "T=R" by (rule environment_artifact_unique[OF source_formed parts(1) source])
  have family: "family_at R r M" using parts(2) same by simp
  let ?H = "native_table_rows M read"
  let ?M = "(\<lambda>(s,a). (f s,f a)) ` M"
  let ?J = "native_table_rows ?M other"
  let ?C = "copy_native_rows f ?H"
  have target_family: "family_at S (f r) ?M" by (rule copy_family[OF family])
  have forward:
    "\<And>s a q J A. (s,a) \<in> M \<Longrightarrow> read a q J A \<Longrightarrow> other (f a) q (f ` J) (f ` A)"
  proof -
    fix s a q J A assume member: "(s,a) \<in> M" and row: "read a q J A"
    have present: "q \<in> Q" by (rule native_table_row_value[OF table source family member row])
    show "other (f a) q (f ` J) (f ` A)" by (rule row_copy[OF row present])
  qed
  have exact: "?J=?C"
  proof (rule set_eqI)
    fix x :: "local_address \<times> (('key \<times> 'val) \<times> (local_address set \<times> local_address set))"
    obtain s q J A where shape: "x=(s,q,J,A)" by (cases x) auto
    show "x \<in> ?J \<longleftrightarrow> x \<in> ?C"
    proof (simp only: shape copy_native_row_member, rule iffI)
      assume "(s,q,J,A) \<in> ?J"
      then obtain t a where original: "(t,a) \<in> M" "s=f t" "other (f a) q J A"
        by (auto simp: native_table_rows_member)
      obtain z L B where old: "read a z L B"
        using native_table_raw_row[OF table source family original(1)] by blast
      have copied: "other (f a) z (f ` L) (f ` B)" by (rule forward[OF original(1) old])
      have equal: "q=z \<and> J=f ` L \<and> A=f ` B" by (rule unique[OF original(3) copied])
      have row: "(t,z,L,B) \<in> ?H" using original(1) old by (auto simp: native_table_rows_member)
      show "\<exists>t L B. (t,q,L,B) \<in> ?H \<and> s=f t \<and> J=f ` L \<and> A=f ` B"
        using row equal original(2) by blast
    next
      assume "\<exists>t L B. (t,q,L,B) \<in> ?H \<and> s=f t \<and> J=f ` L \<and> A=f ` B"
      then obtain t a L B where original: "(t,a) \<in> M" "read a q L B" "s=f t" "J=f ` L" "A=f ` B"
        by (auto simp: native_table_rows_member)
      have copied: "other (f a) q (f ` L) (f ` B)" by (rule forward[OF original(1,2)])
      show "(s,q,J,A) \<in> ?J"
        using original copied by (auto simp: native_table_rows_member)
    qed
  qed
  have functional: "single_valued ?J" using copy_native_rows_functional[OF parts(3) injective] by (simp only: exact)
  have domain: "rel_dom ?J=rel_dom ?M" by (simp only: exact copy_native_row_domain parts(4) pair_image_domain)
  have keys: "inj_on (native_row_keys ?J) (rel_dom ?J)"
    using copy_native_row_keys_injective[OF parts(3) injective parts(5)] by (simp only: exact)
  have row_separation:
    "\<forall>s q J A t z L B. (s,q,J,A) \<in> ?J \<longrightarrow> (t,z,L,B) \<in> ?J \<longrightarrow> s\<noteq>t \<longrightarrow> J \<inter> L = {}"
  proof (intro allI impI)
    fix s q J A t z L B assume left: "(s,q,J,A) \<in> ?J" and right: "(t,z,L,B) \<in> ?J" and different: "s\<noteq>t"
    obtain a X U where first: "(a,q,X,U) \<in> ?H" "s=f a" "J=f ` X"
      using left by (auto simp: exact copy_native_row_member)
    obtain b Y V where second: "(b,z,Y,V) \<in> ?H" "t=f b" "L=f ` Y"
      using right by (auto simp: exact copy_native_row_member)
    have ab: "a\<noteq>b" using first(2) second(2) different by auto
    have separate: "X \<inter> Y = {}" using parts(6) first(1) second(1) ab by blast
    show "J \<inter> L = {}" using image_Int[OF injective, of X Y] separate first(3) second(3) by simp
  qed
  have head: "insert (f r) (rel_dom ?M) \<inter> native_row_interiors ?J = {}"
    using image_Int[OF injective, of "insert r (rel_dom M)" "native_row_interiors ?H"] parts(7)
    by (simp only: exact copy_native_row_interiors pair_image_domain image_insert image_empty)
  have projection: "Q=native_row_values ?J" by (simp only: exact copy_native_row_values parts(8))
  have interior: "f ` I=insert (f r) (rel_dom ?M \<union> native_row_interiors ?J)"
    by (simp only: parts(9) exact copy_native_row_interiors pair_image_domain image_insert image_Un)
  have slots: "f ` K=native_row_slots ?J" by (simp only: exact copy_native_row_slots parts(10))
  have boundary: "f ` I \<inter> f ` K = {}" using image_Int[OF injective, of I K] parts(11) by simp
  show ?thesis unfolding native_table_at_def Let_def
    by (rule conjI[OF target_formed], rule exI[of _ S], rule exI[of _ ?M])
       (use target target_family functional domain keys row_separation head projection interior slots boundary in auto)
qed

end

text \<open>
  Injective physical copying preserves each decoded row value and key while
  moving every row occurrence, interior, and slot. Complete source decoding
  and unique destination decoding force the copied row graph to be exact;
  no extra destination row interpretation is admitted.
\<close>

end
