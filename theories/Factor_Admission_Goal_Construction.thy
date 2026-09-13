theory Factor_Admission_Goal_Construction
  imports Factor_Admission_Installation
begin

section \<open>Goal realization composes through complete program extensions\<close>

definition admission_goal_realized where
  "admission_goal_realized P g d Q \<longleftrightarrow> admission_extension P Q \<and>
    d\<in>system_definitions Q \<and>
    (\<forall>t. (d,t)\<in>positive_meaning Q \<longleftrightarrow> admission_goal_holds (positive_meaning P) g t)"

lemma admission_goal_realized_existing:
  assumes "schema_system_formed P" "d\<in>system_definitions P"
  shows "admission_goal_realized P (Existing_Admission d) d P"
  using assms admission_extension_refl[OF assms(1)]
  by (simp add: admission_goal_realized_def)

theorem admission_goal_realized_pair:
  assumes left: "admission_goal_realized P g a Q"
    and right: "admission_goal_realized Q h b R"
    and supported: "admission_goal_sites h\<subseteq>system_definitions P"
    and extension: "admission_extension R S" and member: "c\<in>system_definitions S"
    and pair: "\<And>t. (c,t)\<in>positive_meaning S \<longleftrightarrow>
      (\<exists>x y. t=Pair_Term x y \<and> (a,x)\<in>positive_meaning R \<and> (b,y)\<in>positive_meaning R)"
  shows "admission_goal_realized P (Paired_Admission g h) c S"
proof -
  have first_extension: "admission_extension P Q" and first_member: "a\<in>system_definitions Q"
    using left by (simp only: admission_goal_realized_def; blast)+
  have second_extension: "admission_extension Q R"
    using right by (simp only: admission_goal_realized_def; blast)
  have first_meaning: "(a,t)\<in>positive_meaning R \<longleftrightarrow> admission_goal_holds (positive_meaning P) g t" for t
    using admission_extension_meaning[OF second_extension first_member, of t] left
    by (simp only: admission_goal_realized_def; blast)
  have second_meaning: "(b,t)\<in>positive_meaning R \<longleftrightarrow> admission_goal_holds (positive_meaning P) h t" for t
    using admission_extension_goal[OF first_extension supported, of t] right
    by (simp only: admission_goal_realized_def; blast)
  have meaning: "(c,t)\<in>positive_meaning S \<longleftrightarrow>
      admission_goal_holds (positive_meaning P) (Paired_Admission g h) t" for t
    by (simp only: pair admission_goal_holds.simps first_meaning second_meaning)
  have composed: "admission_extension P S"
    by (rule admission_extension_trans[OF admission_extension_trans[OF first_extension second_extension] extension])
  show ?thesis using composed member meaning by (simp only: admission_goal_realized_def; blast)
qed

theorem admission_goal_realized_collection:
  assumes child: "admission_goal_realized P g a Q"
    and extension: "admission_extension Q R" and member: "b\<in>system_definitions R"
    and collection: "\<And>t. (b,t)\<in>positive_meaning R \<longleftrightarrow>
      (\<exists>xs. t=data_list_term xs \<and> (\<forall>x\<in>set xs. (a,x)\<in>positive_meaning Q))"
  shows "admission_goal_realized P (Collected_Admission g) b R"
proof -
  have child_extension: "admission_extension P Q"
    and child_meaning: "\<And>t. (a,t)\<in>positive_meaning Q \<longleftrightarrow> admission_goal_holds (positive_meaning P) g t"
    using child by (simp only: admission_goal_realized_def; blast)+
  have meaning: "(b,t)\<in>positive_meaning R \<longleftrightarrow>
      admission_goal_holds (positive_meaning P) (Collected_Admission g) t" for t
    by (simp only: collection admission_goal_holds.simps child_meaning)
  have composed: "admission_extension P R" by (rule admission_extension_trans[OF child_extension extension])
  show ?thesis using composed member meaning by (simp only: admission_goal_realized_def; blast)
qed

section \<open>The shared goal constructor uses the component contracts once\<close>

locale admission_goal_constructor =
  fixes program :: "'s\<Rightarrow>('a,'p,'d,'c) schema_system"
    and leaf :: "'d\<Rightarrow>'s\<Rightarrow>('d\<times>'s) option"
    and pair :: "'d\<Rightarrow>'d\<Rightarrow>'s\<Rightarrow>('d\<times>'s) option"
    and collection :: "'d\<Rightarrow>'s\<Rightarrow>('d\<times>'s) option"
  assumes leaf_step: "\<And>s d. schema_system_formed (program s) \<Longrightarrow> d\<in>system_definitions (program s) \<Longrightarrow>
      leaf d s=Some (d,s)"
    and pair_step: "\<And>s a b. schema_system_formed (program s) \<Longrightarrow>
      a\<in>system_definitions (program s) \<Longrightarrow> b\<in>system_definitions (program s) \<Longrightarrow>
      \<exists>d t. pair a b s=Some (d,t) \<and> admission_extension (program s) (program t) \<and>
        d\<in>system_definitions (program t) \<and>
        (\<forall>x. (d,x)\<in>positive_meaning (program t) \<longleftrightarrow>
          (\<exists>y z. x=Pair_Term y z \<and> (a,y)\<in>positive_meaning (program s) \<and> (b,z)\<in>positive_meaning (program s)))"
    and collection_step: "\<And>s a. schema_system_formed (program s) \<Longrightarrow> a\<in>system_definitions (program s) \<Longrightarrow>
      \<exists>d t. collection a s=Some (d,t) \<and> admission_extension (program s) (program t) \<and>
        d\<in>system_definitions (program t) \<and>
        (\<forall>x. (d,x)\<in>positive_meaning (program t) \<longleftrightarrow>
          (\<exists>xs. x=data_list_term xs \<and> (\<forall>y\<in>set xs. (a,y)\<in>positive_meaning (program s))))"
begin

theorem total:
  assumes source: "schema_system_formed (program s)"
    and supported: "admission_goal_sites g\<subseteq>system_definitions (program s)"
  shows "\<exists>d t. construct_admission_goal leaf pair collection g s=Some (d,t) \<and>
    admission_goal_realized (program s) g d (program t)"
  using source supported
proof (induction g arbitrary: s)
  case (Existing_Admission d)
  have member: "d\<in>system_definitions (program s)" using Existing_Admission.prems(2) by simp
  have result: "construct_admission_goal leaf pair collection (Existing_Admission d) s=Some (d,s)"
    by (simp only: construct_admission_goal.simps leaf_step[OF Existing_Admission.prems(1) member])
  have realized: "admission_goal_realized (program s) (Existing_Admission d) d (program s)"
    by (rule admission_goal_realized_existing[OF Existing_Admission.prems(1) member])
  show ?case using result realized by blast
next
  case (Paired_Admission g h)
  have supported_g: "admission_goal_sites g\<subseteq>system_definitions (program s)"
    and supported_h: "admission_goal_sites h\<subseteq>system_definitions (program s)"
    using Paired_Admission.prems(2) by auto
  obtain a t where first_result: "construct_admission_goal leaf pair collection g s=Some (a,t)"
    and first_realized: "admission_goal_realized (program s) g a (program t)"
    using Paired_Admission.IH(1)[OF Paired_Admission.prems(1) supported_g] by blast
  have first_extension: "admission_extension (program s) (program t)"
    and first_member: "a\<in>system_definitions (program t)"
    using first_realized by (simp only: admission_goal_realized_def; blast)+
  have first_formed: "schema_system_formed (program t)"
    using first_extension by (simp only: admission_extension_def; blast)
  have continued_support: "admission_goal_sites h\<subseteq>system_definitions (program t)"
    using supported_h admission_extension_definitions[OF first_extension] by blast
  obtain b u where second_result: "construct_admission_goal leaf pair collection h t=Some (b,u)"
    and second_realized: "admission_goal_realized (program t) h b (program u)"
    using Paired_Admission.IH(2)[OF first_formed continued_support] by blast
  have second_extension: "admission_extension (program t) (program u)"
    and second_member: "b\<in>system_definitions (program u)"
    using second_realized by (simp only: admission_goal_realized_def; blast)+
  have second_formed: "schema_system_formed (program u)"
    using second_extension by (simp only: admission_extension_def; blast)
  have retained_first: "a\<in>system_definitions (program u)"
    using first_member admission_extension_definitions[OF second_extension] by blast
  obtain d v where combined_result: "pair a b u=Some (d,v)"
    and combined_extension: "admission_extension (program u) (program v)"
    and combined_member: "d\<in>system_definitions (program v)"
    and combined_meaning: "\<And>x. (d,x)\<in>positive_meaning (program v) \<longleftrightarrow>
      (\<exists>y z. x=Pair_Term y z \<and> (a,y)\<in>positive_meaning (program u) \<and> (b,z)\<in>positive_meaning (program u))"
    using pair_step[OF second_formed retained_first second_member] by blast
  have realized: "admission_goal_realized (program s) (Paired_Admission g h) d (program v)"
    by (rule admission_goal_realized_pair[OF first_realized second_realized supported_h
      combined_extension combined_member combined_meaning])
  have result: "construct_admission_goal leaf pair collection (Paired_Admission g h) s=Some (d,v)"
    by (simp add: first_result second_result combined_result)
  show ?case using result realized by blast
next
  case (Collected_Admission g)
  have supported_g: "admission_goal_sites g\<subseteq>system_definitions (program s)"
    using Collected_Admission.prems(2) by simp
  obtain a t where child_result: "construct_admission_goal leaf pair collection g s=Some (a,t)"
    and child_realized: "admission_goal_realized (program s) g a (program t)"
    using Collected_Admission.IH[OF Collected_Admission.prems(1) supported_g] by blast
  have child_formed: "schema_system_formed (program t)" and child_member: "a\<in>system_definitions (program t)"
    using child_realized by (simp only: admission_goal_realized_def admission_extension_def; blast)+
  obtain d u where combined_result: "collection a t=Some (d,u)"
    and combined_extension: "admission_extension (program t) (program u)"
    and combined_member: "d\<in>system_definitions (program u)"
    and combined_meaning: "\<And>x. (d,x)\<in>positive_meaning (program u) \<longleftrightarrow>
      (\<exists>xs. x=data_list_term xs \<and> (\<forall>y\<in>set xs. (a,y)\<in>positive_meaning (program t)))"
    using collection_step[OF child_formed child_member] by blast
  have realized: "admission_goal_realized (program s) (Collected_Admission g) d (program u)"
    by (rule admission_goal_realized_collection[OF child_realized combined_extension combined_member combined_meaning])
  have result: "construct_admission_goal leaf pair collection (Collected_Admission g) s=Some (d,u)"
    by (simp add: child_result combined_result)
  show ?case using result realized by blast
qed

theorem correct:
  assumes source: "schema_system_formed (program s)"
    and supported: "admission_goal_sites g\<subseteq>system_definitions (program s)"
    and result: "construct_admission_goal leaf pair collection g s=Some (d,t)"
  shows "admission_goal_realized (program s) g d (program t)"
  using total[OF source supported] result by auto

end

end
