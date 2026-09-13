theory Finite_Term_Observation_Comparisons
  imports Factor_Executable_Terms Finite_Set_Transformations
begin

definition finite_term_observation_comparison where
  "finite_term_observation_comparison left right=(case left of None \<Rightarrow> None
    | Some (P,A) \<Rightarrow> map_option (\<lambda>(Q,B). (B |-| A,A |-| B)) right)"

definition finite_term_observation_comparison_holds where
  "finite_term_observation_comparison_holds f left right=(case finite_term_observation_comparison left right of
    None \<Rightarrow> False | Some (extra,missing) \<Rightarrow> (if f=0 then extra={||} else missing={||}))"

theorem finite_term_observation_comparison_containment:
  assumes reading: "\<And>P A. L=Some (P,A) \<Longrightarrow> ready P \<and> fset A=meaning P"
    and total: "\<And>P. ready P \<Longrightarrow> \<exists>A. L=Some (P,A)"
  shows "finite_term_observation_comparison_holds f L R \<longleftrightarrow>
    (\<exists>P Q B. ready P \<and> R=Some (Q,B) \<and>
      (if f=0 then fset B\<subseteq>meaning P else meaning P\<subseteq>fset B))"
proof
  assume holds: "finite_term_observation_comparison_holds f L R"
  obtain P A Q B where left: "L=Some (P,A)" and right: "R=Some (Q,B)"
    and residual: "if f=0 then B |-| A={||} else A |-| B={||}"
    using holds by (auto simp: finite_term_observation_comparison_holds_def
      finite_term_observation_comparison_def split: option.splits prod.splits)
  show "\<exists>P Q B. ready P \<and> R=Some (Q,B) \<and>
      (if f=0 then fset B\<subseteq>meaning P else meaning P\<subseteq>fset B)"
    using reading[OF left] right residual
    by (auto simp: finite_difference_empty less_eq_fset.rep_eq split: if_splits; blast)
next
  assume condition: "\<exists>P Q B. ready P \<and> R=Some (Q,B) \<and>
      (if f=0 then fset B\<subseteq>meaning P else meaning P\<subseteq>fset B)"
  obtain P Q B where ready: "ready P" and right: "R=Some (Q,B)"
    and included: "if f=0 then fset B\<subseteq>meaning P else meaning P\<subseteq>fset B"
    using condition by blast
  obtain A where left: "L=Some (P,A)" using total[OF ready] by blast
  have residual: "if f=0 then B |-| A={||} else A |-| B={||}"
    using included reading[OF left]
    by (auto simp: finite_difference_empty less_eq_fset.rep_eq split: if_splits)
  show "finite_term_observation_comparison_holds f L R"
    by (simp add: finite_term_observation_comparison_holds_def finite_term_observation_comparison_def
      left right residual)
qed

theorem finite_term_observation_comparison_exact:
  assumes left: "\<And>P A. L=Some (P,A) \<longleftrightarrow> left_ready P \<and> fset A={t\<in>fset T. left_meaning P t}"
    and right: "\<And>Q B. R=Some (Q,B) \<longleftrightarrow> right_ready Q \<and> fset B={t\<in>fset T. right_meaning Q t}"
  shows "finite_term_observation_comparison_holds f L R \<longleftrightarrow>
    (\<exists>P Q. left_ready P \<and> right_ready Q \<and>
      (\<forall>t\<in>fset T. if f=0 then right_meaning Q t \<longrightarrow> left_meaning P t
        else left_meaning P t \<longrightarrow> right_meaning Q t))"
proof -
  have total: "\<exists>A. L=Some (P,A)" if "left_ready P" for P
    by (rule exI[of _ "ffilter (left_meaning P) T"])
      (simp only: left; use that in auto)
  have comparison: "finite_term_observation_comparison_holds f L R \<longleftrightarrow>
      (\<exists>P Q B. left_ready P \<and> R=Some (Q,B) \<and>
        (if f=0 then fset B\<subseteq>{t\<in>fset T. left_meaning P t}
          else {t\<in>fset T. left_meaning P t}\<subseteq>fset B))"
    by (rule finite_term_observation_comparison_containment[OF _ total])
      (simp only: left)
  show ?thesis
  proof
  assume holds: "finite_term_observation_comparison_holds f L R"
  obtain P Q B where lr: "left_ready P" and r: "R=Some (Q,B)"
    and included: "if f=0 then fset B\<subseteq>{t\<in>fset T. left_meaning P t}
      else {t\<in>fset T. left_meaning P t}\<subseteq>fset B"
    using holds by (simp only: comparison; blast)
  have rr: "right_ready Q" and rm: "fset B={t\<in>fset T. right_meaning Q t}"
    using r by (simp only: right; blast)+
  have compared: "\<forall>t\<in>fset T. if f=0 then right_meaning Q t \<longrightarrow> left_meaning P t
      else left_meaning P t \<longrightarrow> right_meaning Q t"
    using included rm by (auto split: if_splits)
  show "\<exists>P Q. left_ready P \<and> right_ready Q \<and>
      (\<forall>t\<in>fset T. if f=0 then right_meaning Q t \<longrightarrow> left_meaning P t
        else left_meaning P t \<longrightarrow> right_meaning Q t)"
    using lr rr compared by blast
  next
  assume condition: "\<exists>P Q. left_ready P \<and> right_ready Q \<and>
      (\<forall>t\<in>fset T. if f=0 then right_meaning Q t \<longrightarrow> left_meaning P t
        else left_meaning P t \<longrightarrow> right_meaning Q t)"
  obtain P Q where lr: "left_ready P" and rr: "right_ready Q"
    and compared: "\<forall>t\<in>fset T. if f=0 then right_meaning Q t \<longrightarrow> left_meaning P t
      else left_meaning P t \<longrightarrow> right_meaning Q t"
    using condition by blast
  let ?B="ffilter (right_meaning Q) T"
  have r: "R=Some (Q,?B)" by (simp only: right; use rr in auto)
  have included: "if f=0 then fset ?B\<subseteq>{t\<in>fset T. left_meaning P t}
      else {t\<in>fset T. left_meaning P t}\<subseteq>fset ?B"
    using compared by (auto split: if_splits)
  show "finite_term_observation_comparison_holds f L R"
    by (rule iffD2[OF comparison], rule exI[of _ P], rule exI[of _ Q], rule exI[of _ ?B])
      (use lr r included in blast)
  qed
qed

export_code finite_term_observation_comparison finite_term_observation_comparison_holds checking SML

end
