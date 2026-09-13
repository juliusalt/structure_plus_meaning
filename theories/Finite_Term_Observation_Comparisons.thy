theory Finite_Term_Observation_Comparisons
  imports Factor_Executable_Terms
begin

definition finite_term_observation_comparison where
  "finite_term_observation_comparison left right=(case left of None \<Rightarrow> None
    | Some (P,A) \<Rightarrow> map_option (\<lambda>(Q,B). (B |-| A,A |-| B)) right)"

definition finite_term_observation_comparison_holds where
  "finite_term_observation_comparison_holds f left right=(case finite_term_observation_comparison left right of
    None \<Rightarrow> False | Some (extra,missing) \<Rightarrow> (if f=0 then extra={||} else missing={||}))"

theorem finite_term_observation_comparison_exact:
  assumes left: "\<And>P A. L=Some (P,A) \<longleftrightarrow> left_ready P \<and> fset A={t\<in>fset T. left_meaning P t}"
    and right: "\<And>Q B. R=Some (Q,B) \<longleftrightarrow> right_ready Q \<and> fset B={t\<in>fset T. right_meaning Q t}"
  shows "finite_term_observation_comparison_holds f L R \<longleftrightarrow>
    (\<exists>P Q. left_ready P \<and> right_ready Q \<and>
      (\<forall>t\<in>fset T. if f=0 then right_meaning Q t \<longrightarrow> left_meaning P t
        else left_meaning P t \<longrightarrow> right_meaning Q t))"
proof
  assume holds: "finite_term_observation_comparison_holds f L R"
  obtain P A Q B where l: "L=Some (P,A)" and r: "R=Some (Q,B)"
    and residual: "if f=0 then B |-| A={||} else A |-| B={||}"
    using holds by (auto simp: finite_term_observation_comparison_holds_def
      finite_term_observation_comparison_def split: option.splits prod.splits)
  have lr: "left_ready P" and lm: "fset A={t\<in>fset T. left_meaning P t}"
    using l by (simp only: left; blast)+
  have rr: "right_ready Q" and rm: "fset B={t\<in>fset T. right_meaning Q t}"
    using r by (simp only: right; blast)+
  have compared: "\<forall>t\<in>fset T. if f=0 then right_meaning Q t \<longrightarrow> left_meaning P t
      else left_meaning P t \<longrightarrow> right_meaning Q t"
    using residual lm rm by (auto simp: fset_eq_iff split: if_splits)
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
  let ?A="ffilter (left_meaning P) T"
  let ?B="ffilter (right_meaning Q) T"
  have l: "L=Some (P,?A)" by (simp only: left; use lr in auto)
  have r: "R=Some (Q,?B)" by (simp only: right; use rr in auto)
  have residual: "if f=0 then ?B |-| ?A={||} else ?A |-| ?B={||}"
    using compared by (auto simp: fset_eq_iff split: if_splits)
  show "finite_term_observation_comparison_holds f L R"
    by (simp add: finite_term_observation_comparison_holds_def finite_term_observation_comparison_def l r residual)
qed

export_code finite_term_observation_comparison finite_term_observation_comparison_holds checking SML

end
