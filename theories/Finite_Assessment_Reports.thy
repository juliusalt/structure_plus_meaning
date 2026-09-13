theory Finite_Assessment_Reports
  imports Finite_Assessed_Investigation
begin

section \<open>Construct complete report tables from actual contexts\<close>

definition context_assessment_table where
  "context_assessment_table cs ws context assess=map (\<lambda>w.
    let C=context w in (w,C,map (\<lambda>c. (c,assess c C)) cs)) ws"

definition context_assessment_lookup where
  "context_assessment_lookup table c w=(case map_of table w of None \<Rightarrow> None
    | Some (C,cells) \<Rightarrow> map_of cells c)"

lemma mapped_function_lookup:
  "map_of (map (\<lambda>k. (k,f k)) ks) k=(if k\<in>set ks then Some (f k) else None)"
  by (induction ks) auto

lemma context_assessment_lookup_exact:
  "context_assessment_lookup (context_assessment_table cs ws context assess) c w=
    (if w\<in>set ws \<and> c\<in>set cs then Some (assess c (context w)) else None)"
  by (simp add: context_assessment_lookup_def context_assessment_table_def
    Let_def mapped_function_lookup)

lemma assessed_subject_observations_cong:
  assumes same: "\<And>c w f. c\<in>set cs \<Longrightarrow> w\<in>set ws \<Longrightarrow> f\<in>set fs \<Longrightarrow>
    inspect (assess c w) f=inspect' (assess' c w) f"
  shows "assessed_subject_observations cs fs ws assess inspect=
    assessed_subject_observations cs fs ws assess' inspect'"
  unfolding assessed_subject_observations_def
proof (rule arg_cong[where f=concat], rule map_cong[OF refl])
  fix c assume c: "c\<in>set cs"
  show "concat (map (\<lambda>w. let A=assess c w in map (\<lambda>f. (f,c,w)) (filter (inspect A) fs)) ws)=
    concat (map (\<lambda>w. let A=assess' c w in map (\<lambda>f. (f,c,w)) (filter (inspect' A) fs)) ws)"
  proof (rule arg_cong[where f=concat], rule map_cong[OF refl])
    fix w assume w: "w\<in>set ws"
    have filtered: "filter (inspect (assess c w)) fs=filter (inspect' (assess' c w)) fs"
      by (rule filter_cong[OF refl]) (use same[OF c w] in blast)
    show "(let A=assess c w in map (\<lambda>f. (f,c,w)) (filter (inspect A) fs))=
      (let A=assess' c w in map (\<lambda>f. (f,c,w)) (filter (inspect' A) fs))"
      by (simp only: Let_def filtered)
  qed
qed

lemma assessed_subject_investigation_cong:
  assumes "\<And>c w f. c\<in>set cs \<Longrightarrow> w\<in>set ws \<Longrightarrow> f\<in>set fs \<Longrightarrow>
    inspect (assess c w) f=inspect' (assess' c w) f"
  shows "assessed_subject_investigation cs fs ws assess inspect=
    assessed_subject_investigation cs fs ws assess' inspect'"
proof -
  have rows: "assessed_subject_observations cs fs ws assess inspect=
    assessed_subject_observations cs fs ws assess' inspect'"
    by (rule assessed_subject_observations_cong) (rule assms)
  show ?thesis by (simp only: assessed_subject_investigation_def rows)
qed

definition context_assessment_investigation where
  "context_assessment_investigation cs fs ws table inspect=
    assessed_subject_investigation cs fs ws (context_assessment_lookup table)
      (\<lambda>A f. case A of None \<Rightarrow> False | Some a \<Rightarrow> inspect a f)"

theorem context_assessment_investigation_exact:
  "context_assessment_investigation cs fs ws
      (context_assessment_table cs ws context assess) inspect=
    assessed_subject_investigation cs fs ws (\<lambda>c w. assess c (context w)) inspect"
  unfolding context_assessment_investigation_def
  by (rule assessed_subject_investigation_cong)
    (simp add: context_assessment_lookup_exact)

text \<open>
  Each context and every assessment cell is constructed by the supplied actual
  operations. Repeated indices preserve the same value. Lookup and projection
  preserve the complete ordered observation list and every comparison field.
  The lookup theorem requires this constructed table; arbitrary supplied cells
  do not acquire a satisfaction claim about another operation or subject.
\<close>

end
