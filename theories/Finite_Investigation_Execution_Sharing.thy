theory Finite_Investigation_Execution_Sharing
  imports Finite_Assessment_Reports Member_Tree_Indexes "HOL-Library.Product_Lexorder"
begin

declare subject_investigation_selected_def[code del]

lemma subject_investigation_selected_shared_code [code]:
  "subject_investigation_selected cs fs ws observe=(let
    T=ordered_member_tree (fset_of_list (subject_investigation_relation cs fs ws observe))
    in filter (\<lambda>d. \<forall>c\<in>set cs. RBT.lookup T (c,d)\<noteq>None) cs)"
  by (simp only: subject_investigation_selected_def Let_def listed_member_lookup)

declare assessed_subject_investigation_def[code del]

lemma assessed_subject_investigation_shared_code [code]:
  "assessed_subject_investigation cs fs ws assess inspect=(let
    rows=assessed_subject_observations cs fs ws assess inspect;
    R=ordered_member_tree (fset_of_list rows);
    observed=(\<lambda>c w f. RBT.lookup R (f,c,w)\<noteq>None);
    relation=subject_investigation_relation cs fs ws observed;
    T=ordered_member_tree (fset_of_list relation);
    selected=filter (\<lambda>d. \<forall>c\<in>set cs. RBT.lookup T (c,d)\<noteq>None) cs
    in (rows,relation,selected,subject_investigation_adequate cs fs ws observed))"
  by (simp only: assessed_subject_investigation_def subject_investigation_selected_def Let_def
    listed_member_lookup)

text \<open>
  Both equations preserve the complete ordered result for arbitrary candidate,
  facet and problem lists and arbitrary actual observation operations. The observation rows and
  the relation are each indexed once, so every membership question is one lookup where a list of up
  to one row per pair of candidates had been scanned for it. The
  assessment equation shares the same relation between its returned relation
  field and selection. No observation, relation pair, selection or adequacy
  field is supplied by a host table. Physical timing remains a separate account.
\<close>

end
