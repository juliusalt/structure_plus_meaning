theory Finite_Investigation_Execution_Sharing
  imports Finite_Assessment_Reports
begin

declare subject_investigation_selected_def[code del]

lemma subject_investigation_selected_shared_code [code]:
  "subject_investigation_selected cs fs ws observe=(let
    relation=subject_investigation_relation cs fs ws observe
    in filter (\<lambda>d. \<forall>c\<in>set cs. (c,d)\<in>set relation) cs)"
  by (simp only: subject_investigation_selected_def Let_def)

declare assessed_subject_investigation_def[code del]

lemma assessed_subject_investigation_shared_code [code]:
  "assessed_subject_investigation cs fs ws assess inspect=(let
    rows=assessed_subject_observations cs fs ws assess inspect;
    observed=(\<lambda>c w f. (f,c,w)\<in>set rows);
    relation=subject_investigation_relation cs fs ws observed;
    selected=filter (\<lambda>d. \<forall>c\<in>set cs. (c,d)\<in>set relation) cs
    in (rows,relation,selected,subject_investigation_adequate cs fs ws observed))"
  by (simp only: assessed_subject_investigation_def subject_investigation_selected_def Let_def)

text \<open>
  Both equations preserve the complete ordered result for arbitrary candidate,
  facet and problem lists and arbitrary actual observation operations. The
  assessment equation shares the same relation between its returned relation
  field and selection. No observation, relation pair, selection or adequacy
  field is supplied by a host table. Physical timing remains a separate account.
\<close>

end
