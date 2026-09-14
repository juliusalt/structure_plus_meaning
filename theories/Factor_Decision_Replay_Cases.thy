theory Factor_Decision_Replay_Cases
  imports Factor_Finite_Requirement_Decision_Replay Factor_Requirement_Decision_Investigation
    Factor_Native_Replay_Cases
begin

definition decision_certificate_subject where
  "decision_certificate_subject Z c=(case Z of (entry,F,v,Q,D,A,T,Ys) \<Rightarrow>
    case c of ((d,t),p) \<Rightarrow> (F,v,[],p,d,t))"

definition decision_replay_construction where
  "decision_replay_construction m X=map_option finite_decision_replay_body (requirement_decision_method m X)"

definition decision_replay_mutation where
  "decision_replay_mutation (m::nat) X result=(if m<4 then result else if m=4 then None else map_option (\<lambda>(Z,R).
    (Z,if m=5 then {||}
      else if m=6 then (case Z of (d,F,v,Q,D,A,T,Ys) \<Rightarrow> finite_certificate_replays F v [] T)
      else if m=7 then fimage (\<lambda>(c,replay). (c,None)) R
      else if m=8 \<or> m=9 \<or> m=10 then fimage (\<lambda>(c,replay).
        (c,native_replay_apply (if m=8 then 11 else if m=9 then 3 else 9)
          (decision_certificate_subject Z c) replay)) R
      else if m=11 then (case X of (E,u,r,gs,Xs) \<Rightarrow>
        finite_certificate_replays E u r (finite_decision_certificates Z))
      else R)) result)"

lemma decision_replay_mutation_initial:
  "m<4 \<Longrightarrow> decision_replay_mutation m X result=result"
  by (simp only: decision_replay_mutation_def if_True)

definition decision_replay_method where
  "decision_replay_method (m::nat) X=decision_replay_mutation m X
    (decision_replay_construction (if m<4 then m else 0) X)"

theorem decision_replay_original:
  "decision_replay_method 0 (E,u,r,gs,Xs)=finite_requirement_decision_replay E u r gs Xs"
  by (simp add: decision_replay_method_def
    decision_replay_mutation_initial decision_replay_construction_def requirement_decision_method_original
    requirement_decision_base_def finite_requirement_decision_replay_def finite_source_decision_replay_def
    finite_requirement_decision_def case_prod_conv)

lemma decision_replay_original_projection:
  "map_option fst (decision_replay_method 0 (E,u,r,gs,Xs))=finite_requirement_decision E u r gs Xs"
  by (simp only: decision_replay_original finite_requirement_decision_replay_projection)

definition decision_replay_context where
  "decision_replay_context w=map_option (\<lambda>X. (X,(requirement_decision_reference X,
    requirement_decision_original_report X),map (\<lambda>m. (m,decision_replay_construction m X)) [0,1,2,3]))
      (native_requirement_problem w)"

definition decision_replay_prepared where
  "decision_replay_prepared (m::nat) X bases=decision_replay_mutation m X
    (case map_of bases (if m<4 then m else 0) of None \<Rightarrow> None | Some result \<Rightarrow> result)"

lemma decision_replay_prepared_exact:
  "decision_replay_prepared m X (map (\<lambda>k. (k,decision_replay_construction k X)) [0,1,2,3])=
    decision_replay_method m X"
proof -
  have member: "(if m<4 then m else 0)\<in>set [0,1,2,3]" by (auto; arith)
  show ?thesis by (simp only: decision_replay_prepared_def mapped_function_lookup member
    if_True option.case decision_replay_method_def)
qed

text \<open>
  Four actual original-requirement constructions precede all replay controls.
  Later candidates remove the complete result, remove required replay rows,
  include unrelated positive certificates, return unavailable replay values,
  enlarge the retained environment, erase claimed mappings or call interiors,
  or replay the new guard certificate against the earlier source. Each keeps
  the original complete input and its independently computed reference.
\<close>

end
