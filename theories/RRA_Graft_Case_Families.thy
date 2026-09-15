theory RRA_Graft_Case_Families
  imports RRA_Graft_Admission_Methods
begin

type_synonym 'e graft_case_constructor = "(local_address option\<times>finite_exact_artifact) list\<Rightarrow>
  ((local_address option\<times>local_address)\<times>local_address option) list\<Rightarrow>'e"

definition graft_case_family :: "'e graft_case_constructor\<Rightarrow>nat\<Rightarrow>'e\<times>local_address option\<times>'e" where
"graft_case_family environment w=(let R=finite_payload_syntax [7];T=finite_payload_syntax [8];
    E=environment [(None,R)] [];
    F=environment [(None,R),(Some [],T)] []
    in if w=0 then (E,None,E)
    else if w=1 then (environment [(Some [7],R)] [],Some [7],F)
    else if w=2 then (environment [(None,R),(Some [0],T)] [],None,
      environment [(None,R),(Some [],T)] [((Some [],[]),None)])
    else if w=3 then (environment [(None,R),(Some [0],T)] [],None,F)
    else if w=4 then (environment [(None,R),(Some [1],T)] [],None,
      environment [(None,R),(Some [0],T)] [((Some [0],[]),Some [0])])
    else if w=5 then (environment [(Some [300],R)] [],Some [300],F)
    else if w=6 then (environment [(None,R),(Some (replicate 128 0),T)] [],None,F)
    else if w=7 then (environment [(None,R)] [((None,[]),None)],None,
      environment [(None,R),(Some [],T)] [((Some [],[]),None)])
    else if w=8 then (E,None,environment [(None,R),(Some [],T)] [((None,[]),Some [])])
    else if w=9 then (environment [(None,R)] [((None,[]),None)],None,
      environment [(None,R),(Some [],T)] [((None,[]),Some [])])
    else if w=10 then (E,None,environment [(None,R),(Some [],R),(Some [],T)] [])
    else if w=11 then (E,None,environment [(None,T),(Some [],T)] [])
    else if w=12 then (environment [] [],None,environment [] [])
    else if w=13 then (environment
      (map (\<lambda>i. (Some [i,1],T)) [0..<64]@[(None,R)]) [],None,F)
    else if w=14 then (E,None,environment [(None,R),(Some [300],T)] [((None,[]),Some [300])])
    else (E,None,environment [(None,R),(Some [1,2],T),(Some [2,1],T)] []))"

lemma graft_case_family_original:
  "graft_case_family finite_enumerated_environment w=graft_case w"
  by (simp only: graft_case_family_def graft_case_def)

definition graft_admission_case_family :: "'e graft_case_constructor\<Rightarrow>nat\<Rightarrow>'e\<times>local_address option\<times>'e" where
"graft_admission_case_family environment w=(let R=finite_payload_syntax [7];T=finite_payload_syntax [8];
    E=environment [(None,R)] [] in
    if w<16 then graft_case_family environment w
    else if w=16 then (environment [(None,R)] [((None,[]),None)],None,
      environment [(None,R)] [((None,[]),None)])
    else if w=17 then (E,Some [99],environment [(None,R)] [])
    else if w=18 then (E,None,environment [(Some [],R)] [])
    else if w=19 then (environment [(None,R),(None,T)] [],None,E)
    else if w=20 then (E,None,environment [(None,R)] [((None,[256]),None)])
    else (E,None,environment [(None,R)] [((None,[]),Some [])]))"

lemma graft_admission_case_family_original:
  "graft_admission_case_family finite_enumerated_environment w=graft_admission_case w"
  by (simp only: graft_admission_case_family_def graft_admission_case_def graft_case_family_original)

end
