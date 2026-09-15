theory RRA_Cached_Graft_Cases
  imports RRA_Cached_Graft_Methods
begin

definition cached_graft_source_rows where
  "cached_graft_source_rows w=graft_admission_case_family (\<lambda>A B. (A,B)) w"

definition cached_graft_previous_case :: "nat\<Rightarrow>cached_graft_subject" where
  "cached_graft_previous_case w=(case cached_graft_source_rows w of ((A,B),u,(C,D)) \<Rightarrow>
    (load_digit_allocated A B,u,C,D))"

definition cached_graft_chain :: "bool\<Rightarrow>nat\<Rightarrow>digit_allocated_environment option" where
  "cached_graft_chain grow n=(let R=finite_payload_syntax [7];T=finite_payload_syntax [8];
    imported=(if grow then [(None,R),(Some [],T)] else [(None,R)]) in
    foldl (\<lambda>current i. case current of None \<Rightarrow> None | Some q \<Rightarrow>
      digit_allocated_graft q None imported []) (load_digit_allocated [(None,R)] []) [0..<n])"

definition cached_graft_case :: "nat\<Rightarrow>cached_graft_subject" where
  "cached_graft_case w=(let R=finite_payload_syntax [7];T=finite_payload_syntax [8];
    imported=[(None,R),(Some [],T)] in
    if w<22 then cached_graft_previous_case w
    else if w=22 then (cached_graft_chain True 32,None,imported,[])
    else if w=23 then (cached_graft_chain True 128,None,imported,[])
    else if w=24 then (cached_graft_chain False 3,None,imported,[])
    else if w=25 then (cached_graft_chain False 3,None,[(None,R)],[])
    else (cached_graft_chain True 2,None,[(None,R),(Some (replicate 128 0),T)],
      [((None,[]),Some (replicate 128 0))]))"

definition cached_graft_source_report where
  "cached_graft_source_report w=(case cached_graft_source_rows w of ((A,B),u,(C,D)) \<Rightarrow>
    ((finite_enumerated_environment A B,u,finite_enumerated_environment C D),graft_admission_case w))"

definition cached_graft_sources_equal where
  "cached_graft_sources_equal w=(fst (cached_graft_source_report w)=snd (cached_graft_source_report w))"

definition cached_graft_source_scope :: "nat list\<Rightarrow>nat list" where
  "cached_graft_source_scope ws=filter (\<lambda>w. w<22) ws"

lemma cached_graft_source_scope_exact:
  "w\<in>set (cached_graft_source_scope ws) \<longleftrightarrow> w\<in>set ws \<and> w<22"
  by (simp add: cached_graft_source_scope_def)

lemma cached_graft_previous_cases:
  "w<22 \<Longrightarrow> cached_graft_case w=cached_graft_previous_case w"
  by (simp add: cached_graft_case_def Let_def)

definition cached_graft_chain_report where
  "cached_graft_chain_report grow n=map_option digit_allocated_view (cached_graft_chain grow n)"

text \<open>
  Actual source rows instantiate the previously specified complete case family.
  Closed loading distinguishes malformed old preparation from failed new grafts.
  Each persistent history grafts into its preceding actual typed state. Repeated
  boundary-only grafts advance the stored head without adding a use, exposing
  the difference between a valid bound and the minimal recomputed bound.
\<close>

end
