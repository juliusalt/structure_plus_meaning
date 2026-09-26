theory Factor_Narrowed_Controls
  imports Factor_Commitment_Controls Factor_Narrowed_Sockets Factor_Narrowed_Productions
begin

text \<open>
  The narrowed-socket control (R5e, (c)): 48's union in small. Site 0 is membership, 1 inclusion (every element of
  the first list a member of the second), 2 the union u(x,z) :- sub(x,z), sub(z,x), whose answers at x are every list
  with x's set, every order and repetition; 3 inequality of the payloads [1] and [2], 4 absence, 5 distinctness (the
  narrowing consumer), 6 length; 7 root(x,k) :- u(x,z), distinct(z), len(z,k), the union's use narrowed by
  distinctness; 8 the same clause with z in the call, the caller clause at a value of the socket's output; 9 and 10
  the same two without the narrowing consumer. The union's output z is registered at its head variable (variable 1 of
  its clause): the construction returns the distinct union of x, formed and distinct, production (iii) at the
  distinct lists. At x = [1,2,1] R4 neither refutes the true call nor resolves the false one with the union's output
  free, its subtree having no end; at the construction's value the caller clause resolves the true call (length 2) and refutes the false one
  (length 3), which by @{thm [source] registration_complete_at_socket} refutes it at every value in the narrowed class,
  and by narrowing (i) at every value. Without the narrowing consumer the check at the construction's value fails
  (length 3) while the call holds at [1,2,1]: the registration is not complete there, and R4 does not refute
  the call. At (x,[1,2,1]) with length 3 the caller clause without the consumer resolves the true call. The
  production at a head variable is the narrowed socket's, run by R5's committed step, not a registration of the
  witness construction (DECISIONS.md, task 495's entry, the correction by task 725): the search control below runs it.

  The search control (R5f2): 48's union produced at the narrowed socket. The record declares the union's socket in
  site 7's clause (its output premise-only, kept) and in a clause with two unions beside their consumers (site 11,
  55.2's and 60.1's shape), each with the union's production: the collection of the members of x (base queries to
  membership, each element its own key, identity equality of ground terms). The class N is read by the discharge
  alone, never by the search, and stands here as every term. The committed resolution produces the distinct union,
  resolves the true call (length 2) and refutes the false one (length 3), at site 7 and at site 11, where the second
  union is committed and produced once the first is. Site 9 declares no socket: its false call (length 1) is searched
  plainly and left unresolved, never refuted. At bound 0 the production's value is none: R5f1's test still commits the
  goal, its sub-search runs from the state as it is, and at bound 30 the true call is left unresolved (the gap of
  q134, corrected by task 767).
\<close>

definition narrowed_control_union :: "(nat,nat,nat) finite_factor_schema" where
  "narrowed_control_union = \<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)),
    finite_schema_premises={|(0,(1,(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)))),
      (1,(1,(Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 0))))|},
    finite_schema_materials={||}\<rparr>"

definition narrowed_control_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "narrowed_control_program = \<lparr>finite_system_interfaces=fset_of_list (map (\<lambda>d. (d,Finite_Variable 0)) [0..<11]),
    finite_system_clauses={|((0,0),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))),
    finite_schema_premises={||},
    finite_schema_materials={||}\<rparr>),
      ((0,1),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))),
    finite_schema_premises={|(0,(0,(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2))))|},
    finite_schema_materials={||}\<rparr>),
      ((1,0),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Variable 0)),
    finite_schema_premises={||},
    finite_schema_materials={||}\<rparr>),
      ((1,1),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2)),
    finite_schema_premises={|(0,(0,(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2)))),
      (1,(1,(Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))))|},
    finite_schema_materials={||}\<rparr>),
      ((2,0),narrowed_control_union),
      ((3,0),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Pattern_Payload [1]) (Finite_Pattern_Payload [2])),
    finite_schema_premises={||},
    finite_schema_materials={||}\<rparr>),
      ((3,1),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Pattern_Payload [2]) (Finite_Pattern_Payload [1])),
    finite_schema_premises={||},
    finite_schema_materials={||}\<rparr>),
      ((4,0),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Payload [])),
    finite_schema_premises={||},
    finite_schema_materials={||}\<rparr>),
      ((4,1),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))),
    finite_schema_premises={|(0,(3,(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)))),
      (1,(4,(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2))))|},
    finite_schema_materials={||}\<rparr>),
      ((5,0),\<lparr>finite_schema_conclusion=(Finite_Pattern_Payload []),
    finite_schema_premises={||},
    finite_schema_materials={||}\<rparr>),
      ((5,1),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)),
    finite_schema_premises={|(0,(4,(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)))),
      (1,(5,(Finite_Variable 1)))|},
    finite_schema_materials={||}\<rparr>),
      ((6,0),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload [])),
    finite_schema_premises={||},
    finite_schema_materials={||}\<rparr>),
      ((6,1),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Variable 2))),
    finite_schema_premises={|(0,(6,(Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))))|},
    finite_schema_materials={||}\<rparr>),
      ((7,0),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2)),
    finite_schema_premises={|(0,(2,(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)))),
      (1,(5,(Finite_Variable 1))),
      (2,(6,(Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))))|},
    finite_schema_materials={||}\<rparr>),
      ((8,0),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2)),
    finite_schema_premises={|(0,(2,(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)))),
      (1,(5,(Finite_Variable 1))),
      (2,(6,(Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))))|},
    finite_schema_materials={||}\<rparr>),
      ((9,0),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2)),
    finite_schema_premises={|(0,(2,(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)))),
      (2,(6,(Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))))|},
    finite_schema_materials={||}\<rparr>),
      ((10,0),\<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2)),
    finite_schema_premises={|(0,(2,(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)))),
      (2,(6,(Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))))|},
    finite_schema_materials={||}\<rparr>)|}\<rparr>"

fun narrowed_control_list :: "finite_factor_term \<Rightarrow> finite_factor_term list" where
  "narrowed_control_list (Finite_Pair e r) = e # narrowed_control_list r"
| "narrowed_control_list _ = []"

fun narrowed_control_data :: "finite_factor_term list \<Rightarrow> finite_factor_term" where
  "narrowed_control_data [] = Finite_Payload []"
| "narrowed_control_data (e # es) = Finite_Pair e (narrowed_control_data es)"

definition narrowed_control_construction :: "(nat,nat,nat,nat) finite_witness_construction" where
  "narrowed_control_construction = \<lparr>witness_registered = (\<lambda>d S. if d = 2 then {|1|} else {||}),
    witness_value = (\<lambda>P d S B a. if d = 2 \<and> a = 1 then
      map_option (\<lambda>x. narrowed_control_data (remdups (narrowed_control_list x))) (finite_relation_option B 0) else None)\<rparr>"

definition narrowed_control_x :: finite_factor_term where
  "narrowed_control_x = narrowed_control_data [Finite_Payload [1],Finite_Payload [2],Finite_Payload [1]]"

definition narrowed_control_v :: finite_factor_term where
  "narrowed_control_v = narrowed_control_data [Finite_Payload [2],Finite_Payload [1]]"

definition narrowed_control_length :: "nat \<Rightarrow> finite_factor_term" where
  "narrowed_control_length n = narrowed_control_data (replicate n (Finite_Payload []))"

abbreviation narrowed_control_verdict :: "nat \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> bool option" where
  "narrowed_control_verdict d t n \<equiv>
    finite_resolution_verdict (finite_program_resolution no_witness_construction narrowed_control_program d t n)"

definition narrowed_search_query :: "(nat,nat,nat) collection_query" where
  "narrowed_search_query = \<lparr>query_equations=[(0,Finite_Variable 0)],query_site=0,
    query_goal=Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 0),query_element=1\<rparr>"

definition narrowed_search_family :: "(nat,nat,nat) collection_family" where
  "narrowed_search_family = \<lparr>family_base=[narrowed_search_query],family_step=None,
    family_key=(Finite_Variable 0,0),family_identity=None\<rparr>"

definition narrowed_search_registration :: "(nat,nat,nat,nat) collection_registration" where
  "narrowed_search_registration = \<lparr>registration_site=2,registration_schema=narrowed_control_union,
    registration_variable=1,registration_families=Single_Family narrowed_search_family\<rparr>"

definition narrowed_search_clause :: "(nat,nat,nat) finite_factor_schema" where
  "narrowed_search_clause = \<lparr>finite_schema_conclusion=(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2)),
    finite_schema_premises={|(0,(2,(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)))),
      (1,(5,(Finite_Variable 1))),
      (2,(6,(Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))))|},
    finite_schema_materials={||}\<rparr>"

definition narrowed_search_two :: "(nat,nat,nat) finite_factor_schema" where
  "narrowed_search_two = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0)
      (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 4)),
    finite_schema_premises={|(0,(2,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2))),
      (1,(2,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3))),
      (2,(5,Finite_Variable 2)),(3,(5,Finite_Variable 3)),
      (4,(6,Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 4))),
      (5,(6,Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4)))|},
    finite_schema_materials={||}\<rparr>"

definition narrowed_search_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "narrowed_search_program = \<lparr>finite_system_interfaces=fset_of_list (map (\<lambda>d. (d,Finite_Variable 0)) [0..<12]),
    finite_system_clauses=finsert ((11,0),narrowed_search_two) (finite_system_clauses narrowed_control_program)\<rparr>"

definition narrowed_search_declarations :: "(nat,nat,nat,nat) produced_declarations" where
  "narrowed_search_declarations = produced (narrowed \<lparr>declared_producers={||},declared_consumers={||},
      declared_sockets={|(7,narrowed_search_clause,0,True,view_identity,view_identity),
        (11,narrowed_search_two,0,True,view_identity,view_identity),
        (11,narrowed_search_two,1,True,view_identity,view_identity)|}\<rparr>
      (\<lambda>_ _ _ _. True))
    (\<lambda>e S s. if (e=7 \<and> s=0) \<or> (e=11 \<and> s\<in>{0,1}) then Some narrowed_search_registration else None)"

definition narrowed_search_y :: finite_factor_term where
  "narrowed_search_y = narrowed_control_data [Finite_Payload [2],Finite_Payload [1],Finite_Payload [2]]"

abbreviation narrowed_search_verdict :: "nat \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool option" where
  "narrowed_search_verdict d t m n \<equiv> finite_resolution_verdict (finite_committed_resolution no_witness_construction
    (finite_narrowed_commitment narrowed_search_program m narrowed_search_declarations {||}) narrowed_search_program d t n)"

lemma narrowed_controls:
  "witness_value narrowed_control_construction narrowed_control_program 2 narrowed_control_union
      {|(0,narrowed_control_x)|} 1 = Some narrowed_control_v \<and>
    narrowed_control_verdict 7 (Finite_Pair narrowed_control_x (narrowed_control_length 2)) 12 \<noteq> Some False \<and>
    narrowed_control_verdict 7 (Finite_Pair narrowed_control_x (narrowed_control_length 3)) 12 \<noteq> Some True \<and>
    narrowed_control_verdict 8 (Finite_Pair (Finite_Pair narrowed_control_x narrowed_control_v)
      (narrowed_control_length 2)) 90 = Some True \<and>
    narrowed_control_verdict 8 (Finite_Pair (Finite_Pair narrowed_control_x narrowed_control_v)
      (narrowed_control_length 3)) 90 = Some False \<and>
    narrowed_control_verdict 9 (Finite_Pair narrowed_control_x (narrowed_control_length 3)) 12 \<noteq> Some False \<and>
    narrowed_control_verdict 10 (Finite_Pair (Finite_Pair narrowed_control_x narrowed_control_v)
      (narrowed_control_length 3)) 90 = Some False \<and>
    narrowed_control_verdict 10 (Finite_Pair (Finite_Pair narrowed_control_x narrowed_control_x)
      (narrowed_control_length 3)) 90 = Some True \<and>
    narrowed_search_verdict 7 (Finite_Pair narrowed_control_x (narrowed_control_length 2)) 20 60 = Some True \<and>
    narrowed_search_verdict 7 (Finite_Pair narrowed_control_x (narrowed_control_length 3)) 20 60 = Some False \<and>
    narrowed_search_verdict 9 (Finite_Pair narrowed_control_x (narrowed_control_length 1)) 20 12 = None \<and>
    narrowed_search_verdict 11 (Finite_Pair narrowed_control_x (Finite_Pair narrowed_search_y
      (narrowed_control_length 2))) 20 90 = Some True \<and>
    narrowed_search_verdict 11 (Finite_Pair narrowed_control_x (Finite_Pair narrowed_search_y
      (narrowed_control_length 3))) 20 90 = Some False \<and>
    narrowed_search_verdict 7 (Finite_Pair narrowed_control_x (narrowed_control_length 2)) 0 30 = None"
  by eval

end
