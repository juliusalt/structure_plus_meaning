theory Factor_Native_Certificate_Identity_Cases
  imports Factor_Native_Certificate_Inputs
begin

definition native_certificate_identity_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "native_certificate_identity_program=(let q=Finite_Pattern_Payload [];
    leaf=finite_control_rule q {||};
    P=finite_add_view_definition (finite_nat_guard_source_model False) 1 q {|(0,leaf),(1,leaf)|};
    Q=finite_add_view_definition P 3 q {|(0,leaf),(1,leaf)|};
    R=finite_add_view_definition Q 2 q {|(0,finite_control_rule q {|(0,1,q),(1,1,q)|})|}
    in finite_add_view_definition R 4 q {|(0,finite_control_rule q {|(0,1,q),(1,3,q)|})|})"

definition native_certificate_identity_query :: "native_history_problem option" where
  "native_certificate_identity_query=native_history_compile native_certificate_identity_program
    (fimage (\<lambda>d. (d,Finite_Payload [])) (finite_system_definitions native_certificate_identity_program))"

definition native_certificate_identity_supplied :: "nat\<Rightarrow>native_certificate_input" where
  "native_certificate_identity_supplied k=(case native_certificate_identity_query of None \<Rightarrow> Native_Certificate_Query None
    | Some (E,u,r,D) \<Rightarrow> (case native_derivation_base (E,u,r,D) of None \<Rightarrow> Native_Certificate_Query None
      | Some (P,A,T) \<Rightarrow> Native_Certificate_Supplied E u r
        (if k=1 then {||} else A)
        (if k=2 then fimage (map_prod id (native_derivation_alter_root 4)) T else T)))"

definition native_certificate_identity_inputs :: "native_certificate_input list" where
  "native_certificate_identity_inputs=[Native_Certificate_Query native_certificate_identity_query,
    native_certificate_identity_supplied 0,native_certificate_identity_supplied 1,native_certificate_identity_supplied 2]"

definition native_certificate_original_inputs :: "native_certificate_input list" where
  "native_certificate_original_inputs=map (Native_Certificate_Query \<circ> native_certificate_problem) native_certificate_indices"

text \<open>
  These are proposed corrective subjects. The actual source compiler constructs
  two equal leaf definitions with two clauses each, a parent requiring one leaf
  twice, and a parent requiring the two leaf definitions. The existing proof
  constructor generates every supported child combination in its finite rounds.
  Complete native reading and certificate checking remain the judges of the
  resulting values. A supplied copy and two changes separately exercise missing
  positive-call coverage and malformed certificates. No coverage verdict is
  supplied by this construction; native scope comparison must compute it.
\<close>

end
