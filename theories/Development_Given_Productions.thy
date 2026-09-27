theory Development_Given_Productions
  imports Development_Given_Frames Factor_Input_Productions
begin

text \<open>
  The given's production of 12's input (I3 of correction (13) of "Committed choice, for refusals", DECISIONS.md, task
  495's entry, its first part: at the rooted readers). The given's one record (@{const given_declarations}, #782's keyed
  join) declares, beside 48's eight narrowed sockets and their production, the production of
  @{const lookup_declarations}' one socket (37, @{const lookup_socket_schema}, 2, False, @{const view_identity},
  @{const lookup_view}): I2's input registration of 12 (@{const identity_input_registration}), its class every answer.

  The record is #782's overridden at the lookup socket's key (@{const produced_override}, the keyed join over a
  produced base, stated beside #782's join in @{text Factor_Narrowed_Productions}): its socket, class and production
  there, the given's elsewhere. Each part is discharged where it was — the given's record by #782's facts, the
  socket's record by the plain discharge of the lookup socket at the rooted readers and by I2's input production —
  and the override by the two discharges.
\<close>

section \<open>The lookup socket's record and its production\<close>

text \<open>
  The record of @{const lookup_declarations}' socket alone: no producer or consumer, the one socket, its class every
  answer, its production 12's input registration.
\<close>

definition lookup_input_declarations :: "(nat,nat,nat,nat) produced_declarations" where
  "lookup_input_declarations = produced (narrowed \<lparr>declared_producers = {||}, declared_consumers = {||},
      declared_sockets = {|(37,lookup_socket_schema,2,False,view_identity,lookup_view)|}\<rparr> (\<lambda>_ _ _ _. True))
    (\<lambda>_ _ _. Some identity_input_registration)"

lemma lookup_input_fields [simp]:
  "declared_producers lookup_input_declarations = {||}"
  "declared_consumers lookup_input_declarations = {||}"
  "declared_sockets lookup_input_declarations = {|(37,lookup_socket_schema,2,False,view_identity,lookup_view)|}"
  "declared_narrowing lookup_input_declarations e S s = (\<lambda>_. True)"
  "declared_production lookup_input_declarations e S s = Some identity_input_registration"
  by (simp_all add: lookup_input_declarations_def)

lemma lookup_socket_plain:
  "(37,lookup_socket_schema,2,False,view_identity,lookup_view) |\<in>| declared_sockets given_plain_declarations"
  unfolding given_plain_declarations_records
  by (rule declarations_list_socket_member[where D=lookup_declarations])
    (simp only: list.set insert_iff simp_thms, simp add: lookup_declarations_def)

lemma lookup_input_discharged:
  "narrowed_declarations_discharged (positive_meaning given_rooted_readers_system)
    (narrowed_declarations.truncate lookup_input_declarations) given_declarations_correspondence"
proof -
  have "socket_discharged (positive_meaning given_rooted_readers_system) lookup_socket_schema 2 False view_identity
      lookup_view"
    using given_plain_declarations_discharged(2) lookup_socket_plain unfolding declarations_discharged_def by blast
  then show ?thesis
    by (simp add: narrowed_declarations_discharged_def declarations_formed_def view_identity_formed lookup_view_formed
      socket_discharged_narrowed)
qed

lemma lookup_input_frames:
  "narrowed_frames_discharged (positive_meaning given_rooted_readers_system)
    (narrowed_declarations.truncate lookup_input_declarations) lookup_frames"
  unfolding narrowed_frames_discharged_def
proof (intro allI impI)
  fix e S s C keep Vp Vh
  assume f: "(e,S,s,C) |\<in>| lookup_frames"
    and m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (narrowed_declarations.truncate lookup_input_declarations)"
  have m': "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_plain_declarations" using m lookup_socket_plain by simp
  have "socket_framed (positive_meaning given_rooted_readers_system) S s keep Vp Vh (fset C)"
    using given_frames_lookup f m' unfolding frames_discharged_def by blast
  then show "narrowed_socket_framed (positive_meaning given_rooted_readers_system) S s keep Vp Vh
      (declared_narrowing (narrowed_declarations.truncate lookup_input_declarations) e S s) (fset C)"
    by (simp add: socket_framed_narrowed)
qed

text \<open>The meaning at 12 carried to the rooted readers by I2's agreement transfer: artifact identity is reflexive there.\<close>

lemma given_rooted_identity_reflexive:
  "producer_reflexive (positive_meaning (decode_finite_system finite_rooted_given_readers)) 12 view_identity"
proof -
  note a = given_agreements[OF artifact_identity_system_formed guard_identity_agreement]
  have eq: "(12,t) \<in> positive_meaning artifact_identity_system \<longleftrightarrow> (12,t) \<in> positive_meaning given_rooted_readers_system"
    for t
    by (rule positive_meaning_shared_definitions[OF artifact_identity_system_formed given_rooted_readers_formed a(3)])
      (simp_all add: given_rooted_declared_sites)
  have "producer_reflexive (positive_meaning (decode_finite_system finite_rooted_given_readers)) 12 view_identity \<longleftrightarrow>
      producer_reflexive (positive_meaning artifact_identity_system) 12 view_identity"
    by (rule producer_reflexive_agree) (simp add: finite_rooted_given_readers_exact eq)
  then show ?thesis using artifact_identity_reflexive by simp
qed

text \<open>
  The lookup record's production is discharged at any meaning at which 12 is reflexive, at any program; at the rooted
  readers it is by @{thm [source] given_rooted_identity_reflexive}, and at the numbered and installed programs of
  @{text Development_Given_Installed_Productions} by their own reflexivity.
\<close>

lemma lookup_input_productions_at:
  assumes reflexive: "producer_reflexive M 12 view_identity"
  shows "productions_discharged M P m lookup_input_declarations"
proof (rule input_productions_discharged)
  fix e S s keep Vp Vh R
  assume sock: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets lookup_input_declarations"
    and p: "declared_production lookup_input_declarations e S s = Some R"
  have R: "R = identity_input_registration" and V: "Vp = view_identity" using sock p by simp_all
  show "(R = input_registration (registration_site R) (registration_schema R) Vp (registration_variable R) \<and>
        head_registration Vp (registration_schema R) (registration_variable R) \<and>
        producer_reflexive M (registration_site R) Vp \<and> (\<forall>x. declared_narrowing lookup_input_declarations e S s x)) \<or>
      (head_registration Vp (registration_schema R) (registration_variable R) \<and>
        head_registration_produces (finite_collection_construction [R] m) P (registration_site R) (registration_schema R)
          (registration_variable R) (declared_narrowing lookup_input_declarations e S s) \<and>
        head_registration_answers M (finite_collection_construction [R] m) P (registration_site R)
          (registration_schema R) Vp (registration_variable R))"
    unfolding R V identity_input_registration_fields(1-3)
    using identity_input_registration_head reflexive by (simp add: identity_input_registration_def)
qed

lemma lookup_input_productions:
  "productions_discharged (positive_meaning (decode_finite_system finite_rooted_given_readers))
    finite_rooted_given_readers m lookup_input_declarations"
  by (rule lookup_input_productions_at[OF given_rooted_identity_reflexive])

section \<open>The given's record with 12's input production\<close>

definition given_input_declarations :: "(nat,nat,nat,nat) produced_declarations" where
  "given_input_declarations = produced_override given_declarations lookup_input_declarations"

definition given_input_frames :: "(nat,nat,nat) resolution_frames" where
  "given_input_frames = frames_join (resolution_declarations.truncate lookup_input_declarations) given_narrowed_frames
    lookup_frames"

theorem given_input_declarations_discharged:
  "narrowed_declarations_discharged (positive_meaning given_rooted_readers_system)
    (narrowed_declarations.truncate given_input_declarations) given_declarations_correspondence"
  "declarations_discharged (positive_meaning given_rooted_readers_system)
    (unrestricted_declarations given_input_declarations) given_declarations_correspondence"
  "narrowed_productions_declared given_input_declarations"
proof -
  show d: "narrowed_declarations_discharged (positive_meaning given_rooted_readers_system)
      (narrowed_declarations.truncate given_input_declarations) given_declarations_correspondence"
    unfolding given_input_declarations_def
    by (rule produced_override_discharged[OF given_declarations_discharged(1) lookup_input_discharged])
  show "declarations_discharged (positive_meaning given_rooted_readers_system)
      (unrestricted_declarations given_input_declarations) given_declarations_correspondence"
    by (rule unrestricted_discharged[OF d])
  show "narrowed_productions_declared given_input_declarations"
    unfolding given_input_declarations_def
    by (rule produced_override_declared[OF given_declarations_discharged(3)])
      (simp add: narrowed_productions_declared_def)
qed

theorem given_input_declarations_productions:
  "productions_discharged (positive_meaning (decode_finite_system finite_rooted_given_readers))
    finite_rooted_given_readers m given_input_declarations"
  unfolding given_input_declarations_def
  by (rule produced_override_productions[OF given_declarations_productions lookup_input_productions])

theorem given_input_frames_discharged:
  "narrowed_frames_discharged (positive_meaning given_rooted_readers_system)
    (narrowed_declarations.truncate given_input_declarations) given_input_frames"
  unfolding given_input_declarations_def given_input_frames_def
  by (rule produced_override_frames[OF given_narrowed_frames_discharged lookup_input_frames])

theorem given_input_commitment_exchanges:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and only: "finite_registrations_premise_only \<kappa> finite_rooted_given_readers"
  shows "finite_commitment_exchanges (\<lambda>_. False) \<kappa>
    (finite_narrowed_commitment finite_rooted_given_readers m given_input_declarations given_input_frames)
    finite_rooted_given_readers"
proof -
  have d: "narrowed_declarations_discharged (positive_meaning (decode_finite_system finite_rooted_given_readers))
      (narrowed_declarations.truncate given_input_declarations) given_declarations_correspondence"
    using given_input_declarations_discharged(1) by (simp add: finite_rooted_given_readers_exact)
  have f: "narrowed_frames_discharged (positive_meaning (decode_finite_system finite_rooted_given_readers))
      (narrowed_declarations.truncate given_input_declarations) given_input_frames"
    using given_input_frames_discharged by (simp add: finite_rooted_given_readers_exact)
  show ?thesis
    by (rule finite_narrowed_commitment_exchanges[OF \<kappa> d f given_input_declarations_productions
      given_input_declarations_discharged(3) only])
qed

end
