theory RRA_Assembly
  imports RRA_Artifact
begin

type_synonym ('s,'a) piece_family = "('s × 'a rra_object) set"
type_synonym ('s,'a) copied = "'s × 'a"

definition family_formed :: "data_kind ⇒ ('s,'a) piece_family ⇒ bool" where
  "family_formed k P ⟷ finite P ∧
     (∀s O. (s,O)∈P ⟶ object_formed O ∧ kind_of (payload O)=k) ∧
     (∀s O O'. (s,O)∈P ∧ (s,O')∈P ⟶ O=O')"

definition copied_carrier :: "('s,'a) piece_family ⇒ ('s,'a) copied set" where
  "copied_carrier P = {(s,u) |s u O. (s,O)∈P ∧ u∈carrier (base O)}"

definition copied_incidence ::
  "('s,'a) piece_family ⇒ (('s,'a) copied × ('s,'a) copied × ('s,'a) copied) set" where
  "copied_incidence P =
     {((s,r),(s,p),(s,x)) |s r p x O. (s,O)∈P ∧ (r,p,x)∈incidence (base O)}"

definition gluing :: "('s,'a) piece_family ⇒ (('s,'a) copied × ('s,'a) copied) set ⇒ bool" where
  "gluing P E ⟷ equiv (copied_carrier P) E"

definition pushed_structure ::
  "('s,'a) piece_family ⇒ (('s,'a) copied ⇒ 'b) ⇒ 'b rra_structure" where
  "pushed_structure P q =
     ⦇carrier=q ` copied_carrier P,
      incidence=(λ(a,b,c). (q a,q b,q c)) ` copied_incidence P⦈"

fun bag_part :: "'a rra_data ⇒ ((('a × octets) × nat) set)" where
  "bag_part (Bag_Data B)=B" | "bag_part _ = {}"

fun functional_part :: "'a rra_data ⇒ ('a × octets) set" where
  "functional_part (Functional_Data F)=F" | "functional_part _ = {}"

fun node_part :: "'a rra_data ⇒ (('a × 'a) × octets) set" where
  "node_part (Node_Data N)=N" | "node_part _ = {}"

definition bag_total ::
  "('s,'a) piece_family ⇒ (('s,'a) copied ⇒ 'b) ⇒ 'b ⇒ octets ⇒ nat" where
  "bag_total P q y v =
     (∑(s,O)∈P. ∑e∈bag_part (payload O).
       case e of ((u,w),n) ⇒ if q(s,u)=y ∧ w=v then n else 0)"

definition functional_compatible ::
  "('s,'a) piece_family ⇒ (('s,'a) copied ⇒ 'b) ⇒ bool" where
  "functional_compatible P q ⟷
     (∀s O u v t O' u' w.
       (s,O)∈P ∧ (u,v)∈functional_part (payload O) ∧
       (t,O')∈P ∧ (u',w)∈functional_part (payload O') ∧
       q(s,u)=q(t,u') ⟶ v=w)"

definition node_compatible ::
  "('s,'a) piece_family ⇒ (('s,'a) copied ⇒ 'b) ⇒ bool" where
  "node_compatible P q ⟷
     (∀s O d u v t O' d' u' w.
       (s,O)∈P ∧ ((d,u),v)∈node_part (payload O) ∧
       (t,O')∈P ∧ ((d',u'),w)∈node_part (payload O') ∧
       q(s,d)=q(t,d') ⟶ q(s,u)=q(t,u') ∧ v=w)"

definition pushed_data ::
  "data_kind ⇒ ('s,'a) piece_family ⇒ (('s,'a) copied ⇒ 'b) ⇒ 'b rra_data" where
  "pushed_data k P q =
     (case k of
       No_Kind ⇒ No_Data
     | Bag_Kind ⇒ Bag_Data {((y,v),bag_total P q y v) |y v. bag_total P q y v>0}
     | Functional_Kind ⇒ Functional_Data {(q(s,u),v) |s u v O. (s,O)∈P ∧ (u,v)∈functional_part (payload O)}
     | Node_Kind ⇒ Node_Data {((q(s,d),q(s,u)),v) |s d u v O. (s,O)∈P ∧ ((d,u),v)∈node_part (payload O)})"

definition data_push_compatible ::
  "data_kind ⇒ ('s,'a) piece_family ⇒ (('s,'a) copied ⇒ 'b) ⇒ bool" where
  "data_push_compatible k P q ⟷
     (case k of Functional_Kind ⇒ functional_compatible P q
      | Node_Kind ⇒ node_compatible P q | _ ⇒ True)"

definition assembly_witness ::
  "data_kind ⇒ ('s,address) piece_family ⇒ (('s,address) copied ⇒ address) ⇒ exact_record ⇒ bool" where
  "assembly_witness k P q R ⟷
     family_formed k P ∧ record_formed R ∧
     q ` copied_carrier P = carrier (base R) ∧
     data_push_compatible k P q ∧
     base R = pushed_structure P q ∧ payload R = pushed_data k P q"

end
