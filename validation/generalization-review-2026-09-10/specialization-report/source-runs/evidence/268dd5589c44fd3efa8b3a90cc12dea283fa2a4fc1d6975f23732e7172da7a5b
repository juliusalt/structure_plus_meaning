structure Finite_Investigation : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  type 'a fset
  val nat_of_integer : IntInf.int -> nat
  val investigation_basis :
    nat list ->
      nat list ->
        nat list ->
          (nat * (nat * nat)) list ->
            (nat * nat) list ->
              bool *
                ((nat * nat) list *
                  ((nat * (nat * nat) list) list *
                    (nat * (nat * (nat * nat) list)) list))
  val investigation_extend :
    nat list -> (nat * (nat * (nat * nat))) list -> nat list
  val investigation_repairs :
    nat list ->
      nat list ->
        nat list ->
          (nat * (nat * nat)) list ->
            (nat * nat) list ->
              nat list *
                ((nat * (nat * (nat * nat))) list *
                  ((nat * (nat * (nat * nat))) list * (nat * nat) list))
  val investigation_revision :
    nat list ->
      nat list ->
        nat list ->
          (nat * (nat * nat)) list ->
            (nat * nat) list ->
              nat list *
                (nat list *
                  ((nat * (nat * (nat * nat))) list *
                    (nat list * (nat * nat) list)))
  val investigation_inference :
    (nat * (nat * nat) list) list ->
      nat list ->
        (nat * nat) list ->
          bool *
            ((nat * nat) list *
              (nat list * (nat * ((nat * nat) list * (nat * nat))) list))
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

datatype 'a set = Set of 'a list | Coset of 'a list;

fun eq A_ a b = equal A_ a b;

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun member A_ x (Set xs) = membera A_ xs x
  | member A_ x (Coset xs) = not (membera A_ xs x);

fun less_eq_set A_ (Set xs) b = list_all (fn x => member A_ x b) xs
  | less_eq_set A_ a (Coset ys) = list_all (fn y => not (member A_ y a)) ys
  | less_eq_set A_ (Coset []) (Set []) = false;

fun equal_seta A_ a b = less_eq_set A_ a b andalso less_eq_set A_ b a;

fun equal_set A_ = {equal = equal_seta A_} : 'a set equal;

datatype 'a fset = Abs_fset of 'a set;

fun fset (Abs_fset x) = x;

fun less_eq_fset A_ xa xc = less_eq_set A_ (fset xa) (fset xc);

fun equal_fseta A_ a b = less_eq_fset A_ a b andalso less_eq_fset A_ b a;

fun equal_fset A_ = {equal = equal_fseta A_} : 'a fset equal;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

datatype num = One | Bit0 of num | Bit1 of num;

fun id x = (fn xa => xa) x;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun bex (Set xs) p = list_ex p xs;

fun ball (Set xs) p = list_all p xs;

fun fold f [] s = s
  | fold f (x :: xs) s = fold f xs (f x s);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

val zero_nat : nat = Nat (0 : IntInf.int);

fun length_tailrec [] n = n
  | length_tailrec (x :: xs) n = length_tailrec xs (suc n);

fun size_list xs = length_tailrec xs zero_nat;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun card A_ (Set xs) = size_list (remdups A_ xs);

fun fcard A_ xa = card A_ (fset xa);

fun filtera p [] = []
  | filtera p (x :: xs) = (if p x then x :: filtera p xs else filtera p xs);

fun filter p (Set xs) = Set (filtera p xs);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Set xs) = Set (inserta A_ x xs)
  | insert A_ x (Coset xs) = Coset (removeAll A_ x xs);

fun fimage xb xc = Abs_fset (image xb (fset xc));

fun sup_set A_ (Set xs) a = fold (insert A_) xs a
  | sup_set A_ (Coset xs) a = Coset (filtera (fn x => not (member A_ x a)) xs);

val bot_set : 'a set = Set [];

fun sup_seta A_ (Set xs) = fold (sup_set A_) xs bot_set;

fun ffUnion A_ xa = Abs_fset (sup_seta A_ (image fset (fset xa)));

fun ffilter xb xc = Abs_fset (filter xb (fset xc));

fun finsert A_ xb xc = Abs_fset (insert A_ xb (fset xc));

fun fset_of_list xa = Abs_fset (Set xa);

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

fun whilea b c s = (if b s then whilea b c (c s) else s);

fun max A_ a b = (if less_eq A_ a b then b else a);

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

val bot_fset : 'a fset = Abs_fset bot_set;

fun sup_fset A_ xb xc = Abs_fset (sup_set A_ (fset xb) (fset xc));

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun equal_bool false p = not p
  | equal_bool true p = p
  | equal_bool p false = not p
  | equal_bool p true = p;

fun finite_candidate_profile A_ B_ f table c =
  fimage (fn (fa, (_, a)) => (fa, a))
    (ffilter (fn (fa, (d, _)) => member A_ fa (fset f) andalso eq B_ d c)
      table);

fun finite_basis_residual A_ B_ C_ c f table relation =
  ffUnion (equal_prod A_ A_)
    (fimage
      (fn ca =>
        fimage (fn a => (ca, a))
          (ffilter
            (fn d =>
              not (equal_bool (relation ca d)
                    (less_eq_set (equal_prod B_ C_)
                      (fset (finite_candidate_profile B_ A_ f table ca))
                      (fset (finite_candidate_profile B_ A_ f table d)))))
            c))
      c);

fun stabilizing_iteration A_ n f x =
  (if equal_nata n zero_nat then x
    else let
           val next = f x;
         in
           (if eq A_ next x then x
             else stabilizing_iteration A_ (minus_nat n one_nat) f next)
         end);

fun finite_edge_compose A_ B_ C_ r s =
  ffUnion (equal_prod A_ C_)
    (fimage
      (fn (x, y) =>
        fimage (fn (_, a) => (x, a)) (ffilter (fn (u, _) => eq B_ u y) s))
      r);

fun finite_edge_closure A_ e =
  stabilizing_iteration (equal_fset (equal_prod A_ A_))
    (minus_nat (fcard (equal_prod A_ A_) e) one_nat)
    (fn r => sup_fset (equal_prod A_ A_) r (finite_edge_compose A_ A_ A_ r e))
    e;

fun finite_observation_table_formed A_ B_ c u table =
  ball (fset table)
    (fn (f, (ca, _)) => member B_ f (fset u) andalso member A_ ca (fset c));

fun finite_basis_evaluation A_ B_ C_ c u f table relation residual =
  finite_observation_table_formed A_ B_ c u table andalso
    (less_eq_set B_ (fset f) (fset u) andalso
      equal_fseta (equal_prod A_ A_) residual
        (finite_basis_residual A_ B_ C_ c f table relation));

fun finite_candidate_losses A_ B_ C_ f table c d =
  ffilter
    (fn q =>
      not (member (equal_prod A_ C_) q
            (fset (finite_candidate_profile A_ B_ f table d))))
    (finite_candidate_profile A_ B_ f table c);

fun finite_transition_keys key r = fimage (fn (k, a) => (k, key a)) r;

fun finite_reachable_outputs_from A_ B_ key r roots =
  let
    val paths = finite_edge_closure B_ (finite_transition_keys key r);
    val keys = fimage key roots;
  in
    sup_fset A_ roots
      (fimage snd
        (ffilter
          (fn (k, _) =>
            member B_ k (fset keys) orelse
              bex (fset keys)
                (fn ra => member (equal_prod B_ B_) (ra, k) (fset paths)))
          r))
  end;

fun finite_premise_functional A_ B_ h =
  ball (fset h)
    (fn (i, a) =>
      ball (fset h) (fn (j, b) => (if eq A_ i j then eq B_ a b else true)));

fun finite_inference_demand_edges A_ B_ C_ f k =
  ffUnion (equal_prod A_ C_)
    (fimage
      (fn (a, h) =>
        (if member A_ a (fset k) orelse not (finite_premise_functional B_ C_ h)
          then bot_fset else fimage (fn (_, b) => (a, b)) h))
      f);

fun finite_inference_demand A_ B_ f k a =
  finite_reachable_outputs_from A_ A_ id
    (finite_inference_demand_edges A_ B_ A_ f k) a;

fun investigation_atoms rules known goals =
  map snd goals @ known @ map fst rules @ maps (fn (_, a) => map snd a) rules;

fun investigation_select A_ xs a =
  filtera (fn x => member A_ x (fset a)) (remdups A_ xs);

fun investigation_profile selected observations c =
  investigation_select (equal_prod equal_nat equal_nat)
    (map (fn (f, (_, a)) => (f, a)) observations)
    (finite_candidate_profile equal_nat equal_nat (fset_of_list selected)
      (fset_of_list observations) c);

fun investigation_pairs candidates =
  maps (fn c => map (fn a => (c, a)) candidates) candidates;

fun investigation_basis candidates facets selected observations relation =
  let
    val c = fset_of_list candidates;
    val u = fset_of_list facets;
    val f = fset_of_list selected;
    val table = fset_of_list observations;
    val compare =
      (fn ca => fn d =>
        membera (equal_prod equal_nat equal_nat) relation (ca, d));
    val residual =
      finite_basis_residual equal_nat equal_nat equal_nat c f table compare;
  in
    (finite_basis_evaluation equal_nat equal_nat equal_nat c u f table compare
       residual,
      (investigation_select (equal_prod equal_nat equal_nat)
         (investigation_pairs candidates) residual,
        (map (fn ca => (ca, investigation_profile selected observations ca))
           candidates,
          map (fn (ca, d) =>
                (ca, (d, investigation_select (equal_prod equal_nat equal_nat)
                           (investigation_profile selected observations ca)
                           (finite_candidate_losses equal_nat equal_nat
                             equal_nat f table ca d))))
            (investigation_pairs candidates))))
  end;

fun investigation_rules rules =
  fset_of_list (map (fn (a, h) => (a, fset_of_list h)) rules);

fun finite_inference_round A_ B_ f k x =
  sup_set A_ (fset k)
    (image fst
      (filter
        (fn (_, h) =>
          finite_premise_functional B_ A_ h andalso
            less_eq_set A_ (image snd (fset h)) x)
        (fset f)));

fun investigation_extend selected repairs =
  remdups equal_nat (selected @ map (fn (_, (_, (f, _))) => f) repairs);

fun finite_sound_observation_facets A_ B_ C_ c relation u table =
  ffilter
    (fn f =>
      ball (fset c)
        (fn ca =>
          ball (fset c)
            (fn d =>
              (if relation ca d
                then less_eq_set (equal_prod B_ C_)
                       (fset (finite_candidate_profile B_ A_
                               (finsert B_ f bot_fset) table ca))
                       (fset (finite_candidate_profile B_ A_
                               (finsert B_ f bot_fset) table d))
                else true))))
    u;

fun investigation_retain candidates facets selected observations relation =
  investigation_select equal_nat selected
    (finite_sound_observation_facets equal_nat equal_nat equal_nat
      (fset_of_list candidates)
      (fn c => fn d => membera (equal_prod equal_nat equal_nat) relation (c, d))
      (fset_of_list facets) (fset_of_list observations));

fun finite_inference_formed A_ B_ f =
  ball (fset f) (fn (_, a) => finite_premise_functional B_ A_ a);

fun finite_inference_result A_ B_ f k =
  whilea
    (fn x => not (eq (equal_set A_) (finite_inference_round A_ B_ f k x) x))
    (finite_inference_round A_ B_ f k) bot_set;

fun investigation_reasons rules known demanded =
  maps (fn (a, h) =>
         (if member equal_nat a (fset demanded) andalso
               (not (membera equal_nat known a) andalso
                 finite_premise_functional equal_nat equal_nat (fset_of_list h))
           then map (fn (i, b) => (a, (h, (i, b)))) h else []))
    rules;

fun finite_available_observation_repairs A_ B_ C_ c relation u f table =
  let
    val a =
      ffilter (fn fa => not (member B_ fa (fset f)))
        (finite_sound_observation_facets A_ B_ C_ c relation u table);
  in
    ffUnion (equal_prod A_ (equal_prod A_ (equal_prod B_ C_)))
      (fimage
        (fn (ca, d) =>
          (if relation ca d then bot_fset
            else fimage (fn (fa, w) => (ca, (d, (fa, w))))
                   (finite_candidate_losses B_ A_ C_ a table ca d)))
        (finite_basis_residual A_ B_ C_ c f table relation))
  end;

fun finite_unrepairable_comparisons A_ B_ C_ c relation u table =
  finite_basis_residual A_ B_ C_ c
    (finite_sound_observation_facets A_ B_ C_ c relation u table) table
    relation;

fun finite_observation_conflicts A_ B_ C_ c relation f table =
  ffUnion (equal_prod A_ (equal_prod A_ (equal_prod B_ C_)))
    (fimage
      (fn ca =>
        ffUnion (equal_prod A_ (equal_prod A_ (equal_prod B_ C_)))
          (fimage
            (fn d =>
              (if relation ca d
                then fimage (fn (fa, w) => (ca, (d, (fa, w))))
                       (finite_candidate_losses B_ A_ C_ f table ca d)
                else bot_fset))
            c))
      c);

fun investigation_loss_rows candidates observations =
  maps (fn (c, d) => map (fn (f, (_, w)) => (c, (d, (f, w)))) observations)
    (investigation_pairs candidates);

fun investigation_repairs candidates facets selected observations relation =
  let
    val c = fset_of_list candidates;
    val u = fset_of_list facets;
    val f = fset_of_list selected;
    val table = fset_of_list observations;
    val compare =
      (fn ca => fn d =>
        membera (equal_prod equal_nat equal_nat) relation (ca, d));
    val loss_rows = investigation_loss_rows candidates observations;
  in
    (investigation_select equal_nat facets
       (finite_sound_observation_facets equal_nat equal_nat equal_nat c compare
         u table),
      (investigation_select
         (equal_prod equal_nat
           (equal_prod equal_nat (equal_prod equal_nat equal_nat)))
         loss_rows
         (finite_observation_conflicts equal_nat equal_nat equal_nat c compare f
           table),
        (investigation_select
           (equal_prod equal_nat
             (equal_prod equal_nat (equal_prod equal_nat equal_nat)))
           loss_rows
           (finite_available_observation_repairs equal_nat equal_nat equal_nat c
             compare u f table),
          investigation_select (equal_prod equal_nat equal_nat)
            (investigation_pairs candidates)
            (finite_unrepairable_comparisons equal_nat equal_nat equal_nat c
              compare u table))))
  end;

fun investigation_revision candidates facets selected observations relation =
  let
    val retained =
      investigation_retain candidates facets selected observations relation;
    val withdrawn =
      filtera (fn f => not (membera equal_nat retained f))
        (remdups equal_nat selected);
    val repairs =
      fst (snd (snd (investigation_repairs candidates facets retained
                      observations relation)));
    val revised = investigation_extend retained repairs;
    val residual =
      fst (snd (investigation_basis candidates facets revised observations
                 relation));
  in
    (retained, (withdrawn, (repairs, (revised, residual))))
  end;

fun finite_inference_residual A_ B_ C_ f k h =
  (if equal_fseta (equal_prod C_ A_) h bot_fset then bot_fset
    else let
           val settled = finite_inference_result A_ B_ f k;
         in
           ffilter (fn (_, a) => not (member A_ a settled)) h
         end);

fun investigation_inference rules known goals =
  let
    val f = investigation_rules rules;
    val k = fset_of_list known;
    val h = fset_of_list goals;
    val g = finite_inference_residual equal_nat equal_nat equal_nat f k h;
    val d = finite_inference_demand equal_nat equal_nat f k (fimage snd h);
  in
    (finite_inference_formed equal_nat equal_nat f andalso
       finite_premise_functional equal_nat equal_nat h,
      (investigation_select (equal_prod equal_nat equal_nat) goals g,
        (investigation_select equal_nat (investigation_atoms rules known goals)
           d,
          investigation_reasons rules known d)))
  end;

end; (*struct Finite_Investigation*)
