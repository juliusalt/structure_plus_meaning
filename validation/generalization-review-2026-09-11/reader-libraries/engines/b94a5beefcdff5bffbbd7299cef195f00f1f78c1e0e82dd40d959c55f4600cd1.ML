structure Native_Reasoning : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  type 'a equal
  type num
  type 'a one
  type 'a zero
  type 'a numeral
  datatype 'a set = Set of 'a list | Coset of 'a list
  type 'a fset
  val fset : 'a fset -> 'a set
  type ('a, 'b) finite_rra_structure_ext
  type 'a multiset
  type ('a, 'b, 'c) finite_opaque_basis_ext
  type ('a, 'b, 'c) finite_structured_object_ext
  datatype finite_exact_target =
    Finite_Whole of ((nat list), (nat list), unit) finite_structured_object_ext
    | Finite_Anchor of
        ((nat list), (nat list), unit) finite_structured_object_ext * nat list
  datatype finite_factor_term = Finite_Target of finite_exact_target |
    Finite_Payload of nat list |
    Finite_Pair of finite_factor_term * finite_factor_term
  datatype 'a finite_term_pattern = Finite_Variable of 'a |
    Finite_Pattern_Target of finite_exact_target |
    Finite_Pattern_Payload of nat list |
    Finite_Pattern_Pair of 'a finite_term_pattern * 'a finite_term_pattern
  type ('a, 'b) finite_material_pattern_ext
  type ('a, 'b, 'c, 'd) finite_factor_schema_ext
  datatype admission_goal = Existing_Admission of nat |
    Paired_Admission of admission_goal * admission_goal |
    Collected_Admission of admission_goal
  datatype admission_instruction = Pair_Admission_Instruction of nat * nat * nat
    | List_Admission_Instruction of nat * nat
  val fset_of_list : 'a list -> 'a fset
  val nat_of_integer : IntInf.int -> nat
  val admission_plan :
    admission_goal -> nat -> nat * (nat * admission_instruction list)
  val finite_empty_artifact :
    ((nat list), (nat list), unit) finite_structured_object_ext
  val finite_schema_conclusion :
    ('a, 'b, 'c, 'd) finite_factor_schema_ext -> 'a finite_term_pattern
  val finite_schema_materials :
    ('a, 'b, 'c, 'd) finite_factor_schema_ext ->
      ('b * ('a, unit) finite_material_pattern_ext) fset
  val finite_schema_premises :
    ('a, 'b, 'c, 'd) finite_factor_schema_ext ->
      ('b * ('c * 'a finite_term_pattern)) fset
  val finite_material_functions :
    ('a, 'b) finite_material_pattern_ext -> 'a finite_term_pattern
  val finite_material_source :
    ('a, 'b) finite_material_pattern_ext -> 'a finite_term_pattern
  val finite_material_counts :
    ('a, 'b) finite_material_pattern_ext -> 'a finite_term_pattern
  val finite_material_edges :
    ('a, 'b) finite_material_pattern_ext -> 'a finite_term_pattern
  val finite_material_atoms :
    ('a, 'b) finite_material_pattern_ext -> 'a finite_term_pattern
  val natural_library_coverage :
    (nat *
      ((nat, nat, nat, unit) finite_factor_schema_ext *
        (nat * (nat * nat finite_term_pattern)) list)) list ->
      (nat * finite_factor_term) fset ->
        (nat * (nat * finite_factor_term)) fset ->
          bool *
            ((nat * (nat * nat) fset) fset *
              ((nat * (nat * finite_factor_term)) fset *
                (nat fset * (nat * ((nat * nat) fset * (nat * nat))) fset)))
  val make :
    'a finite_term_pattern ->
      ('b * ('c * 'a finite_term_pattern)) fset ->
        ('b * ('a, unit) finite_material_pattern_ext) fset ->
          ('a, 'b, 'c, unit) finite_factor_schema_ext
  val specialization_report_reasoning_library :
    (nat *
      ((nat, nat, nat, unit) finite_factor_schema_ext *
        (nat * (nat * nat finite_term_pattern)) list)) list
  val binding_list_construction_library :
    'a one * 'a zero -> 'b numeral -> 'c zero * 'c numeral ->
      (nat *
        ((nat, nat, nat, unit) finite_factor_schema_ext *
          ('a * ('b * 'c finite_term_pattern)) list)) list
  val binding_observation_reasoning_library :
    (nat *
      ((nat, nat, nat, unit) finite_factor_schema_ext *
        (nat * (nat * nat finite_term_pattern)) list)) list
  val reader_library_coverage :
    (nat * finite_factor_term) fset ->
      (nat * (nat * finite_factor_term)) fset ->
        bool *
          ((nat * (nat * nat) fset) fset *
            ((nat * (nat * finite_factor_term)) fset *
              (nat fset * (nat * ((nat * nat) fset * (nat * nat))) fset)))
  val finite_reasoning_term_equal :
    finite_factor_term -> finite_factor_term -> bool
  val makea :
    'a finite_term_pattern ->
      'a finite_term_pattern ->
        'a finite_term_pattern ->
          'a finite_term_pattern ->
            'a finite_term_pattern -> ('a, unit) finite_material_pattern_ext
  val finite_generated_schema_applications :
    'a equal -> 'b equal -> 'c equal -> 'd equal ->
      ('a * (('b, 'c, 'd, unit) finite_factor_schema_ext *
              ('c * ('d * 'b finite_term_pattern)) list)) list ->
        ('d * finite_factor_term) list ->
          ('a * (('b, 'c, 'd, unit) finite_factor_schema_ext *
                  (finite_factor_term *
                    (('b * finite_factor_term) fset *
                      ('c * ('d * finite_factor_term)) fset))))
            fset
  val finite_generated_schema_rules :
    'a equal -> 'b equal -> 'c equal -> 'd equal ->
      ('a * (('b, 'c, 'd, unit) finite_factor_schema_ext *
              ('c * ('d * 'b finite_term_pattern)) list)) list ->
        ('d * finite_factor_term) list ->
          (('a * finite_factor_term) * ('c * ('d * finite_factor_term)) fset)
            fset
  val finite_learned_investigation :
    'a equal -> 'b equal -> 'c equal -> 'd equal ->
      ('a * (('b, 'c, 'a, unit) finite_factor_schema_ext *
              ('c * ('a * 'b finite_term_pattern)) list)) list ->
        ('a * finite_factor_term) list ->
          ('a * finite_factor_term) fset ->
            ('d * ('a * finite_factor_term)) fset ->
              bool *
                (('a * (('b, 'c, 'a, unit) finite_factor_schema_ext *
                         (finite_factor_term *
                           (('b * finite_factor_term) fset *
                             ('c * ('a * finite_factor_term)) fset))))
                   fset *
                  (('d * ('a * finite_factor_term)) fset *
                    (('a * finite_factor_term) fset *
                      (('a * finite_factor_term) *
                        (('c * ('a * finite_factor_term)) fset *
                          ('c * ('a * finite_factor_term))))
                        fset)))
  val natural_chained_investigation :
    nat ->
      (nat *
        ((nat, nat, nat, unit) finite_factor_schema_ext *
          (nat * (nat * nat finite_term_pattern)) list)) list ->
        (nat * finite_factor_term) list ->
          (nat * finite_factor_term) fset ->
            (nat * (nat * finite_factor_term)) fset ->
              bool *
                ((nat *
                   ((nat, nat, nat, unit) finite_factor_schema_ext *
                     (finite_factor_term *
                       ((nat * finite_factor_term) fset *
                         (nat * (nat * finite_factor_term)) fset))))
                   fset *
                  ((nat * (nat * finite_factor_term)) fset *
                    ((nat * finite_factor_term) fset *
                      ((nat * finite_factor_term) *
                        ((nat * (nat * finite_factor_term)) fset *
                          (nat * (nat * finite_factor_term))))
                        fset)))
  val natural_construction_frontier :
    nat ->
      (nat *
        ((nat, nat, nat, unit) finite_factor_schema_ext *
          (nat * (nat * nat finite_term_pattern)) list)) list ->
        (nat * finite_factor_term) fset -> (nat * finite_factor_term) fset
  val natural_learned_investigation :
    (nat *
      ((nat, nat, nat, unit) finite_factor_schema_ext *
        (nat * (nat * nat finite_term_pattern)) list)) list ->
      (nat * finite_factor_term) list ->
        (nat * finite_factor_term) fset ->
          (nat * (nat * finite_factor_term)) fset ->
            bool *
              ((nat *
                 ((nat, nat, nat, unit) finite_factor_schema_ext *
                   (finite_factor_term *
                     ((nat * finite_factor_term) fset *
                       (nat * (nat * finite_factor_term)) fset))))
                 fset *
                ((nat * (nat * finite_factor_term)) fset *
                  ((nat * finite_factor_term) fset *
                    ((nat * finite_factor_term) *
                      ((nat * (nat * finite_factor_term)) fset *
                        (nat * (nat * finite_factor_term))))
                      fset)))
  val finite_binding_observation_frontier :
    finite_factor_term ->
      finite_factor_term list -> (nat * finite_factor_term) list
  val finite_admission_counter_check : finite_factor_term -> bool
  val admitted_reasoning_frontier :
    (nat * finite_factor_term) list -> (nat * finite_factor_term) list
  val admission_pair_reasoning_experiment :
    nat ->
      bool *
        ((nat *
           ((nat, nat, nat, unit) finite_factor_schema_ext *
             (finite_factor_term *
               ((nat * finite_factor_term) fset *
                 (nat * (nat * finite_factor_term)) fset))))
           fset *
          ((nat * (nat * finite_factor_term)) fset *
            ((nat * finite_factor_term) fset *
              ((nat * finite_factor_term) *
                ((nat * (nat * finite_factor_term)) fset *
                  (nat * (nat * finite_factor_term))))
                fset)))
  val finite_binding_list_seed :
    finite_factor_term -> finite_factor_term -> (nat * finite_factor_term) list
  val binding_observation_investigation :
    bool ->
      (finite_factor_term * finite_factor_term list) list ->
        (nat * (nat * finite_factor_term)) fset ->
          bool *
            ((nat *
               ((nat, nat, nat, unit) finite_factor_schema_ext *
                 (finite_factor_term *
                   ((nat * finite_factor_term) fset *
                     (nat * (nat * finite_factor_term)) fset))))
               fset *
              ((nat * (nat * finite_factor_term)) fset *
                ((nat * finite_factor_term) fset *
                  ((nat * finite_factor_term) *
                    ((nat * (nat * finite_factor_term)) fset *
                      (nat * (nat * finite_factor_term))))
                    fset)))
  val reasoning_counterexample_experiment :
    bool ->
      bool *
        ((nat *
           ((nat, nat, nat, unit) finite_factor_schema_ext *
             (finite_factor_term *
               ((nat * finite_factor_term) fset *
                 (nat * (nat * finite_factor_term)) fset))))
           fset *
          ((nat * (nat * finite_factor_term)) fset *
            ((nat * finite_factor_term) fset *
              ((nat * finite_factor_term) *
                ((nat * (nat * finite_factor_term)) fset *
                  (nat * (nat * finite_factor_term))))
                fset)))
  val finite_binding_observation_outputs :
    finite_factor_term ->
      finite_factor_term list ->
        (finite_factor_term list * finite_factor_term list) option
  val generated_input_execution :
    nat -> bool * ((nat * (nat * admission_instruction list)) * bool list)
  val specialization_report_investigation :
    (nat * finite_factor_term) list ->
      (nat * finite_factor_term) fset ->
        (nat * (nat * finite_factor_term)) fset ->
          bool *
            ((nat *
               ((nat, nat, nat, unit) finite_factor_schema_ext *
                 (finite_factor_term *
                   ((nat * finite_factor_term) fset *
                     (nat * (nat * finite_factor_term)) fset))))
               fset *
              ((nat * (nat * finite_factor_term)) fset *
                ((nat * finite_factor_term) fset *
                  ((nat * finite_factor_term) *
                    ((nat * (nat * finite_factor_term)) fset *
                      (nat * (nat * finite_factor_term))))
                    fset)))
  val binding_list_construction_investigation :
    nat ->
      bool ->
        bool ->
          finite_factor_term ->
            finite_factor_term ->
              (nat * (nat * finite_factor_term)) fset ->
                bool *
                  ((nat *
                     ((nat, nat, nat, unit) finite_factor_schema_ext *
                       (finite_factor_term *
                         ((nat * finite_factor_term) fset *
                           (nat * (nat * finite_factor_term)) fset))))
                     fset *
                    ((nat * (nat * finite_factor_term)) fset *
                      ((nat * finite_factor_term) fset *
                        ((nat * finite_factor_term) *
                          ((nat * (nat * finite_factor_term)) fset *
                            (nat * (nat * finite_factor_term))))
                          fset)))
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

datatype num = One | Bit0 of num | Bit1 of num;

val one_nata : nat = Nat (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

fun plus_nata m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nata : nat = Nat (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = zero_nata} : nat zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val numeral_nat =
  {one_numeral = one_nat, semigroup_add_numeral = semigroup_add_nat} :
  nat numeral;

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

fun equal_boola false p = not p
  | equal_boola true p = p
  | equal_boola p false = not p
  | equal_boola p true = p;

val equal_bool = {equal = equal_boola} : bool equal;

datatype 'a fset = Abs_fset of 'a set;

fun fset (Abs_fset x) = x;

fun less_eq_fset A_ xa xc = less_eq_set A_ (fset xa) (fset xc);

fun equal_fseta A_ a b = less_eq_fset A_ a b andalso less_eq_fset A_ b a;

fun equal_fset A_ = {equal = equal_fseta A_} : 'a fset equal;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun equal_unita u v = true;

val equal_unit = {equal = equal_unita} : unit equal;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

datatype ('a, 'b) finite_rra_structure_ext =
  Finite_rra_structure_ext of 'a fset * ('a * ('a * 'a)) fset * 'b;

fun equal_finite_rra_structure_ext A_ B_
  (Finite_rra_structure_ext (finite_carriera, finite_incidencea, morea))
  (Finite_rra_structure_ext (finite_carrier, finite_incidence, more)) =
  eq (equal_fset A_) finite_carriera finite_carrier andalso
    (equal_fseta (equal_prod A_ (equal_prod A_ A_)) finite_incidencea
       finite_incidence andalso
      eq B_ morea more);

datatype 'a multiset = Mset of 'a list;

datatype ('a, 'b, 'c) finite_opaque_basis_ext =
  Finite_opaque_basis_ext of ('a * 'b) multiset * ('a * 'b) fset * 'c;

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun extract p [] = NONE
  | extract p (x :: xs) =
    (if p x then SOME ([], (x, xs))
      else (case extract p xs of NONE => NONE
             | SOME (ys, (y, zs)) => SOME (x :: ys, (y, zs))));

fun null [] = true
  | null (x :: xs) = false;

fun subset_eq_mset_impl A_ [] ys = SOME (not (null ys))
  | subset_eq_mset_impl A_ (x :: xs) ys =
    (case extract (eq A_ x) ys of NONE => NONE
      | SOME (ys1, (_, ys2)) => subset_eq_mset_impl A_ xs (ys1 @ ys2));

fun equal_multiset A_ (Mset xs) (Mset ys) =
  equal_option equal_bool (subset_eq_mset_impl A_ xs ys) (SOME false);

fun equal_finite_opaque_basis_ext A_ B_ C_
  (Finite_opaque_basis_ext (finite_baga, finite_bindingsa, morea))
  (Finite_opaque_basis_ext (finite_bag, finite_bindings, more)) =
  equal_multiset (equal_prod A_ B_) finite_baga finite_bag andalso
    (equal_fseta (equal_prod A_ B_) finite_bindingsa finite_bindings andalso
      eq C_ morea more);

datatype ('a, 'b, 'c) finite_structured_object_ext =
  Finite_structured_object_ext of
    ('a, unit) finite_rra_structure_ext *
      ('a, 'b, unit) finite_opaque_basis_ext * 'c;

fun equal_finite_structured_object_ext A_ B_ C_
  (Finite_structured_object_ext (finite_structurea, finite_dataa, morea))
  (Finite_structured_object_ext (finite_structure, finite_data, more)) =
  equal_finite_rra_structure_ext A_ equal_unit finite_structurea
    finite_structure andalso
    (equal_finite_opaque_basis_ext A_ B_ equal_unit finite_dataa
       finite_data andalso
      eq C_ morea more);

datatype finite_exact_target =
  Finite_Whole of ((nat list), (nat list), unit) finite_structured_object_ext |
  Finite_Anchor of
    ((nat list), (nat list), unit) finite_structured_object_ext * nat list;

fun equal_finite_exact_target (Finite_Whole x1) (Finite_Anchor (x21, x22)) =
  false
  | equal_finite_exact_target (Finite_Anchor (x21, x22)) (Finite_Whole x1) =
    false
  | equal_finite_exact_target (Finite_Anchor (x21, x22))
    (Finite_Anchor (y21, y22)) =
    equal_finite_structured_object_ext (equal_list equal_nat)
      (equal_list equal_nat) equal_unit x21 y21 andalso
      equal_lista equal_nat x22 y22
  | equal_finite_exact_target (Finite_Whole x1) (Finite_Whole y1) =
    equal_finite_structured_object_ext (equal_list equal_nat)
      (equal_list equal_nat) equal_unit x1 y1;

datatype finite_factor_term = Finite_Target of finite_exact_target |
  Finite_Payload of nat list |
  Finite_Pair of finite_factor_term * finite_factor_term;

fun equal_finite_factor_terma (Finite_Payload x2) (Finite_Pair (x31, x32)) =
  false
  | equal_finite_factor_terma (Finite_Pair (x31, x32)) (Finite_Payload x2) =
    false
  | equal_finite_factor_terma (Finite_Target x1) (Finite_Pair (x31, x32)) =
    false
  | equal_finite_factor_terma (Finite_Pair (x31, x32)) (Finite_Target x1) =
    false
  | equal_finite_factor_terma (Finite_Target x1) (Finite_Payload x2) = false
  | equal_finite_factor_terma (Finite_Payload x2) (Finite_Target x1) = false
  | equal_finite_factor_terma (Finite_Pair (x31, x32)) (Finite_Pair (y31, y32))
    = equal_finite_factor_terma x31 y31 andalso
        equal_finite_factor_terma x32 y32
  | equal_finite_factor_terma (Finite_Payload x2) (Finite_Payload y2) =
    equal_lista equal_nat x2 y2
  | equal_finite_factor_terma (Finite_Target x1) (Finite_Target y1) =
    equal_finite_exact_target x1 y1;

val equal_finite_factor_term = {equal = equal_finite_factor_terma} :
  finite_factor_term equal;

datatype 'a finite_term_pattern = Finite_Variable of 'a |
  Finite_Pattern_Target of finite_exact_target |
  Finite_Pattern_Payload of nat list |
  Finite_Pattern_Pair of 'a finite_term_pattern * 'a finite_term_pattern;

fun equal_finite_term_patterna A_ (Finite_Pattern_Payload x3)
  (Finite_Pattern_Pair (x41, x42)) = false
  | equal_finite_term_patterna A_ (Finite_Pattern_Pair (x41, x42))
    (Finite_Pattern_Payload x3) = false
  | equal_finite_term_patterna A_ (Finite_Pattern_Target x2)
    (Finite_Pattern_Pair (x41, x42)) = false
  | equal_finite_term_patterna A_ (Finite_Pattern_Pair (x41, x42))
    (Finite_Pattern_Target x2) = false
  | equal_finite_term_patterna A_ (Finite_Pattern_Target x2)
    (Finite_Pattern_Payload x3) = false
  | equal_finite_term_patterna A_ (Finite_Pattern_Payload x3)
    (Finite_Pattern_Target x2) = false
  | equal_finite_term_patterna A_ (Finite_Variable x1)
    (Finite_Pattern_Pair (x41, x42)) = false
  | equal_finite_term_patterna A_ (Finite_Pattern_Pair (x41, x42))
    (Finite_Variable x1) = false
  | equal_finite_term_patterna A_ (Finite_Variable x1)
    (Finite_Pattern_Payload x3) = false
  | equal_finite_term_patterna A_ (Finite_Pattern_Payload x3)
    (Finite_Variable x1) = false
  | equal_finite_term_patterna A_ (Finite_Variable x1)
    (Finite_Pattern_Target x2) = false
  | equal_finite_term_patterna A_ (Finite_Pattern_Target x2)
    (Finite_Variable x1) = false
  | equal_finite_term_patterna A_ (Finite_Pattern_Pair (x41, x42))
    (Finite_Pattern_Pair (y41, y42)) =
    equal_finite_term_patterna A_ x41 y41 andalso
      equal_finite_term_patterna A_ x42 y42
  | equal_finite_term_patterna A_ (Finite_Pattern_Payload x3)
    (Finite_Pattern_Payload y3) = equal_lista equal_nat x3 y3
  | equal_finite_term_patterna A_ (Finite_Pattern_Target x2)
    (Finite_Pattern_Target y2) = equal_finite_exact_target x2 y2
  | equal_finite_term_patterna A_ (Finite_Variable x1) (Finite_Variable y1) =
    eq A_ x1 y1;

fun equal_finite_term_pattern A_ = {equal = equal_finite_term_patterna A_} :
  'a finite_term_pattern equal;

datatype ('a, 'b) finite_material_pattern_ext =
  Finite_material_pattern_ext of
    'a finite_term_pattern * 'a finite_term_pattern * 'a finite_term_pattern *
      'a finite_term_pattern * 'a finite_term_pattern * 'b;

datatype ('a, 'b, 'c, 'd) finite_factor_schema_ext =
  Finite_factor_schema_ext of
    'a finite_term_pattern * ('b * ('c * 'a finite_term_pattern)) fset *
      ('b * ('a, unit) finite_material_pattern_ext) fset * 'd;

fun equal_finite_material_pattern_exta A_ B_
  (Finite_material_pattern_ext
    (finite_material_sourcea, finite_material_atomsa, finite_material_edgesa,
      finite_material_countsa, finite_material_functionsa, morea))
  (Finite_material_pattern_ext
    (finite_material_source, finite_material_atoms, finite_material_edges,
      finite_material_counts, finite_material_functions, more))
  = equal_finite_term_patterna A_ finite_material_sourcea
      finite_material_source andalso
      (equal_finite_term_patterna A_ finite_material_atomsa
         finite_material_atoms andalso
        (equal_finite_term_patterna A_ finite_material_edgesa
           finite_material_edges andalso
          (equal_finite_term_patterna A_ finite_material_countsa
             finite_material_counts andalso
            (equal_finite_term_patterna A_ finite_material_functionsa
               finite_material_functions andalso
              eq B_ morea more))));

fun equal_finite_material_pattern_ext A_ B_ =
  {equal = equal_finite_material_pattern_exta A_ B_} :
  ('a, 'b) finite_material_pattern_ext equal;

fun equal_finite_factor_schema_exta A_ B_ C_ D_
  (Finite_factor_schema_ext
    (finite_schema_conclusiona, finite_schema_premisesa,
      finite_schema_materialsa, morea))
  (Finite_factor_schema_ext
    (finite_schema_conclusion, finite_schema_premises, finite_schema_materials,
      more))
  = equal_finite_term_patterna A_ finite_schema_conclusiona
      finite_schema_conclusion andalso
      (equal_fseta
         (equal_prod B_ (equal_prod C_ (equal_finite_term_pattern A_)))
         finite_schema_premisesa finite_schema_premises andalso
        (equal_fseta
           (equal_prod B_ (equal_finite_material_pattern_ext A_ equal_unit))
           finite_schema_materialsa finite_schema_materials andalso
          eq D_ morea more));

fun equal_finite_factor_schema_ext A_ B_ C_ D_ =
  {equal = equal_finite_factor_schema_exta A_ B_ C_ D_} :
  ('a, 'b, 'c, 'd) finite_factor_schema_ext equal;

datatype admission_goal = Existing_Admission of nat |
  Paired_Admission of admission_goal * admission_goal |
  Collected_Admission of admission_goal;

datatype admission_instruction = Pair_Admission_Instruction of nat * nat * nat |
  List_Admission_Instruction of nat * nat;

fun id x = (fn xa => xa) x;

fun suc n = plus_nata n one_nata;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun bex (Set xs) p = list_ex p xs;

fun ball (Set xs) p = list_all p xs;

fun fold f [] s = s
  | fold f (x :: xs) s = fold f xs (f x s);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun take n [] = []
  | take n (x :: xs) =
    (if equal_nata n zero_nata then []
      else x :: take (minus_nat n one_nata) xs);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun length_tailrec [] n = n
  | length_tailrec (x :: xs) n = length_tailrec xs (suc n);

fun size_list xs = length_tailrec xs zero_nata;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun card A_ (Set xs) = size_list (remdups A_ xs);

fun fcard A_ xa = card A_ (fset xa);

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun filtera p [] = []
  | filtera p (x :: xs) = (if p x then x :: filtera p xs else filtera p xs);

fun filter p (Set xs) = Set (filtera p xs);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Set xs) = Set (inserta A_ x xs)
  | insert A_ x (Coset xs) = Coset (removeAll A_ x xs);

fun remove A_ x (Set xs) = Set (removeAll A_ x xs)
  | remove A_ x (Coset xs) = Coset (inserta A_ x xs);

fun fimage xb xc = Abs_fset (image xb (fset xc));

fun sup_set A_ (Set xs) a = fold (insert A_) xs a
  | sup_set A_ (Coset xs) a = Coset (filtera (fn x => not (member A_ x a)) xs);

val bot_set : 'a set = Set [];

fun sup_seta A_ (Set xs) = fold (sup_set A_) xs bot_set;

fun ffUnion A_ xa = Abs_fset (sup_seta A_ (image fset (fset xa)));

fun ffilter xb xc = Abs_fset (filter xb (fset xc));

fun finsert A_ xb xc = Abs_fset (insert A_ xb (fset xc));

fun distinct A_ [] = true
  | distinct A_ (x :: xs) = not (membera A_ xs x) andalso distinct A_ xs;

fun is_none NONE = true
  | is_none (SOME x) = false;

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun fset_of_list xa = Abs_fset (Set xa);

fun set_mset (Mset xs) = Set xs;

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun octets_formed xs =
  list_all (fn x => less_nat x (nat_of_integer (256 : IntInf.int))) xs;

fun whilea b c s = (if b s then whilea b c (c s) else s);

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun inf_set A_ a (Set xs) = Set (filtera (fn x => member A_ x a) xs)
  | inf_set A_ a (Coset xs) = fold (remove A_) xs a;

fun numeral A_ One = one (one_numeral A_)
  | numeral A_ (Bit0 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m
    end
  | numeral A_ (Bit1 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_)
        (plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m)
        (one (one_numeral A_))
    end;

val bot_fset : 'a fset = Abs_fset bot_set;

fun inf_fset A_ xb xc = Abs_fset (inf_set A_ (fset xb) (fset xc));

fun sup_fset A_ xb xc = Abs_fset (sup_set A_ (fset xb) (fset xc));

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun admission_plan (Existing_Admission d) n = (d, (n, []))
  | admission_plan (Paired_Admission (g, h)) n =
    let
      val (a, (m, is)) = admission_plan g n;
      val (b, (k, js)) = admission_plan h m;
    in
      (k, (suc k, is @ js @ [Pair_Admission_Instruction (k, a, b)]))
    end
  | admission_plan (Collected_Admission g) n =
    let
      val (a, (m, is)) = admission_plan g n;
    in
      (m, (suc m, is @ [List_Admission_Instruction (m, a)]))
    end;

fun finite_bindings
  (Finite_opaque_basis_ext (finite_bag, finite_bindings, more)) =
  finite_bindings;

fun finite_bag (Finite_opaque_basis_ext (finite_bag, finite_bindings, more)) =
  finite_bag;

fun finite_relation_functional A_ B_ f =
  ball (fset f)
    (fn x =>
      ball (fset f)
        (fn y =>
          (if eq A_ (fst x) (fst y) then eq B_ (snd x) (snd y) else true)));

fun finite_basis_formed A_ B_ u d =
  finite_relation_functional A_ B_ (finite_bindings d) andalso
    (ball (set_mset (finite_bag d)) (fn x => member A_ (fst x) (fset u)) andalso
      ball (fset (finite_bindings d)) (fn x => member A_ (fst x) (fset u)));

fun finite_structure
  (Finite_structured_object_ext (finite_structure, finite_data, more)) =
  finite_structure;

fun finite_data
  (Finite_structured_object_ext (finite_structure, finite_data, more)) =
  finite_data;

fun finite_carrier
  (Finite_rra_structure_ext (finite_carrier, finite_incidence, more)) =
  finite_carrier;

fun finite_incidence
  (Finite_rra_structure_ext (finite_carrier, finite_incidence, more)) =
  finite_incidence;

fun finite_structure_formed A_ s =
  ball (fset (finite_incidence s))
    (fn (r, (p, x)) =>
      member A_ r (fset (finite_carrier s)) andalso
        (member A_ p (fset (finite_carrier s)) andalso
          member A_ x (fset (finite_carrier s))));

fun finite_object_formed A_ B_ c =
  finite_structure_formed A_ (finite_structure c) andalso
    finite_basis_formed A_ B_ (finite_carrier (finite_structure c))
      (finite_data c);

fun finite_exact_formed c =
  finite_object_formed (equal_list equal_nat) (equal_list equal_nat) c andalso
    (ball (fset (finite_carrier (finite_structure c))) octets_formed andalso
      (ball (set_mset (finite_bag (finite_data c)))
         (fn x => octets_formed (snd x)) andalso
        ball (fset (finite_bindings (finite_data c)))
          (fn x => octets_formed (snd x))));

val zero_multiset : 'a multiset = Mset [];

fun finite_target_formed (Finite_Whole c) = finite_exact_formed c
  | finite_target_formed (Finite_Anchor (c, a)) =
    finite_exact_formed c andalso
      member (equal_list equal_nat) a
        (fset (finite_carrier (finite_structure c)));

fun finite_term_formed (Finite_Target t) = finite_target_formed t
  | finite_term_formed (Finite_Payload v) = octets_formed v
  | finite_term_formed (Finite_Pair (x, y)) =
    finite_term_formed x andalso finite_term_formed y;

val finite_empty_artifact :
  ((nat list), (nat list), unit) finite_structured_object_ext
  = Finite_structured_object_ext
      (Finite_rra_structure_ext (bot_fset, bot_fset, ()),
        Finite_opaque_basis_ext (zero_multiset, bot_fset, ()), ());

fun finite_occurrence_read c (Finite_Target t) =
  (case t of Finite_Whole _ => NONE
    | Finite_Anchor (d, a) =>
      (if equal_finite_structured_object_ext (equal_list equal_nat)
            (equal_list equal_nat) equal_unit c d
        then SOME a else NONE))
  | finite_occurrence_read c (Finite_Payload v) = NONE
  | finite_occurrence_read c (Finite_Pair (x, y)) = NONE;

fun finite_atom_read c (Finite_Pair (Finite_Payload a, x)) =
  (if equal_option (equal_list equal_nat) (finite_occurrence_read c x) (SOME a)
    then SOME a else NONE)
  | finite_atom_read c (Finite_Target v) = NONE
  | finite_atom_read c (Finite_Payload v) = NONE
  | finite_atom_read c (Finite_Pair (Finite_Target vb, va)) = NONE
  | finite_atom_read c (Finite_Pair (Finite_Pair (vb, vc), va)) = NONE;

fun stabilizing_iteration A_ n f x =
  (if equal_nata n zero_nata then x
    else let
           val next = f x;
         in
           (if eq A_ next x then x
             else stabilizing_iteration A_ (minus_nat n one_nata) f next)
         end);

fun finite_edge_compose A_ B_ C_ r s =
  ffUnion (equal_prod A_ C_)
    (fimage
      (fn (x, y) =>
        fimage (fn (_, a) => (x, a)) (ffilter (fn (u, _) => eq B_ u y) s))
      r);

fun finite_edge_closure A_ e =
  stabilizing_iteration (equal_fset (equal_prod A_ A_))
    (minus_nat (fcard (equal_prod A_ A_) e) one_nata)
    (fn r => sup_fset (equal_prod A_ A_) r (finite_edge_compose A_ A_ A_ r e))
    e;

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

fun finite_pattern_formed (Finite_Variable a) = true
  | finite_pattern_formed (Finite_Pattern_Target t) = finite_target_formed t
  | finite_pattern_formed (Finite_Pattern_Payload v) = octets_formed v
  | finite_pattern_formed (Finite_Pattern_Pair (p, q)) =
    finite_pattern_formed p andalso finite_pattern_formed q;

fun finite_matching_bindings A_ (Finite_Variable a) t =
  finsert (equal_prod A_ equal_finite_factor_term) (a, t) bot_fset
  | finite_matching_bindings A_ (Finite_Pattern_Target x) t = bot_fset
  | finite_matching_bindings A_ (Finite_Pattern_Payload v) t = bot_fset
  | finite_matching_bindings A_ (Finite_Pattern_Pair (p, q)) t =
    (case t of Finite_Target _ => bot_fset | Finite_Payload _ => bot_fset
      | Finite_Pair (x, y) =>
        sup_fset (equal_prod A_ equal_finite_factor_term)
          (finite_matching_bindings A_ p x) (finite_matching_bindings A_ q y));

fun finite_term_bindings_formed A_ b v =
  finite_relation_functional A_ equal_finite_factor_term v andalso
    (eq (equal_fset A_) (fimage fst v) b andalso
      ball (fset v) (fn (_, a) => finite_term_formed a));

fun finite_pattern_variables A_ (Finite_Variable a) = finsert A_ a bot_fset
  | finite_pattern_variables A_ (Finite_Pattern_Target t) = bot_fset
  | finite_pattern_variables A_ (Finite_Pattern_Payload v) = bot_fset
  | finite_pattern_variables A_ (Finite_Pattern_Pair (p, q)) =
    sup_fset A_ (finite_pattern_variables A_ p) (finite_pattern_variables A_ q);

fun finite_pattern_instance A_ v (Finite_Variable a) t =
  member (equal_prod A_ equal_finite_factor_term) (a, t) (fset v)
  | finite_pattern_instance A_ v (Finite_Pattern_Target x) t =
    finite_target_formed x andalso equal_finite_factor_terma t (Finite_Target x)
  | finite_pattern_instance A_ va (Finite_Pattern_Payload v) t =
    octets_formed v andalso equal_finite_factor_terma t (Finite_Payload v)
  | finite_pattern_instance A_ v (Finite_Pattern_Pair (p, q)) t =
    (case t of Finite_Target _ => false | Finite_Payload _ => false
      | Finite_Pair (x, y) =>
        finite_pattern_instance A_ v p x andalso
          finite_pattern_instance A_ v q y);

fun finite_pattern_accepts A_ p t =
  finite_term_formed t andalso
    (finite_term_bindings_formed A_ (finite_pattern_variables A_ p)
       (finite_matching_bindings A_ p t) andalso
      finite_pattern_instance A_ (finite_matching_bindings A_ p t) p t);

fun finite_premise_joins A_ B_ C_ [] k = [(bot_fset, bot_fset)]
  | finite_premise_joins A_ B_ C_ ((s, (d, p)) :: ps) k =
    maps (fn (v, h) =>
           map_filter
             (fn x =>
               (if let
                     val (e, t) = x;
                   in
                     eq B_ e d andalso
                       (finite_pattern_accepts C_ p t andalso
                         finite_relation_functional C_ equal_finite_factor_term
                           (sup_fset (equal_prod C_ equal_finite_factor_term) v
                             (finite_matching_bindings C_ p t)))
                   end
                 then SOME let
                             val (e, t) = x;
                           in
                             (sup_fset (equal_prod C_ equal_finite_factor_term)
                                v (finite_matching_bindings C_ p t),
                               finsert
                                 (equal_prod A_
                                   (equal_prod B_ equal_finite_factor_term))
                                 (s, (e, t)) h)
                           end
                 else NONE))
             k)
      (finite_premise_joins A_ B_ C_ ps k);

fun finite_schema_conclusion
  (Finite_factor_schema_ext
    (finite_schema_conclusion, finite_schema_premises, finite_schema_materials,
      more))
  = finite_schema_conclusion;

fun finite_schema_materials
  (Finite_factor_schema_ext
    (finite_schema_conclusion, finite_schema_premises, finite_schema_materials,
      more))
  = finite_schema_materials;

fun finite_schema_premises
  (Finite_factor_schema_ext
    (finite_schema_conclusion, finite_schema_premises, finite_schema_materials,
      more))
  = finite_schema_premises;

fun finite_material_functions
  (Finite_material_pattern_ext
    (finite_material_source, finite_material_atoms, finite_material_edges,
      finite_material_counts, finite_material_functions, more))
  = finite_material_functions;

fun finite_material_source
  (Finite_material_pattern_ext
    (finite_material_source, finite_material_atoms, finite_material_edges,
      finite_material_counts, finite_material_functions, more))
  = finite_material_source;

fun finite_material_counts
  (Finite_material_pattern_ext
    (finite_material_source, finite_material_atoms, finite_material_edges,
      finite_material_counts, finite_material_functions, more))
  = finite_material_counts;

fun finite_material_edges
  (Finite_material_pattern_ext
    (finite_material_source, finite_material_atoms, finite_material_edges,
      finite_material_counts, finite_material_functions, more))
  = finite_material_edges;

fun finite_material_atoms
  (Finite_material_pattern_ext
    (finite_material_source, finite_material_atoms, finite_material_edges,
      finite_material_counts, finite_material_functions, more))
  = finite_material_atoms;

fun finite_material_formed m =
  finite_pattern_formed (finite_material_source m) andalso
    (finite_pattern_formed (finite_material_atoms m) andalso
      (finite_pattern_formed (finite_material_edges m) andalso
        (finite_pattern_formed (finite_material_counts m) andalso
          finite_pattern_formed (finite_material_functions m))));

fun finite_schema_formed A_ B_ C_ s =
  finite_pattern_formed (finite_schema_conclusion s) andalso
    (finite_relation_functional B_
       (equal_prod C_ (equal_finite_term_pattern A_))
       (finite_schema_premises s) andalso
      (ball (fset (finite_schema_premises s))
         (fn (_, (_, a)) => finite_pattern_formed a) andalso
        (finite_relation_functional B_
           (equal_finite_material_pattern_ext A_ equal_unit)
           (finite_schema_materials s) andalso
          (eq (equal_fset B_)
             (inf_fset B_ (fimage fst (finite_schema_premises s))
               (fimage fst (finite_schema_materials s)))
             bot_fset andalso
            ball (fset (finite_schema_materials s))
              (fn (_, a) => finite_material_formed a)))));

fun finite_premise_entries h = fimage (fn (s, (d, _)) => (s, d)) h;

fun finite_pattern_values A_ v (Finite_Variable a) =
  fimage snd (ffilter (fn z => eq A_ (fst z) a) v)
  | finite_pattern_values A_ v (Finite_Pattern_Target t) =
    (if finite_target_formed t
      then finsert equal_finite_factor_term (Finite_Target t) bot_fset
      else bot_fset)
  | finite_pattern_values A_ v (Finite_Pattern_Payload b) =
    (if octets_formed b
      then finsert equal_finite_factor_term (Finite_Payload b) bot_fset
      else bot_fset)
  | finite_pattern_values A_ v (Finite_Pattern_Pair (p, q)) =
    ffUnion equal_finite_factor_term
      (fimage
        (fn x =>
          fimage (fn a => Finite_Pair (x, a)) (finite_pattern_values A_ v q))
        (finite_pattern_values A_ v p));

fun finite_schema_library_formed B_ C_ D_ l =
  list_all
    (fn (_, (s, ps)) =>
      finite_schema_formed B_ C_ D_ s andalso
        equal_seta
          (equal_prod C_ (equal_prod D_ (equal_finite_term_pattern B_)))
          (Set ps) (fset (finite_schema_premises s)))
    l;

fun finite_inference_demand_reasons A_ B_ f k a =
  let
    val demanded = finite_inference_demand A_ B_ f k a;
  in
    ffUnion
      (equal_prod A_
        (equal_prod (equal_fset (equal_prod B_ A_)) (equal_prod B_ A_)))
      (fimage
        (fn (aa, h) =>
          (if member A_ aa (fset demanded) andalso
                (not (member A_ aa (fset k)) andalso
                  finite_premise_functional B_ A_ h)
            then fimage (fn (i, b) => (aa, (h, (i, b)))) h else bot_fset))
        f)
  end;

fun finite_inference_round A_ B_ f k x =
  sup_set A_ (fset k)
    (image fst
      (filter
        (fn (_, h) =>
          finite_premise_functional B_ A_ h andalso
            less_eq_set A_ (image snd (fset h)) x)
        (fset f)));

fun finite_inference_result A_ B_ f k =
  whilea
    (fn x => not (eq (equal_set A_) (finite_inference_round A_ B_ f k x) x))
    (finite_inference_round A_ B_ f k) bot_set;

fun finite_library_entry_rules l =
  fimage
    (fn (d, (s, _)) => (d, finite_premise_entries (finite_schema_premises s)))
    (fset_of_list l);

fun finite_library_blocked_goals A_ C_ l k goals =
  ffilter
    (fn (_, (d, _)) =>
      not (member A_ d
            (finite_inference_result A_ C_ (finite_library_entry_rules l)
              (fimage fst k))))
    goals;

fun finite_library_coverage A_ B_ C_ D_ l k goals =
  let
    val rules = finite_library_entry_rules l;
    val known = fimage fst k;
    val targets = fimage (fn (_, (d, _)) => d) goals;
    val formed =
      finite_schema_library_formed B_ C_ A_ l andalso
        (ball (fset k) (fn (_, a) => finite_term_formed a) andalso
          (ball (fset goals) (fn (_, (_, a)) => finite_term_formed a) andalso
            finite_premise_functional D_
              (equal_prod A_ equal_finite_factor_term) goals));
  in
    (formed,
      (rules,
        (finite_library_blocked_goals A_ C_ l k goals,
          (finite_inference_demand A_ C_ rules known targets,
            finite_inference_demand_reasons A_ C_ rules known targets))))
  end;

fun finite_incidence_read c (Finite_Pair (x, Finite_Pair (y, z))) =
  (case (finite_occurrence_read c x,
          (finite_occurrence_read c y, finite_occurrence_read c z))
    of (NONE, _) => NONE | (SOME _, (NONE, _)) => NONE
    | (SOME _, (SOME _, NONE)) => NONE
    | (SOME a, (SOME b, SOME ca)) => SOME (a, (b, ca)))
  | finite_incidence_read c (Finite_Target v) = NONE
  | finite_incidence_read c (Finite_Payload v) = NONE
  | finite_incidence_read c (Finite_Pair (v, Finite_Target vb)) = NONE
  | finite_incidence_read c (Finite_Pair (v, Finite_Payload vb)) = NONE;

fun finite_schema_premise_instance A_ B_ C_ s v q =
  finite_relation_functional B_ (equal_prod C_ equal_finite_factor_term)
    q andalso
    (eq (equal_fset B_) (fimage fst q)
       (fimage fst (finite_schema_premises s)) andalso
      ball (fset (finite_schema_premises s))
        (fn (sa, (d, p)) =>
          bex (fset q)
            (fn (r, (e, t)) =>
              eq B_ r sa andalso
                (eq C_ e d andalso finite_pattern_instance A_ v p t))));

fun finite_material_variables A_ m =
  sup_fset A_
    (sup_fset A_
      (sup_fset A_
        (sup_fset A_ (finite_pattern_variables A_ (finite_material_source m))
          (finite_pattern_variables A_ (finite_material_atoms m)))
        (finite_pattern_variables A_ (finite_material_edges m)))
      (finite_pattern_variables A_ (finite_material_counts m)))
    (finite_pattern_variables A_ (finite_material_functions m));

fun finite_schema_variables A_ s =
  sup_fset A_
    (sup_fset A_ (finite_pattern_variables A_ (finite_schema_conclusion s))
      (ffUnion A_
        (fimage (fn (_, (_, a)) => finite_pattern_variables A_ a)
          (finite_schema_premises s))))
    (ffUnion A_
      (fimage (fn (_, a) => finite_material_variables A_ a)
        (finite_schema_materials s)));

fun finite_schema_instance A_ B_ C_ s v t q =
  finite_schema_formed A_ B_ C_ s andalso
    (finite_term_bindings_formed A_ (finite_schema_variables A_ s) v andalso
      (finite_pattern_instance A_ v (finite_schema_conclusion s) t andalso
        finite_schema_premise_instance A_ B_ C_ s v q));

fun natural_library_coverage l k goals =
  finite_library_coverage equal_nat equal_nat equal_nat equal_nat l k goals;

fun finite_attachment_read c (Finite_Pair (x, Finite_Payload v)) =
  map_option (fn a => (a, v)) (finite_occurrence_read c x)
  | finite_attachment_read c (Finite_Target v) = NONE
  | finite_attachment_read c (Finite_Payload v) = NONE
  | finite_attachment_read c (Finite_Pair (v, Finite_Target vb)) = NONE
  | finite_attachment_read c (Finite_Pair (v, Finite_Pair (vb, vc))) = NONE;

fun finite_enumerated_artifact a e b f =
  Finite_structured_object_ext
    (Finite_rra_structure_ext (fset_of_list a, fset_of_list e, ()),
      Finite_opaque_basis_ext (Mset b, fset_of_list f, ()), ());

fun finite_artifact_enumeration c a e b f =
  finite_exact_formed c andalso
    (distinct (equal_list equal_nat) a andalso
      (distinct
         (equal_prod (equal_list equal_nat)
           (equal_prod (equal_list equal_nat) (equal_list equal_nat)))
         e andalso
        (distinct (equal_prod (equal_list equal_nat) (equal_list equal_nat))
           f andalso
          equal_finite_structured_object_ext (equal_list equal_nat)
            (equal_list equal_nat) equal_unit c
            (finite_enumerated_artifact a e b f))));

fun finite_enumeration_read read (Finite_Target t) =
  (case t
    of Finite_Whole c =>
      (if equal_finite_structured_object_ext (equal_list equal_nat)
            (equal_list equal_nat) equal_unit c finite_empty_artifact
        then SOME [] else NONE)
    | Finite_Anchor (_, _) => NONE)
  | finite_enumeration_read read (Finite_Payload v) = NONE
  | finite_enumeration_read read (Finite_Pair (x, xs)) =
    (case read x of NONE => NONE
      | SOME a =>
        map_option (fn b => a :: b) (finite_enumeration_read read xs));

fun finite_material_observation (Finite_Target (Finite_Whole c)) atoms edges
  counts functions =
  (case (finite_enumeration_read (finite_atom_read c) atoms,
          (finite_enumeration_read (finite_incidence_read c) edges,
            (finite_enumeration_read (finite_attachment_read c) counts,
              finite_enumeration_read (finite_attachment_read c) functions)))
    of (NONE, _) => false | (SOME _, (NONE, _)) => false
    | (SOME _, (SOME _, (NONE, _))) => false
    | (SOME _, (SOME _, (SOME _, NONE))) => false
    | (SOME a, (SOME e, (SOME ba, SOME b))) =>
      finite_artifact_enumeration c a e ba b)
  | finite_material_observation (Finite_Target (Finite_Anchor (va, vb))) atoms
    edges counts functions = false
  | finite_material_observation (Finite_Payload v) atoms edges counts functions
    = false
  | finite_material_observation (Finite_Pair (v, va)) atoms edges counts
    functions = false;

fun finite_pattern_instances A_ v (Finite_Variable a) =
  fimage snd (ffilter (fn x => eq A_ (fst x) a) v)
  | finite_pattern_instances A_ v (Finite_Pattern_Target t) =
    (if finite_target_formed t
      then finsert equal_finite_factor_term (Finite_Target t) bot_fset
      else bot_fset)
  | finite_pattern_instances A_ va (Finite_Pattern_Payload v) =
    (if octets_formed v
      then finsert equal_finite_factor_term (Finite_Payload v) bot_fset
      else bot_fset)
  | finite_pattern_instances A_ v (Finite_Pattern_Pair (p, q)) =
    ffUnion equal_finite_factor_term
      (fimage
        (fn x =>
          fimage (fn a => Finite_Pair (x, a)) (finite_pattern_instances A_ v q))
        (finite_pattern_instances A_ v p));

fun finite_material_satisfied A_ v m =
  bex (fset (finite_pattern_instances A_ v (finite_material_source m)))
    (fn s =>
      bex (fset (finite_pattern_instances A_ v (finite_material_atoms m)))
        (fn a =>
          bex (fset (finite_pattern_instances A_ v (finite_material_edges m)))
            (fn e =>
              bex (fset (finite_pattern_instances A_ v
                          (finite_material_counts m)))
                (fn b =>
                  bex (fset (finite_pattern_instances A_ v
                              (finite_material_functions m)))
                    (finite_material_observation s a e b)))));

fun finite_schema_material_satisfied A_ s v =
  ball (fset (finite_schema_materials s))
    (fn (_, a) => finite_material_satisfied A_ v a);

fun finite_schema_generation A_ B_ C_ s ps k =
  (if finite_schema_formed A_ B_ C_ s andalso
        equal_seta
          (equal_prod B_ (equal_prod C_ (equal_finite_term_pattern A_)))
          (Set ps) (fset (finite_schema_premises s))
    then ffUnion
           (equal_prod equal_finite_factor_term
             (equal_prod (equal_fset (equal_prod A_ equal_finite_factor_term))
               (equal_fset
                 (equal_prod B_ (equal_prod C_ equal_finite_factor_term)))))
           (fimage
             (fn (v, h) =>
               fimage (fn t => (t, (v, h)))
                 (ffilter
                   (fn t =>
                     finite_schema_instance A_ B_ C_ s v t h andalso
                       finite_schema_material_satisfied A_ s v)
                   (finite_pattern_values A_ v (finite_schema_conclusion s))))
             (fset_of_list (finite_premise_joins B_ C_ A_ ps k)))
    else bot_fset);

fun make finite_schema_conclusion finite_schema_premises finite_schema_materials
  = Finite_factor_schema_ext
      (finite_schema_conclusion, finite_schema_premises,
        finite_schema_materials, ());

val finite_specialization_report_schema :
  (nat, nat, nat, unit) finite_factor_schema_ext
  = Finite_factor_schema_ext
      (Finite_Pattern_Pair
         (Finite_Pattern_Pair
            (Finite_Pattern_Pair
               (Finite_Variable zero_nata,
                 Finite_Pattern_Pair
                   (Finite_Variable one_nata,
                     Finite_Variable (nat_of_integer (2 : IntInf.int)))),
              Finite_Pattern_Pair
                (Finite_Variable (nat_of_integer (3 : IntInf.int)),
                  Finite_Variable (nat_of_integer (4 : IntInf.int)))),
           Finite_Variable (nat_of_integer (5 : IntInf.int))),
        fset_of_list
          [(zero_nata,
             (nat_of_integer (294 : IntInf.int),
               Finite_Pattern_Pair
                 (Finite_Pattern_Pair
                    (Finite_Variable zero_nata,
                      Finite_Pattern_Pair
                        (Finite_Variable one_nata,
                          Finite_Variable (nat_of_integer (2 : IntInf.int)))),
                   Finite_Pattern_Pair
                     (Finite_Variable (nat_of_integer (3 : IntInf.int)),
                       Finite_Variable (nat_of_integer (4 : IntInf.int)))))),
            (one_nata,
              (nat_of_integer (126 : IntInf.int),
                Finite_Pattern_Pair
                  (Finite_Variable (nat_of_integer (4 : IntInf.int)),
                    Finite_Variable (nat_of_integer (5 : IntInf.int)))))],
        bot_fset, ());

val specialization_report_reasoning_library :
  (nat *
    ((nat, nat, nat, unit) finite_factor_schema_ext *
      (nat * (nat * nat finite_term_pattern)) list)) list
  = [(nat_of_integer (342 : IntInf.int),
       (finite_specialization_report_schema,
         [(zero_nata,
            (nat_of_integer (294 : IntInf.int),
              Finite_Pattern_Pair
                (Finite_Pattern_Pair
                   (Finite_Variable zero_nata,
                     Finite_Pattern_Pair
                       (Finite_Variable one_nata,
                         Finite_Variable (nat_of_integer (2 : IntInf.int)))),
                  Finite_Pattern_Pair
                    (Finite_Variable (nat_of_integer (3 : IntInf.int)),
                      Finite_Variable (nat_of_integer (4 : IntInf.int)))))),
           (one_nata,
             (nat_of_integer (126 : IntInf.int),
               Finite_Pattern_Pair
                 (Finite_Variable (nat_of_integer (4 : IntInf.int)),
                   Finite_Variable (nat_of_integer (5 : IntInf.int)))))]))];

val finite_binding_list_step_schema :
  (nat, nat, nat, unit) finite_factor_schema_ext
  = Finite_factor_schema_ext
      (Finite_Pattern_Pair
         (Finite_Variable zero_nata,
           Finite_Pattern_Pair
             (Finite_Pattern_Pair
                (Finite_Variable one_nata,
                  Finite_Variable (nat_of_integer (2 : IntInf.int))),
               Finite_Pattern_Pair
                 (Finite_Variable (nat_of_integer (3 : IntInf.int)),
                   Finite_Variable (nat_of_integer (4 : IntInf.int))))),
        fset_of_list
          [(zero_nata,
             (nat_of_integer (343 : IntInf.int),
               Finite_Pattern_Pair
                 (Finite_Variable zero_nata,
                   Finite_Pattern_Pair
                     (Finite_Variable one_nata,
                       Finite_Variable (nat_of_integer (3 : IntInf.int)))))),
            (one_nata,
              (nat_of_integer (345 : IntInf.int),
                Finite_Pattern_Pair
                  (Finite_Variable zero_nata,
                    Finite_Pattern_Pair
                      (Finite_Variable (nat_of_integer (2 : IntInf.int)),
                        Finite_Variable (nat_of_integer (4 : IntInf.int))))))],
        bot_fset, ());

fun binding_list_construction_library (A1_, A2_) B_ (C1_, C2_) =
  [(nat_of_integer (345 : IntInf.int),
     (finite_binding_list_step_schema,
       [(zero A2_,
          (numeral B_
             (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))),
            Finite_Pattern_Pair
              (Finite_Variable (zero C1_),
                Finite_Pattern_Pair
                  (Finite_Variable (one (one_numeral C2_)),
                    Finite_Variable (numeral C2_ (Bit1 One)))))),
         (one A1_,
           (numeral B_
              (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))),
             Finite_Pattern_Pair
               (Finite_Variable (zero C1_),
                 Finite_Pattern_Pair
                   (Finite_Variable (numeral C2_ (Bit0 One)),
                     Finite_Variable (numeral C2_ (Bit0 (Bit0 One)))))))]))];

val finite_binding_observation_schema :
  (nat, nat, nat, unit) finite_factor_schema_ext
  = Finite_factor_schema_ext
      (Finite_Pattern_Pair
         (Finite_Variable zero_nata,
           Finite_Pattern_Pair
             (Finite_Variable one_nata,
               Finite_Pattern_Pair
                 (Finite_Variable (nat_of_integer (2 : IntInf.int)),
                   Finite_Variable (nat_of_integer (3 : IntInf.int))))),
        fset_of_list
          [(zero_nata,
             (nat_of_integer (345 : IntInf.int),
               Finite_Pattern_Pair
                 (Finite_Variable zero_nata,
                   Finite_Pattern_Pair
                     (Finite_Variable one_nata,
                       Finite_Variable (nat_of_integer (2 : IntInf.int)))))),
            (one_nata,
              (nat_of_integer (346 : IntInf.int),
                Finite_Pattern_Pair
                  (Finite_Variable zero_nata,
                    Finite_Pattern_Pair
                      (Finite_Variable one_nata,
                        Finite_Variable (nat_of_integer (3 : IntInf.int))))))],
        bot_fset, ());

val binding_observation_reasoning_library :
  (nat *
    ((nat, nat, nat, unit) finite_factor_schema_ext *
      (nat * (nat * nat finite_term_pattern)) list)) list
  = [(nat_of_integer (347 : IntInf.int),
       (finite_binding_observation_schema,
         [(zero_nata,
            (nat_of_integer (345 : IntInf.int),
              Finite_Pattern_Pair
                (Finite_Variable zero_nata,
                  Finite_Pattern_Pair
                    (Finite_Variable one_nata,
                      Finite_Variable (nat_of_integer (2 : IntInf.int)))))),
           (one_nata,
             (nat_of_integer (346 : IntInf.int),
               Finite_Pattern_Pair
                 (Finite_Variable zero_nata,
                   Finite_Pattern_Pair
                     (Finite_Variable one_nata,
                       Finite_Variable
                         (nat_of_integer (3 : IntInf.int))))))]))];

val reader_construction_library :
  (nat *
    ((nat, nat, nat, unit) finite_factor_schema_ext *
      (nat * (nat * nat finite_term_pattern)) list)) list
  = specialization_report_reasoning_library @
      binding_observation_reasoning_library @
        binding_list_construction_library (one_nat, zero_nat) numeral_nat
          (zero_nat, numeral_nat);

fun reader_library_coverage k goals =
  natural_library_coverage reader_construction_library k goals;

fun finite_reasoning_term_equal t u = equal_finite_factor_terma t u;

fun finite_inference_residual A_ B_ C_ f k h =
  (if equal_fseta (equal_prod C_ A_) h bot_fset then bot_fset
    else let
           val settled = finite_inference_result A_ B_ f k;
         in
           ffilter (fn (_, a) => not (member A_ a settled)) h
         end);

fun admission_direct_pair_head (B1_, B2_) pair payload a b n =
  let
    val nila = payload [];
    val goal =
      pair (payload [one B1_])
        (pair (pair (payload [zero B2_]) a) (pair (payload [zero B2_]) b));
    val instruction = pair n (pair a (pair b nila));
  in
    pair (pair goal n) (pair n (pair (pair nila n) (pair instruction nila)))
  end;

fun finite_admission_counter n =
  (if equal_nata n zero_nata then Finite_Payload []
    else Finite_Pair
           (Finite_Payload [],
             finite_admission_counter (minus_nat n one_nata)));

val reasoning_false_goal : finite_factor_term =
  admission_direct_pair_head (one_nat, zero_nat)
    (fn a => fn b => Finite_Pair (a, b)) Finite_Payload
    (finite_admission_counter zero_nata) (finite_admission_counter one_nata)
    (Finite_Payload [zero_nata]);

fun finite_premise_set_joins A_ B_ C_ [] c =
  finsert
    (equal_prod (equal_fset (equal_prod C_ equal_finite_factor_term))
      (equal_fset (equal_prod A_ (equal_prod B_ equal_finite_factor_term))))
    (bot_fset, bot_fset) bot_fset
  | finite_premise_set_joins A_ B_ C_ ((s, (d, p)) :: ps) c =
    ffUnion
      (equal_prod (equal_fset (equal_prod C_ equal_finite_factor_term))
        (equal_fset (equal_prod A_ (equal_prod B_ equal_finite_factor_term))))
      (fimage
        (fn (v, h) =>
          fimage
            (fn (e, t) =>
              (sup_fset (equal_prod C_ equal_finite_factor_term) v
                 (finite_matching_bindings C_ p t),
                finsert (equal_prod A_ (equal_prod B_ equal_finite_factor_term))
                  (s, (e, t)) h))
            (ffilter
              (fn (e, t) =>
                eq B_ e d andalso
                  (finite_pattern_accepts C_ p t andalso
                    finite_relation_functional C_ equal_finite_factor_term
                      (sup_fset (equal_prod C_ equal_finite_factor_term) v
                        (finite_matching_bindings C_ p t))))
              c))
        (finite_premise_set_joins A_ B_ C_ ps c));

fun makea finite_material_source finite_material_atoms finite_material_edges
  finite_material_counts finite_material_functions =
  Finite_material_pattern_ext
    (finite_material_source, finite_material_atoms, finite_material_edges,
      finite_material_counts, finite_material_functions, ());

fun finite_schema_generation_on_set A_ B_ C_ s ps c =
  (if finite_schema_formed A_ B_ C_ s andalso
        equal_seta
          (equal_prod B_ (equal_prod C_ (equal_finite_term_pattern A_)))
          (Set ps) (fset (finite_schema_premises s))
    then ffUnion
           (equal_prod equal_finite_factor_term
             (equal_prod (equal_fset (equal_prod A_ equal_finite_factor_term))
               (equal_fset
                 (equal_prod B_ (equal_prod C_ equal_finite_factor_term)))))
           (fimage
             (fn (v, h) =>
               fimage (fn t => (t, (v, h)))
                 (ffilter
                   (fn t =>
                     finite_schema_instance A_ B_ C_ s v t h andalso
                       finite_schema_material_satisfied A_ s v)
                   (finite_pattern_values A_ v (finite_schema_conclusion s))))
             (finite_premise_set_joins B_ C_ A_ ps c))
    else bot_fset);

fun finite_generated_applications_on_set A_ B_ C_ D_ l c =
  ffUnion
    (equal_prod A_
      (equal_prod (equal_finite_factor_schema_ext B_ C_ D_ equal_unit)
        (equal_prod equal_finite_factor_term
          (equal_prod (equal_fset (equal_prod B_ equal_finite_factor_term))
            (equal_fset
              (equal_prod C_ (equal_prod D_ equal_finite_factor_term)))))))
    (fimage
      (fn (d, (s, ps)) =>
        fimage (fn (t, (v, h)) => (d, (s, (t, (v, h)))))
          (finite_schema_generation_on_set B_ C_ D_ s ps c))
      (fset_of_list l));

fun finite_generated_rules_on_set A_ B_ C_ D_ l c =
  fimage (fn (d, (_, (t, (_, a)))) => ((d, t), a))
    (finite_generated_applications_on_set A_ B_ C_ D_ l c);

fun finite_learned_investigation_on_set A_ B_ C_ D_ l c k goals =
  let
    val applications = finite_generated_applications_on_set A_ B_ C_ A_ l c;
    val rules = finite_generated_rules_on_set A_ B_ C_ A_ l c;
    val formed =
      finite_schema_library_formed B_ C_ A_ l andalso
        (ball (fset c) (fn q => finite_term_formed (snd q)) andalso
          (ball (fset k) (fn q => finite_term_formed (snd q)) andalso
            (ball (fset goals) (fn (_, q) => finite_term_formed (snd q)) andalso
              finite_premise_functional D_
                (equal_prod A_ equal_finite_factor_term) goals)));
  in
    (formed,
      (applications,
        (finite_inference_residual (equal_prod A_ equal_finite_factor_term) C_
           D_ rules k goals,
          (finite_inference_demand (equal_prod A_ equal_finite_factor_term) C_
             rules k (fimage snd goals),
            finite_inference_demand_reasons
              (equal_prod A_ equal_finite_factor_term) C_ rules k
              (fimage snd goals)))))
  end;

fun finite_construction_frontier A_ B_ C_ n l c =
  (if equal_nata n zero_nata then c
    else let
           val d =
             finite_construction_frontier A_ B_ C_ (minus_nat n one_nata) l c;
         in
           sup_fset (equal_prod A_ equal_finite_factor_term) d
             (fimage fst (finite_generated_rules_on_set A_ B_ C_ A_ l d))
         end);

fun finite_chained_investigation A_ B_ C_ D_ n l c k goals =
  finite_learned_investigation_on_set A_ B_ C_ D_ l
    (finite_construction_frontier A_ B_ C_ n l (fset_of_list c)) k goals;

fun finite_generated_schema_applications A_ B_ C_ D_ l c =
  ffUnion
    (equal_prod A_
      (equal_prod (equal_finite_factor_schema_ext B_ C_ D_ equal_unit)
        (equal_prod equal_finite_factor_term
          (equal_prod (equal_fset (equal_prod B_ equal_finite_factor_term))
            (equal_fset
              (equal_prod C_ (equal_prod D_ equal_finite_factor_term)))))))
    (fimage
      (fn (d, (s, ps)) =>
        fimage (fn (t, (v, h)) => (d, (s, (t, (v, h)))))
          (finite_schema_generation B_ C_ D_ s ps c))
      (fset_of_list l));

fun finite_generated_schema_rules A_ B_ C_ D_ l c =
  fimage (fn (d, (_, (t, (_, a)))) => ((d, t), a))
    (finite_generated_schema_applications A_ B_ C_ D_ l c);

fun finite_learned_investigation A_ B_ C_ D_ l c k goals =
  let
    val applications = finite_generated_schema_applications A_ B_ C_ A_ l c;
    val rules = finite_generated_schema_rules A_ B_ C_ A_ l c;
    val formed =
      finite_schema_library_formed B_ C_ A_ l andalso
        (list_all (fn q => finite_term_formed (snd q)) c andalso
          (ball (fset k) (fn q => finite_term_formed (snd q)) andalso
            (ball (fset goals) (fn (_, q) => finite_term_formed (snd q)) andalso
              finite_premise_functional D_
                (equal_prod A_ equal_finite_factor_term) goals)));
  in
    (formed,
      (applications,
        (finite_inference_residual (equal_prod A_ equal_finite_factor_term) C_
           D_ rules k goals,
          (finite_inference_demand (equal_prod A_ equal_finite_factor_term) C_
             rules k (fimage snd goals),
            finite_inference_demand_reasons
              (equal_prod A_ equal_finite_factor_term) C_ rules k
              (fimage snd goals)))))
  end;

fun natural_chained_investigation n l c k goals =
  finite_chained_investigation equal_nat equal_nat equal_nat equal_nat n l c k
    goals;

fun natural_construction_frontier n l c =
  finite_construction_frontier equal_nat equal_nat equal_nat n l c;

fun natural_learned_investigation l c k goals =
  finite_learned_investigation equal_nat equal_nat equal_nat equal_nat l c k
    goals;

val reasoning_false_frontier : (nat * finite_factor_term) list =
  [(nat_of_integer (340 : IntInf.int), finite_admission_counter zero_nata),
    (nat_of_integer (340 : IntInf.int), finite_admission_counter one_nata),
    (nat_of_integer (340 : IntInf.int), Finite_Payload [zero_nata])];

val admission_pair_reasoning_goal : finite_factor_term =
  admission_direct_pair_head (one_nat, zero_nat)
    (fn a => fn b => Finite_Pair (a, b)) Finite_Payload
    (finite_admission_counter zero_nata) (finite_admission_counter one_nata)
    (finite_admission_counter (nat_of_integer (2 : IntInf.int)));

fun finite_binding_observation_row first u r =
  (case r of Finite_Target _ => NONE | Finite_Payload _ => NONE
    | Finite_Pair (Finite_Target _, _) => NONE
    | Finite_Pair (Finite_Payload _, _) => NONE
    | Finite_Pair (Finite_Pair (_, _), Finite_Target _) => NONE
    | Finite_Pair (Finite_Pair (_, _), Finite_Payload _) => NONE
    | Finite_Pair (Finite_Pair (owner, a), Finite_Pair (x, y)) =>
      (if equal_finite_factor_terma owner u andalso
            (finite_term_formed u andalso
              (finite_term_formed a andalso
                (finite_term_formed x andalso finite_term_formed y)))
        then SOME (Finite_Pair (a, (if first then x else y))) else NONE));

fun finite_binding_observation_view first u [] =
  (if finite_term_formed u then SOME [] else NONE)
  | finite_binding_observation_view first u (r :: rs) =
    (case finite_binding_observation_row first u r of NONE => NONE
      | SOME v =>
        map_option (fn a => v :: a)
          (finite_binding_observation_view first u rs));

fun finite_binding_observation_frontier u bs =
  (case finite_binding_observation_view true u bs of NONE => []
    | SOME xs =>
      [(nat_of_integer (345 : IntInf.int),
         Finite_Pair
           (u, Finite_Pair
                 (foldr (fn a => fn b => Finite_Pair (a, b)) bs
                    (Finite_Payload []),
                   foldr (fn a => fn b => Finite_Pair (a, b)) xs
                     (Finite_Payload []))))]) @
    (case finite_binding_observation_view false u bs of NONE => []
      | SOME ys =>
        [(nat_of_integer (346 : IntInf.int),
           Finite_Pair
             (u, Finite_Pair
                   (foldr (fn a => fn b => Finite_Pair (a, b)) bs
                      (Finite_Payload []),
                     foldr (fn a => fn b => Finite_Pair (a, b)) ys
                       (Finite_Payload []))))]);

fun binding_observation_calls sources =
  maps (fn (a, b) => finite_binding_observation_frontier a b) sources;

fun finite_admission_counter_number (Finite_Target t) = NONE
  | finite_admission_counter_number (Finite_Payload b) =
    (if null b then SOME zero_nata else NONE)
  | finite_admission_counter_number (Finite_Pair (a, b)) =
    (if equal_finite_factor_terma a (Finite_Payload [])
      then map_option suc (finite_admission_counter_number b) else NONE);

fun finite_admission_counter_check t =
  not (is_none (finite_admission_counter_number t));

fun admitted_reasoning_frontier c =
  filtera
    (fn (d, t) =>
      equal_nata d (nat_of_integer (340 : IntInf.int)) andalso
        finite_admission_counter_check t)
    c;

val investigation_input_goal : admission_goal =
  Paired_Admission
    (Existing_Admission (nat_of_integer (311 : IntInf.int)),
      Collected_Admission
        (Paired_Admission
          (Existing_Admission (nat_of_integer (2 : IntInf.int)),
            Existing_Admission (nat_of_integer (2 : IntInf.int)))));

fun input_example_admitted n =
  not (member equal_nat n
        (insert equal_nat (nat_of_integer (6 : IntInf.int))
          (insert equal_nat (nat_of_integer (7 : IntInf.int))
            (insert equal_nat (nat_of_integer (8 : IntInf.int))
              (insert equal_nat (nat_of_integer (10 : IntInf.int)) bot_set)))));

val finite_admission_direct_pair_schema :
  (nat, nat, nat, unit) finite_factor_schema_ext
  = Finite_factor_schema_ext
      (admission_direct_pair_head (one_nat, zero_nat)
         (fn a => fn b => Finite_Pattern_Pair (a, b)) Finite_Pattern_Payload
         (Finite_Variable zero_nata) (Finite_Variable one_nata)
         (Finite_Variable (nat_of_integer (2 : IntInf.int))),
        fset_of_list
          [(zero_nata,
             (nat_of_integer (340 : IntInf.int), Finite_Variable zero_nata)),
            (one_nata,
              (nat_of_integer (340 : IntInf.int), Finite_Variable one_nata)),
            (nat_of_integer (2 : IntInf.int),
              (nat_of_integer (340 : IntInf.int),
                Finite_Variable (nat_of_integer (2 : IntInf.int))))],
        bot_fset, ());

fun admission_pair_reasoning_library A_ (B1_, B2_) C_ (D1_, D2_) =
  [(numeral A_ (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))),
     (finite_admission_direct_pair_schema,
       [(zero B1_,
          (numeral C_
             (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))),
            Finite_Variable (zero D1_))),
         (one (one_numeral B2_),
           (numeral C_
              (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))),
             Finite_Variable (one (one_numeral D2_)))),
         (numeral B2_ (Bit0 One),
           (numeral C_
              (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))),
             Finite_Variable (numeral D2_ (Bit0 One))))]))];

val admission_pair_reasoning_frontier : (nat * finite_factor_term) list =
  map (fn n => (nat_of_integer (340 : IntInf.int), finite_admission_counter n))
    [zero_nata, one_nata, nat_of_integer (2 : IntInf.int)];

fun admission_pair_reasoning_experiment stage =
  finite_learned_investigation equal_nat equal_nat equal_nat equal_nat
    (if equal_nata stage zero_nata then []
      else admission_pair_reasoning_library numeral_nat (zero_nat, numeral_nat)
             numeral_nat (zero_nat, numeral_nat))
    admission_pair_reasoning_frontier
    (fset_of_list
      (if equal_nata stage one_nata
        then take (nat_of_integer (2 : IntInf.int))
               admission_pair_reasoning_frontier
        else admission_pair_reasoning_frontier))
    (finsert
      (equal_prod equal_nat (equal_prod equal_nat equal_finite_factor_term))
      (zero_nata,
        (nat_of_integer (341 : IntInf.int), admission_pair_reasoning_goal))
      bot_fset);

fun finite_binding_list_seed u r =
  (case finite_binding_observation_row true u r of NONE => []
    | SOME x =>
      [(nat_of_integer (343 : IntInf.int), Finite_Pair (u, Finite_Pair (r, x))),
        (nat_of_integer (345 : IntInf.int),
          Finite_Pair
            (u, Finite_Pair (Finite_Payload [], Finite_Payload [])))]);

fun binding_observation_sources_formed sources =
  list_all
    (fn (u, bs) => finite_term_formed u andalso list_all finite_term_formed bs)
    sources;

fun binding_observation_investigation enabled sources goals =
  let
    val c = binding_observation_calls sources;
    val result =
      natural_learned_investigation
        (if enabled then binding_observation_reasoning_library else []) c
        (fset_of_list c) goals;
  in
    (fst result andalso binding_observation_sources_formed sources, snd result)
  end;

fun reasoning_counterexample_experiment trust_frontier =
  finite_learned_investigation equal_nat equal_nat equal_nat equal_nat
    (admission_pair_reasoning_library numeral_nat (zero_nat, numeral_nat)
      numeral_nat (zero_nat, numeral_nat))
    reasoning_false_frontier
    (fset_of_list
      (if trust_frontier then reasoning_false_frontier
        else admitted_reasoning_frontier reasoning_false_frontier))
    (finsert
      (equal_prod equal_nat (equal_prod equal_nat equal_finite_factor_term))
      (zero_nata, (nat_of_integer (341 : IntInf.int), reasoning_false_goal))
      bot_fset);

fun finite_binding_observation_outputs u bs =
  (case finite_binding_observation_view true u bs of NONE => NONE
    | SOME xs =>
      map_option (fn a => (xs, a))
        (finite_binding_observation_view false u bs));

fun generated_input_execution n =
  (less_eq_nat (nat_of_integer (336 : IntInf.int)) n,
    (admission_plan investigation_input_goal n,
      (if less_nat n (nat_of_integer (336 : IntInf.int)) then []
        else map input_example_admitted
               [zero_nata, one_nata, nat_of_integer (2 : IntInf.int),
                 nat_of_integer (3 : IntInf.int),
                 nat_of_integer (4 : IntInf.int),
                 nat_of_integer (5 : IntInf.int),
                 nat_of_integer (6 : IntInf.int),
                 nat_of_integer (7 : IntInf.int),
                 nat_of_integer (8 : IntInf.int),
                 nat_of_integer (9 : IntInf.int),
                 nat_of_integer (10 : IntInf.int)])));

fun specialization_report_investigation c k goals =
  natural_learned_investigation specialization_report_reasoning_library c k
    goals;

fun binding_list_construction_investigation n enabled admit_row u r goals =
  let
    val c = finite_binding_list_seed u r;
    val k =
      fset_of_list
        (if admit_row then c
          else filtera
                 (fn q =>
                   not (equal_nata (fst q) (nat_of_integer (343 : IntInf.int))))
                 c);
    val result =
      natural_chained_investigation n
        (if enabled
          then binding_list_construction_library (one_nat, zero_nat) numeral_nat
                 (zero_nat, numeral_nat)
          else [])
        c k goals;
  in
    (fst result andalso (finite_term_formed u andalso finite_term_formed r),
      snd result)
  end;

end; (*struct Native_Reasoning*)
