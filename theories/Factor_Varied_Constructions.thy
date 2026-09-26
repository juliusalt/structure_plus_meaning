theory Factor_Varied_Constructions
  imports Factor_Finite_Schema_Matching Factor_Least_Witness_Registrations Factor_System_Alpha
    Finite_Set_Composition
begin

text \<open>
  V1 of DECISIONS.md "A checker does not produce", its addition "Registrations and declarations reach an installed
  package by matching its clauses against the placed ones" (task 642). A witness construction over a program P is
  carried to a program N whose clauses at the same sites are alpha variants of P's: at each clause T of N and each
  clause S of P at T's site that the clause match (@{const finite_schema_match}) sends to T by binder and socket maps
  (f, h), the construction registers the images under f of what it registers at S, and its value at an image is the
  source's value at S with the bindings carried back through f on S's scope. The value is produced over P, as the
  relocated construction's (@{const finite_relocated_construction}) is produced over its source; N's clauses check
  it. Where several matched clauses give values, there is a value only when they agree. A clause of N no clause of P
  matches keeps no registration and is searched plainly. No clause key is read or mapped: a clause is named by its
  site and its schema, compared as a value.
\<close>

section \<open>Bindings carried back along a binder map\<close>

text \<open>
  Ground bindings of a clause of N are carried back to a clause of P over the source's finite scope: a source
  variable x of the scope is bound to t exactly when f x is bound to t. The preimage is computed over the scope, so
  the carrying reads no inverse of f.
\<close>

definition finite_bindings_carried_back ::
    "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> ('b \<times> finite_factor_term) fset \<Rightarrow> ('a \<times> finite_factor_term) fset" where
  "finite_bindings_carried_back f X B =
    ffUnion (fimage (\<lambda>x. fimage (\<lambda>z. (x,snd z)) (ffilter (\<lambda>z. fst z = f x) B)) X)"


lemma finite_fst_member: "x |\<in>| fimage fst A \<longleftrightarrow> (\<exists>t. (x,t) |\<in>| A)"
  by (simp add: fimage.rep_eq fst_eq_Domain Domain_iff)

lemma finite_bindings_carried_back_member:
  "(x,t) |\<in>| finite_bindings_carried_back f X B \<longleftrightarrow> x |\<in>| X \<and> (f x,t) |\<in>| B"
proof
  assume "(x,t) |\<in>| finite_bindings_carried_back f X B"
  then obtain y z where yz: "y |\<in>| X" "z |\<in>| B" "fst z = f y" "(x,t) = (y,snd z)"
    unfolding finite_bindings_carried_back_def finite_union_image_member
    by (auto simp: fimage.rep_eq ffilter.rep_eq)
  have "z = (f x,t)" using yz(3,4) by (cases z) simp
  then show "x |\<in>| X \<and> (f x,t) |\<in>| B" using yz by simp
next
  assume xt: "x |\<in>| X \<and> (f x,t) |\<in>| B"
  have "(x,snd (f x,t)) |\<in>| fimage (\<lambda>z. (x,snd z)) (ffilter (\<lambda>z. fst z = f x) B)"
    by (rule fimageI) (simp add: xt ffilter.rep_eq)
  then show "(x,t) |\<in>| finite_bindings_carried_back f X B"
    unfolding finite_bindings_carried_back_def finite_union_image_member using xt by auto
qed

section \<open>The varied construction\<close>

definition finite_varied_clause_registered ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> 'd \<Rightarrow> ('b,'t::linorder,'d) finite_factor_schema \<Rightarrow>
      ('d \<times> 'c) \<times> ('a,'s,'d) finite_factor_schema \<Rightarrow> 'b fset" where
  "finite_varied_clause_registered \<kappa> d T z = (case z of ((d',c),S) \<Rightarrow> if d' = d then
    (case finite_schema_match S T of None \<Rightarrow> {||}
      | Some (f,h) \<Rightarrow> fimage f (witness_registered \<kappa> d S |\<inter>| finite_schema_variables S)) else {||})"

definition finite_varied_registered ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('b,'t::linorder,'d,'e) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> 'd \<Rightarrow> ('b,'t,'d) finite_factor_schema \<Rightarrow> 'b fset" where
  "finite_varied_registered P N \<kappa> d T =
    (if (d,T) |\<in>| fimage (\<lambda>z. (fst (fst z),snd z)) (finite_system_clauses N)
      then ffUnion (fimage (finite_varied_clause_registered \<kappa> d T) (finite_system_clauses P)) else {||})"

definition finite_varied_values ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
      'd \<Rightarrow> ('b,'t::linorder,'d) finite_factor_schema \<Rightarrow> ('b \<times> finite_factor_term) fset \<Rightarrow> 'b \<Rightarrow>
      finite_factor_term option fset" where
  "finite_varied_values P \<kappa> d T B b =
    ffUnion (fimage (\<lambda>((d',c),S). if d' = d then (case finite_schema_match S T of None \<Rightarrow> {||}
      | Some (f,h) \<Rightarrow> fimage (\<lambda>x. witness_value \<kappa> P d S (finite_bindings_carried_back f (finite_schema_variables S) B) x)
          (ffilter (\<lambda>x. f x = b) (witness_registered \<kappa> d S |\<inter>| finite_schema_variables S))) else {||})
      (finite_system_clauses P))"

definition finite_varied_construction ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('b,'t::linorder,'d,'e) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('b,'t,'d,'e) finite_witness_construction" where
  "finite_varied_construction P N \<kappa> = \<lparr>
    witness_registered = finite_varied_registered P N \<kappa>,
    witness_value = (\<lambda>Q d T B b. let Vs = finite_varied_values P \<kappa> d T B b in
      if Vs = {|fthe_elem Vs|} then fthe_elem Vs else None)\<rparr>"

lemma finite_clause_site_member:
  "(d,T) |\<in>| fimage (\<lambda>z. (fst (fst z),snd z)) C \<longleftrightarrow> (\<exists>c. ((d,c),T) |\<in>| C)"
proof
  assume "(d,T) |\<in>| fimage (\<lambda>z. (fst (fst z),snd z)) C"
  then obtain z where z: "z |\<in>| C" "(d,T) = (fst (fst z),snd z)" by (auto simp: fimage.rep_eq)
  then have "((d,snd (fst z)),T) = z" by (cases z) auto
  then show "\<exists>c. ((d,c),T) |\<in>| C" using z(1) by metis
next
  assume "\<exists>c. ((d,c),T) |\<in>| C"
  then obtain c where "((d,c),T) |\<in>| C" by blast
  from fimageI[OF this, of "\<lambda>z. (fst (fst z),snd z)"] show "(d,T) |\<in>| fimage (\<lambda>z. (fst (fst z),snd z)) C" by simp
qed

lemma finite_varied_clause_registered_member:
  "b |\<in>| finite_varied_clause_registered \<kappa> d T ((d',c),S) \<longleftrightarrow> d' = d \<and>
    (\<exists>f h x. finite_schema_match S T = Some (f,h) \<and> x |\<in>| witness_registered \<kappa> d S \<and>
      x |\<in>| finite_schema_variables S \<and> b = f x)"
  by (auto simp: finite_varied_clause_registered_def fimage.rep_eq split: option.splits)

lemma finite_varied_registered_member:
  "b |\<in>| finite_varied_registered P N \<kappa> d T \<longleftrightarrow> (\<exists>c'. ((d,c'),T) |\<in>| finite_system_clauses N) \<and>
    (\<exists>c S f h x. ((d,c),S) |\<in>| finite_system_clauses P \<and> finite_schema_match S T = Some (f,h) \<and>
      x |\<in>| witness_registered \<kappa> d S \<and> x |\<in>| finite_schema_variables S \<and> b = f x)"
proof
  assume reg: "b |\<in>| finite_varied_registered P N \<kappa> d T"
  then have guard: "(d,T) |\<in>| fimage (\<lambda>z. (fst (fst z),snd z)) (finite_system_clauses N)"
    unfolding finite_varied_registered_def by (auto split: if_splits)
  from reg obtain z where z: "z |\<in>| finite_system_clauses P" "b |\<in>| finite_varied_clause_registered \<kappa> d T z"
    unfolding finite_varied_registered_def if_P[OF guard] finite_union_image_member by blast
  obtain d' c S where zs: "z = ((d',c),S)" by (metis prod.collapse)
  show "(\<exists>c'. ((d,c'),T) |\<in>| finite_system_clauses N) \<and>
    (\<exists>c S f h x. ((d,c),S) |\<in>| finite_system_clauses P \<and> finite_schema_match S T = Some (f,h) \<and>
      x |\<in>| witness_registered \<kappa> d S \<and> x |\<in>| finite_schema_variables S \<and> b = f x)"
    using guard[unfolded finite_clause_site_member] z(1)[unfolded zs]
      z(2)[unfolded zs finite_varied_clause_registered_member] by blast
next
  assume "(\<exists>c'. ((d,c'),T) |\<in>| finite_system_clauses N) \<and>
    (\<exists>c S f h x. ((d,c),S) |\<in>| finite_system_clauses P \<and> finite_schema_match S T = Some (f,h) \<and>
      x |\<in>| witness_registered \<kappa> d S \<and> x |\<in>| finite_schema_variables S \<and> b = f x)"
  then obtain c' c S f h x where N: "((d,c'),T) |\<in>| finite_system_clauses N"
    and S: "((d,c),S) |\<in>| finite_system_clauses P" "finite_schema_match S T = Some (f,h)"
      "x |\<in>| witness_registered \<kappa> d S" "x |\<in>| finite_schema_variables S" "b = f x" by blast
  have guard: "(d,T) |\<in>| fimage (\<lambda>z. (fst (fst z),snd z)) (finite_system_clauses N)"
    unfolding finite_clause_site_member using N by blast
  have "b |\<in>| finite_varied_clause_registered \<kappa> d T ((d,c),S)"
    unfolding finite_varied_clause_registered_member using S(2-5) by blast
  then show "b |\<in>| finite_varied_registered P N \<kappa> d T"
    unfolding finite_varied_registered_def finite_union_image_member if_P[OF guard] using S(1) by blast
qed

lemma finite_varied_values_member:
  "w |\<in>| finite_varied_values P \<kappa> d T B b \<longleftrightarrow> (\<exists>c S f h x. ((d,c),S) |\<in>| finite_system_clauses P \<and>
    finite_schema_match S T = Some (f,h) \<and> x |\<in>| witness_registered \<kappa> d S \<and> x |\<in>| finite_schema_variables S \<and>
    f x = b \<and> w = witness_value \<kappa> P d S (finite_bindings_carried_back f (finite_schema_variables S) B) x)"
proof
  assume "w |\<in>| finite_varied_values P \<kappa> d T B b"
  then show "\<exists>c S f h x. ((d,c),S) |\<in>| finite_system_clauses P \<and>
    finite_schema_match S T = Some (f,h) \<and> x |\<in>| witness_registered \<kappa> d S \<and> x |\<in>| finite_schema_variables S \<and>
    f x = b \<and> w = witness_value \<kappa> P d S (finite_bindings_carried_back f (finite_schema_variables S) B) x"
    unfolding finite_varied_values_def finite_union_image_member
    by (auto simp: fimage.rep_eq ffilter.rep_eq split: if_splits option.splits prod.splits)
next
  assume "\<exists>c S f h x. ((d,c),S) |\<in>| finite_system_clauses P \<and>
    finite_schema_match S T = Some (f,h) \<and> x |\<in>| witness_registered \<kappa> d S \<and> x |\<in>| finite_schema_variables S \<and>
    f x = b \<and> w = witness_value \<kappa> P d S (finite_bindings_carried_back f (finite_schema_variables S) B) x"
  then obtain c S f h x where S: "((d,c),S) |\<in>| finite_system_clauses P" "finite_schema_match S T = Some (f,h)"
    "x |\<in>| witness_registered \<kappa> d S" "x |\<in>| finite_schema_variables S" "f x = b"
    "w = witness_value \<kappa> P d S (finite_bindings_carried_back f (finite_schema_variables S) B) x" by blast
  have "w |\<in>| fimage (\<lambda>x. witness_value \<kappa> P d S (finite_bindings_carried_back f (finite_schema_variables S) B) x)
      (ffilter (\<lambda>x. f x = b) (witness_registered \<kappa> d S |\<inter>| finite_schema_variables S))"
    unfolding S(6) by (rule fimageI) (simp add: S(3-5) ffilter.rep_eq)
  then show "w |\<in>| finite_varied_values P \<kappa> d T B b"
    unfolding finite_varied_values_def finite_union_image_member using S(1,2)
    by (intro exI[of _ "((d,c),S)"]) simp
qed

lemma finite_varied_construction_registered [simp]:
  "witness_registered (finite_varied_construction P N \<kappa>) = finite_varied_registered P N \<kappa>"
  by (simp add: finite_varied_construction_def)

lemma finite_varied_construction_value:
  assumes "witness_value (finite_varied_construction P N \<kappa>) Q d T B b = Some v"
  shows "\<exists>c S f h x. ((d,c),S) |\<in>| finite_system_clauses P \<and> finite_schema_match S T = Some (f,h) \<and>
    x |\<in>| witness_registered \<kappa> d S \<and> x |\<in>| finite_schema_variables S \<and> f x = b \<and>
    witness_value \<kappa> P d S (finite_bindings_carried_back f (finite_schema_variables S) B) x = Some v"
proof -
  let ?Vs = "finite_varied_values P \<kappa> d T B b"
  have single: "?Vs = {|fthe_elem ?Vs|}" and elem: "fthe_elem ?Vs = Some v"
    using assms by (simp_all add: finite_varied_construction_def Let_def split: if_splits)
  have "Some v |\<in>| ?Vs" using single elem by (metis finsertI1)
  then show ?thesis unfolding finite_varied_values_member by metis
qed

section \<open>Formation and what the variation registers\<close>



lemma finite_varied_construction_formed:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
  shows "finite_witness_construction_formed (finite_varied_construction P N \<kappa>)"
  unfolding finite_witness_construction_formed_def
proof (intro allI impI)
  fix Q d T B b v assume "witness_value (finite_varied_construction P N \<kappa>) Q d T B b = Some v"
  from finite_varied_construction_value[OF this] obtain S B' x where "witness_value \<kappa> P d S B' x = Some v" by blast
  then show "finite_term_formed v" using \<kappa> unfolding finite_witness_construction_formed_def by blast
qed

lemma finite_varied_registered_clause:
  assumes "b |\<in>| witness_registered (finite_varied_construction P N \<kappa>) d T"
  shows "\<exists>c. ((d,c),T) |\<in>| finite_system_clauses N"
  using assms by (simp add: finite_varied_registered_member)

text \<open>
  Every variable of a clause's scope the construction registers at a clause of P is registered at each clause of N
  at the same site the match sends that clause to, at its image under the match's binder map.
\<close>

lemma finite_varied_registered_reaches:
  assumes "((d,c),S) |\<in>| finite_system_clauses P" "((d,c'),T) |\<in>| finite_system_clauses N"
    and "finite_schema_match S T = Some (f,h)" "x |\<in>| witness_registered \<kappa> d S" "x |\<in>| finite_schema_variables S"
  shows "f x |\<in>| witness_registered (finite_varied_construction P N \<kappa>) d T"
  unfolding finite_varied_construction_registered finite_varied_registered_member using assms by blast

text \<open>
  At programs whose clause families at a site are variants, every registration within a clause's scope reaches N:
  each clause of P has an alpha variant among N's clauses at its site, which the match finds.
\<close>

lemma finite_varied_registered_variant:
  assumes source: "finite_system_formed P" and target: "finite_system_formed N"
    and family: "schema_family_variant k (system_clause_family (decode_finite_system P) d)
      (system_clause_family (decode_finite_system N) d)"
    and clause: "((d,c),S) |\<in>| finite_system_clauses P"
    and registered: "x |\<in>| witness_registered \<kappa> d S" "x |\<in>| finite_schema_variables S"
  shows "\<exists>c' T f h. ((d,c'),T) |\<in>| finite_system_clauses N \<and> finite_schema_match S T = Some (f,h) \<and>
    f x |\<in>| witness_registered (finite_varied_construction P N \<kappa>) d T"
proof -
  have "(c,decode_finite_schema S) \<in> system_clause_family (decode_finite_system P) d" using clause by auto
  then obtain T0 where T0: "(k c,T0) \<in> system_clause_family (decode_finite_system N) d"
      "schema_alpha_variant (decode_finite_schema S) T0"
    using schema_family_variant_entry[OF family] by blast
  then obtain T where T: "((d,k c),T) |\<in>| finite_system_clauses N" "T0 = decode_finite_schema T" by auto
  have "finite_schema_match S T \<noteq> None"
    using finite_schema_match_exact(2)[OF finite_system_formed_parts(2)[OF source clause]
      finite_system_formed_parts(2)[OF target T(1)]] T0(2) T(2) by simp
  then obtain f h where m: "finite_schema_match S T = Some (f,h)" by auto
  show ?thesis using finite_varied_registered_reaches[OF clause T(1) m registered] T(1) m by blast
qed

section \<open>The premises holding a variable, along a match\<close>

lemma resolution_value_carried:
  assumes "\<And>y. y |\<in>| finite_pattern_variables p \<Longrightarrow> \<theta> (f y) = \<psi> y"
  shows "resolution_value \<theta> (map_finite_term_pattern f p) = resolution_value \<psi> p"
  unfolding resolution_value_rename by (rule resolution_value_cong) (simp add: assms)

lemma finite_material_carried:
  fixes f :: "'a \<Rightarrow> 'b" and M :: "'a finite_material_pattern"
  assumes agreeing: "\<And>y. y |\<in>| finite_material_variables M \<Longrightarrow> \<theta> (f y) = \<psi> y"
  shows "finite_material_ground_satisfied (finite_material_pattern_substitute
        (\<lambda>z. finite_exact_term_pattern (\<theta> z) :: 'b finite_term_pattern) (finite_rename_material f M)) \<longleftrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute
        (\<lambda>z. finite_exact_term_pattern (\<psi> z) :: 'a finite_term_pattern) M)"
proof -
  have fields: "resolution_value \<theta> (map_finite_term_pattern f (finite_material_source M)) =
        resolution_value \<psi> (finite_material_source M)"
      "resolution_value \<theta> (map_finite_term_pattern f (finite_material_atoms M)) =
        resolution_value \<psi> (finite_material_atoms M)"
      "resolution_value \<theta> (map_finite_term_pattern f (finite_material_edges M)) =
        resolution_value \<psi> (finite_material_edges M)"
      "resolution_value \<theta> (map_finite_term_pattern f (finite_material_counts M)) =
        resolution_value \<psi> (finite_material_counts M)"
      "resolution_value \<theta> (map_finite_term_pattern f (finite_material_functions M)) =
        resolution_value \<psi> (finite_material_functions M)"
    using agreeing by (auto intro!: resolution_value_carried simp: finite_material_variables_def)
  show ?thesis by (simp add: finite_material_ground_satisfied_values finite_rename_material_def fields)
qed

context finite_schema_matched
begin

text \<open>
  The premises of T holding the image of a variable x of S's scope are the images of the premises of S holding x.
  Where the valuations agree through f on the variables of those premises and the two programs mean the same at
  their callees, the premises holding f x hold in N exactly when those holding x hold in P. This is the reading of
  @{const finite_variable_premises_hold} along a match, stated once.
\<close>

lemma premises_carried:
  assumes x: "x \<in> schema_variables (decode_finite_schema S)"
    and agree: "\<And>s e p y. (s,e,p) |\<in>| finite_schema_premises S \<Longrightarrow>
      (e,y) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (e,y) \<in> positive_meaning (decode_finite_system P)"
    and call_values: "\<And>s e p y. (s,e,p) |\<in>| finite_schema_premises S \<Longrightarrow> x |\<in>| finite_pattern_variables p \<Longrightarrow>
      y |\<in>| finite_pattern_variables p \<Longrightarrow> \<theta> (f y) = \<psi> y"
    and material_values: "\<And>s M y. (s,M) |\<in>| finite_schema_materials S \<Longrightarrow> x |\<in>| finite_material_variables M \<Longrightarrow>
      y |\<in>| finite_material_variables M \<Longrightarrow> \<theta> (f y) = \<psi> y"
  shows "finite_variable_premises_hold N T (f x) \<theta> \<longleftrightarrow> finite_variable_premises_hold P S x \<psi>"
proof
  assume H: "finite_variable_premises_hold N T (f x) \<theta>"
  show "finite_variable_premises_hold P S x \<psi>"
    unfolding finite_variable_premises_hold_def
  proof (intro conjI allI impI)
    fix s e p assume sp: "(s,e,p) |\<in>| finite_schema_premises S" and xp: "x |\<in>| finite_pattern_variables p"
    have tp: "(h s,e,map_finite_term_pattern f p) |\<in>| finite_schema_premises T" by (rule call[OF sp])
    have fx: "f x |\<in>| finite_pattern_variables (map_finite_term_pattern f p)" using call_variable[OF sp x] xp by simp
    have "(e,decode_finite_term (resolution_value \<theta> (map_finite_term_pattern f p))) \<in>
        positive_meaning (decode_finite_system N)"
      using H tp fx unfolding finite_variable_premises_hold_def by blast
    moreover have "resolution_value \<theta> (map_finite_term_pattern f p) = resolution_value \<psi> p"
      by (rule resolution_value_carried) (rule call_values[OF sp xp])
    ultimately show "(e,decode_finite_term (resolution_value \<psi> p)) \<in> positive_meaning (decode_finite_system P)"
      using agree[OF sp] by simp
  next
    fix s Mt assume sM: "(s,Mt) |\<in>| finite_schema_materials S" and xM: "x |\<in>| finite_material_variables Mt"
    have tM: "(h s,finite_rename_material f Mt) |\<in>| finite_schema_materials T" by (rule material[OF sM])
    have fx: "f x |\<in>| finite_material_variables (finite_rename_material f Mt)"
      using material_variable[OF sM x] xM by simp
    have "finite_material_ground_satisfied (finite_material_pattern_substitute
        (\<lambda>z. finite_exact_term_pattern (\<theta> z) :: 'b finite_term_pattern) (finite_rename_material f Mt))"
      using H tM fx unfolding finite_variable_premises_hold_def by blast
    then show "finite_material_ground_satisfied (finite_material_pattern_substitute
        (\<lambda>z. finite_exact_term_pattern (\<psi> z) :: 'a finite_term_pattern) Mt)"
      using finite_material_carried[where \<theta>=\<theta> and \<psi>=\<psi> and f=f and M=Mt, OF material_values[OF sM xM]]
      by blast
  qed
next
  assume H: "finite_variable_premises_hold P S x \<psi>"
  show "finite_variable_premises_hold N T (f x) \<theta>"
    unfolding finite_variable_premises_hold_def
  proof (intro conjI allI impI)
    fix t e q assume tq: "(t,e,q) |\<in>| finite_schema_premises T" and xq: "f x |\<in>| finite_pattern_variables q"
    obtain s p where sp: "(s,e,p) |\<in>| finite_schema_premises S" and q: "t = h s" "q = map_finite_term_pattern f p"
      using call_origin[OF tq] by blast
    have xp: "x |\<in>| finite_pattern_variables p" using call_variable[OF sp x] xq q(2) by simp
    have "(e,decode_finite_term (resolution_value \<psi> p)) \<in> positive_meaning (decode_finite_system P)"
      using H sp xp unfolding finite_variable_premises_hold_def by blast
    moreover have "resolution_value \<theta> (map_finite_term_pattern f p) = resolution_value \<psi> p"
      by (rule resolution_value_carried) (rule call_values[OF sp xp])
    ultimately show "(e,decode_finite_term (resolution_value \<theta> q)) \<in> positive_meaning (decode_finite_system N)"
      using agree[OF sp] q(2) by simp
  next
    fix t Nt assume tN: "(t,Nt) |\<in>| finite_schema_materials T" and xN: "f x |\<in>| finite_material_variables Nt"
    obtain s Mt where sM: "(s,Mt) |\<in>| finite_schema_materials S" and N: "t = h s" "Nt = finite_rename_material f Mt"
      using material_origin[OF tN] by blast
    have xM: "x |\<in>| finite_material_variables Mt" using material_variable[OF sM x] xN N(2) by simp
    have "finite_material_ground_satisfied (finite_material_pattern_substitute
        (\<lambda>z. finite_exact_term_pattern (\<psi> z) :: 'a finite_term_pattern) Mt)"
      using H sM xM unfolding finite_variable_premises_hold_def by blast
    then show "finite_material_ground_satisfied (finite_material_pattern_substitute
        (\<lambda>z. finite_exact_term_pattern (\<theta> z) :: 'b finite_term_pattern) Nt)"
      using finite_material_carried[where \<theta>=\<theta> and \<psi>=\<psi> and f=f and M=Mt, OF material_values[OF sM xM]] N(2)
      by blast
  qed
qed

end

section \<open>Completeness at the varied program\<close>

text \<open>
  The two programs mean the same at the callees of the matched clauses: at every premise of a clause of P matched
  to a clause of N at its site. Alpha variants mean the same everywhere (@{thm [source] system_alpha_positive_meaning}).
\<close>

definition finite_varied_meanings_agree ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('b,'t::linorder,'d,'e) finite_schema_system \<Rightarrow> bool" where
  "finite_varied_meanings_agree P N \<longleftrightarrow> (\<forall>d c S c' T f h s e p y. ((d,c),S) |\<in>| finite_system_clauses P \<longrightarrow>
    ((d,c'),T) |\<in>| finite_system_clauses N \<longrightarrow> finite_schema_match S T = Some (f,h) \<longrightarrow>
    (s,e,p) |\<in>| finite_schema_premises S \<longrightarrow>
    ((e,y) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (e,y) \<in> positive_meaning (decode_finite_system P)))"

lemma finite_varied_meanings_agree_variant:
  assumes "system_alpha_variant (decode_finite_system P) (decode_finite_system N)"
  shows "finite_varied_meanings_agree P N"
  by (simp add: finite_varied_meanings_agree_def system_alpha_positive_meaning[OF assms])


theorem varied_construction_complete:
  assumes source: "finite_system_formed P" and target: "finite_system_formed N"
    and complete: "finite_construction_complete \<kappa> P"
    and agree: "finite_varied_meanings_agree P N"
  shows "finite_construction_complete (finite_varied_construction P N \<kappa>) N"
  unfolding finite_construction_complete_def
proof (intro allI impI conjI)
  fix d c T b
  assume clause: "((d,c),T) |\<in>| finite_system_clauses N"
    and reg: "b |\<in>| witness_registered (finite_varied_construction P N \<kappa>) d T"
  obtain c1 S f h x where S: "((d,c1),S) |\<in>| finite_system_clauses P" "finite_schema_match S T = Some (f,h)"
    "x |\<in>| witness_registered \<kappa> d S" "x |\<in>| finite_schema_variables S" "b = f x"
    using reg by (auto simp: finite_varied_registered_member)
  interpret M: finite_schema_matched S T f h
    by unfold_locales (fact finite_system_formed_parts(2)[OF source S(1)] finite_system_formed_parts(2)[OF target clause] S(2))+
  have xS: "x \<in> schema_variables (decode_finite_schema S)" using S(4) by (simp add: finite_schema_variables_correct)
  have "x |\<notin>| finite_pattern_variables (finite_schema_conclusion S)"
    using complete S(1,3) unfolding finite_construction_complete_def by blast
  then show "b |\<notin>| finite_pattern_variables (finite_schema_conclusion T)"
    using M.conclusion_variable[OF xS] S(5) by simp
next
  fix d c T b
  assume clause: "((d,c),T) |\<in>| finite_system_clauses N"
  show "finite_value_complete N T b (\<lambda>B. witness_value (finite_varied_construction P N \<kappa>) N d T B b)"
    unfolding finite_value_complete_def
  proof (intro allI impI)
    fix B v
    assume fn: "finite_relation_functional B" and bf: "fBall B (\<lambda>(b,t). finite_term_formed t)"
      and free: "b |\<notin>| fimage fst B" and bound: "finite_variable_premises_bound T b (fimage fst B)"
      and val: "witness_value (finite_varied_construction P N \<kappa>) N d T B b = Some v"
    obtain c1 S f h x where S: "((d,c1),S) |\<in>| finite_system_clauses P" "finite_schema_match S T = Some (f,h)"
      "x |\<in>| witness_registered \<kappa> d S" "x |\<in>| finite_schema_variables S" "f x = b"
      "witness_value \<kappa> P d S (finite_bindings_carried_back f (finite_schema_variables S) B) x = Some v"
      using finite_varied_construction_value[OF val] by blast
    interpret M: finite_schema_matched S T f h
      by unfold_locales (fact finite_system_formed_parts(2)[OF source S(1)] finite_system_formed_parts(2)[OF target clause] S(2))+
    define B' where "B' = finite_bindings_carried_back f (finite_schema_variables S) B"
    have B'_mem: "(y,t) |\<in>| B' \<longleftrightarrow> y \<in> schema_variables (decode_finite_schema S) \<and> (f y,t) |\<in>| B" for y t
      by (simp add: B'_def finite_bindings_carried_back_member finite_schema_variables_correct)
    have xS: "x \<in> schema_variables (decode_finite_schema S)" using S(4) by (simp add: finite_schema_variables_correct)
    have agreeS: "(e,y) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (e,y) \<in> positive_meaning (decode_finite_system P)"
      if "(s,e,p) |\<in>| finite_schema_premises S" for s e p y
      using agree S(1) clause S(2) that unfolding finite_varied_meanings_agree_def by blast
    have fn': "finite_relation_functional B'"
      unfolding finite_relation_functional_correct single_valued_def
    proof (intro allI impI)
      fix y t u assume "(y,t) \<in> fset B'" "(y,u) \<in> fset B'"
      then have "(f y,t) |\<in>| B" "(f y,u) |\<in>| B" using B'_mem by blast+
      then show "t = u" using fn unfolding finite_relation_functional_correct single_valued_def by blast
    qed
    have bf': "fBall B' (\<lambda>(y,t). finite_term_formed t)"
    proof (rule fBallI)
      fix z assume z: "z |\<in>| B'"
      obtain y t where zyt: "z = (y,t)" by (cases z)
      have "(f y,t) |\<in>| B" using z zyt B'_mem by blast
      then have "(\<lambda>(b,t). finite_term_formed t) (f y,t)" by (rule fbspec[OF bf])
      then show "(\<lambda>(y,t). finite_term_formed t) z" using zyt by simp
    qed
    have free': "x |\<notin>| fimage fst B'"
    proof
      assume "x |\<in>| fimage fst B'"
      then have "\<exists>t. (x,t) |\<in>| B'" by (simp only: finite_fst_member)
      then obtain t where "(x,t) |\<in>| B'" ..
      then have "(b,t) |\<in>| B" using B'_mem[of x t] S(5) by simp
      then show False using free fimageI[of "(b,t)" B fst] by simp
    qed
    have key: "y |\<in>| fimage fst B'" if "f y |\<in>| fimage fst B" "y \<in> schema_variables (decode_finite_schema S)" for y
    proof -
      have "\<exists>t. (f y,t) |\<in>| B" using that(1) by (simp only: finite_fst_member)
      then obtain t where "(f y,t) |\<in>| B" ..
      then have "(y,t) |\<in>| B'" using B'_mem[of y t] that(2) by simp
      from fimageI[OF this, of fst] show ?thesis by simp
    qed
    have ne: "f y \<noteq> b" if "y \<in> schema_variables (decode_finite_schema S)" "y \<noteq> x" for y
      using inj_onD[OF M.binders _ that(1) xS] that(2) S(5) by metis
    have bound': "finite_variable_premises_bound S x (fimage fst B')"
      unfolding finite_variable_premises_bound_def
    proof (intro conjI allI impI)
      fix s e p assume sp: "(s,e,p) |\<in>| finite_schema_premises S" and xp: "x |\<in>| finite_pattern_variables p"
      show "finite_pattern_variables p |\<subseteq>| finsert x (fimage fst B')"
      proof (rule fsubsetI)
        fix y assume yp: "y |\<in>| finite_pattern_variables p"
        show "y |\<in>| finsert x (fimage fst B')"
        proof (cases "y = x")
          case False
          have yS: "y \<in> schema_variables (decode_finite_schema S)" using M.call_scope[OF sp] yp by auto
          have tp: "(h s,e,map_finite_term_pattern f p) |\<in>| finite_schema_premises T" by (rule M.call[OF sp])
          have held: "b |\<in>| finite_pattern_variables (map_finite_term_pattern f p)"
            using M.call_variable[OF sp xS] xp S(5) by simp
          have fy: "f y |\<in>| finite_pattern_variables (map_finite_term_pattern f p)"
            using M.call_variable[OF sp yS] yp by simp
          have "f y |\<in>| fimage fst B"
            by (rule finite_variable_premises_bound_premise[OF bound tp held fy ne[OF yS False]])
          then show ?thesis using key[OF _ yS] by simp
        qed simp
      qed
    next
      fix s Mt assume sM: "(s,Mt) |\<in>| finite_schema_materials S" and xM: "x |\<in>| finite_material_variables Mt"
      show "finite_material_variables Mt |\<subseteq>| finsert x (fimage fst B')"
      proof (rule fsubsetI)
        fix y assume yM: "y |\<in>| finite_material_variables Mt"
        show "y |\<in>| finsert x (fimage fst B')"
        proof (cases "y = x")
          case False
          have yS: "y \<in> schema_variables (decode_finite_schema S)" using M.material_scope[OF sM] yM by auto
          have tM: "(h s,finite_rename_material f Mt) |\<in>| finite_schema_materials T" by (rule M.material[OF sM])
          have held: "b |\<in>| finite_material_variables (finite_rename_material f Mt)"
            using M.material_variable[OF sM xS] xM S(5) by simp
          have fy: "f y |\<in>| finite_material_variables (finite_rename_material f Mt)"
            using M.material_variable[OF sM yS] yM by simp
          have sub: "finite_material_variables (finite_rename_material f Mt) |\<subseteq>| finsert b (fimage fst B)"
            using bound tM held unfolding finite_variable_premises_bound_def by blast
          have "f y |\<in>| fimage fst B" using fsubsetD[OF sub fy] ne[OF yS False] by simp
          then show ?thesis using key[OF _ yS] by simp
        qed simp
      qed
    qed
    have agree_at: "((finite_binding_valuation B)(b:=w)) (f y) = ((finite_binding_valuation B')(x:=w)) y"
      if "y |\<in>| finsert x (fimage fst B')" for w y
    proof (cases "y = x")
      case True
      then show ?thesis using S(5) by simp
    next
      case False
      have "y |\<in>| fimage fst B'" using that False by simp
      then have "\<exists>t. (y,t) |\<in>| B'" by (simp only: finite_fst_member)
      then obtain t where yt: "(y,t) |\<in>| B'" ..
      have fyt: "(f y,t) |\<in>| B" and yS: "y \<in> schema_variables (decode_finite_schema S)"
        using yt B'_mem[of y t] by simp_all
      show ?thesis using ne[OF yS False] False finite_binding_valuation_member[OF fn fyt]
          finite_binding_valuation_member[OF fn' yt] by simp
    qed
    have call_values: "((finite_binding_valuation B)(b:=w)) (f y) = ((finite_binding_valuation B')(x:=w)) y"
      if "(s,e,p) |\<in>| finite_schema_premises S" "x |\<in>| finite_pattern_variables p" "y |\<in>| finite_pattern_variables p"
      for w s e p y
    proof -
      have "finite_pattern_variables p |\<subseteq>| finsert x (fimage fst B')"
        using bound' that(1,2) unfolding finite_variable_premises_bound_def by blast
      then show ?thesis by (rule agree_at[OF fsubsetD[OF _ that(3)]])
    qed
    have material_values: "((finite_binding_valuation B)(b:=w)) (f y) = ((finite_binding_valuation B')(x:=w)) y"
      if "(s,Mt) |\<in>| finite_schema_materials S" "x |\<in>| finite_material_variables Mt"
        "y |\<in>| finite_material_variables Mt" for w s Mt y
    proof -
      have "finite_material_variables Mt |\<subseteq>| finsert x (fimage fst B')"
        using bound' that(1,2) unfolding finite_variable_premises_bound_def by blast
      then show ?thesis by (rule agree_at[OF fsubsetD[OF _ that(3)]])
    qed
    have iff: "finite_variable_premises_hold N T (f x) ((finite_binding_valuation B)(b:=w)) \<longleftrightarrow>
        finite_variable_premises_hold P S x ((finite_binding_valuation B')(x:=w))" for w
      by (rule M.premises_carried[OF xS]) (erule agreeS, erule (2) call_values, erule (2) material_values)
    have cS: "finite_value_complete P S x (\<lambda>B. witness_value \<kappa> P d S B x)"
      using complete S(1,3) unfolding finite_construction_complete_def by blast
    have iffS: "(\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P S x ((finite_binding_valuation B')(x:=w))) \<longleftrightarrow>
        finite_variable_premises_hold P S x ((finite_binding_valuation B')(x:=v))"
      using cS fn' bf' free' bound' S(6)[folded B'_def] unfolding finite_value_complete_def by blast
    show "(\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold N T b ((finite_binding_valuation B)(b:=w))) \<longleftrightarrow>
        finite_variable_premises_hold N T b ((finite_binding_valuation B)(b:=v))"
      using iffS iff S(5) by simp
  qed
qed

corollary varied_construction_complete_variant:
  assumes variant: "system_alpha_variant (decode_finite_system P) (decode_finite_system N)"
    and complete: "finite_construction_complete \<kappa> P"
  shows "finite_construction_complete (finite_varied_construction P N \<kappa>) N"
proof -
  have "finite_system_formed P" "finite_system_formed N"
    using variant by (simp_all add: system_alpha_variant_def finite_system_formed_correct)
  then show ?thesis
    by (rule varied_construction_complete[OF _ _ complete finite_varied_meanings_agree_variant[OF variant]])
qed

section \<open>The exact forms at the varied program\<close>

text \<open>
  The committed forms at no commitment over the varied construction, its formation discharged by the source's and
  its completeness by @{text varied_construction_complete}: resolved, the call holds in N; refuted, it does not.
\<close>

lemmas varied_complete_resolution_refutation_exact =
  finite_complete_resolution_refutation_exact[OF finite_varied_construction_formed varied_construction_complete]

lemmas varied_complete_verdict_exact =
  finite_complete_verdict_exact[OF finite_varied_construction_formed varied_construction_complete]

lemmas varied_complete_demand_exact =
  finite_complete_demand_exact[OF finite_varied_construction_formed varied_construction_complete]

lemmas native_varied_resolution_exact =
  native_complete_resolution_exact[OF finite_varied_construction_formed varied_construction_complete]

section \<open>After the relocation, in a finite mapped extension\<close>

text \<open>
  The relocation carries a construction complete at the numbered Q to the placed program (@{text
  relocated_construction_complete}); the installation reads at its result a package that is an alpha variant of the
  placed program, and any finite program whose decoding the installed site reads is that package
  (@{thm [source] native_package_unique}). The construction varied from the placed program to that finite program is
  complete there.
\<close>

context finite_mapped_native_extension
begin

lemma installed_variant:
  assumes result: "finite_extend_mapped_native E P Q g = Some (F,u)"
    and read: "native_package_at (decode_finite_environment F) u [] (decode_finite_system R)"
  shows "system_alpha_variant (decode_finite_system goal) (decode_finite_system R)"
proof -
  obtain T where T: "native_package_at (decode_finite_environment F) u [] T"
      "system_alpha_variant (rename_system placement (decode_finite_system Q)) T"
    using correct[OF result] by blast
  have "T = decode_finite_system R" by (rule native_package_unique[OF T(1) read])
  then show ?thesis using T(2) by simp
qed

theorem varied_relocated_complete:
  fixes R :: "(local_address,local_address,local_address option definition_site,local_address) finite_schema_system"
  assumes result: "finite_extend_mapped_native E P Q g = Some (F,u)"
    and read: "native_package_at (decode_finite_environment F) u [] (decode_finite_system R)"
    and complete: "finite_construction_complete \<kappa> Q"
  shows "finite_construction_complete (finite_varied_construction goal R (finite_relocated_construction placement Q \<kappa>)) R"
  by (rule varied_construction_complete_variant[OF installed_variant[OF result read]
    relocated_construction_complete[OF complete]])

lemmas native_varied_relocated_resolution_exact =
  native_complete_resolution_exact[OF finite_varied_construction_formed[OF finite_relocated_construction_formed]
    varied_relocated_complete]

end

end
