theory Development_Installed_Presentations_Execution
  imports Development_Installed_Presentations Native_Execution_Refinements
begin

text \<open>
  The control of V3 (task 657) of DECISIONS.md "A checker does not produce", its addition "Registrations and
  declarations reach an installed package by matching its clauses against the placed ones": one evaluation, compiled
  once, over the native package reader's refinements, in a thin theory no theory imports. It reads back the three
  installed presentations the route evaluates (the given's readers', the asked relation's installed guard, the first
  request's installed program), each read-back timed apart from its installation, and at 77, 392, 525 and 561, each
  where its numbered program holds it, it finds the match between every placed clause the given's registrations name
  and the installed clauses at its site, and compares what V3's varied construction registers there with what the
  relocated construction registers at the placed clause. The constructions compared are V3's by their definitions
  (@{const given_installed_construction}, @{text given_readers_extension.installed_construction}): the placed program
  renamed by the installation's placement, the relocated construction of @{const given_witness_registrations}, varied
  from the placed program to the presentation the reader returns. The control reads the clauses and changes none; it
  decides nothing for the route.
\<close>

text \<open>
  The two extensions' installations are evaluated by the code equations their own theories state
  (@{thm [source] asked_installation_code}, @{thm [source] first_request_installation_code}).
\<close>

section \<open>The match at one registered site\<close>

text \<open>
  At a site e of the placed program P and the installed presentation N, with the relocated construction \<kappa> over P and
  its variation \<kappa>' to N: the placed and installed clauses at e; the placed clauses at which \<kappa> registers a variable
  of their scope, with the sizes of what it registers; whether each such clause's match finds exactly one installed
  clause at e; whether \<kappa>' registers at each installed clause found exactly the images, under the match's binder map,
  of what \<kappa> registers at the placed clause; whether each installed clause found is matched by exactly one placed
  clause at e, so that no pair of distinct alpha-equal placed clauses stands there, where the variation would give no
  value; and whether \<kappa>' registers at no installed clause at e that no registered placed clause matches.
\<close>

definition installed_match_site where
  "installed_match_site P N \<kappa> \<kappa>' e=(let
    placed=ffilter (\<lambda>((d,c),S). d=e) (finite_system_clauses P);
    installed=ffilter (\<lambda>((d,c),T). d=e) (finite_system_clauses N);
    registered=(\<lambda>S. witness_registered \<kappa> e S |\<inter>| finite_schema_variables S);
    sources=ffilter (\<lambda>((d,c),S). registered S\<noteq>{||}) placed;
    matches=(\<lambda>S. ffilter (\<lambda>((d,c),T). finite_schema_match S T\<noteq>None) installed);
    matched=(\<lambda>T. ffilter (\<lambda>((d,c),S). finite_schema_match S T\<noteq>None) placed);
    carried=(\<lambda>S T. case finite_schema_match S T of None \<Rightarrow> False
      | Some (f,h) \<Rightarrow> witness_registered \<kappa>' e T=fimage f (registered S)) in
    ((integer_of_nat (fcard placed),integer_of_nat (fcard installed)),integer_of_nat (fcard sources),
      map integer_of_nat (sorted_list_of_fset (fimage (\<lambda>((d,c),S). fcard (registered S)) sources)),
      fBall sources (\<lambda>((d,c),S). fcard (matches S)=1),
      fBall sources (\<lambda>((d,c),S). fBall (matches S) (\<lambda>((d',c'),T). carried S T)),
      fBall sources (\<lambda>((d,c),S). fBall (matches S) (\<lambda>((d',c'),T). fcard (matched T)=1)),
      fBall installed (\<lambda>((d,c),T). witness_registered \<kappa>' e T\<noteq>{||} \<longrightarrow>
        fBex sources (\<lambda>((d',c'),S). finite_schema_match S T\<noteq>None))))"

text \<open>
  The report of an installation with placement g of the numbered program Q, at the presentation N the reader
  returned: at every site of ks that Q defines, the match at its placement, over V3's constructions.
\<close>

definition installed_match_report :: "(nat \<Rightarrow> local_address option definition_site) \<Rightarrow>
    (nat,nat,nat,nat) finite_schema_system \<Rightarrow> local_address option finite_native_system \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow>
    (integer\<times>(integer\<times>integer)\<times>integer\<times>integer list\<times>bool\<times>bool\<times>bool\<times>bool) list" where
  "installed_match_report g Q N n ks=(let P=finite_rename_system g Q;
    \<kappa>=finite_relocated_construction g Q (finite_collection_construction given_witness_registrations (nat_of_integer n));
    \<kappa>'=finite_varied_construction P N \<kappa> in
    map (\<lambda>k. (integer_of_nat k,installed_match_site P N \<kappa> \<kappa>' (g k)))
      (filter (\<lambda>k. k |\<in>| finite_system_definitions Q) (map nat_of_integer ks)))"

text \<open>The read-back at an installed environment and site, and what the control reports of it.\<close>

definition installed_readings :: "local_address option finite_artifact_environment \<Rightarrow> local_address option \<Rightarrow>
    local_address option finite_native_system fset" where
  "installed_readings E u=finite_native_package_readings E u []"

definition installed_reading_count :: "local_address option finite_native_system fset \<Rightarrow> integer" where
  "installed_reading_count R=integer_of_nat (fcard R)"

definition installed_reading :: "local_address option finite_native_system fset \<Rightarrow> local_address option finite_native_system" where
  "installed_reading R=fthe_elem R"

definition installed_definition_count :: "local_address option finite_native_system \<Rightarrow> integer" where
  "installed_definition_count N=integer_of_nat (fcard (finite_system_definitions N))"

section \<open>The evaluation\<close>

text \<open>
  One @{text ML} block compiles every constant once. The three installations are values of the compiled code, made as
  it is compiled, so no read-back's time holds its installation. Each
  presentation is read back at its installed environment and site by the native package reader, timed apart, and must
  be the only reading there; the match report at each is timed beside it. A match not found, a registration not
  carried exactly, an installed clause matched by two placed clauses, or a registration outside the matched clauses
  refuses the theory.
\<close>

ML \<open>
structure Installed_Presentations_Execution =
struct
  fun timed label f x =
    let val (t, r) = Timing.timing f x
    in (writeln ("INSTALLED PRESENTATIONS " ^ label ^ ": " ^ Timing.message t); r) end
  val readings = @{code installed_readings}
  val count = @{code installed_reading_count}
  val the_reading = @{code installed_reading}
  val definitions = @{code installed_definition_count}
  val report = @{code installed_match_report}
  val sites = [77, 392, 525, 561]
  val bound = 40
  fun read label (env, use) =
    let
      val rs = timed (label ^ " read back") (fn () => readings env use) ()
      val n = count rs
      val _ = if n = 1 then () else error ("INSTALLED PRESENTATIONS " ^ label ^ ": " ^ IntInf.toString n ^ " readings")
      val p = the_reading rs
      val _ = writeln ("INSTALLED PRESENTATIONS " ^ label ^ ": " ^ IntInf.toString (definitions p) ^
        " definitions read back")
    in p end
  fun flag b = if b then "yes" else "NO"
  fun site label (k, ((p, i), (r, (sizes, (found, (exact, (single, elsewhere))))))) =
    (writeln ("INSTALLED PRESENTATIONS " ^ label ^ " at " ^ IntInf.toString k ^ ": placed clauses " ^
      IntInf.toString p ^ ", installed clauses " ^ IntInf.toString i ^ ", registered placed clauses " ^
      IntInf.toString r ^ " (registered variables " ^ String.concatWith "," (map IntInf.toString sizes) ^
      "), match found " ^ flag found ^ ", carried exactly " ^ flag exact ^ ", one placed clause per match " ^
      flag single ^ ", nothing registered elsewhere " ^ flag elsewhere);
     if r > 0 andalso found andalso exact andalso single andalso elsewhere then ()
     else error ("INSTALLED PRESENTATIONS " ^ label ^ " at " ^ IntInf.toString k ^ ": the match fails"))
  fun matched label g q n =
    let val rows = timed (label ^ " matched") (fn () => report g q n bound sites) ()
    in List.app (site label) rows end
  fun run () =
    let
      val given = read "given's readers" @{code given_readers_installed}
      val _ = matched "given's readers" @{code given_readers_placement} @{code finite_rooted_given_readers} given
      val asked = read "asked relation" (@{code asked_environment}, @{code asked_use})
      val _ = matched "asked relation" @{code asked_placement} @{code finite_asked_program} asked
      val request = read "first request" (@{code first_request_environment}, @{code first_request_use})
      val _ = matched "first request" @{code first_request_placement} @{code finite_first_request_program} request
    in () end
end
\<close>

ML \<open>val _ = Installed_Presentations_Execution.run ()\<close>

end
