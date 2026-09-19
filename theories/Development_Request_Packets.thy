theory Development_Request_Packets
  imports Development_Refinement_Verification Isabelle_Entity_Export
begin

section \<open>A request is presented to an executor by reading its terms back\<close>

text \<open>
  An executor receives the request and nothing else. The request is a native value over the
  positions of its state's name table; its presentation to an executor reads every position
  back to the name the table holds there and every presented type and term back to the Isabelle
  type and term the exporter translated, so the executor reads the refined constant, the
  issued support and the least context, which holds the incumbent equations, exactly as the checked context states them. The reading
  is the inverse of the exporter's translation; it adds no content and chooses nothing. Schematic
  variables and schematic type variables are read as free ones, because an answer states them in
  a lemma.
\<close>

definition development_packet_constant :: "development_request \<Rightarrow> isabelle_term" where
  "development_packet_constant r=fst (snd r)"

definition development_packet_support :: "development_request \<Rightarrow> nat list" where
  "development_packet_support r=sorted_list_of_fset (fst (snd (snd r)))"

definition development_packet_context :: "isabelle_context \<Rightarrow> development_request \<Rightarrow> isabelle_entity list" where
  "development_packet_context C r=filter (\<lambda>e. e |\<in>| snd (snd (snd r))) (snd C)"

lemma development_packet_context_exact:
  "set (development_packet_context C r)=set (snd C)\<inter>fset (snd (snd (snd r)))"
  by (auto simp: development_packet_context_def)

ML \<open>
structure Development_Request_Packets =
struct

fun number t = snd (HOLogic.dest_number t);

fun typ names (\<^Const_>\<open>Isabelle_Type_Application for c Ts\<close>) =
      Type (nth names (number c), map (typ names) (HOLogic.dest_list Ts))
  | typ names (\<^Const_>\<open>Isabelle_Type_Free for a S\<close>) =
      TFree (nth names (number a), map (nth names o number) (HOLogic.dest_list S))
  | typ names (\<^Const_>\<open>Isabelle_Type_Variable for a _ S\<close>) =
      TFree (nth names (number a), map (nth names o number) (HOLogic.dest_list S))
  | typ _ t = raise TERM ("Not a presented type", [t]);

(*Schematic variables become free variables of the same name and type.*)
fun term names (\<^Const_>\<open>Isabelle_Constant _ for c T\<close>) = Const (nth names (number c), typ names T)
  | term names (\<^Const_>\<open>Isabelle_Free _ for x T\<close>) = Free (nth names (number x), typ names T)
  | term names (\<^Const_>\<open>Isabelle_Variable _ for x _ T\<close>) = Free (nth names (number x), typ names T)
  | term _ (\<^Const_>\<open>Isabelle_Bound _ for i\<close>) = Bound (number i)
  | term names (\<^Const_>\<open>Isabelle_Abstraction _ for T t\<close>) = Abs ("x", typ names T, term names t)
  | term names (\<^Const_>\<open>Isabelle_Application _ for t u\<close>) = term names t $ term names u
  | term _ t = raise TERM ("Not a presented term", [t]);

fun entity names (\<^Const_>\<open>Isabelle_Base_Constant _ for t\<close>) = ("declaration", term names t)
  | entity names (\<^Const_>\<open>Isabelle_Development_Constant _ for t\<close>) = ("declaration", term names t)
  | entity names (\<^Const_>\<open>Isabelle_Frontier_Constant _ for t\<close>) = ("declaration", term names t)
  | entity names (\<^Const_>\<open>Isabelle_Definition _ for p\<close>) = ("definition", term names p)
  | entity names (\<^Const_>\<open>Isabelle_Specification _ for p\<close>) = ("specification", term names p)
  | entity names (\<^Const_>\<open>Isabelle_Code_Equation _ for p\<close>) = ("code equation", term names p)
  | entity _ t = raise TERM ("Not a presented entity", [t]);

fun json_string s =
  "\"" ^ String.translate (fn #"\"" => "\\\"" | #"\\" => "\\\\" | #"\n" => "\\n" | c => String.str c) s ^ "\"";

fun text ctxt t =
  Pretty.pure_string_of (Syntax.pretty_term (Config.put show_types true ctxt) t);

fun declaration ctxt (Const (c, T)) =
      "{\"name\":" ^ json_string c ^ ",\"type\":" ^ json_string (Pretty.pure_string_of (Syntax.pretty_typ ctxt T)) ^ "}"
  | declaration ctxt t = json_string (text ctxt t);

(*The packet of the request a state presents for a subject: the refined constant, the issued
  support as declarations of the state, the least context, the facts the answer theory provides
  and the declared form of an answer.*)
fun packet ctxt {state, subject, context, request} =
  let
    val evaluate = Code_Evaluation.dynamic_value_strict ctxt;
    val names = map HOLogic.dest_literal (HOLogic.dest_list (evaluate (HOLogic.mk_fst context)));
    val constant = term names (evaluate \<^Const>\<open>development_packet_constant for request\<close>);
    val support = map number (HOLogic.dest_list (evaluate \<^Const>\<open>development_packet_support for request\<close>));
    val entities = map (entity names) (HOLogic.dest_list (evaluate \<^Const>\<open>development_packet_context for context request\<close>));
    val declared = map_filter (fn ("declaration", t) => SOME t | _ => NONE) entities;
    fun declared_name (Const (c, _)) = SOME c | declared_name _ = NONE;
    val support_declarations =
      filter (fn t => member (op =) (map (nth names) support) (the_default "" (declared_name t))) declared;
    val items = filter (fn (kind, _) => kind <> "declaration") entities;
  in
    "{\"request\":{\"state\":" ^ json_string state ^ ",\"subject\":" ^ json_string subject ^ "}," ^
    "\"constant\":" ^ declaration ctxt constant ^ "," ^
    "\"support\":[" ^ commas (map (declaration ctxt) support_declarations) ^ "]," ^
    "\"context\":[" ^ commas (map (fn (kind, t) => "{\"kind\":" ^ json_string kind ^ ",\"text\":" ^
      json_string (text ctxt t) ^ "}") items) ^ "]," ^
    "\"facts\":[\"development_demanded_code\"]," ^
    "\"answer\":{\"fields\":[\"request\",\"definitions\",\"equation\",\"proof\"]}}"
  end;

fun export_packet thy name text =
  Export.export thy (Path.binding0 (Path.make ["request", name])) [XML.Text text];

end
\<close>

text \<open>
  The packet is the whole of what an executor receives. It carries no file, no name of a
  theory to read and no tool; an answer is judged only by the verdict of its checked state, so
  anything else an answer's text attempts is either inside the state the verdict reads or
  refused with it.
\<close>

end
