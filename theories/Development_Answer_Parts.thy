theory Development_Answer_Parts
  imports Main
begin

section \<open>The declared parts of an answer are read by Isabelle's own syntax\<close>

text \<open>
  An executor answers a refinement request with three declared parts: new definitions together with
  the lemmas about them, the equation, and its proof. The harness places the parts in the answer's
  theory, so whatever text a part holds would be processed as theory text there. Before that theory
  is processed at all, the parts are read here with the outer syntax of the context the answer is
  framed in, and a part is refused unless it has the declared form:

  \<^item> the definitions consist of definitional commands (\<open>definition\<close>, \<open>fun\<close>, \<open>function\<close>,
    \<open>primrec\<close>, \<open>termination\<close>), theorem statements with their proofs, and document text; a
    declaration or a theorem statement names no attribute and no target, since an attribute or a
    target would act beyond the answer's own constants once the theory is adopted;
  \<^item> the proof consists of proof commands only, so nothing follows the answer's lemma;
  \<^item> the equation is one proposition: placed between quotes it is exactly one string token;
  \<^item> no part names a method that runs ML, holds a control antiquotation, or holds a document
    antiquotation in its text or comments;
  \<^item> a name the definitions introduce, for a constant or a fact, is not already the name of a
    constant or a fact of the frame, since the adopted answer would otherwise change what that name
    reads as in every theory importing it.

  What is refused never reaches the answer's theory. The reading decides the form of the parts,
  never their meaning: whether the answer refines its subject is the verdict of its checked state.
\<close>

ML \<open>
structure Development_Answer_Parts =
struct

val declaring_commands = ["definition", "fun", "function", "primrec", "termination"];
val theorem_commands = ["lemma", "theorem", "corollary"];
val document_commands = ["text", "section", "subsection", "subsubsection", "paragraph", "txt"];
val proof_commands =
  ["proof", "qed", "by", "apply", "apply_end", "done", "defer", "prefer", "next", "have", "show",
   "hence", "thus", "obtain", "fix", "assume", "presume", "define", "let", "note", "from", "with",
   "using", "unfolding", "then", "also", "finally", "moreover", "ultimately", "case", "consider",
   "supply", "subgoal", "{", "}", ".", "..", "txt"];
val ml_methods = ["tactic", "raw_tactic"];

fun refuse part msg = error ("The answer's " ^ part ^ " part is refused: " ^ msg);

fun antiquoted text = String.isSubstring "@{" text orelse String.isSubstring "\092<^" text;

fun check_tokens part toks =
  List.app (fn tok =>
    if Token.is_error tok then refuse part "it does not read as outer syntax"
    else if is_some (Token.get_control tok) then refuse part "it holds a control antiquotation"
    else if Token.is_comment tok andalso antiquoted (Token.content_of tok)
    then refuse part "a comment holds an antiquotation"
    else if Token.ident_with (member (op =) ml_methods) tok
    then refuse part ("it names the method " ^ Token.content_of tok ^ ", which runs ML")
    else ()) toks;

fun commands part toks =
  let
    fun split [] = []
      | split (c :: ts) =
          if Token.is_command c then
            let val (body, rest) = chop_prefix (not o Token.is_command) ts
            in (Token.content_of c, body) :: split rest end
          else refuse part "it holds text outside a command";
  in split (filter (fn tok => Token.is_proper tok andalso Token.not_eof tok) toks) end;

fun statement_header body =
  #1 (chop_prefix (fn tok => not (Token.keyword_with (fn s => s = ":") tok) andalso
    not (Token.is_kind Token.String tok) andalso not (Token.is_kind Token.Cartouche tok)) body);

fun check_header part name toks =
  if exists (Token.keyword_with (fn s => s = "[" orelse s = "in")) toks
  then refuse part ("the " ^ name ^ " declares an attribute or a target")
  else ();

fun check_text part body =
  if exists (antiquoted o Token.content_of) body then refuse part "a text holds an antiquotation" else ();

fun header_names toks =
  let
    fun names [] _ = []
      | names (tok :: rest) depth =
          if Token.keyword_with (fn s => s = "::") tok then names (drop 1 rest) depth
          else if Token.keyword_with (fn s => s = "(") tok then names rest (depth + 1)
          else if Token.keyword_with (fn s => s = ")") tok then names rest (depth - 1)
          else if depth = 0 andalso (Token.is_kind Token.Ident tok orelse Token.is_kind Token.Long_Ident tok)
          then Token.content_of tok :: names rest depth
          else names rest depth;
  in names toks 0 end;

fun check_fresh part thy declared name =
  if declared thy name
  then refuse part ("the name " ^ name ^ " already names a constant or a fact of the frame")
  else ();

fun fresh_constant thy name = Sign.declared_const thy (Sign.intern_const thy name);
fun fresh_fact thy name = Global_Theory.defined_fact thy (Global_Theory.intern_fact thy name);

fun check_definition thy part (name, body) =
  if member (op =) theorem_commands name then
    let val header = statement_header body
    in check_header part name header; List.app (check_fresh part thy fresh_fact) (header_names header) end
  else if member (op =) declaring_commands name then
    (check_header part name body;
     if name = "termination" then ()
     else List.app (check_fresh part thy fresh_constant)
       (header_names (#1 (chop_prefix (not o Token.keyword_with (fn s => s = "where")) body))))
  else if member (op =) document_commands name then check_text part body
  else if member (op =) proof_commands name then ()
  else refuse part ("the command " ^ name ^ " is not a declared part of an answer");

fun check_proof part (name, body) =
  if name = "txt" then check_text part body
  else if member (op =) proof_commands name then ()
  else refuse part ("the command " ^ name ^ " is not a proof command");

fun check_equation keywords equation =
  (case filter (fn tok => Token.is_proper tok andalso Token.not_eof tok)
      (Token.explode keywords Position.none ("\"" ^ equation ^ "\"")) of
    [tok] =>
      if Token.is_kind Token.String tok then ()
      else refuse "equation" "it is not one proposition"
  | _ => refuse "equation" "it is not one proposition");

fun check thy (definitions, equation, proof) =
  let
    val keywords = Thy_Header.get_keywords thy;
    fun lex text = Token.explode keywords Position.none text;
    val declared = lex definitions;
    val proved = lex proof;
    val _ = check_tokens "definitions" declared;
    val _ = List.app (check_definition thy "definitions") (commands "definitions" declared);
    val _ = check_tokens "proof" proved;
    val steps = commands "proof" proved;
    val _ = if null steps then refuse "proof" "it holds no proof" else ();
    val _ = List.app (check_proof "proof") steps;
    val _ = check_equation keywords equation;
  in () end;

end
\<close>

end
