"""Use complete native dictionaries without inserting data inside streamed records."""
import re

import native_program_json
import native_stream_json
import program_evaluation_json


def program(code, *, parallel, terms):
    original = native_program_json.ARTIFACT_ROWS
    if original not in code or 'complete_object_reference artifact (!retained_artifacts)' in code:
        return code
    assert code.count(original) == 1
    start = original.index('fun jartifact ')
    end = original.index('fun jartifactRow ', start)
    raw = original[start:end].replace('fun jartifact ', 'fun jartifact_raw ', 1)
    renderer = original[:start] + raw + r'''
val native_artifact_rows = ref (N.complete_object_table_rows N.complete_empty_artifacts);
val () = print "NATIVE_ARTIFACT_STREAM {\"version\":3}\n";
fun jartifact rows = let
  val (index,next) = N.complete_artifact_reference rows (!native_artifact_rows);
  val () = native_artifact_rows := next;
  in "{\"__native_complete_artifact__\":" ^ jnat index ^ "}" end;
''' + original[end:]
    use_terms = terms and program_evaluation_json.TERM in code
    if use_terms:
        renderer += '\nval native_term_rows = ref N.complete_empty_terms;\n'
    if parallel:
        renderer = renderer.replace('= ref ', '= Unsynchronized.ref ')
    code = code.replace(original, renderer, 1)
    source = native_stream_json.PRELUDE
    start = source.index('fun wartifact ')
    end = source.index('fun wartifactRow ', start)
    old = source[start:end]
    assert code.count(old) == 1
    code = code.replace(old, 'fun wartifact rows = print (jartifact rows);\n', 1)
    if use_terms:
        original_term = program_evaluation_json.TERM
        assert code.count(original_term) == 1
        raw_term = re.sub(r'\bjterm\b', 'jterm_raw', original_term)
        code = code.replace(original_term, raw_term + r'''
fun jterm term = let
  val (index,next) = N.complete_term_reference term (!native_term_rows);
  val () = native_term_rows := next;
  in "{\"__native_complete_term__\":" ^ jnat index ^ "}" end;
''', 1)
        code += r'''
val () = print ("NATIVE_TERM_TABLE " ^ jlist jterm_raw (!native_term_rows) ^ "\n");
'''
        term_count = 'Int.toString (length (!native_term_rows))'
    else:
        code += '\nval () = print "NATIVE_TERM_TABLE []\\n";\n'
        term_count = '"0"'
    # Rendering terms can discover additional artifact values. Write that table last.
    code += r'''
val () = print ("NATIVE_ARTIFACT_TABLE " ^ jlist jartifact_raw (!native_artifact_rows) ^ "\n");
val () = print ("NATIVE_ARTIFACT_END {\"entries\":" ^ Int.toString (length (!native_artifact_rows)) ^
  ",\"terms\":" ^ ''' + term_count + r''' ^ "}\n");
'''
    return code
