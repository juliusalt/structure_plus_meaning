"""Reference native whole artifacts before converting their complete fields."""
import re


def program_with_references(code, prefix):
    start = code.index('fun wartifact ')
    end = code.index('fun wartifactRow ', start)
    original = code[start:end]
    assert original.count('fun wartifact ') == 1
    replacement = original.replace('fun wartifact ', 'fun wartifact_raw ', 1)
    replacement += r'''
val retained_artifacts = ref N.complete_empty_artifacts;
fun wartifact artifact = let
  val (index,next) = N.complete_object_reference artifact (!retained_artifacts);
  val () = retained_artifacts := next;
  in print ("{\"__artifact_ref__\":" ^ jnat index ^ "}") end;
'''
    code = code[:start] + replacement + code[end:]
    code, changed = re.subn(r'wartifact \(N\.finite_artifact_rows ([A-Za-z_][A-Za-z_0-9]*)\)',
                           r'wartifact \1', code)
    assert changed >= 2 and 'wartifact (N.finite_artifact_rows' not in code
    environment = 'wlist wartifactRow (N.finite_environment_artifact_rows e)'
    assert code.count(environment) == 1
    code = code.replace(environment, 'wlist wartifactRow (N.complete_environment_artifact_objects e)')
    address = 'fun waddress x = wlist (wencoded jnat) x;'
    assert code.count(address) == 1
    code = code.replace(address, 'fun waddress x = print (jaddress x);')
    code += '\nval () = wemit "' + prefix + '_ARTIFACTS"\n'
    code += '  (fn () => wlist wartifact_raw (N.complete_object_table_rows (!retained_artifacts)));\n'
    return code
