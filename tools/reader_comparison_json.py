"""Serialize complete reader contexts, results and derived condition rows."""


def prelude(value, inspector):
    return r'''
fun jcontext (x,reference) = "{\"subject\":" ^ jsubject x ^ ",\"reference_readings\":" ^ jf __VALUE__ reference ^ "}";
fun jresult (result,reference) = "{\"readings\":" ^ jf __VALUE__ result ^
  ",\"reference_readings\":" ^ jf __VALUE__ reference ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jcandidate (m,result) = "{\"method\":" ^ jnat m ^ ",\"result\":" ^ jresult result ^ "}";
fun jassessed (m,result) = "{\"method\":" ^ jnat m ^ ",\"qualities\":" ^ jlist jquality
  (map (fn f => (f,N.__INSPECTOR__ result f)) facets) ^ "}";
'''.replace('__VALUE__', value).replace('__INSPECTOR__', inspector)
