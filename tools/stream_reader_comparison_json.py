"""Stream complete reader contexts and result sets with supplied value writers."""


def prelude(value, subject, inspector):
    return r'''
fun wcontext (x,reference) = wobject [
  ("\"subject\"",fn () => __SUBJECT__ x),
  ("\"reference_readings\"",fn () => wf __VALUE__ reference)];
fun wresult (result,reference) = wobject [
  ("\"readings\"",fn () => wf __VALUE__ result),
  ("\"reference_readings\"",fn () => wf __VALUE__ reference)];
fun wcandidate (m,result) = wobject [
  ("\"method\"",fn () => print (jnat m)),
  ("\"result\"",fn () => wresult result)];
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jassessed (m,result) = "{\"method\":" ^ jnat m ^ ",\"qualities\":" ^ jlist jquality
  (map (fn f => (f,N.__INSPECTOR__ result f)) facets) ^ "}";
'''.replace('__VALUE__', value).replace('__SUBJECT__', subject).replace('__INSPECTOR__', inspector)
