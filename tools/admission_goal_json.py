"""Serialize the complete shared admission goal with its actual site values."""

PRELUDE = r'''
fun jgoalWith site (N.Existing_Admission d) = "{\"existing\":" ^ site d ^ "}"
  | jgoalWith site (N.Paired_Admission (g,h)) =
      "{\"pair\":[" ^ jgoalWith site g ^ "," ^ jgoalWith site h ^ "]}"
  | jgoalWith site (N.Collected_Admission g) = "{\"collection\":" ^ jgoalWith site g ^ "}";
'''
