"""Serialize complete investigation, repair and revision results."""

PRELUDE = r'''
fun jpair (a,b) = "[" ^ jnat a ^ "," ^ jnat b ^ "]";
fun jtriple (a,(b,c)) = "[" ^ jnat a ^ "," ^ jnat b ^ "," ^ jnat c ^ "]";
fun jquad (a,(b,(c,d))) = "[" ^ jnat a ^ "," ^ jnat b ^ "," ^ jnat c ^ "," ^ jnat d ^ "]";
fun jprofile (c,p) = "{\"candidate\":" ^ jnat c ^ ",\"profile\":" ^ jlist jpair p ^ "}";
fun jloss (c,(d,p)) = "{\"from\":" ^ jnat c ^ ",\"to\":" ^ jnat d ^ ",\"losses\":" ^ jlist jpair p ^ "}";
fun jbasis (formed,(residual,(profiles,losses))) =
  "{\"formed\":" ^ Bool.toString formed ^ ",\"residual\":" ^ jlist jpair residual ^
  ",\"profiles\":" ^ jlist jprofile profiles ^ ",\"losses\":" ^ jlist jloss losses ^ "}";
fun jrepairs (safe,(conflicts,(repairs,unrepairable))) =
  "{\"safe\":" ^ jlist jnat safe ^ ",\"conflicts\":" ^ jlist jquad conflicts ^
  ",\"repairs\":" ^ jlist jquad repairs ^ ",\"unrepairable\":" ^ jlist jpair unrepairable ^ "}";
fun jrevision (retained,(withdrawn,(repairs,(revised,residual)))) =
  "{\"retained\":" ^ jlist jnat retained ^ ",\"withdrawn\":" ^ jlist jnat withdrawn ^
  ",\"repairs\":" ^ jlist jquad repairs ^ ",\"selection\":" ^ jlist jnat revised ^
  ",\"residual\":" ^ jlist jpair residual ^ "}";
'''
