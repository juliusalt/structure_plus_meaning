theory RRA_Use_Codec_Cases
  imports RRA_Use_Codec_Methods
begin

definition use_codec_requests :: "nat\<Rightarrow>local_address option fset" where
  "use_codec_requests w=(if w=0 then {|None,Some []|}
    else if w=1 then {|Some [0],Some [1]|}
    else if w=2 then {|Some [2],Some [3]|}
    else if w=3 then {|Some [7],Some [8]|}
    else if w=4 then {|Some [31],Some [33]|}
    else if w=5 then {|Some [127],Some [129]|}
    else if w=6 then {|Some [0],Some [255],Some [256]|}
    else if w=7 then {|Some [300],Some [999]|}
    else if w=8 then {|Some [0,1],Some [1,0],Some [1],Some [1,0,0]|}
    else if w=9 then {|Some (replicate 32 0),Some (replicate 128 0)|}
    else if w=10 then {|Some [1024,4095,0]|}
    else if w=11 then {|Some [0],Some [1,2]|}
    else if w=12 then {|None,Some [],Some [2]|}
    else if w=13 then {|Some [1]|}
    else if w=14 then {||}
    else {|None|})"

definition use_codec_magnitude :: "nat\<Rightarrow>nat" where
  "use_codec_magnitude w=(if w=0 \<or> w=9 \<or> w=13 then 0
    else if w=1 \<or> w=8 then 1 else if w=2 \<or> w=11 \<or> w=12 then 2
    else if w=3 then 4 else if w=4 then 6 else if w=5 then 8
    else if w=6 then 9 else if w=7 then 10 else if w=10 then 12 else 0)"

definition use_codec_case :: "nat\<Rightarrow>use_codec_subject" where
  "use_codec_case w=(let A=use_codec_requests w;
    P=fimage use_binary_path A |\<union>| fimage digit_use_path A |\<union>|
      fimage (rev \<circ> digit_use_path) A |\<union>|
      {|[],[False],[True],[False,False],[True,True],[True,True,False,False],
        [True,True,True,True,False,False],[True,False,True]|}
    in (A,P,use_codec_magnitude w))"

text \<open>
  Complete use and path inputs include absent and present empty words, coordinate
  boundaries, long words, binary magnitude boundaries, coordinates beyond a
  byte, noncanonical digits and incomplete paths. A request outside its stated
  magnitude bound remains visible; its conditional cost requirement is not
  reported as an unconditional guarantee. This finite family is a stated scope.
\<close>

end
