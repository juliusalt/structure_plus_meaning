# Complete original-use codec comparison

The original subject is an optional finite word of arbitrary natural coordinates.
The three semantic conditions inspect actual roundtrips, every accepted supplied
path and separation of distinct supplied uses. An independent cost condition
requires a path of at most `1 + word_length * (2*k + 1)` when every original
coordinate is below `2^k`. Both the prerequisite and the actual length are retained.

The generic finite codec assessment derives both complete graphs from actual
encoder and decoder operations. The prefix-word reader composes exact nonempty
component readers, preserving the entire suffix and rejecting incomplete input.
The digit component separately proves canonical natural recovery and its bound.
Every use and slot boundary remains explicit; no byte restriction is introduced.

The executed family has ten codecs and sixteen complete use/path subjects.
Unary, digit and reversed-digit codecs satisfy the semantic conditions; digit
and reversed-digit codecs also satisfy the stated budget. All three have
independent all-input semantic theorems, and both digit variants have an
all-input conditional budget theorem. The finite family includes absent uses,
present empty words, byte and magnitude boundaries, long words, noncanonical
and incomplete paths, an empty request set and a false magnitude prerequisite.

The complete reports retain small-coordinate overhead: `[1]` has unary/digit
path lengths 3/4, `[2]` has 4/6, `[33]` has 35/14, and `[129]` has 131/18.
The original multi-coordinate `[1024,4095,0]` has lengths 5123/50. A false
prerequisite does not turn its conditional cost observation into a bound.
Fault controls include byte clamping, absent/empty conflation, ignored final
positions, unchecked noncanonical digits, constant paths, refusal and reversed
encoding with the wrong decoder. Every graph and counterexample is reconstructed.

Revision from no facets has 67 residual pairs and 916 repair witnesses, and
reaches `[3,2,0,1]` with an empty residual. The `[0]` and semantic-only bases
retain their own complete repairs and revised results. Comparison admissibility
is about the declared finite family. It does not establish arbitrary candidate
or input coverage. Store integration, actual allocation traversals, arithmetic
cost, full physical decision cost, workflow enforcement and genesis remain open.

Run `python3 -B tools/reconstruct_use_codecs.py --poly <PolyML> --output <fresh>`.
The repository retains the complete source boundary and complete-report identity;
the recipe rebuilds proofs, exports, actual executions and comparison results.
