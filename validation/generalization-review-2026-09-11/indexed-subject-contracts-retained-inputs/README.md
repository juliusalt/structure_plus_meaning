# Exact retained inputs and whitespace diagnostics

The staged scan reports six issues in retained evidence: five raw failure logs
and one generated proof-context source. Every affected byte sequence is kept
exactly. The active source and documentation changes pass the whitespace scan.

The prospective comparison uses all six complete original byte arrays and the
actual outputs of identity and whitespace trimming. Equality with the original
bytes is the condition. The returned repair selects facet 0, leaves no residual,
and makes identity the only eligible candidate under all six required observations.
The finite evaluator consumes these host-derived observations conditionally.
It does not certify arbitrary host semantics or create an exception for other files.

The archive retains the full diagnostic, complete inputs and results, the initial
malformed case specification and its diagnostic, and the decision made before
accepting the unchanged evidence into the commit.

Both investigations replay successfully with complete result and assessment
equality. The retained [replays](replays.json) bind the unchanged archive index.
