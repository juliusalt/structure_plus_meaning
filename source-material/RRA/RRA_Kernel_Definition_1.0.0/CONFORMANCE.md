# Conformance Surface

A conforming implementation declares its implemented modules and data profiles.

## Structure

It must expose or implement equivalent finite operations for:

- formation of `(U,I)`;
- literal equality;
- checking a supplied structural isomorphism;
- checking a supplied bounded-view isomorphism.

## Data

For each declared profile it must validate formation and transport data under a supplied isomorphism exactly as specified.

## Exact Artifact

It must preserve exact local addresses and profile data, reject malformed canonical inputs, reproduce canonical bytes, verify references, and validate citations.

## Assembly

It must compute the abstract quotient or verify a compact witness. For a valid witness, the output must contain all and only the pushforward carrier, incidence, and selected-profile data.

## Evidence Envelopes

It must validate exact field shape and references without assigning semantic force to an envelope.

## Live Trajectories

It must implement the atomic transition relation, retain immutable generations, preserve exact predecessor links, and return no partial success state.

## Reference implementation status

The included Python package implements the finite definitions with the Python standard library. The included test suite covers formation, coordinate renaming, exact encoding, reference verification, all data profiles, abstract and exact assembly, envelope formation, transaction conflict, and ABA-sensitive generation identity.
