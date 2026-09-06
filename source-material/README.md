# Source material

These files preserve the supplied design material and the history of the
reconstruction. Their embedded claims of normativity, completeness, or successful
validation belong to those historical documents. They do not establish the
properties of the active system.

The owner's current instructions govern the development. The active definitions
and proofs are selected by the repository's ROOT file. A successful Isabelle
build checks those proofs relative to their definitions; the alignment audit
also examines whether the definitions express the intended distinctions.

| Material | Role |
|---|---|
| factor-foundation-kernel-v6.1.tex | Supplied Factor proposal; architectural evidence and candidate mechanisms. |
| RRA_Kernel_Definition_1.0.0.zip and RRA/ | Supplied RRA package, including its historical implementations and validation files. |
| bootstrap-delivered.zip | Exact delivered bootstrap theories and top-level explanatory files, before repair. |
| bootstrap-build-repair.zip | Buildable repair of the delivered session before architectural reconstruction, with its build receipt. |
| SOURCE_SHA256SUMS.txt | Supplied-source identities; it does not certify the contents' correctness. |

The build repair closes parsing and proof errors. Its definitions still contain
the architectural defects recorded by plan.md. It is preserved to make the
transition inspectable, not as a competing foundation.

`intermediate-data-assembly-footprint.zip` preserves the checked intermediate
session after native data migration, assembly-output derivation, footprints,
and fragment reconstruction. Its higher theories still use the delivered
resolver-based design. They were removed from the active graph for replacement,
not accepted as the intended semantic system.
