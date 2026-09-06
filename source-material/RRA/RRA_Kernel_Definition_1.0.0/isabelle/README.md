# Isabelle/HOL definitions

The session `RRA_Kernel` mirrors the normative modules.

```bash
isabelle build -D isabelle
```

Theory order:

```text
RRA_Core
  ↓
RRA_Data
  ├── RRA_Artifact ── RRA_Live
  └── RRA_Artifact ── RRA_Assembly
                         ↓
                      RRA_Kernel
```

The theories define the carriers, formation predicates, renaming relations, data profiles, exact records, assembly witness, and live-state interfaces. The executable Python model supplies the concrete reference algorithms and canonical codecs.
