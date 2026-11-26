# External Axioms

**None (0 custom axioms).**

Every theorem in `PolarCodes` is proved unconditionally from Mathlib (`v4.35.0`) and Lean 4 core. Running `lake env lean PolarCodes/AuditAxioms.lean` checks that all 50 exported theorems depend exclusively on Lean 4's standard axioms:

- `propext`
- `Classical.choice`
- `Quot.sound`

No `axiom`, `sorry`, `admit`, `native_decide`, `unsafe`, or compiler-trust extensions are used anywhere in `PolarCodes` or `comparator/Solution.lean`.
