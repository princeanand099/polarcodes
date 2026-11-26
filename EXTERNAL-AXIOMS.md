# External Axioms

**Zero external or custom axioms are used.**

Every definition and theorem in `PolarCodes` is built strictly on top of Lean 4 (`v4.35.0`) and Mathlib, using only the three standard Lean 4 axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`

This is verified on every CI run by:
1. `PolarCodes/AuditAxioms.lean` (`#print axioms` on all 29 headline theorems),
2. Automated repository hygiene checks (zero `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `partial`), and
3. `lake exe comparator`.
