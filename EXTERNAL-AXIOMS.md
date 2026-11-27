# External Axioms

`PolarCodes` introduces no custom axioms. Every declaration depends only on Lean 4's standard axioms:

- `propext`
- `Classical.choice`
- `Quot.sound`

Verify locally with:

```bash
lake env lean PolarCodes/AuditAxioms.lean
lake comparator
```
