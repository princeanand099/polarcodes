# Polynomial-Blocklength Quantum Polar Codes (Lean 4)

Formal verification in Lean 4 (`v4.35.0`) of *Polynomial-Blocklength Quantum Polar Codes via Nonlinear Dephasing Contraction* (Prince Anand, November 2026).

## Requirements & Build

- Lean toolchain: `leanprover/lean4:v4.35.0` (see `lean-toolchain`)
- Dependencies: Mathlib `v4.35.0` and `comparator` `v4.35.0` (see `lakefile.toml`)

```bash
lake exe cache get
lake build PolarCodes
```

## Module Organization

- `PolarCodes/BinaryEntropy.lean` — Binary entropy `h2`, inverse `h2Inv`, binary convolution `binConv`, `gc`, `gq`, `deltaGap`, `φ`, and Lemma 3.1.
- `PolarCodes/QuantumStates.lean` — Density operators, von Neumann entropy, Umegaki relative entropy, QJS, hockey-stick divergence, trace distance, root fidelity, Uhlmann's theorem, Frenkel's integral formula, and DPI (in progress).
- `PolarCodes/Channels.lean` — Binary-input c-q channels, Definition 2.1, entropy conservation (2.8), and Renes' channel duality (Proposition 2.2) (planned).
- `PolarCodes/HockeyStick.lean` — Lemma 3.2 and Proposition 3.3 (QJJS) (planned).
- `PolarCodes/DephasingSDPI.lean` — Theorem 1.3 (Nonlinear SDPI for Qubit Dephasing) (planned).
- `PolarCodes/MrsGerber.lean` — Lemma 4.1, Theorem 1.2(a)–(b), Propositions 4.2–4.4 (planned).
- `PolarCodes/Bhattacharyya.lean` — Lemma 5.1 (planned).
- `PolarCodes/Polarization.lean` — Lemmas 5.2–5.4 (Three-Stage Polarization) (planned).
- `PolarCodes/MainTheorem.lean` — Theorem 1.1 and Corollary 5.5 (planned).

## Project Records

- `PROOF-PATH.md` — Manuscript-to-Lean theorem correspondence and dependency DAG.
- `PROGRESS.md` — Continuous formalization progress record.
- `EXTERNAL-AXIOMS.md` — External-axiom register (target: 0 custom axioms; standard Lean axioms only).
- `ATTRIBUTION.md` — Mathematical references and attribution.
- `CITATION.cff` — Citation metadata.
