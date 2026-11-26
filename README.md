# PolarCodes — Lean 4 Formalization

Zero-`sorry`, zero-custom-`axiom` Lean 4 (`v4.35.0`) formalization of:

> **Polynomial-Blocklength Quantum Polar Codes via Nonlinear Dephasing Contraction**
> Prince Anand (November 2026)

## Scope

- **Proved (unconditional, Mathlib-only)**: All 35 modules of `PolarCodes` compile with `LAKE_BUILD_EXIT=0` and zero custom axioms (`propext`, `Classical.choice`, `Quot.sound` only), formalizing:
  - Section 2.1–2.3: Fuchs–van de Graaf inequalities (Eq. 2.3), hockey-stick variational equality (Eq. 2.2), Klein's inequality equality (`relEntropy ρ σ = 0 ↔ ρ = σ`), QJS range/equality characterizations and general-state relative-entropy identity, general finite-distribution block-diagonal fidelity additivity, Definition 2.1, Eq. (2.7)–(2.8), and Proposition 2.2 (D1–D3 at both the entropic and output-isometry / channel-equivalence levels);
  - General finite-dimensional CPTP maps (Stinespring dilation) and the general CPTP Data Processing Inequality for Umegaki relative entropy, QJS, and c-q conditional entropy;
  - Section 3: Lemma 3.1 (including standalone `ContinuousOn`, `StrictMonoOn`, `StrictConvexOn`, and `HasDerivAt` for `phi`), Frenkel's integral formula (Eq. 3.7), hockey-stick integral (Eq. 3.8), Lemma 3.2 (full equal-support generality), Proposition 3.3 (QJJS + classical symmetric equality for all `x ∈ [0, 1]`), and Theorem 1.3 (nonlinear dephasing SDPI + equatorial equality in both entropy-difference and explicit-finiteness Umegaki relative-entropy forms);
  - Section 4: Lemma 4.1 (including Umegaki relative-entropy Part 4), Theorem 1.2(a)–(b), and Propositions 4.2–4.4;
  - Section 5.1–5.2: Lemma 5.1, Lemmas 5.2–5.4 (three-stage martingale polarization), Arıkan's polar transform `G_N = B_N F^{\otimes n}`, synthesized channels `W_n^{(i)}`, deterministic `G_N`-coset polar codes, Quantum Successive-Cancellation (QSC) decoder, Sen's noncommutative union bound, Wilde–Guha's QSC error bound, and full coding-theoretic **Theorem 1.1**;
  - Section 5.3 (**Corollary 5.5**): Renes–Wilde amplitude/phase c-q polarization reduction (`corollary_5_5_simultaneous_css_polarization` and `corollary_5_5_quantum_private_polar_coding`), proving rate `≥ I_sym(𝒩) - ε/2`, dual unpolarized fractions `≤ ε/4`, structurally pinned degradable assistance-set containment (`C.assistanceRate ≤ ε/2`), and amplitude/phase c-q QSC block-error bounds (`ampPhaseErrorSum ≤ 2 · 2^{-N^{0.49}}`).
- **Not proved / outside scope**: Renes–Wilde [10]'s coherent CSS quantum encoder/decoder CPTP maps (entanglement fidelity / coherent trace-distance decoding error) and wiretap private-coding Eve trace-distance secrecy analysis (`‖ρ_ME - π_M ⊗ σ_E‖₁`) are cited as external black-box operational reductions from [10] and are not formalized as coherent quantum circuits or wiretap protocols.

## Check It Yourself

```bash
lake exe cache get
bash scripts/verify.sh
```

Or run the individual steps:

```bash
lake build PolarCodes Solution
lake env lean PolarCodes/AuditAxioms.lean
lake comparator
```
