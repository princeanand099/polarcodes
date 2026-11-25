# PolarCodes — Lean 4 Formalization

 Lean 4 (`v4.35.0`) formalization of:

> **Polynomial-Blocklength Quantum Polar Codes via Nonlinear Dephasing Contraction**
> Prince Anand (November 2026)

## Scope

- **Proved (unconditional, Mathlib-only)**: All 24 modules of `PolarCodes` compile with `LAKE_BUILD_EXIT=0` and zero custom axioms (`propext`, `Classical.choice`, `Quot.sound` only), formalizing Definition 2.1, Propositions 2.2, 3.3, 4.2, 4.3, 4.4, Lemmas 3.1, 3.2, 4.1, 5.1, 5.2, 5.3, 5.4, Theorems 1.1, 1.2(a)–(b), 1.3, and Corollary 5.5.
- **Not proved / outside scope**: None; every mathematical result in the manuscript is formalized unconditionally.

## Manuscript-to-Lean Mapping

| Manuscript Result | Lean Declaration | Module |
|---|---|---|
| Definition 2.1 (`W₁ ⊠ W₂`, `W₁ ⊛ W₂`) | `CQChannel.checkCombine`, `CQChannel.varCombine` | `PolarCodes/Channels.lean` |
| Eq. (2.7)–(2.8) (Entropy conservation) | `condEntropy_varCombine_eq`, `entropy_conservation` | `PolarCodes/QuantumProps.lean` |
| Proposition 2.2 (Channel duality D1–D3) | `prop_2_2_D1`, `prop_2_2_D2`, `prop_2_2_D3` | `PolarCodes/ChannelDuality.lean` |
| Lemma 3.1 (Perspective-symmetric inequality) | `lemma_3_1_gx_nonneg`, `antitoneOn_deltaGap` | `PolarCodes/BinaryEntropy.lean` |
| Wyner–Ziv convexity & Eq. (1.8) asymptotics | `convexOn_gc`, `prop_4_3_asymptotic` | `PolarCodes/ScalarSupplements.lean` |
| Frenkel integral formula (Eq. 3.7) | `relEntropy_frenkel_integral` | `PolarCodes/FrenkelIntegral.lean` |
| Hockey-stick integral (Eq. 3.8) | `relEntropy_hockeyStick_integral` | `PolarCodes/HockeyStick.lean` |
| Data Processing Inequality & Lemma 5.1(a) | `relEntropy_partialTrace₂_le`, `fidelityParam_le_sqrt_condEntropy` | `PolarCodes/DataProcessing.lean` |
| Lemma 3.2 (Simultaneous hockey-stick measure) | `lemma_3_2_hockeyStick_measure` | `PolarCodes/HockeyStickMeasure.lean` |
| Proposition 3.3 (QJJS inequality) | `prop_3_3_qjjs` | `PolarCodes/QJJS.lean` |
| **Theorem 1.3** (Nonlinear dephasing SDPI + tightness) | `theorem_1_3_dephasing_sdpi`, `theorem_1_3_equatorial_equality` | `PolarCodes/DephasingSDPI.lean` |
| Lemma 4.1 (Gram-matrix dephasing reduction) | `lemma_4_1_gram_dephasing` | `PolarCodes/GramDephasing.lean` |
| **Theorem 1.2(a)** (Hybrid Q-MGL: pure, BSC, classical) | `theorem_1_2a_pure`, `theorem_1_2a_bsc`, `theorem_1_2a_classical` | `PolarCodes/MrsGerberHybrid.lean`, `PolarCodes/MrsGerberClassical.lean` |
| Proposition 4.2 (Four-branch purification bound) | `prop_4_2_four_branch` | `PolarCodes/MrsGerber.lean` |
| Proposition 4.3 & 4.4 (Scalar splitting & potential contraction) | `prop_4_3_scalar`, `prop_4_4_potential_contraction_general` | `PolarCodes/SplittingBounds.lean` |
| **Theorem 1.2(b)** (Linear splitting & potential contraction) | `theorem_1_2b_linear_splitting`, `theorem_1_2b_potential_contraction` | `PolarCodes/MrsGerber.lean` |
| Lemma 5.1(b) (Synthetic fidelity evolution) | `fidelityParam_plusChannel`, `fidelityParam_minusChannel_le` | `PolarCodes/QuantumProps.lean`, `PolarCodes/Bhattacharyya.lean` |
| Lemmas 5.2, 5.3, 5.4 (Three-stage polarization) | `lemma_5_2_stage1`, `lemma_5_3_stage2`, `lemma_5_4_stage3` | `PolarCodes/Polarization.lean`, `PolarCodes/PolarizationFine.lean` |
| **Theorem 1.1** (Polynomial-blocklength quantum polarization) | `theorem_1_1_quantum_polar_poly_blocklength` | `PolarCodes/MainTheorem.lean` |
| **Corollary 5.5** (Simultaneous CSS polarization) | `corollary_5_5_simultaneous_css_polarization` | `PolarCodes/MainTheorem.lean` |

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
