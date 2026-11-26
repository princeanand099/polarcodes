# PolarCodes — Lean 4 Formalization

Complete, zero-`sorry`, zero-custom-`axiom` Lean 4 (`v4.35.0`) formalization of:

> **Polynomial-Blocklength Quantum Polar Codes via Nonlinear Dephasing Contraction**
> Prince Anand (November 2026)

## Scope

- **Proved (unconditional, Mathlib-only)**: All 33 modules of `PolarCodes` compile with `LAKE_BUILD_EXIT=0` and zero custom axioms (`propext`, `Classical.choice`, `Quot.sound` only), formalizing:
  - Definition 2.1, Eq. (2.7)–(2.8), and Proposition 2.2 (D1–D3 at both the entropic and output-isometry / channel-equivalence levels);
  - General finite-dimensional CPTP maps (Stinespring dilation) and the general CPTP Data Processing Inequality for Umegaki relative entropy, QJS, and c-q conditional entropy;
  - Lemma 3.1, Frenkel's integral formula (Eq. 3.7), hockey-stick integral (Eq. 3.8), Lemma 3.2 (full equal-support generality), Proposition 3.3 (QJJS + classical symmetric equality for all `x ∈ [0, 1]`), and Theorem 1.3 (nonlinear dephasing SDPI + equatorial equality in both entropy-difference and Umegaki relative-entropy forms);
  - Lemma 4.1, Theorem 1.2(a)–(b), and Propositions 4.2–4.4;
  - Lemma 5.1, Lemmas 5.2–5.4 (three-stage martingale polarization), Arıkan's polar transform `G_N = B_N F^{\otimes n}`, synthesized channels `W_n^{(i)}`, deterministic `G_N`-coset polar codes, Quantum Successive-Cancellation (QSC) decoder, Sen's noncommutative union bound, Wilde–Guha's QSC error bound, full coding-theoretic **Theorem 1.1**, and the full Renes–Wilde quantum & private polar coding **Corollary 5.5** (including degradable vanishing assistance and combined decoding/secrecy error).
- **Not proved / outside scope**: None; every mathematical and coding-theoretic result in the manuscript is formalized unconditionally.

## Manuscript-to-Lean Mapping

| Manuscript Result | Lean Declaration | Module |
|---|---|---|
| Definition 2.1 (`W₁ ⊠ W₂`, `W₁ ⊛ W₂`) | `CQChannel.checkCombine`, `CQChannel.varCombine` | `PolarCodes/Channels.lean` |
| Eq. (2.7)–(2.8) (Entropy conservation) | `condEntropy_varCombine_eq`, `entropy_conservation` | `PolarCodes/QuantumProps.lean` |
| Proposition 2.2 (D1–D3 entropic) | `prop_2_2_D1`, `prop_2_2_D2`, `prop_2_2_D3` | `PolarCodes/ChannelDuality.lean` |
| Proposition 2.2 (D2–D3 channel equivalence) | `prop_2_2_D2_channelEquiv`, `prop_2_2_D3_channelEquiv` | `PolarCodes/ChannelDualityEquiv.lean`, `PolarCodes/ChannelEquiv.lean` |
| General CPTP maps & CPTP DPI | `CPTPMap`, `relEntropy_cptp_le`, `condEntropy_cptp_ge` | `PolarCodes/QuantumChannels.lean` |
| Lemma 3.1 (Perspective-symmetric inequality) | `lemma_3_1_gx_nonneg`, `antitoneOn_deltaGap` | `PolarCodes/BinaryEntropy.lean` |
| Wyner–Ziv convexity & Eq. (1.8) asymptotics | `convexOn_gc`, `prop_4_3_asymptotic` | `PolarCodes/ScalarSupplements.lean` |
| Frenkel integral formula (Eq. 3.7) | `relEntropy_frenkel_integral` | `PolarCodes/FrenkelIntegral.lean` |
| Hockey-stick integral (Eq. 3.8) | `relEntropy_hockeyStick_integral` | `PolarCodes/HockeyStick.lean` |
| Partial-trace DPI & Lemma 5.1(a) | `relEntropy_partialTrace₂_le`, `fidelityParam_le_sqrt_condEntropy` | `PolarCodes/DataProcessing.lean` |
| Lemma 3.2 (Equal-support hockey-stick measure) | `lemma_3_2_hockeyStick_measure`, `lemma_3_2_hockeyStick_measure_equalSupport` | `PolarCodes/HockeyStickMeasure.lean`, `PolarCodes/Refinements.lean` |
| Proposition 3.3 (QJJS + classical equality) | `prop_3_3_qjjs`, `prop_3_3_qjjs_classical_equality` | `PolarCodes/QJJS.lean`, `PolarCodes/Refinements.lean` |
| **Theorem 1.3** (Nonlinear dephasing SDPI + tightness) | `theorem_1_3_dephasing_sdpi`, `theorem_1_3_dephasing_sdpi_relEntropy`, `theorem_1_3_equatorial_equality_relEntropy` | `PolarCodes/DephasingSDPI.lean`, `PolarCodes/Refinements.lean` |
| Lemma 4.1 (Gram-matrix dephasing reduction) | `lemma_4_1_gram_dephasing` | `PolarCodes/GramDephasing.lean` |
| **Theorem 1.2(a)** (Hybrid Q-MGL: pure, BSC, classical) | `theorem_1_2a_pure`, `theorem_1_2a_bsc`, `theorem_1_2a_classical` | `PolarCodes/MrsGerberHybrid.lean`, `PolarCodes/MrsGerberClassical.lean` |
| Proposition 4.2 (Four-branch purification bound) | `prop_4_2_four_branch` | `PolarCodes/MrsGerber.lean` |
| Propositions 4.3 & 4.4 (Scalar splitting & contraction) | `prop_4_3_scalar`, `prop_4_4_potential_contraction_general` | `PolarCodes/SplittingBounds.lean` |
| **Theorem 1.2(b)** (Linear splitting & contraction) | `theorem_1_2b_linear_splitting`, `theorem_1_2b_potential_contraction` | `PolarCodes/MrsGerber.lean` |
| Lemma 5.1(b) (Synthetic fidelity evolution) | `fidelityParam_plusChannel`, `fidelityParam_minusChannel_le` | `PolarCodes/QuantumProps.lean`, `PolarCodes/Bhattacharyya.lean` |
| Lemmas 5.2, 5.3, 5.4 (Three-stage polarization) | `lemma_5_2_stage1`, `lemma_5_3_stage2`, `lemma_5_4_stage3` | `PolarCodes/Polarization.lean`, `PolarCodes/PolarizationFine.lean` |
| Arıkan `G_N`, `W_n^{(i)}`, QSC decoder, Wilde–Guha bound | `arikanTransform`, `synthChannel`, `CosetPolarCode`, `wilde_guha_qsc_bound` | `PolarCodes/NoncommutativeUnion.lean`, `PolarCodes/ArikanTransform.lean`, `PolarCodes/PolarCoding.lean` |
| **Theorem 1.1** (Full coding-theoretic poly-blocklength) | `theorem_1_1_quantum_polar_poly_blocklength`, `theorem_1_1_coding_poly_blocklength` | `PolarCodes/MainTheorem.lean`, `PolarCodes/PolarCoding.lean` |
| **Corollary 5.5** (Full quantum & private polar coding) | `corollary_5_5_simultaneous_css_polarization`, `corollary_5_5_quantum_private_polar_coding` | `PolarCodes/MainTheorem.lean`, `PolarCodes/QuantumPolarCoding.lean` |

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
