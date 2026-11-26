# PolarCodes — Lean 4 Formalization

Zero-`sorry`, zero-custom-`axiom` Lean 4 (`v4.35.0`) formalization of:

> **Polynomial-Blocklength Quantum Polar Codes via Nonlinear Dephasing Contraction**
> Prince Anand (November 2026)

## Scope

- **Proved (unconditional, Mathlib-only)**: All 36 modules of `PolarCodes` (68 audited exported theorems in `PolarCodes/AuditAxioms.lean`, 13 locked headline theorems in `comparator/`) use exclusively Lean 4's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), formalizing:
  - **Section 2.1–2.3**: Fuchs–van de Graaf inequalities (Eq. 2.3), hockey-stick variational equality (Eq. 2.2), `posPartMat A * negPartMat A = 0`, Klein's inequality equality (`relEntropy ρ σ = 0 ↔ ρ = σ`), QJS range/equality characterizations and general-state relative-entropy identity, general finite-distribution block-diagonal fidelity additivity, Definition 2.1, Eq. (2.7)–(2.8), and Proposition 2.2 (D1–D3 at entropic, `IsoEquiv` for (D2) variable-node `prop_2_2_D2_var_isoEquiv`, and `ChannelEquiv` levels);
  - **General CPTP maps & DPI**: Finite-dimensional Stinespring CPTP maps and the general CPTP Data Processing Inequality for Umegaki relative entropy, QJS, and c-q conditional entropy;
  - **Section 3**: Lemma 3.1 (including standalone `ContinuousOn`, `StrictMonoOn`, `StrictConvexOn`, and `HasDerivAt` for `phi`), Frenkel's integral formula (Eq. 3.7) and hockey-stick integral (Eq. 3.8) for both positive-definite states and arbitrary rank-deficient states satisfying `suppSubset ρ σ`, Lemma 3.2 (positive-definite and equal-support generality with explicit `relEntropy ≠ ⊤`), Proposition 3.3 (QJJS + classical symmetric equality for all `x ∈ [0, 1]`), and **Theorem 1.3** (nonlinear dephasing SDPI + equatorial equality in both entropy-difference and explicit-finiteness Umegaki relative-entropy forms);
  - **Section 4**: Lemma 4.1 (tightened to `p ∈ [0, 1/2]`, with characteristic-polynomial / nonzero-eigenvalue coincidence and Umegaki relative-entropy Part 4), **Theorem 1.2(a)–(b)**, and Propositions 4.2–4.4;
  - **Section 5.1–5.2**: Lemma 5.1, Lemmas 5.2–5.4 (three-stage martingale polarization), Arıkan's polar transform `G_N = B_N F^{\otimes n}`, synthesized channels `W_n^{(i)}`, deterministic `G_N`-coset polar codes, Quantum Successive-Cancellation (QSC) decoder syntactically pinned via `qscPolarCode` / `CosetPolarCode.IsQSCDecoder`, Sen's noncommutative union bound, Wilde–Guha's QSC error bound, and full coding-theoretic **Theorem 1.1**;
  - **Section 5.3 (Corollary 5.5)**: Renes–Wilde amplitude/phase c-q polarization reduction (`corollary_5_5_simultaneous_css_polarization` and `corollary_5_5_quantum_private_polar_coding`), proving rate `≥ I_sym(𝒩) - ε/2`, dual unpolarized fractions `≤ ε/4`, structurally pinned degradable assistance-set containment (`CSSPrivatePolarCode.assistanceSet_spec` and `C.assistanceRate ≤ ε/2`), and amplitude/phase c-q QSC block-error bounds (`ampPhaseErrorSum ≤ 2 · 2^{-N^{0.49}}`).
- **Not proved / outside scope**: Renes–Wilde [10]'s coherent CSS quantum encoder/decoder CPTP maps (entanglement fidelity / coherent trace-distance decoding error) and wiretap private-coding Eve trace-distance secrecy analysis (`‖ρ_ME - π_M ⊗ σ_E‖₁`) are cited as external black-box operational reductions from [10] and are not formalized as coherent quantum circuits or wiretap protocols.

## Manuscript-to-Lean Mapping

| Manuscript Result | Lean Declaration | Module |
|---|---|---|
| Section 2.1 (Fuchs–van de Graaf Eq. 2.3, hockey-stick Eq. 2.2) | `one_sub_rootFidelity_le_traceDist`, `traceDist_le_sqrt_one_sub_rootFidelity_sq`, `hockeyStick_eq_sSup` | `PolarCodes/PhiAndFuchs.lean`, `PolarCodes/DivergenceCharacterizations.lean` |
| Section 2.1 (Klein equality, QJS characterizations, block-diag fidelity) | `relEntropy_eq_zero_iff`, `qjs_eq_avg_relEntropy`, `qjs_mem_Icc`, `qjs_eq_zero_iff`, `qjs_eq_one_iff`, `rootFidelity_block_diagonal` | `PolarCodes/DivergenceCharacterizations.lean` |
| Definition 2.1 (`W₁ ⊠ W₂`, `W₁ ⊛ W₂`) | `CQChannel.checkCombine`, `CQChannel.varCombine` | `PolarCodes/Channels.lean` |
| Eq. (2.7)–(2.8) (Entropy conservation) | `condEntropy_varCombine_eq`, `entropy_conservation` | `PolarCodes/QuantumProps.lean` |
| Proposition 2.2 (D1–D3 entropic, `IsoEquiv`, `ChannelEquiv`) | `prop_2_2_D1`, `prop_2_2_D2`, `prop_2_2_D3`, `prop_2_2_D2_var_isoEquiv`, `prop_2_2_D2_channelEquiv`, `prop_2_2_D3_channelEquiv` | `PolarCodes/ChannelDuality.lean`, `PolarCodes/ChannelDualityEquiv.lean`, `PolarCodes/ChannelEquiv.lean` |
| General CPTP maps & CPTP DPI | `CPTPMap`, `relEntropy_cptp_le`, `condEntropy_cptp_ge` | `PolarCodes/QuantumChannels.lean` |
| Lemma 3.1 (`phi` regularity & perspective-symmetric inequality) | `lemma_3_1_gx_nonneg`, `antitoneOn_deltaGap`, `continuousOn_phi`, `strictMonoOn_phi`, `strictConvexOn_phi`, `hasDerivAt_phi_cParam` | `PolarCodes/BinaryEntropy.lean`, `PolarCodes/PhiAndFuchs.lean` |
| Wyner–Ziv convexity & Eq. (1.8) asymptotics | `convexOn_gc`, `prop_4_3_asymptotic` | `PolarCodes/ScalarSupplements.lean` |
| Frenkel & hockey-stick integrals (Eq. 3.7–3.8, `PosDef` & `suppSubset`) | `relEntropy_frenkel_integral`, `relEntropy_hockeyStick_integral`, `relEntropy_frenkel_integral_of_suppSubset`, `relEntropy_hockeyStick_integral_of_suppSubset` | `PolarCodes/FrenkelIntegral.lean`, `PolarCodes/HockeyStick.lean`, `PolarCodes/RankDeficientFrenkel.lean` |
| Partial-trace DPI & Lemma 5.1(a) | `relEntropy_partialTrace₂_le`, `fidelityParam_le_sqrt_condEntropy` | `PolarCodes/DataProcessing.lean` |
| Lemma 3.2 (Equal-support hockey-stick measure, explicit finiteness) | `lemma_3_2_hockeyStick_measure`, `lemma_3_2_hockeyStick_measure_equalSupport` | `PolarCodes/HockeyStickMeasure.lean`, `PolarCodes/Refinements.lean` |
| Proposition 3.3 (QJJS + classical equality) | `prop_3_3_qjjs`, `prop_3_3_qjjs_classical_equality` | `PolarCodes/QJJS.lean`, `PolarCodes/Refinements.lean` |
| **Theorem 1.3** (Nonlinear dephasing SDPI + tightness, explicit finiteness) | `theorem_1_3_dephasing_sdpi`, `theorem_1_3_dephasing_sdpi_relEntropy`, `theorem_1_3_equatorial_equality_relEntropy` | `PolarCodes/DephasingSDPI.lean`, `PolarCodes/Refinements.lean` |
| Lemma 4.1 (Gram-matrix dephasing reduction + charpoly + `relEntropy`) | `lemma_4_1_gram_dephasing`, `lemma_4_1_gram_dephasing_relEntropy` | `PolarCodes/GramDephasing.lean`, `PolarCodes/DivergenceCharacterizations.lean` |
| **Theorem 1.2(a)** (Hybrid Q-MGL: pure, BSC, classical) | `theorem_1_2a_pure`, `theorem_1_2a_bsc`, `theorem_1_2a_classical` | `PolarCodes/MrsGerberHybrid.lean`, `PolarCodes/MrsGerberClassical.lean` |
| Proposition 4.2 (Four-branch purification bound) | `prop_4_2_four_branch` | `PolarCodes/MrsGerber.lean` |
| Propositions 4.3 & 4.4 (Scalar splitting & contraction) | `prop_4_3_scalar`, `prop_4_4_potential_contraction_general` | `PolarCodes/SplittingBounds.lean` |
| **Theorem 1.2(b)** (Linear splitting & contraction) | `theorem_1_2b_linear_splitting`, `theorem_1_2b_potential_contraction` | `PolarCodes/MrsGerber.lean` |
| Lemma 5.1(b) (Synthetic fidelity evolution) | `fidelityParam_plusChannel`, `fidelityParam_minusChannel_le` | `PolarCodes/QuantumProps.lean`, `PolarCodes/Bhattacharyya.lean` |
| Lemmas 5.2, 5.3, 5.4 (Three-stage polarization) | `lemma_5_2_stage1`, `lemma_5_3_stage2`, `lemma_5_4_stage3` | `PolarCodes/Polarization.lean`, `PolarCodes/PolarizationFine.lean` |
| Arıkan `G_N`, `W_n^{(i)}`, QSC decoder, Wilde–Guha bound | `arikanTransform`, `synthChannel`, `qscPolarCode`, `wilde_guha_qsc_bound` | `PolarCodes/NoncommutativeUnion.lean`, `PolarCodes/ArikanTransform.lean`, `PolarCodes/PolarCoding.lean` |
| **Theorem 1.1** (Syntactically pinned QSC poly-blocklength polar codes) | `theorem_1_1_quantum_polar_poly_blocklength`, `theorem_1_1_coding_poly_blocklength` | `PolarCodes/MainTheorem.lean`, `PolarCodes/PolarCoding.lean` |
| **Corollary 5.5** (Renes–Wilde amplitude/phase c-q polarization reduction) | `corollary_5_5_simultaneous_css_polarization`, `corollary_5_5_quantum_private_polar_coding` | `PolarCodes/MainTheorem.lean`, `PolarCodes/QuantumPolarCoding.lean` |

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
