# PolarCodes

Lean 4 formalization of *Polynomial-Blocklength Quantum Polar Codes via Nonlinear Dephasing Contraction* (Prince Anand, 2026).

Lean is pinned to `v4.35.0` (see `lean-toolchain`) with Mathlib4 and `leanprover/comparator` pinned in `lakefile.toml` and `lake-manifest.json`.

## Main Results

| Manuscript Result | Lean Declaration | Module |
| :--- | :--- | :--- |
| Theorem 1.1 (Polarization fraction) | `PolarCodes.theorem_1_1_quantum_polar_poly_blocklength` | `PolarCodes/MainTheorem.lean` |
| Theorem 1.1 (QSC polar coding) | `PolarCodes.theorem_1_1_coding_poly_blocklength` | `PolarCodes/PolarCoding.lean` |
| Theorem 1.2(a) (Pure-state, BSC, classical Q-MGL) | `PolarCodes.theorem_1_2a_pure`, `PolarCodes.theorem_1_2a_bsc`, `PolarCodes.theorem_1_2a_classical` | `PolarCodes/MrsGerberHybrid.lean`, `PolarCodes/MrsGerberClassical.lean` |
| Theorem 1.2(a) Remark (BSC & pure-state equality) | `PolarCodes.theorem_1_2a_bsc_equality`, `PolarCodes.theorem_1_2a_pure_equality` | `PolarCodes/MrsGerberEquality.lean` |
| Theorem 1.2(b) (Linear splitting & potential contraction) | `PolarCodes.theorem_1_2b_linear_splitting`, `PolarCodes.theorem_1_2b_potential_contraction` | `PolarCodes/MrsGerber.lean` |
| Theorem 1.3 (Nonlinear dephasing SDPI & equality) | `PolarCodes.theorem_1_3_dephasing_sdpi`, `PolarCodes.theorem_1_3_dephasing_sdpi_relEntropy`, `PolarCodes.theorem_1_3_equatorial_equality_relEntropy` | `PolarCodes/DephasingSDPI.lean`, `PolarCodes/Refinements.lean` |
| Corollary 5.5 (Simultaneous CSS polarization) | `PolarCodes.corollary_5_5_simultaneous_css_polarization`, `PolarCodes.corollary_5_5_quantum_private_polar_coding` | `PolarCodes/MainTheorem.lean`, `PolarCodes/QuantumPolarCoding.lean` |
| Corollary 5.5 (Operational wiretap & coherent CSS coding) | `PolarCodes.corollary_5_5_operational_quantum_private_polar_coding` | `PolarCodes/OperationalCorollary55.lean` |
| Proposition 2.2 (Renes channel duality D1–D3) | `PolarCodes.prop_2_2_D1`, `PolarCodes.prop_2_2_D2_var_isoEquiv`, `PolarCodes.prop_2_2_D2_channelEquiv`, `PolarCodes.prop_2_2_D3_channelEquiv` | `PolarCodes/ChannelDuality.lean`, `PolarCodes/ChannelDualityEquiv.lean`, `PolarCodes/ChannelEquiv.lean` |
| Section 2.1 (Divergence & entropy characterizations) | `PolarCodes.one_sub_rootFidelity_le_traceDist`, `PolarCodes.traceDist_le_sqrt_one_sub_rootFidelity_sq`, `PolarCodes.hockeyStick_isGreatest`, `PolarCodes.hockeyStick_eq_sSup`, `PolarCodes.vonNeumannEntropy_mem_Icc`, `PolarCodes.relEntropy_eq_zero_iff`, `PolarCodes.qjs_eq_avg_relEntropy` | `PolarCodes/PhiAndFuchs.lean`, `PolarCodes/DivergenceCharacterizations.lean` |
| Section 3 (Lemma 3.1, Eqs. 3.7–3.8, Lemma 3.2, Prop. 3.3) | `PolarCodes.strictConvexOn_phi`, `PolarCodes.relEntropy_frenkel_integral_of_suppSubset`, `PolarCodes.relEntropy_hockeyStick_integral_of_suppSubset`, `PolarCodes.lemma_3_2_hockeyStick_measure_equalSupport`, `PolarCodes.prop_3_3_qjjs` | `PolarCodes/PhiAndFuchs.lean`, `PolarCodes/RankDeficientFrenkel.lean`, `PolarCodes/Refinements.lean`, `PolarCodes/QJJS.lean` |
| Section 4 (Lemma 4.1, Propositions 4.2–4.4) | `PolarCodes.lemma_4_1_gram_dephasing`, `PolarCodes.lemma_4_1_gram_dephasing_relEntropy`, `PolarCodes.prop_4_2_four_branch`, `PolarCodes.prop_4_3_asymptotic`, `PolarCodes.prop_4_4_potential_contraction_general` | `PolarCodes/GramDephasing.lean`, `PolarCodes/DivergenceCharacterizations.lean`, `PolarCodes/MrsGerber.lean`, `PolarCodes/ScalarSupplements.lean`, `PolarCodes/SplittingBounds.lean` |

## Setup

Install `elan` if `lake` is not already available, then clone and build:

```bash
git clone https://github.com/princeanand099/polarcodes.git
cd polarcodes
lake exe cache get
lake build PolarCodes Solution
```

## Verification

```bash
lake env lean PolarCodes/AuditAxioms.lean
lake comparator
rg -n '\b(sorry|sorryAx|admit|axiom|native_decide|unsafe|unsafeCast|implemented_by|extern|partial|skipKernelTC|local instance)\b' PolarCodes.lean PolarCodes/ comparator/ChallengeDefs.lean comparator/Solution.lean
```

`PolarCodes/AuditAxioms.lean` lists only `propext`, `Classical.choice`, and `Quot.sound` across all 48 audited theorems; `lake comparator` checks the standalone challenge statements in `comparator/Challenge.lean` against `comparator/Solution.lean`.

## Repository Documentation

- `PROOF-PATH.md`: Module dependency structure and proof architecture.
- `PROGRESS.md`: Module inventory (41 library modules).
- `EXTERNAL-AXIOMS.md`: Axiom dependency record.
- `ATTRIBUTION.md` and `CITATION.cff`: References and citation metadata.
