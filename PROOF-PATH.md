# Proof Path & Module Dependency DAG

This document records the 36-module dependency structure of `PolarCodes`.

## Layer 1 — Scalar & Quantum Foundations
1. `PolarCodes/BinaryEntropy.lean` — `h2`, `h2Inv`, `binConv`, `gc`, `gq`, `deltaGap`, `antitoneOn_deltaGap`, **Lemma 3.1** (`lemma_3_1_gx_nonneg`).
2. `PolarCodes/QuantumStates.lean` — `DensityOp`, `eigvals`, `eigUnitary`, `sqrtMat`, `mix`, `midpoint`, `tensor`, `conjUnitary`, `vonNeumannEntropy`, `suppSubset`, `relEntropy`, `qjs`, `hockeyStick`, `traceDist`, `rootFidelity`.
3. `PolarCodes/Channels.lean` — `CQChannel`, `condEntropy`, `symCapacity`, `fidelityParam`, `potential`, `ketBraBool`, **Definition 2.1** (`checkCombine`, `varCombine`, `minusChannel`, `plusChannel`), `IsPureState`, `IsClassical`.
4. `PolarCodes/SplittingBounds.lean` — `theta0`, `theta2`, `Lambda0`, **Proposition 4.3** (`prop_4_3_scalar`), **Proposition 4.4** (`prop_4_4_potential_contraction_general`).
5. `PolarCodes/ScalarSupplements.lean` — Wyner–Ziv convexity (`convexOn_gc`) and Eq. (1.8) asymptotics (`prop_4_3_asymptotic`).

## Layer 2 — Channel Algebra, Purification & Duality
6. `PolarCodes/QuantumProps.lean` — Sylvester charpoly, unitary invariance, additivity, block midpoint entropy, **Eq. (2.7)–(2.8)** (`condEntropy_varCombine_eq`, `entropy_conservation`), **Lemma 5.1(b) plus** (`fidelityParam_plusChannel`).
7. `PolarCodes/GramDephasing.lean` — `pauliZTensorI`, `dephaseState`, `dephaseCoherence`, `pureState`, `gramState`, **Lemma 4.1** (`lemma_4_1_gram_dephasing`, tightened to `p ∈ [0, 1/2]` with characteristic-polynomial coincidence).
8. `PolarCodes/Bhattacharyya.lean` — Polar decomposition, `partialTrace₂`, Uhlmann purification (`exists_uhlmann_purification`), **Lemma 5.1(b) minus** (`fidelityParam_minusChannel_le`).
9. `PolarCodes/ChannelDuality.lean` — **Proposition 2.2** entropic form (`prop_2_2_D1`, `checkCombine_duality`, `prop_2_2_D2`, `prop_2_2_D3`).

## Layer 3 — Frenkel Integral, CPTP DPI, Hockey-Stick & Nonlinear SDPI (Section 3)
10. `PolarCodes/SpectralTrace.lean` — `posPartTrace`, `negPartTrace`, `negEigCount`, Sylvester's Law of Inertia (`negEigCount_congruence`), `density_spectral_eq`.
11. `PolarCodes/FrenkelHelpers.lean` — Measurability and Lebesgue integral helpers for the Hermitian pencil `(1 - t) ρ + t σ + r I`.
12. `PolarCodes/FrenkelIntegral.lean` — **Frenkel's Integral Formula (Eq. 3.7, `PosDef`)** (`relEntropy_frenkel_integral`).
13. `PolarCodes/DataProcessing.lean` — Partial-trace DPI (`relEntropy_partialTrace₂_le`, `qjs_partialTrace₂_le`), **Lemma 5.1(a)** (`condEntropy_ge_one_sub_h2`, `fidelityParam_le_sqrt_condEntropy`).
14. `PolarCodes/QuantumChannels.lean` — Stinespring `CPTPMap`, `complementary`, `comp`, `IsDegradable`, and **General CPTP DPI** (`relEntropy_cptp_le`, `qjs_cptp_le`, `condEntropy_cptp_ge`).
15. `PolarCodes/HockeyStick.lean` — **Eq. (3.8, `PosDef`)** (`relEntropy_hockeyStick_integral`, `frenkel_lintegral_eq_hockeyStick_lintegral`).
16. `PolarCodes/RankDeficientFrenkel.lean` — **Eq. (3.7)–(3.8)** for arbitrary rank-deficient states satisfying `suppSubset ρ σ` (`relEntropy_frenkel_integral_of_suppSubset`, `relEntropy_hockeyStick_integral_of_suppSubset`).
17. `PolarCodes/PhiAndFuchs.lean` — Standalone **Lemma 3.1** properties of `phi` (`hasDerivAt_phi_cParam`, `continuousOn_phi`, `strictMonoOn_phi`, `strictConvexOn_phi`) and **Fuchs–van de Graaf (Eq. 2.3)** (`one_sub_rootFidelity_le_traceDist`, `traceDist_le_sqrt_one_sub_rootFidelity_sq`).
18. `PolarCodes/HockeyStickMeasure.lean` — **Lemma 3.2** (`lemma_3_2_hockeyStick_measure`, with explicit `relEntropy ≠ ⊤`) and `qjs_lt_one_posDef`.
19. `PolarCodes/QJJS.lean` — **Proposition 3.3** (`prop_3_3_qjjs_posDef`, `prop_3_3_qjjs`).
20. `PolarCodes/DephasingSDPI.lean` — **Theorem 1.3** (`theorem_1_3_dephasing_sdpi`, `theorem_1_3_equatorial_equality`).
21. `PolarCodes/Refinements.lean` — Equal-support **Lemma 3.2** (`lemma_3_2_hockeyStick_measure_equalSupport`), **Proposition 3.3** symmetric classical equality (`prop_3_3_qjjs_classical_equality`), and Umegaki relative-entropy **Theorem 1.3** (`theorem_1_3_dephasing_sdpi_relEntropy`, `theorem_1_3_equatorial_equality_relEntropy`, with explicit `relEntropy ≠ ⊤`).
22. `PolarCodes/DivergenceCharacterizations.lean` — Section 2.1 characterizations (`posPartMat_mul_negPartMat`, **Eq. 2.2** `hockeyStick_eq_sSup`, `qjs_eq_avg_relEntropy`, `relEntropy_eq_zero_iff`, `qjs_mem_Icc`, `qjs_eq_zero_iff`, `qjs_eq_one_iff`, `rootFidelity_block_diagonal`) and **Lemma 4.1** `relEntropy` Part 4 (`lemma_4_1_gram_dephasing_relEntropy`).
23. `PolarCodes/ChannelEquiv.lean` — `CQChannel.IsoEquiv`, `CQChannel.ChannelEquiv`, and **Proposition 2.2 (D3)** channel equivalence (`prop_2_2_D3_channelEquiv`).
24. `PolarCodes/ChannelDualityEquiv.lean` — **Proposition 2.2 (D2)** variable-node `IsoEquiv` (`prop_2_2_D2_var_isoEquiv`) and `ChannelEquiv` (`prop_2_2_D2_channelEquiv`).

## Layer 4 — Quantum Mrs. Gerber's Lemma & Polarization Splitting (Section 4)
25. `PolarCodes/MrsGerberHybrid.lean` — **Theorem 1.2(a)** pure-state and BSC branches (`theorem_1_2a_pure`, `theorem_1_2a_bsc`).
26. `PolarCodes/MrsGerberClassical.lean` — Simultaneous diagonalization and **Theorem 1.2(a)** classical branch (`theorem_1_2a_classical`).
27. `PolarCodes/MrsGerber.lean` — **Proposition 4.2** (`prop_4_2_four_branch`) and **Theorem 1.2(b)** (`theorem_1_2b_linear_splitting`, `theorem_1_2b_potential_contraction`).

## Layer 5 — Three-Stage Polarization, QSC Coding & Main Theorems (Section 5)
28. `PolarCodes/Polarization.lean` — Binary-tree Doob maximal inequality, Hoeffding bound, `PolarProcess`, **Lemma 5.2** (`lemma_5_2_stage1`), **Lemma 5.3** (`lemma_5_3_stage2`).
29. `PolarCodes/PolarizationFine.lean` — **Lemma 5.4** (`lemma_5_4_stage3`), `polar_error_exponent_bound`, abstract **Theorem 1.1** and **Corollary 5.5**.
30. `PolarCodes/MainTheorem.lean` — Concrete `polarChannelTree`, `cqPolarProcess`, fidelity-fraction **Theorem 1.1** (`theorem_1_1_quantum_polar_poly_blocklength`), simultaneous polarization **Corollary 5.5** (`corollary_5_5_simultaneous_css_polarization`).
31. `PolarCodes/NoncommutativeUnion.lean` — Helstrom projectors, Powers–Størmer inequality, Gao/Sen noncommutative union bound (`sen_noncommutative_union_bound`).
32. `PolarCodes/ArikanTransform.lean` — Product channel `W^{\otimes 2^n}`, Arıkan transform `G_N = B_N F^{\otimes n}`, synthesized channels `W_n^{(i)}` (`synthChannel`), exact correspondence (`synthChannel_condEntropy_eq`, `synthChannel_fidelityParam_eq`).
33. `PolarCodes/PolarCoding.lean` — `CosetPolarCode`, QSC sequential decoder (`qscPolarCode`), Wilde–Guha bound (`wilde_guha_qsc_bound`), and syntactically pinned QSC **Theorem 1.1** (`theorem_1_1_coding_poly_blocklength`).
34. `PolarCodes/QuantumPolarCodingBase.lean` — `symCoherentInfo`, Renes–Wilde `ampChannel` & `phaseChannel`, `amp_phase_symCapacity_sum`, `goodSet`/`veryNoisySet`/`unpolarizedSet`, `dual_unpolarized_fraction_le`, channel-tree duality & degradation monotonicity.
35. `PolarCodes/QuantumPolarCoding.lean` — `phaseChannel_dual_channelEquiv`, `degradable_amp_phase_sum_le_one`, `degradable_assistance_subset_unpolarized`, structurally pinned `CSSPrivatePolarCode`, and **Corollary 5.5** c-q polarization reduction (`corollary_5_5_quantum_private_polar_coding`).
36. `PolarCodes/SanityChecks.lean` — Nontrivial non-vacuity checks (`noiselessChannel`, `idQubitChannel`) for Theorems 1.1, 1.2(b), 1.3, and Corollary 5.5.

## Verification & Comparator Layer
- `PolarCodes/AuditAxioms.lean` — `#print axioms` audit across all 68 exported theorems.
- `comparator/ChallengeDefs.lean`, `comparator/Challenge.lean`, `comparator/Solution.lean`, `comparator.json` — Standalone docstring-free Mathlib-only statement lock across 13 headline theorems verified by `lake comparator`.
