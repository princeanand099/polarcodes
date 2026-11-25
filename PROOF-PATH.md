# Proof Path & Module Dependency DAG

This document records the 24-module dependency structure of `PolarCodes`.

## Layer 1 — Scalar & Quantum Foundations
1. `PolarCodes/BinaryEntropy.lean` — `h2`, `h2Inv`, `binConv`, `gc`, `gq`, `deltaGap`, `antitoneOn_deltaGap`, **Lemma 3.1** (`lemma_3_1_gx_nonneg`).
2. `PolarCodes/QuantumStates.lean` — `DensityOp`, `eigvals`, `eigUnitary`, `sqrtMat`, `mix`, `midpoint`, `tensor`, `conjUnitary`, `vonNeumannEntropy`, `relEntropy`, `qjs`, `hockeyStick`, `traceDist`, `rootFidelity`.
3. `PolarCodes/Channels.lean` — `CQChannel`, `condEntropy`, `symCapacity`, `fidelityParam`, `potential`, `ketBraBool`, **Definition 2.1** (`checkCombine`, `varCombine`, `minusChannel`, `plusChannel`), `IsPureState`, `IsClassical`.
4. `PolarCodes/SplittingBounds.lean` — `theta0`, `theta2`, `Lambda0`, **Proposition 4.3** (`prop_4_3_scalar`), **Proposition 4.4** (`prop_4_4_potential_contraction_general`).
5. `PolarCodes/ScalarSupplements.lean` — Wyner–Ziv convexity (`convexOn_gc`) and Eq. (1.8) asymptotics (`prop_4_3_asymptotic`).

## Layer 2 — Channel Algebra, Purification & Duality
6. `PolarCodes/QuantumProps.lean` — Sylvester charpoly, unitary invariance, additivity, block midpoint entropy, **Eq. (2.7)–(2.8)** (`condEntropy_varCombine_eq`, `entropy_conservation`), **Lemma 5.1(b) plus** (`fidelityParam_plusChannel`).
7. `PolarCodes/GramDephasing.lean` — `pauliZTensorI`, `dephaseState`, `dephaseCoherence`, `pureState`, `gramState`, **Lemma 4.1** (`lemma_4_1_gram_dephasing`).
8. `PolarCodes/Bhattacharyya.lean` — Polar decomposition, `partialTrace₂`, Uhlmann purification (`exists_uhlmann_purification`), **Lemma 5.1(b) minus** (`fidelityParam_minusChannel_le`).
9. `PolarCodes/ChannelDuality.lean` — **Proposition 2.2** (`prop_2_2_D1`, `checkCombine_duality`, `prop_2_2_D2`, `prop_2_2_D3`).

## Layer 3 — Frenkel Integral, DPI, Hockey-Stick & Nonlinear SDPI (Section 3)
10. `PolarCodes/SpectralTrace.lean` — `posPartTrace`, `negPartTrace`, `negEigCount`, Sylvester's Law of Inertia (`negEigCount_congruence`).
11. `PolarCodes/FrenkelHelpers.lean` — Measurability and Lebesgue integral helpers for the Hermitian pencil `(1 - t) ρ + t σ + r I`.
12. `PolarCodes/FrenkelIntegral.lean` — **Frenkel's Integral Formula (Eq. 3.7)** (`relEntropy_frenkel_integral`).
13. `PolarCodes/DataProcessing.lean` — DPI (`relEntropy_partialTrace₂_le`, `qjs_partialTrace₂_le`), **Lemma 5.1(a)** (`condEntropy_ge_one_sub_h2`, `fidelityParam_le_sqrt_condEntropy`).
14. `PolarCodes/HockeyStick.lean` — **Eq. (3.8)** (`relEntropy_hockeyStick_integral`).
15. `PolarCodes/HockeyStickMeasure.lean` — **Lemma 3.2** (`lemma_3_2_hockeyStick_measure`).
16. `PolarCodes/QJJS.lean` — **Proposition 3.3** (`prop_3_3_qjjs_posDef`, `prop_3_3_qjjs`).
17. `PolarCodes/DephasingSDPI.lean` — **Theorem 1.3** (`theorem_1_3_dephasing_sdpi`, `theorem_1_3_equatorial_equality`).

## Layer 4 — Quantum Mrs. Gerber's Lemma & Polarization Splitting (Section 4)
18. `PolarCodes/MrsGerberHybrid.lean` — **Theorem 1.2(a)** pure-state and BSC branches (`theorem_1_2a_pure`, `theorem_1_2a_bsc`).
19. `PolarCodes/MrsGerberClassical.lean` — Simultaneous diagonalization and **Theorem 1.2(a)** classical branch (`theorem_1_2a_classical`).
20. `PolarCodes/MrsGerber.lean` — **Proposition 4.2** (`prop_4_2_four_branch`) and **Theorem 1.2(b)** (`theorem_1_2b_linear_splitting`, `theorem_1_2b_potential_contraction`).

## Layer 5 — Three-Stage Martingale Polarization & Main Theorems (Section 5)
21. `PolarCodes/Polarization.lean` — Binary-tree Doob maximal inequality, Hoeffding bound, `PolarProcess`, **Lemma 5.2** (`lemma_5_2_stage1`), **Lemma 5.3** (`lemma_5_3_stage2`).
22. `PolarCodes/PolarizationFine.lean` — **Lemma 5.4** (`lemma_5_4_stage3`), abstract **Theorem 1.1** (`polar_process_poly_blocklength`), abstract **Corollary 5.5** (`polar_process_dual_pair_poly_blocklength`).
23. `PolarCodes/MainTheorem.lean` — Concrete `polarChannelTree`, `cqPolarProcess`, **Theorem 1.1** (`theorem_1_1_quantum_polar_poly_blocklength`), **Corollary 5.5** (`corollary_5_5_simultaneous_css_polarization`).
24. `PolarCodes/SanityChecks.lean` — Concrete non-vacuity witnesses for Theorems 1.1, 1.2(b), and 1.3.

## Verification & Comparator Layer
- `PolarCodes/AuditAxioms.lean` — `#print axioms` audit across all 30 exported theorems.
- `comparator/ChallengeDefs.lean`, `comparator/Challenge.lean`, `comparator/Solution.lean`, `comparator.json` — Standalone statement lock verified by `lake comparator`.
