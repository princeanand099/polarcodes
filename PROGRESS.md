# Formalization Progress Record

- **Current Stage**: Stage 4 (Proving core modules in dependency order, zero-`sorry`, zero-`axiom`)
- **Last Updated**: 2026-11-24

## CI-Verified Zero-`sorry` Modules (0 custom axioms)

- [x] `PolarCodes/BinaryEntropy.lean` — `h2`, `h2Inv`, `binConv`, `gc`, `gq`, `deltaGap`, `cParam`, `phiParam`, `phi`, `phiExt`, `phiDerivParam`, `betaParam`, `gx`, `strictConcaveOn_h2`, `convexOn_h2Inv`, `antitoneOn_deltaGap`, and **Lemma 3.1** (`lemma_3_1_tangent`, `lemma_3_1_gx_nonneg`).
- [x] `PolarCodes/QuantumStates.lean` — `DensityOp`, `sqrtMat`, `sqrtMat_mul_self`, `mix`, `midpoint`, `tensor`, `conjUnitary`, `vonNeumannEntropy`, `relEntropy`, `qjs`, `hockeyStick`, `traceDist`, `rootFidelity`.
- [x] `PolarCodes/Channels.lean` — `CQChannel`, `condEntropy`, `symCapacity`, `fidelityParam`, `potential`, `ketBraBool`, **Definition 2.1** (`checkCombine`, `varCombine`, `minusChannel`, `plusChannel`), `IsPureState`, `IsClassical`.
- [x] `PolarCodes/SplittingBounds.lean` — 4-term `log` Taylor bounds, `theta0_gt` (`θ₀ > 0.05673`), `theta2_gt_theta0`, `Lambda0_lt` (`Λ₀ < 0.99960`), **Proposition 4.3** (`prop_4_3_region1`, `prop_4_3_region2`, `prop_4_3_scalar`), and **Proposition 4.4** (`prop_4_4_potential_contraction_general`).
- [x] `PolarCodes/Polarization.lean` — Binary-tree probability space (`treeAvg`, `treeProb`), Markov inequality (`treeProb_markov`), **Doob's maximal inequality** (`tree_doob_maximal`), and **Hoeffding's inequality** (`tree_hoeffding_lower`).

## Remaining Modules to Formalize

- [ ] `PolarCodes/Polarization.lean` — Stages 1–3 (**Lemmas 5.2, 5.3, 5.4**) and abstract polynomial-blocklength rate/error theorem.
- [ ] `PolarCodes/BinaryEntropy.lean` — Wyner–Ziv convexity of `gc` (`convexOn_gc`) and endpoint limit (Eq. 1.8).
- [ ] `PolarCodes/Channels.lean` — Entropy conservation (Eq. 2.8) and Renes' channel duality (**Proposition 2.2** & Eq. 2.9).
- [ ] `PolarCodes/HockeyStick.lean` — Frenkel's hockey-stick integral representation, **Lemma 3.2**, and **Proposition 3.3** (QJJS).
- [ ] `PolarCodes/DephasingSDPI.lean` — **Theorem 1.3** (Nonlinear SDPI for Qubit Dephasing).
- [ ] `PolarCodes/MrsGerber.lean` — **Lemma 4.1**, **Theorem 1.2(a)**, **Proposition 4.2**, and **Theorem 1.2(b)**.
- [ ] `PolarCodes/Bhattacharyya.lean` — **Lemma 5.1** (Quantum Bhattacharyya evolution & entropy relation).
- [ ] `PolarCodes/MainTheorem.lean` — Wilde–Guha SC decoder bound, **Theorem 1.1**, and **Corollary 5.5**.
- [ ] `PolarCodes/SanityChecks.lean`, `PolarCodes/AuditAxioms.lean`, `comparator/ChallengeDefs.lean`, `comparator/Challenge.lean`, `comparator/Solution.lean`.
- [ ] Full verification CI (`full_verify: true`: `lake build`, hygiene check, `AuditAxioms`, `lake comparator`).
