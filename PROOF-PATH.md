# Manuscript-to-Lean Correspondence & Dependency DAG

Manuscript: *Polynomial-Blocklength Quantum Polar Codes via Nonlinear Dephasing Contraction* (Prince Anand, November 2026).

| Manuscript Result | Location | Planned Module | Lean Declaration | Dependencies | Fidelity | Proof Status |
|---|---|---|---|---|---|---|
| Binary entropy `h2`, `h2Inv`, `binConv`, `gc`, `gq`, `Δ` | Sec 1.2 | `PolarCodes/BinaryEntropy.lean` | `h2`, `h2Inv`, `binConv`, `gc`, `gq`, `deltaGap` | Mathlib | Checked | In progress |
| Lemma 3.1 (Perspective-Symmetric Scalar Inequality) | Sec 3.1 | `PolarCodes/BinaryEntropy.lean` | `lemma_3_1_gx_nonneg` | `h2`, `phiParam` | Planned | Pending |
| Sec 2.1 Entropies, Divergences, Distinguishability | Sec 2.1 | `PolarCodes/QuantumStates.lean` | `DensityOp`, `vonNeumannEntropy`, `relEntropy`, `qjs`, `hockeyStick`, `rootFidelity` | Mathlib | Planned | Pending |
| Def 2.1 & Eq (2.8) Polar Channel Combinations & Conservation | Sec 2.2 | `PolarCodes/Channels.lean` | `checkCombine`, `varCombine`, `entropy_conservation` | `QuantumStates` | Planned | Pending |
| Proposition 2.2 (Renes' Channel Duality) & Eq (2.9) | Sec 2.3 | `PolarCodes/Channels.lean` | `prop_2_2_renes_duality`, `check_duality_identity` | `Channels` | Planned | Pending |
| Lemma 3.2 (Simultaneous Hockey-Stick Representation) | Sec 3.1 | `PolarCodes/HockeyStick.lean` | `lemma_3_2_hockey_stick_rep` | `QuantumStates` | Planned | Pending |
| Proposition 3.3 (Quantum Jeffreys–Jensen–Shannon Inequality) | Sec 3.2 | `PolarCodes/HockeyStick.lean` | `prop_3_3_qjjs` | Lemma 3.1, Lemma 3.2 | Planned | Pending |
| Theorem 1.3 (Nonlinear SDPI for Qubit Dephasing) | Sec 1.2, 3.2 | `PolarCodes/DephasingSDPI.lean` | `theorem_1_3_dephasing_sdpi` | Prop 3.3, Lemma 3.1 | Planned | Pending |
| Lemma 4.1 (Gram-Matrix Dephasing Reduction) | Sec 4.1 | `PolarCodes/MrsGerber.lean` | `lemma_4_1_gram_matrix` | `QuantumStates`, `DephasingSDPI` | Planned | Pending |
| Theorem 1.2(a) (Hybrid Quantum Mrs. Gerber Bounds) | Sec 1.2, 4.1 | `PolarCodes/MrsGerber.lean` | `theorem_1_2a_pure`, `theorem_1_2a_classical` | Thm 1.3, Lemma 4.1, Prop 2.2 | Planned | Pending |
| Proposition 4.2 (Four-Branch Purification Bound) | Sec 4.2 | `PolarCodes/MrsGerber.lean` | `prop_4_2_four_branch` | Thm 1.2(a), Prop 2.2 | Planned | Pending |
| Proposition 4.3 (Linear Splitting Constant & Asymptotics) | Sec 4.2 | `PolarCodes/MrsGerber.lean` | `prop_4_3_linear_splitting`, `prop_4_3_endpoint_limit` | Prop 4.2 | Planned | Pending |
| Proposition 4.4 (Uniform Potential Contraction) | Sec 4.2 | `PolarCodes/MrsGerber.lean` | `prop_4_4_potential_contraction` | Prop 4.3 | Planned | Pending |
| Theorem 1.2(b) (General Quantum Mrs. Gerber Bounds) | Sec 1.2, 4.2 | `PolarCodes/MrsGerber.lean` | `theorem_1_2b_general` | Prop 4.2–4.4 | Planned | Pending |
| Lemma 5.1 (Quantum Bhattacharyya Evolution) | Sec 5.1 | `PolarCodes/Bhattacharyya.lean` | `lemma_5_1_bhattacharyya` | `Channels`, `QuantumStates` | Planned | Pending |
| Lemma 5.2 (Stage 1: Rough Polarization) | Sec 5.2 | `PolarCodes/Polarization.lean` | `lemma_5_2_stage1` | Prop 4.4, Lemma 5.1 | Planned | Pending |
| Lemma 5.3 (Stage 2: Bootstrap Polarization) | Sec 5.2 | `PolarCodes/Polarization.lean` | `lemma_5_3_stage2` | Lemma 5.1, Lemma 5.2 | Planned | Pending |
| Lemma 5.4 (Stage 3: Fine Polarization) | Sec 5.2 | `PolarCodes/Polarization.lean` | `lemma_5_4_stage3` | Lemma 5.1, Lemma 5.3 | Planned | Pending |
| Theorem 1.1 (Polynomial-Blocklength C-Q Polar Codes) | Sec 1.2, 5.2 | `PolarCodes/MainTheorem.lean` | `theorem_1_1_poly_polar_codes` | Lemmas 5.2–5.4 | Planned | Pending |
| Corollary 5.5 (Private & Quantum Polar Coding) | Sec 5.3 | `PolarCodes/MainTheorem.lean` | `corollary_5_5_private_quantum` | Thm 1.1 | Planned | Pending |
