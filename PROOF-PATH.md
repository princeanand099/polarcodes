# Proof Architecture & Dependency Path

1. **Analytic Core (Sections 2–4)**:
   - `BinaryEntropy` → `ScalarSupplements` → `PhiAndFuchs` establishes `phi`, `h2`, `h2Inv`, `binConv`, standalone `phi` regularity/convexity (`hasDerivAt_phi_cParam`, `continuousOn_phi`, `strictMonoOn_phi`, `strictConvexOn_phi`), Fuchs–van de Graaf (`one_sub_rootFidelity_le_traceDist`, `traceDist_le_sqrt_one_sub_rootFidelity_sq`), and `hockeyStick_eq_sSup`.
   - `QuantumStates` → `SpectralTrace` → `FrenkelHelpers` → `FrenkelIntegral` → `HockeyStick` → `RankDeficientFrenkel` derives Eq. (3.7) and Eq. (3.8) for full-rank and rank-deficient `suppSubset ρ σ` states (`relEntropy_frenkel_integral_of_suppSubset`, `relEntropy_hockeyStick_integral_of_suppSubset`).
   - `HockeyStickMeasure` → `QJJS` → `GramDephasing` → `DephasingSDPI` → `Refinements` → `DivergenceCharacterizations` proves Lemma 3.2, Lemma 4.1 (`lemma_4_1_gram_dephasing`, `lemma_4_1_gram_dephasing_relEntropy`), and Theorem 1.3 (`theorem_1_3_dephasing_sdpi`, `theorem_1_3_dephasing_sdpi_relEntropy`, `theorem_1_3_equatorial_equality_relEntropy`).

2. **Polarization & Coding Layer (Section 5 & Theorems 1.1–1.2)**:
   - `QuantumProps` + `Bhattacharyya` → `MrsGerberHybrid` + `MrsGerberClassical` → `MrsGerber` → `Polarization` + `PolarizationFine` → `MainTheorem` proves `theorem_1_2a_pure`, `theorem_1_2a_bsc`, `theorem_1_2a_classical`, `theorem_1_2b_linear_splitting`, `theorem_1_2b_potential_contraction`, and `theorem_1_1_quantum_polar_poly_blocklength`.
   - `NoncommutativeUnion` + `ArikanTransform` → `PolarCoding` proves `wilde_guha_qsc_bound`, `wilde_guha_qsc_avg_bound`, and `theorem_1_1_coding_poly_blocklength` with `qscPolarCode`.

3. **Quantum & Private Operational Layer (Corollary 5.5)**:
   - `ChannelDuality` + `ChannelEquiv` + `ChannelDualityEquiv` + `QuantumChannels` → `QuantumPolarCodingBase` + `QuantumPolarCoding` proves `prop_2_2_D2_var_isoEquiv`, `amp_phase_symCapacity_sum`, `degradable_assistance_subset_unpolarized`, and `corollary_5_5_quantum_private_polar_coding`.
   - `PrivatePolarCoding` formalizes trace-distance duality (`T(W⊥(0), W⊥(1)) = Z(W)`), randomized wiretap privacy amplification over `(𝒩.complementary)^⊗N`, and `exists_wiretap_frozen_good`.
   - `CoherentQuantumPolarCoding` formalizes `CPTPMap.tensorPow`, Walsh–Hadamard phase-randomized `cssPolarEncoder`, `exists_uhlmann_unitary`, and `exists_coherent_css_decoder`.
   - `OperationalCorollary55` proves `corollary_5_5_operational_quantum_private_polar_coding` uniting both operational codes with structurally pinned `assistSet = assistPinned`.
