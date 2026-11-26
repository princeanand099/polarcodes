# Proof Architecture & Dependency Path

1. **Analytic Core (Sections 2–4)**:
   - `BinaryEntropy` → `ScalarSupplements` → `PhiAndFuchs` establishes `phi`, `h2`, `h2Inv`, `binConv`, `fuchs_van_de_graaf`, and `hockeyStick_variational_eq`.
   - `QuantumStates` → `SpectralTrace` → `FrenkelHelpers` → `FrenkelIntegral` → `HockeyStick` → `RankDeficientFrenkel` derives Eq. (3.7) and Eq. (3.8) for full-rank and rank-deficient `suppSubset ρ σ` states.
   - `HockeyStickMeasure` → `QJJS` → `GramDephasing` → `DephasingSDPI` → `Refinements` → `DivergenceCharacterizations` proves Lemma 3.2, Lemma 4.1, and Theorem 1.3.

2. **Polarization & Coding Layer (Section 5 & Theorem 1.1–1.2)**:
   - `QuantumProps` + `Bhattacharyya` → `MrsGerberHybrid` + `MrsGerberClassical` → `MrsGerber` → `Polarization` + `PolarizationFine` → `MainTheorem` proves `theorem_1_2_a_bhattacharyya_contraction`, `theorem_1_2_b_entropy_contraction`, and `theorem_1_1_quantum_polar_poly_blocklength`.
   - `NoncommutativeUnion` + `ArikanTransform` → `PolarCoding` proves `wilde_guha_qsc_bound` and `theorem_1_1_coding_poly_blocklength` with `qscPolarCode`.

3. **Quantum & Private Operational Layer (Corollary 5.5)**:
   - `ChannelDuality` + `ChannelEquiv` + `ChannelDualityEquiv` + `QuantumChannels` → `QuantumPolarCodingBase` + `QuantumPolarCoding` proves `amp_phase_symCapacity_sum`, `degradable_assistance_subset_unpolarized`, and `corollary_5_5_quantum_private_polar_coding`.
   - `PrivatePolarCoding` formalizes trace-distance duality (`T(W⊥(0), W⊥(1)) = Z(W)`), randomized wiretap privacy amplification over `(𝒩.complementary)^⊗N`, and `exists_wiretap_frozen_good`.
   - `CoherentQuantumPolarCoding` formalizes `CPTPMap.tensorPow`, Walsh–Hadamard phase-randomized `cssPolarEncoder`, `exists_uhlmann_unitary`, and `exists_coherent_css_decoder`.
   - `OperationalCorollary55` proves `corollary_5_5_operational_quantum_private_polar_coding` uniting both operational codes with structurally pinned `assistSet = assistPinned`.
