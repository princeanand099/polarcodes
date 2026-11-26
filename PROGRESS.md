# Formalization Progress

**Status:** Complete (40 modules, 0 `sorry`s, 0 custom axioms).

| Module | Contents | Status |
| :--- | :--- | :--- |
| `PolarCodes.BinaryEntropy` | Binary entropy `h2`, inverse `h2Inv`, `binConv`, `phi` | Proved |
| `PolarCodes.QuantumStates` | `DensityOp`, `vonNeumannEntropy`, `relEntropy`, `qjs`, `rootFidelity`, `traceDist` | Proved |
| `PolarCodes.Channels` | `CQChannel`, `minusChannel`, `plusChannel`, `polarChannelTree` | Proved |
| `PolarCodes.QuantumProps` | `fidelityParam`, `condEntropy`, `symCapacity`, uniform block fidelity | Proved |
| `PolarCodes.ScalarSupplements` | Scalar `phi` inequalities and `h2` convexity/concavity helpers | Proved |
| `PolarCodes.Bhattacharyya` | `theorem_1_2_a_bhattacharyya_contraction`, Helstrom error bound | Proved |
| `PolarCodes.SpectralTrace` | `posPartMat`, `negPartMat`, `posPartTrace`, `negPartTrace`, Sylvester's law | Proved |
| `PolarCodes.NoncommutativeUnion` | Sen's noncommutative union bound `sen_noncommutative_union_bound` | Proved |
| `PolarCodes.ChannelDuality` | `CQChannel.dual`, `bscChannel`, `becChannel`, `pureChannel`, (D1) | Proved |
| `PolarCodes.FrenkelHelpers` | Measure-theoretic helpers for Frenkel's integral | Proved |
| `PolarCodes.FrenkelIntegral` | `relEntropy_frenkel_integral` (Eq. 3.7, `PosDef`) | Proved |
| `PolarCodes.DataProcessing` | Data processing inequality for `relEntropy` and `qjs`, Lemma 5.1(a) | Proved |
| `PolarCodes.HockeyStick` | `hockeyStick`, `relEntropy_hockeyStick_integral` (Eq. 3.8, `PosDef`) | Proved |
| `PolarCodes.QuantumChannels` | `CPTPMap`, `ampChannel`, `phaseChannel`, `symCoherentInfo`, DPI | Proved |
| `PolarCodes.HockeyStickMeasure` | `lemma_3_2_hockeyStick_measure` (with `≠ ⊤` finiteness) | Proved |
| `PolarCodes.QJJS` | Quantum Jensen–Shannon–hockey-stick representation | Proved |
| `PolarCodes.GramDephasing` | `lemma_4_1_gram_dephasing` (charpoly, `p ≤ 1/2`, entropy) | Proved |
| `PolarCodes.DephasingSDPI` | `theorem_1_3_dephasing_sdpi`, `theorem_1_3_equatorial_equality` | Proved |
| `PolarCodes.MrsGerberHybrid` | Hybrid Mrs. Gerber inequality | Proved |
| `PolarCodes.MrsGerberClassical` | Classical Mrs. Gerber inequality | Proved |
| `PolarCodes.MrsGerber` | `quantum_mrs_gerber` (`H(W^-) ≤ 1 - Φ(H(W))`) | Proved |
| `PolarCodes.ChannelEquiv` | `IsoEquiv`, `ChannelEquiv`, `DegradedTo` | Proved |
| `PolarCodes.ChannelDualityEquiv` | Prop 2.2 (D2)–(D3) + `prop_2_2_D2_var_isoEquiv` | Proved |
| `PolarCodes.Polarization` | Martingale polarization convergence | Proved |
| `PolarCodes.PolarizationFine` | Fine polynomial-blocklength polarization & `polar_error_exponent_bound` | Proved |
| `PolarCodes.SplittingBounds` | Splitting-tree entropy bounds | Proved |
| `PolarCodes.MainTheorem` | `theorem_1_2_b_entropy_contraction`, `theorem_1_1_quantum_polar_poly_blocklength` | Proved |
| `PolarCodes.Refinements` | Equal-support `lemma_3_2_hockeyStick_measure_equalSupport`, `relEntropy` Theorem 1.3 | Proved |
| `PolarCodes.ArikanTransform` | `arikanTransform`, `synthChannel`, `productState` | Proved |
| `PolarCodes.PhiAndFuchs` | Lemma 3.1 `phi` properties, `fuchs_van_de_graaf`, `hockeyStick_variational_eq` | Proved |
| `PolarCodes.RankDeficientFrenkel` | Eq. 3.7–3.8 for arbitrary `suppSubset ρ σ` | Proved |
| `PolarCodes.DivergenceCharacterizations` | `relEntropy_eq_zero_iff`, `qjs_mem_Icc`, `qjs_eq_zero_iff`, `qjs_eq_one_iff`, `rootFidelity_block_diagonal`, `lemma_4_1_gram_dephasing_relEntropy` | Proved |
| `PolarCodes.PolarCoding` | `qscPolarCode`, `wilde_guha_qsc_bound`, `theorem_1_1_coding_poly_blocklength` | Proved |
| `PolarCodes.QuantumPolarCodingBase` | `amp_phase_symCapacity_sum`, `degradable_assistance_subset_unpolarized` | Proved |
| `PolarCodes.QuantumPolarCoding` | `CSSPrivatePolarCode` (with `assistanceSet_spec`), `corollary_5_5_quantum_private_polar_coding` | Proved |
| `PolarCodes.PrivatePolarCoding` | `OperationalPrivatePolarCode`, `traceDist_dual_eq_fidelityParam`, `exists_wiretap_frozen_good` | Proved |
| `PolarCodes.CoherentQuantumPolarCoding` | `OperationalQuantumPolarCode`, `cssPolarEncoder`, `exists_coherent_css_decoder` | Proved |
| `PolarCodes.OperationalCorollary55` | `corollary_5_5_operational_quantum_private_polar_coding` | Proved |
| `PolarCodes.SanityChecks` | Non-vacuity checks on `bscChannel (1/4)`, Theorem 1.1, Corollary 5.5 | Proved |
| `PolarCodes.AuditAxioms` | Kernel `#print axioms` audit for all headline theorems | Proved |
