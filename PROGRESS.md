# Module Inventory

41 library modules under `PolarCodes/`, together with standalone comparator modules under `comparator/`.

| Module | Contents |
| :--- | :--- |
| `PolarCodes.BinaryEntropy` | `h2`, `h2Inv`, `binConv`, `gc`, `gq`, `deltaGap`, `phi`, Lemma 3.1 |
| `PolarCodes.QuantumStates` | `DensityOp`, `vonNeumannEntropy`, `relEntropy`, `qjs`, `hockeyStick`, `rootFidelity`, `traceDist` |
| `PolarCodes.Channels` | `CQChannel`, `checkCombine`, `varCombine`, `minusChannel`, `plusChannel`, `polarChannelTree` |
| `PolarCodes.QuantumProps` | `fidelityParam`, `condEntropy`, `symCapacity`, `entropy_conservation`, `fidelityParam_plusChannel` |
| `PolarCodes.ScalarSupplements` | `convexOn_gc`, `prop_4_3_asymptotic` |
| `PolarCodes.Bhattacharyya` | Uhlmann purification, `fidelityParam_minusChannel_le`, Helstrom bound |
| `PolarCodes.SpectralTrace` | `posPartMat`, `negPartMat`, `posPartTrace`, `negPartTrace`, Sylvester's law of inertia |
| `PolarCodes.NoncommutativeUnion` | `sen_noncommutative_union_bound` |
| `PolarCodes.ChannelDuality` | `CQChannel.dual`, `bscChannel`, `becChannel`, `pureChannel`, Proposition 2.2 (D1–D3) |
| `PolarCodes.FrenkelHelpers` | Measurability and Lebesgue integral lemmas for the Hermitian pencil |
| `PolarCodes.FrenkelIntegral` | `relEntropy_frenkel_integral` (Eq. 3.7, full-rank) |
| `PolarCodes.DataProcessing` | Partial-trace data processing inequality, Lemma 5.1(a) |
| `PolarCodes.HockeyStick` | `relEntropy_hockeyStick_integral` (Eq. 3.8, full-rank), convexity and Stieltjes foundations |
| `PolarCodes.QuantumChannels` | `CPTPMap`, `ampChannel`, `phaseChannel`, `symCoherentInfo`, general CPTP DPI |
| `PolarCodes.HockeyStickMeasure` | `lemma_3_2_hockeyStick_measure` (full-rank), `qjs_lt_one_posDef` |
| `PolarCodes.QJJS` | `prop_3_3_qjjs` |
| `PolarCodes.GramDephasing` | `dephaseState`, `dephaseCoherence`, `gramState`, `lemma_4_1_gram_dephasing` |
| `PolarCodes.DephasingSDPI` | `theorem_1_3_dephasing_sdpi`, `theorem_1_3_equatorial_equality` |
| `PolarCodes.MrsGerberHybrid` | `theorem_1_2a_pure`, `theorem_1_2a_bsc` |
| `PolarCodes.MrsGerberClassical` | `theorem_1_2a_classical` |
| `PolarCodes.MrsGerberEquality` | `theorem_1_2a_bsc_equality`, `theorem_1_2a_pure_equality` |
| `PolarCodes.MrsGerber` | `prop_4_2_four_branch`, `theorem_1_2b_linear_splitting`, `theorem_1_2b_potential_contraction` |
| `PolarCodes.ChannelEquiv` | `IsoEquiv`, `ChannelEquiv`, `DegradedTo`, `prop_2_2_D3_channelEquiv` |
| `PolarCodes.ChannelDualityEquiv` | `prop_2_2_D2_var_isoEquiv`, `prop_2_2_D2_channelEquiv` |
| `PolarCodes.Polarization` | Martingale polarization, Doob maximal and Hoeffding bounds, Lemmas 5.2–5.3 |
| `PolarCodes.PolarizationFine` | Lemma 5.4, abstract polynomial-blocklength polarization |
| `PolarCodes.SplittingBounds` | `theta0`, `Lambda0`, Propositions 4.3–4.4 |
| `PolarCodes.MainTheorem` | `theorem_1_1_quantum_polar_poly_blocklength`, `corollary_5_5_simultaneous_css_polarization` |
| `PolarCodes.Refinements` | `lemma_3_2_hockeyStick_measure_equalSupport`, `prop_3_3_qjjs_classical_equality`, `theorem_1_3_dephasing_sdpi_relEntropy`, `theorem_1_3_equatorial_equality_relEntropy` |
| `PolarCodes.ArikanTransform` | `arikanTransform`, `synthChannel`, `productState` |
| `PolarCodes.PhiAndFuchs` | Lemma 3.1 `phi` regularity/convexity, Fuchs–van de Graaf (Section 2.1), `hockeyStick_isGreatest`, `hockeyStick_eq_sSup`, `vonNeumannEntropy_mem_Icc` |
| `PolarCodes.RankDeficientFrenkel` | `relEntropy_frenkel_integral_of_suppSubset`, `relEntropy_hockeyStick_integral_of_suppSubset` |
| `PolarCodes.DivergenceCharacterizations` | `relEntropy_eq_zero_iff`, `qjs_mem_Icc`, `qjs_eq_zero_iff`, `qjs_eq_one_iff`, `qjs_eq_avg_relEntropy`, `rootFidelity_block_diagonal`, `lemma_4_1_gram_dephasing_relEntropy` |
| `PolarCodes.PolarCoding` | `qscPolarCode`, `wilde_guha_qsc_bound`, `wilde_guha_qsc_avg_bound`, `theorem_1_1_coding_poly_blocklength` |
| `PolarCodes.QuantumPolarCodingBase` | `amp_phase_symCapacity_sum`, `degradable_assistance_subset_unpolarized` |
| `PolarCodes.QuantumPolarCoding` | `CSSPrivatePolarCode`, `corollary_5_5_quantum_private_polar_coding` |
| `PolarCodes.PrivatePolarCoding` | `OperationalPrivatePolarCode`, `traceDist_dual_eq_fidelityParam`, `exists_wiretap_frozen_good` |
| `PolarCodes.CoherentQuantumPolarCoding` | `OperationalQuantumPolarCode`, `cssPolarEncoder`, `exists_uhlmann_unitary`, `exists_coherent_css_decoder` |
| `PolarCodes.OperationalCorollary55` | `corollary_5_5_operational_quantum_private_polar_coding` |
| `PolarCodes.SanityChecks` | Instantiation checks on `bscChannel (1 / 4)`, Theorem 1.1, and Corollary 5.5 |
| `PolarCodes.AuditAxioms` | `#print axioms` audit across 48 declarations |
