# Proof Architecture

1. **Scalar and Quantum Foundations (Sections 2–3)**
   - `BinaryEntropy`, `ScalarSupplements`, and `PhiAndFuchs` define `h2`, `h2Inv`, `binConv`, `gc`, `gq`, `deltaGap`, and `phi`, establishing Lemma 3.1 (`hasDerivAt_phi_cParam`, `continuousOn_phi`, `strictMonoOn_phi`, `strictConvexOn_phi`), Fuchs–van de Graaf (`one_sub_rootFidelity_le_traceDist`, `traceDist_le_sqrt_one_sub_rootFidelity_sq`), variational hockey-stick attainment (`hockeyStick_isGreatest`, `hockeyStick_eq_sSup`), and `vonNeumannEntropy_mem_Icc`.
   - `QuantumStates`, `SpectralTrace`, `FrenkelHelpers`, `FrenkelIntegral`, `HockeyStick`, and `RankDeficientFrenkel` prove Eqs. (3.7)–(3.8) for full-rank states and under `suppSubset ρ σ`.
   - `HockeyStickMeasure`, `QJJS`, `GramDephasing`, `DephasingSDPI`, `Refinements`, and `DivergenceCharacterizations` prove Lemma 3.2, Proposition 3.3, Lemma 4.1, and Theorem 1.3.

2. **Quantum Mrs. Gerber Bounds and Polarization (Sections 4–5.2)**
   - `QuantumProps`, `Bhattacharyya`, `MrsGerberHybrid`, `MrsGerberClassical`, `MrsGerberEquality`, and `MrsGerber` prove Theorem 1.2(a) (including BSC and pure-state equality cases), Proposition 4.2, and Theorem 1.2(b).
   - `SplittingBounds`, `Polarization`, `PolarizationFine`, and `MainTheorem` prove Propositions 4.3–4.4, Lemmas 5.2–5.4, and `theorem_1_1_quantum_polar_poly_blocklength`.
   - `NoncommutativeUnion`, `ArikanTransform`, and `PolarCoding` prove `wilde_guha_qsc_bound`, `wilde_guha_qsc_avg_bound`, and `theorem_1_1_coding_poly_blocklength`.

3. **Channel Duality and Operational Quantum / Private Coding (Sections 2.3 & 5.3)**
   - `ChannelDuality`, `ChannelEquiv`, `ChannelDualityEquiv`, `QuantumChannels`, `QuantumPolarCodingBase`, and `QuantumPolarCoding` prove Proposition 2.2 (D1–D3) and `corollary_5_5_quantum_private_polar_coding`.
   - `PrivatePolarCoding`, `CoherentQuantumPolarCoding`, and `OperationalCorollary55` prove `exists_wiretap_frozen_good`, `exists_coherent_css_decoder`, and `corollary_5_5_operational_quantum_private_polar_coding`.

4. **Verification**
   - `SanityChecks` instantiates the main theorems on `bscChannel (1 / 4)` and arbitrary qubit CPTP maps.
   - `AuditAxioms` prints axiom dependencies for 48 declarations.
   - `comparator/` provides standalone statement definitions (`ChallengeDefs.lean`), locked statements (`Challenge.lean`), and proofs (`Solution.lean`) checked by `lake comparator`.
