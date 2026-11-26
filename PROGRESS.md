# Formalization Progress

**Status**: 36 / 36 library modules written with zero `sorry` and zero custom axioms (33-module baseline CI-verified on `d4fac514`; 36-module audit-remediation update ready for `full_verify: true` CI verification).

| # | Module | Manuscript Results | Status |
|---|---|---|---|
| 1 | `PolarCodes/BinaryEntropy.lean` | `h2`, `h2Inv`, `deltaGap`, Lemma 3.1 | Complete |
| 2 | `PolarCodes/QuantumStates.lean` | `DensityOp`, `vonNeumannEntropy`, `suppSubset`, `relEntropy`, `qjs`, `hockeyStick`, `traceDist`, `rootFidelity` | Complete |
| 3 | `PolarCodes/Channels.lean` | `CQChannel`, Definition 2.1 (`checkCombine`, `varCombine`) | Complete |
| 4 | `PolarCodes/QuantumProps.lean` | Eq. (2.7)–(2.8) (`entropy_conservation`), Lemma 5.1(b) plus | Complete |
| 5 | `PolarCodes/GramDephasing.lean` | `dephaseState`, `dephaseCoherence`, Lemma 4.1 (tight `p ≤ 1/2` + charpoly coincidence) | Complete |
| 6 | `PolarCodes/Bhattacharyya.lean` | Uhlmann purification, Lemma 5.1(b) minus | Complete |
| 7 | `PolarCodes/SplittingBounds.lean` | `theta0`, `Lambda0`, Propositions 4.3 & 4.4 | Complete |
| 8 | `PolarCodes/SpectralTrace.lean` | `posPartTrace`, `negPartTrace`, Sylvester's Law of Inertia, `density_spectral_eq` | Complete |
| 9 | `PolarCodes/ChannelDuality.lean` | Proposition 2.2 (D1–D3 entropic) | Complete |
| 10 | `PolarCodes/FrenkelHelpers.lean` | Measurability & Lebesgue integral helpers | Complete |
| 11 | `PolarCodes/Polarization.lean` | Doob maximal, Hoeffding, Lemmas 5.2 & 5.3 | Complete |
| 12 | `PolarCodes/FrenkelIntegral.lean` | Frenkel's integral formula (Eq. 3.7, `PosDef`) | Complete |
| 13 | `PolarCodes/DataProcessing.lean` | Partial-trace DPI, Lemma 5.1(a) | Complete |
| 14 | `PolarCodes/QuantumChannels.lean` | Stinespring `CPTPMap`, general CPTP DPI (`relEntropy_cptp_le`, `condEntropy_cptp_ge`) | Complete |
| 15 | `PolarCodes/PolarizationFine.lean` | Lemma 5.4, `polar_error_exponent_bound`, abstract Theorem 1.1 & Corollary 5.5 | Complete |
| 16 | `PolarCodes/HockeyStick.lean` | Hockey-stick integral (Eq. 3.8, `PosDef`) & `frenkel_lintegral_eq_hockeyStick_lintegral` | Complete |
| 17 | `PolarCodes/RankDeficientFrenkel.lean` | Rank-deficient `suppSubset` Frenkel & hockey-stick integrals (Eq. 3.7–3.8) | Complete |
| 18 | `PolarCodes/ScalarSupplements.lean` | Wyner–Ziv convexity (`convexOn_gc`), Eq. (1.8) | Complete |
| 19 | `PolarCodes/PhiAndFuchs.lean` | Standalone `phi` regularity/convexity (Lemma 3.1) & Fuchs–van de Graaf (Eq. 2.3) | Complete |
| 20 | `PolarCodes/HockeyStickMeasure.lean` | Lemma 3.2 (positive-definite base, explicit `relEntropy ≠ ⊤`) & `qjs_lt_one_posDef` | Complete |
| 21 | `PolarCodes/QJJS.lean` | Proposition 3.3 | Complete |
| 22 | `PolarCodes/DephasingSDPI.lean` | Theorem 1.3 (SDPI + equatorial equality) | Complete |
| 23 | `PolarCodes/Refinements.lean` | Equal-support Lemma 3.2, Prop 3.3 classical equality, `relEntropy` Theorem 1.3 (explicit finiteness) | Complete |
| 24 | `PolarCodes/DivergenceCharacterizations.lean` | `posPartMat * negPartMat = 0`, Eq. 2.2 variational, Klein/QJS characterizations, block-diag fidelity, Lemma 4.1 `relEntropy` | Complete |
| 25 | `PolarCodes/ChannelEquiv.lean` | `IsoEquiv`, `ChannelEquiv`, Proposition 2.2 (D3) channel equivalence | Complete |
| 26 | `PolarCodes/ChannelDualityEquiv.lean` | Proposition 2.2 (D2) `IsoEquiv` (variable-node) & `ChannelEquiv` | Complete |
| 27 | `PolarCodes/MrsGerberHybrid.lean` | Theorem 1.2(a) pure-state & BSC branches | Complete |
| 28 | `PolarCodes/MrsGerberClassical.lean` | Theorem 1.2(a) classical branch | Complete |
| 29 | `PolarCodes/MrsGerber.lean` | Proposition 4.2, Theorem 1.2(b) | Complete |
| 30 | `PolarCodes/MainTheorem.lean` | Fidelity-fraction Theorem 1.1, simultaneous CSS Corollary 5.5 | Complete |
| 31 | `PolarCodes/NoncommutativeUnion.lean` | Helstrom projectors, Powers–Størmer, Sen's noncommutative union bound | Complete |
| 32 | `PolarCodes/ArikanTransform.lean` | Product channel `W^{\otimes N}`, Arıkan `G_N`, synthesized channels `W_n^{(i)}` | Complete |
| 33 | `PolarCodes/PolarCoding.lean` | `CosetPolarCode`, QSC decoder, Wilde–Guha bound, syntactically pinned QSC Theorem 1.1 | Complete |
| 34 | `PolarCodes/QuantumPolarCodingBase.lean` | Renes–Wilde `ampChannel`/`phaseChannel`, `symCoherentInfo`, dual unpolarized bound | Complete |
| 35 | `PolarCodes/QuantumPolarCoding.lean` | Degradable vanishing assistance, pinned `CSSPrivatePolarCode`, Corollary 5.5 c-q polarization reduction | Complete |
| 36 | `PolarCodes/SanityChecks.lean` | Nontrivial non-vacuity checks (`noiselessChannel`, `idQubitChannel`) for Theorems 1.1, 1.2(b), 1.3 & Corollary 5.5 | Complete |
| — | `PolarCodes/AuditAxioms.lean` | `#print axioms` audit across 68 exported theorems | Complete |
| — | `comparator/` + `comparator.json` | Standalone docstring-free statement lock for 13 headline theorems (`lake comparator`) | Complete |
