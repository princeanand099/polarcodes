# Formalization Progress

**Status**: Complete (33 / 33 library modules compiled with `LAKE_BUILD_EXIT=0`, zero `sorry`, zero custom axioms).

| # | Module | Manuscript Results | Status |
|---|---|---|---|
| 1 | `PolarCodes/BinaryEntropy.lean` | `h2`, `h2Inv`, `deltaGap`, Lemma 3.1 | Complete |
| 2 | `PolarCodes/QuantumStates.lean` | `DensityOp`, `vonNeumannEntropy`, `suppSubset`, `relEntropy`, `qjs`, `hockeyStick`, `rootFidelity` | Complete |
| 3 | `PolarCodes/Channels.lean` | `CQChannel`, Definition 2.1 (`checkCombine`, `varCombine`) | Complete |
| 4 | `PolarCodes/QuantumProps.lean` | Eq. (2.7)–(2.8) (`entropy_conservation`), Lemma 5.1(b) plus | Complete |
| 5 | `PolarCodes/GramDephasing.lean` | `dephaseState`, `dephaseCoherence`, Lemma 4.1 | Complete |
| 6 | `PolarCodes/Bhattacharyya.lean` | Uhlmann purification, Lemma 5.1(b) minus | Complete |
| 7 | `PolarCodes/SplittingBounds.lean` | `theta0`, `Lambda0`, Propositions 4.3 & 4.4 | Complete |
| 8 | `PolarCodes/SpectralTrace.lean` | `posPartTrace`, `negPartTrace`, Sylvester's Law of Inertia | Complete |
| 9 | `PolarCodes/ChannelDuality.lean` | Proposition 2.2 (D1–D3 entropic) | Complete |
| 10 | `PolarCodes/FrenkelHelpers.lean` | Measurability & Lebesgue integral helpers | Complete |
| 11 | `PolarCodes/Polarization.lean` | Doob maximal, Hoeffding, Lemmas 5.2 & 5.3 | Complete |
| 12 | `PolarCodes/FrenkelIntegral.lean` | Frenkel's integral formula (Eq. 3.7) | Complete |
| 13 | `PolarCodes/DataProcessing.lean` | Partial-trace DPI, Lemma 5.1(a) | Complete |
| 14 | `PolarCodes/QuantumChannels.lean` | Stinespring `CPTPMap`, general CPTP DPI (`relEntropy_cptp_le`, `condEntropy_cptp_ge`) | Complete |
| 15 | `PolarCodes/PolarizationFine.lean` | Lemma 5.4, `polar_error_exponent_bound`, abstract Theorem 1.1 & Corollary 5.5 | Complete |
| 16 | `PolarCodes/HockeyStick.lean` | Hockey-stick integral (Eq. 3.8) | Complete |
| 17 | `PolarCodes/ScalarSupplements.lean` | Wyner–Ziv convexity (`convexOn_gc`), Eq. (1.8) | Complete |
| 18 | `PolarCodes/HockeyStickMeasure.lean` | Lemma 3.2 (positive-definite base) | Complete |
| 19 | `PolarCodes/QJJS.lean` | Proposition 3.3 | Complete |
| 20 | `PolarCodes/DephasingSDPI.lean` | Theorem 1.3 (SDPI + equatorial equality) | Complete |
| 21 | `PolarCodes/Refinements.lean` | Equal-support Lemma 3.2, Prop 3.3 classical equality, relEntropy Theorem 1.3 | Complete |
| 22 | `PolarCodes/ChannelEquiv.lean` | `IsoEquiv`, `ChannelEquiv`, Proposition 2.2 (D3) channel equivalence | Complete |
| 23 | `PolarCodes/ChannelDualityEquiv.lean` | Proposition 2.2 (D2) channel equivalence | Complete |
| 24 | `PolarCodes/MrsGerberHybrid.lean` | Theorem 1.2(a) pure-state & BSC branches | Complete |
| 25 | `PolarCodes/MrsGerberClassical.lean` | Theorem 1.2(a) classical branch | Complete |
| 26 | `PolarCodes/MrsGerber.lean` | Proposition 4.2, Theorem 1.2(b) | Complete |
| 27 | `PolarCodes/MainTheorem.lean` | Fidelity-fraction Theorem 1.1, simultaneous CSS Corollary 5.5 | Complete |
| 28 | `PolarCodes/NoncommutativeUnion.lean` | Helstrom projectors, Powers–Størmer, Sen's noncommutative union bound | Complete |
| 29 | `PolarCodes/ArikanTransform.lean` | Product channel `W^{\otimes N}`, Arıkan `G_N`, synthesized channels `W_n^{(i)}` | Complete |
| 30 | `PolarCodes/PolarCoding.lean` | `CosetPolarCode`, QSC decoder, Wilde–Guha bound, full coding Theorem 1.1 | Complete |
| 31 | `PolarCodes/QuantumPolarCodingBase.lean` | Renes–Wilde `ampChannel`/`phaseChannel`, `symCoherentInfo`, dual unpolarized bound | Complete |
| 32 | `PolarCodes/QuantumPolarCoding.lean` | Degradable vanishing assistance, `CSSPrivatePolarCode`, full Corollary 5.5 | Complete |
| 33 | `PolarCodes/SanityChecks.lean` | Non-vacuity witness checks | Complete |
| — | `PolarCodes/AuditAxioms.lean` | `#print axioms` audit across 50 exported theorems | Complete |
| — | `comparator/` + `comparator.json` | Standalone challenge/solution lock for 13 headline theorems (`lake comparator`) | Complete |
