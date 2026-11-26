# Polynomial-Blocklength Quantum Polar Codes (Lean 4)

Unconditional, **zero-`sorry`**, **zero-custom-axiom** (`propext`, `Classical.choice`, `Quot.sound` only) Lean 4 (`v4.35.0`) formalization of:

> **Prince Anand**, *Polynomial-Blocklength Quantum Polar Codes via Nonlinear Dephasing Contraction* (2026).

Every theorem, lemma, proposition, and coding-theoretic corollary in Sections 1–5 (including the Renes–Wilde [10] operational private classical wiretap and entanglement-assisted coherent CSS quantum polar coding layers) is proved strictly on top of Mathlib.

## Headline Results Formalized

1. **Theorem 1.1 (Polynomial-Blocklength Quantum Polar Codes)**
   - `theorem_1_1_quantum_polar_poly_blocklength` (`PolarCodes/MainTheorem.lean`): existence of universal constants `μ > 0, C₀ > 0` such that for every finite-dimensional binary-input c-q channel `W`, `ε ∈ (0, 1)`, and `N = 2^n ≥ C₀ (1/ε)^μ`, the fraction of polarized good channels with `Z(W_n^{(b)}) ≤ 2^{-200 N^{0.49047}}` is at least `I(W) - ε`.
   - `theorem_1_1_coding_poly_blocklength` (`PolarCodes/PolarCoding.lean`): explicit deterministic `G_N`-coset c-q polar code `qscPolarCode W n infoSet frozen` using Wilde–Guha's Quantum Successive-Cancellation (QSC) sequential Helstrom decoder, achieving rate `R ≥ I(W) - ε` and average block-error probability `P_e(N, R) ≤ 2^{-N^{0.49}}`.

2. **Theorem 1.2 (Quantum Mrs. Gerber's Lemma & Polarization Contraction)**
   - **Theorem 1.2(a)**: `theorem_1_2a_pure`, `theorem_1_2a_bsc` (`PolarCodes/MrsGerberHybrid.lean`), and `theorem_1_2a_classical` (`PolarCodes/MrsGerberClassical.lean`).
   - **Theorem 1.2(b)**: `theorem_1_2b_linear_splitting` and `theorem_1_2b_potential_contraction` (`PolarCodes/MrsGerber.lean`), together with `fidelityParam_plusChannel` and `fidelityParam_minusChannel_le` (`PolarCodes/QuantumProps.lean`, `PolarCodes/Bhattacharyya.lean`).

3. **Theorem 1.3 (Optimal Dephasing SDPI & Equatorial Equality)**
   - `theorem_1_3_dephasing_sdpi` & `theorem_1_3_dephasing_sdpi_relEntropy` (`PolarCodes/DephasingSDPI.lean`, `PolarCodes/Refinements.lean`): `D((Z_p ⊗ id)(Ψ) ‖ (Z_{1/2} ⊗ id)(Ψ)) ≤ 1 - h₂(h₂⁻¹(1 - D((Z_0 ⊗ id)(Ψ) ‖ (Z_{1/2} ⊗ id)(Ψ))) ⋆ p)` for all `p ∈ [0, 1/2]` with explicit finiteness guarantees (`≠ ⊤`).
   - `theorem_1_3_equatorial_equality` & `theorem_1_3_equatorial_equality_relEntropy`: equality attained on equatorial qubit states `½(I + x X)`.

4. **Corollary 5.5 (Operational Quantum & Private Polar Coding — Renes–Wilde [10])**
   - `corollary_5_5_quantum_private_polar_coding` (`PolarCodes/QuantumPolarCoding.lean`): coupled amplitude/phase c-q polarization reduction with structurally pinned assistance set `assistanceSet_spec`, rate `≥ I_sym(𝒩) - ε/2`, unpolarized fractions `≤ ε/4`, and vanishing assistance rate `≤ ε/2` for degradable channels.
   - `corollary_5_5_operational_quantum_private_polar_coding` (`PolarCodes/OperationalCorollary55.lean`, built on `PolarCodes/PrivatePolarCoding.lean` and `PolarCodes/CoherentQuantumPolarCoding.lean`):
     - **Operational Private Wiretap Polar Code** (`OperationalPrivatePolarCode`): randomized privacy-amplification encoder, pre-shared secret-key register `assistSet = assistPinned`, Bob's QSC decoding error `bobDecodingError ≤ 2^{-N^{0.49}}`, and Eve's complementary-channel `(𝒩.complementary)^⊗N` trace-distance secrecy error `eveSecrecyError ≤ 2^{-N^{0.49}}`.
     - **Operational Entanglement-Assisted Coherent CSS Quantum Polar Code** (`OperationalQuantumPolarCode`): Walsh–Hadamard phase-randomized isometric CSS encoder `cssPolarEncoder`, coherent Stinespring + Uhlmann CPTP decoder `𝒟`, rate `≥ I_sym(𝒩) - ε/2`, and entanglement-transmission trace-distance error `entanglementError ≤ 2^{-N^{0.49}}`.
     - **Degradable Vanishing Assistance**: for `𝒩.IsDegradable`, both `secretKeyRate ≤ ε/2` and `assistanceRate ≤ ε/2`.

5. **Supporting Analytic & Structural Results (Sections 2–4)**
   - **Section 2.1**: Klein's inequality equality (`relEntropy_eq_zero_iff`), QJS bounds & equality characterizations (`qjs_mem_Icc`, `qjs_eq_zero_iff`, `qjs_eq_one_iff`, `qjs_eq_avg_relEntropy`), general finite-distribution block-diagonal fidelity (`rootFidelity_block_diagonal`), Fuchs–van de Graaf (`one_sub_rootFidelity_le_traceDist`, `traceDist_le_sqrt_one_sub_rootFidelity_sq`), hockey-stick variational equality (`hockeyStick_eq_sSup`), and `posPartMat_mul_negPartMat` in `PhiAndFuchs.lean`, `SpectralTrace.lean`, and `DivergenceCharacterizations.lean`.
   - **Section 2.2–2.3**: Proposition 2.2 (D1)–(D3) including `prop_2_2_D2_var_isoEquiv`, `prop_2_2_D2_channelEquiv`, `prop_2_2_D3_channelEquiv` (`ChannelDuality.lean`, `ChannelEquiv.lean`, `ChannelDualityEquiv.lean`).
   - **Section 3**: Lemma 3.1 standalone `phi` properties (`hasDerivAt_phi_cParam`, `continuousOn_phi`, `strictMonoOn_phi`, `strictConvexOn_phi` in `PhiAndFuchs.lean`), Frenkel & hockey-stick integrals for rank-deficient `suppSubset ρ σ` (`relEntropy_frenkel_integral_of_suppSubset`, `relEntropy_hockeyStick_integral_of_suppSubset` in `RankDeficientFrenkel.lean`), and Lemma 3.2 simultaneous hockey-stick measure for both full-rank and equal-support states (`HockeyStickMeasure.lean`, `Refinements.lean`).
   - **Section 4**: Lemma 4.1 Gram-dephasing spectral/entropy/relative-entropy bridge (`lemma_4_1_gram_dephasing`, `lemma_4_1_gram_dephasing_relEntropy` in `GramDephasing.lean`, `DivergenceCharacterizations.lean`).

## Verification & Hygiene

- `lake build` compiles all **40 modules** with **0 `sorry`s**.
- `PolarCodes/AuditAxioms.lean` kernel-checks 41 headline theorems (`propext`, `Classical.choice`, `Quot.sound` only).
- `PolarCodes/SanityChecks.lean` verifies non-vacuity on `bscChannel (1 / 4)` (`symCapacity > 0`) as well as Theorem 1.1 and Corollary 5.5.
- `lake comparator` verifies `comparator/Challenge.lean` against `comparator/Solution.lean`.
