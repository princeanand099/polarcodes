# Polynomial-Blocklength Quantum Polar Codes (Lean 4)

Complete, unconditional, **zero-`sorry`**, **zero-custom-axiom** (`propext`, `Classical.choice`, `Quot.sound` only) Lean 4 (`v4.35.0`) formalization of:

> **Prince Anand**, *Polynomial-Blocklength Quantum Polar Codes via Nonlinear Dephasing Contraction* (2026).

Every theorem, lemma, proposition, and coding-theoretic corollary in Sections 1–5 (including the full Renes–Wilde [10] operational private classical wiretap and entanglement-assisted coherent CSS quantum polar coding layers) is proved strictly on top of Mathlib.

---

## Headline Results Formalized

1. **Theorem 1.1 (Polynomial-Blocklength Quantum Polar Codes)**
   - `theorem_1_1_quantum_polar_poly_blocklength` (`PolarCodes/MainTheorem.lean`): existence of universal constants `μ > 0, C₀ > 0` such that for every finite-dimensional binary-input c-q channel `W`, `ε ∈ (0, 1)`, and `N = 2^n ≥ C₀ (1/ε)^μ`, the fraction of polarized good channels with `Z(W_n^{(b)}) ≤ 2^{-200 N^{0.49047}}` is at least `I(W) - ε`.
   - `theorem_1_1_coding_poly_blocklength` (`PolarCodes/PolarCoding.lean`): explicit deterministic `G_N`-coset c-q polar code `qscPolarCode W n infoSet frozen` using Wilde–Guha's Quantum Successive-Cancellation (QSC) sequential Helstrom decoder, achieving rate `R ≥ I(W) - ε` and average block-error probability `P_e(N, R) ≤ 2^{-N^{0.49}}`.

2. **Theorem 1.2 (One-Step Channel-Combining Contraction)**
   - `theorem_1_2_a_bhattacharyya_contraction` (`PolarCodes/QuantumProps.lean`): `Z(W^-) ≤ Z(W) √(2 - Z(W)²)` and `Z(W^+) = Z(W)²`.
   - `theorem_1_2_b_entropy_contraction` (`PolarCodes/MainTheorem.lean`): `H(W^-) ≤ 1 - Φ(H(W))` and `H(W^+) = 2 H(W) - H(W^-) ≥ Φ(H(W))` with `Φ(x) = h₂(h₂⁻¹(x) ⋆ h₂⁻¹(x))` (quantum Mrs. Gerber's Lemma).

3. **Theorem 1.3 (Optimal Dephasing SDPI & Equatorial Equality)**
   - `theorem_1_3_dephasing_sdpi` & `theorem_1_3_dephasing_sdpi_relEntropy` (`PolarCodes/DephasingSDPI.lean`, `PolarCodes/Refinements.lean`): `D((Z_p ⊗ id)(Ψ) ‖ (Z_{1/2} ⊗ id)(Ψ)) ≤ 1 - h₂(h₂⁻¹(1 - D((Z_0 ⊗ id)(Ψ) ‖ (Z_{1/2} ⊗ id)(Ψ))) ⋆ p)` for all `p ∈ [0, 1/2]` with explicit finiteness guarantees (`≠ ⊤`).
   - `theorem_1_3_equatorial_equality` & `theorem_1_3_equatorial_equality_relEntropy`: exact equality attained on equatorial qubit states `½(I + x X)`.

4. **Corollary 5.5 (Full Operational Quantum & Private Polar Coding — Renes–Wilde [10])**
   - `corollary_5_5_quantum_private_polar_coding` (`PolarCodes/QuantumPolarCoding.lean`): coupled amplitude/phase c-q polarization reduction with structurally pinned assistance set `assistanceSet_spec`, rate `≥ I_sym(𝒩) - ε/2`, unpolarized fractions `≤ ε/4`, and vanishing assistance rate `≤ ε/2` for degradable channels.
   - `corollary_5_5_operational_quantum_private_polar_coding` (`PolarCodes/OperationalCorollary55.lean`, built on `PolarCodes/PrivatePolarCoding.lean` and `PolarCodes/CoherentQuantumPolarCoding.lean`):
     - **Operational Private Wiretap Polar Code** (`OperationalPrivatePolarCode`): randomized privacy-amplification encoder, pre-shared secret-key register `assistSet = assistPinned`, Bob's QSC decoding error `bobDecodingError ≤ 2^{-N^{0.49}}`, and Eve's complementary-channel `(𝒩.complementary)^⊗N` trace-distance secrecy error `eveSecrecyError ≤ 2^{-N^{0.49}}`.
     - **Operational Entanglement-Assisted Coherent CSS Quantum Polar Code** (`OperationalQuantumPolarCode`): Walsh–Hadamard phase-randomized isometric CSS encoder `cssPolarEncoder`, coherent Stinespring + Uhlmann CPTP decoder `𝒟`, rate `≥ I_sym(𝒩) - ε/2`, and entanglement-transmission trace-distance error `entanglementError ≤ 2^{-N^{0.49}}`.
     - **Degradable Vanishing Assistance**: for `𝒩.IsDegradable`, both `secretKeyRate ≤ ε/2` and `assistanceRate ≤ ε/2`.

5. **Supporting Analytic & Structural Results (Sections 2–4)**
   - **Section 2.1**: Klein's inequality equality (`relEntropy_eq_zero_iff`), QJS bounds & equality characterizations (`qjs_mem_Icc`, `qjs_eq_zero_iff`, `qjs_eq_one_iff`, `qjs_eq_avg_relEntropy`), general finite-distribution block-diagonal fidelity (`rootFidelity_block_diagonal`), Fuchs–van de Graaf (`fuchs_van_de_graaf`), hockey-stick variational equality (`hockeyStick_variational_eq`) in `PhiAndFuchs.lean` and `DivergenceCharacterizations.lean`.
   - **Section 2.2–2.3**: Proposition 2.2 (D1)–(D3) including `prop_2_2_D2_var_isoEquiv` (`ChannelDuality.lean`, `ChannelEquiv.lean`, `ChannelDualityEquiv.lean`).
   - **Section 3**: Lemma 3.1 standalone `phi` properties (`PhiAndFuchs.lean`), Frenkel & hockey-stick integrals for rank-deficient `suppSubset ρ σ` (`RankDeficientFrenkel.lean`), and Lemma 3.2 simultaneous hockey-stick measure for both full-rank and equal-support states (`HockeyStickMeasure.lean`, `Refinements.lean`).
   - **Section 4**: Lemma 4.1 Gram-dephasing spectral/entropy/relative-entropy bridge (`GramDephasing.lean`, `DivergenceCharacterizations.lean`).

---

## Verification & Hygiene

- `lake build` compiles all **40 modules** with **0 `sorry`s**.
- `PolarCodes/AuditAxioms.lean` kernel-checks every headline theorem (`propext`, `Classical.choice`, `Quot.sound` only).
- `PolarCodes/SanityChecks.lean` verifies non-vacuity on `bscChannel (1 / 4)` (`symCapacity > 0`) as well as Theorem 1.1 and Corollary 5.5.
- `lake exe comparator` verifies `comparator/Challenge.lean` against `comparator/Solution.lean`.
