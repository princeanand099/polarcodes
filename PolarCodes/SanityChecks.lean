/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.OperationalCorollary55
import PolarCodes.DivergenceCharacterizations
import PolarCodes.RankDeficientFrenkel
import PolarCodes.ChannelDualityEquiv

/-!
# Nontrivial Non-Vacuity Sanity Checks

Exercises the headline theorems on concrete nontrivial channels (`bscChannel (1 / 4)` with
strictly positive symmetric capacity `I(BSC(1/4)) > 0`) as well as Theorem 1.1 coding and
Corollary 5.5 (both c-q polarization reduction and operational wiretap / coherent CSS).
-/

namespace PolarCodes.SanityChecks

private lemma exists_two_pow_ge (B : ℝ) : ∃ n : ℕ, B ≤ (2 : ℝ) ^ n := by
  obtain ⟨n, hn⟩ := exists_nat_gt B
  refine ⟨n, le_trans (le_of_lt hn) ?_⟩
  clear hn
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    push_cast
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    linarith

/-- `BSC(1/4)` has strictly positive symmetric capacity `1 - h₂(1/4) > 0`. -/
lemma bsc_quarter_symCapacity_pos :
    0 < (bscChannel (1 / 4) (by norm_num) (by norm_num)).symCapacity := by
  have hc := condEntropy_bscChannel (1 / 4) (by norm_num) (by norm_num)
  have hlt : h2 (1 / 4 : ℝ) < h2 (1 / 2 : ℝ) :=
    strictMonoOn_h2 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)
  rw [h2_half] at hlt
  unfold CQChannel.symCapacity
  unfold CQChannel.condEntropy at hc
  linarith

/-- Non-vacuity check for `theorem_1_1_coding_poly_blocklength` on `BSC(1/4)` at `ε = 1 / 10`. -/
example :
    ∃ (n : ℕ) (infoSet : Finset (Fin (2 ^ n))) (frozen : Fin (2 ^ n) → Bool),
      let W := bscChannel (1 / 4) (by norm_num) (by norm_num)
      let C := qscPolarCode W n infoSet frozen
      W.symCapacity - 1 / 10 ≤ C.rate ∧
      C.avgBlockError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := by
  rcases theorem_1_1_coding_poly_blocklength.{0} with ⟨μ, C₀, hμ, hC₀, h⟩
  obtain ⟨n, hn⟩ := exists_two_pow_ge (C₀ * (1 / (1 / 10 : ℝ)) ^ μ)
  obtain ⟨infoSet, frozen, hr, he⟩ :=
    h (bscChannel (1 / 4) (by norm_num) (by norm_num)) (by norm_num : (0 : ℝ) < 1 / 10)
      (by norm_num) n hn
  exact ⟨n, infoSet, frozen, hr, he⟩

/-- Non-vacuity check for `corollary_5_5_quantum_private_polar_coding` on any qubit CPTP map. -/
example {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d) :
    ∃ (n : ℕ) (C : CSSPrivatePolarCode 𝒩 n
        ((2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ)))),
      symCoherentInfo 𝒩 - 1 / 4 ≤ C.rate ∧
      C.ampPhaseErrorSum ≤ 2 * (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := by
  rcases corollary_5_5_quantum_private_polar_coding with ⟨μ, C₀, hμ, hC₀, h⟩
  obtain ⟨n, hn⟩ := exists_two_pow_ge (C₀ * (1 / (1 / 2 : ℝ)) ^ μ)
  obtain ⟨C, hr, _, _, hsum, _, _, _⟩ := h 𝒩 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) n hn
  exact ⟨n, C, by linarith, hsum⟩

/-- Non-vacuity check for `corollary_5_5_operational_quantum_private_polar_coding`. -/
example {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d) :
    ∃ (n : ℕ) (C_priv : OperationalPrivatePolarCode 𝒩 n)
      (C_quant : OperationalQuantumPolarCode 𝒩 n),
      symCoherentInfo 𝒩 - 1 / 4 ≤ C_priv.rate ∧
      C_priv.bobDecodingError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
      C_priv.eveSecrecyError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
      C_quant.entanglementError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := by
  rcases corollary_5_5_operational_quantum_private_polar_coding with ⟨μ, C₀, hμ, hC₀, h⟩
  obtain ⟨n, hn⟩ := exists_two_pow_ge (C₀ * (1 / (1 / 2 : ℝ)) ^ μ)
  obtain ⟨C_priv, C_quant, _, _, hr, _, hbob, hsec, hent, _⟩ :=
    h 𝒩 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) n hn
  exact ⟨n, C_priv, C_quant, by linarith, hbob, hsec, hent⟩

end PolarCodes.SanityChecks
