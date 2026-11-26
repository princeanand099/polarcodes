/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.CoherentQuantumPolarCoding

/-!
# Operational Corollary 5.5: Unified Private Wiretap & Coherent CSS Quantum Polar Coding

This module combines `PrivatePolarCoding.lean` and `CoherentQuantumPolarCoding.lean` with the
polynomial-blocklength polarization theorem (`theorem_1_1_quantum_polar_poly_blocklength`) and the
degradable assistance-set containment (`degradable_assistance_subset_unpolarized`) to prove
`corollary_5_5_operational_quantum_private_polar_coding` unconditionally on top of Mathlib.
-/

open Matrix BigOperators Real Finset
open scoped ComplexOrder

namespace PolarCodes

private lemma operational_exponent_bounds {n : ℕ} (hn : 1 ≤ n) :
    let N : ℝ := (2 : ℝ) ^ n
    let thresh : ℝ := (2 : ℝ) ^ (-(200 : ℝ) * N ^ (49047 / 100000 : ℝ))
    2 * Real.sqrt (N * thresh) + N * thresh ≤ (2 : ℝ) ^ (-N ^ (49 / 100 : ℝ)) ∧
    2 * Real.sqrt (2 * (2 * Real.sqrt (N * thresh) + N * thresh)) ≤
      (2 : ℝ) ^ (-N ^ (49 / 100 : ℝ)) := by
  intro N thresh
  have hN_ge2 : (2 : ℝ) ≤ N := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hN_pos : 0 < N := by linarith
  have hN_ge1 : (1 : ℝ) ≤ N := by linarith
  have hpow_mono : N ^ (49 / 100 : ℝ) ≤ N ^ (49047 / 100000 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
  have hpow_ge1 : (1 : ℝ) ≤ N ^ (49 / 100 : ℝ) := Real.one_le_rpow hN_ge1 (by norm_num)
  have hlogN_le : Real.log N ≤ (100 / 49 : ℝ) * N ^ (49 / 100 : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hN_pos (49 / 100 : ℝ))
    rw [Real.log_rpow hN_pos] at h1
    linarith
  have hn_le : (n : ℝ) ≤ 5 * N ^ (49 / 100 : ℝ) := by
    have hlogN_eq : Real.log N = (n : ℝ) * Real.log 2 := by
      simp only [N, Real.log_pow]
    have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hNthresh_eq : N * thresh = (2 : ℝ) ^ ((n : ℝ) - 200 * N ^ (49047 / 100000 : ℝ)) := by
    simp only [thresh, N]
    rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  have hNthresh_le : N * thresh ≤ (2 : ℝ) ^ (-96 * N ^ (49 / 100 : ℝ)) := by
    rw [hNthresh_eq]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hNthresh_le20 : N * thresh ≤ (2 : ℝ) ^ (-20 * N ^ (49 / 100 : ℝ)) := by
    refine le_trans hNthresh_le ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hsqrt_le20 : 2 * Real.sqrt (N * thresh) ≤ (2 : ℝ) ^ (-20 * N ^ (49 / 100 : ℝ)) := by
    have h1 : Real.sqrt (N * thresh) ≤ Real.sqrt ((2 : ℝ) ^ (-96 * N ^ (49 / 100 : ℝ))) :=
      Real.sqrt_le_sqrt hNthresh_le
    have h2 : Real.sqrt ((2 : ℝ) ^ (-96 * N ^ (49 / 100 : ℝ))) =
        (2 : ℝ) ^ (-48 * N ^ (49 / 100 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; ring
    have h3 : 2 * Real.sqrt (N * thresh) ≤ (2 : ℝ) ^ (1 - 48 * N ^ (49 / 100 : ℝ)) := by
      calc 2 * Real.sqrt (N * thresh)
          ≤ 2 * (2 : ℝ) ^ (-48 * N ^ (49 / 100 : ℝ)) := by linarith
        _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-48 * N ^ (49 / 100 : ℝ)) := by norm_num
        _ = (2 : ℝ) ^ (1 - 48 * N ^ (49 / 100 : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    refine le_trans h3 ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hsum_le : 2 * Real.sqrt (N * thresh) + N * thresh ≤
      (2 : ℝ) ^ (1 - 20 * N ^ (49 / 100 : ℝ)) := by
    calc 2 * Real.sqrt (N * thresh) + N * thresh
        ≤ (2 : ℝ) ^ (-20 * N ^ (49 / 100 : ℝ)) + (2 : ℝ) ^ (-20 * N ^ (49 / 100 : ℝ)) := by
            linarith
      _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-20 * N ^ (49 / 100 : ℝ)) := by norm_num; ring
      _ = (2 : ℝ) ^ (1 - 20 * N ^ (49 / 100 : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
  constructor
  · refine le_trans hsum_le ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  · have h2sum : 2 * (2 * Real.sqrt (N * thresh) + N * thresh) ≤
        (2 : ℝ) ^ (2 - 20 * N ^ (49 / 100 : ℝ)) := by
      calc 2 * (2 * Real.sqrt (N * thresh) + N * thresh)
          ≤ (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (1 - 20 * N ^ (49 / 100 : ℝ)) := by norm_num; linarith
        _ = (2 : ℝ) ^ (2 - 20 * N ^ (49 / 100 : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    have hsqrt2sum : Real.sqrt (2 * (2 * Real.sqrt (N * thresh) + N * thresh)) ≤
        (2 : ℝ) ^ (1 - 10 * N ^ (49 / 100 : ℝ)) := by
      have h1 := Real.sqrt_le_sqrt h2sum
      have h2 : Real.sqrt ((2 : ℝ) ^ (2 - 20 * N ^ (49 / 100 : ℝ))) =
          (2 : ℝ) ^ (1 - 10 * N ^ (49 / 100 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1; ring
      exact h2 ▸ h1
    have hfin : 2 * Real.sqrt (2 * (2 * Real.sqrt (N * thresh) + N * thresh)) ≤
        (2 : ℝ) ^ (2 - 10 * N ^ (49 / 100 : ℝ)) := by
      calc 2 * Real.sqrt (2 * (2 * Real.sqrt (N * thresh) + N * thresh))
          ≤ (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (1 - 10 * N ^ (49 / 100 : ℝ)) := by norm_num; linarith
        _ = (2 : ℝ) ^ (2 - 10 * N ^ (49 / 100 : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    refine le_trans hfin ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith

/-- **Corollary 5.5 (Operational Renes–Wilde [10] Private Wiretap & Coherent CSS Quantum Polar Coding)**:
There exist universal constants `μ > 0` and `C₀ > 0` such that for every finite-dimensional
qubit-input quantum channel `𝒩 : CPTPMap Bool d`, every gap `ε ∈ (0, 1)`, and every depth `n`
with blocklength `N = 2^n ≥ C₀ (1 / ε)^μ`, letting
`assistPinned = {i | i ∉ 𝒢_N(W_A, thresh) ∧ dualIndex n i ∉ 𝒢_N(W_P, thresh)}`:
1. There exists an operational private wiretap polar code `C_priv : OperationalPrivatePolarCode 𝒩 n`
   with `C_priv.assistSet = assistPinned`, rate `C_priv.rate ≥ I_sym(𝒩) - ε / 2`, Bob QSC decoding
   error `C_priv.bobDecodingError ≤ 2^{-N^{0.49}}`, and Eve complementary-channel trace-distance
   secrecy error `C_priv.eveSecrecyError ≤ 2^{-N^{0.49}}`.
2. There exists an operational entanglement-assisted coherent CSS quantum polar code
   `C_quant : OperationalQuantumPolarCode 𝒩 n` with `C_quant.assistSet = assistPinned`,
   rate `C_quant.rate ≥ I_sym(𝒩) - ε / 2`, and coherent entanglement-transmission trace-distance
   error `C_quant.entanglementError ≤ 2^{-N^{0.49}}`.
3. If `𝒩` is degradable (`𝒩.IsDegradable`), both the secret-key rate and the entanglement-assistance
   rate vanish: `C_priv.secretKeyRate ≤ ε / 2` and `C_quant.assistanceRate ≤ ε / 2`. -/
theorem corollary_5_5_operational_quantum_private_polar_coding :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d)
        {ε : ℝ}, 0 < ε → ε < 1 →
        ∀ (n : ℕ), C₀ * (1 / ε) ^ μ ≤ (2 : ℝ) ^ n →
          let thresh : ℝ := (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))
          let assistPinned : Finset (Fin (2 ^ n)) :=
            Finset.univ.filter (fun i : Fin (2 ^ n) ↦
              i ∉ goodSet (ampChannel 𝒩) n thresh ∧
              dualIndex n i ∉ goodSet (phaseChannel 𝒩) n thresh)
          ∃ (C_priv : OperationalPrivatePolarCode 𝒩 n)
            (C_quant : OperationalQuantumPolarCode 𝒩 n),
            C_priv.assistSet = assistPinned ∧
            C_quant.assistSet = assistPinned ∧
            symCoherentInfo 𝒩 - ε / 2 ≤ C_priv.rate ∧
            symCoherentInfo 𝒩 - ε / 2 ≤ C_quant.rate ∧
            C_priv.bobDecodingError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
            C_priv.eveSecrecyError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
            C_quant.entanglementError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
            (𝒩.IsDegradable → C_priv.secretKeyRate ≤ ε / 2 ∧ C_quant.assistanceRate ≤ ε / 2) := by
  rcases theorem_1_1_quantum_polar_poly_blocklength.{0} with ⟨μ, C₀, hμ, hC₀, hpolar⟩
  refine ⟨μ, max (C₀ * (8 : ℝ) ^ μ) 2, hμ,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro d _ _ 𝒩 ε hε0 hε1 n hn
  dsimp only
  set thresh : ℝ := (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))
  have h1eps : (1 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε0, one_mul]; exact le_of_lt hε1
  have hpow_ge1 : (1 : ℝ) ≤ (1 / ε) ^ μ := Real.one_le_rpow h1eps (le_of_lt hμ)
  have hn_ge2 : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (2 : ℝ) = 2 * 1 := by ring
      _ ≤ max (C₀ * (8 : ℝ) ^ μ) 2 * (1 / ε) ^ μ :=
          mul_le_mul (le_max_right _ _) hpow_ge1 (by norm_num) (by positivity)
      _ ≤ (2 : ℝ) ^ n := hn
  have hn1 : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    subst this; norm_num at hn_ge2
  have hε8_pos : (0 : ℝ) < ε / 8 := by linarith
  have hε8_lt1 : ε / 8 < 1 := by linarith
  have hn_eps8 : C₀ * (1 / (ε / 8)) ^ μ ≤ (2 : ℝ) ^ n := by
    have h8 : (1 / (ε / 8)) ^ μ = (8 : ℝ) ^ μ * (1 / ε) ^ μ := by
      have heq : (1 : ℝ) / (ε / 8) = 8 * (1 / ε) := by field_simp
      rw [heq, Real.mul_rpow (by norm_num) (by positivity)]
    rw [h8, ← mul_assoc]
    exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hn
  have hWA := hpolar (ampChannel 𝒩) hε8_pos hε8_lt1 n hn_eps8
  have hWAd := hpolar (ampChannel 𝒩).dual hε8_pos hε8_lt1 n hn_eps8
  have hWP := hpolar (phaseChannel 𝒩) hε8_pos hε8_lt1 n hn_eps8
  have hWPd := hpolar (phaseChannel 𝒩).dual hε8_pos hε8_lt1 n hn_eps8
  rw [← goodSet_card_eq_treeProb] at hWA hWAd hWP hWPd
  have hthresh_le : thresh ≤ 1 / 4 := by
    have hpow2 : (1 : ℝ) ≤ ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    have hexp : -(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ) ≤ (-2 : ℝ) := by linarith
    calc thresh = (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ)) := rfl
      _ ≤ (2 : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 1 / 4 := by norm_num
  have hU_A : ((unpolarizedSet (ampChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n ≤ ε / 4 := by
    have := dual_unpolarized_fraction_le (ampChannel 𝒩) n hthresh_le hWA hWAd
    linarith
  have hU_P : ((unpolarizedSet (phaseChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n ≤ ε / 4 := by
    have := dual_unpolarized_fraction_le (phaseChannel 𝒩) n hthresh_le hWP hWPd
    linarith
  -- 4-way Renes–Wilde partition
  let infoSet : Finset (Fin (2 ^ n)) :=
    (goodSet (ampChannel 𝒩) n thresh).filter (fun i ↦ dualIndex n i ∈ goodSet (phaseChannel 𝒩) n thresh)
  let randSet : Finset (Fin (2 ^ n)) :=
    (goodSet (ampChannel 𝒩) n thresh).filter (fun i ↦ dualIndex n i ∉ goodSet (phaseChannel 𝒩) n thresh)
  let assistSet : Finset (Fin (2 ^ n)) :=
    Finset.univ.filter (fun i : Fin (2 ^ n) ↦
      i ∉ goodSet (ampChannel 𝒩) n thresh ∧ dualIndex n i ∉ goodSet (phaseChannel 𝒩) n thresh)
  have hdisj_ir : Disjoint infoSet randSet := by
    rw [Finset.disjoint_left]
    intro i hi hr
    exact (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hi).2
  have hdisj_ia : Disjoint infoSet assistSet := by
    rw [Finset.disjoint_left]
    intro i hi ha
    exact (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp hi).1
  have hdisj_ra : Disjoint randSet assistSet := by
    rw [Finset.disjoint_left]
    intro i hr ha
    exact (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp hr).1
  obtain ⟨uF, huF⟩ := exists_wiretap_frozen_good 𝒩 n infoSet randSet assistSet hdisj_ir hdisj_ia
  obtain ⟨v, 𝒟, hcoh⟩ :=
    exists_coherent_css_decoder 𝒩 n infoSet randSet assistSet hdisj_ir hdisj_ia hdisj_ra uF
  let C_priv : OperationalPrivatePolarCode 𝒩 n :=
    ⟨infoSet, randSet, assistSet, hdisj_ir, hdisj_ia, hdisj_ra, uF⟩
  let C_quant : OperationalQuantumPolarCode 𝒩 n :=
    ⟨infoSet, randSet, assistSet, hdisj_ir, hdisj_ia, hdisj_ra, uF, v, 𝒟⟩
  -- Bound the two error terms in `huF` by `2 * √(2^n * thresh) + 2^n * thresh`
  have hthresh_nn : 0 ≤ thresh := Real.rpow_nonneg (by norm_num) _
  have hbob_sum_le : ∑ i ∈ infoSet ∪ randSet,
      (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam ≤ (2 : ℝ) ^ n * thresh := by
    have h1 : ∑ i ∈ infoSet ∪ randSet,
        (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam ≤
        ∑ _i ∈ infoSet ∪ randSet, thresh := by
      apply Finset.sum_le_sum; intro i hi
      have hiG : i ∈ goodSet (ampChannel 𝒩) n thresh := by
        rcases Finset.mem_union.mp hi with hi | hi
        · exact (Finset.mem_filter.mp hi).1
        · exact (Finset.mem_filter.mp hi).1
      simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiG
      have hnn : 0 ≤ (synthChannel (ampChannel 𝒩) n i).fidelityParam := rootFidelity_nonneg _ _
      linarith
    have hcard_le : ((infoSet ∪ randSet).card : ℝ) ≤ (2 : ℝ) ^ n := by
      simpa [Fintype.card_fin] using (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_univ (infoSet ∪ randSet))
    calc ∑ i ∈ infoSet ∪ randSet, (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam
        ≤ ((infoSet ∪ randSet).card : ℝ) * thresh := by simpa [Finset.sum_const, nsmul_eq_mul] using h1
      _ ≤ (2 : ℝ) ^ n * thresh := mul_le_mul_of_nonneg_right hcard_le hthresh_nn
  have hsec_sum_le : ∑ i ∈ (randSet ∪ assistSet)ᶜ,
      (1 / 2 : ℝ) * (synthChannel (phaseChannel 𝒩) n (dualIndex n i)).fidelityParam ≤
      (2 : ℝ) ^ n * thresh := by
    have h1 : ∑ i ∈ (randSet ∪ assistSet)ᶜ,
        (1 / 2 : ℝ) * (synthChannel (phaseChannel 𝒩) n (dualIndex n i)).fidelityParam ≤
        ∑ _i ∈ (randSet ∪ assistSet)ᶜ, thresh := by
      apply Finset.sum_le_sum; intro i hi
      simp only [Finset.mem_compl, Finset.mem_union, randSet, assistSet, Finset.mem_filter,
        Finset.mem_univ, true_and, not_or, not_and, not_not] at hi
      have hiGP : dualIndex n i ∈ goodSet (phaseChannel 𝒩) n thresh := by
        by_cases hiGA : i ∈ goodSet (ampChannel 𝒩) n thresh
        · exact hi.1 hiGA
        · exact hi.2 hiGA
      simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiGP
      have hnn : 0 ≤ (synthChannel (phaseChannel 𝒩) n (dualIndex n i)).fidelityParam :=
        rootFidelity_nonneg _ _
      linarith
    have hcard_le : (((randSet ∪ assistSet)ᶜ).card : ℝ) ≤ (2 : ℝ) ^ n := by
      simpa [Fintype.card_fin] using (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_univ (randSet ∪ assistSet)ᶜ)
    calc ∑ i ∈ (randSet ∪ assistSet)ᶜ,
          (1 / 2 : ℝ) * (synthChannel (phaseChannel 𝒩) n (dualIndex n i)).fidelityParam
        ≤ (((randSet ∪ assistSet)ᶜ).card : ℝ) * thresh := by simpa [Finset.sum_const, nsmul_eq_mul] using h1
      _ ≤ (2 : ℝ) ^ n * thresh := mul_le_mul_of_nonneg_right hcard_le hthresh_nn
  have hcomb_le : wiretapBobError 𝒩 n infoSet randSet assistSet uF +
      wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF ≤
      2 * Real.sqrt ((2 : ℝ) ^ n * thresh) + (2 : ℝ) ^ n * thresh := by
    calc wiretapBobError 𝒩 n infoSet randSet assistSet uF +
          wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF
        ≤ 2 * Real.sqrt (∑ i ∈ infoSet ∪ randSet,
            (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam) +
          ∑ i ∈ (randSet ∪ assistSet)ᶜ,
            (1 / 2 : ℝ) * (synthChannel (phaseChannel 𝒩) n (dualIndex n i)).fidelityParam := huF
      _ ≤ 2 * Real.sqrt ((2 : ℝ) ^ n * thresh) + (2 : ℝ) ^ n * thresh :=
          add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbob_sum_le) (by norm_num))
            hsec_sum_le
  have hbob_nn : 0 ≤ C_priv.bobDecodingError := C_priv.bobDecodingError_nonneg
  have hsec_nn : 0 ≤ C_priv.eveSecrecyError := C_priv.eveSecrecyError_nonneg
  have hbob_le : C_priv.bobDecodingError ≤ 2 * Real.sqrt ((2 : ℝ) ^ n * thresh) + (2 : ℝ) ^ n * thresh := by
    change wiretapBobError 𝒩 n infoSet randSet assistSet uF ≤ _
    have : 0 ≤ wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF := hsec_nn
    linarith
  have hsec_le : C_priv.eveSecrecyError ≤ 2 * Real.sqrt ((2 : ℝ) ^ n * thresh) + (2 : ℝ) ^ n * thresh := by
    change wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF ≤ _
    have : 0 ≤ wiretapBobError 𝒩 n infoSet randSet assistSet uF := hbob_nn
    linarith
  obtain ⟨hexp1, hexp2⟩ := operational_exponent_bounds hn1
  have hrate_ge : symCoherentInfo 𝒩 - ε / 2 ≤ (infoSet.card : ℝ) / (2 : ℝ) ^ n := by
    let gP_dual : Finset (Fin (2 ^ n)) :=
      (goodSet (phaseChannel 𝒩) n thresh).image (dualIndex n)
    have hinfo_eq : infoSet = goodSet (ampChannel 𝒩) n thresh ∩ gP_dual := by
      ext i
      simp only [infoSet, gP_dual, Finset.mem_filter, Finset.mem_inter, Finset.mem_image]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, dualIndex n i, h2, dualIndex_involutive n i⟩
      · rintro ⟨h1, j, hj, rfl⟩; exact ⟨h1, by rwa [dualIndex_involutive]⟩
    have hgP_card : gP_dual.card = (goodSet (phaseChannel 𝒩) n thresh).card :=
      Finset.card_image_of_injective _ (dualIndex_bijective n).1
    have hcard_inter : (goodSet (ampChannel 𝒩) n thresh).card +
        (goodSet (phaseChannel 𝒩) n thresh).card ≤ infoSet.card + 2 ^ n := by
      rw [hinfo_eq, ← hgP_card]
      have hu := Finset.card_union_add_card_inter (goodSet (ampChannel 𝒩) n thresh) gP_dual
      have hle : (goodSet (ampChannel 𝒩) n thresh ∪ gP_dual).card ≤ 2 ^ n := by
        simpa [Fintype.card_fin] using Finset.card_le_univ (goodSet (ampChannel 𝒩) n thresh ∪ gP_dual)
      omega
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hrate1 : ((goodSet (ampChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n +
        ((goodSet (phaseChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n - 1 ≤
        (infoSet.card : ℝ) / (2 : ℝ) ^ n := by
      have hcast : ((goodSet (ampChannel 𝒩) n thresh).card : ℝ) +
          ((goodSet (phaseChannel 𝒩) n thresh).card : ℝ) ≤ (infoSet.card : ℝ) + (2 : ℝ) ^ n := by
        exact_mod_cast hcard_inter
      rw [← add_div, sub_le_iff_le_add, div_le_iff₀ hpow_pos]
      have hmul : ((infoSet.card : ℝ) / (2 : ℝ) ^ n + 1) * (2 : ℝ) ^ n = (infoSet.card : ℝ) + (2 : ℝ) ^ n := by
        field_simp [ne_of_gt hpow_pos]
      linarith
    have hcap := amp_phase_symCapacity_sum 𝒩
    linarith
  refine ⟨C_priv, C_quant, rfl, rfl, hrate_ge, hrate_ge, le_trans hbob_le hexp1,
    le_trans hsec_le hexp1, ?_, ?_⟩
  · -- Entanglement error bound
    have h1 : Real.sqrt (2 * wiretapBobError 𝒩 n infoSet randSet assistSet uF) ≤
        Real.sqrt (2 * (2 * Real.sqrt ((2 : ℝ) ^ n * thresh) + (2 : ℝ) ^ n * thresh)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hbob_le (by norm_num))
    have h2 : Real.sqrt (2 * wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF) ≤
        Real.sqrt (2 * (2 * Real.sqrt ((2 : ℝ) ^ n * thresh) + (2 : ℝ) ^ n * thresh)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsec_le (by norm_num))
    calc C_quant.entanglementError
        = quantumEntanglementError 𝒩 n infoSet assistSet C_quant.encoder 𝒟 := rfl
      _ ≤ Real.sqrt (2 * wiretapBobError 𝒩 n infoSet randSet assistSet uF) +
          Real.sqrt (2 * wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF) := hcoh
      _ ≤ 2 * Real.sqrt (2 * (2 * Real.sqrt ((2 : ℝ) ^ n * thresh) + (2 : ℝ) ^ n * thresh)) := by
          linarith
      _ ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := hexp2
  · -- Vanishing assistance rate for degradable channels
    intro hdeg
    have hsub := degradable_assistance_subset_unpolarized 𝒩 hdeg n hthresh_le
    have hcard : assistSet.card ≤
        (unpolarizedSet (ampChannel 𝒩) n thresh).card +
        (unpolarizedSet (phaseChannel 𝒩) n thresh).card := by
      calc assistSet.card
          ≤ (unpolarizedSet (ampChannel 𝒩) n thresh ∪
              (unpolarizedSet (phaseChannel 𝒩) n thresh).image (dualIndex n)).card :=
            Finset.card_le_card hsub
        _ ≤ (unpolarizedSet (ampChannel 𝒩) n thresh).card +
            ((unpolarizedSet (phaseChannel 𝒩) n thresh).image (dualIndex n)).card :=
            Finset.card_union_le _ _
        _ = (unpolarizedSet (ampChannel 𝒩) n thresh).card +
            (unpolarizedSet (phaseChannel 𝒩) n thresh).card := by
            rw [Finset.card_image_of_injective _ (dualIndex_bijective n).1]
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hdiv : (assistSet.card : ℝ) / (2 : ℝ) ^ n ≤
        ((unpolarizedSet (ampChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n +
        ((unpolarizedSet (phaseChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hpow_pos)
    have hassist_le : (assistSet.card : ℝ) / (2 : ℝ) ^ n ≤ ε / 2 := by linarith
    exact ⟨hassist_le, hassist_le⟩

end PolarCodes
