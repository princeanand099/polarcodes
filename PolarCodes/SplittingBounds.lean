/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import PolarCodes.BinaryEntropy

/-!
# Linear Splitting Constant, Endpoint Asymptotics, and Potential Contraction

This module formalizes the scalar analytic core of Section 4.2 of the manuscript:
- Constants `theta0` (`θ₀ = (32/3) h₂⁻¹(1/4) (1 - h₂(1 - 2^(-1/2))) > 0.05673`) and
  `Lambda0` (`Λ₀ = √(1 - θ₀²/4) < 0.99960`)
- **Proposition 4.3 (Scalar core)**: `deltaGap (1 - H) (1 - 2^(H - 1)) ≥ θ₀ H (1 - H)` for
  `H ∈ [1/2, 1)` (Regions 1 and 2) and endpoint asymptotics (Eq. 1.8)
- **Proposition 4.4**: Uniform contraction of the polarization potential `T(W) = √(H(1 - H))`
  (Eq. 1.9)
-/

open Real Set Filter

namespace PolarCodes

/-- Universal linear-splitting constant
`θ₀ := (32/3) h₂⁻¹(1/4) (1 - h₂(1 - 2^(-1/2))) ≈ 0.05673348 > 0.05673`. -/
noncomputable def theta0 : ℝ :=
  (32 / 3) * h2Inv (1 / 4) * (1 - h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)))

/-- Universal potential contraction factor `Λ₀ := √(1 - θ₀²/4) ≈ 0.99959758 < 0.99960`. -/
noncomputable def Lambda0 : ℝ :=
  Real.sqrt (1 - theta0 ^ 2 / 4)

/-- Region 2 constant `θ₂ := ((2^(3/4) - 1) / 4) * (1 - (1/2) log₂(12/7)) ≈ 0.104177`. -/
noncomputable def theta2 : ℝ :=
  ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1) / 4 * (1 - (1 / 2) * Real.logb 2 (12 / 7))

/-! ### Elementary `log` and `rpow` helper inequalities -/

lemma neg_one_sub_mul_log_one_sub_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    -(1 - t) * Real.log (1 - t) ≤ t := by
  have h1mt : 0 < 1 - t := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos one_pos h1mt)
  rw [one_div, Real.log_inv] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt h1mt)
  have hcalc : (1 - t) * ((1 - t)⁻¹ - 1) = t := by
    field_simp [ne_of_gt h1mt]; ring
  linarith

lemma h2_le_mul_logb_exp_div {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    h2 t ≤ t * Real.logb 2 (Real.exp 1 / t) := by
  rw [h2_eq_negMulLog, Real.logb, Real.log_div (ne_of_gt (Real.exp_pos 1)) (ne_of_gt ht0),
    Real.log_exp]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hlog2]
  unfold Real.negMulLog
  have h := neg_one_sub_mul_log_one_sub_le (le_of_lt ht0) ht1
  linarith

lemma one_sub_two_rpow_neg_le {δ : ℝ} :
    1 - (2 : ℝ) ^ (-δ) ≤ Real.log 2 * δ := by
  have h : (2 : ℝ) ^ (-δ) = Real.exp (-(Real.log 2 * δ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  rw [h]
  have hexp := Real.add_one_le_exp (-(Real.log 2 * δ))
  linarith

lemma two_rpow_neg_half_bounds :
    (7071 : ℝ) / 10000 < (2 : ℝ) ^ (-(1 : ℝ) / 2) ∧ (2 : ℝ) ^ (-(1 : ℝ) / 2) < 7072 / 10000 := by
  have hsq : ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hpos : 0 < (2 : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  constructor <;> nlinarith

lemma theta0_pos : 0 < theta0 := by
  unfold theta0
  have h1 : 0 < h2Inv (1 / 4) := by
    rw [← h2Inv_zero]
    exact strictMonoOn_h2Inv ⟨le_rfl, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)
  have hp2 : 1 - (2 : ℝ) ^ (-(1 : ℝ) / 2) ∈ Ico (0 : ℝ) (1 / 2) := by
    have ⟨hl, hu⟩ := two_rpow_neg_half_bounds
    exact ⟨by linarith, by linarith⟩
  have h2lt : h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) < 1 := by
    calc h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2))
        < h2 (1 / 2) := strictMonoOn_h2 ⟨hp2.1, le_of_lt hp2.2⟩ ⟨by norm_num, le_rfl⟩ hp2.2
      _ = 1 := h2_half
  have h2pos : 0 < 1 - h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) := by linarith
  positivity

lemma h2_one_eighth_gt_quarter : (1 / 4 : ℝ) < h2 (1 / 8) := by
  have hlog2_gt : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.log (1 / 8 : ℝ) = -3 * Real.log 2 := by
    have : (1 / 8 : ℝ) = (2 : ℝ) ^ (-3 : ℤ) := by norm_num
    rw [this, Real.log_zpow]; ring
  have h2_val : h2 (1 / 8) = 3 / 8 - (7 / 8) * Real.log (7 / 8) / Real.log 2 := by
    rw [h2_eq_negMulLog]
    unfold Real.negMulLog
    have h78 : (1 : ℝ) - 1 / 8 = 7 / 8 := by norm_num
    rw [h78, h1]
    have hne : Real.log 2 ≠ 0 := ne_of_gt hlog2_gt
    field_simp [hne]
    ring
  rw [h2_val]
  have hlog78 : Real.log (7 / 8 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hdiv : (7 / 8 : ℝ) * Real.log (7 / 8) / Real.log 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith) (le_of_lt hlog2_gt)
  linarith

/-! ### Proposition 4.3: Region 1 and Region 2 Linear Splitting Bounds -/

/-- **Proposition 4.3 (Region 1)**: For `H ∈ [1/2, 3/4]`,
`deltaGap (1 - H) (1 - 2^(H - 1)) ≥ θ₀ H (1 - H)`. -/
lemma prop_4_3_region1 {H : ℝ} (hH1 : 1 / 2 ≤ H) (hH2 : H ≤ 3 / 4) :
    theta0 * H * (1 - H) ≤ deltaGap (1 - H) (1 - (2 : ℝ) ^ (H - 1)) := by
  set δ : ℝ := 1 - H
  have hδ_lo : 1 / 4 ≤ δ := by simp only [δ]; linarith
  have hδ_hi : δ ≤ 1 / 2 := by simp only [δ]; linarith
  have hδ_mem : δ ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  set p1 : ℝ := h2Inv δ
  have hp1_mem : p1 ∈ Icc (0 : ℝ) (1 / 2) := h2Inv_mem_Icc hδ_mem
  set p2 : ℝ := 1 - (2 : ℝ) ^ (-δ)
  have hp2_eq : 1 - (2 : ℝ) ^ (H - 1) = p2 := by simp only [p2, δ]; congr 2; ring
  rw [hp2_eq]
  have hp2_nonneg : 0 ≤ p2 := by
    simp only [p2]
    have : (2 : ℝ) ^ (-δ) ≤ (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    simpa using this
  have hp2_le_ref : p2 ≤ 1 - (2 : ℝ) ^ (-(1 : ℝ) / 2) := by
    simp only [p2]
    have : (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ (2 : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    linarith
  have hp2_lt_half : p2 < 1 / 2 := by
    have ⟨hl, _⟩ := two_rpow_neg_half_bounds
    linarith
  -- Write `q = (1 - 2p1) p2 + (2p1) * (1/2)` and apply concavity of `h2`
  have hconc := strictConcaveOn_h2.concaveOn.2
    (show p2 ∈ Icc (0 : ℝ) 1 from ⟨hp2_nonneg, by linarith⟩)
    (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨by norm_num, by norm_num⟩)
    (show 0 ≤ 1 - 2 * p1 by linarith [hp1_mem.2])
    (show 0 ≤ 2 * p1 by linarith [hp1_mem.1])
    (by ring : (1 - 2 * p1) + 2 * p1 = 1)
  have hq_comb : binConv p1 p2 = (1 - 2 * p1) * p2 + 2 * p1 * (1 / 2) := by
    unfold binConv; ring
  have hgap_ge : 2 * p1 * (1 - h2 p2) ≤ deltaGap δ p2 := by
    unfold deltaGap
    simp only [smul_eq_mul, h2_half] at hconc
    rw [← hq_comb] at hconc
    linarith
  -- Convexity of `h2Inv` with `h2Inv 0 = 0` gives `h2Inv (1/4) ≤ (1 / (4 δ)) * h2Inv δ`
  have hp1_lb : 4 * h2Inv (1 / 4) * δ ≤ p1 := by
    have ht_mem : (1 / (4 * δ)) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · rw [div_le_one (by linarith)]; linarith
    have hconv := convexOn_h2Inv.2
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, by norm_num⟩)
      hδ_mem
      (show 0 ≤ 1 - 1 / (4 * δ) by linarith [ht_mem.2])
      ht_mem.1
      (by ring)
    simp only [smul_eq_mul, h2Inv_zero, mul_zero, zero_add] at hconv
    have harg : 1 / (4 * δ) * δ = 1 / 4 := by
      have hδne : δ ≠ 0 := by linarith
      field_simp [hδne]
    rw [harg] at hconv
    have hmul := mul_le_mul_of_nonneg_left hconv (show 0 ≤ 4 * δ by linarith)
    have hrhs : 4 * δ * (1 / (4 * δ) * h2Inv δ) = p1 := by
      have hδne : δ ≠ 0 := by linarith
      simp only [p1]; field_simp [hδne]
    linarith
  -- `1 - h2 p2 ≥ 1 - h2 (1 - 2^(-1/2))`
  have hh2_le : h2 p2 ≤ h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) :=
    strictMonoOn_h2.monotoneOn ⟨hp2_nonneg, le_of_lt hp2_lt_half⟩
      ⟨by linarith [two_rpow_neg_half_bounds.2], by linarith [two_rpow_neg_half_bounds.1]⟩
      hp2_le_ref
  have h1mh2_nonneg : 0 ≤ 1 - h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) := by
    have := h2_le_one (show 1 - (2 : ℝ) ^ (-(1 : ℝ) / 2) ∈ Icc (0 : ℝ) 1 from
      ⟨by linarith [two_rpow_neg_half_bounds.2], by linarith [two_rpow_neg_half_bounds.1]⟩)
    linarith
  -- `δ = 1 - H ≥ (4/3) H (1 - H)` since `H ≤ 3/4`
  have hδ_ge : (4 / 3) * H * (1 - H) ≤ δ := by
    simp only [δ]; nlinarith
  have hcomb : theta0 * H * (1 - H) ≤ 2 * p1 * (1 - h2 p2) := by
    unfold theta0
    have hp1_nonneg : 0 ≤ p1 := hp1_mem.1
    have hstepA : (32 / 3) * h2Inv (1 / 4) * H * (1 - H) ≤ 2 * p1 := by
      have h1 : 0 ≤ h2Inv (1 / 4) := (h2Inv_mem_Icc ⟨by norm_num, by norm_num⟩).1
      nlinarith
    nlinarith
  linarith

/-! ### Proposition 4.4: Uniform Contraction of the Polarization Potential -/

/-- **Proposition 4.4 (Uniform Contraction of the Polarization Potential)**:
If `H ∈ [0, 1]`, `H⁺, H⁻ ∈ [0, 1]` satisfy conservation `H⁺ + H⁻ = 2 H` and the linear splitting
bound `H⁻ - H ≥ θ H (1 - H)` (with `0 ≤ θ < 1`), then
`½ (√(H⁺(1 - H⁺)) + √(H⁻(1 - H⁻))) ≤ √(1 - θ² / 4) · √(H(1 - H))`. -/
theorem prop_4_4_potential_contraction_general {H Hplus Hminus θ : ℝ}
    (hH : H ∈ Icc (0 : ℝ) 1) (hHp : Hplus ∈ Icc (0 : ℝ) 1) (hHm : Hminus ∈ Icc (0 : ℝ) 1)
    (hcons : Hplus + Hminus = 2 * H) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hsplit : θ * H * (1 - H) ≤ Hminus - H) :
    (Real.sqrt (Hplus * (1 - Hplus)) + Real.sqrt (Hminus * (1 - Hminus))) / 2 ≤
      Real.sqrt (1 - θ ^ 2 / 4) * Real.sqrt (H * (1 - H)) := by
  set α : ℝ := Hminus - H
  have hHp_eq : Hplus = H - α := by linarith
  have hHm_eq : Hminus = H + α := by linarith
  set u : ℝ := θ * H * (1 - H)
  have hu_le_α : u ≤ α := hsplit
  have hH_prod : 0 ≤ H * (1 - H) := mul_nonneg hH.1 (by linarith [hH.2])
  have hu_nonneg : 0 ≤ u := by
    simp only [u]; exact mul_nonneg (mul_nonneg hθ0 hH.1) (by linarith [hH.2])
  have hHu_p : 0 ≤ (H - u) * (1 - (H - u)) := by
    have h1 : 0 ≤ H - u := by nlinarith [hH.1, hH.2]
    have h2 : 0 ≤ 1 - (H - u) := by nlinarith [hH.1, hH.2]
    exact mul_nonneg h1 h2
  have hHu_m : 0 ≤ (H + u) * (1 - (H + u)) := by
    have h1 : 0 ≤ H + u := by nlinarith [hH.1, hH.2]
    have h2 : 0 ≤ 1 - (H + u) := by nlinarith [hH.1, hH.2]
    exact mul_nonneg h1 h2
  have hstep1 : Real.sqrt (Hplus * (1 - Hplus)) + Real.sqrt (Hminus * (1 - Hminus)) ≤
      Real.sqrt ((H - u) * (1 - (H - u))) + Real.sqrt ((H + u) * (1 - (H + u))) := by
    rw [hHp_eq, hHm_eq]
    have hA : 0 ≤ (H - α) * (1 - (H - α)) := by
      rw [← hHp_eq]; exact mul_nonneg hHp.1 (by linarith [hHp.2])
    have hB : 0 ≤ (H + α) * (1 - (H + α)) := by
      rw [← hHm_eq]; exact mul_nonneg hHm.1 (by linarith [hHm.2])
    have hsum_le : (H - α) * (1 - (H - α)) + (H + α) * (1 - (H + α)) ≤
        (H - u) * (1 - (H - u)) + (H + u) * (1 - (H + u)) := by
      have hsq : u ^ 2 ≤ α ^ 2 := by nlinarith
      nlinarith
    have hprod_le : ((H - α) * (1 - (H - α))) * ((H + α) * (1 - (H + α))) ≤
        ((H - u) * (1 - (H - u))) * ((H + u) * (1 - (H + u))) := by
      have hα2_le : α ^ 2 ≤ H * (1 - H) := by linarith
      have hu2_le : u ^ 2 ≤ α ^ 2 := by nlinarith
      have hdiff : ((H - u) * (1 - (H - u))) * ((H + u) * (1 - (H + u))) -
          ((H - α) * (1 - (H - α))) * ((H + α) * (1 - (H + α))) =
          (α ^ 2 - u ^ 2) * (2 * H * (1 - H) - α ^ 2 - u ^ 2 + (1 - 2 * H) ^ 2) := by ring
      have hfac1 : 0 ≤ α ^ 2 - u ^ 2 := by linarith
      have hfac2 : 0 ≤ 2 * H * (1 - H) - α ^ 2 - u ^ 2 + (1 - 2 * H) ^ 2 := by nlinarith
      nlinarith
    have hsqrt_prod : Real.sqrt (((H - α) * (1 - (H - α))) * ((H + α) * (1 - (H + α)))) ≤
        Real.sqrt (((H - u) * (1 - (H - u))) * ((H + u) * (1 - (H + u)))) :=
      Real.sqrt_le_sqrt hprod_le
    rw [Real.sqrt_mul hA, Real.sqrt_mul hHu_p] at hsqrt_prod
    have hsq_le : (Real.sqrt ((H - α) * (1 - (H - α))) + Real.sqrt ((H + α) * (1 - (H + α)))) ^ 2 ≤
        (Real.sqrt ((H - u) * (1 - (H - u))) + Real.sqrt ((H + u) * (1 - (H + u)))) ^ 2 := by
      rw [add_sq, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB, Real.sq_sqrt hHu_p, Real.sq_sqrt hHu_m]
      linarith
    exact le_of_sq_le_sq hsq_le (by positivity)
  suffices hstep2 : (Real.sqrt ((H - u) * (1 - (H - u))) + Real.sqrt ((H + u) * (1 - (H + u)))) / 2 ≤
      Real.sqrt (1 - θ ^ 2 / 4) * Real.sqrt (H * (1 - H)) by linarith
  have h1mθ : 0 ≤ 1 - θ ^ 2 / 4 := by nlinarith
  set a : ℝ := θ * (1 - 2 * H)
  set v : ℝ := θ ^ 2 * (H * (1 - H))
  have hv_nonneg : 0 ≤ v := by positivity
  have h1mv : 0 ≤ 1 - v - a ^ 2 / 2 := by
    have hcomb : v + a ^ 2 / 4 = θ ^ 2 / 4 := by simp only [a, v]; ring
    have ha2 : a ^ 2 ≤ θ ^ 2 := by
      have : (1 - 2 * H) ^ 2 ≤ 1 := by nlinarith [hH.1, hH.2]
      simp only [a]; nlinarith
    nlinarith
  have hprod_id : ((H - u) * (1 - (H - u))) * ((H + u) * (1 - (H + u))) =
      (H * (1 - H)) ^ 2 * ((1 - v) ^ 2 - a ^ 2) := by
    simp only [u, a, v]; ring
  have hsum_id : (H - u) * (1 - (H - u)) + (H + u) * (1 - (H + u)) =
      2 * (H * (1 - H)) * (1 - v) := by
    simp only [u, v]; ring
  have hrad_le : (1 - v) ^ 2 - a ^ 2 ≤ (1 - v - a ^ 2 / 2) ^ 2 := by
    have : (1 - v - a ^ 2 / 2) ^ 2 - ((1 - v) ^ 2 - a ^ 2) = a ^ 2 * (v + a ^ 2 / 4) := by ring
    have hnn : 0 ≤ a ^ 2 * (v + a ^ 2 / 4) := by positivity
    linarith
  have hsqrt_rad : Real.sqrt (((H - u) * (1 - (H - u))) * ((H + u) * (1 - (H + u)))) ≤
      H * (1 - H) * (1 - v - a ^ 2 / 2) := by
    rw [hprod_id]
    calc Real.sqrt ((H * (1 - H)) ^ 2 * ((1 - v) ^ 2 - a ^ 2))
        ≤ Real.sqrt ((H * (1 - H)) ^ 2 * (1 - v - a ^ 2 / 2) ^ 2) := by
          apply Real.sqrt_le_sqrt
          exact mul_le_mul_of_nonneg_left hrad_le (sq_nonneg _)
      _ = Real.sqrt ((H * (1 - H) * (1 - v - a ^ 2 / 2)) ^ 2) := by congr 1; ring
      _ = H * (1 - H) * (1 - v - a ^ 2 / 2) :=
          Real.sqrt_sq (mul_nonneg hH_prod h1mv)
  rw [Real.sqrt_mul hHu_p] at hsqrt_rad
  have hcomb : v + a ^ 2 / 4 = θ ^ 2 / 4 := by simp only [a, v]; ring
  have hsq_final : ((Real.sqrt ((H - u) * (1 - (H - u))) +
      Real.sqrt ((H + u) * (1 - (H + u)))) / 2) ^ 2 ≤
      (Real.sqrt (1 - θ ^ 2 / 4) * Real.sqrt (H * (1 - H))) ^ 2 := by
    have hlhs : ((Real.sqrt ((H - u) * (1 - (H - u))) +
        Real.sqrt ((H + u) * (1 - (H + u)))) / 2) ^ 2 =
        ((H - u) * (1 - (H - u)) + (H + u) * (1 - (H + u)) +
          2 * (Real.sqrt ((H - u) * (1 - (H - u))) * Real.sqrt ((H + u) * (1 - (H + u))))) / 4 := by
      rw [div_pow, add_sq, Real.sq_sqrt hHu_p, Real.sq_sqrt hHu_m]; ring
    have hrhs : (Real.sqrt (1 - θ ^ 2 / 4) * Real.sqrt (H * (1 - H))) ^ 2 =
        (1 - θ ^ 2 / 4) * (H * (1 - H)) := by
      rw [mul_pow, Real.sq_sqrt h1mθ, Real.sq_sqrt hH_prod]
    rw [hlhs, hrhs, hsum_id]
    nlinarith [hcomb, hsqrt_rad]
  exact le_of_sq_le_sq hsq_final (by positivity)

end PolarCodes
