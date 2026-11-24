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
  all `H ∈ [1/2, 1)` (Regions 1 and 2)
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

/-! ### Elementary `log` Taylor bounds and `rpow` helper inequalities -/

lemma log_one_add_ge_poly4 {x : ℝ} (hx0 : 0 ≤ x) :
    x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 ≤ Real.log (1 + x) := by
  let f : ℝ → ℝ := fun t ↦ Real.log (1 + t) - (t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4)
  have hf0 : f 0 = 0 := by simp [f]
  have hderiv : ∀ t : ℝ, 0 < 1 + t → HasDerivAt f (t ^ 4 / (1 + t)) t := by
    intro t hpos
    have hd1 : HasDerivAt (fun s : ℝ ↦ Real.log (1 + s)) (1 / (1 + t)) t := by
      simpa using ((hasDerivAt_const t (1 : ℝ)).fun_add (hasDerivAt_id' t)).log (ne_of_gt hpos)
    have h1 := hasDerivAt_id' t
    have h2 : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
      convert (hasDerivAt_pow 2 t).div_const 2 using 1; ring
    have h3 : HasDerivAt (fun s : ℝ ↦ s ^ 3 / 3) (t ^ 2) t := by
      convert (hasDerivAt_pow 3 t).div_const 3 using 1; ring
    have h4 : HasDerivAt (fun s : ℝ ↦ s ^ 4 / 4) (t ^ 3) t := by
      convert (hasDerivAt_pow 4 t).div_const 4 using 1; ring
    convert hd1.fun_sub (((h1.fun_sub h2).fun_add h3).fun_sub h4) using 1
    field_simp [ne_of_gt hpos]; ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · have hc : ContinuousOn (fun t : ℝ ↦ Real.log (1 + t)) (Ici 0) :=
        ContinuousOn.log (by fun_prop) (fun t ht ↦ by linarith [Set.mem_Ici.mp ht])
      exact hc.sub (by fun_prop : Continuous (fun t : ℝ ↦ t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4)).continuousOn
    · intro t ht
      exact (hderiv t (by linarith [Set.mem_Ici.mp (interior_subset ht)])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(hderiv t (by linarith)).deriv]
      positivity
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx0) hx0
  simp only [f] at h hf0; linarith

lemma log_one_add_le_poly3 {x : ℝ} (hx0 : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let f : ℝ → ℝ := fun t ↦ Real.log (1 + t) - (t - t ^ 2 / 2 + t ^ 3 / 3)
  have hf0 : f 0 = 0 := by simp [f]
  have hderiv : ∀ t : ℝ, 0 < 1 + t → HasDerivAt f (-(t ^ 3 / (1 + t))) t := by
    intro t hpos
    have hd1 : HasDerivAt (fun s : ℝ ↦ Real.log (1 + s)) (1 / (1 + t)) t := by
      simpa using ((hasDerivAt_const t (1 : ℝ)).fun_add (hasDerivAt_id' t)).log (ne_of_gt hpos)
    have h1 := hasDerivAt_id' t
    have h2 : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
      convert (hasDerivAt_pow 2 t).div_const 2 using 1; ring
    have h3 : HasDerivAt (fun s : ℝ ↦ s ^ 3 / 3) (t ^ 2) t := by
      convert (hasDerivAt_pow 3 t).div_const 3 using 1; ring
    convert hd1.fun_sub ((h1.fun_sub h2).fun_add h3) using 1
    field_simp [ne_of_gt hpos]; ring
  have hanti : AntitoneOn f (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · have hc : ContinuousOn (fun t : ℝ ↦ Real.log (1 + t)) (Ici 0) :=
        ContinuousOn.log (by fun_prop) (fun t ht ↦ by linarith [Set.mem_Ici.mp ht])
      exact hc.sub (by fun_prop : Continuous (fun t : ℝ ↦ t - t ^ 2 / 2 + t ^ 3 / 3)).continuousOn
    · intro t ht
      exact (hderiv t (by linarith [Set.mem_Ici.mp (interior_subset ht)])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(hderiv t (by linarith)).deriv]
      have : 0 ≤ t ^ 3 / (1 + t) := by positivity
      linarith
  have h := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx0) hx0
  simp only [f] at h hf0; linarith

lemma log_one_sub_le_poly3 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x - x ^ 2 / 2 - x ^ 3 / 3 := by
  let f : ℝ → ℝ := fun t ↦ Real.log (1 - t) - (-t - t ^ 2 / 2 - t ^ 3 / 3)
  have hf0 : f 0 = 0 := by simp [f]
  have hderiv : ∀ t : ℝ, 0 < 1 - t → HasDerivAt f (-(t ^ 3 / (1 - t))) t := by
    intro t hpos
    have hd1 : HasDerivAt (fun s : ℝ ↦ Real.log (1 - s)) (-1 / (1 - t)) t := by
      simpa using ((hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id' t)).log (ne_of_gt hpos)
    have h1 := (hasDerivAt_id' t).fun_neg
    have h2 : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
      convert (hasDerivAt_pow 2 t).div_const 2 using 1; ring
    have h3 : HasDerivAt (fun s : ℝ ↦ s ^ 3 / 3) (t ^ 2) t := by
      convert (hasDerivAt_pow 3 t).div_const 3 using 1; ring
    convert hd1.fun_sub ((h1.fun_sub h2).fun_sub h3) using 1
    field_simp [ne_of_gt hpos]; ring
  have hanti : AntitoneOn f (Ico 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico 0 1)
    · have hc : ContinuousOn (fun t : ℝ ↦ Real.log (1 - t)) (Ico 0 1) :=
        ContinuousOn.log (by fun_prop) (fun t ht ↦ by linarith [ht.2])
      exact hc.sub (by fun_prop : Continuous (fun t : ℝ ↦ -t - t ^ 2 / 2 - t ^ 3 / 3)).continuousOn
    · intro t ht
      rw [interior_Ico] at ht
      exact (hderiv t (by linarith [ht.2])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have ht0 : 0 < t := ht.1
      have hpos : 0 < 1 - t := by linarith [ht.2]
      rw [(hderiv t hpos).deriv]
      have : 0 ≤ t ^ 3 / (1 - t) := by positivity
      linarith
  have h := hanti ⟨le_rfl, by norm_num⟩ ⟨hx0, hx1⟩ hx0
  simp only [f] at h hf0; linarith

lemma log_one_sub_ge_poly4 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -x - x ^ 2 / 2 - x ^ 3 / 3 - x ^ 4 / (4 * (1 - x)) ≤ Real.log (1 - x) := by
  let f : ℝ → ℝ := fun t ↦ Real.log (1 - t) - (-t - t ^ 2 / 2 - t ^ 3 / 3 - t ^ 4 / (4 * (1 - x)))
  have hf0 : f 0 = 0 := by simp [f]
  have hposx : 0 < 1 - x := by linarith
  have hderiv : ∀ t : ℝ, 0 < 1 - t → HasDerivAt f (t ^ 3 * (x - t) / ((1 - t) * (1 - x))) t := by
    intro t hpos
    have hd1 : HasDerivAt (fun s : ℝ ↦ Real.log (1 - s)) (-1 / (1 - t)) t := by
      simpa using ((hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id' t)).log (ne_of_gt hpos)
    have h1 := (hasDerivAt_id' t).fun_neg
    have h2 : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
      convert (hasDerivAt_pow 2 t).div_const 2 using 1; ring
    have h3 : HasDerivAt (fun s : ℝ ↦ s ^ 3 / 3) (t ^ 2) t := by
      convert (hasDerivAt_pow 3 t).div_const 3 using 1; ring
    have h4 : HasDerivAt (fun s : ℝ ↦ s ^ 4 / (4 * (1 - x))) (t ^ 3 / (1 - x)) t := by
      convert (hasDerivAt_pow 4 t).div_const (4 * (1 - x)) using 1
      field_simp [ne_of_gt hposx]; ring
    convert hd1.fun_sub (((h1.fun_sub h2).fun_sub h3).fun_sub h4) using 1
    field_simp [ne_of_gt hpos, ne_of_gt hposx]; ring
  have hmono : MonotoneOn f (Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · have hc : ContinuousOn (fun t : ℝ ↦ Real.log (1 - t)) (Icc 0 x) :=
        ContinuousOn.log (by fun_prop) (fun t ht ↦ by linarith [ht.2])
      exact hc.sub (by fun_prop : Continuous (fun t : ℝ ↦ -t - t ^ 2 / 2 - t ^ 3 / 3 - t ^ 4 / (4 * (1 - x)))).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t (by linarith [ht.2])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0 < t := ht.1
      have hxt : 0 < x - t := by linarith [ht.2]
      have hpos : 0 < 1 - t := by linarith [ht.2]
      rw [(hderiv t hpos).deriv]
      positivity
  have h := hmono ⟨le_rfl, hx0⟩ ⟨hx0, le_rfl⟩ hx0
  simp only [f] at h hf0; linarith

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
    (7071067 : ℝ) / 10000000 < (2 : ℝ) ^ (-(1 : ℝ) / 2) ∧
      (2 : ℝ) ^ (-(1 : ℝ) / 2) < 7071068 / 10000000 := by
  have hsq : ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hpos : 0 < (2 : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  constructor <;> nlinarith

lemma log_three_bounds :
    (1098610 : ℝ) / 1000000 < Real.log 3 ∧ Real.log 3 < 1098614 / 1000000 := by
  have h98 : Real.log ((9 : ℝ) / 8) = Real.log (1 + 1 / 17) - Real.log (1 - 1 / 17) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    congr 1; norm_num
  have hrel : 2 * Real.log 3 = 3 * Real.log 2 + Real.log ((9 : ℝ) / 8) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
      have : (9 : ℝ) = (3 : ℝ) ^ (2 : ℕ) := by norm_num
      rw [this, Real.log_pow]; ring
    have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      have : (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
      rw [this, Real.log_pow]; ring
    linarith
  have h1 := log_one_add_ge_poly4 (x := (1 : ℝ) / 17) (by norm_num)
  have h2 := log_one_add_le_poly3 (x := (1 : ℝ) / 17) (by norm_num)
  have h3 := log_one_sub_le_poly3 (x := (1 : ℝ) / 17) (by norm_num) (by norm_num)
  have h4 := log_one_sub_ge_poly4 (x := (1 : ℝ) / 17) (by norm_num) (by norm_num)
  have hl2_lo := Real.log_two_gt_d9
  have hl2_hi := Real.log_two_lt_d9
  constructor <;> linarith

/-- Numerical bound `θ₀ > 0.05673` (Eq. 1.7). -/
theorem theta0_gt : (5673 : ℝ) / 100000 < theta0 := by
  have hl2_lo := Real.log_two_gt_d9
  have hl2_hi := Real.log_two_lt_d9
  have ⟨hl3_lo, hl3_hi⟩ := log_three_bounds
  have hp1 : (41692 : ℝ) / 1000000 ≤ h2Inv (1 / 4) := by
    rw [le_h2Inv_iff ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩]
    set p : ℝ := 41692 / 1000000
    have hp_eq : p = (1 + 608 / 1000000) / (2 ^ 3 * 3) := by simp only [p]; norm_num
    have hlogp : Real.log p = Real.log (1 + 608 / 1000000) - 3 * Real.log 2 - Real.log 3 := by
      rw [hp_eq, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]; ring
    have hlogp_lb := log_one_add_ge_poly4 (x := (608 : ℝ) / 1000000) (by norm_num)
    have hlog1mp_lb := log_one_sub_ge_poly4 (x := p) (by simp only [p]; norm_num) (by simp only [p]; norm_num)
    rw [h2_eq_negMulLog, div_le_iff₀ (by linarith : 0 < Real.log 2)]
    unfold Real.negMulLog
    have hp_val : p = 41692 / 1000000 := rfl
    nlinarith [hlogp, hlogp_lb, hlog1mp_lb, hl2_lo, hl2_hi, hl3_hi, hp_val]
  have hh2p2 : h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) < 872435 / 1000000 := by
    set p2 : ℝ := 1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)
    have ⟨hlo, hhi⟩ := two_rpow_neg_half_bounds
    have hp2_lo : (2928932 : ℝ) / 10000000 < p2 := by simp only [p2]; linarith
    have hp2_hi : p2 < 2928933 / 10000000 := by simp only [p2]; linarith
    have h1mp2 : 1 - p2 = (2 : ℝ) ^ (-(1 : ℝ) / 2) := by simp only [p2]; ring
    have hlog1mp2 : Real.log (1 - p2) = -(1 / 2) * Real.log 2 := by
      rw [h1mp2, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]; ring
    set q0 : ℝ := 2928932 / 10000000
    have hlog4q0 : Real.log (4 * q0) = Real.log (1 + 1715728 / 21715728) - Real.log (1 - 1715728 / 21715728) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]
      congr 1; simp only [q0]; norm_num
    have hlogq0 : Real.log q0 = Real.log (4 * q0) - 2 * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by simp only [q0]; norm_num)]
      have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
        rw [this, Real.log_pow]; ring
      linarith
    have hu_lo := log_one_add_ge_poly4 (x := (1715728 : ℝ) / 21715728) (by norm_num)
    have hu_hi := log_one_sub_le_poly3 (x := (1715728 : ℝ) / 21715728) (by norm_num) (by norm_num)
    norm_num at hu_lo hu_hi hlog4q0 hlogq0
    have hlogq0_lb : (-122795 : ℝ) / 100000 < Real.log q0 := by linarith
    have hlogp2_ge : (-122795 : ℝ) / 100000 < Real.log p2 :=
      lt_of_lt_of_le hlogq0_lb (Real.log_le_log (by simp only [q0]; norm_num) (le_of_lt hp2_lo))
    rw [h2_eq_negMulLog, div_lt_iff₀ (by linarith : 0 < Real.log 2)]
    unfold Real.negMulLog
    have hp2_pos : 0 < p2 := by linarith
    have hterm1 : -p2 * Real.log p2 < (2928933 / 10000000) * (122795 / 100000) := by nlinarith
    have hterm2 : -(1 - p2) * Real.log (1 - p2) = (1 - p2) * (Real.log 2 / 2) := by
      rw [hlog1mp2]; ring
    nlinarith
  unfold theta0
  nlinarith

lemma theta0_pos : 0 < theta0 := lt_trans (by norm_num) theta0_gt

lemma theta0_lt_101 : theta0 < 101 / 1000 := by
  unfold theta0
  have h1 : h2Inv (1 / 4) ≤ 1 / 20 := by
    rw [h2Inv_le_iff ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩]
    rw [h2_eq_negMulLog, le_div_iff₀ (Real.log_pos (by norm_num))]
    unfold Real.negMulLog
    have hlog20 : 4 * Real.log 2 ≤ Real.log 20 := by
      have h16 : (4 : ℝ) * Real.log 2 = Real.log 16 := by
        have : (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
        rw [this, Real.log_pow]; ring
      rw [h16]; exact Real.log_le_log (by norm_num) (by norm_num)
    have hlog120 : Real.log ((1 : ℝ) / 20) = -Real.log 20 := by
      rw [one_div, Real.log_inv]
    have hlog1920 : Real.log (1 - (1 : ℝ) / 20) ≤ -(1 : ℝ) / 20 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - 1 / 20 by norm_num)
      linarith
    have hl2_hi := Real.log_two_lt_d9
    rw [hlog120]; nlinarith
  have hh2_ge : (811 : ℝ) / 1000 < h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) := by
    have hmono : h2 (1 / 4) ≤ h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) :=
      strictMonoOn_h2.monotoneOn ⟨by norm_num, by norm_num⟩
        ⟨by linarith [two_rpow_neg_half_bounds.2], by linarith [two_rpow_neg_half_bounds.1]⟩
        (by linarith [two_rpow_neg_half_bounds.2])
    have hq : (811 : ℝ) / 1000 < h2 (1 / 4) := by
      rw [h2_eq_negMulLog, lt_div_iff₀ (Real.log_pos (by norm_num))]
      unfold Real.negMulLog
      have h4 : Real.log ((1 : ℝ) / 4) = -2 * Real.log 2 := by
        have : ((1 : ℝ) / 4) = (2 : ℝ) ^ (-2 : ℤ) := by norm_num
        rw [this, Real.log_zpow]; ring
      have h34 : Real.log (1 - (1 : ℝ) / 4) = Real.log 3 - 2 * Real.log 2 := by
        have : (1 : ℝ) - 1 / 4 = 3 / 2 ^ 2 := by norm_num
        rw [this, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; ring
      have ⟨_, hl3_hi⟩ := log_three_bounds
      have hl2_lo := Real.log_two_gt_d9
      have hl2_hi := Real.log_two_lt_d9
      rw [h4, h34]; linarith
    linarith
  have hp1_nn : 0 ≤ h2Inv (1 / 4) := (h2Inv_mem_Icc ⟨by norm_num, by norm_num⟩).1
  have h1mh2_nn : 0 ≤ 1 - h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) := by
    have hmem : 1 - (2 : ℝ) ^ (-(1 : ℝ) / 2) ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [two_rpow_neg_half_bounds.2], by linarith [two_rpow_neg_half_bounds.1]⟩
    linarith [h2_le_one hmem]
  nlinarith

lemma theta0_lt_one : theta0 < 1 := lt_trans theta0_lt_101 (by norm_num)

lemma theta2_gt_theta0 : theta0 < theta2 := by
  have h2_34 : (168 : ℝ) / 100 < (2 : ℝ) ^ ((3 : ℝ) / 4) := by
    have hpow : ((2 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 = 8 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hpos : 0 < (2 : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
    by_contra hle
    have hle' : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 168 / 100 := not_lt.mp hle
    have h4 : ((2 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 ≤ (168 / 100 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (le_of_lt hpos) hle' 4
    rw [hpow] at h4; norm_num at h4
  have hlog_12_7 : Real.logb 2 (12 / 7) < 4 / 5 := by
    rw [Real.logb, div_lt_iff₀ (Real.log_pos (by norm_num))]
    have hpow : ((5 : ℕ) : ℝ) * Real.log (12 / 7 : ℝ) < ((4 : ℕ) : ℝ) * Real.log 2 := by
      rw [← Real.log_pow, ← Real.log_pow]
      exact Real.log_lt_log (by norm_num) (by norm_num)
    norm_num at hpow
    linarith
  have hth2 : (102 : ℝ) / 1000 < theta2 := by
    unfold theta2
    nlinarith
  linarith [theta0_lt_101]

/-- Numerical bound `Λ₀ < 0.99960` (Eq. 1.9). -/
theorem Lambda0_lt : Lambda0 < 99960 / 100000 := by
  unfold Lambda0
  rw [Real.sqrt_lt' (by norm_num)]
  have h := theta0_gt
  nlinarith

lemma Lambda0_pos : 0 < Lambda0 := by
  unfold Lambda0
  apply Real.sqrt_pos.mpr
  have h := theta0_lt_one
  have h0 := theta0_pos
  nlinarith

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
  have hh2_le : h2 p2 ≤ h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) :=
    strictMonoOn_h2.monotoneOn ⟨hp2_nonneg, le_of_lt hp2_lt_half⟩
      ⟨by linarith [two_rpow_neg_half_bounds.2], by linarith [two_rpow_neg_half_bounds.1]⟩
      hp2_le_ref
  have h1mh2_nonneg : 0 ≤ 1 - h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)) := by
    have := h2_le_one (show 1 - (2 : ℝ) ^ (-(1 : ℝ) / 2) ∈ Icc (0 : ℝ) 1 from
      ⟨by linarith [two_rpow_neg_half_bounds.2], by linarith [two_rpow_neg_half_bounds.1]⟩)
    linarith
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

/-- **Proposition 4.3 (Region 2)**: For `H ∈ [3/4, 1)`,
`deltaGap (1 - H) (1 - 2^(H - 1)) ≥ θ₀ H (1 - H)`. -/
lemma prop_4_3_region2 {H : ℝ} (hH1 : 3 / 4 ≤ H) (hH2 : H < 1) :
    theta0 * H * (1 - H) ≤ deltaGap (1 - H) (1 - (2 : ℝ) ^ (H - 1)) := by
  set δ : ℝ := 1 - H
  have hδ0 : 0 < δ := by simp only [δ]; linarith
  have hδ_hi : δ ≤ 1 / 4 := by simp only [δ]; linarith
  have hδ_mem : δ ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hδ0, by linarith⟩
  set L : ℝ := Real.logb 2 (1 / δ)
  have hL_ge : 2 ≤ L := by
    simp only [L, Real.logb]
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    have h4 : (4 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
    have hlog4 : 2 * Real.log 2 = Real.log 4 := by
      have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      rw [this, Real.log_pow]; ring
    rw [hlog4]
    exact Real.log_le_log (by norm_num) h4
  have hL_pos : 0 < L := by linarith
  set p1 : ℝ := h2Inv δ
  have hp1_mem : p1 ∈ Icc (0 : ℝ) (1 / 2) := h2Inv_mem_Icc hδ_mem
  set p2 : ℝ := 1 - (2 : ℝ) ^ (-δ)
  have hp2_eq : 1 - (2 : ℝ) ^ (H - 1) = p2 := by simp only [p2, δ]; congr 2; ring
  rw [hp2_eq]
  have hp1_lb : δ / (4 * L) ≤ p1 := by
    set t : ℝ := δ / (4 * L)
    have ht0 : 0 < t := by simp only [t]; positivity
    have ht_le : t ≤ 1 / 32 := by
      simp only [t]; rw [div_le_iff₀ (by positivity)]; nlinarith
    rw [le_h2Inv_iff hδ_mem ⟨le_of_lt ht0, by linarith⟩]
    have hh2t := h2_le_mul_logb_exp_div ht0 (by linarith)
    have hlog_eq : Real.logb 2 (Real.exp 1 / t) = L + Real.logb 2 (4 * Real.exp 1 * L) := by
      have harg : Real.exp 1 / t = (1 / δ) * (4 * Real.exp 1 * L) := by
        simp only [t]; field_simp [ne_of_gt hδ0, ne_of_gt hL_pos]
      rw [harg, Real.logb, Real.log_mul (by positivity) (by positivity), add_div]
      rfl
    have hanti_L : Real.log (4 * Real.exp 1 * L) / L ≤ Real.log (8 * Real.exp 1) / 2 := by
      let g : ℝ → ℝ := fun s ↦ Real.log (4 * Real.exp 1 * s) / s
      have hganti : AntitoneOn g (Ici 2) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ici 2)
        · have hc : ContinuousOn (fun s : ℝ ↦ Real.log (4 * Real.exp 1 * s)) (Ici 2) :=
            ContinuousOn.log (by fun_prop) (fun s hs ↦ ne_of_gt (by
              have : 2 ≤ s := Set.mem_Ici.mp hs; positivity))
          exact hc.div continuousOn_id (fun s hs ↦ ne_of_gt (by linarith [Set.mem_Ici.mp hs]))
        · intro s hs
          have hs0 : 0 < s := by linarith [Set.mem_Ici.mp (interior_subset hs)]
          have hd1 : HasDerivAt (fun r : ℝ ↦ Real.log (4 * Real.exp 1 * r)) (1 / s) s := by
            have hlin := (hasDerivAt_id' s).const_mul (4 * Real.exp 1)
            convert hlin.log (ne_of_gt (by positivity)) using 1
            field_simp [ne_of_gt hs0, ne_of_gt (Real.exp_pos 1)]
          exact (hd1.fun_div (hasDerivAt_id' s) (ne_of_gt hs0)).differentiableAt.differentiableWithinAt
        · intro s hs
          rw [interior_Ici, Set.mem_Ioi] at hs
          have hs0 : 0 < s := by linarith
          have hd1 : HasDerivAt (fun r : ℝ ↦ Real.log (4 * Real.exp 1 * r)) (1 / s) s := by
            have hlin := (hasDerivAt_id' s).const_mul (4 * Real.exp 1)
            convert hlin.log (ne_of_gt (by positivity)) using 1
            field_simp [ne_of_gt hs0, ne_of_gt (Real.exp_pos 1)]
          have hd := hd1.fun_div (hasDerivAt_id' s) (ne_of_gt hs0)
          rw [hd.deriv]
          have hnum : 1 / s * s - Real.log (4 * Real.exp 1 * s) * 1 ≤ 0 := by
            have h1 : 1 / s * s = 1 := by field_simp [ne_of_gt hs0]
            rw [h1, mul_one, sub_nonpos]
            have hge : Real.exp 1 ≤ 4 * Real.exp 1 * s := by nlinarith [Real.exp_pos 1]
            calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
              _ ≤ Real.log (4 * Real.exp 1 * s) := Real.log_le_log (Real.exp_pos 1) hge
          exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg s)
      have h := hganti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hL_ge) hL_ge
      simpa [g, show (4 : ℝ) * Real.exp 1 * 2 = 8 * Real.exp 1 by ring] using h
    have h8e_lt : Real.log (8 * Real.exp 1) < 5 * Real.log 2 := by
      have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have h32 : (5 : ℝ) * Real.log 2 = Real.log 32 := by
        have : (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
        rw [this, Real.log_pow]; ring
      rw [h32]
      exact Real.log_lt_log (by positivity) (by linarith)
    have hlogb_bound : Real.logb 2 (4 * Real.exp 1 * L) / (4 * L) < 3 / 4 := by
      rw [Real.logb, div_div]
      have h1 : Real.log (4 * Real.exp 1 * L) / (Real.log 2 * (4 * L)) =
          (Real.log (4 * Real.exp 1 * L) / L) / (4 * Real.log 2) := by ring
      rw [h1, div_lt_iff₀ (by positivity : 0 < 4 * Real.log 2)]
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hmul_le : t * Real.logb 2 (Real.exp 1 / t) ≤ δ := by
      rw [hlog_eq]
      have hcalc : t * (L + Real.logb 2 (4 * Real.exp 1 * L)) =
          δ * (1 / 4 + Real.logb 2 (4 * Real.exp 1 * L) / (4 * L)) := by
        simp only [t]; field_simp [ne_of_gt hL_pos]
      rw [hcalc]
      nlinarith
    linarith
  have hp1_ub : p1 ≤ δ / 2 := by
    rw [h2Inv_le_iff hδ_mem ⟨by linarith, by linarith⟩]
    have hconc := strictConcaveOn_h2.concaveOn.2
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, by norm_num⟩)
      (show (1 / 8 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨by norm_num, by norm_num⟩)
      (show 0 ≤ 1 - 4 * δ by linarith)
      (show 0 ≤ 4 * δ by linarith)
      (by ring : (1 - 4 * δ) + 4 * δ = 1)
    simp only [smul_eq_mul, h2_zero, mul_zero, zero_add] at hconc
    have harg : 4 * δ * (1 / 8 : ℝ) = δ / 2 := by ring
    rw [harg] at hconc
    have hq := h2_one_eighth_gt_quarter
    nlinarith
  set q : ℝ := binConv p1 p2
  have hp2_pos : 0 < p2 := by
    simp only [p2]
    have : (2 : ℝ) ^ (-δ) < (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    simpa using this
  have hp2_le : p2 ≤ Real.log 2 * δ := one_sub_two_rpow_neg_le
  have hp1_pos : 0 < p1 := lt_of_lt_of_le (by positivity) hp1_lb
  have hq_gt_p2 : p2 < q := by
    simp only [q, binConv]
    have : 2 * p2 < 1 := by nlinarith [Real.log_two_lt_d9, hp2_le, hδ_hi]
    nlinarith
  have hq_le : q ≤ (6 / 5) * δ := by
    simp only [q, binConv]
    have hl2 := Real.log_two_lt_d9
    nlinarith
  have hq_le_310 : q ≤ 3 / 10 := by linarith
  have hlogq_lb : (1 - (1 / 2) * Real.logb 2 (12 / 7)) * L ≤ Real.logb 2 ((1 - q) / q) := by
    have hq_pos : 0 < q := lt_trans hp2_pos hq_gt_p2
    have hrat : 7 / (12 * δ) ≤ (1 - q) / q := by
      rw [div_le_div_iff₀ (by positivity) hq_pos]
      nlinarith
    have hlog_ge : Real.logb 2 (7 / (12 * δ)) ≤ Real.logb 2 ((1 - q) / q) := by
      rw [Real.logb, Real.logb]
      apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num)))
      exact Real.log_le_log (by positivity) hrat
    have hlog_split : Real.logb 2 (7 / (12 * δ)) = L - Real.logb 2 (12 / 7) := by
      simp only [L, Real.logb]
      have harg : (7 : ℝ) / (12 * δ) = (1 / δ) / (12 / 7) := by field_simp [ne_of_gt hδ0]
      rw [harg, Real.log_div (by positivity) (by norm_num), sub_div]
    have hlog12_7_pos : 0 ≤ Real.logb 2 (12 / 7) := by
      rw [Real.logb]
      exact div_nonneg (Real.log_nonneg (by norm_num)) (le_of_lt (Real.log_pos (by norm_num)))
    nlinarith
  have hconc_slope : (q - p2) * Real.logb 2 ((1 - q) / q) ≤ deltaGap δ p2 := by
    unfold deltaGap
    change (q - p2) * Real.logb 2 ((1 - q) / q) ≤ h2 q - h2 p2
    have hmvt := exists_hasDerivAt_eq_slope h2 (fun x ↦ Real.logb 2 ((1 - x) / x)) hq_gt_p2
      (continuousOn_h2.mono (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩))
      (fun x hx ↦ hasDerivAt_h2 (by linarith [hx.1]) (by linarith [hx.2]))
    rcases hmvt with ⟨c, ⟨hc1, hc2⟩, hslope⟩
    have hc_pos : 0 < c := lt_trans hp2_pos hc1
    have hq_pos : 0 < q := lt_trans hc_pos hc2
    have h1mq_pos : 0 < 1 - q := by linarith
    have hderiv_ge : Real.logb 2 ((1 - q) / q) ≤ Real.logb 2 ((1 - c) / c) := by
      rw [Real.logb, Real.logb]
      apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num)))
      apply Real.log_le_log (div_pos h1mq_pos hq_pos)
      rw [div_le_div_iff₀ hq_pos hc_pos]; nlinarith
    have hmul := mul_le_mul_of_nonneg_left hderiv_ge (show 0 ≤ q - p2 by linarith)
    have heq : (q - p2) * Real.logb 2 ((1 - c) / c) = h2 q - h2 p2 := by
      rw [hslope]; field_simp [ne_of_gt (show 0 < q - p2 by linarith)]
    linarith
  have hq_sub : q - p2 = p1 * (1 - 2 * p2) := by simp only [q, binConv]; ring
  have h1m2p2 : 1 - 2 * p2 = (2 : ℝ) ^ H - 1 := by
    simp only [p2, δ]
    have h2H : (2 : ℝ) ^ H = 2 * (2 : ℝ) ^ (-(1 - H)) := by
      calc (2 : ℝ) ^ H = (2 : ℝ) ^ ((1 : ℝ) + -(1 - H)) := by congr 1; ring
        _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(1 - H)) := Real.rpow_add (by norm_num) _ _
        _ = 2 * (2 : ℝ) ^ (-(1 - H)) := by rw [Real.rpow_one]
    linarith
  have h2H_ge : (2 : ℝ) ^ ((3 : ℝ) / 4) - 1 ≤ 1 - 2 * p2 := by
    rw [h1m2p2]
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hH1
    linarith
  have h2_34_gt1 : 0 < (2 : ℝ) ^ ((3 : ℝ) / 4) - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ ((3 : ℝ) / 4) := by
      rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by norm_num]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
    linarith
  have hlog12_7_lt2 : 0 < 1 - (1 / 2) * Real.logb 2 (12 / 7) := by
    have h : Real.logb 2 (12 / 7) < 2 := by
      rw [Real.logb, div_lt_iff₀ (Real.log_pos (by norm_num))]
      have h4 : 2 * Real.log 2 = Real.log 4 := by
        have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
        rw [this, Real.log_pow]; ring
      rw [h4]; exact Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  have hprod_lb : theta2 * δ ≤ (q - p2) * Real.logb 2 ((1 - q) / q) := by
    rw [hq_sub]
    have hstep1 : (δ / (4 * L)) * ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1) ≤ p1 * (1 - 2 * p2) :=
      mul_le_mul hp1_lb h2H_ge (le_of_lt h2_34_gt1) (le_of_lt hp1_pos)
    have h1m2p2_nn : 0 ≤ 1 - 2 * p2 := by linarith
    have hstep2 : ((δ / (4 * L)) * ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) *
        ((1 - (1 / 2) * Real.logb 2 (12 / 7)) * L) ≤
        (p1 * (1 - 2 * p2)) * Real.logb 2 ((1 - q) / q) :=
      mul_le_mul hstep1 hlogq_lb (by positivity) (mul_nonneg (le_of_lt hp1_pos) h1m2p2_nn)
    have hcancel : ((δ / (4 * L)) * ((2 : ℝ) ^ ((3 : ℝ) / 4) - 1)) *
        ((1 - (1 / 2) * Real.logb 2 (12 / 7)) * L) = theta2 * δ := by
      unfold theta2; field_simp [ne_of_gt hL_pos]
    linarith
  have hH_le : H * (1 - H) ≤ δ := by simp only [δ]; nlinarith
  have hth_le : theta0 * H * (1 - H) ≤ theta2 * δ := by
    have hth := theta2_gt_theta0
    have h0 := theta0_pos
    nlinarith
  linarith

/-- **Proposition 4.3 (Combined Scalar Bound)**:
For all `H ∈ [1/2, 1)`, `deltaGap (1 - H) (1 - 2^(H - 1)) ≥ θ₀ H (1 - H)`. -/
theorem prop_4_3_scalar {H : ℝ} (hH1 : 1 / 2 ≤ H) (hH2 : H < 1) :
    theta0 * H * (1 - H) ≤ deltaGap (1 - H) (1 - (2 : ℝ) ^ (H - 1)) := by
  rcases le_or_gt H (3 / 4) with hle | hgt
  · exact prop_4_3_region1 hH1 hle
  · exact prop_4_3_region2 (le_of_lt hgt) hH2

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
