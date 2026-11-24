/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# Binary Entropy, Binary Convolution, and Scalar Convexity

This module defines the scalar information-theoretic functions from Sections 1.2 and 3.1 of the
manuscript:
- Binary entropy `h2` and its inverse `h2Inv` on `[0, 1] → [0, 1/2]`
- Binary convolution `binConv` (`a * b := a(1-b) + (1-a)b`)
- Classical and conjectured quantum Mrs. Gerber functions `gc`, `gq`, and `deltaGap` (`Δ(u, p)`)
- The parametric function `φ(c)` from (3.1) and Lemma 3.1 (Perspective-Symmetric Scalar Inequality)
-/

open Real Set Filter

namespace PolarCodes

/-- Binary entropy function `h₂(p) = -p log₂ p - (1-p) log₂(1-p)` in bits, with `0 log₂ 0 = 0`. -/
noncomputable def h2 (p : ℝ) : ℝ :=
  -p * Real.logb 2 p - (1 - p) * Real.logb 2 (1 - p)

/-- Inverse binary entropy `h₂⁻¹ : [0, 1] → [0, 1/2]`. -/
noncomputable def h2Inv (u : ℝ) : ℝ :=
  sSup {p ∈ Icc (0 : ℝ) (1 / 2) | h2 p ≤ u}

/-- Binary convolution `a * b := a(1 - b) + (1 - a)b`. -/
def binConv (a b : ℝ) : ℝ :=
  a * (1 - b) + (1 - a) * b

/-- Classical Mrs. Gerber function `g_c(u, v) := h₂(h₂⁻¹(u) * h₂⁻¹(v))`. -/
noncomputable def gc (u v : ℝ) : ℝ :=
  h2 (binConv (h2Inv u) (h2Inv v))

/-- Duality-symmetrized quantum Mrs. Gerber function
`g_q(u, v) := min(g_c(u, v), u + v - 1 + g_c(1 - u, 1 - v))`. -/
noncomputable def gq (u v : ℝ) : ℝ :=
  min (gc u v) (u + v - 1 + gc (1 - u) (1 - v))

/-- Entropy-splitting gap `Δ(u, p) := h₂(h₂⁻¹(u) * p) - h₂(p)`. -/
noncomputable def deltaGap (u p : ℝ) : ℝ :=
  h2 (binConv (h2Inv u) p) - h2 p

/-- Parametric coherence coordinate `c(x) = 1 - h₂((1 - x) / 2)` for `x ∈ [0, 1)`. -/
noncomputable def cParam (x : ℝ) : ℝ :=
  1 - h2 ((1 - x) / 2)

/-- Parametric Jeffreys–Jensen–Shannon function `φ(c(x)) = (x / 2) log₂((1 + x) / (1 - x))`. -/
noncomputable def phiParam (x : ℝ) : ℝ :=
  (x / 2) * Real.logb 2 ((1 + x) / (1 - x))

/-- The function `φ : [0, 1) → [0, ∞)` defined parametrically by (3.1). -/
noncomputable def phi (c : ℝ) : ℝ :=
  phiParam (1 - 2 * h2Inv (1 - c))

/-- Extended-valued `φ : [0, 1] → [0, ∞]` with `φ(1) = ∞`. -/
noncomputable def phiExt (c : ℝ) : ENNReal :=
  if c < 1 then ENNReal.ofReal (phi c) else ⊤

/-- Derivative formula (3.2) for `φ'(c(x))`. -/
noncomputable def phiDerivParam (x : ℝ) : ℝ :=
  1 + (2 * x) / ((1 - x ^ 2) * Real.log ((1 + x) / (1 - x)))

/-- Tangent intercept `β(x) := λ(x) c(x) - φ(c(x))` from Lemma 3.1. -/
noncomputable def betaParam (x : ℝ) : ℝ :=
  phiDerivParam x * cParam x - phiParam x

/-- Perspective-symmetric scalar function `g_x(t)` from (3.3) in Lemma 3.1. -/
noncomputable def gx (x t : ℝ) : ℝ :=
  (1 / 4) * (t - 1) * Real.logb 2 t
    - phiDerivParam x * ((t / 2) * Real.logb 2 (2 * t / (1 + t))
        + (1 / 2) * Real.logb 2 (2 / (1 + t)))
    + betaParam x * ((1 + t) / 2)

/-! ### Elementary identities for `binConv` and `h2` -/

lemma binConv_comm (a b : ℝ) : binConv a b = binConv b a := by
  unfold binConv; ring

lemma binConv_assoc (a b c : ℝ) : binConv (binConv a b) c = binConv a (binConv b c) := by
  unfold binConv; ring

lemma binConv_zero_left (b : ℝ) : binConv 0 b = b := by
  unfold binConv; ring

lemma binConv_zero_right (a : ℝ) : binConv a 0 = a := by
  unfold binConv; ring

lemma binConv_half_left (b : ℝ) : binConv (1 / 2) b = 1 / 2 := by
  unfold binConv; ring

lemma binConv_half_right (a : ℝ) : binConv a (1 / 2) = 1 / 2 := by
  unfold binConv; ring

lemma one_sub_two_mul_binConv (a b : ℝ) :
    1 - 2 * binConv a b = (1 - 2 * a) * (1 - 2 * b) := by
  unfold binConv; ring

lemma binConv_mem_Icc {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) (1 / 2)) (hb : b ∈ Icc (0 : ℝ) (1 / 2)) :
    binConv a b ∈ Icc (0 : ℝ) (1 / 2) := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  constructor
  · unfold binConv; nlinarith
  · have h := one_sub_two_mul_binConv a b
    have hprod : 0 ≤ (1 - 2 * a) * (1 - 2 * b) := by nlinarith
    linarith

lemma le_binConv_left {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) (1 / 2)) (hb : b ∈ Icc (0 : ℝ) (1 / 2)) :
    a ≤ binConv a b := by
  rcases ha with ⟨_, ha1⟩
  rcases hb with ⟨hb0, _⟩
  unfold binConv; nlinarith

lemma le_binConv_right {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) (1 / 2)) (hb : b ∈ Icc (0 : ℝ) (1 / 2)) :
    b ≤ binConv a b := by
  rw [binConv_comm]; exact le_binConv_left hb ha

lemma h2_zero : h2 0 = 0 := by
  simp [h2]

lemma h2_one : h2 1 = 0 := by
  simp [h2]

lemma h2_symm (p : ℝ) : h2 (1 - p) = h2 p := by
  unfold h2
  have h : 1 - (1 - p) = p := by ring
  rw [h]; ring

lemma h2_half : h2 (1 / 2) = 1 := by
  unfold h2
  have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h1, Real.logb, one_div, Real.log_inv]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog2]
  ring

lemma h2_eq_neg_mul_log_div (p : ℝ) :
    h2 p = (-p * Real.log p - (1 - p) * Real.log (1 - p)) / Real.log 2 := by
  unfold h2 Real.logb
  ring

lemma h2_nonneg {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) : 0 ≤ h2 p := by
  rcases hp with ⟨hp0, hp1⟩
  rw [h2_eq_neg_mul_log_div]
  apply div_nonneg _ (le_of_lt (Real.log_pos (by norm_num)))
  have h1 : 0 ≤ -p * Real.log p := by
    rcases eq_or_lt_of_le hp0 with rfl | hp0'
    · simp
    · have hlog : Real.log p ≤ 0 := Real.log_nonpos hp0 hp1
      nlinarith
  have h2' : 0 ≤ -(1 - p) * Real.log (1 - p) := by
    rcases eq_or_lt_of_le (sub_nonneg.mpr hp1) with h0 | h0'
    · rw [← h0]; simp
    · have hlog : Real.log (1 - p) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
      nlinarith
  linarith

lemma hasDerivAt_h2 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt h2 (Real.logb 2 ((1 - p) / p)) p := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h1p : 0 < 1 - p := by linarith
  have hd1 : HasDerivAt (fun x : ℝ ↦ -x * Real.log x) (-Real.log p - 1) p := by
    have := (hasDerivAt_id p).neg.mul (Real.hasDerivAt_log (ne_of_gt hp0))
    convert this using 1
    field_simp [ne_of_gt hp0]
    ring
  have hd2 : HasDerivAt (fun x : ℝ ↦ -(1 - x) * Real.log (1 - x)) (Real.log (1 - p) + 1) p := by
    have hsub : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) p := by
      simpa using (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
    have hneg : HasDerivAt (fun x : ℝ ↦ -(1 - x)) 1 p := by
      simpa using hsub.neg
    have hlog : HasDerivAt (fun x : ℝ ↦ Real.log (1 - x)) ((-1) / (1 - p)) p := by
      simpa using hsub.log (ne_of_gt h1p)
    have := hneg.mul hlog
    convert this using 1
    field_simp [ne_of_gt h1p]
    ring
  have hsum : HasDerivAt (fun x : ℝ ↦ (-x * Real.log x - (1 - x) * Real.log (1 - x)) / Real.log 2)
      (((-Real.log p - 1) + (Real.log (1 - p) + 1)) / Real.log 2) p := by
    have hadd := hd1.add hd2
    have hfun : (fun x : ℝ ↦ -x * Real.log x + -(1 - x) * Real.log (1 - x)) =
        (fun x : ℝ ↦ -x * Real.log x - (1 - x) * Real.log (1 - x)) := by
      ext x; ring
    rw [hfun] at hadd
    exact hadd.div_const (Real.log 2)
  have hfun2 : (fun x : ℝ ↦ (-x * Real.log x - (1 - x) * Real.log (1 - x)) / Real.log 2) = h2 := by
    ext x; exact (h2_eq_neg_mul_log_div x).symm
  rw [hfun2] at hsum
  convert hsum using 1
  rw [Real.logb, Real.log_div (ne_of_gt h1p) (ne_of_gt hp0)]
  ring

lemma continuousOn_h2 : ContinuousOn h2 (Icc 0 1) := by
  have hfun : h2 = fun p : ℝ ↦ (-p * Real.log p - (1 - p) * Real.log (1 - p)) / Real.log 2 := by
    ext p; exact h2_eq_neg_mul_log_div p
  rw [hfun]
  have hc1 : Continuous (fun p : ℝ ↦ p * Real.log p) := Real.continuous_mul_log
  have hc2 : Continuous (fun p : ℝ ↦ (1 - p) * Real.log (1 - p)) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  have hc : Continuous (fun p : ℝ ↦ (-p * Real.log p - (1 - p) * Real.log (1 - p)) / Real.log 2) := by
    have h1 : Continuous (fun p : ℝ ↦ -(p * Real.log p)) := hc1.neg
    have h2' : Continuous (fun p : ℝ ↦ -(p * Real.log p) - (1 - p) * Real.log (1 - p)) := h1.sub hc2
    convert h2'.div_const (Real.log 2) using 1
    ext p; ring
  exact hc.continuousOn

lemma strictMonoOn_h2 : StrictMonoOn h2 (Icc 0 (1 / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 / 2))
  · exact continuousOn_h2.mono (Icc_subset_Icc_right (by norm_num))
  · intro x hx
    rw [interior_Icc] at hx
    rcases hx with ⟨hx0, hx1⟩
    rw [(hasDerivAt_h2 hx0 (by linarith)).deriv]
    rw [Real.logb]
    apply div_pos _ (Real.log_pos (by norm_num))
    apply Real.log_pos
    rw [one_lt_div hx0]
    linarith

lemma h2_le_one {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) : h2 p ≤ 1 := by
  rcases le_or_gt p (1 / 2) with hle | hgt
  · rw [← h2_half]
    exact strictMonoOn_h2.monotoneOn ⟨hp.1, hle⟩ ⟨by norm_num, le_rfl⟩ hle
  · rw [← h2_symm, ← h2_half]
    exact strictMonoOn_h2.monotoneOn ⟨by linarith [hp.2], by linarith⟩ ⟨by norm_num, le_rfl⟩
      (by linarith)

end PolarCodes
