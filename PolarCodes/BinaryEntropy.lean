/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# Binary Entropy, Binary Convolution, and Scalar Convexity

This module defines the scalar information-theoretic functions from Sections 1.2 and 3.1 of the
manuscript and proves their analytic properties, including **Lemma 3.1** (Perspective-Symmetric
Scalar Inequality):
- Binary entropy `h2` and its inverse `h2Inv` on `[0, 1] → [0, 1/2]`
- Binary convolution `binConv` (`a * b := a(1-b) + (1-a)b`)
- Classical and conjectured quantum Mrs. Gerber functions `gc`, `gq`, and `deltaGap` (`Δ(u, p)`)
- The parametric function `φ(c)` from (3.1) and Lemma 3.1 (`lemma_3_1_gx_nonneg`)
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

lemma h2_eq_negMulLog (p : ℝ) :
    h2 p = (Real.negMulLog p + Real.negMulLog (1 - p)) / Real.log 2 := by
  unfold h2 Real.logb Real.negMulLog
  ring

lemma h2_nonneg {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) : 0 ≤ h2 p := by
  rw [h2_eq_negMulLog]
  apply div_nonneg _ (le_of_lt (Real.log_pos (by norm_num)))
  have h1 : 0 ≤ Real.negMulLog p := Real.negMulLog_nonneg hp.1 hp.2
  have h2' : 0 ≤ Real.negMulLog (1 - p) := Real.negMulLog_nonneg (by linarith [hp.2]) (by linarith [hp.1])
  linarith

lemma continuous_h2 : Continuous h2 := by
  have hfun : h2 = fun p : ℝ ↦ (Real.negMulLog p + Real.negMulLog (1 - p)) / Real.log 2 := by
    ext p; exact h2_eq_negMulLog p
  rw [hfun]
  exact (Real.continuous_negMulLog.add
    (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id))).div_const (Real.log 2)

lemma continuousOn_h2 : ContinuousOn h2 (Icc 0 1) :=
  continuous_h2.continuousOn

lemma hasDerivAt_h2 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt h2 (Real.logb 2 ((1 - p) / p)) p := by
  have h1p : 0 < 1 - p := by linarith
  have hd1 : HasDerivAt Real.negMulLog (-Real.log p - 1) p :=
    Real.hasDerivAt_negMulLog (ne_of_gt hp0)
  have hsub : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) p := by
    simpa using (hasDerivAt_const p (1 : ℝ)).fun_sub (hasDerivAt_id p)
  have hd2 : HasDerivAt (fun x : ℝ ↦ Real.negMulLog (1 - x)) ((-Real.log (1 - p) - 1) * (-1)) p :=
    (Real.hasDerivAt_negMulLog (ne_of_gt h1p)).comp p hsub
  have hsum : HasDerivAt (fun x : ℝ ↦ (Real.negMulLog x + Real.negMulLog (1 - x)) / Real.log 2)
      (((-Real.log p - 1) + (-Real.log (1 - p) - 1) * (-1)) / Real.log 2) p :=
    (hd1.fun_add hd2).div_const (Real.log 2)
  have hfun : (fun x : ℝ ↦ (Real.negMulLog x + Real.negMulLog (1 - x)) / Real.log 2) = h2 := by
    ext x; exact (h2_eq_negMulLog x).symm
  rw [hfun] at hsum
  convert hsum using 1
  rw [Real.logb, Real.log_div (ne_of_gt h1p) (ne_of_gt hp0)]
  ring

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
  · calc h2 p ≤ h2 (1 / 2) := strictMonoOn_h2.monotoneOn ⟨hp.1, hle⟩ ⟨by norm_num, le_rfl⟩ hle
      _ = 1 := h2_half
  · calc h2 p = h2 (1 - p) := (h2_symm p).symm
      _ ≤ h2 (1 / 2) :=
        strictMonoOn_h2.monotoneOn ⟨by linarith [hp.2], by linarith⟩ ⟨by norm_num, le_rfl⟩
          (by linarith)
      _ = 1 := h2_half

lemma strictConcaveOn_h2 : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) h2 := by
  have hfun : h2 = fun p : ℝ ↦ (Real.log 2)⁻¹ * (Real.negMulLog p + Real.negMulLog (1 - p)) := by
    ext p; rw [h2_eq_negMulLog, div_eq_inv_mul]
  rw [hfun]
  have h1 : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) Real.negMulLog :=
    Real.strictConcaveOn_negMulLog.subset (fun x hx ↦ hx.1) (convex_Icc 0 1)
  have h2' : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) (fun p : ℝ ↦ Real.negMulLog (1 - p)) := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hx' : 1 - x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hy' : 1 - y ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hneq : 1 - x ≠ 1 - y := by intro h; exact hxy (by linarith)
    have hcomb : 1 - (a * x + b * y) = a * (1 - x) + b * (1 - y) := by nlinarith
    simpa [smul_eq_mul, hcomb] using h1.2 hx' hy' hneq ha hb hab
  exact (h1.add h2').smul (inv_pos.mpr (Real.log_pos (by norm_num)))

/-! ### Properties of `h2Inv` -/

lemma exists_h2_eq {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ∃ p ∈ Icc (0 : ℝ) (1 / 2), h2 p = u := by
  have himg := intermediate_value_Icc (a := (0 : ℝ)) (b := 1 / 2) (by norm_num)
    (continuousOn_h2.mono (Icc_subset_Icc_right (by norm_num)))
  rw [h2_zero, h2_half] at himg
  exact himg hu

lemma h2Inv_eq_of_h2_eq {p u : ℝ} (hp : p ∈ Icc (0 : ℝ) (1 / 2)) (hpu : h2 p = u) :
    h2Inv u = p := by
  unfold h2Inv
  apply le_antisymm
  · apply csSup_le
    · exact ⟨p, hp, le_of_eq hpu⟩
    · rintro q ⟨hq, hqu⟩
      by_contra hlt
      push_neg at hlt
      have := strictMonoOn_h2 hp hq hlt
      linarith
  · apply le_csSup
    · exact ⟨1 / 2, fun q hq ↦ hq.1.2⟩
    · exact ⟨hp, le_of_eq hpu⟩

lemma h2Inv_h2 {p : ℝ} (hp : p ∈ Icc (0 : ℝ) (1 / 2)) : h2Inv (h2 p) = p :=
  h2Inv_eq_of_h2_eq hp rfl

lemma h2_h2Inv {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : h2 (h2Inv u) = u := by
  rcases exists_h2_eq hu with ⟨p, hp, rfl⟩
  rw [h2Inv_h2 hp]

lemma h2Inv_mem_Icc {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : h2Inv u ∈ Icc (0 : ℝ) (1 / 2) := by
  rcases exists_h2_eq hu with ⟨p, hp, rfl⟩
  rw [h2Inv_h2 hp]
  exact hp

lemma h2Inv_zero : h2Inv 0 = 0 :=
  h2Inv_eq_of_h2_eq ⟨le_rfl, by norm_num⟩ h2_zero

lemma h2Inv_one : h2Inv 1 = 1 / 2 :=
  h2Inv_eq_of_h2_eq ⟨by norm_num, le_rfl⟩ h2_half

lemma strictMonoOn_h2Inv : StrictMonoOn h2Inv (Icc 0 1) := by
  intro u hu v hv huv
  by_contra hle
  push_neg at hle
  have h1 := strictMonoOn_h2.monotoneOn (h2Inv_mem_Icc hv) (h2Inv_mem_Icc hu) hle
  rw [h2_h2Inv hv, h2_h2Inv hu] at h1
  linarith

lemma le_h2Inv_iff {u t : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    t ≤ h2Inv u ↔ h2 t ≤ u := by
  constructor
  · intro h
    have := strictMonoOn_h2.monotoneOn ht (h2Inv_mem_Icc hu) h
    rwa [h2_h2Inv hu] at this
  · intro h
    have htu : h2 t ∈ Icc (0 : ℝ) 1 :=
      ⟨h2_nonneg ⟨ht.1, by linarith [ht.2]⟩, h2_le_one ⟨ht.1, by linarith [ht.2]⟩⟩
    have := strictMonoOn_h2Inv.monotoneOn htu hu h
    rwa [h2Inv_h2 ht] at this

lemma h2Inv_le_iff {u t : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    h2Inv u ≤ t ↔ u ≤ h2 t := by
  constructor
  · intro h
    have := strictMonoOn_h2.monotoneOn (h2Inv_mem_Icc hu) ht h
    rwa [h2_h2Inv hu] at this
  · intro h
    have htu : h2 t ∈ Icc (0 : ℝ) 1 :=
      ⟨h2_nonneg ⟨ht.1, by linarith [ht.2]⟩, h2_le_one ⟨ht.1, by linarith [ht.2]⟩⟩
    have := strictMonoOn_h2Inv.monotoneOn hu htu h
    rwa [h2Inv_h2 ht] at this

lemma convexOn_h2Inv : ConvexOn ℝ (Icc (0 : ℝ) 1) h2Inv := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro u hu v hv a b ha hb hab
  have hu' := h2Inv_mem_Icc hu
  have hv' := h2Inv_mem_Icc hv
  have hcomb_uv : a * u + b * v ∈ Icc (0 : ℝ) 1 :=
    (convex_Icc 0 1) hu hv ha hb hab
  have hcomb_p : a * h2Inv u + b * h2Inv v ∈ Icc (0 : ℝ) (1 / 2) :=
    (convex_Icc 0 (1 / 2)) hu' hv' ha hb hab
  rw [h2Inv_le_iff hcomb_uv hcomb_p]
  have hconc := strictConcaveOn_h2.concaveOn.2
    ⟨hu'.1, by linarith [hu'.2]⟩ ⟨hv'.1, by linarith [hv'.2]⟩ ha hb hab
  simpa [smul_eq_mul, h2_h2Inv hu, h2_h2Inv hv] using hconc

/-! ### Monotonicity of `deltaGap` in `p` (used in Proposition 4.2) -/

lemma antitoneOn_deltaGap {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    AntitoneOn (deltaGap u) (Icc 0 (1 / 2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (1 / 2))
  · unfold deltaGap
    have hc : Continuous (fun p : ℝ ↦ h2 (binConv (h2Inv u) p) - h2 p) :=
      (continuous_h2.comp (by unfold binConv; fun_prop)).sub continuous_h2
    exact hc.continuousOn
  · intro p hp
    rw [interior_Icc] at hp
    rcases hp with ⟨hp0, hp1⟩
    have hp1_mem := h2Inv_mem_Icc hu
    have hq_pos : 0 < binConv (h2Inv u) p := by
      unfold binConv; nlinarith [hp1_mem.1, hp1_mem.2]
    have hq_lt1 : binConv (h2Inv u) p < 1 := by
      have h := binConv_mem_Icc hp1_mem ⟨le_of_lt hp0, le_of_lt hp1⟩
      linarith [h.2]
    have hlin : HasDerivAt (fun x : ℝ ↦ binConv (h2Inv u) x) (1 - 2 * h2Inv u) p := by
      have hfun : (fun x : ℝ ↦ binConv (h2Inv u) x) = fun x : ℝ ↦ h2Inv u + (1 - 2 * h2Inv u) * x := by
        ext x; unfold binConv; ring
      rw [hfun]
      simpa using (hasDerivAt_const p (h2Inv u)).fun_add
        ((hasDerivAt_id p).const_mul (1 - 2 * h2Inv u))
    have hd : HasDerivAt (deltaGap u)
        (Real.logb 2 ((1 - binConv (h2Inv u) p) / binConv (h2Inv u) p) * (1 - 2 * h2Inv u)
          - Real.logb 2 ((1 - p) / p)) p :=
      ((hasDerivAt_h2 hq_pos hq_lt1).comp p hlin).fun_sub (hasDerivAt_h2 hp0 (by linarith))
    exact hd.differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    rcases hp with ⟨hp0, hp1⟩
    have hp1_mem := h2Inv_mem_Icc hu
    have hq_mem := binConv_mem_Icc hp1_mem ⟨le_of_lt hp0, le_of_lt hp1⟩
    have hq_pos : 0 < binConv (h2Inv u) p := by unfold binConv; nlinarith [hp1_mem.1, hp1_mem.2]
    have hq_lt1 : binConv (h2Inv u) p < 1 := by linarith [hq_mem.2]
    have hlin : HasDerivAt (fun x : ℝ ↦ binConv (h2Inv u) x) (1 - 2 * h2Inv u) p := by
      have hfun : (fun x : ℝ ↦ binConv (h2Inv u) x) = fun x : ℝ ↦ h2Inv u + (1 - 2 * h2Inv u) * x := by
        ext x; unfold binConv; ring
      rw [hfun]
      simpa using (hasDerivAt_const p (h2Inv u)).fun_add
        ((hasDerivAt_id p).const_mul (1 - 2 * h2Inv u))
    have hd : HasDerivAt (deltaGap u)
        (Real.logb 2 ((1 - binConv (h2Inv u) p) / binConv (h2Inv u) p) * (1 - 2 * h2Inv u)
          - Real.logb 2 ((1 - p) / p)) p :=
      ((hasDerivAt_h2 hq_pos hq_lt1).comp p hlin).fun_sub (hasDerivAt_h2 hp0 (by linarith))
    rw [hd.deriv]
    have hpleq : p ≤ binConv (h2Inv u) p :=
      le_binConv_right hp1_mem ⟨le_of_lt hp0, le_of_lt hp1⟩
    have hq_ratio_ge : 1 ≤ (1 - binConv (h2Inv u) p) / binConv (h2Inv u) p := by
      rw [le_div_iff₀ hq_pos]; linarith [hq_mem.2]
    have hq_log_nonneg : 0 ≤ Real.logb 2 ((1 - binConv (h2Inv u) p) / binConv (h2Inv u) p) := by
      rw [Real.logb]
      exact div_nonneg (Real.log_nonneg hq_ratio_ge) (le_of_lt (Real.log_pos (by norm_num)))
    have hratio_le : (1 - binConv (h2Inv u) p) / binConv (h2Inv u) p ≤ (1 - p) / p := by
      rw [div_le_div_iff₀ hq_pos hp0]
      nlinarith
    have hlog_le : Real.logb 2 ((1 - binConv (h2Inv u) p) / binConv (h2Inv u) p) ≤
        Real.logb 2 ((1 - p) / p) := by
      rw [Real.logb, Real.logb]
      apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num)))
      exact Real.log_le_log (by positivity) hratio_le
    have hfac : 1 - 2 * h2Inv u ≤ 1 := by linarith [hp1_mem.1]
    nlinarith

/-! ### Lemma 3.1: Perspective-Symmetric Scalar Inequality -/

lemma cParam_zero : cParam 0 = 0 := by
  unfold cParam; norm_num [h2_half]

lemma phiParam_zero : phiParam 0 = 0 := by
  unfold phiParam; simp

lemma cParam_even (y : ℝ) : cParam (-y) = cParam y := by
  unfold cParam
  have h : (1 - (-y)) / 2 = 1 - (1 - y) / 2 := by ring
  rw [h, h2_symm]

lemma phiParam_even (y : ℝ) (hy0 : -1 < y) (hy1 : y < 1) : phiParam (-y) = phiParam y := by
  unfold phiParam
  have h1 : 1 + -y = 1 - y := by ring
  have h2 : 1 - -y = 1 + y := by ring
  rw [h1, h2]
  have hinv : (1 - y) / (1 + y) = ((1 + y) / (1 - y))⁻¹ := by
    field_simp [ne_of_gt (by linarith : 0 < 1 - y), ne_of_gt (by linarith : 0 < 1 + y)]
  rw [hinv, Real.logb, Real.log_inv, Real.logb]
  ring

lemma cParam_eq_logb {y : ℝ} (hy0 : -1 < y) (hy1 : y < 1) :
    cParam y = ((1 + y) / 2) * Real.logb 2 (1 + y) + ((1 - y) / 2) * Real.logb 2 (1 - y) := by
  unfold cParam h2 Real.logb
  have h1 : 1 - (1 - y) / 2 = (1 + y) / 2 := by ring
  rw [h1]
  have hpos1 : 0 < 1 + y := by linarith
  have hpos2 : 0 < 1 - y := by linarith
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.log_div (ne_of_gt hpos2) (by norm_num), Real.log_div (ne_of_gt hpos1) (by norm_num)]
  field_simp [hlog2]
  ring

lemma hasDerivAt_cParam {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt cParam ((1 / 2) * Real.logb 2 ((1 + x) / (1 - x))) x := by
  have hlin : HasDerivAt (fun t : ℝ ↦ (1 - t) / 2) (-1 / 2) x := by
    have hsub : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x)
    simpa using hsub.div_const 2
  have hh2 : HasDerivAt (fun t : ℝ ↦ h2 ((1 - t) / 2))
      (Real.logb 2 ((1 - (1 - x) / 2) / ((1 - x) / 2)) * (-1 / 2)) x :=
    (hasDerivAt_h2 (by linarith) (by linarith)).comp x hlin
  have hc : HasDerivAt cParam (-(Real.logb 2 ((1 - (1 - x) / 2) / ((1 - x) / 2)) * (-1 / 2))) x := by
    unfold cParam
    simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub hh2
  convert hc using 1
  have hrat : (1 - (1 - x) / 2) / ((1 - x) / 2) = (1 + x) / (1 - x) := by
    field_simp [ne_of_gt (by linarith : 0 < 1 - x)]
    ring
  rw [hrat]; ring

lemma hasDerivAt_phiParam {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt phiParam
      ((1 / 2) * Real.logb 2 ((1 + x) / (1 - x)) + x / (Real.log 2 * (1 - x ^ 2))) x := by
  have h1mx : 0 < 1 - x := by linarith
  have h1px : 0 < 1 + x := by linarith
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hd_half : HasDerivAt (fun t : ℝ ↦ t / 2) (1 / 2) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have hd_num : HasDerivAt (fun t : ℝ ↦ 1 + t) 1 x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).fun_add (hasDerivAt_id x)
  have hd_den : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x)
  have hd_quot : HasDerivAt (fun t : ℝ ↦ (1 + t) / (1 - t))
      ((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) x :=
    hd_num.fun_div hd_den (ne_of_gt h1mx)
  have hd_log : HasDerivAt (fun t : ℝ ↦ Real.log ((1 + t) / (1 - t)))
      (((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) / ((1 + x) / (1 - x))) x :=
    hd_quot.log (ne_of_gt (div_pos h1px h1mx))
  have hd_logb : HasDerivAt (fun t : ℝ ↦ Real.logb 2 ((1 + t) / (1 - t)))
      ((((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) / ((1 + x) / (1 - x))) / Real.log 2) x :=
    hd_log.div_const (Real.log 2)
  have hprod := hd_half.fun_mul hd_logb
  convert hprod using 1
  have hsq : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
  rw [hsq]
  field_simp [hlog2, ne_of_gt h1mx, ne_of_gt h1px]
  ring

lemma phiParam_deriv_eq_mul {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (1 / 2) * Real.logb 2 ((1 + x) / (1 - x)) + x / (Real.log 2 * (1 - x ^ 2)) =
      phiDerivParam x * ((1 / 2) * Real.logb 2 ((1 + x) / (1 - x))) := by
  unfold phiDerivParam Real.logb
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h1mx2 : 1 - x ^ 2 ≠ 0 := by nlinarith
  have hlog_pos : 0 < Real.log ((1 + x) / (1 - x)) := by
    apply Real.log_pos
    rw [one_lt_div (by linarith)]
    linarith
  have hlog_ne : Real.log ((1 + x) / (1 - x)) ≠ 0 := ne_of_gt hlog_pos
  field_simp [hlog2, h1mx2, hlog_ne]
  ring

private lemma strictMonoOn_sinh_div : StrictMonoOn (fun v : ℝ ↦ Real.sinh v / v) (Ioi 0) := by
  have hnum_pos : ∀ v > (0 : ℝ), 0 < v * Real.cosh v - Real.sinh v := by
    intro v hv
    have hmono : StrictMonoOn (fun t : ℝ ↦ t * Real.cosh t - Real.sinh t) (Ici 0) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      · exact ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
      · intro t ht
        rw [interior_Ici] at ht
        have hd : HasDerivAt (fun s : ℝ ↦ s * Real.cosh s - Real.sinh s) (t * Real.sinh t) t := by
          have h1 := (hasDerivAt_id t).fun_mul (Real.hasDerivAt_cosh t)
          have h2 := Real.hasDerivAt_sinh t
          convert h1.fun_sub h2 using 1
          ring
        rw [hd.deriv]
        exact mul_pos ht (Real.sinh_pos_iff.mpr ht)
    have h0 := hmono (left_mem_Ici) (le_of_lt hv) hv
    simpa using h0
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact (Real.continuous_sinh.continuousOn).div continuousOn_id (fun t ht ↦ ne_of_gt ht)
  · intro v hv
    rw [interior_Ioi] at hv
    have hd : HasDerivAt (fun t : ℝ ↦ Real.sinh t / t)
        ((Real.cosh v * v - Real.sinh v * 1) / v ^ 2) v :=
      (Real.hasDerivAt_sinh v).fun_div (hasDerivAt_id v) (ne_of_gt hv)
    rw [hd.deriv]
    apply div_pos _ (sq_pos_of_pos hv)
    linarith [hnum_pos v hv]

lemma strictMonoOn_phiDerivParam : StrictMonoOn phiDerivParam (Ioo 0 1) := by
  intro x hx y hy hxy
  have hrewrite : ∀ z ∈ Ioo (0 : ℝ) 1,
      phiDerivParam z = 1 + Real.sinh (Real.log ((1 + z) / (1 - z))) /
        Real.log ((1 + z) / (1 - z)) := by
    intro z hz
    unfold phiDerivParam
    congr 1
    have hpos : 0 < (1 + z) / (1 - z) := div_pos (by linarith [hz.1]) (by linarith [hz.2])
    have hsinh : Real.sinh (Real.log ((1 + z) / (1 - z))) = 2 * z / (1 - z ^ 2) := by
      rw [Real.sinh_eq, Real.exp_log hpos, Real.exp_neg, Real.exp_log hpos]
      have h1mz : 1 - z ≠ 0 := by linarith [hz.2]
      have h1pz : 1 + z ≠ 0 := by linarith [hz.1]
      have hsq : 1 - z ^ 2 = (1 - z) * (1 + z) := by ring
      rw [hsq]
      field_simp [h1mz, h1pz]
      ring
    rw [hsinh]
    ring
  rw [hrewrite x hx, hrewrite y hy]
  apply add_lt_add_left
  have hlog_x : 0 < Real.log ((1 + x) / (1 - x)) := by
    apply Real.log_pos; rw [one_lt_div (by linarith [hx.2])]; linarith [hx.1]
  have hlog_y : 0 < Real.log ((1 + y) / (1 - y)) := by
    apply Real.log_pos; rw [one_lt_div (by linarith [hy.2])]; linarith [hy.1]
  have hrat : (1 + x) / (1 - x) < (1 + y) / (1 - y) := by
    rw [div_lt_div_iff₀ (by linarith [hx.2]) (by linarith [hy.2])]
    nlinarith
  exact strictMonoOn_sinh_div hlog_x hlog_y
    (Real.log_lt_log (div_pos (by linarith [hx.1]) (by linarith [hx.2])) hrat)

/-- **Lemma 3.1 (Tangent Inequality in Parametric Form)**:
For every `x ∈ (0, 1)` and `y ∈ [0, 1)`,
`φ(c(y)) - φ(c(x)) - φ'(c(x)) (c(y) - c(x)) ≥ 0`, with equality iff `y = x`. -/
lemma lemma_3_1_tangent {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ico (0 : ℝ) 1) :
    0 ≤ phiParam y - phiParam x - phiDerivParam x * (cParam y - cParam x) ∧
      (phiParam y - phiParam x - phiDerivParam x * (cParam y - cParam x) = 0 ↔ y = x) := by
  let F : ℝ → ℝ := fun z ↦ phiParam z - phiParam x - phiDerivParam x * (cParam z - cParam x)
  have hFx : F x = 0 := by simp [F]
  have hFcont : ContinuousOn F (Ico 0 1) := by
    have hc_c : ContinuousOn cParam (Ico 0 1) := by
      unfold cParam
      exact continuousOn_const.sub (continuous_h2.comp (by fun_prop)).continuousOn
    have hc_p : ContinuousOn phiParam (Ico 0 1) := by
      unfold phiParam Real.logb
      have hdiv : ContinuousOn (fun z : ℝ ↦ (1 + z) / (1 - z)) (Ico 0 1) :=
        (continuous_const.add continuous_id).continuousOn.div
          (continuous_const.sub continuous_id).continuousOn (fun z hz ↦ by linarith [hz.2])
      have hlog : ContinuousOn (fun z : ℝ ↦ Real.log ((1 + z) / (1 - z))) (Ico 0 1) :=
        hdiv.log (fun z hz ↦ ne_of_gt (div_pos (by linarith [hz.1]) (by linarith [hz.2])))
      exact ((continuous_id.div_const 2).continuousOn.mul (hlog.div_const (Real.log 2)))
    exact (hc_p.sub continuousOn_const).sub
      (continuousOn_const.mul (hc_c.sub continuousOn_const))
  have hFderiv : ∀ z ∈ Ioo (0 : ℝ) 1,
      HasDerivAt F ((phiDerivParam z - phiDerivParam x) *
        ((1 / 2) * Real.logb 2 ((1 + z) / (1 - z)))) z := by
    intro z hz
    have hp := hasDerivAt_phiParam hz.1 hz.2
    have hc := hasDerivAt_cParam hz.1 hz.2
    have h1 := (hp.sub_const (phiParam x)).fun_sub
      ((hc.sub_const (cParam x)).const_mul (phiDerivParam x))
    convert h1 using 1
    rw [phiParam_deriv_eq_mul hz.1 hz.2]
    ring
  have hanti : StrictAntiOn F (Icc 0 x) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 x)
    · exact hFcont.mono (fun z hz ↦ ⟨hz.1, lt_of_le_of_lt hz.2 hx.2⟩)
    · intro z hz
      rw [interior_Icc] at hz
      have hz01 : z ∈ Ioo (0 : ℝ) 1 := ⟨hz.1, lt_trans hz.2 hx.2⟩
      rw [(hFderiv z hz01).deriv]
      have hlt : phiDerivParam z < phiDerivParam x := strictMonoOn_phiDerivParam hz01 hx hz.2
      have hlog : 0 < (1 / 2) * Real.logb 2 ((1 + z) / (1 - z)) := by
        apply mul_pos (by norm_num)
        rw [Real.logb]
        apply div_pos _ (Real.log_pos (by norm_num))
        apply Real.log_pos; rw [one_lt_div (by linarith [hz01.2])]; linarith [hz01.1]
      nlinarith
  have hmono : StrictMonoOn F (Ico x 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico x 1)
    · exact hFcont.mono (fun z hz ↦ ⟨le_trans (le_of_lt hx.1) hz.1, hz.2⟩)
    · intro z hz
      rw [interior_Ico] at hz
      have hz01 : z ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hx.1 hz.1, hz.2⟩
      rw [(hFderiv z hz01).deriv]
      have hgt : phiDerivParam x < phiDerivParam z := strictMonoOn_phiDerivParam hx hz01 hz.1
      have hlog : 0 < (1 / 2) * Real.logb 2 ((1 + z) / (1 - z)) := by
        apply mul_pos (by norm_num)
        rw [Real.logb]
        apply div_pos _ (Real.log_pos (by norm_num))
        apply Real.log_pos; rw [one_lt_div (by linarith [hz01.2])]; linarith [hz01.1]
      nlinarith
  rcases lt_trichotomy y x with hlt | rfl | hgt
  · have hpos : 0 < F y := by
      rw [← hFx]
      exact hanti ⟨hy.1, le_of_lt hlt⟩ ⟨le_of_lt hx.1, le_rfl⟩ hlt
    exact ⟨le_of_lt hpos, ⟨fun h ↦ absurd h (ne_of_gt hpos), fun h ↦ absurd h (ne_of_lt hlt)⟩⟩
  · exact ⟨le_of_eq hFx.symm, ⟨fun _ ↦ rfl, fun _ ↦ hFx⟩⟩
  · have hpos : 0 < F y := by
      rw [← hFx]
      exact hmono ⟨le_rfl, hx.2⟩ ⟨le_of_lt hgt, hy.2⟩ hgt
    exact ⟨le_of_lt hpos, ⟨fun h ↦ absurd h (ne_of_gt hpos), fun h ↦ absurd h (ne_of_gt hgt)⟩⟩

/-- **Lemma 3.1 (Perspective-Symmetric Scalar Inequality)**:
For every `x ∈ (0, 1)` and `t > 0`, `gx x t ≥ 0`, with equality if and only if
`t = (1 + x) / (1 - x)` or `t = (1 - x) / (1 + x)`. -/
theorem lemma_3_1_gx_nonneg {x t : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (ht : 0 < t) :
    0 ≤ gx x t ∧ (gx x t = 0 ↔ t = (1 + x) / (1 - x) ∨ t = (1 - x) / (1 + x)) := by
  set y : ℝ := (t - 1) / (t + 1)
  have ht1 : 0 < 1 + t := by linarith
  have hy_gt : -1 < y := by
    simp only [y]; rw [lt_div_iff₀ (by linarith : 0 < t + 1)]; linarith
  have hy_lt : y < 1 := by
    simp only [y]; rw [div_lt_iff₀ (by linarith : 0 < t + 1)]; linarith
  have habs_mem : |y| ∈ Ico (0 : ℝ) 1 := ⟨abs_nonneg y, abs_lt.mpr ⟨hy_gt, hy_lt⟩⟩
  have h1py : 1 + y = 2 * t / (1 + t) := by
    simp only [y]; field_simp [ne_of_gt ht1, ne_of_gt (by linarith : 0 < t + 1)]; ring
  have h1my : 1 - y = 2 / (1 + t) := by
    simp only [y]; field_simp [ne_of_gt ht1, ne_of_gt (by linarith : 0 < t + 1)]; ring
  have htrat : (1 + y) / (1 - y) = t := by
    rw [h1py, h1my]; field_simp [ne_of_gt ht1]
  have hdiv : gx x t / ((1 + t) / 2) =
      phiParam |y| - phiParam x - phiDerivParam x * (cParam |y| - cParam x) := by
    have hphi_abs : phiParam |y| = phiParam y := by
      rcases le_or_gt 0 y with hy0 | hy0
      · rw [abs_of_nonneg hy0]
      · rw [abs_of_neg hy0, phiParam_even y hy_gt hy_lt]
    have hc_abs : cParam |y| = cParam y := by
      rcases le_or_gt 0 y with hy0 | hy0
      · rw [abs_of_nonneg hy0]
      · rw [abs_of_neg hy0, cParam_even y]
    rw [hphi_abs, hc_abs, cParam_eq_logb hy_gt hy_lt]
    unfold gx betaParam phiParam
    rw [htrat, h1py, h1my]
    have h1 : t / (1 + t) = (2 * t / (1 + t)) / 2 := by ring
    have h2 : 1 / (1 + t) = (2 / (1 + t)) / 2 := by ring
    have hy_def : y = (t - 1) / (1 + t) := by simp only [y]; ring
    rw [hy_def]
    field_simp [ne_of_gt ht1]
    ring
  have hpos_half : 0 < (1 + t) / 2 := by linarith
  have ⟨hne, heq⟩ := lemma_3_1_tangent hx habs_mem
  have hgx_eq : gx x t = ((1 + t) / 2) *
      (phiParam |y| - phiParam x - phiDerivParam x * (cParam |y| - cParam x)) := by
    rw [← hdiv]; field_simp [ne_of_gt hpos_half]
  constructor
  · rw [hgx_eq]; exact mul_nonneg (le_of_lt hpos_half) hne
  · rw [hgx_eq, mul_eq_zero, or_iff_right (ne_of_gt hpos_half), heq]
    have h1mx : 1 - x ≠ 0 := by linarith [hx.2]
    have h1px : 1 + x ≠ 0 := by linarith [hx.1]
    have ht1' : t + 1 ≠ 0 := by linarith
    constructor
    · intro habs
      rcases eq_or_eq_neg_of_abs_eq habs with hyx | hyx
      · left
        have h : (t - 1) / (t + 1) = x := hyx
        rw [div_eq_iff ht1'] at h
        rw [eq_div_iff h1mx]; linarith
      · right
        have h : (t - 1) / (t + 1) = -x := hyx
        rw [div_eq_iff ht1'] at h
        rw [eq_div_iff h1px]; linarith
    · rintro (rfl | rfl)
      · have : y = x := by
          simp only [y]; field_simp [h1mx]; ring
        rw [this, abs_of_pos hx.1]
      · have : y = -x := by
          simp only [y]; field_simp [h1px]; ring
        rw [this, abs_neg, abs_of_pos hx.1]

end PolarCodes
