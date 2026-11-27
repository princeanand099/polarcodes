/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.Refinements
import PolarCodes.NoncommutativeUnion
import PolarCodes.ScalarSupplements

/-!
# Standalone `phi` Properties, Fuchs–van de Graaf (Eq. 2.3), and Hockey-Stick Variational Form (Eq. 2.2)

This module proves:
1. Standalone analytic properties of `phi` on `[0, 1)` (`hasDerivAt_phi_cParam`,
   `continuousOn_phi`, `strictMonoOn_phi`, `strictConvexOn_phi`).
2. Fuchs–van de Graaf inequalities (Eq. 2.3) (`one_sub_rootFidelity_le_traceDist`,
   `traceDist_le_sqrt_one_sub_rootFidelity_sq`).
3. Orthogonality `posPartMat hA * negPartMat hA = 0`, hockey-stick variational attainment and
   equality (Eq. 2.2) (`posPartTrace_isGreatest`, `posPartTrace_eq_sSup`,
   `hockeyStick_isGreatest`, `hockeyStick_eq_sSup`), and `vonNeumannEntropy_mem_Icc`.
-/

open Matrix BigOperators Real Set Filter Polynomial
open scoped ComplexOrder Topology

namespace PolarCodes

section PhiStandalone

/-! ### 1. Standalone Properties of `phi` on `[0, 1)` -/

private lemma cParam_eq_iff {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    let x := 1 - 2 * h2Inv (1 - c)
    0 ≤ x ∧ x < 1 ∧ cParam x = c := by
  intro x
  have h1mc0 : 0 < 1 - c := by linarith
  have h1mc1 : 1 - c ≤ 1 := by linarith
  have hinv := h2Inv_mem_Icc ⟨le_of_lt h1mc0, h1mc1⟩
  have hinv_pos : 0 < h2Inv (1 - c) := by
    by_contra h0; push Not at h0
    have heq : h2Inv (1 - c) = 0 := le_antisymm h0 hinv.1
    have := h2_h2Inv ⟨le_of_lt h1mc0, h1mc1⟩
    rw [heq, h2_zero] at this; linarith
  refine ⟨by simp only [x]; linarith [hinv.2], by simp only [x]; linarith, ?_⟩
  simp only [cParam, x]
  have hhalf : (1 - (1 - 2 * h2Inv (1 - c))) / 2 = h2Inv (1 - c) := by ring
  rw [hhalf, h2_h2Inv ⟨le_of_lt h1mc0, h1mc1⟩]; ring

private lemma hasDerivAt_cParam_aux {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt cParam (Real.logb 2 ((1 + x) / (1 - x)) / 2) x := by
  convert hasDerivAt_cParam hx0 hx1 using 1
  ring

private lemma hasDerivAt_phiParam_aux {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt phiParam ((Real.logb 2 ((1 + x) / (1 - x)) + 2 * x / ((1 - x ^ 2) * Real.log 2)) / 2) x := by
  have h1mx : 0 < 1 - x := by linarith
  have h1px : 0 < 1 + x := by linarith
  have h1mx2 : 0 < 1 - x ^ 2 := by nlinarith
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hfun : phiParam = fun t ↦ (t / 2) * (Real.log ((1 + t) / (1 - t)) / Real.log 2) := by
    ext t; simp [phiParam, Real.logb]
  rw [hfun]
  have hd_quo : HasDerivAt (fun t : ℝ ↦ (1 + t) / (1 - t))
      ((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) x := by
    convert ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).div
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) (ne_of_gt h1mx) using 1
    · ext r; rfl
    · simp
  have hd_log : HasDerivAt (fun t : ℝ ↦ Real.log ((1 + t) / (1 - t)))
      (((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) / ((1 + x) / (1 - x))) x :=
    hd_quo.log (ne_of_gt (div_pos h1px h1mx))
  have hd_div : HasDerivAt (fun t : ℝ ↦ Real.log ((1 + t) / (1 - t)) / Real.log 2)
      ((((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) / ((1 + x) / (1 - x))) / Real.log 2) x :=
    hd_log.div_const (Real.log 2)
  have hd_half : HasDerivAt (fun t : ℝ ↦ t / 2) (1 / 2) x :=
    (hasDerivAt_id x).div_const 2
  have hd_mul := hd_half.mul hd_div
  convert hd_mul using 1
  simp only [Real.logb]
  field_simp [ne_of_gt h1mx, ne_of_gt h1px, ne_of_gt h1mx2, hlog2]
  ring

private lemma cParam_deriv_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < Real.logb 2 ((1 + x) / (1 - x)) / 2 := by
  have hgt : 1 < (1 + x) / (1 - x) := by
    rw [one_lt_div (by linarith)]; linarith
  exact div_pos (Real.logb_pos (by norm_num) hgt) two_pos

private lemma phiDerivParam_eq_ratio {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    phiDerivParam x =
      ((Real.logb 2 ((1 + x) / (1 - x)) + 2 * x / ((1 - x ^ 2) * Real.log 2)) / 2) /
        (Real.logb 2 ((1 + x) / (1 - x)) / 2) := by
  have h1mx : 0 < 1 - x := by linarith
  have h1px : 0 < 1 + x := by linarith
  have h1mx2 : 0 < 1 - x ^ 2 := by nlinarith
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog_pos : 0 < Real.log ((1 + x) / (1 - x)) :=
    Real.log_pos (by rw [one_lt_div h1mx]; linarith)
  have hlogb_pos : 0 < Real.logb 2 ((1 + x) / (1 - x)) := by
    rw [Real.logb]; exact div_pos hlog_pos (Real.log_pos (by norm_num))
  unfold phiDerivParam
  simp only [Real.logb]
  field_simp [ne_of_gt h1mx2, hlog2, ne_of_gt hlog_pos, ne_of_gt hlogb_pos]

/-- Standalone derivative of `phi` at `c = cParam x` for `x ∈ (0, 1)`. -/
theorem hasDerivAt_phi_cParam {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt phi (phiDerivParam x) (cParam x) := by
  have hcx_mem : cParam x ∈ Ioo (0 : ℝ) 1 := by
    have hp0 : 0 < (1 - x) / 2 := by linarith
    have hp1 : (1 - x) / 2 < 1 / 2 := by linarith
    have hlt1 : h2 ((1 - x) / 2) < 1 := by
      have := strictMonoOn_h2 ⟨le_of_lt hp0, le_of_lt hp1⟩ (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 (1 / 2)) hp1
      rwa [h2_half] at this
    have hgt0 : 0 < h2 ((1 - x) / 2) := by
      have := strictMonoOn_h2 (by norm_num : (0 : ℝ) ∈ Icc 0 (1 / 2)) ⟨le_of_lt hp0, le_of_lt hp1⟩ hp0
      rwa [h2_zero] at this
    exact ⟨by simp only [cParam]; linarith, by simp only [cParam]; linarith⟩
  have hcont_x : ContinuousAt (fun c : ℝ ↦ 1 - 2 * h2Inv (1 - c)) (cParam x) := by
    have h1 : ContinuousOn (fun c : ℝ ↦ 1 - 2 * h2Inv (1 - c)) (Icc 0 1) := by
      refine continuousOn_const.sub (continuousOn_const.mul ?_)
      exact continuousOn_h2Inv.comp (continuousOn_const.sub continuousOn_id)
        (fun c hc ↦ ⟨by linarith [hc.2], by linarith [hc.1]⟩)
    exact h1.continuousAt (Icc_mem_nhds hcx_mem.1 hcx_mem.2)
  have hinv_at : 1 - 2 * h2Inv (1 - cParam x) = x := by
    simp only [cParam, sub_sub_cancel]
    rw [h2Inv_h2 ⟨by linarith, by linarith⟩]; ring
  have hleft_inv : ∀ᶠ c in 𝓝 (cParam x), cParam (1 - 2 * h2Inv (1 - c)) = c := by
    filter_upwards [Ioo_mem_nhds hcx_mem.1 hcx_mem.2] with c hc
    exact (cParam_eq_iff (le_of_lt hc.1) hc.2).2.2
  have hd_c := hasDerivAt_cParam_aux hx0 hx1
  have hd_inv : HasDerivAt (fun c : ℝ ↦ 1 - 2 * h2Inv (1 - c))
      ((Real.logb 2 ((1 + x) / (1 - x)) / 2)⁻¹) (cParam x) :=
    HasDerivAt.of_local_left_inverse hcont_x (by rwa [hinv_at])
      (ne_of_gt (cParam_deriv_pos hx0 hx1)) hleft_inv
  have hd_phiP : HasDerivAt phiParam
      ((Real.logb 2 ((1 + x) / (1 - x)) + 2 * x / ((1 - x ^ 2) * Real.log 2)) / 2)
      (1 - 2 * h2Inv (1 - cParam x)) := by
    rw [hinv_at]; exact hasDerivAt_phiParam_aux hx0 hx1
  have hcomp_phi : HasDerivAt (fun c : ℝ ↦ phiParam (1 - 2 * h2Inv (1 - c)))
      (((Real.logb 2 ((1 + x) / (1 - x)) + 2 * x / ((1 - x ^ 2) * Real.log 2)) / 2) *
        (Real.logb 2 ((1 + x) / (1 - x)) / 2)⁻¹) (cParam x) :=
    by simpa [Function.comp_def] using hd_phiP.comp (cParam x) hd_inv
  rw [phiDerivParam_eq_ratio hx0 hx1, div_eq_mul_inv]
  exact hcomp_phi

/-- Standalone continuity of `phi` on `[0, 1)`. -/
theorem continuousOn_phi : ContinuousOn phi (Ico (0 : ℝ) 1) := by
  have hx_cont : ContinuousOn (fun c : ℝ ↦ 1 - 2 * h2Inv (1 - c)) (Ico (0 : ℝ) 1) := by
    refine continuousOn_const.sub (continuousOn_const.mul ?_)
    exact continuousOn_h2Inv.comp (continuousOn_const.sub continuousOn_id)
      (fun c hc ↦ ⟨by linarith [hc.2], by linarith [hc.1]⟩)
  have hphiP_cont : ContinuousOn phiParam (Ico (0 : ℝ) 1) := by
    intro x hx
    have hfun : phiParam = fun t : ℝ ↦ (t / 2) * (Real.log ((1 + t) / (1 - t)) / Real.log 2) := by
      ext t; simp [phiParam, Real.logb]
    rw [hfun]
    have h1 : ContinuousAt (fun t : ℝ ↦ (t / 2) * (Real.log ((1 + t) / (1 - t)) / Real.log 2)) x := by
      refine (continuousAt_id.div_const 2).mul ?_
      refine ContinuousAt.div_const ?_ (Real.log 2)
      refine ContinuousAt.comp (g := Real.log) (f := fun t : ℝ ↦ (1 + t) / (1 - t))
        (Real.continuousAt_log (ne_of_gt (div_pos (by linarith [hx.1] : (0 : ℝ) < 1 + x)
          (by linarith [hx.2] : (0 : ℝ) < 1 - x)))) ?_
      exact (continuousAt_const.add continuousAt_id).div
        (continuousAt_const.sub continuousAt_id) (ne_of_gt (by linarith [hx.2] : (0 : ℝ) < 1 - x))
    exact h1.continuousWithinAt
  exact hphiP_cont.comp hx_cont fun c hc ↦
    let h := cParam_eq_iff hc.1 hc.2; ⟨h.1, h.2.1⟩

/-- Standalone strict monotonicity of `phi` on `[0, 1)`. -/
theorem strictMonoOn_phi : StrictMonoOn phi (Ico (0 : ℝ) 1) := by
  have hphiP_mono : StrictMonoOn phiParam (Ico (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hcont : ContinuousOn phiParam (Icc x y) := by
      intro t ht
      have ht0 : 0 ≤ t := le_trans hx.1 ht.1
      have ht1 : t < 1 := lt_of_le_of_lt ht.2 hy.2
      have hfun : phiParam = fun s : ℝ ↦ (s / 2) * (Real.log ((1 + s) / (1 - s)) / Real.log 2) := by
        ext s; simp [phiParam, Real.logb]
      rw [hfun]
      have h1 : ContinuousAt (fun s : ℝ ↦ (s / 2) * (Real.log ((1 + s) / (1 - s)) / Real.log 2)) t := by
        refine (continuousAt_id.div_const 2).mul ?_
        refine ContinuousAt.div_const ?_ (Real.log 2)
        refine ContinuousAt.comp (g := Real.log) (f := fun s : ℝ ↦ (1 + s) / (1 - s))
          (Real.continuousAt_log (ne_of_gt (div_pos (by linarith : (0 : ℝ) < 1 + t) (by linarith : (0 : ℝ) < 1 - t)))) ?_
        exact (continuousAt_const.add continuousAt_id).div
          (continuousAt_const.sub continuousAt_id) (ne_of_gt (by linarith : (0 : ℝ) < 1 - t))
      exact h1.continuousWithinAt
    exact strictMonoOn_of_deriv_pos (convex_Icc x y) hcont
      (fun t ht ↦ by
        rw [interior_Icc] at ht
        have ht0 : 0 < t := lt_of_le_of_lt hx.1 ht.1
        have ht1 : t < 1 := lt_trans ht.2 hy.2
        rw [(hasDerivAt_phiParam_aux ht0 ht1).deriv]
        have h1 : 0 < Real.logb 2 ((1 + t) / (1 - t)) :=
          Real.logb_pos (by norm_num) (by rw [one_lt_div (by linarith)]; linarith)
        have h2 : 0 < 2 * t / ((1 - t ^ 2) * Real.log 2) :=
          div_pos (by linarith) (mul_pos (by nlinarith) (Real.log_pos (by norm_num)))
        linarith)
      (left_mem_Icc.mpr (le_of_lt hxy)) (right_mem_Icc.mpr (le_of_lt hxy)) hxy
  intro c₁ hc₁ c₂ hc₂ hlt
  have h1 := cParam_eq_iff hc₁.1 hc₁.2
  have h2 := cParam_eq_iff hc₂.1 hc₂.2
  have hinv_lt : h2Inv (1 - c₂) < h2Inv (1 - c₁) :=
    strictMonoOn_h2Inv (⟨by linarith [hc₂.2], by linarith [hc₂.1]⟩ : 1 - c₂ ∈ Icc 0 1)
      (⟨by linarith [hc₁.2], by linarith [hc₁.1]⟩ : 1 - c₁ ∈ Icc 0 1) (by linarith)
  exact hphiP_mono ⟨h1.1, h1.2.1⟩ ⟨h2.1, h2.2.1⟩ (by linarith)

/-- Standalone strict convexity of `phi` on `[0, 1)`. -/
theorem strictConvexOn_phi : StrictConvexOn ℝ (Ico (0 : ℝ) 1) phi := by
  have hderiv_mono : StrictMonoOn (deriv phi) (Ioo (0 : ℝ) 1) := by
    intro c₁ hc₁ c₂ hc₂ hlt
    have h1 := cParam_eq_iff (le_of_lt hc₁.1) hc₁.2
    have h2 := cParam_eq_iff (le_of_lt hc₂.1) hc₂.2
    set x₁ := 1 - 2 * h2Inv (1 - c₁)
    set x₂ := 1 - 2 * h2Inv (1 - c₂)
    have hx₁_pos : 0 < x₁ := by
      have hinv_lt : h2Inv (1 - c₁) < 1 / 2 := by
        have hm1 : (1 - c₁ : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hc₁.2], by linarith [hc₁.1]⟩
        have hm2 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
        have hst := strictMonoOn_h2Inv hm1 hm2 (by linarith [hc₁.1])
        rwa [h2Inv_one] at hst
      simp only [x₁]; linarith
    have hx₂_pos : 0 < x₂ := by
      have hinv_lt : h2Inv (1 - c₂) < 1 / 2 := by
        have hm1 : (1 - c₂ : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hc₂.2], by linarith [hc₂.1]⟩
        have hm2 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
        have hst := strictMonoOn_h2Inv hm1 hm2 (by linarith [hc₂.1])
        rwa [h2Inv_one] at hst
      simp only [x₂]; linarith
    have hx_lt : x₁ < x₂ := by
      have hinv_lt : h2Inv (1 - c₂) < h2Inv (1 - c₁) :=
        strictMonoOn_h2Inv (⟨by linarith [hc₂.2], by linarith [hc₂.1]⟩ : 1 - c₂ ∈ Icc 0 1)
          (⟨by linarith [hc₁.2], by linarith [hc₁.1]⟩ : 1 - c₁ ∈ Icc 0 1) (by linarith)
      simp only [x₁, x₂]; linarith
    have hd1 : deriv phi c₁ = phiDerivParam x₁ := by
      have h := (hasDerivAt_phi_cParam hx₁_pos h1.2.1).deriv
      rwa [h1.2.2] at h
    have hd2 : deriv phi c₂ = phiDerivParam x₂ := by
      have h := (hasDerivAt_phi_cParam hx₂_pos h2.2.1).deriv
      rwa [h2.2.2] at h
    rw [hd1, hd2]
    have haux_mono : StrictMonoOn (fun t : ℝ ↦ t / ((1 - t ^ 2) * Real.log ((1 + t) / (1 - t)))) (Ioo 0 1) := by
      intro a ha b hb hab
      let g : ℝ → ℝ := fun t ↦ (1 / t - t) * Real.log ((1 + t) / (1 - t))
      have hg_deriv : ∀ t ∈ Ioo (0 : ℝ) 1,
          HasDerivAt g ((-(1 / t ^ 2 + 1)) * Real.log ((1 + t) / (1 - t)) + 2 / t) t := by
        intro t ht
        have ht0 : 0 < t := ht.1
        have h1mt : 0 < 1 - t := by linarith [ht.2]
        have h1pt : 0 < 1 + t := by linarith
        have hd1' : HasDerivAt (fun s : ℝ ↦ 1 / s - s) (-(1 / t ^ 2) - 1) t := by
          have hinv := hasDerivAt_inv (ne_of_gt ht0)
          have h1' : (fun s : ℝ ↦ 1 / s - s) = (fun s : ℝ ↦ s⁻¹ - s) := by ext s; simp [one_div]
          rw [h1']
          convert hinv.sub (hasDerivAt_id t) using 1
          · ext s; rfl
          · simp [one_div]
        have hd_quo : HasDerivAt (fun s : ℝ ↦ (1 + s) / (1 - s))
            ((1 * (1 - t) - (1 + t) * (-1)) / (1 - t) ^ 2) t := by
          convert ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).div
            ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)) (ne_of_gt h1mt) using 1
          · ext r; rfl
          · simp
        have hd_log : HasDerivAt (fun s : ℝ ↦ Real.log ((1 + s) / (1 - s)))
            (((1 * (1 - t) - (1 + t) * (-1)) / (1 - t) ^ 2) / ((1 + t) / (1 - t))) t :=
          hd_quo.log (ne_of_gt (div_pos h1pt h1mt))
        convert hd1'.mul hd_log using 1
        field_simp [ne_of_gt ht0, ne_of_gt h1mt, ne_of_gt h1pt]
        ring
      have hg_neg : ∀ t ∈ Ioo (0 : ℝ) 1,
          (-(1 / t ^ 2 + 1)) * Real.log ((1 + t) / (1 - t)) + 2 / t < 0 := by
        intro t ht
        have ht0 : 0 < t := ht.1
        have ht1 : t < 1 := ht.2
        have hlog_gt : 2 * t < Real.log ((1 + t) / (1 - t)) := by
          let q : ℝ → ℝ := fun s ↦ Real.log ((1 + s) / (1 - s)) - 2 * s
          have hq_cont : ContinuousOn q (Icc 0 t) := by
            intro s hs
            have h1ms : 0 < 1 - s := by linarith [hs.2, ht1]
            have h1ps : 0 < 1 + s := by linarith [hs.1]
            have hc1 : ContinuousAt (fun r : ℝ ↦ (1 + r) / (1 - r)) s :=
              (continuousAt_const.add continuousAt_id).div
                (continuousAt_const.sub continuousAt_id) (ne_of_gt h1ms)
            have hc2 : ContinuousAt (fun r : ℝ ↦ Real.log ((1 + r) / (1 - r))) s :=
              ContinuousAt.comp (g := Real.log) (f := fun r : ℝ ↦ (1 + r) / (1 - r))
                (Real.continuousAt_log (ne_of_gt (div_pos h1ps h1ms))) hc1
            have hc3 : ContinuousAt (fun r : ℝ ↦ 2 * r) s :=
              continuousAt_const.mul continuousAt_id
            exact (hc2.sub hc3).continuousWithinAt
          have hq_mono : StrictMonoOn q (Icc 0 t) := by
            apply strictMonoOn_of_deriv_pos (convex_Icc 0 t) hq_cont
            intro s hs
            rw [interior_Icc] at hs
            have hs0 : 0 < s := hs.1
            have hs1 : s < 1 := lt_trans hs.2 ht1
            have h1ms : 0 < 1 - s := by linarith
            have h1ps : 0 < 1 + s := by linarith
            have hd_quo : HasDerivAt (fun r : ℝ ↦ (1 + r) / (1 - r))
                ((1 * (1 - s) - (1 + s) * (-1)) / (1 - s) ^ 2) s := by
              convert ((hasDerivAt_const s (1 : ℝ)).add (hasDerivAt_id s)).div
                ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)) (ne_of_gt h1ms) using 1
              · ext r; rfl
              · simp
            have hd_log := hd_quo.log (ne_of_gt (div_pos h1ps h1ms))
            have hd_lin : HasDerivAt (fun r : ℝ ↦ 2 * r) (2 * 1) s :=
              (hasDerivAt_id s).const_mul (2 : ℝ)
            have hd_q : HasDerivAt q (2 * s ^ 2 / (1 - s ^ 2)) s := by
              have hsub := hd_log.sub hd_lin
              convert hsub using 1
              field_simp [ne_of_gt h1ms, ne_of_gt h1ps, ne_of_gt (by nlinarith : 0 < 1 - s ^ 2)]
              ring
            rw [hd_q.deriv]
            exact div_pos (by positivity) (by nlinarith)
          have hq0 : q 0 = 0 := by simp [q]
          have := hq_mono (left_mem_Icc.mpr (le_of_lt ht0)) (right_mem_Icc.mpr (le_of_lt ht0)) ht0
          linarith
        have hpos : 0 < 1 / t ^ 2 + 1 := by positivity
        have hmul : (1 / t ^ 2 + 1) * (2 * t) < (1 / t ^ 2 + 1) * Real.log ((1 + t) / (1 - t)) :=
          mul_lt_mul_of_pos_left hlog_gt hpos
        have halg : (1 / t ^ 2 + 1) * (2 * t) = 2 / t + 2 * t := by
          field_simp [ne_of_gt ht0]
        linarith
      have hg_anti : StrictAntiOn g (Icc a b) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc a b)
        · intro t ht
          exact (hg_deriv t ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hb.2⟩).continuousAt.continuousWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          have htIoo : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans ha.1 ht.1, lt_trans ht.2 hb.2⟩
          rw [(hg_deriv t htIoo).deriv]
          exact hg_neg t htIoo
      have hgb_lt_ga : g b < g a :=
        hg_anti (left_mem_Icc.mpr (le_of_lt hab)) (right_mem_Icc.mpr (le_of_lt hab)) hab
      have hda : 0 < (1 - a ^ 2) * Real.log ((1 + a) / (1 - a)) :=
        mul_pos (by nlinarith [ha.1, ha.2]) (Real.log_pos (by rw [one_lt_div (by linarith [ha.2])]; linarith [ha.1]))
      have hdb : 0 < (1 - b ^ 2) * Real.log ((1 + b) / (1 - b)) :=
        mul_pos (by nlinarith [hb.1, hb.2]) (Real.log_pos (by rw [one_lt_div (by linarith [hb.2])]; linarith [hb.1]))
      rw [div_lt_div_iff₀ hda hdb]
      have hga_eq : g a = ((1 - a ^ 2) * Real.log ((1 + a) / (1 - a))) / a := by
        simp only [g]; field_simp [ne_of_gt ha.1]
      have hgb_eq : g b = ((1 - b ^ 2) * Real.log ((1 + b) / (1 - b))) / b := by
        simp only [g]; field_simp [ne_of_gt hb.1]
      rw [hga_eq, hgb_eq, div_lt_div_iff₀ hb.1 ha.1] at hgb_lt_ga
      linarith
    unfold phiDerivParam
    have hlt' := haux_mono ⟨hx₁_pos, h1.2.1⟩ ⟨hx₂_pos, h2.2.1⟩ hx_lt
    dsimp only at hlt'
    have h2lt : 2 * (x₁ / ((1 - x₁ ^ 2) * Real.log ((1 + x₁) / (1 - x₁)))) <
        2 * (x₂ / ((1 - x₂ ^ 2) * Real.log ((1 + x₂) / (1 - x₂)))) :=
      mul_lt_mul_of_pos_left hlt' two_pos
    rw [mul_div_assoc', mul_div_assoc'] at h2lt
    linarith
  refine ⟨convex_Ico 0 1, ?_⟩
  intro x hx y hy hne a b ha hb hab
  have hderiv_Ioo : ∀ w ∈ Ioo (0 : ℝ) 1, HasDerivAt phi (deriv phi w) w := by
    intro w hw
    have hw_eq := cParam_eq_iff (le_of_lt hw.1) hw.2
    set xw := 1 - 2 * h2Inv (1 - w)
    have hxw_pos : 0 < xw := by
      have hinv_lt : h2Inv (1 - w) < 1 / 2 := by
        have hm1 : (1 - w : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hw.2], by linarith [hw.1]⟩
        have hm2 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
        have hst := strictMonoOn_h2Inv hm1 hm2 (by linarith [hw.1])
        rwa [h2Inv_one] at hst
      simp only [xw]; linarith
    have hd := hasDerivAt_phi_cParam hxw_pos hw_eq.2.1
    rw [hw_eq.2.2] at hd
    rw [hd.deriv]; exact hd
  suffices hsym : ∀ x' y' a' b' : ℝ, x' ∈ Ico (0 : ℝ) 1 → y' ∈ Ico (0 : ℝ) 1 →
      x' < y' → 0 < a' → 0 < b' → a' + b' = 1 →
      phi (a' * x' + b' * y') < a' * phi x' + b' * phi y' by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · simpa [smul_eq_mul] using hsym x y a b hx hy hlt ha hb hab
    · have h := hsym y x b a hy hx hgt hb ha (by linarith)
      simpa [smul_eq_mul, add_comm] using h
  intro x' y' a' b' hx' hy' hxy ha' hb' hab'
  set z := a' * x' + b' * y'
  have hpos_d : 0 < y' - x' := by linarith
  have hzx : z - x' = b' * (y' - x') := by
    simp only [z]; rw [show a' = 1 - b' by linarith]; ring
  have hyz : y' - z = a' * (y' - x') := by
    simp only [z]; rw [show b' = 1 - a' by linarith]; ring
  have hxz : x' < z := by linarith [mul_pos hb' hpos_d]
  have hzy : z < y' := by linarith [mul_pos ha' hpos_d]
  have ⟨c₁, hc₁, hceq₁⟩ := exists_hasDerivAt_eq_slope phi (deriv phi) hxz
    (continuousOn_phi.mono fun w hw ↦ ⟨le_trans hx'.1 hw.1, lt_of_le_of_lt hw.2 (lt_trans hzy hy'.2)⟩)
    (fun w hw ↦ hderiv_Ioo w ⟨lt_of_le_of_lt hx'.1 hw.1, lt_trans hw.2 (lt_trans hzy hy'.2)⟩)
  have ⟨c₂, hc₂, hceq₂⟩ := exists_hasDerivAt_eq_slope phi (deriv phi) hzy
    (continuousOn_phi.mono fun w hw ↦ ⟨le_trans hx'.1 (le_trans (le_of_lt hxz) hw.1), lt_of_le_of_lt hw.2 hy'.2⟩)
    (fun w hw ↦ hderiv_Ioo w ⟨lt_of_le_of_lt hx'.1 (lt_trans hxz hw.1), lt_trans hw.2 hy'.2⟩)
  have hc₁_mem : c₁ ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hx'.1 hc₁.1, lt_trans hc₁.2 (lt_trans hzy hy'.2)⟩
  have hc₂_mem : c₂ ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hx'.1 (lt_trans hxz hc₂.1), lt_trans hc₂.2 hy'.2⟩
  have hlt_slope : (phi z - phi x') / (z - x') < (phi y' - phi z) / (y' - z) := by
    rw [← hceq₁, ← hceq₂]
    exact hderiv_mono hc₁_mem hc₂_mem (lt_trans hc₁.2 hc₂.1)
  rw [div_lt_div_iff₀ (by linarith) (by linarith), hzx, hyz] at hlt_slope
  have hlt2 : (phi z - phi x') * a' < (phi y' - phi z) * b' := by
    nlinarith [hpos_d]
  have hsum_z : phi z * a' + phi z * b' = phi z := by
    rw [← mul_add, hab', mul_one]
  linarith

end PhiStandalone

section FuchsVanDeGraaf

/-! ### 2. Fuchs–van de Graaf Inequalities (Eq. 2.3) -/

variable {d : Type*} [Fintype d] [DecidableEq d]

private lemma charpoly_mul_rect_eq {d₁ d₂ : Type*}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (A : Matrix d₁ d₂ ℂ) (B : Matrix d₂ d₁ ℂ) :
    (A * B).charpoly * Polynomial.X ^ (Fintype.card d₂) =
      (B * A).charpoly * Polynomial.X ^ (Fintype.card d₁) := by
  let P : Matrix (d₁ ⊕ d₂) (d₁ ⊕ d₂) ℂ := Matrix.fromBlocks 0 A 0 0
  let Q : Matrix (d₁ ⊕ d₂) (d₁ ⊕ d₂) ℂ := Matrix.fromBlocks 0 0 B 0
  have hPQ : P * Q = Matrix.fromBlocks (A * B) 0 0 0 := by
    simp [P, Q, Matrix.fromBlocks_multiply]
  have hQP : Q * P = Matrix.fromBlocks 0 0 0 (B * A) := by
    simp [P, Q, Matrix.fromBlocks_multiply]
  have hzero1 : (0 : Matrix d₁ d₁ ℂ).charpoly = Polynomial.X ^ Fintype.card d₁ := by
    have h0 : (0 : Matrix d₁ d₁ ℂ) = Matrix.diagonal (fun _ : d₁ ↦ (0 : ℂ)) := by
      ext i j; simp [Matrix.diagonal_apply]
    rw [h0, charpoly_diagonal_complex]; simp [Finset.prod_const]
  have hzero2 : (0 : Matrix d₂ d₂ ℂ).charpoly = Polynomial.X ^ Fintype.card d₂ := by
    have h0 : (0 : Matrix d₂ d₂ ℂ) = Matrix.diagonal (fun _ : d₂ ↦ (0 : ℂ)) := by
      ext i j; simp [Matrix.diagonal_apply]
    rw [h0, charpoly_diagonal_complex]; simp [Finset.prod_const]
  have hcomm := Matrix.charpoly_mul_comm P Q
  rw [hPQ, hQP, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_fromBlocks_zero₁₂,
    hzero2, hzero1, mul_comm (Polynomial.X ^ Fintype.card d₁)] at hcomm
  exact hcomm

lemma traceDist_eq_hockeyStick_one (ρ σ : DensityOp d) :
    traceDist ρ σ = hockeyStick 1 ρ σ := rfl

lemma traceDist_eq_half_traceNorm (ρ σ : DensityOp d) :
    traceDist ρ σ = (1 / 2) * traceNorm (ρ.mat - σ.mat) := by
  have hΔ : (ρ.mat - σ.mat).IsHermitian := ρ.isHermitian.sub σ.isHermitian
  have hsum0 : ∑ i : d, hΔ.eigenvalues i = 0 := by
    have htr : (ρ.mat - σ.mat).trace = 0 := by
      rw [Matrix.trace_sub, ρ.trace_one, σ.trace_one, sub_self]
    have htr_eig : (ρ.mat - σ.mat).trace = ∑ i : d, (hΔ.eigenvalues i : ℂ) := by
      simpa using hΔ.trace_eq_sum_eigenvalues
    have hre := congr_arg Complex.re (htr_eig.symm.trans htr)
    simpa [Complex.re_sum] using hre
  have hpos_neg : posPartTrace hΔ = negPartTrace hΔ := by
    have hsub : posPartTrace hΔ - negPartTrace hΔ = ∑ i : d, hΔ.eigenvalues i := by
      unfold posPartTrace negPartTrace
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      rcases le_total (hΔ.eigenvalues i) 0 with hle | hge
      · rw [max_eq_right hle, max_eq_left (by linarith)]; ring
      · rw [max_eq_left hge, max_eq_right (by linarith)]; ring
    linarith
  have habs : ∑ i : d, |hΔ.eigenvalues i| = posPartTrace hΔ + negPartTrace hΔ := by
    unfold posPartTrace negPartTrace
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rcases le_total (hΔ.eigenvalues i) 0 with hle | hge
    · rw [abs_of_nonpos hle, max_eq_right hle, max_eq_left (by linarith)]; ring
    · rw [abs_of_nonneg hge, max_eq_left hge, max_eq_right (by linarith)]; ring
  have htn : traceNorm (ρ.mat - σ.mat) = ∑ i : d, |hΔ.eigenvalues i| := by
    set U : Matrix d d ℂ := (hΔ.eigenvectorUnitary : Matrix d d ℂ)
    have hspec : ρ.mat - σ.mat = U * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues) * star U := by
      simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hΔ.spectral_theorem
    have hU_star : star U * U = 1 := Unitary.coe_star_mul_self hΔ.eigenvectorUnitary
    have hsq : (ρ.mat - σ.mat)ᴴ * (ρ.mat - σ.mat) =
        U * Matrix.diagonal (fun i : d ↦ (((hΔ.eigenvalues i) ^ 2 : ℝ) : ℂ)) * star U := by
      rw [hΔ.eq]
      conv_lhs => rw [hspec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hU_star, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i j; simp only [Matrix.diagonal_apply, Function.comp_apply]
      split_ifs with h
      · subst h; rw [← Complex.ofReal_mul, sq]
      · rfl
    unfold traceNorm
    have hD_herm : (Matrix.diagonal (fun i : d ↦ (((hΔ.eigenvalues i) ^ 2 : ℝ) : ℂ))).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext i; simp
    have hcp : (((ρ.mat - σ.mat)ᴴ * (ρ.mat - σ.mat)).charpoly) =
        (Matrix.diagonal (fun i : d ↦ (((hΔ.eigenvalues i) ^ 2 : ℝ) : ℂ))).charpoly := by
      rw [hsq]
      have hsim := Matrix.charpoly_mul_comm (U * Matrix.diagonal (fun i : d ↦ (((hΔ.eigenvalues i) ^ 2 : ℝ) : ℂ))) (star U)
      rw [hsim, ← Matrix.mul_assoc, hU_star, Matrix.one_mul]
    have hsum := spectral_sum_eq_of_charpoly_mul_X_pow (f := Real.sqrt) (k := 0) (l := 0)
      (Matrix.posSemidef_conjTranspose_mul_self (ρ.mat - σ.mat)).isHermitian hD_herm
      (by rw [hcp]) Real.sqrt_zero
    rw [hsum, spectral_sum_diagonal (fun i ↦ (hΔ.eigenvalues i) ^ 2) hD_herm (by simp)]
    apply Finset.sum_congr rfl; intro i _
    exact Real.sqrt_sq_eq_abs _
  have hhs : hockeyStick 1 ρ σ = posPartTrace hΔ := by
    rw [hockeyStick_eq_posPartTrace]
    exact posPartTrace_eq_of_eq _ hΔ (by simp)
  rw [traceDist_eq_hockeyStick_one, hhs, htn, habs]
  linarith

/-- **Fuchs–van de Graaf Lower Bound (Eq. 2.3)**: `1 - F(ρ, σ) ≤ T(ρ, σ)`. -/
theorem one_sub_rootFidelity_le_traceDist (ρ σ : DensityOp d) :
    1 - rootFidelity ρ σ ≤ traceDist ρ σ := by
  have hps := powers_stormer_traceNorm ρ σ
  have htr_le : ((ρ.sqrtMat * σ.sqrtMat).trace).re ≤ rootFidelity ρ σ := by
    have h1 := re_trace_unitary_mul_le_traceNorm (1 : Matrix.unitaryGroup d ℂ) (ρ.sqrtMat * σ.sqrtMat)
    have h2 : traceNorm (ρ.sqrtMat * σ.sqrtMat) = rootFidelity ρ σ := by
      unfold traceNorm rootFidelity
      have hM : (ρ.sqrtMat * σ.sqrtMat)ᴴ * (ρ.sqrtMat * σ.sqrtMat) =
          σ.sqrtMat * ρ.mat * σ.sqrtMat := by
        rw [Matrix.conjTranspose_mul, ρ.sqrtMat_isHermitian.eq, σ.sqrtMat_isHermitian.eq,
          Matrix.mul_assoc, ← Matrix.mul_assoc ρ.sqrtMat ρ.sqrtMat, ρ.sqrtMat_mul_self,
          Matrix.mul_assoc]
      have hcp : (σ.sqrtMat * ρ.mat * σ.sqrtMat).charpoly =
          (ρ.sqrtMat * σ.mat * ρ.sqrtMat).charpoly := by
        have h1' := Matrix.charpoly_mul_comm (σ.sqrtMat * ρ.sqrtMat) (ρ.sqrtMat * σ.sqrtMat)
        have hL : (σ.sqrtMat * ρ.sqrtMat) * (ρ.sqrtMat * σ.sqrtMat) = σ.sqrtMat * ρ.mat * σ.sqrtMat := by
          simp only [Matrix.mul_assoc, ← Matrix.mul_assoc ρ.sqrtMat ρ.sqrtMat, ρ.sqrtMat_mul_self]
        have hR : (ρ.sqrtMat * σ.sqrtMat) * (σ.sqrtMat * ρ.sqrtMat) = ρ.sqrtMat * σ.mat * ρ.sqrtMat := by
          simp only [Matrix.mul_assoc, ← Matrix.mul_assoc σ.sqrtMat σ.sqrtMat, σ.sqrtMat_mul_self]
        rw [← hL, ← hR]; exact h1'
      have hcp' : (((ρ.sqrtMat * σ.sqrtMat)ᴴ * (ρ.sqrtMat * σ.sqrtMat)).charpoly) =
          (ρ.sqrtMat * σ.mat * ρ.sqrtMat).charpoly := by rw [hM, hcp]
      exact spectral_sum_eq_of_charpoly_mul_X_pow (f := Real.sqrt) (k := 0) (l := 0)
        (Matrix.posSemidef_conjTranspose_mul_self _).isHermitian
        (posSemidef_sqrt_mul_sqrt ρ σ).isHermitian (by rw [hcp']) Real.sqrt_zero
    simpa [h2] using h1
  rw [traceDist_eq_half_traceNorm]
  linarith

/-- **Fuchs–van de Graaf Upper Bound (Eq. 2.3)**: `T(ρ, σ) ≤ √(1 - F(ρ, σ)²)`. -/
theorem traceDist_le_sqrt_one_sub_rootFidelity_sq (ρ σ : DensityOp d) :
    traceDist ρ σ ≤ Real.sqrt (1 - rootFidelity ρ σ ^ 2) := by
  obtain ⟨ψ₀, ψ₁, hψ₀, hψ₁, hpt₀, hpt₁, hov⟩ := exists_uhlmann_purification ρ σ
  let P₀ := pureState ψ₀ hψ₀
  let P₁ := pureState ψ₁ hψ₁
  have hcontr : traceDist ρ σ ≤ traceDist P₀ P₁ := by
    rw [traceDist_eq_hockeyStick_one, traceDist_eq_hockeyStick_one,
      hockeyStick_eq_posPartTrace, hockeyStick_eq_posPartTrace]
    have hneg1 : posPartTrace (hockeyStick_isHermitian 1 ρ σ) =
        negPartTrace (σ.isHermitian.sub ρ.isHermitian) := by
      have hBA := σ.isHermitian.sub ρ.isHermitian
      rw [negPartTrace_eq_posPartTrace_neg hBA (by rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, hBA.eq])]
      exact posPartTrace_eq_of_eq _ _ (by simp [neg_sub])
    have hneg2 : posPartTrace (hockeyStick_isHermitian 1 P₀ P₁) =
        negPartTrace (P₁.isHermitian.sub P₀.isHermitian) := by
      have hBA := P₁.isHermitian.sub P₀.isHermitian
      rw [negPartTrace_eq_posPartTrace_neg hBA (by rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, hBA.eq])]
      exact posPartTrace_eq_of_eq _ _ (by simp [neg_sub])
    rw [hneg1, hneg2]
    have hpt_diff : partialTrace₂Mat d d (P₁.mat - P₀.mat) = σ.mat - ρ.mat := by
      rw [map_sub]
      exact congr_arg₂ (· - ·) hpt₁ hpt₀
    have hB' : (partialTrace₂Mat d d (P₁.mat - P₀.mat)).IsHermitian :=
      hpt_diff ▸ (σ.isHermitian.sub ρ.isHermitian)
    rw [negPartTrace_eq_of_eq (σ.isHermitian.sub ρ.isHermitian) hB' hpt_diff.symm]
    exact negPartTrace_map_le (partialTrace₂Mat d d)
      (fun X hX ↦ partialTrace₂Mat_posSemidef hX)
      (fun X _ ↦ by rw [partialTrace₂Mat_trace]) (P₁.isHermitian.sub P₀.isHermitian) hB'
  let c : ℂ := ∑ p : d × d, star (ψ₀ p) * ψ₁ p
  have hc_norm : ‖c‖ = rootFidelity ρ σ := hov
  have hc_le1 : ‖c‖ ≤ 1 := by
    calc ‖c‖ ≤ ∑ p : d × d, ‖star (ψ₀ p) * ψ₁ p‖ := norm_sum_le _ _
      _ = ∑ p : d × d, ‖ψ₀ p‖ * ‖ψ₁ p‖ := by simp [norm_mul]
      _ ≤ Real.sqrt (∑ p, ‖ψ₀ p‖ ^ 2) * Real.sqrt (∑ p, ‖ψ₁ p‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun p ↦ ‖ψ₀ p‖) (fun p ↦ ‖ψ₁ p‖)
      _ = 1 := by rw [hψ₀, hψ₁, Real.sqrt_one, mul_one]
  set r : ℝ := Real.sqrt (1 - ‖c‖ ^ 2)
  have hr_sq : r ^ 2 = 1 - ‖c‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_nonneg c])
  let A : Matrix (d × d) (Fin 2) ℂ := Matrix.of fun p k ↦ if k = 0 then ψ₀ p else ψ₁ p
  let B : Matrix (Fin 2) (d × d) ℂ := Matrix.of fun k p ↦ if k = 0 then star (ψ₀ p) else -star (ψ₁ p)
  have hAB : A * B = P₀.mat - P₁.mat := by
    ext p q
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [A, B, P₀, P₁, pureState, Matrix.mul_apply, Matrix.sub_apply, Matrix.of_apply,
      Fin.sum_univ_two, ↓reduceIte, h10]
    ring
  have hnorm_sum : ∀ (v : (d × d) → ℂ), (∑ p, ‖v p‖ ^ 2 = 1) →
      ∑ p : d × d, star (v p) * v p = (1 : ℂ) := by
    intro v hv
    have h1 : ∀ p, star (v p) * v p = ((‖v p‖ ^ 2 : ℝ) : ℂ) := fun p ↦ by
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [h1, ← Complex.ofReal_sum, hv, Complex.ofReal_one]
  have hBA : B * A = Matrix.of ![![(1 : ℂ), c], ![-star c, -1]] := by
    ext k₁ k₂
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [A, B, Matrix.mul_apply, Matrix.of_apply]
    fin_cases k₁ <;> fin_cases k₂ <;> simp only [Fin.zero_eta, Fin.mk_one, ↓reduceIte, h10,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · exact hnorm_sum ψ₀ hψ₀
    · rfl
    · simp only [neg_mul, Finset.sum_neg_distrib, c, star_sum, star_mul', star_star]
      congr 1; apply Finset.sum_congr rfl; intro p _; ring
    · simp only [neg_mul, Finset.sum_neg_distrib, hnorm_sum ψ₁ hψ₁]
  let D2 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (Complex.ofReal ∘ fun k : Fin 2 ↦ if k = 0 then r else -r)
  have hD2_herm : D2.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext k; fin_cases k <;> simp
  have hcp_BA : (B * A).charpoly = D2.charpoly := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    rw [hBA, charpoly_diagonal_complex, Fin.prod_univ_two]
    simp only [Function.comp_apply, ↓reduceIte, h10, Complex.ofReal_neg]
    rw [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      ↓reduceIte, h10, h01, zero_sub, map_one, map_neg]
    have hc_mul : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hrC : (r : ℂ) * (r : ℂ) = 1 - c * star c := by
      rw [← Complex.ofReal_mul, ← sq, hr_sq, hc_mul, Complex.ofReal_sub, Complex.ofReal_one]
    have hC : Polynomial.C ((r : ℂ) * (r : ℂ)) = Polynomial.C (1 : ℂ) - Polynomial.C c * Polynomial.C (star c) := by
      rw [hrC, map_sub, map_one, map_mul]
    calc (Polynomial.X - 1) * (Polynomial.X - -1) - -Polynomial.C c * -(-Polynomial.C (star c))
        = Polynomial.X ^ 2 - (Polynomial.C (1 : ℂ) - Polynomial.C c * Polynomial.C (star c)) := by
          simp only [map_one]; ring
      _ = Polynomial.X ^ 2 - Polynomial.C ((r : ℂ) * (r : ℂ)) := by rw [← hC]
      _ = (Polynomial.X - Polynomial.C (r : ℂ)) * (Polynomial.X - -Polynomial.C (r : ℂ)) := by
          simp only [map_mul]; ring
  have hpure_td : traceDist P₀ P₁ = r := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have hcp_syl := charpoly_mul_rect_eq A B
    rw [hAB, hcp_BA] at hcp_syl
    have hsum := spectral_sum_eq_of_charpoly_mul_X_pow (f := fun x : ℝ ↦ max x 0)
      (P₀.isHermitian.sub P₁.isHermitian) hD2_herm hcp_syl (by simp)
    have hD2_sum := spectral_sum_diagonal (f := fun x : ℝ ↦ max x 0)
      (fun k : Fin 2 ↦ if k = 0 then r else -r) hD2_herm (by simp)
    rw [traceDist_eq_hockeyStick_one, hockeyStick_eq_posPartTrace,
      posPartTrace_eq_of_eq _ (P₀.isHermitian.sub P₁.isHermitian) (by simp)]
    unfold posPartTrace
    rw [hsum, hD2_sum, Fin.sum_univ_two]
    simp only [↓reduceIte, h10]
    have hr_nn : 0 ≤ r := Real.sqrt_nonneg _
    rw [max_eq_left hr_nn, max_eq_right (by linarith)]
    ring
  rw [← hc_norm]
  exact hcontr.trans (le_of_eq hpure_td)

end FuchsVanDeGraaf

section VariationalHockeyStick

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Orthogonality of the positive and negative spectral parts: `A_+ A_- = 0`. -/
lemma posPartMat_mul_negPartMat {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    posPartMat hA * negPartMat hA = 0 := by
  unfold posPartMat negPartMat
  set U : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hD : Matrix.diagonal (fun i : d ↦ ((max (hA.eigenvalues i) 0 : ℝ) : ℂ)) *
      Matrix.diagonal (fun i : d ↦ ((max (-hA.eigenvalues i) 0 : ℝ) : ℂ)) = 0 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.zero_apply]
    split_ifs with h
    · subst h
      rw [← Complex.ofReal_mul]
      have h0 : max (hA.eigenvalues i) 0 * max (-hA.eigenvalues i) 0 = 0 := by
        rcases le_total (hA.eigenvalues i) 0 with hle | hge
        · rw [max_eq_right hle, zero_mul]
        · rw [max_eq_right (by linarith : -hA.eigenvalues i ≤ 0), mul_zero]
      rw [h0, Complex.ofReal_zero]
    · rfl
  calc (U * Matrix.diagonal (fun i ↦ ((max (hA.eigenvalues i) 0 : ℝ) : ℂ)) * star U) *
        (U * Matrix.diagonal (fun i ↦ ((max (-hA.eigenvalues i) 0 : ℝ) : ℂ)) * star U)
      = U * (Matrix.diagonal (fun i ↦ ((max (hA.eigenvalues i) 0 : ℝ) : ℂ)) *
          ((star U * U) * Matrix.diagonal (fun i ↦ ((max (-hA.eigenvalues i) 0 : ℝ) : ℂ)))) *
          star U := by simp only [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal (fun i ↦ ((max (hA.eigenvalues i) 0 : ℝ) : ℂ)) *
          Matrix.diagonal (fun i ↦ ((max (-hA.eigenvalues i) 0 : ℝ) : ℂ))) * star U := by
          rw [hU, Matrix.one_mul]
    _ = 0 := by rw [hD, Matrix.mul_zero, Matrix.zero_mul]

/-- Attainment of the variational supremum for the positive spectral trace part:
`Tr(A_+)` is the greatest element of `{ Re Tr(Λ A) : 0 ≼ Λ ≼ I }`. -/
theorem posPartTrace_isGreatest {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    IsGreatest { x : ℝ | ∃ Λ : Matrix d d ℂ, Λ.PosSemidef ∧ (1 - Λ).PosSemidef ∧
      x = ((Λ * A).trace).re } (posPartTrace hA) := by
  set S : Set ℝ := { x : ℝ | ∃ Λ : Matrix d d ℂ, Λ.PosSemidef ∧ (1 - Λ).PosSemidef ∧
    x = ((Λ * A).trace).re }
  set U : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
  let indP : d → ℝ := fun i ↦ if 0 < hA.eigenvalues i then 1 else 0
  let P : Matrix d d ℂ := U * Matrix.diagonal (fun i ↦ (indP i : ℂ)) * star U
  have hP_psd : P.PosSemidef := by
    have hD : (Matrix.diagonal (fun i : d ↦ (indP i : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]; intro i
      simp only [indP]; split_ifs <;> norm_num
    simpa [P, Matrix.star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same U
  have h1mP_psd : (1 - P).PosSemidef := by
    have hD : (Matrix.diagonal (fun i : d ↦ ((1 - indP i : ℝ) : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]; intro i
      simp only [indP]; split_ifs <;> norm_num
    have hEq : 1 - P = U * Matrix.diagonal (fun i ↦ ((1 - indP i : ℝ) : ℂ)) * star U := by
      have h1 : (1 : Matrix d d ℂ) = U * Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) * star U := by
        rw [Matrix.diagonal_one, Matrix.mul_one]
        exact (Unitary.coe_mul_star_self hA.eigenvectorUnitary).symm
      rw [h1]
      simp only [P, ← Matrix.sub_mul, ← Matrix.mul_sub]
      congr 2; ext i j; simp only [Matrix.sub_apply, Matrix.diagonal_apply]
      split_ifs <;> simp
    rw [hEq]
    simpa [Matrix.star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same U
  have hPA : ((P * A).trace).re = posPartTrace hA := by
    have hspec : A = U * Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) * star U := by
      simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
    have hmul : P * A = U * Matrix.diagonal (fun i ↦ ((max (hA.eigenvalues i) 0 : ℝ) : ℂ)) * star U := by
      conv_lhs => rw [hspec]
      simp only [P, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, Unitary.coe_star_mul_self hA.eigenvectorUnitary,
        Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i j
      simp only [Matrix.diagonal_apply, Function.comp_apply, indP]
      split_ifs with hij hpos
      · simp [max_eq_left (le_of_lt hpos)]
      · simp [max_eq_right (le_of_not_gt hpos)]
      · rfl
    rw [hmul, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self hA.eigenvectorUnitary,
      Matrix.one_mul, Matrix.trace_diagonal]
    simp [posPartTrace]
  have hmem : posPartTrace hA ∈ S := ⟨P, hP_psd, h1mP_psd, hPA.symm⟩
  have hbdd : ∀ x ∈ S, x ≤ posPartTrace hA := by
    rintro x ⟨Λ, hΛ, h1Λ, rfl⟩
    have htr1 : ((Λ * A).trace).re =
        ((Λ * posPartMat hA).trace).re - ((Λ * negPartMat hA).trace).re := by
      have hA_eq : A = posPartMat hA - negPartMat hA := (posPartMat_sub_negPartMat hA).symm
      conv_lhs => rw [hA_eq]
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    have hneg_nn : 0 ≤ ((Λ * negPartMat hA).trace).re :=
      re_trace_mul_nonneg_of_posSemidef hΛ (negPartMat_posSemidef hA)
    have hdiff_nn : 0 ≤ (((1 - Λ) * posPartMat hA).trace).re :=
      re_trace_mul_nonneg_of_posSemidef h1Λ (posPartMat_posSemidef hA)
    have hpos_le : ((Λ * posPartMat hA).trace).re ≤ posPartTrace hA := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
        trace_posPartMat hA, Complex.ofReal_re] at hdiff_nn
      linarith
    linarith
  exact ⟨hmem, hbdd⟩

/-- Variational equality for the positive spectral trace part:
`Tr(A_+) = sup { Re Tr(Λ A) : 0 ≼ Λ ≼ I }`. -/
theorem posPartTrace_eq_sSup {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    posPartTrace hA =
      sSup { x : ℝ | ∃ Λ : Matrix d d ℂ, Λ.PosSemidef ∧ (1 - Λ).PosSemidef ∧
        x = ((Λ * A).trace).re } :=
  (posPartTrace_isGreatest hA).csSup_eq.symm

/-- Attainment of the variational form of the hockey-stick divergence (Eq. 2.2):
`E_γ(ρ ‖ σ)` is the greatest element of `{ Re Tr(Λ (ρ - γ σ)) : 0 ≼ Λ ≼ I }`. -/
theorem hockeyStick_isGreatest (γ : ℝ) (ρ σ : DensityOp d) :
    IsGreatest { x : ℝ | ∃ Λ : Matrix d d ℂ, Λ.PosSemidef ∧ (1 - Λ).PosSemidef ∧
      x = ((Λ * (ρ.mat - (γ : ℂ) • σ.mat)).trace).re } (hockeyStick γ ρ σ) := by
  have hA : (ρ.mat - (γ : ℂ) • σ.mat).IsHermitian :=
    ρ.isHermitian.sub (by
      simpa [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def,
        Complex.conj_ofReal] using congr_arg ((γ : ℂ) • ·) σ.isHermitian.eq)
  exact posPartTrace_isGreatest hA

/-- **Eq. (2.2) (Variational Form of Hockey-Stick Divergence)**:
`E_γ(ρ ‖ σ) = sup { Re Tr(Λ (ρ - γ σ)) : 0 ≼ Λ ≼ I }`. -/
theorem hockeyStick_eq_sSup (γ : ℝ) (ρ σ : DensityOp d) :
    hockeyStick γ ρ σ =
      sSup { x : ℝ | ∃ Λ : Matrix d d ℂ, Λ.PosSemidef ∧ (1 - Λ).PosSemidef ∧
        x = ((Λ * (ρ.mat - (γ : ℂ) • σ.mat)).trace).re } :=
  (hockeyStick_isGreatest γ ρ σ).csSup_eq.symm

/-- Von Neumann entropy bounds: `0 ≤ S(ρ) ≤ log₂ |d|` for every density operator on a nonempty
finite-dimensional Hilbert space. -/
theorem vonNeumannEntropy_mem_Icc [Nonempty d] (ρ : DensityOp d) :
    0 ≤ vonNeumannEntropy ρ ∧ vonNeumannEntropy ρ ≤ Real.logb 2 (Fintype.card d) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · unfold vonNeumannEntropy
    apply div_nonneg _ (le_of_lt hlog2)
    apply Finset.sum_nonneg; intro i _
    have hle1 : ρ.eigvals i ≤ 1 := by
      calc ρ.eigvals i ≤ ∑ j : d, ρ.eigvals j :=
            Finset.single_le_sum (fun j _ ↦ ρ.eigvals_nonneg j) (Finset.mem_univ i)
        _ = 1 := ρ.sum_eigvals
    exact Real.negMulLog_nonneg (ρ.eigvals_nonneg i) hle1
  · unfold vonNeumannEntropy Real.logb
    apply div_le_div_of_nonneg_right _ (le_of_lt hlog2)
    have hcard_pos : (0 : ℝ) < (Fintype.card d : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    set c : ℝ := (Fintype.card d : ℝ)⁻¹
    have hc_pos : 0 < c := inv_pos.mpr hcard_pos
    have hpt : ∀ i : d, Real.negMulLog (ρ.eigvals i) ≤
        c - ρ.eigvals i - ρ.eigvals i * Real.log c := by
      intro i
      rcases eq_or_lt_of_le (ρ.eigvals_nonneg i) with h0 | hpos
      · rw [← h0]; simp [Real.negMulLog]; linarith
      · have hlog := Real.log_le_sub_one_of_pos (div_pos hc_pos hpos)
        rw [Real.log_div (ne_of_gt hc_pos) (ne_of_gt hpos)] at hlog
        have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hpos)
        have hdiv : ρ.eigvals i * (c / ρ.eigvals i - 1) = c - ρ.eigvals i := by
          field_simp [ne_of_gt hpos]
        rw [hdiv] at hmul
        unfold Real.negMulLog
        linarith
    calc ∑ i : d, Real.negMulLog (ρ.eigvals i)
        ≤ ∑ i : d, (c - ρ.eigvals i - ρ.eigvals i * Real.log c) :=
          Finset.sum_le_sum fun i _ ↦ hpt i
      _ = (∑ _ : d, c) - (∑ i : d, ρ.eigvals i) - (∑ i : d, ρ.eigvals i) * Real.log c := by
          simp only [Finset.sum_sub_distrib, ← Finset.sum_mul]
      _ = (Fintype.card d : ℝ) * c - 1 - 1 * Real.log c := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ρ.sum_eigvals]
      _ = Real.log (Fintype.card d) := by
          have hmc : (Fintype.card d : ℝ) * c = 1 := mul_inv_cancel₀ (ne_of_gt hcard_pos)
          rw [hmc, one_mul, Real.log_inv]; ring

end VariationalHockeyStick

end PolarCodes
