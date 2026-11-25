/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.HockeyStickMeasure

/-!
# Quantum Jeffreys–Jensen–Shannon Inequality (Proposition 3.3)

This module proves **Proposition 3.3** (`prop_3_3_qjjs_posDef`, `prop_3_3_qjjs`):
`φ(QJS(ρ, σ)) ≤ ¼ (D(ρ ‖ σ) + D(σ ‖ ρ))` for all finite-dimensional density operators `ρ, σ ∈ D(H)`.
-/

open Matrix BigOperators Real MeasureTheory Set Filter
open scoped ComplexOrder ENNReal Topology

namespace PolarCodes

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### Part 6: Proposition 3.3 — Quantum Jeffreys–Jensen–Shannon Inequality -/

/-- **Proposition 3.3 (QJJS, full-rank real form)**: For full-rank `ρ, σ ≻ 0`,
`φ(QJS(ρ, σ)) ≤ ¼ (D(ρ ‖ σ) + D(σ ‖ ρ))`. -/
theorem prop_3_3_qjjs_posDef {ρ σ : DensityOp d} (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    phi (qjs ρ σ) ≤ (1 / 4 : ℝ) * ((relEntropy ρ σ).toReal + (relEntropy σ ρ).toReal) := by
  by_cases hc0 : qjs ρ σ = 0
  · rw [hc0, phi_zero]
    positivity
  have hc_pos : 0 < qjs ρ σ := lt_of_le_of_ne (qjs_eq_half_relEntropy_midpoint hρ hσ).1 (Ne.symm hc0)
  obtain ⟨a, b, μ, ha, hab, hprob, hsupp, _, hmean, hEq34, hEq35, hEq36⟩ :=
    lemma_3_2_hockeyStick_measure hρ hσ
  -- Show `QJS(ρ, σ) < 1` for full-rank `ρ, σ ≻ 0`
  have hc_lt1 : qjs ρ σ < 1 := by
    rw [hEq36]
    have hlt_pt : ∀ t ∈ Icc a b,
        t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t)) < (1 + t) / 2 := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
      have h1 : Real.logb 2 (2 * t / (1 + t)) < 1 := by
        rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity), Real.rpow_one,
          div_lt_iff₀ (by linarith)]
        linarith
      have h2 : Real.logb 2 (2 / (1 + t)) < 1 := by
        rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity), Real.rpow_one,
          div_lt_iff₀ (by linarith)]
        linarith
      nlinarith
    have hI_lhs : Integrable (fun t : ℝ ↦
        t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) μ := by
      have hcont : ContinuousOn (fun t : ℝ ↦
          t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) (Icc a b) := by
        refine ContinuousOn.add ?_ ?_
        · refine (continuousOn_id.div_const 2).mul (ContinuousOn.div_const ?_ _)
          refine Real.continuousOn_log.comp ?_ ?_
          · exact (continuousOn_const.mul continuousOn_id).div (continuousOn_const.add continuousOn_id)
              fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
          · intro t ht; exact ne_of_gt (div_pos (by linarith [lt_of_lt_of_le ha ht.1])
              (by linarith [lt_of_lt_of_le ha ht.1]))
        · refine continuousOn_const.mul (ContinuousOn.div_const ?_ _)
          refine Real.continuousOn_log.comp ?_ ?_
          · exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
              fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
          · intro t ht; exact ne_of_gt (div_pos two_pos (by linarith [lt_of_lt_of_le ha ht.1]))
      obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
      have hm : AEStronglyMeasurable (fun t : ℝ ↦
          t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) μ := by
        have hrest : μ.restrict (Icc a b) = μ := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp)
        rw [← hrest]; exact hcont.aestronglyMeasurable measurableSet_Icc
      refine Integrable.mono' (integrable_const M) hm ?_
      filter_upwards [ae_iff.mpr hsupp] with t ht
      exact hM t ht
    have hI_rhs : Integrable (fun t : ℝ ↦ (1 + t) / 2) μ := by
      have hcont : ContinuousOn (fun t : ℝ ↦ (1 + t) / 2) (Icc a b) := by fun_prop
      obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
      refine Integrable.mono' (integrable_const M) (by fun_prop) ?_
      filter_upwards [ae_iff.mpr hsupp] with t ht
      exact hM t ht
    -- Strict inequality via max gap on compact `[a, b]`
    have hcont_diff : ContinuousOn (fun t : ℝ ↦
        (1 + t) / 2 - (t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t)))) (Icc a b) := by
      refine ContinuousOn.sub (by fun_prop) (ContinuousOn.add ?_ ?_)
      · refine (continuousOn_id.div_const 2).mul (ContinuousOn.div_const ?_ _)
        refine Real.continuousOn_log.comp ?_ ?_
        · exact (continuousOn_const.mul continuousOn_id).div (continuousOn_const.add continuousOn_id)
            fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
        · intro t ht; exact ne_of_gt (div_pos (by linarith [lt_of_lt_of_le ha ht.1])
            (by linarith [lt_of_lt_of_le ha ht.1]))
      · refine continuousOn_const.mul (ContinuousOn.div_const ?_ _)
        refine Real.continuousOn_log.comp ?_ ?_
        · exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
            fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
        · intro t ht; exact ne_of_gt (div_pos two_pos (by linarith [lt_of_lt_of_le ha ht.1]))
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, left_mem_Icc.mpr hab⟩ hcont_diff
    set δ := (1 + t₀) / 2 - (t₀ / 2 * Real.logb 2 (2 * t₀ / (1 + t₀)) + 1 / 2 * Real.logb 2 (2 / (1 + t₀)))
    have hδ_pos : 0 < δ := sub_pos.mpr (hlt_pt t₀ ht₀)
    have hint_le : ∫ t, (t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) ∂μ ≤
        ∫ t, ((1 + t) / 2 - δ) ∂μ := by
      apply integral_mono_ae hI_lhs (hI_rhs.sub (integrable_const δ))
      filter_upwards [ae_iff.mpr hsupp] with t ht
      linarith [hmin ht]
    have hrhs_val : ∫ t, ((1 + t) / 2 - δ) ∂μ = 1 - δ := by
      have h1 : ∫ t, ((1 + t) / 2) ∂μ = 1 := by
        have hint_t : Integrable (fun t : ℝ ↦ t) μ := by
          refine Integrable.mono' (integrable_const b) (continuous_id : Continuous (fun t : ℝ ↦ t)).aestronglyMeasurable ?_
          filter_upwards [ae_iff.mpr hsupp] with t ht
          rw [Real.norm_of_nonneg (by linarith [ht.1])]; exact ht.2
        rw [integral_div, integral_add (integrable_const 1) hint_t, integral_const, smul_eq_mul,
          hmean, show μ.real univ = 1 by simp [Measure.real]]
        ring
      rw [integral_sub hI_rhs (integrable_const δ), h1, integral_const, smul_eq_mul,
        show μ.real univ = 1 by simp [Measure.real], one_mul]
    linarith
  -- Let `x = 1 - 2 h₂⁻¹(1 - QJS(ρ, σ)) ∈ (0, 1)`
  let c := qjs ρ σ
  let x := 1 - 2 * h2Inv (1 - c)
  have h1mc0 : 0 < 1 - c := by linarith
  have h1mc1 : 1 - c < 1 := by linarith
  have hinv_mem := h2Inv_mem_Icc (le_of_lt h1mc0) (le_of_lt h1mc1)
  have hinv_pos : 0 < h2Inv (1 - c) := by
    by_contra h0; push Not at h0
    have heq0 : h2Inv (1 - c) = 0 := le_antisymm h0 hinv_mem.1
    have := h2_h2Inv (le_of_lt h1mc0) (le_of_lt h1mc1)
    rw [heq0, h2_zero] at this; linarith
  have hinv_lt : h2Inv (1 - c) < 1 / 2 := by
    by_contra h1; push Not at h1
    have heq : h2Inv (1 - c) = 1 / 2 := le_antisymm hinv_mem.2 h1
    have := h2_h2Inv (le_of_lt h1mc0) (le_of_lt h1mc1)
    rw [heq, h2_half] at this; linarith
  have hx0 : 0 < x := by simp only [x]; linarith
  have hx1 : x < 1 := by simp only [x]; linarith
  have hcx : cParam x = c := by
    simp only [cParam, x]
    have : (1 - (1 - 2 * h2Inv (1 - c))) / 2 = h2Inv (1 - c) := by ring
    rw [this, h2_h2Inv (le_of_lt h1mc0) (le_of_lt h1mc1)]; ring
  have hphi_eq : phi c = phiParam x := by
    unfold phi; simp only [x]
  -- Integrate `gx x t ≥ 0` (Lemma 3.1) against `μ`
  have hgx_nn : 0 ≤ ∫ t, gx x t ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_iff.mpr hsupp] with t ht
    exact lemma_3_1_gx_nonneg hx0 hx1 (lt_of_lt_of_le ha ht.1)
  -- Express `∫ gx x t ∂μ` in terms of `D(ρ‖σ)`, `D(σ‖ρ)`, `QJS(ρ, σ)`
  have hint_of_cont : ∀ (ψ : ℝ → ℝ), ContinuousOn ψ (Icc a b) → Integrable ψ μ := by
    intro ψ hψ
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ
    have hm : AEStronglyMeasurable ψ μ := by
      have hrest : μ.restrict (Icc a b) = μ := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp)
      rw [← hrest]; exact hψ.aestronglyMeasurable measurableSet_Icc
    refine Integrable.mono' (integrable_const M) hm ?_
    filter_upwards [ae_iff.mpr hsupp] with t ht
    exact hM t ht
  have hI1 : Integrable (fun t : ℝ ↦ (1 / 4 : ℝ) * (t - 1) * Real.logb 2 t) μ :=
    hint_of_cont _ ((continuousOn_const.mul (continuousOn_id.sub continuousOn_const)).mul
      (ContinuousOn.div_const (Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (lt_of_lt_of_le ha ht.1)) _))
  have hI2 : Integrable (fun t : ℝ ↦
      phiDerivParam x * (t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t)))) μ := by
    apply (hint_of_cont _ _).const_mul
    refine ContinuousOn.add ?_ ?_
    · refine (continuousOn_id.div_const 2).mul (ContinuousOn.div_const ?_ _)
      refine Real.continuousOn_log.comp ?_ ?_
      · exact (continuousOn_const.mul continuousOn_id).div (continuousOn_const.add continuousOn_id)
          fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
      · intro t ht; exact ne_of_gt (div_pos (by linarith [lt_of_lt_of_le ha ht.1])
          (by linarith [lt_of_lt_of_le ha ht.1]))
    · refine continuousOn_const.mul (ContinuousOn.div_const ?_ _)
      refine Real.continuousOn_log.comp ?_ ?_
      · exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
          fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
      · intro t ht; exact ne_of_gt (div_pos two_pos (by linarith [lt_of_lt_of_le ha ht.1]))
  have hI3 : Integrable (fun t : ℝ ↦ betaParam x * ((1 + t) / 2)) μ :=
    hint_of_cont _ (by fun_prop)
  have hgx_split : ∫ t, gx x t ∂μ =
      (∫ t, (1 / 4 : ℝ) * (t - 1) * Real.logb 2 t ∂μ) -
      phiDerivParam x * (∫ t, (t / 2 * Real.logb 2 (2 * t / (1 + t)) +
        1 / 2 * Real.logb 2 (2 / (1 + t))) ∂μ) +
      betaParam x * (∫ t, (1 + t) / 2 ∂μ) := by
    unfold gx
    rw [integral_add (hI1.sub hI2) hI3, integral_sub hI1 hI2, integral_const_mul, integral_const_mul]
  have hJ : ∫ t, (1 / 4 : ℝ) * (t - 1) * Real.logb 2 t ∂μ =
      (1 / 4 : ℝ) * ((relEntropy ρ σ).toReal + (relEntropy σ ρ).toReal) := by
    rw [hEq34, hEq35]
    have hIa : Integrable (fun t : ℝ ↦ t * Real.logb 2 t - (t - 1) / Real.log 2) μ :=
      hint_of_cont _ ((continuousOn_id.mul (ContinuousOn.div_const
        (Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (lt_of_lt_of_le ha ht.1)) _)).sub (by fun_prop))
    have hIb : Integrable (fun t : ℝ ↦ -Real.logb 2 t + (t - 1) / Real.log 2) μ :=
      hint_of_cont _ (((ContinuousOn.div_const
        (Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (lt_of_lt_of_le ha ht.1)) _).neg).add (by fun_prop))
    rw [← integral_add hIa hIb, ← integral_const_mul]
    apply integral_congr_ae; filter_upwards with t; ring
  have hhalf_mean : ∫ t, (1 + t) / 2 ∂μ = 1 := by
    have hint_t : Integrable (fun t : ℝ ↦ t) μ := hint_of_cont _ continuousOn_id
    rw [integral_div, integral_add (integrable_const 1) hint_t, integral_const, smul_eq_mul,
      hmean, show μ.real univ = 1 by simp [Measure.real]]
    ring
  rw [hgx_split, hJ, ← hEq36, hhalf_mean, mul_one] at hgx_nn
  have hbeta : phiDerivParam x * c - betaParam x = phi c := by
    rw [hphi_eq, ← hcx]; unfold betaParam; ring
  linarith

/-- Support inclusion `suppSubset ρ σ` implies `ker σ ⊆ ker ρ`. -/
private lemma suppSubset_ker {ρ σ : DensityOp d} (hsupp : suppSubset ρ σ)
    (v : d → ℂ) (hσv : σ.mat.mulVec v = 0) : ρ.mat.mulVec v = 0 := by
  set Uρ : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
  set Uσ : Matrix d d ℂ := (σ.eigUnitary : Matrix d d ℂ)
  have hspecρ : ρ.mat = Uρ * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star Uρ := by
    simpa [Uρ, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
  have hspecσ : σ.mat = Uσ * Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) * star Uσ := by
    simpa [Uσ, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
  set y : d → ℂ := (star Uσ).mulVec v
  have hy : ∀ j : d, σ.eigvals j ≠ 0 → y j = 0 := by
    intro j hj
    have h1 := congr_arg (fun w ↦ ((star Uσ).mulVec w) j) hσv
    have hL : ((star Uσ).mulVec (σ.mat.mulVec v)) j = (σ.eigvals j : ℂ) * y j := by
      conv_lhs => rw [hspecσ]
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc (star Uσ), ← Matrix.mul_assoc (star Uσ),
        Unitary.coe_star_mul_self σ.eigUnitary, Matrix.one_mul, Matrix.mulVec_mulVec,
        Matrix.mulVec_diagonal]; rfl
    rw [hL, Matrix.mulVec_zero, Pi.zero_apply] at h1
    have hne : (σ.eigvals j : ℂ) ≠ 0 := by exact_mod_cast hj
    exact (mul_eq_zero.mp h1).resolve_left hne
  have hzero : (fun i : d ↦ (Complex.ofReal ∘ ρ.eigvals) i * ((star Uρ).mulVec v) i) = 0 := by
    ext i; simp only [Function.comp_apply, Pi.zero_apply]
    by_cases hρi : ρ.eigvals i = 0
    · simp [hρi]
    · suffices ((star Uρ).mulVec v) i = 0 by simp [this]
      have hv : v = Uσ.mulVec y := by
        simp only [y, Matrix.mulVec_mulVec, Unitary.coe_mul_star_self σ.eigUnitary, Matrix.one_mulVec]
      rw [hv, Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero; intro j _
      by_cases hσj : σ.eigvals j = 0
      · have hW := hsupp i j hρi hσj
        have hW' : (star Uρ * Uσ) i j = 0 := by
          have hstar : star (star Uσ * Uρ) = star Uρ * Uσ := by
            simp [Matrix.star_mul, star_star]
          have hji := congr_fun (congr_fun hstar i) j
          simp only [Matrix.star_apply] at hji
          rw [← hji, hW, star_zero]
        rw [hW', zero_mul]
      · rw [hy j hσj, mul_zero]
  conv_lhs => rw [hspecρ]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, hzero, Matrix.mulVec_zero]

private lemma relEntropy_sum_split {α : Type*} [Fintype α] [DecidableEq α] (A B : DensityOp α) :
    (∑ i : α, ∑ j : α,
      ‖((star (B.eigUnitary : Matrix α α ℂ)) * (A.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 *
        (A.eigvals i * (Real.log (A.eigvals i) - Real.log (B.eigvals j)))) =
    (∑ i : α, A.eigvals i * Real.log (A.eigvals i)) -
    (∑ i : α, ∑ j : α, A.eigvals i * Real.log (B.eigvals j) *
      ‖((star (B.eigUnitary : Matrix α α ℂ)) * (A.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2) := by
  set W : Matrix α α ℂ := star (B.eigUnitary : Matrix α α ℂ) * (A.eigUnitary : Matrix α α ℂ)
  have hcol1 : ∀ i : α, ∑ j : α, ‖W j i‖ ^ 2 = 1 := by
    intro i
    have hB : (B.eigUnitary : Matrix α α ℂ) * star (B.eigUnitary : Matrix α α ℂ) = 1 :=
      Unitary.coe_mul_star_self B.eigUnitary
    have hA : star (A.eigUnitary : Matrix α α ℂ) * (A.eigUnitary : Matrix α α ℂ) = 1 :=
      Unitary.coe_star_mul_self A.eigUnitary
    have hU : star W * W = 1 := by
      simp only [W, Matrix.star_mul, star_star, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (B.eigUnitary : Matrix α α ℂ), hB, Matrix.one_mul, hA]
    have hii := congr_arg Complex.re (congr_fun (congr_fun hU i) i)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re,
      Complex.re_sum] at hii
    rw [← hii]
    apply Finset.sum_congr rfl; intro j _
    have hsq : star (W j i) * W j i = ((‖W j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hsq, Complex.ofReal_re]
  have hrew : (∑ i : α, ∑ j : α, ‖W j i‖ ^ 2 * (A.eigvals i * (Real.log (A.eigvals i) - Real.log (B.eigvals j)))) =
      ∑ i : α, ((∑ j : α, ‖W j i‖ ^ 2) * (A.eigvals i * Real.log (A.eigvals i)) -
        ∑ j : α, A.eigvals i * Real.log (B.eigvals j) * ‖W j i‖ ^ 2) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hrew, Finset.sum_sub_distrib]
  congr 1; apply Finset.sum_congr rfl; intro i _; rw [hcol1 i, one_mul]

private lemma relEntropy_cross_eq_trace_log {α : Type*} [Fintype α] [DecidableEq α] (A B : DensityOp α) :
    (∑ i : α, ∑ j : α, A.eigvals i * Real.log (B.eigvals j) *
      ‖((star (B.eigUnitary : Matrix α α ℂ)) * (A.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2) =
    (A.mat * ((B.eigUnitary : Matrix α α ℂ) *
      Matrix.diagonal (fun j ↦ (Real.log (B.eigvals j) : ℂ)) *
      star (B.eigUnitary : Matrix α α ℂ))).trace.re := by
  set UA : Matrix α α ℂ := (A.eigUnitary : Matrix α α ℂ)
  set UB : Matrix α α ℂ := (B.eigUnitary : Matrix α α ℂ)
  have hspecA : A.mat = UA * Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * star UA := by
    simpa [UA, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using A.isHermitian.spectral_theorem
  set W : Matrix α α ℂ := star UB * UA
  have htrC : (A.mat * (UB * Matrix.diagonal (fun j ↦ (Real.log (B.eigvals j) : ℂ)) * star UB)).trace =
      (Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *
        (star W * Matrix.diagonal (fun j ↦ (Real.log (B.eigvals j) : ℂ)) * W)).trace := by
    conv_lhs => rw [hspecA]
    have hstarW : star W = star UA * UB := by
      simp [W, Matrix.star_mul, star_star]
    rw [hstarW]
    calc (UA * Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * star UA *
            (UB * Matrix.diagonal (fun j ↦ (Real.log (B.eigvals j) : ℂ)) * star UB)).trace
        = (Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *
            (star UA * UB * Matrix.diagonal (fun j ↦ (Real.log (B.eigvals j) : ℂ)) * (star UB * UA))).trace := by
          rw [Matrix.trace_mul_comm UA]; simp only [Matrix.mul_assoc]
      _ = _ := rfl
  rw [htrC]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
    Function.comp_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro j _
  have hsq : (star (W j i) * W j i) = ((‖W j i‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcalc : (A.eigvals i : ℂ) * (star (W j i) * (Real.log (B.eigvals j) : ℂ) * W j i) =
      ((A.eigvals i * Real.log (B.eigvals j) * ‖W j i‖ ^ 2 : ℝ) : ℂ) := by
    calc _ = (A.eigvals i : ℂ) * (Real.log (B.eigvals j) : ℂ) * (star (W j i) * W j i) := by ring
      _ = _ := by rw [hsq]; push_cast; ring
  simp only [Matrix.star_apply]
  rw [hcalc, Complex.ofReal_re]

/-- **Proposition 3.3 (Quantum Jeffreys–Jensen–Shannon Inequality)** for ALL density operators
`ρ, σ ∈ D(H)`: `φ(QJS(ρ, σ)) ≤ ¼ (D(ρ ‖ σ) + D(σ ‖ ρ))`. -/
theorem prop_3_3_qjjs (ρ σ : DensityOp d) :
    phiExt (qjs ρ σ) ≤ (1 / 4 : ℝ≥0∞) * (relEntropy ρ σ + relEntropy σ ρ) := by
  by_cases hsupp : suppSubset ρ σ ∧ suppSubset σ ρ
  · -- Restrict to the common support `S_pos = {i : d | 0 < ρ.eigvals i}`
    -- On `S_pos`, both `ρ` and `σ` are strictly positive definite (`PosDef`)!
    set S_pos : Finset d := Finset.univ.filter fun i : d ↦ 0 < ρ.eigvals i
    let d' := {i : d // i ∈ S_pos}
    set U : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
    let V : Matrix d d' ℂ := Matrix.of fun r k ↦ U r k.1
    have hVHV : Vᴴ * V = 1 := by
      ext j k
      simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
      have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) j.1) k.1
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h
      convert h using 1
      simp [Subtype.ext_iff]
    -- Helper: `ρ` vanishes on columns of `U` outside `S_pos`
    have hρ_ker : ∀ i : d, i ∉ S_pos → ρ.mat.mulVec (fun r ↦ U r i) = 0 := by
      intro i hi
      have h0 : ρ.eigvals i = 0 := by
        have hle : ρ.eigvals i ≤ 0 := by simp [S_pos] at hi; exact hi
        exact le_antisymm hle (ρ.eigvals_nonneg i)
      have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by
        simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
      have hcol : (star U).mulVec (fun r ↦ U r i) = Pi.single i 1 := by
        ext j
        have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) j) i
        simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
          Pi.single_apply, eq_comm] using h
      conv_lhs => rw [hspec]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcol, Matrix.mulVec_diagonal]
      have hzero : (fun j : d ↦ (Complex.ofReal ∘ ρ.eigvals) j * Pi.single i 1 j) = 0 := by
        ext j; by_cases hj : j = i
        · subst hj; simp [h0]
        · simp [Pi.single_eq_of_ne hj]
      rw [hzero, Matrix.mulVec_zero]
    have hσ_ker : ∀ i : d, i ∉ S_pos → σ.mat.mulVec (fun r ↦ U r i) = 0 := by
      intro i hi
      exact suppSubset_ker hsupp.2 (fun r ↦ U r i) (hρ_ker i hi)
    -- Projected density operators `ρ' = Vᴴ ρ V` and `σ' = Vᴴ σ V` on `d'`
    have hρ'_mat : Vᴴ * ρ.mat * V = Matrix.diagonal (fun k : d' ↦ (ρ.eigvals k.1 : ℂ)) := by
      have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by
        simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
      ext j k
      have hmul : Vᴴ * U = Matrix.of fun (a : d') (b : d) ↦ if a.1 = b then (1 : ℂ) else 0 := by
        ext a b
        have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) a.1) b
        simpa [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.star_apply, Matrix.of_apply,
          Matrix.one_apply] using h
      have hmul2 : star U * V = Matrix.of fun (a : d) (b : d') ↦ if a = b.1 then (1 : ℂ) else 0 := by
        ext a b
        have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) a) b.1
        simpa [V, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply] using h
      have hcalc : Vᴴ * ρ.mat * V =
          (Vᴴ * U) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * (star U * V) := by
        conv_lhs => rw [hspec]
        simp only [Matrix.mul_assoc]
      rw [hcalc, hmul, hmul2]
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, Function.comp_apply,
        ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ↓reduceIte, Finset.sum_ite_eq', Subtype.ext_iff]
      split_ifs <;> simp_all
    let ρ' : DensityOp d' :=
      { mat := Vᴴ * ρ.mat * V
        posSemidef := by
          simpa [Matrix.conjTranspose_conjTranspose] using ρ.posSemidef.mul_mul_conjTranspose_same Vᴴ
        trace_one := by
          rw [hρ'_mat, Matrix.trace_diagonal]
          have htr : ρ.mat.trace = ∑ i : d, (ρ.eigvals i : ℂ) := by
            have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by
              simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
                Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
            conv_lhs => rw [hspec]
            rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self ρ.eigUnitary, Matrix.one_mul,
              Matrix.trace_diagonal]; rfl
          rw [← ρ.trace_one, htr, Finset.sum_coe_sort S_pos (fun i ↦ (ρ.eigvals i : ℂ))]
          symm
          apply Finset.sum_subset (Finset.subset_univ S_pos)
          intro i _ hi
          have hle : ρ.eigvals i ≤ 0 := by simp [S_pos] at hi; exact hi
          simp [le_antisymm hle (ρ.eigvals_nonneg i)] }
    have hρ'_pd : ρ'.mat.PosDef := by
      simp only [ρ', hρ'_mat, Matrix.posDef_diagonal_iff]
      intro k
      have hk : 0 < ρ.eigvals k.1 := (Finset.mem_filter.mp k.2).2
      exact_mod_cast hk
    -- `V * Vᴴ` is the projection onto `supp(ρ)`, and `V * Vᴴ * σ * V * Vᴴ = σ`
    have hVVH_σ : (V * Vᴴ) * σ.mat = σ.mat := by
      -- Check on columns of `U` (which form a unitary basis)
      have hU_eq : ((V * Vᴴ) * σ.mat) * U = σ.mat * U := by
        ext r i
        simp only [Matrix.mul_apply]
        have hσUi : (σ.mat * U) r i = (σ.mat.mulVec (fun x ↦ U x i)) r := rfl
        have hVVH_apply : ∀ (v : d → ℂ) (x : d), ((V * Vᴴ).mulVec v) x =
            ∑ k : d', U x k.1 * (∑ y : d, star (U y k.1) * v y) := by
          intro v x
          simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, V, Matrix.conjTranspose_apply,
            Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro y _; ring
        have hLHS : ∑ y : d, (∑ z : d, (V * Vᴴ) r z * σ.mat z y) * U y i =
            ((V * Vᴴ).mulVec (σ.mat.mulVec (fun x ↦ U x i))) r := by
          simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro z _; apply Finset.sum_congr rfl; intro y _; ring
        rw [hLHS]
        -- Expand `σ (U e_i)` in the basis `U`: its coefficient along `U e_j` for `j ∉ S_pos` is 0!
        have horth : ∀ j : d, j ∉ S_pos →
            ∑ y : d, star (U y j) * (σ.mat.mulVec (fun x ↦ U x i)) y = 0 := by
          intro j hj
          have hsym : ∑ y : d, star (U y j) * (σ.mat.mulVec (fun x ↦ U x i)) y =
              star (∑ x : d, star (U x i) * (σ.mat.mulVec (fun y ↦ U y j)) x) := by
            simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', star_star, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y _; apply Finset.sum_congr rfl; intro x _
            have hh := congr_fun (congr_fun σ.isHermitian.eq x) y
            simp only [Matrix.conjTranspose_apply] at hh
            rw [hh]; ring
          rw [hsym, hσ_ker j hj]; simp
        rw [hVVH_apply]
        have hfull : (σ.mat.mulVec (fun x ↦ U x i)) r =
            ∑ j : d, U r j * (∑ y : d, star (U y j) * (σ.mat.mulVec (fun x ↦ U x i)) y) := by
          calc (σ.mat.mulVec (fun x ↦ U x i)) r
              = ((U * star U).mulVec (σ.mat.mulVec (fun x ↦ U x i))) r := by
                rw [Unitary.coe_mul_star_self ρ.eigUnitary, Matrix.one_mulVec]
            _ = _ := by
                simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
                  Finset.sum_mul, Finset.mul_sum]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro y _; ring
        rw [hfull, Finset.sum_coe_sort S_pos (fun j ↦ U r j * (∑ y : d, star (U y j) * (σ.mat.mulVec (fun x ↦ U x i)) y))]
        symm
        apply Finset.sum_subset (Finset.subset_univ S_pos)
        intro j _ hj; rw [horth j hj, mul_zero]
      calc (V * Vᴴ) * σ.mat = ((V * Vᴴ) * σ.mat * U) * star U := by
            rw [Matrix.mul_assoc, Unitary.coe_mul_star_self ρ.eigUnitary, Matrix.mul_one]
        _ = (σ.mat * U) * star U := by rw [hU_eq]
        _ = σ.mat := by rw [Matrix.mul_assoc, Unitary.coe_mul_star_self ρ.eigUnitary, Matrix.mul_one]
    have hσ_VVH : σ.mat * (V * Vᴴ) = σ.mat := by
      have h := congr_arg Matrix.conjTranspose hVVH_σ
      simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, σ.isHermitian.eq] using h
    let σ' : DensityOp d' :=
      { mat := Vᴴ * σ.mat * V
        posSemidef := by
          simpa [Matrix.conjTranspose_conjTranspose] using σ.posSemidef.mul_mul_conjTranspose_same Vᴴ
        trace_one := by
          calc (Vᴴ * σ.mat * V).trace = ((V * Vᴴ) * σ.mat).trace := by
                rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
            _ = σ.mat.trace := by rw [hVVH_σ]
            _ = 1 := σ.trace_one }
    have hσ'_pd : σ'.mat.PosDef := by
      rw [Matrix.posDef_iff_dotProduct_mulVec]
      refine ⟨σ'.isHermitian, fun w hw ↦ ?_⟩
      have hVw_ne : V.mulVec w ≠ 0 := by
        intro h0; apply hw
        have := congr_arg Vᴴ.mulVec h0
        rw [Matrix.mulVec_mulVec, hVHV, Matrix.one_mulVec, Matrix.mulVec_zero] at this
        exact this
      have hρ_pos : (0 : ℂ) < star (V.mulVec w) ⬝ᵥ ρ.mat.mulVec (V.mulVec w) := by
        have hq : star (V.mulVec w) ⬝ᵥ ρ.mat.mulVec (V.mulVec w) = star w ⬝ᵥ ρ'.mat.mulVec w := by
          simp only [ρ', Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
          congr 1; ext j
          simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply,
            Matrix.conjTranspose_apply, star_sum, star_mul', star_star]
          apply Finset.sum_congr rfl; intro i _; ring
        rw [hq]; exact (Matrix.posDef_iff_dotProduct_mulVec.mp hρ'_pd).2 hw
      have hσ_ne : σ.mat.mulVec (V.mulVec w) ≠ 0 := by
        intro h0
        have hρ0 := suppSubset_ker hsupp.1 (V.mulVec w) h0
        rw [hρ0, dotProduct_zero] at hρ_pos
        exact lt_irrefl 0 hρ_pos
      have hqσ : star w ⬝ᵥ σ'.mat.mulVec w = star (V.mulVec w) ⬝ᵥ σ.mat.mulVec (V.mulVec w) := by
        simp only [σ', Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
        congr 1; ext j
        simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply,
          Matrix.conjTranspose_apply, star_sum, star_mul', star_star]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hqσ]
      have hnn := (Matrix.posSemidef_iff_dotProduct_mulVec.mp σ.posSemidef).2 (V.mulVec w)
      rcases lt_or_eq_of_le hnn with hlt | heq
      · exact hlt
      · exfalso; apply hσ_ne
        -- If `⟨v, σ v⟩ = 0` for `σ ≽ 0`, then `σ v = 0`
        have hre0 := congr_arg Complex.re heq.symm
        rw [re_quadForm_spectral σ.isHermitian (V.mulVec w), Complex.zero_re] at hre0
        have hterm0 : ∀ i : d, σ.isHermitian.eigenvalues i *
            ‖((star (σ.isHermitian.eigenvectorUnitary : Matrix d d ℂ)).mulVec (V.mulVec w)) i‖ ^ 2 = 0 := by
          intro i
          exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
            mul_nonneg (σ.posSemidef.eigenvalues_nonneg j) (sq_nonneg _)).mp hre0 i (Finset.mem_univ i)
        have hspec : σ.mat = (σ.isHermitian.eigenvectorUnitary : Matrix d d ℂ) *
            Matrix.diagonal (Complex.ofReal ∘ σ.isHermitian.eigenvalues) *
            star (σ.isHermitian.eigenvectorUnitary : Matrix d d ℂ) := by
          simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
        conv_lhs => rw [hspec]
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
        have hzero : (fun i : d ↦ (Complex.ofReal ∘ σ.isHermitian.eigenvalues) i *
            ((star (σ.isHermitian.eigenvectorUnitary : Matrix d d ℂ)).mulVec (V.mulVec w)) i) = 0 := by
          ext i
          rcases mul_eq_zero.mp (hterm0 i) with h1 | h2
          · simp [h1]
          · simp [norm_eq_zero.mp (sq_eq_zero_iff.mp h2)]
        rw [hzero, Matrix.mulVec_zero]
    -- `V * ρ' * Vᴴ = ρ`, `V * σ' * Vᴴ = σ`, so `relEntropy` and `qjs` agree!
    have hVρ'VH : V * ρ'.mat * Vᴴ = ρ.mat := by
      have hVVH_ρ : (V * Vᴴ) * ρ.mat = ρ.mat := by
        have hU_eq : ((V * Vᴴ) * ρ.mat) * U = ρ.mat * U := by
          ext r i
          have hLHS : ((V * Vᴴ) * ρ.mat * U) r i =
              ((V * Vᴴ).mulVec (ρ.mat.mulVec (fun x ↦ U x i))) r := by
            simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro z _; apply Finset.sum_congr rfl; intro y _; ring
          rw [hLHS]
          have hVVH_apply : ∀ (v : d → ℂ) (x : d), ((V * Vᴴ).mulVec v) x =
              ∑ k : d', U x k.1 * (∑ y : d, star (U y k.1) * v y) := by
            intro v x
            simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, V, Matrix.conjTranspose_apply,
              Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro y _; ring
          rw [hVVH_apply]
          have horth : ∀ j : d, j ∉ S_pos →
              ∑ y : d, star (U y j) * (ρ.mat.mulVec (fun x ↦ U x i)) y = 0 := by
            intro j hj
            have hsym : ∑ y : d, star (U y j) * (ρ.mat.mulVec (fun x ↦ U x i)) y =
                star (∑ x : d, star (U x i) * (ρ.mat.mulVec (fun y ↦ U y j)) x) := by
              simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', star_star, Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro y _; apply Finset.sum_congr rfl; intro x _
              have hh := congr_fun (congr_fun ρ.isHermitian.eq x) y
              simp only [Matrix.conjTranspose_apply] at hh
              rw [hh]; ring
            rw [hsym, hρ_ker j hj]; simp
          have hfull : (ρ.mat * U) r i =
              ∑ j : d, U r j * (∑ y : d, star (U y j) * (ρ.mat.mulVec (fun x ↦ U x i)) y) := by
            calc (ρ.mat * U) r i
                = ((U * star U).mulVec (ρ.mat.mulVec (fun x ↦ U x i))) r := by
                  rw [Unitary.coe_mul_star_self ρ.eigUnitary, Matrix.one_mulVec]; rfl
              _ = _ := by
                  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
                    Finset.sum_mul, Finset.mul_sum]
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro y _; ring
          rw [hfull, Finset.sum_coe_sort S_pos (fun j ↦ U r j * (∑ y : d, star (U y j) * (ρ.mat.mulVec (fun x ↦ U x i)) y))]
          symm
          apply Finset.sum_subset (Finset.subset_univ S_pos)
          intro j _ hj; rw [horth j hj, mul_zero]
        calc (V * Vᴴ) * ρ.mat = ((V * Vᴴ) * ρ.mat * U) * star U := by
              rw [Matrix.mul_assoc, Unitary.coe_mul_star_self ρ.eigUnitary, Matrix.mul_one]
          _ = (ρ.mat * U) * star U := by rw [hU_eq]
          _ = ρ.mat := by rw [Matrix.mul_assoc, Unitary.coe_mul_star_self ρ.eigUnitary, Matrix.mul_one]
      have hρ_VVH : ρ.mat * (V * Vᴴ) = ρ.mat := by
        have h := congr_arg Matrix.conjTranspose hVVH_ρ
        simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ρ.isHermitian.eq] using h
      calc V * ρ'.mat * Vᴴ = ((V * Vᴴ) * ρ.mat) * (V * Vᴴ) := by simp only [ρ', Matrix.mul_assoc]
        _ = ρ.mat := by rw [hVVH_ρ, hρ_VVH]
    have hVσ'VH : V * σ'.mat * Vᴴ = σ.mat := by
      calc V * σ'.mat * Vᴴ = ((V * Vᴴ) * σ.mat) * (V * Vᴴ) := by simp only [σ', Matrix.mul_assoc]
        _ = σ.mat := by rw [hVVH_σ, hσ_VVH]
    -- Isometric embedding `τ' ↦ V τ' Vᴴ` preserves `vonNeumannEntropy`, `qjs`, and `relEntropy`
    have hS_iso : ∀ (τ' : DensityOp d') (τ : DensityOp d), V * τ'.mat * Vᴴ = τ.mat →
        vonNeumannEntropy τ = vonNeumannEntropy τ' := by
      intro τ' τ hmat
      unfold vonNeumannEntropy DensityOp.eigvals
      congr 1
      let A : Matrix d d' ℂ := V * τ'.sqrtMat
      have hAAH : A * Aᴴ = τ.mat := by
        calc A * Aᴴ = V * (τ'.sqrtMat * τ'.sqrtMat) * Vᴴ := by
              simp only [A, Matrix.conjTranspose_mul, τ'.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
          _ = V * τ'.mat * Vᴴ := by rw [τ'.sqrtMat_mul_self]
          _ = τ.mat := hmat
      have hAHA : Aᴴ * A = τ'.mat := by
        calc Aᴴ * A = τ'.sqrtMat * ((Vᴴ * V) * τ'.sqrtMat) := by
              simp only [A, Matrix.conjTranspose_mul, τ'.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
          _ = τ'.mat := by rw [hVHV, Matrix.one_mul, τ'.sqrtMat_mul_self]
      have hcp := charpoly_mul_conjTranspose_eq A
      rw [hAAH, hAHA] at hcp
      exact spectral_sum_eq_of_charpoly_mul_X_pow τ.isHermitian τ'.isHermitian hcp
        (by simp [Real.negMulLog])
    have hqjs_eq : qjs ρ σ = qjs ρ' σ' := by
      unfold qjs
      rw [hS_iso ρ' ρ hVρ'VH, hS_iso σ' σ hVσ'VH]
      have hmid : V * (DensityOp.midpoint ρ' σ').mat * Vᴴ = (DensityOp.midpoint ρ σ).mat := by
        simp only [DensityOp.midpoint, DensityOp.mix, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_smul, Matrix.smul_mul, hVρ'VH, hVσ'VH]
      rw [hS_iso (DensityOp.midpoint ρ' σ') (DensityOp.midpoint ρ σ) hmid]
    -- Show `relEntropy ρ σ = relEntropy ρ' σ'` and `relEntropy σ ρ = relEntropy σ' ρ'`
    -- via `relEntropy_eq_frenkel`? Even simpler: directly from `relEntropy` definition!
    have hD_iso : ∀ (τ₁' τ₂' : DensityOp d') (τ₁ τ₂ : DensityOp d),
        τ₁'.mat.PosDef → τ₂'.mat.PosDef →
        V * τ₁'.mat * Vᴴ = τ₁.mat → V * τ₂'.mat * Vᴴ = τ₂.mat →
        suppSubset τ₁ τ₂ →
        relEntropy τ₁ τ₂ = relEntropy τ₁' τ₂' := by
      intro τ₁' τ₂' τ₁ τ₂ h1pd h2pd hm1 hm2 hsup
      unfold relEntropy
      have hsup' : suppSubset τ₁' τ₂' := fun _ j _ hj ↦ absurd hj (ne_of_gt (h2pd.eigenvalues_pos j))
      simp only [hsup, hsup', ↓reduceIte]
      congr 1; congr 1
      rw [relEntropy_sum_split τ₁ τ₂, relEntropy_sum_split τ₁' τ₂']
      have hterm1 : (∑ i : d, τ₁.eigvals i * Real.log (τ₁.eigvals i)) =
          ∑ k : d', τ₁'.eigvals k * Real.log (τ₁'.eigvals k) := by
        have hS := hS_iso τ₁' τ₁ hm1
        unfold vonNeumannEntropy Real.negMulLog at hS
        have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
        have hS' : ∑ i : d, -(τ₁.eigvals i * Real.log (τ₁.eigvals i)) =
            ∑ k : d', -(τ₁'.eigvals k * Real.log (τ₁'.eigvals k)) := by
          field_simp [hlog2] at hS; linarith
        simp only [Finset.sum_neg_distrib] at hS'
        linarith
      have hterm2 : (∑ i : d, ∑ j : d, τ₁.eigvals i * Real.log (τ₂.eigvals j) *
            ‖((star (τ₂.eigUnitary : Matrix d d ℂ)) * (τ₁.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2) =
          ∑ i : d', ∑ j : d', τ₁'.eigvals i * Real.log (τ₂'.eigvals j) *
            ‖((star (τ₂'.eigUnitary : Matrix d' d' ℂ)) * (τ₁'.eigUnitary : Matrix d' d' ℂ)) j i‖ ^ 2 := by
        let L₂ : Matrix d d ℂ := (τ₂.eigUnitary : Matrix d d ℂ) *
          Matrix.diagonal (fun j ↦ (Real.log (τ₂.eigvals j) : ℂ)) *
          star (τ₂.eigUnitary : Matrix d d ℂ)
        let L₂' : Matrix d' d' ℂ := (τ₂'.eigUnitary : Matrix d' d' ℂ) *
          Matrix.diagonal (fun j ↦ (Real.log (τ₂'.eigvals j) : ℂ)) *
          star (τ₂'.eigUnitary : Matrix d' d' ℂ)
        rw [relEntropy_cross_eq_trace_log τ₁ τ₂, relEntropy_cross_eq_trace_log τ₁' τ₂']
        have hL_eq : V * L₂' * Vᴴ = L₂ := by
          set U₂' : Matrix d' d' ℂ := (τ₂'.eigUnitary : Matrix d' d' ℂ)
          have hspec2' : τ₂'.mat = U₂' * Matrix.diagonal (Complex.ofReal ∘ τ₂'.eigvals) * star U₂' := by
            simpa [U₂', DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
              Unitary.conjStarAlgAut_apply] using τ₂'.isHermitian.spectral_theorem
          set U₂ : Matrix d d ℂ := (τ₂.eigUnitary : Matrix d d ℂ)
          have hspec2 : τ₂.mat = U₂ * Matrix.diagonal (Complex.ofReal ∘ τ₂.eigvals) * star U₂ := by
            simpa [U₂, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
              Unitary.conjStarAlgAut_apply] using τ₂.isHermitian.spectral_theorem
          have hcol_eq : ∀ j : d, (V * L₂' * Vᴴ).mulVec (fun r ↦ U₂ r j) =
              L₂.mulVec (fun r ↦ U₂ r j) := by
            intro j
            have hR : L₂.mulVec (fun r ↦ U₂ r j) =
                (Real.log (τ₂.eigvals j) : ℂ) • (fun r ↦ U₂ r j) := by
              have hcol : (star U₂).mulVec (fun r ↦ U₂ r j) = Pi.single j 1 := by
                ext k
                have h := congr_fun (congr_fun (Unitary.coe_star_mul_self τ₂.eigUnitary) k) j
                simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
                  Matrix.one_apply, Pi.single_apply, eq_comm] using h
              simp only [L₂]
              rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcol, Matrix.mulVec_diagonal]
              ext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
            rw [hR]
            have hτ2_eig : τ₂.mat.mulVec (fun r ↦ U₂ r j) =
                (τ₂.eigvals j : ℂ) • (fun r ↦ U₂ r j) := by
              have hcol : (star U₂).mulVec (fun r ↦ U₂ r j) = Pi.single j 1 := by
                ext k
                have h := congr_fun (congr_fun (Unitary.coe_star_mul_self τ₂.eigUnitary) k) j
                simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
                  Matrix.one_apply, Pi.single_apply, eq_comm] using h
              conv_lhs => rw [hspec2]
              rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcol, Matrix.mulVec_diagonal]
              ext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
            by_cases hj0 : τ₂.eigvals j = 0
            · rw [hj0, Real.log_zero, Complex.ofReal_zero, zero_smul]
              have hVh0 : Vᴴ.mulVec (fun r ↦ U₂ r j) = 0 := by
                have h0 : (V * τ₂'.mat * Vᴴ).mulVec (fun r ↦ U₂ r j) = 0 := by
                  rw [hm2, hτ2_eig, hj0, Complex.ofReal_zero, zero_smul]
                have h1 := congr_arg Vᴴ.mulVec h0
                rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc Vᴴ, ← Matrix.mul_assoc Vᴴ,
                  hVHV, Matrix.one_mul, Matrix.mulVec_zero, Matrix.mulVec_mulVec] at h1
                by_contra hne
                have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp h2pd).2 hne
                rw [h1, dotProduct_zero] at hp; exact lt_irrefl 0 hp
              rw [Matrix.mulVec_mulVec, hVh0, Matrix.mulVec_zero]
            · set w : d' → ℂ := Vᴴ.mulVec (fun r ↦ U₂ r j)
              have hVw : V.mulVec w = fun r ↦ U₂ r j := by
                have h1 : (V * Vᴴ).mulVec (τ₂.mat.mulVec (fun r ↦ U₂ r j)) =
                    τ₂.mat.mulVec (fun r ↦ U₂ r j) := by
                  rw [← Matrix.mulVec_mulVec, ← hm2, ← Matrix.mul_assoc (V * Vᴴ),
                    Matrix.mul_assoc V, hVHV, Matrix.mul_one]
                rw [hτ2_eig, Matrix.mulVec_smul] at h1
                have hneC : (τ₂.eigvals j : ℂ) ≠ 0 := by exact_mod_cast hj0
                have := congr_arg (fun v : d → ℂ ↦ (τ₂.eigvals j : ℂ)⁻¹ • v) h1
                simp only [smul_smul, inv_mul_cancel₀ hneC, one_smul] at this
                simpa [w, Matrix.mulVec_mulVec] using this
              have hτ2'_w : τ₂'.mat.mulVec w = (τ₂.eigvals j : ℂ) • w := by
                have h1 := congr_arg Vᴴ.mulVec hτ2_eig
                rw [← hm2, Matrix.mulVec_mulVec, ← Matrix.mul_assoc Vᴴ, ← Matrix.mul_assoc Vᴴ,
                  hVHV, Matrix.one_mul, Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h1
                exact h1
              set y : d' → ℂ := (star U₂').mulVec w
              have hy_coord : ∀ k : d', τ₂'.eigvals k ≠ τ₂.eigvals j → y k = 0 := by
                intro k hk
                have h1 := congr_arg (fun v ↦ ((star U₂').mulVec v) k) hτ2'_w
                have hL : ((star U₂').mulVec (τ₂'.mat.mulVec w)) k = (τ₂'.eigvals k : ℂ) * y k := by
                  conv_lhs => rw [hspec2']
                  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc (star U₂'), ← Matrix.mul_assoc (star U₂'),
                    Unitary.coe_star_mul_self τ₂'.eigUnitary, Matrix.one_mul, Matrix.mulVec_mulVec,
                    Matrix.mulVec_diagonal]
                  rfl
                rw [hL, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h1
                have hsub : ((τ₂'.eigvals k : ℂ) - (τ₂.eigvals j : ℂ)) * y k = 0 := by linear_combination h1
                have hneC : (τ₂'.eigvals k : ℂ) - (τ₂.eigvals j : ℂ) ≠ 0 := by
                  rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.mpr hk
                exact (mul_eq_zero.mp hsub).resolve_left hneC
              have hL2'_w : L₂'.mulVec w = (Real.log (τ₂.eigvals j) : ℂ) • w := by
                simp only [L₂']
                rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
                have hdiag : (fun k : d' ↦ (Real.log (τ₂'.eigvals k) : ℂ) * y k) =
                    (Real.log (τ₂.eigvals j) : ℂ) • y := by
                  ext k; simp only [Pi.smul_apply, smul_eq_mul]
                  by_cases hk : τ₂'.eigvals k = τ₂.eigvals j
                  · rw [hk]
                  · rw [hy_coord k hk, mul_zero, mul_zero]
                rw [hdiag, Matrix.mulVec_smul, show U₂'.mulVec y = w by
                  simp only [y, Matrix.mulVec_mulVec, Unitary.coe_mul_star_self τ₂'.eigUnitary,
                    Matrix.one_mulVec]]
              rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hL2'_w, Matrix.mulVec_smul, hVw]
          have hmulU : (V * L₂' * Vᴴ) * U₂ = L₂ * U₂ := by
            ext r j; exact congr_fun (hcol_eq j) r
          calc V * L₂' * Vᴴ = ((V * L₂' * Vᴴ) * U₂) * star U₂ := by
                rw [Matrix.mul_assoc, Unitary.coe_mul_star_self τ₂.eigUnitary, Matrix.mul_one]
            _ = (L₂ * U₂) * star U₂ := by rw [hmulU]
            _ = L₂ := by rw [Matrix.mul_assoc, Unitary.coe_mul_star_self τ₂.eigUnitary, Matrix.mul_one]
        rw [← hL_eq, ← hm1]
        congr 1
        calc (V * τ₁'.mat * Vᴴ * (V * L₂' * Vᴴ)).trace
            = (V * τ₁'.mat * ((Vᴴ * V) * L₂') * Vᴴ).trace := by simp only [Matrix.mul_assoc]
          _ = (V * (τ₁'.mat * L₂') * Vᴴ).trace := by rw [hVHV, Matrix.one_mul]; simp only [Matrix.mul_assoc]
          _ = (τ₁'.mat * L₂').trace := by
                rw [Matrix.trace_mul_cycle, hVHV, Matrix.one_mul]
      linarith
    have hD1 := hD_iso ρ' σ' ρ σ hρ'_pd hσ'_pd hVρ'VH hVσ'VH hsupp.1
    have hD2 := hD_iso σ' ρ' σ ρ hσ'_pd hρ'_pd hVσ'VH hVρ'VH hsupp.2
    rw [hqjs_eq, hD1, hD2]
    have hmain := prop_3_3_qjjs_posDef hρ'_pd hσ'_pd
    have hfin1 : relEntropy ρ' σ' ≠ ⊤ := by
      unfold relEntropy
      have hs : suppSubset ρ' σ' := fun _ j _ hj ↦ absurd hj (ne_of_gt (hσ'_pd.eigenvalues_pos j))
      simp [hs]
    have hfin2 : relEntropy σ' ρ' ≠ ⊤ := by
      unfold relEntropy
      have hs : suppSubset σ' ρ' := fun _ j _ hj ↦ absurd hj (ne_of_gt (hρ'_pd.eigenvalues_pos j))
      simp [hs]
    have hc_lt1 : qjs ρ' σ' < 1 := by
      by_contra hge; push Not at hge
      obtain ⟨a, b, μ, ha, hab, hprob, hsuppμ, _, hmean, _, _, hEq36⟩ :=
        lemma_3_2_hockeyStick_measure hρ'_pd hσ'_pd
      have hlt_pt : ∀ t ∈ Icc a b,
          t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t)) < (1 + t) / 2 := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
        have h1 : Real.logb 2 (2 * t / (1 + t)) < 1 := by
          rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity), Real.rpow_one,
            div_lt_iff₀ (by linarith)]; linarith
        have h2 : Real.logb 2 (2 / (1 + t)) < 1 := by
          rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity), Real.rpow_one,
            div_lt_iff₀ (by linarith)]; linarith
        nlinarith
      have hcont_diff : ContinuousOn (fun t : ℝ ↦
          (1 + t) / 2 - (t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t)))) (Icc a b) := by
        refine ContinuousOn.sub (by fun_prop) (ContinuousOn.add ?_ ?_)
        · refine (continuousOn_id.div_const 2).mul (ContinuousOn.div_const ?_ _)
          refine Real.continuousOn_log.comp ?_ ?_
          · exact (continuousOn_const.mul continuousOn_id).div (continuousOn_const.add continuousOn_id)
              fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
          · intro t ht; exact ne_of_gt (div_pos (by linarith [lt_of_lt_of_le ha ht.1])
              (by linarith [lt_of_lt_of_le ha ht.1]))
        · refine continuousOn_const.mul (ContinuousOn.div_const ?_ _)
          refine Real.continuousOn_log.comp ?_ ?_
          · exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
              fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
          · intro t ht; exact ne_of_gt (div_pos two_pos (by linarith [lt_of_lt_of_le ha ht.1]))
      obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, left_mem_Icc.mpr hab⟩ hcont_diff
      set δ := (1 + t₀) / 2 - (t₀ / 2 * Real.logb 2 (2 * t₀ / (1 + t₀)) + 1 / 2 * Real.logb 2 (2 / (1 + t₀)))
      have hδ_pos : 0 < δ := sub_pos.mpr (hlt_pt t₀ ht₀)
      have hI_lhs : Integrable (fun t : ℝ ↦
          t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) μ := by
        have hcont : ContinuousOn (fun t : ℝ ↦
            t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) (Icc a b) := by
          have := (show ContinuousOn (fun t : ℝ ↦ (1 + t) / 2) (Icc a b) by fun_prop).sub hcont_diff
          exact this.congr fun t _ ↦ by ring
        obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
        have hm : AEStronglyMeasurable (fun t : ℝ ↦
            t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) μ := by
          have hrest : μ.restrict (Icc a b) = μ := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsuppμ)
          rw [← hrest]; exact hcont.aestronglyMeasurable measurableSet_Icc
        refine Integrable.mono' (integrable_const M) hm ?_
        filter_upwards [ae_iff.mpr hsuppμ] with t ht
        exact hM t ht
      have hI_rhs : Integrable (fun t : ℝ ↦ (1 + t) / 2) μ := by
        have hcont : ContinuousOn (fun t : ℝ ↦ (1 + t) / 2) (Icc a b) := by fun_prop
        obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
        refine Integrable.mono' (integrable_const M) (by fun_prop) ?_
        filter_upwards [ae_iff.mpr hsuppμ] with t ht
        exact hM t ht
      have hint_le : ∫ t, (t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) ∂μ ≤
          ∫ t, ((1 + t) / 2 - δ) ∂μ := by
        apply integral_mono_ae hI_lhs (hI_rhs.sub (integrable_const δ))
        filter_upwards [ae_iff.mpr hsuppμ] with t ht
        linarith [hmin ht]
      have hrhs_val : ∫ t, ((1 + t) / 2 - δ) ∂μ = 1 - δ := by
        have hint_t : Integrable (fun t : ℝ ↦ t) μ := by
          refine Integrable.mono' (integrable_const b) (continuous_id : Continuous (fun t : ℝ ↦ t)).aestronglyMeasurable ?_
          filter_upwards [ae_iff.mpr hsuppμ] with t ht
          rw [Real.norm_of_nonneg (by linarith [ht.1])]; exact ht.2
        rw [integral_sub hI_rhs (integrable_const δ), integral_div, integral_add (integrable_const 1) hint_t,
          integral_const, smul_eq_mul, hmean, show μ.real univ = 1 by simp [Measure.real],
          integral_const, smul_eq_mul, show μ.real univ = 1 by simp [Measure.real]]
        ring
      linarith
    unfold phiExt
    simp only [hc_lt1, ↓reduceIte]
    have hRHS : (1 / 4 : ℝ≥0∞) * (relEntropy ρ' σ' + relEntropy σ' ρ') =
        ENNReal.ofReal ((1 / 4 : ℝ) * ((relEntropy ρ' σ').toReal + (relEntropy σ' ρ').toReal)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hfin1, ENNReal.ofReal_toReal hfin2]
      congr 1; norm_num
    rw [hRHS]
    exact ENNReal.ofReal_le_ofReal hmain
  · -- If `supp(ρ) ≠ supp(σ)`, then `D(ρ ‖ σ) + D(σ ‖ ρ) = ⊤`
    have htop : relEntropy ρ σ + relEntropy σ ρ = ⊤ := by
      by_cases h1 : suppSubset ρ σ
      · have h2 : ¬ suppSubset σ ρ := fun h2 ↦ hsupp ⟨h1, h2⟩
        unfold relEntropy; simp [h2]
      · unfold relEntropy; simp [h1]
    rw [htop, ENNReal.mul_top (by norm_num : (1 / 4 : ℝ≥0∞) ≠ 0)]
    exact le_top

end PolarCodes
