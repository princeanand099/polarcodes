/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.QJJS
import PolarCodes.ScalarSupplements

/-!
# Nonlinear Strong Data Processing Inequality for Qubit Dephasing (Theorem 1.3)

This module proves **Theorem 1.3** (`theorem_1_3_dephasing_sdpi`):
For every bipartite quantum state `Ψ ∈ D(ℂ² ⊗ H_B)` and every dephasing parameter `p ∈ [0, 1/2]`,
the relative entropy of coherence `C(p) = S((Z_{1/2} ⊗ id)(Ψ)) - S((Z_p ⊗ id)(Ψ))` satisfies
`C(p) ≤ 1 - h₂(h₂⁻¹(1 - C(0)) * p)`.

We also prove tightness (`theorem_1_3_equatorial_equality`): every equatorial single-qubit state
`Ψ_A = ½ (I + x X)` (`x ∈ [0, 1]`) attains equality for every `p ∈ [0, 1/2]`.

The proof for full-rank states `Ψ ≻ 0` uses Klein's inequality (`D(ρ ‖ σ) ≥ 0`) along the
continuous-time dephasing semigroup `p(t) = (1 - e^{-t})/2` together with **Proposition 3.3**
(`prop_3_3_qjjs_posDef`), producing the exact finite-step contraction inequality
`C(t) - C(t+h) ≥ (e^h - 1) φ(C(t+h))` and Lipschitz continuity of `t ↦ C(t)`, which integrates
via Riemann sums to `x(t) ≤ e^{-t} x(0)`. General states follow by `ε ↓ 0` perturbation with
the maximally mixed state using `tendsto_vonNeumannEntropy_mix_maxMixed`.
-/

open Matrix BigOperators Real Filter Topology Set
open scoped ComplexOrder ENNReal

namespace PolarCodes

variable {d : Type*} [Fintype d] [DecidableEq d]

private lemma conjUnitary_posDef {α : Type*} [Fintype α] [DecidableEq α]
    {ρ : DensityOp α} (hρ : ρ.mat.PosDef) (U : Matrix.unitaryGroup α ℂ) :
    (DensityOp.conjUnitary U ρ).mat.PosDef := by
  have hU : Function.Injective (fun v : α → ℂ ↦ v ᵥ* (U : Matrix α α ℂ)) := by
    intro v w hvw
    have h1 := congr_arg (fun x ↦ x ᵥ* star (U : Matrix α α ℂ)) hvw
    have hUmul : (U : Matrix α α ℂ) * star (U : Matrix α α ℂ) = 1 := Unitary.coe_mul_star_self U
    simp only [Matrix.vecMul_vecMul, hUmul, Matrix.vecMul_one] at h1
    exact h1
  simpa [DensityOp.conjUnitary, Matrix.star_eq_conjTranspose] using
    hρ.mul_mul_conjTranspose_same hU

private lemma maxMixedState_posDef' (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    (maxMixedState α).mat.PosDef := by
  have hpos : (0 : ℝ) < ((Fintype.card α : ℝ)⁻¹) := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  simpa [maxMixedState, Complex.real_smul] using (Matrix.PosDef.one (n := α) (R := ℂ)).smul hpos

private lemma qjs_lt_one_posDef {α : Type*} [Fintype α] [DecidableEq α]
    {ρ σ : DensityOp α} (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    qjs ρ σ < 1 := by
  obtain ⟨a, b, μ, ha, hab, hprob, hsuppμ, _, hmean, _, _, hEq36⟩ :=
    lemma_3_2_hockeyStick_measure hρ hσ
  have hlt_pt : ∀ s ∈ Icc a b,
      s / 2 * Real.logb 2 (2 * s / (1 + s)) + 1 / 2 * Real.logb 2 (2 / (1 + s)) < (1 + s) / 2 := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have h1 : Real.logb 2 (2 * s / (1 + s)) < 1 := by
      rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity), Real.rpow_one,
        div_lt_iff₀ (by linarith)]; linarith
    have h2 : Real.logb 2 (2 / (1 + s)) < 1 := by
      rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity), Real.rpow_one,
        div_lt_iff₀ (by linarith)]; linarith
    nlinarith
  have hcont_diff : ContinuousOn (fun s : ℝ ↦
      (1 + s) / 2 - (s / 2 * Real.logb 2 (2 * s / (1 + s)) + 1 / 2 * Real.logb 2 (2 / (1 + s)))) (Icc a b) := by
    refine ContinuousOn.sub (by fun_prop) (ContinuousOn.add ?_ ?_)
    · refine (continuousOn_id.div_const 2).mul (ContinuousOn.div_const ?_ _)
      refine Real.continuousOn_log.comp ?_ ?_
      · exact (continuousOn_const.mul continuousOn_id).div (continuousOn_const.add continuousOn_id)
          fun s hs ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha hs.1])
      · intro s hs; exact ne_of_gt (div_pos (by linarith [lt_of_lt_of_le ha hs.1])
          (by linarith [lt_of_lt_of_le ha hs.1]))
    · refine continuousOn_const.mul (ContinuousOn.div_const ?_ _)
      refine Real.continuousOn_log.comp ?_ ?_
      · exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
          fun s hs ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha hs.1])
      · intro s hs; exact ne_of_gt (div_pos two_pos (by linarith [lt_of_lt_of_le ha hs.1]))
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, left_mem_Icc.mpr hab⟩ hcont_diff
  set δ := (1 + t₀) / 2 - (t₀ / 2 * Real.logb 2 (2 * t₀ / (1 + t₀)) + 1 / 2 * Real.logb 2 (2 / (1 + t₀)))
  have hδ_pos : 0 < δ := sub_pos.mpr (hlt_pt t₀ ht₀)
  have hI_lhs : MeasureTheory.Integrable (fun s : ℝ ↦
      s / 2 * Real.logb 2 (2 * s / (1 + s)) + 1 / 2 * Real.logb 2 (2 / (1 + s))) μ := by
    have hcont : ContinuousOn (fun s : ℝ ↦
        s / 2 * Real.logb 2 (2 * s / (1 + s)) + 1 / 2 * Real.logb 2 (2 / (1 + s))) (Icc a b) := by
      have := (show ContinuousOn (fun s : ℝ ↦ (1 + s) / 2) (Icc a b) by fun_prop).sub hcont_diff
      exact this.congr fun s _ ↦ by dsimp only [Pi.sub_apply]; ring
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    have hm : MeasureTheory.AEStronglyMeasurable (fun s : ℝ ↦
        s / 2 * Real.logb 2 (2 * s / (1 + s)) + 1 / 2 * Real.logb 2 (2 / (1 + s))) μ := by
      have hrest : μ.restrict (Icc a b) = μ :=
        MeasureTheory.Measure.restrict_eq_self_of_ae_mem (MeasureTheory.ae_iff.mpr hsuppμ)
      rw [← hrest]; exact hcont.aestronglyMeasurable measurableSet_Icc
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const M) hm ?_
    filter_upwards [MeasureTheory.ae_iff.mpr hsuppμ] with s hs
    exact hM s hs
  have hI_rhs : MeasureTheory.Integrable (fun s : ℝ ↦ (1 + s) / 2) μ := by
    have hcont : ContinuousOn (fun s : ℝ ↦ (1 + s) / 2) (Icc a b) := by fun_prop
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const M) (by fun_prop) ?_
    filter_upwards [MeasureTheory.ae_iff.mpr hsuppμ] with s hs
    exact hM s hs
  have hint_le : ∫ s, (s / 2 * Real.logb 2 (2 * s / (1 + s)) + 1 / 2 * Real.logb 2 (2 / (1 + s))) ∂μ ≤
      ∫ s, ((1 + s) / 2 - δ) ∂μ := by
    apply MeasureTheory.integral_mono_ae hI_lhs (hI_rhs.sub (MeasureTheory.integrable_const δ))
    filter_upwards [MeasureTheory.ae_iff.mpr hsuppμ] with s hs
    have hle : δ ≤ (1 + s) / 2 - (s / 2 * Real.logb 2 (2 * s / (1 + s)) + 1 / 2 * Real.logb 2 (2 / (1 + s))) := hmin hs
    dsimp only [Pi.sub_apply]; linarith
  have hrhs_val : ∫ s, ((1 + s) / 2 - δ) ∂μ = 1 - δ := by
    have hint_s : MeasureTheory.Integrable (fun s : ℝ ↦ s) μ := by
      refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const b)
        (continuous_id : Continuous (fun s : ℝ ↦ s)).aestronglyMeasurable ?_
      filter_upwards [MeasureTheory.ae_iff.mpr hsuppμ] with s hs
      rw [Real.norm_of_nonneg (by linarith [hs.1])]; exact hs.2
    rw [MeasureTheory.integral_sub hI_rhs (MeasureTheory.integrable_const δ),
      MeasureTheory.integral_div, MeasureTheory.integral_add (MeasureTheory.integrable_const 1) hint_s,
      MeasureTheory.integral_const, smul_eq_mul, hmean,
      show μ.real univ = 1 by simp [MeasureTheory.Measure.real],
      MeasureTheory.integral_const, smul_eq_mul,
      show μ.real univ = 1 by simp [MeasureTheory.Measure.real]]
    ring
  linarith

/-! ### Part 1: Matrix Logarithm Trace and Klein's Inequality for Positive Definite States -/

/-- Natural matrix logarithm `log(σ) = U_σ diag(log σ_j) U_σ†` for a density operator `σ`. -/
private noncomputable def natLogMat (σ : DensityOp d) : Matrix d d ℂ :=
  (σ.eigUnitary : Matrix d d ℂ) *
    Matrix.diagonal (fun j ↦ (Real.log (σ.eigvals j) : ℂ)) *
    star (σ.eigUnitary : Matrix d d ℂ)

/-- For any density operators `ρ, σ`, `Re Tr(ρ log σ)` equals the eigenbasis cross-sum
`∑ i j ‖(U_σ† U_ρ)_{ji}‖² ρ_i log σ_j`. -/
private lemma re_trace_mul_natLogMat (ρ σ : DensityOp d) :
    (ρ.mat * natLogMat σ).trace.re =
      ∑ i : d, ∑ j : d,
        ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (ρ.eigvals i * Real.log (σ.eigvals j)) := by
  set Uρ : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
  set Uσ : Matrix d d ℂ := (σ.eigUnitary : Matrix d d ℂ)
  set W : Matrix d d ℂ := star Uσ * Uρ
  have hspecρ : ρ.mat = Uρ * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star Uρ := by
    simpa [Uρ, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
  have htr : (ρ.mat * natLogMat σ).trace =
      (Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *
        (star W * Matrix.diagonal (fun j ↦ (Real.log (σ.eigvals j) : ℂ)) * W)).trace := by
    conv_lhs => rw [hspecρ]
    have hstarW : star W = star Uρ * Uσ := by simp [W, Matrix.star_mul, star_star]
    rw [hstarW]
    calc (Uρ * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star Uρ *
            (Uσ * Matrix.diagonal (fun j ↦ (Real.log (σ.eigvals j) : ℂ)) * star Uσ)).trace
        = (Uρ * (Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star Uρ *
            (Uσ * Matrix.diagonal (fun j ↦ (Real.log (σ.eigvals j) : ℂ)) * star Uσ))).trace := by
          simp only [Matrix.mul_assoc]
      _ = (Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *
            (star Uρ * Uσ * Matrix.diagonal (fun j ↦ (Real.log (σ.eigvals j) : ℂ)) * (star Uσ * Uρ))).trace := by
          rw [Matrix.trace_mul_comm Uρ]; simp only [Matrix.mul_assoc]
      _ = _ := rfl
  rw [htr]
  have htr_simp : (Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *
      (star W * Matrix.diagonal (fun j ↦ (Real.log (σ.eigvals j) : ℂ)) * W)).trace =
      ∑ i : d, ∑ j : d, (ρ.eigvals i : ℂ) * (star (W j i) * (Real.log (σ.eigvals j) : ℂ) * W j i) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
      Function.comp_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.mul_sum, Matrix.star_apply]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [htr_simp, Complex.re_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro j _
  have hsq : star (W j i) * W j i = ((‖W j i‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcalc : (ρ.eigvals i : ℂ) * (star (W j i) * (Real.log (σ.eigvals j) : ℂ) * W j i) =
      ((‖W j i‖ ^ 2 * (ρ.eigvals i * Real.log (σ.eigvals j)) : ℝ) : ℂ) := by
    calc _ = (ρ.eigvals i : ℂ) * (Real.log (σ.eigvals j) : ℂ) * (star (W j i) * W j i) := by ring
      _ = _ := by rw [hsq]; push_cast; ring
  rw [hcalc, Complex.ofReal_re]

/-- For any positive definite `ρ, σ`,
`(relEntropy ρ σ).toReal * log 2 = -log 2 * S(ρ) - Re Tr(ρ log σ)` and is nonnegative. -/
private lemma relEntropy_toReal_mul_log2 {ρ σ : DensityOp d}
    (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    0 ≤ (relEntropy ρ σ).toReal ∧
    (relEntropy ρ σ).toReal * Real.log 2 =
      -(Real.log 2) * vonNeumannEntropy ρ - (ρ.mat * natLogMat σ).trace.re := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsupp : suppSubset ρ σ := fun _ j _ hj ↦ absurd hj (ne_of_gt (hσ.eigenvalues_pos j))
  set W : Matrix d d ℂ := star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)
  have hcol1 : ∀ i : d, ∑ j : d, ‖W j i‖ ^ 2 = 1 := by
    intro i
    have hσU : (σ.eigUnitary : Matrix d d ℂ) * star (σ.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_mul_star_self σ.eigUnitary
    have hρU : star (ρ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_star_mul_self ρ.eigUnitary
    have hU : star W * W = 1 := by
      simp only [W, Matrix.star_mul, star_star, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (σ.eigUnitary : Matrix d d ℂ), hσU, Matrix.one_mul, hρU]
    have hii := congr_arg Complex.re (congr_fun (congr_fun hU i) i)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re,
      Complex.re_sum] at hii
    rw [← hii]
    apply Finset.sum_congr rfl; intro j _
    have hsq : star (W j i) * W j i = ((‖W j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hsq, Complex.ofReal_re]
  have hrow1 : ∀ j : d, ∑ i : d, ‖W j i‖ ^ 2 = 1 := by
    intro j
    have hρU : (ρ.eigUnitary : Matrix d d ℂ) * star (ρ.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_mul_star_self ρ.eigUnitary
    have hσU : star (σ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_star_mul_self σ.eigUnitary
    have hU : W * star W = 1 := by
      simp only [W, Matrix.star_mul, star_star, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (ρ.eigUnitary : Matrix d d ℂ), hρU, Matrix.one_mul, hσU]
    have hjj := congr_arg Complex.re (congr_fun (congr_fun hU j) j)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re,
      Complex.re_sum] at hjj
    rw [← hjj]
    apply Finset.sum_congr rfl; intro i _
    have hsq : W j i * star (W j i) = ((‖W j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hsq, Complex.ofReal_re]
  have hsum_nn : 0 ≤ ∑ i : d, ∑ j : d, ‖W j i‖ ^ 2 *
      (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j))) := by
    have hge : ∑ i : d, ∑ j : d, ‖W j i‖ ^ 2 * (ρ.eigvals i - σ.eigvals j) ≤
        ∑ i : d, ∑ j : d, ‖W j i‖ ^ 2 *
          (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j))) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have ha : 0 < ρ.eigvals i := hρ.eigenvalues_pos i
      have hb : 0 < σ.eigvals j := hσ.eigenvalues_pos j
      have hlog := Real.log_le_sub_one_of_pos (div_pos hb ha)
      rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt ha)
      have hdiv : ρ.eigvals i * (σ.eigvals j / ρ.eigvals i - 1) = σ.eigvals j - ρ.eigvals i := by
        field_simp [ne_of_gt ha]
      rw [hdiv] at hmul; linarith
    have hzero : ∑ i : d, ∑ j : d, ‖W j i‖ ^ 2 * (ρ.eigvals i - σ.eigvals j) = 0 := by
      have htr_eq : ∀ (τ : DensityOp d), ∑ i : d, τ.eigvals i = 1 := by
        intro τ
        have hspec : τ.mat = (τ.eigUnitary : Matrix d d ℂ) *
            Matrix.diagonal (Complex.ofReal ∘ τ.eigvals) * star (τ.eigUnitary : Matrix d d ℂ) := by
          simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
            Unitary.conjStarAlgAut_apply] using τ.isHermitian.spectral_theorem
        have h1 := congr_arg (fun M : Matrix d d ℂ ↦ M.trace.re) hspec
        rw [τ.trace_one, Complex.one_re, Matrix.trace_mul_cycle,
          Unitary.coe_star_mul_self τ.eigUnitary, Matrix.one_mul, Matrix.trace_diagonal] at h1
        simpa [Complex.re_sum] using h1.symm
      have hs1 : ∑ i : d, ∑ j : d, ‖W j i‖ ^ 2 * (ρ.eigvals i - σ.eigvals j) =
          (∑ i : d, (∑ j : d, ‖W j i‖ ^ 2) * ρ.eigvals i) -
          (∑ j : d, (∑ i : d, ‖W j i‖ ^ 2) * σ.eigvals j) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        congr 1
        · apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_mul]
        · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_mul]
      rw [hs1]
      simp_rw [hcol1, hrow1, one_mul, htr_eq ρ, htr_eq σ, sub_self]
    linarith
  have hval : (relEntropy ρ σ).toReal =
      (∑ i : d, ∑ j : d, ‖W j i‖ ^ 2 *
        (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j)))) / Real.log 2 := by
    unfold relEntropy
    rw [if_pos hsupp, ENNReal.toReal_ofReal (div_nonneg hsum_nn (le_of_lt hlog2))]
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  rw [hval, div_mul_cancel₀ _ (ne_of_gt hlog2), re_trace_mul_natLogMat]
  have hS : -(Real.log 2) * vonNeumannEntropy ρ = ∑ i : d, ρ.eigvals i * Real.log (ρ.eigvals i) := by
    unfold vonNeumannEntropy Real.negMulLog
    field_simp [ne_of_gt hlog2]
    simp only [neg_mul, Finset.sum_neg_distrib, neg_neg]
  rw [hS]
  have hsplit : (∑ i : d, ∑ j : d, ‖W j i‖ ^ 2 *
      (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j)))) =
      (∑ i : d, (∑ j : d, ‖W j i‖ ^ 2) * (ρ.eigvals i * Real.log (ρ.eigvals i))) -
      (∑ i : d, ∑ j : d, ‖W j i‖ ^ 2 * (ρ.eigvals i * Real.log (σ.eigvals j))) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_mul]
  rw [hsplit]
  simp_rw [hcol1, one_mul]; rfl

/-- `Re Tr(σ log σ) = -(log 2) * S(σ)` for any density operator `σ`. -/
private lemma re_trace_self_mul_natLogMat (σ : DensityOp d) :
    (σ.mat * natLogMat σ).trace.re = -(Real.log 2) * vonNeumannEntropy σ := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [re_trace_mul_natLogMat]
  simp only [Unitary.coe_star_mul_self σ.eigUnitary, Matrix.one_apply]
  have hsum : (∑ i : d, ∑ j : d, ‖(if j = i then (1 : ℂ) else 0)‖ ^ 2 *
      (σ.eigvals i * Real.log (σ.eigvals j))) = ∑ i : d, σ.eigvals i * Real.log (σ.eigvals i) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum]
  unfold vonNeumannEntropy Real.negMulLog
  field_simp [hlog2]
  simp [neg_mul, Finset.sum_neg_distrib]

/-- **Klein's First-Order Entropy Difference Identity**: for positive definite `ρ, σ`,
`(S(σ) - S(ρ)) * log 2 = ((ρ - σ) * log σ).trace.re + D(ρ ‖ σ) * log 2`,
and in particular `(S(σ) - S(ρ)) * log 2 ≥ ((ρ - σ) * log σ).trace.re`. -/
private lemma entropy_sub_ge_trace_log {ρ σ : DensityOp d}
    (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    ((ρ.mat - σ.mat) * natLogMat σ).trace.re ≤
      (vonNeumannEntropy σ - vonNeumannEntropy ρ) * Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨hD_nn, hD_eq⟩ := relEntropy_toReal_mul_log2 hρ hσ
  have hself := re_trace_self_mul_natLogMat σ
  have hsub : ((ρ.mat - σ.mat) * natLogMat σ).trace.re =
      (ρ.mat * natLogMat σ).trace.re - (σ.mat * natLogMat σ).trace.re := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  rw [hsub, hself]
  nlinarith

/-- Unitary conjugation commutes with `natLogMat` for `PosDef` states:
`U * natLogMat ρ * U† = natLogMat (conjUnitary U ρ)`. -/
private lemma conjUnitary_natLogMat {ρ : DensityOp d} (hρ : ρ.mat.PosDef)
    (U : Matrix.unitaryGroup d ℂ) :
    (U : Matrix d d ℂ) * natLogMat ρ * star (U : Matrix d d ℂ) =
      natLogMat (DensityOp.conjUnitary U ρ) := by
  set σ := DensityOp.conjUnitary U ρ
  have hσ_pd : σ.mat.PosDef := conjUnitary_posDef hρ U
  set Uρ : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
  set Uσ : Matrix d d ℂ := (σ.eigUnitary : Matrix d d ℂ)
  have hspecρ : ρ.mat = Uρ * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star Uρ := by
    simpa [Uρ, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
  have hspecσ : σ.mat = Uσ * Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) * star Uσ := by
    simpa [Uσ, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
  -- Check agreement on every eigenvector column `Uσ e_j` of `σ`
  have hcol_eq : ∀ j : d,
      ((U : Matrix d d ℂ) * natLogMat ρ * star (U : Matrix d d ℂ)).mulVec (fun r ↦ Uσ r j) =
        (natLogMat σ).mulVec (fun r ↦ Uσ r j) := by
    intro j
    have hcol : (star Uσ).mulVec (fun r ↦ Uσ r j) = Pi.single j 1 := by
      ext k
      have h := congr_fun (congr_fun (Unitary.coe_star_mul_self σ.eigUnitary) k) j
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
        Matrix.one_apply, Pi.single_apply, eq_comm] using h
    have hR : (natLogMat σ).mulVec (fun r ↦ Uσ r j) =
        (Real.log (σ.eigvals j) : ℂ) • (fun r ↦ Uσ r j) := by
      change (Uσ * Matrix.diagonal (fun j ↦ (Real.log (σ.eigvals j) : ℂ)) * star Uσ) *ᵥ (fun r ↦ Uσ r j) = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol]
      ext r; simp [Matrix.mulVec, dotProduct, Matrix.mulVec_diagonal, Matrix.diagonal_apply, Pi.single_apply, mul_comm]
    rw [hR]
    have hσ_eig : σ.mat.mulVec (fun r ↦ Uσ r j) = (σ.eigvals j : ℂ) • (fun r ↦ Uσ r j) := by
      conv_lhs => rw [hspecσ]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol]
      ext r; simp [Matrix.mulVec, dotProduct, Matrix.mulVec_diagonal, Matrix.diagonal_apply, Pi.single_apply, mul_comm]
    set w : d → ℂ := (star (U : Matrix d d ℂ)).mulVec (fun r ↦ Uσ r j)
    have hρ_eig : ρ.mat.mulVec w = (σ.eigvals j : ℂ) • w := by
      have h1 := congr_arg (star (U : Matrix d d ℂ)).mulVec hσ_eig
      have hσ_mat : σ.mat = (U : Matrix d d ℂ) * ρ.mat * star (U : Matrix d d ℂ) := rfl
      have hU_smul : star (U : Matrix d d ℂ) * (U : Matrix d d ℂ) = 1 := Unitary.coe_star_mul_self U
      rw [hσ_mat, Matrix.mulVec_mulVec, ← Matrix.mul_assoc (star (U : Matrix d d ℂ)),
        ← Matrix.mul_assoc (star (U : Matrix d d ℂ)), hU_smul, Matrix.one_mul,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h1
      exact h1
    set y : d → ℂ := (star Uρ).mulVec w
    have hy_coord : ∀ k : d, ρ.eigvals k ≠ σ.eigvals j → y k = 0 := by
      intro k hk
      have h1 := congr_arg (fun v ↦ ((star Uρ).mulVec v) k) hρ_eig
      have hL : ((star Uρ).mulVec (ρ.mat.mulVec w)) k = (ρ.eigvals k : ℂ) * y k := by
        conv_lhs => rw [hspecρ]
        have hUρ_smul : star Uρ * Uρ = 1 := Unitary.coe_star_mul_self ρ.eigUnitary
        rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc (star Uρ), ← Matrix.mul_assoc (star Uρ),
          hUρ_smul, Matrix.one_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]; rfl
      rw [hL, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h1
      have hsub : ((ρ.eigvals k : ℂ) - (σ.eigvals j : ℂ)) * y k = 0 := by linear_combination h1
      have hne : (ρ.eigvals k : ℂ) - (σ.eigvals j : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.mpr hk
      exact (mul_eq_zero.mp hsub).resolve_left hne
    have hlog_w : (natLogMat ρ).mulVec w = (Real.log (σ.eigvals j) : ℂ) • w := by
      change (Uρ * Matrix.diagonal (fun k ↦ (Real.log (ρ.eigvals k) : ℂ)) * star Uρ) *ᵥ w = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have hdiag : Matrix.diagonal (fun k ↦ (Real.log (ρ.eigvals k) : ℂ)) *ᵥ y =
          (Real.log (σ.eigvals j) : ℂ) • y := by
        ext k; rw [Matrix.mulVec_diagonal]; simp only [Pi.smul_apply, smul_eq_mul]
        by_cases hk : ρ.eigvals k = σ.eigvals j
        · rw [hk]
        · rw [hy_coord k hk, mul_zero, mul_zero]
      have hUρ_mul : Uρ * star Uρ = 1 := Unitary.coe_mul_star_self ρ.eigUnitary
      rw [hdiag, Matrix.mulVec_smul, show Uρ.mulVec y = w by
        simp only [y, Matrix.mulVec_mulVec, hUρ_mul, Matrix.one_mulVec]]
    have hU_mul : (U : Matrix d d ℂ) * star (U : Matrix d d ℂ) = 1 := Unitary.coe_mul_star_self U
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hlog_w, Matrix.mulVec_smul]
    simp only [w, Matrix.mulVec_mulVec, hU_mul, Matrix.one_mulVec]
  have hmulU : ((U : Matrix d d ℂ) * natLogMat ρ * star (U : Matrix d d ℂ)) * Uσ = natLogMat σ * Uσ := by
    ext r j; exact congr_fun (hcol_eq j) r
  have hUσ_mul : Uσ * star Uσ = 1 := Unitary.coe_mul_star_self σ.eigUnitary
  calc (U : Matrix d d ℂ) * natLogMat ρ * star (U : Matrix d d ℂ)
      = ((U : Matrix d d ℂ) * natLogMat ρ * star (U : Matrix d d ℂ) * Uσ) * star Uσ := by
        rw [Matrix.mul_assoc ((U : Matrix d d ℂ) * natLogMat ρ * star (U : Matrix d d ℂ)),
          hUσ_mul, Matrix.mul_one]
    _ = (natLogMat σ * Uσ) * star Uσ := by rw [hmulU]
    _ = natLogMat σ := by rw [Matrix.mul_assoc, hUσ_mul, Matrix.mul_one]

/-- Symmetrized trace identity for a pair `(ρ, Z ρ Z)` with `Z = pauliZTensorI d`:
`Re Tr((ρ - ρ̃) log ρ) = ½ (D(ρ ‖ ρ̃) + D(ρ̃ ‖ ρ)) * log 2`. -/
private lemma trace_diff_log_pauliZ {ρ : DensityOp (Bool × d)} (hρ : ρ.mat.PosDef) :
    ((ρ.mat - (DensityOp.conjUnitary (pauliZTensorI d) ρ).mat) * natLogMat ρ).trace.re =
      (1 / 2 : ℝ) * ((relEntropy ρ (DensityOp.conjUnitary (pauliZTensorI d) ρ)).toReal +
        (relEntropy (DensityOp.conjUnitary (pauliZTensorI d) ρ) ρ).toReal) * Real.log 2 := by
  set Z := pauliZTensorI d
  set ρ' := DensityOp.conjUnitary Z ρ
  have hZ_self : (Z : Matrix (Bool × d) (Bool × d) ℂ) * (Z : Matrix (Bool × d) (Bool × d) ℂ) = 1 := by
    ext ⟨b, x⟩ ⟨c, y⟩
    simp only [Z, pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hpq : (b, x) = (c, y)
    · rcases Prod.mk.inj hpq with ⟨rfl, rfl⟩; simp only [↓reduceIte, Finset.sum_ite_eq', Finset.mem_univ]; cases b <;> simp
    · simp only [hpq, ↓reduceIte]
      apply Finset.sum_eq_zero; intro r _
      by_cases h : (b, x) = r
      · subst h; simp [hpq]
      · simp [h]
  have hZ_star : star (Z : Matrix (Bool × d) (Bool × d) ℂ) = (Z : Matrix (Bool × d) (Bool × d) ℂ) := by
    ext p q
    simp only [Z, pauliZTensorI, Matrix.star_apply, Matrix.diagonal_apply]
    by_cases hpq : q = p
    · subst hpq; cases q.1 <;> simp
    · simp [hpq, Ne.symm hpq]
  have hρ'_pd : ρ'.mat.PosDef := conjUnitary_posDef hρ Z
  have hZρ'Z : (Z : Matrix (Bool × d) (Bool × d) ℂ) * ρ'.mat * star (Z : Matrix (Bool × d) (Bool × d) ℂ) = ρ.mat := by
    simp only [ρ', DensityOp.conjUnitary, hZ_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Z : Matrix (Bool × d) (Bool × d) ℂ) (Z : Matrix (Bool × d) (Bool × d) ℂ),
      hZ_self, Matrix.one_mul, Matrix.mul_one]
  have hlog_conj : (Z : Matrix (Bool × d) (Bool × d) ℂ) * natLogMat ρ *
      star (Z : Matrix (Bool × d) (Bool × d) ℂ) = natLogMat ρ' :=
    conjUnitary_natLogMat hρ Z
  -- Conjugating inside trace shows `Tr((ρ - ρ') log ρ) = -Tr((ρ - ρ') log ρ')`
  have hneg : ((ρ.mat - ρ'.mat) * natLogMat ρ).trace = -((ρ.mat - ρ'.mat) * natLogMat ρ').trace := by
    have htr_cyc : ((ρ.mat - ρ'.mat) * natLogMat ρ).trace =
        (((Z : Matrix (Bool × d) (Bool × d) ℂ) * (ρ.mat - ρ'.mat) * star (Z : Matrix (Bool × d) (Bool × d) ℂ)) *
          ((Z : Matrix (Bool × d) (Bool × d) ℂ) * natLogMat ρ * star (Z : Matrix (Bool × d) (Bool × d) ℂ))).trace := by
      have hZs : star (Z : Matrix (Bool × d) (Bool × d) ℂ) * (Z : Matrix (Bool × d) (Bool × d) ℂ) = 1 :=
        Unitary.coe_star_mul_self Z
      calc ((ρ.mat - ρ'.mat) * natLogMat ρ).trace
          = ((ρ.mat - ρ'.mat) * natLogMat ρ * (star (Z : Matrix (Bool × d) (Bool × d) ℂ) * (Z : Matrix (Bool × d) (Bool × d) ℂ))).trace := by
              rw [hZs, Matrix.mul_one]
        _ = (((Z : Matrix (Bool × d) (Bool × d) ℂ) * ((ρ.mat - ρ'.mat) * natLogMat ρ * star (Z : Matrix (Bool × d) (Bool × d) ℂ)))).trace := by
              rw [← Matrix.mul_assoc ((ρ.mat - ρ'.mat) * natLogMat ρ), Matrix.trace_mul_comm]
        _ = (((Z : Matrix (Bool × d) (Bool × d) ℂ) * (ρ.mat - ρ'.mat) * star (Z : Matrix (Bool × d) (Bool × d) ℂ)) *
              ((Z : Matrix (Bool × d) (Bool × d) ℂ) * natLogMat ρ * star (Z : Matrix (Bool × d) (Bool × d) ℂ))).trace := by
              simp only [Matrix.mul_assoc]
              rw [← Matrix.mul_assoc (star (Z : Matrix (Bool × d) (Bool × d) ℂ)) (Z : Matrix (Bool × d) (Bool × d) ℂ),
                hZs, Matrix.one_mul]
    rw [htr_cyc, hlog_conj, Matrix.mul_sub, Matrix.sub_mul, hZρ'Z,
      show (Z : Matrix (Bool × d) (Bool × d) ℂ) * ρ.mat * star (Z : Matrix (Bool × d) (Bool × d) ℂ) = ρ'.mat from rfl]
    rw [show ρ'.mat - ρ.mat = -(ρ.mat - ρ'.mat) by abel, Matrix.neg_mul, Matrix.trace_neg]
  have hneg_re : ((ρ.mat - ρ'.mat) * natLogMat ρ).trace.re = -((ρ.mat - ρ'.mat) * natLogMat ρ').trace.re := by
    have := congr_arg Complex.re hneg; simpa using this
  have hsum_tr : ((ρ.mat - ρ'.mat) * natLogMat ρ).trace.re - ((ρ.mat - ρ'.mat) * natLogMat ρ').trace.re =
      ((relEntropy ρ ρ').toReal + (relEntropy ρ' ρ).toReal) * Real.log 2 := by
    have h1 := (relEntropy_toReal_mul_log2 hρ hρ'_pd).2
    have h2 := (relEntropy_toReal_mul_log2 hρ'_pd hρ).2
    have hs1 := re_trace_self_mul_natLogMat ρ
    have hs2 := re_trace_self_mul_natLogMat ρ'
    have hdiff1 : ((ρ.mat - ρ'.mat) * natLogMat ρ).trace.re =
        (ρ.mat * natLogMat ρ).trace.re - (ρ'.mat * natLogMat ρ).trace.re := by
      rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    have hdiff2 : ((ρ.mat - ρ'.mat) * natLogMat ρ').trace.re =
        (ρ.mat * natLogMat ρ').trace.re - (ρ'.mat * natLogMat ρ').trace.re := by
      rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    rw [hdiff1, hdiff2, hs1, hs2]
    linarith
  linarith

/-! ### Part 2: Continuous-Time Dephasing Semigroup and Theorem 1.3 for Full-Rank States -/

/-- The dephasing semigroup parameter `p(t) = (1 - e^{-t}) / 2 ∈ [0, 1/2)` for `t ≥ 0`. -/
private noncomputable def dephaseP (t : ℝ) : ℝ := (1 - Real.exp (-t)) / 2

private lemma dephaseP_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ dephaseP t := by
  unfold dephaseP
  have hle : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

private lemma dephaseP_lt_half (t : ℝ) : dephaseP t < 1 / 2 := by
  unfold dephaseP
  have hpos : 0 < Real.exp (-t) := Real.exp_pos _
  linarith

private lemma dephaseP_le_one (t : ℝ) : dephaseP t ≤ 1 :=
  le_trans (le_of_lt (dephaseP_lt_half t)) (by norm_num)

/-- For `Ψ ≻ 0` and `p ∈ [0, 1/2]`, `dephaseState p Ψ ≻ 0`. -/
private lemma dephaseState_posDef {Ψ : DensityOp (Bool × d)} (hΨ : Ψ.mat.PosDef)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (dephaseState p hp0 (le_trans hp1 (by norm_num)) Ψ).mat.PosDef := by
  have hconj : (DensityOp.conjUnitary (pauliZTensorI d) Ψ).mat.PosDef :=
    conjUnitary_posDef hΨ (pauliZTensorI d)
  have h1 : ((1 - p : ℝ) • Ψ.mat).PosDef := hΨ.smul (by linarith : (0 : ℝ) < 1 - p)
  have h2 : (p • (DensityOp.conjUnitary (pauliZTensorI d) Ψ).mat).PosSemidef :=
    hconj.posSemidef.smul hp0
  simpa [dephaseState, DensityOp.mix, Complex.real_smul] using h1.add_posSemidef h2

/-- Semigroup difference identities along `t ↦ Ψ_t = dephaseState (dephaseP t) Ψ`. -/
private lemma dephaseState_semigroup_sub (Ψ : DensityOp (Bool × d)) {t h : ℝ}
    (ht : 0 ≤ t) (hh : 0 ≤ h) :
    let Ψt := dephaseState (dephaseP t) (dephaseP_nonneg ht) (dephaseP_le_one t) Ψ
    let Ψth := dephaseState (dephaseP (t + h)) (dephaseP_nonneg (by linarith)) (dephaseP_le_one (t + h)) Ψ
    let Ψt' := DensityOp.conjUnitary (pauliZTensorI d) Ψt
    let Ψth' := DensityOp.conjUnitary (pauliZTensorI d) Ψth
    Ψt.mat - Ψth.mat = (((Real.exp h - 1) / 2 : ℝ) : ℂ) • (Ψth.mat - Ψth'.mat) ∧
    Ψt.mat - Ψth.mat = (((1 - Real.exp (-h)) / 2 : ℝ) : ℂ) • (Ψt.mat - Ψt'.mat) := by
  intro Ψt Ψth Ψt' Ψth'
  set Z := pauliZTensorI d
  have hZ_self : (Z : Matrix (Bool × d) (Bool × d) ℂ) * (Z : Matrix (Bool × d) (Bool × d) ℂ) = 1 := by
    ext ⟨b, x⟩ ⟨c, y⟩
    simp only [Z, pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hpq : (b, x) = (c, y)
    · rcases Prod.mk.inj hpq with ⟨rfl, rfl⟩; simp only [↓reduceIte, Finset.sum_ite_eq', Finset.mem_univ]; cases b <;> simp
    · simp only [hpq, ↓reduceIte]
      apply Finset.sum_eq_zero; intro r _
      by_cases h1 : (b, x) = r
      · subst h1; simp [hpq]
      · simp [h1]
  have hZ_star : star (Z : Matrix (Bool × d) (Bool × d) ℂ) = (Z : Matrix (Bool × d) (Bool × d) ℂ) := by
    ext p q
    simp only [Z, pauliZTensorI, Matrix.star_apply, Matrix.diagonal_apply]
    by_cases hpq : q = p
    · subst hpq; cases q.1 <;> simp
    · simp [hpq, Ne.symm hpq]
  have hconj_dephase : ∀ (u : ℝ) (hu0 : 0 ≤ u),
      (DensityOp.conjUnitary Z (dephaseState (dephaseP u) (dephaseP_nonneg hu0) (dephaseP_le_one u) Ψ)).mat =
        ((dephaseP u : ℝ) : ℂ) • Ψ.mat + (((1 - dephaseP u : ℝ) : ℂ) • (DensityOp.conjUnitary Z Ψ).mat) := by
    intro u hu0
    have hZeq : (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) = (Z : Matrix (Bool × d) (Bool × d) ℂ) := rfl
    simp only [DensityOp.conjUnitary, dephaseState, DensityOp.mix, hZeq, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hZ_star]
    rw [← Matrix.mul_assoc (Z : Matrix (Bool × d) (Bool × d) ℂ) (Z : Matrix (Bool × d) (Bool × d) ℂ),
      hZ_self, Matrix.one_mul, Matrix.mul_one, add_comm]
    ext i j; simp [Complex.real_smul]
  have hdiff_u : ∀ (u : ℝ) (hu0 : 0 ≤ u),
      (dephaseState (dephaseP u) (dephaseP_nonneg hu0) (dephaseP_le_one u) Ψ).mat -
      (DensityOp.conjUnitary Z (dephaseState (dephaseP u) (dephaseP_nonneg hu0) (dephaseP_le_one u) Ψ)).mat =
        ((Real.exp (-u) : ℝ) : ℂ) • (Ψ.mat - (DensityOp.conjUnitary Z Ψ).mat) := by
    intro u hu0
    rw [hconj_dephase u hu0]
    ext i j
    simp only [dephaseState, DensityOp.mix, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul, dephaseP]
    push_cast; ring
  have hstep : Ψt.mat - Ψth.mat =
      (((Real.exp (-t) - Real.exp (-(t + h))) / 2 : ℝ) : ℂ) • (Ψ.mat - (DensityOp.conjUnitary Z Ψ).mat) := by
    ext i j
    simp only [Ψt, Ψth, dephaseState, DensityOp.mix, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Complex.real_smul, dephaseP]
    push_cast; ring
  rw [hstep, hdiff_u (t + h) (by linarith), hdiff_u t ht]
  constructor
  · rw [smul_smul]; congr 1
    rw [← Complex.ofReal_mul]; congr 1
    have hexp : Real.exp (-(t + h)) = Real.exp (-t) * Real.exp (-h) := by
      rw [← Real.exp_add]; congr 1; ring
    have hmul : Real.exp h * Real.exp (-h) = 1 := by rw [← Real.exp_add]; simp
    rw [hexp]
    calc (Real.exp (-t) - Real.exp (-t) * Real.exp (-h)) / 2
        = (Real.exp (-t) * (Real.exp h * Real.exp (-h)) - Real.exp (-t) * Real.exp (-h)) / 2 := by rw [hmul, mul_one]
      _ = (Real.exp h - 1) / 2 * (Real.exp (-t) * Real.exp (-h)) := by ring
  · rw [smul_smul]; congr 1
    rw [← Complex.ofReal_mul]; congr 1
    have hexp : Real.exp (-(t + h)) = Real.exp (-t) * Real.exp (-h) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp]; ring

/-- Pure real-analysis ODE contraction lemma for Theorem 1.3:
if `C : ℝ → ℝ` takes values in `[0, 1)`, is Lipschitz-decreasing with constant `L ≥ 0`,
and satisfies `C(t) - C(t + h) ≥ (e^h - 1) * φ(C(t + h))` for all `t, h ≥ 0`, then
`x(t) = 1 - 2 h₂⁻¹(1 - C(t))` satisfies `x(T) ≤ e^{-T} x(0)`. -/
private lemma ode_log_contraction (C : ℝ → ℝ) (T L : ℝ) (hT_nn : 0 ≤ T) (hL_nn : 0 ≤ L)
    (hC_bounds : ∀ t, 0 ≤ t → 0 ≤ C t ∧ C t < 1)
    (hstep_lower : ∀ t h, 0 ≤ t → 0 ≤ h → (Real.exp h - 1) * phi (C (t + h)) ≤ C t - C (t + h))
    (hstep_upper : ∀ t h, 0 ≤ t → 0 ≤ h → C t - C (t + h) ≤ L * h) :
    1 - 2 * h2Inv (1 - C T) ≤ Real.exp (-T) * (1 - 2 * h2Inv (1 - C 0)) := by
  let x : ℝ → ℝ := fun t ↦ 1 - 2 * h2Inv (1 - C t)
  have hx_eq : ∀ t (ht : 0 ≤ t), x t ∈ Ico (0 : ℝ) 1 ∧ C t = cParam (x t) ∧ phi (C t) = phiParam (x t) := by
    intro t ht
    obtain ⟨hC0', hC1'⟩ := hC_bounds t ht
    have hinv_mem : h2Inv (1 - C t) ∈ Icc (0 : ℝ) (1 / 2) := h2Inv_mem_Icc ⟨by linarith, by linarith⟩
    have hh2_inv : h2 (h2Inv (1 - C t)) = 1 - C t := h2_h2Inv ⟨by linarith, by linarith⟩
    have hx0 : 0 ≤ x t := by simp only [x]; linarith [hinv_mem.2]
    have hx1 : x t < 1 := by
      by_contra hge; push Not at hge
      have hinv0 : h2Inv (1 - C t) = 0 := by simp only [x] at hge; linarith [hinv_mem.1]
      rw [hinv0, h2_zero] at hh2_inv; linarith
    have hC_eq_c : C t = cParam (x t) := by
      unfold cParam; simp only [x]
      have harg : (1 - (1 - 2 * h2Inv (1 - C t))) / 2 = h2Inv (1 - C t) := by ring
      rw [harg, hh2_inv]; ring
    have hphi_eq : phi (C t) = phiParam (x t) := by
      unfold phi phiParam
      have harg : (1 + (1 - 2 * h2Inv (1 - C t))) / (1 - (1 - 2 * h2Inv (1 - C t))) =
          (1 - h2Inv (1 - C t)) / h2Inv (1 - C t) := by
        by_cases h0 : h2Inv (1 - C t) = 0
        · simp [h0]
        · field_simp [h0]; ring
      simp only [x, harg]
    exact ⟨⟨hx0, hx1⟩, hC_eq_c, hphi_eq⟩
  show x T ≤ Real.exp (-T) * x 0
  by_cases hCT0 : C T = 0
  · have hinv : h2Inv (1 - C T) = 1 / 2 := by rw [hCT0, sub_zero]; exact h2Inv_one
    have hxT0 : x T = 0 := by simp [x, hinv]
    rw [hxT0]
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hx_eq 0 le_rfl).1.1
  · have hCT_pos : 0 < C T := lt_of_le_of_ne (hC_bounds T hT_nn).1 (Ne.symm hCT0)
    have hC_anti : ∀ s t, 0 ≤ s → s ≤ t → C t ≤ C s := by
      intro s t hs hst
      have hstep := hstep_lower s (t - s) hs (by linarith)
      have hphi_nn : 0 ≤ phi (C t) := by
        rw [(hx_eq t (by linarith)).2.2]
        unfold phiParam
        have hx0 := (hx_eq t (by linarith)).1.1
        have hx1 := (hx_eq t (by linarith)).1.2
        have hge1 : 1 ≤ (1 + x t) / (1 - x t) := by rw [one_le_div (by linarith)]; linarith
        exact mul_nonneg (by linarith) (Real.logb_nonneg (by norm_num) hge1)
      have hexp_nn : 0 ≤ Real.exp (t - s) - 1 := by linarith [Real.add_one_le_exp (t - s)]
      rw [show s + (t - s) = t by ring] at hstep
      nlinarith
    have hC_cont : ContinuousOn C (Icc 0 T) := by
      rw [Metric.continuousOn_iff]
      intro t ht ε hε
      refine ⟨ε / (L + 1), div_pos hε (by linarith), fun s hs hdist ↦ ?_⟩
      rw [Real.dist_eq] at hdist ⊢
      rcases le_or_gt s t with hst | hts
      · have h1 := hC_anti s t hs.1 hst
        have h2 := hstep_upper s (t - s) hs.1 (by linarith)
        rw [show s + (t - s) = t by ring] at h2
        rw [abs_of_nonneg (by linarith)]
        have habs : t - s < ε / (L + 1) := by linarith [(abs_lt.mp hdist).1]
        have hL1 : L * (t - s) < (L + 1) * (ε / (L + 1)) := by nlinarith
        rw [mul_div_cancel₀ _ (by linarith : L + 1 ≠ 0)] at hL1; linarith
      · have h1 := hC_anti t s ht.1 (le_of_lt hts)
        have h2 := hstep_upper t (s - t) ht.1 (by linarith)
        rw [show t + (s - t) = s by ring] at h2
        rw [abs_of_nonpos (by linarith)]
        have habs : s - t < ε / (L + 1) := by linarith [(abs_lt.mp hdist).2]
        have hL1 : L * (s - t) < (L + 1) * (ε / (L + 1)) := by nlinarith
        rw [mul_div_cancel₀ _ (by linarith : L + 1 ≠ 0)] at hL1; linarith
    have hx_cont : ContinuousOn x (Icc 0 T) := by
      refine continuousOn_const.sub (continuousOn_const.mul ?_)
      refine continuousOn_h2Inv.comp (continuousOn_const.sub hC_cont) fun t ht ↦ ?_
      obtain ⟨h0, h1⟩ := hC_bounds t ht.1
      exact ⟨by linarith, by linarith⟩
    have hx_anti : ∀ s t, 0 ≤ s → s ≤ t → x t ≤ x s := by
      intro s t hs hst
      have hle : C t ≤ C s := hC_anti s t hs hst
      have hinv_le : h2Inv (1 - C s) ≤ h2Inv (1 - C t) := by
        have hs_mem : 1 - C s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [(hC_bounds s hs).2], by linarith [(hC_bounds s hs).1]⟩
        have ht_mem : 1 - C t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [(hC_bounds t (by linarith)).2], by linarith [(hC_bounds t (by linarith)).1]⟩
        by_contra hlt; push Not at hlt
        have h1 := strictMonoOn_h2 (h2Inv_mem_Icc ht_mem) (h2Inv_mem_Icc hs_mem) hlt
        rw [h2_h2Inv ht_mem, h2_h2Inv hs_mem] at h1
        linarith
      simp only [x]; linarith
    have hxT_pos : 0 < x T := by
      by_contra hle; push Not at hle
      have hxT0 : x T = 0 := le_antisymm hle (hx_eq T hT_nn).1.1
      have hCT' := (hx_eq T hT_nn).2.1
      rw [hxT0] at hCT'
      unfold cParam at hCT'; norm_num at hCT'; rw [h2_half] at hCT'; linarith
    have hx0_lt1 : x 0 < 1 := (hx_eq 0 le_rfl).1.2
    let cDeriv : ℝ → ℝ := fun u ↦ (1 / 2 : ℝ) * Real.logb 2 ((1 + u) / (1 - u))
    have hcParam_deriv : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivAt cParam (cDeriv u) u := by
      intro u hu
      have h1mu : 0 < 1 - u := by linarith [hu.2]
      have h1pu : 0 < 1 + u := by linarith [hu.1]
      have hhalf_mem : (1 - u) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hd_h2 := hasDerivAt_h2 hhalf_mem.1 hhalf_mem.2
      have hd_lin : HasDerivAt (fun v : ℝ ↦ (1 - v) / 2) (-1 / 2) u := by
        have h1 : HasDerivAt (fun v : ℝ ↦ 1 - v) (0 - 1) u :=
          (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)
        simpa using h1.div_const (2 : ℝ)
      have hcomp : HasDerivAt (fun v : ℝ ↦ 1 - h2 ((1 - v) / 2))
          (0 - Real.logb 2 ((1 - (1 - u) / 2) / ((1 - u) / 2)) * (-1 / 2)) u := by
        have h1 : HasDerivAt (h2 ∘ fun v : ℝ ↦ (1 - v) / 2)
            (Real.logb 2 ((1 - (1 - u) / 2) / ((1 - u) / 2)) * (-1 / 2)) u :=
          HasDerivAt.comp u hd_h2 hd_lin
        exact (hasDerivAt_const u (1 : ℝ)).sub h1
      have hderiv_eq : 0 - Real.logb 2 ((1 - (1 - u) / 2) / ((1 - u) / 2)) * (-1 / 2) = cDeriv u := by
        unfold cDeriv
        have harg : (1 - (1 - u) / 2) / ((1 - u) / 2) = (1 + u) / (1 - u) := by
          field_simp [ne_of_gt h1mu]; ring
        rw [harg]; ring
      rw [hderiv_eq] at hcomp
      exact hcomp
    have hcDeriv_mono : StrictMonoOn cDeriv (Ioo 0 1) := by
      intro u hu v hv huv
      unfold cDeriv
      apply mul_lt_mul_of_pos_left _ (by norm_num)
      apply Real.logb_lt_logb (by norm_num) (div_pos (by linarith [hu.1]) (by linarith [hu.2]))
      rw [div_lt_div_iff₀ (by linarith [hu.2]) (by linarith [hv.2])]; nlinarith
    have hcDeriv_pos : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < cDeriv u := by
      intro u hu
      unfold cDeriv
      apply mul_pos (by norm_num)
      exact Real.logb_pos (by norm_num) (by rw [one_lt_div (by linarith [hu.2])]; linarith [hu.1])
    have hcDeriv_cont : ContinuousOn cDeriv (Icc (x T) (x 0)) := by
      refine continuousOn_const.mul (ContinuousOn.div_const ?_ _)
      refine Real.continuousOn_log.comp ?_ ?_
      · exact (continuousOn_const.add continuousOn_id).div (continuousOn_const.sub continuousOn_id)
          fun u hu ↦ ne_of_gt (by linarith [hu.2])
      · intro u hu; exact ne_of_gt (div_pos (by linarith [hu.1]) (by linarith [hu.2]))
    have hlog_bound : ∀ ε : ℝ, 0 < ε → T ≤ (1 + ε) ^ 2 * (Real.log (x 0) - Real.log (x T)) := by
      intro ε hε
      rcases eq_or_lt_of_le hT_nn with hT0 | hT_pos
      · rw [← hT0]; simp
      have huc_cD := isCompact_Icc.uniformContinuousOn_of_continuous hcDeriv_cont
      have huc_x := isCompact_Icc.uniformContinuousOn_of_continuous hx_cont
      rw [Metric.uniformContinuousOn_iff] at huc_cD huc_x
      have hcDT_pos : 0 < cDeriv (x T) := hcDeriv_pos (x T) ⟨hxT_pos, lt_of_le_of_lt (hx_anti 0 T le_rfl hT_nn) hx0_lt1⟩
      obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := huc_cD (ε * cDeriv (x T)) (mul_pos hε hcDT_pos)
      set δ_x := min δ₁ (ε * x T)
      have hδx_pos : 0 < δ_x := lt_min hδ₁_pos (mul_pos hε hxT_pos)
      obtain ⟨δ_t, hδt_pos, hδt⟩ := huc_x δ_x hδx_pos
      obtain ⟨N, hN⟩ := exists_nat_gt (T / δ_t)
      have hN_pos : 0 < N := by
        by_contra h0; push Not at h0
        have hN0 : N = 0 := Nat.eq_zero_of_le_zero h0
        subst hN0; simp at hN; linarith [div_pos hT_pos hδt_pos]
      set h : ℝ := T / (N : ℝ)
      have hh_pos : 0 < h := div_pos hT_pos (Nat.cast_pos.mpr hN_pos)
      have hh_lt : h < δ_t := by
        rw [div_lt_iff₀ (Nat.cast_pos.mpr hN_pos)]
        have := (div_lt_iff₀ hδt_pos).mp hN; linarith
      have hstep_k : ∀ k ∈ Finset.range N,
          h ≤ (1 + ε) ^ 2 * (Real.log (x (k * h)) - Real.log (x ((k + 1) * h))) := by
        intro k hk
        have hk_lt : k < N := Finset.mem_range.mp hk
        have htk_nn : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) (le_of_lt hh_pos)
        have htk1_le : ((k + 1 : ℕ) : ℝ) * h ≤ T := by
          simp only [h]; rw [mul_div_assoc', div_le_iff₀ (Nat.cast_pos.mpr hN_pos)]
          have : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk_lt
          nlinarith
        have htk_le : (k : ℝ) * h ≤ T := by
          have : (k : ℝ) * h ≤ ((k + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
          linarith
        have htk1_eq : (k : ℝ) * h + h = ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
        set a := x ((k + 1) * h)
        set b := x (k * h)
        have hab : a ≤ b := by
          have := hx_anti (k * h) (((k + 1 : ℕ) : ℝ) * h) htk_nn (by push_cast; linarith)
          simpa [a, b, Nat.cast_add, Nat.cast_one] using this
        have ha_pos : 0 < a := lt_of_lt_of_le hxT_pos (by
          have := hx_anti (((k + 1 : ℕ) : ℝ) * h) T (by positivity) htk1_le
          simpa [a, Nat.cast_add, Nat.cast_one] using this)
        have hb_lt1 : b < 1 := lt_of_le_of_lt (hx_anti 0 (k * h) le_rfl htk_nn) hx0_lt1
        have hlow : h * (a * cDeriv a) ≤ C (k * h) - C (((k + 1 : ℕ) : ℝ) * h) := by
          have h1 := hstep_lower (k * h) h htk_nn (le_of_lt hh_pos)
          rw [htk1_eq] at h1
          have hphi_eq : phi (C (((k + 1 : ℕ) : ℝ) * h)) = a * cDeriv a := by
            rw [(hx_eq _ (by positivity)).2.2]
            unfold phiParam cDeriv
            simp only [a, Nat.cast_add, Nat.cast_one]; ring
          rw [hphi_eq] at h1
          have hexp : h ≤ Real.exp h - 1 := by linarith [Real.add_one_le_exp h]
          have ha_cD_nn : 0 ≤ a * cDeriv a := mul_nonneg (le_of_lt ha_pos) (le_of_lt (hcDeriv_pos a ⟨ha_pos, lt_of_le_of_lt hab hb_lt1⟩))
          nlinarith
        have hup : C (k * h) - C (((k + 1 : ℕ) : ℝ) * h) ≤ cDeriv b * (b - a) := by
          rw [(hx_eq (k * h) htk_nn).2.1, (hx_eq (((k + 1 : ℕ) : ℝ) * h) (by positivity)).2.1]
          have ha_eq : x (((k + 1 : ℕ) : ℝ) * h) = a := by simp only [a, Nat.cast_add, Nat.cast_one]
          rw [ha_eq]
          rcases eq_or_lt_of_le hab with heq | hlt
          · rw [heq, sub_self, sub_self, mul_zero]
          · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope cParam cDeriv hlt
              (fun u hu ↦ (hcParam_deriv u ⟨lt_of_lt_of_le ha_pos hu.1, lt_of_le_of_lt hu.2 hb_lt1⟩).continuousAt.continuousWithinAt)
              (fun u hu ↦ hcParam_deriv u ⟨lt_trans ha_pos hu.1, lt_trans hu.2 hb_lt1⟩)
            have hdiff : cParam b - cParam a = cDeriv ξ * (b - a) := by
              rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hlt))]
            rw [hdiff]
            have hcD_le : cDeriv ξ ≤ cDeriv b :=
              le_of_lt (hcDeriv_mono ⟨lt_trans ha_pos hξ.1, lt_trans hξ.2 hb_lt1⟩
                ⟨lt_of_lt_of_le ha_pos hab, hb_lt1⟩ hξ.2)
            exact mul_le_mul_of_nonneg_right hcD_le (sub_nonneg.mpr hab)
        have hdist_t : dist (k * h) (((k + 1 : ℕ) : ℝ) * h) < δ_t := by
          rw [Real.dist_eq, show (k : ℝ) * h - ((k + 1 : ℕ) : ℝ) * h = -h by push_cast; ring,
            abs_neg, abs_of_pos hh_pos]; exact hh_lt
        have hba_lt : b - a < δ_x := by
          have := hδt (k * h) ⟨htk_nn, htk_le⟩ (((k + 1 : ℕ) : ℝ) * h) ⟨by positivity, htk1_le⟩ hdist_t
          rw [Real.dist_eq] at this
          simpa [a, b, Nat.cast_add, Nat.cast_one, abs_of_nonneg (sub_nonneg.mpr hab)] using this
        have hb_le : b ≤ (1 + ε) * a := by
          have h1 : b - a < ε * x T := lt_of_lt_of_le hba_lt (min_le_right _ _)
          have ha_ge : x T ≤ a := by
            have := hx_anti (((k + 1 : ℕ) : ℝ) * h) T (by positivity) htk1_le
            simpa [a, Nat.cast_add, Nat.cast_one] using this
          nlinarith
        have hcDb_le : cDeriv b ≤ (1 + ε) * cDeriv a := by
          have hdist_x : dist b a < δ₁ := by
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hab)]
            exact lt_of_lt_of_le hba_lt (min_le_left _ _)
          have ha_mem : a ∈ Icc (x T) (x 0) :=
            ⟨by simpa [a, Nat.cast_add, Nat.cast_one] using hx_anti (((k + 1 : ℕ) : ℝ) * h) T (by positivity) htk1_le,
             by simpa [a, Nat.cast_add, Nat.cast_one] using hx_anti 0 (((k + 1 : ℕ) : ℝ) * h) le_rfl (by positivity)⟩
          have hb_mem : b ∈ Icc (x T) (x 0) :=
            ⟨hx_anti (k * h) T htk_nn htk_le, hx_anti 0 (k * h) le_rfl htk_nn⟩
          have h1 := hδ₁ b hb_mem a ha_mem hdist_x
          rw [Real.dist_eq] at h1
          have hcDa_ge : cDeriv (x T) ≤ cDeriv a := by
            rcases eq_or_lt_of_le ha_mem.1 with heq | hlt
            · rw [heq]
            · exact le_of_lt (hcDeriv_mono ⟨hxT_pos, lt_of_le_of_lt (hx_anti 0 T le_rfl hT_nn) hx0_lt1⟩
                ⟨ha_pos, lt_of_le_of_lt hab hb_lt1⟩ hlt)
          nlinarith [(abs_lt.mp h1).2]
        have hlog_step : (b - a) / b ≤ Real.log b - Real.log a := by
          have hb_pos : 0 < b := lt_of_lt_of_le ha_pos hab
          have h := Real.log_le_sub_one_of_pos (div_pos ha_pos hb_pos)
          rw [Real.log_div (ne_of_gt ha_pos) (ne_of_gt hb_pos)] at h
          have hrew : 1 - a / b = (b - a) / b := by field_simp [ne_of_gt hb_pos]
          linarith
        have hcDa_pos : 0 < cDeriv a := hcDeriv_pos a ⟨ha_pos, lt_of_le_of_lt hab hb_lt1⟩
        have hb_pos : 0 < b := lt_of_lt_of_le ha_pos hab
        have hcomb : h * (a * cDeriv a) ≤ (1 + ε) ^ 2 * (a * cDeriv a) * (Real.log b - Real.log a) := by
          have hba_log : b - a ≤ b * (Real.log b - Real.log a) := by
            have := mul_le_mul_of_nonneg_left hlog_step (le_of_lt hb_pos)
            rwa [mul_div_cancel₀ _ (ne_of_gt hb_pos)] at this
          have hlog_nn : 0 ≤ Real.log b - Real.log a := sub_nonneg.mpr (Real.log_le_log ha_pos hab)
          calc h * (a * cDeriv a)
              ≤ cDeriv b * (b - a) := le_trans hlow hup
            _ ≤ ((1 + ε) * cDeriv a) * (b * (Real.log b - Real.log a)) :=
                mul_le_mul hcDb_le hba_log (sub_nonneg.mpr hab) (mul_nonneg (by linarith) (le_of_lt hcDa_pos))
            _ = (1 + ε) * cDeriv a * b * (Real.log b - Real.log a) := by ring
            _ ≤ (1 + ε) * cDeriv a * ((1 + ε) * a) * (Real.log b - Real.log a) := by
                apply mul_le_mul_of_nonneg_right _ hlog_nn
                exact mul_le_mul_of_nonneg_left hb_le (mul_nonneg (by linarith) (le_of_lt hcDa_pos))
            _ = (1 + ε) ^ 2 * (a * cDeriv a) * (Real.log b - Real.log a) := by ring
        have hpos_acD : 0 < a * cDeriv a := mul_pos ha_pos hcDa_pos
        have hdiv := le_of_mul_le_mul_right (show h * (a * cDeriv a) ≤
            ((1 + ε) ^ 2 * (Real.log b - Real.log a)) * (a * cDeriv a) by linarith) hpos_acD
        simpa [a, b] using hdiv
      have hsum := Finset.sum_le_sum hstep_k
      have hlhs : ∑ _k ∈ Finset.range N, h = T := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, h]
        exact mul_div_cancel₀ T (Nat.cast_ne_zero.mpr (ne_of_gt hN_pos))
      have hrhs : ∑ k ∈ Finset.range N,
          (1 + ε) ^ 2 * (Real.log (x ((k : ℝ) * h)) - Real.log (x (((k : ℝ) + 1) * h))) =
          (1 + ε) ^ 2 * (Real.log (x 0) - Real.log (x T)) := by
        rw [← Finset.mul_sum]
        congr 1
        have htele := Finset.sum_range_sub' (fun k : ℕ ↦ Real.log (x ((k : ℝ) * h))) N
        have hN_eq : (N : ℝ) * h = T := mul_div_cancel₀ T (Nat.cast_ne_zero.mpr (ne_of_gt hN_pos))
        simp only [Nat.cast_zero, zero_mul, hN_eq] at htele
        convert htele using 2 with k
        push_cast; ring
      linarith
    have hT_le_log : T ≤ Real.log (x 0) - Real.log (x T) := by
      by_contra hgt; push Not at hgt
      set D := Real.log (x 0) - Real.log (x T)
      have hD_nn : 0 ≤ D := sub_nonneg.mpr (Real.log_le_log hxT_pos (hx_anti 0 T le_rfl hT_nn))
      set gap := T - D
      have hgap_pos : 0 < gap := sub_pos.mpr hgt
      set ε := min 1 (gap / (4 * (D + 1)))
      have hε_pos : 0 < ε := lt_min one_pos (div_pos hgap_pos (by linarith))
      have hε_le1 : ε ≤ 1 := min_le_left _ _
      have hε_le2 : ε ≤ gap / (4 * (D + 1)) := min_le_right _ _
      have hb := hlog_bound ε hε_pos
      have hsq : (1 + ε) ^ 2 * D ≤ D + 3 * ε * D := by nlinarith
      have h3ε : 3 * ε * D < gap := by
        have h1 : ε * (4 * (D + 1)) ≤ gap := (le_div_iff₀ (by linarith)).mp hε_le2
        nlinarith
      linarith
    have hx0_pos : 0 < x 0 := lt_of_lt_of_le hxT_pos (hx_anti 0 T le_rfl hT_nn)
    have hlog_eq : Real.log (x T) ≤ Real.log (Real.exp (-T) * x 0) := by
      rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hx0_pos), Real.log_exp]; linarith
    exact (Real.log_le_log_iff hxT_pos (mul_pos (Real.exp_pos _) hx0_pos)).mp hlog_eq

/-- **Theorem 1.3 for Full-Rank States** (`Ψ ≻ 0`). -/
private theorem theorem_1_3_dephasing_sdpi_posDef {Ψ : DensityOp (Bool × d)} (hΨ : Ψ.mat.PosDef)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) Ψ ≤
      1 - h2 (binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) p) := by
  -- Boundary case `p = 1/2`: LHS = 0, RHS = 1 - h2(1/2) = 0
  rcases eq_or_lt_of_le hp1 with rfl | hp_lt
  · have hC : dephaseCoherence (1 / 2) hp0 (by norm_num) Ψ = 0 := by
      unfold dephaseCoherence; ring
    have hbc : binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) (1 / 2) = 1 / 2 := by
      unfold binConv; ring
    rw [hC, hbc, h2_half]; norm_num
  -- Write `p = (1 - exp (-T)) / 2` with `T = -log(1 - 2p) ≥ 0`
  set T : ℝ := -Real.log (1 - 2 * p)
  have h12p_pos : 0 < 1 - 2 * p := by linarith
  have h12p_le1 : 1 - 2 * p ≤ 1 := by linarith
  have hT_nn : 0 ≤ T := by
    simp only [T, neg_nonneg]
    exact Real.log_nonpos (le_of_lt h12p_pos) h12p_le1
  have hpT : dephaseP T = p := by
    simp only [dephaseP, T, neg_neg, Real.exp_log h12p_pos]; ring
  -- Define `C(t) = dephaseCoherence (dephaseP t) Ψ` for `t ≥ 0`
  let Ψt : ∀ t : ℝ, 0 ≤ t → DensityOp (Bool × d) :=
    fun t ht ↦ dephaseState (dephaseP t) (dephaseP_nonneg ht) (dephaseP_le_one t) Ψ
  let C : ℝ → ℝ := fun t ↦
    if ht : 0 ≤ t then dephaseCoherence (dephaseP t) (dephaseP_nonneg ht) (dephaseP_le_one t) Ψ
    else 0
  have hC_eq : ∀ t (ht : 0 ≤ t),
      C t = dephaseCoherence (dephaseP t) (dephaseP_nonneg ht) (dephaseP_le_one t) Ψ := by
    intro t ht; simp [C, ht]
  have hC0 : C 0 = dephaseCoherence 0 le_rfl (by norm_num) Ψ := by
    rw [hC_eq 0 le_rfl]
    unfold dephaseCoherence
    have h0 : dephaseP 0 = 0 := by simp [dephaseP]
    have hmat : (dephaseState (dephaseP 0) (dephaseP_nonneg le_rfl) (dephaseP_le_one 0) Ψ).mat =
        (dephaseState 0 le_rfl (by norm_num) Ψ).mat := by
      simp [dephaseState, DensityOp.mix, h0]
    rw [vonNeumannEntropy_eq_of_mat_eq hmat]
  have hCT : C T = dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) Ψ := by
    rw [hC_eq T hT_nn]
    unfold dephaseCoherence
    have hmat : (dephaseState (dephaseP T) (dephaseP_nonneg hT_nn) (dephaseP_le_one T) Ψ).mat =
        (dephaseState p hp0 (le_trans hp1 (by norm_num)) Ψ).mat := by
      simp [dephaseState, DensityOp.mix, hpT]
    rw [vonNeumannEntropy_eq_of_mat_eq hmat]
  -- Bounds on `C(t)`: `0 ≤ C(t) < 1` for all `t ≥ 0`
  have hC_bounds : ∀ t (ht : 0 ≤ t), 0 ≤ C t ∧ C t < 1 := by
    intro t ht
    rw [hC_eq t ht, dephaseCoherence_eq_qjs]
    have hpd1 := dephaseState_posDef hΨ (dephaseP_nonneg ht) (le_of_lt (dephaseP_lt_half t))
    have hpd2 : (DensityOp.conjUnitary (pauliZTensorI d) (Ψt t ht)).mat.PosDef :=
      conjUnitary_posDef hpd1 (pauliZTensorI d)
    exact ⟨(qjs_eq_half_relEntropy_midpoint hpd1 hpd2).1, qjs_lt_one_posDef hpd1 hpd2⟩
  -- Key finite-step lower bound: `C(t) - C(t+h) ≥ (exp h - 1) * phi (C(t+h))`
  have hstep_lower : ∀ t h, 0 ≤ t → 0 ≤ h → (Real.exp h - 1) * phi (C (t + h)) ≤ C t - C (t + h) := by
    intro t h ht hh
    have hth : 0 ≤ t + h := by linarith
    have hpd_t := dephaseState_posDef hΨ (dephaseP_nonneg ht) (le_of_lt (dephaseP_lt_half t))
    have hpd_th := dephaseState_posDef hΨ (dephaseP_nonneg hth) (le_of_lt (dephaseP_lt_half (t + h)))
    have hpd_th' : (DensityOp.conjUnitary (pauliZTensorI d) (Ψt (t + h) hth)).mat.PosDef :=
      conjUnitary_posDef hpd_th (pauliZTensorI d)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hklein := entropy_sub_ge_trace_log hpd_t hpd_th
    have hsemi := (dephaseState_semigroup_sub Ψ ht hh).1
    have hsym := trace_diff_log_pauliZ hpd_th
    have hdiff_C : C t - C (t + h) = vonNeumannEntropy (Ψt (t + h) hth) - vonNeumannEntropy (Ψt t ht) := by
      rw [hC_eq t ht, hC_eq (t + h) hth]; unfold dephaseCoherence; ring
    have htr_eq : (((Ψt t ht).mat - (Ψt (t + h) hth).mat) * natLogMat (Ψt (t + h) hth)).trace.re =
        ((Real.exp h - 1) / 2) *
          (((Ψt (t + h) hth).mat - (DensityOp.conjUnitary (pauliZTensorI d) (Ψt (t + h) hth)).mat) *
            natLogMat (Ψt (t + h) hth)).trace.re := by
      dsimp only [Ψt]
      rw [hsemi, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [htr_eq, hsym, ← hdiff_C] at hklein
    have hqjjs := prop_3_3_qjjs_posDef hpd_th hpd_th'
    dsimp only [Ψt] at hqjjs hklein
    rw [← dephaseCoherence_eq_qjs (dephaseP (t + h)) (dephaseP_nonneg hth) (dephaseP_le_one (t + h)) Ψ,
      ← hC_eq (t + h) hth] at hqjjs
    have hexp_nn : 0 ≤ Real.exp h - 1 := by linarith [Real.add_one_le_exp h]
    have hmul1 : (Real.exp h - 1) * phi (C (t + h)) * Real.log 2 ≤ (C t - C (t + h)) * Real.log 2 := by
      have h1 := mul_le_mul_of_nonneg_left hqjjs hexp_nn
      have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hlog2)
      linarith
    exact le_of_mul_le_mul_right hmul1 hlog2
  -- Key finite-step upper bound (Lipschitz): `C(t) - C(t+h) ≤ L * h`
  obtain ⟨L, hL_nn, hstep_upper⟩ : ∃ L : ℝ, 0 ≤ L ∧
      ∀ t h, 0 ≤ t → 0 ≤ h → C t - C (t + h) ≤ L * h := by
    -- Lower bound all eigenvalues of `Ψ_t` by `lam_min = min_i Ψ.eigvals i > 0`
    have hne : Nonempty (Bool × d) := by
      by_contra h0
      haveI : IsEmpty (Bool × d) := not_nonempty_iff.mp h0
      have htr := Ψ.trace_one
      simp [Matrix.trace] at htr
    obtain ⟨i₀, _, hi₀_min⟩ := Finset.exists_min_image Finset.univ Ψ.eigvals Finset.univ_nonempty
    set lam_min := Ψ.eigvals i₀
    have hlam_pos : 0 < lam_min := hΨ.eigenvalues_pos i₀
    have hlam_le1 : lam_min ≤ 1 := by
      have htr : ∑ i : Bool × d, Ψ.eigvals i = 1 := by
        have hspec : Ψ.mat = (Ψ.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
            Matrix.diagonal (Complex.ofReal ∘ Ψ.eigvals) * star (Ψ.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) := by
          simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
            Unitary.conjStarAlgAut_apply] using Ψ.isHermitian.spectral_theorem
        have h1 := congr_arg (fun M : Matrix (Bool × d) (Bool × d) ℂ ↦ M.trace.re) hspec
        rw [Ψ.trace_one, Complex.one_re, Matrix.trace_mul_cycle,
          Unitary.coe_star_mul_self Ψ.eigUnitary, Matrix.one_mul, Matrix.trace_diagonal] at h1
        simpa [Complex.re_sum] using h1.symm
      have hle := Finset.single_le_sum (f := Ψ.eigvals) (fun i _ ↦ Ψ.eigvals_nonneg i) (Finset.mem_univ i₀)
      linarith
    -- Every eigenvalue of `Ψ_t` is `≥ lam_min`
    have heig_ge : ∀ (t : ℝ) (ht : 0 ≤ t) (j : Bool × d), lam_min ≤ (Ψt t ht).eigvals j := by
      intro t ht j
      -- `⟨v, Ψ_t v⟩ ≥ lam_min ‖v‖²` for every unit vector `v` (here the `j`-th eigenvector of `Ψ_t`)
      have hΨ_lb : ∀ v : Bool × d → ℂ, lam_min * (∑ k, ‖v k‖ ^ 2) ≤ (star v ⬝ᵥ Ψ.mat.mulVec v).re := by
        intro v
        rw [re_quadForm_spectral Ψ.isHermitian v]
        have hnorm : ∑ k : Bool × d, ‖((star (Ψ.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v) k‖ ^ 2 =
            ∑ k : Bool × d, ‖v k‖ ^ 2 := by
          have h1 : star ((star (Ψ.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v) ⬝ᵥ
              (star (Ψ.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v = star v ⬝ᵥ v := by
            rw [Matrix.dotProduct_mulVec]
            have hvec : star ((star (Ψ.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v) ᵥ*
                star (Ψ.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) =
                star v ᵥ* ((Ψ.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
                  star (Ψ.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)) := by
              ext k
              simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply, Matrix.star_apply,
                Matrix.mul_apply, star_sum, star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring
            have hUmul : (Ψ.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
                star (Ψ.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) = 1 :=
              Unitary.coe_mul_star_self Ψ.eigUnitary
            rw [hvec, hUmul, Matrix.vecMul_one]
          have hre := congr_arg Complex.re h1
          simp only [dotProduct, Pi.star_apply, Complex.re_sum] at hre
          convert hre using 1 <;>
            (apply Finset.sum_congr rfl; intro k _
             have hsq : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z ↦ by
               rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
             rw [hsq, Complex.ofReal_re])
        rw [← hnorm, Finset.mul_sum]
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hi₀_min k (Finset.mem_univ k)) (sq_nonneg _)
      set v : Bool × d → ℂ := fun r ↦ ((Ψt t ht).eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) r j
      have hv_norm : ∑ k, ‖v k‖ ^ 2 = 1 := by
        have h := congr_arg Complex.re (congr_fun (congr_fun (Unitary.coe_star_mul_self (Ψt t ht).eigUnitary) j) j)
        simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at h
        rw [← h]; apply Finset.sum_congr rfl; intro k _
        have hsq : star (v k) * v k = ((‖v k‖ ^ 2 : ℝ) : ℂ) := by
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [hsq, Complex.ofReal_re]
      have hv_eig : (star v ⬝ᵥ (Ψt t ht).mat.mulVec v).re = (Ψt t ht).eigvals j := by
        rw [re_quadForm_spectral (Ψt t ht).isHermitian v]
        have hcol : (star ((Ψt t ht).eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v = Pi.single j 1 := by
          ext k
          have h := congr_fun (congr_fun (Unitary.coe_star_mul_self (Ψt t ht).eigUnitary) k) j
          simpa [v, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
            Pi.single_apply, eq_comm] using h
        dsimp only [DensityOp.eigUnitary] at hcol
        rw [hcol, Finset.sum_eq_single j]
        · simp [DensityOp.eigvals]
        · intro k _ hkj; simp [Pi.single_eq_of_ne hkj]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [← hv_eig]
      have hquad_mix : (star v ⬝ᵥ (Ψt t ht).mat.mulVec v).re =
          (1 - dephaseP t) * (star v ⬝ᵥ Ψ.mat.mulVec v).re +
          dephaseP t * (star ((star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v) ⬝ᵥ
            Ψ.mat.mulVec ((star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v)).re := by
        have hq2 : star v ⬝ᵥ (DensityOp.conjUnitary (pauliZTensorI d) Ψ).mat.mulVec v =
            star ((star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v) ⬝ᵥ
              Ψ.mat.mulVec ((star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v) := by
          rw [DensityOp.conjUnitary, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
          congr 1; ext k
          simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply, Matrix.star_apply,
            star_sum, star_mul', star_star]
          apply Finset.sum_congr rfl; intro r _; ring
        simp only [Ψt, dephaseState, DensityOp.mix, Matrix.add_mulVec, Matrix.smul_mulVec,
          dotProduct_add, dotProduct_smul, Complex.add_re, Complex.real_smul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hq2]
      have hZv_norm : ∑ k, ‖((star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v) k‖ ^ 2 = 1 := by
        rw [← hv_norm]
        apply Finset.sum_congr rfl; intro k _
        simp only [pauliZTensorI, Matrix.mulVec, dotProduct, Matrix.star_apply, Matrix.diagonal_apply]
        rw [Finset.sum_eq_single k]
        · cases k.1 <;> simp
        · intro r _ hrk; simp [hrk]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hquad_mix]
      have hb1 := hΨ_lb v; rw [hv_norm, mul_one] at hb1
      have hb2 := hΨ_lb ((star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v)
      rw [hZv_norm, mul_one] at hb2
      have hp0' := dephaseP_nonneg ht
      have hp1' := le_of_lt (dephaseP_lt_half t)
      nlinarith
    refine ⟨-Real.log lam_min / Real.log 2, div_nonneg (neg_nonneg.mpr (Real.log_nonpos (le_of_lt hlam_pos) hlam_le1))
      (le_of_lt (Real.log_pos (by norm_num))), ?_⟩
    intro t h ht hh
    have hth : 0 ≤ t + h := by linarith
    have hpd_t := dephaseState_posDef hΨ (dephaseP_nonneg ht) (le_of_lt (dephaseP_lt_half t))
    have hpd_th := dephaseState_posDef hΨ (dephaseP_nonneg hth) (le_of_lt (dephaseP_lt_half (t + h)))
    have hpd_t' : (DensityOp.conjUnitary (pauliZTensorI d) (Ψt t ht)).mat.PosDef :=
      conjUnitary_posDef hpd_t (pauliZTensorI d)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    -- Apply Klein's inequality in the reverse direction: `(S(Ψ_t) - S(Ψ_{t+h})) log 2 ≥ ((Ψ_{t+h} - Ψ_t) log Ψ_t).trace.re`
    have hklein := entropy_sub_ge_trace_log hpd_th hpd_t
    have hsemi := (dephaseState_semigroup_sub Ψ ht hh).2
    have hsym := trace_diff_log_pauliZ hpd_t
    have hdiff_C : C t - C (t + h) = vonNeumannEntropy (Ψt (t + h) hth) - vonNeumannEntropy (Ψt t ht) := by
      rw [hC_eq t ht, hC_eq (t + h) hth]; unfold dephaseCoherence; ring
    have htr_eq : (((Ψt (t + h) hth).mat - (Ψt t ht).mat) * natLogMat (Ψt t ht)).trace.re =
        -((1 - Real.exp (-h)) / 2) *
          (((Ψt t ht).mat - (DensityOp.conjUnitary (pauliZTensorI d) (Ψt t ht)).mat) *
            natLogMat (Ψt t ht)).trace.re := by
      have hneg_sub : (Ψt (t + h) hth).mat - (Ψt t ht).mat = -((Ψt t ht).mat - (Ψt (t + h) hth).mat) := by abel
      dsimp only [Ψt] at hneg_sub ⊢
      rw [hneg_sub, hsemi, Matrix.neg_mul, Matrix.smul_mul, Matrix.trace_neg, Matrix.trace_smul,
        Complex.neg_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [htr_eq, hsym] at hklein
    -- Bound `D(Ψ_t ‖ Ψ̃_t) + D(Ψ̃_t ‖ Ψ_t) ≤ 2 * (-log lam_min / log 2)`
    have hD_ub : ∀ (A B : DensityOp (Bool × d)), A.mat.PosDef → B.mat.PosDef →
        (∀ j, lam_min ≤ B.eigvals j) → (relEntropy A B).toReal * Real.log 2 ≤ -Real.log lam_min := by
      intro A B hA hB hB_lb
      rw [(relEntropy_toReal_mul_log2 hA hB).2]
      have hSA_nn : 0 ≤ vonNeumannEntropy A := by
        unfold vonNeumannEntropy
        apply div_nonneg _ (le_of_lt hlog2)
        apply Finset.sum_nonneg; intro i _
        have h1 : A.eigvals i ≤ 1 := by
          have htr : ∑ k : Bool × d, A.eigvals k = 1 := by
            have hspec : A.mat = (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
                Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) := by
              simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
                Unitary.conjStarAlgAut_apply] using A.isHermitian.spectral_theorem
            have h1 := congr_arg (fun M : Matrix (Bool × d) (Bool × d) ℂ ↦ M.trace.re) hspec
            rw [A.trace_one, Complex.one_re, Matrix.trace_mul_cycle,
              Unitary.coe_star_mul_self A.eigUnitary, Matrix.one_mul, Matrix.trace_diagonal] at h1
            simpa [Complex.re_sum] using h1.symm
          linarith [Finset.single_le_sum (f := A.eigvals) (fun k _ ↦ A.eigvals_nonneg k) (Finset.mem_univ i)]
        exact Real.negMulLog_nonneg (A.eigvals_nonneg i) h1
      have hlogB_lb : Real.log lam_min ≤ (A.mat * natLogMat B).trace.re := by
        rw [re_trace_mul_natLogMat]
        set W : Matrix (Bool × d) (Bool × d) ℂ :=
          star (B.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) * (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)
        have hcol1 : ∀ i : Bool × d, ∑ j : Bool × d, ‖W j i‖ ^ 2 = 1 := by
          intro i
          have hU : star W * W = 1 := by
            simp only [W, Matrix.star_mul, star_star, Matrix.mul_assoc]
            have hBmul : (B.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
                star (B.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) = 1 :=
              Unitary.coe_mul_star_self B.eigUnitary
            have hAmul : star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
                (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) = 1 :=
              Unitary.coe_star_mul_self A.eigUnitary
            rw [← Matrix.mul_assoc (B.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ),
              hBmul, Matrix.one_mul, hAmul]
          have hii := congr_arg Complex.re (congr_fun (congr_fun hU i) i)
          simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re,
            Complex.re_sum] at hii
          rw [← hii]; apply Finset.sum_congr rfl; intro j _
          have hsq : star (W j i) * W j i = ((‖W j i‖ ^ 2 : ℝ) : ℂ) := by
            rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          rw [hsq, Complex.ofReal_re]
        have htrA : ∑ i : Bool × d, A.eigvals i = 1 := by
          have hspec : A.mat = (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
              Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) := by
            simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
              Unitary.conjStarAlgAut_apply] using A.isHermitian.spectral_theorem
          have h1 := congr_arg (fun M : Matrix (Bool × d) (Bool × d) ℂ ↦ M.trace.re) hspec
          rw [A.trace_one, Complex.one_re, Matrix.trace_mul_cycle,
            Unitary.coe_star_mul_self A.eigUnitary, Matrix.one_mul, Matrix.trace_diagonal] at h1
          simpa [Complex.re_sum] using h1.symm
        calc Real.log lam_min = ∑ i : Bool × d, (∑ j : Bool × d, ‖W j i‖ ^ 2) * (A.eigvals i * Real.log lam_min) := by
              simp_rw [hcol1, one_mul, ← Finset.sum_mul, htrA, one_mul]
          _ = ∑ i : Bool × d, ∑ j : Bool × d, ‖W j i‖ ^ 2 * (A.eigvals i * Real.log lam_min) := by
              apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_mul]
          _ ≤ ∑ i : Bool × d, ∑ j : Bool × d, ‖W j i‖ ^ 2 * (A.eigvals i * Real.log (B.eigvals j)) := by
              apply Finset.sum_le_sum; intro i _
              apply Finset.sum_le_sum; intro j _
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (Real.log_le_log hlam_pos (hB_lb j)) (A.eigvals_nonneg i)) (sq_nonneg _)
      nlinarith
    have heig_ge' : ∀ j, lam_min ≤ (DensityOp.conjUnitary (pauliZTensorI d) (Ψt t ht)).eigvals j := by
      intro j
      -- Same eigenvalues as `Ψt t ht`, or quadratic form lower bound directly via `hΨ`!
      set τ := DensityOp.conjUnitary (pauliZTensorI d) (Ψt t ht)
      set v : Bool × d → ℂ := fun r ↦ (τ.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) r j
      have hv_eig : (star v ⬝ᵥ τ.mat.mulVec v).re = τ.eigvals j := by
        rw [re_quadForm_spectral τ.isHermitian v]
        have hcol : (star (τ.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v = Pi.single j 1 := by
          ext k
          have h := congr_fun (congr_fun (Unitary.coe_star_mul_self τ.eigUnitary) k) j
          simpa [v, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
            Pi.single_apply, eq_comm] using h
        dsimp only [DensityOp.eigUnitary] at hcol
        rw [hcol, Finset.sum_eq_single j]
        · simp [DensityOp.eigvals]
        · intro k _ hkj; simp [Pi.single_eq_of_ne hkj]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [← hv_eig]
      set w : Bool × d → ℂ := (star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v
      have hq : star v ⬝ᵥ τ.mat.mulVec v = star w ⬝ᵥ (Ψt t ht).mat.mulVec w := by
        simp only [τ, w]
        rw [DensityOp.conjUnitary, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
        congr 1; ext k
        simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply, Matrix.star_apply,
          star_sum, star_mul', star_star]
        apply Finset.sum_congr rfl; intro r _; ring
      rw [hq, re_quadForm_spectral (Ψt t ht).isHermitian w]
      have hw_norm : ∑ k, ‖((star ((Ψt t ht).eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec w) k‖ ^ 2 = 1 := by
        have h1 : star ((star ((Ψt t ht).eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec w) ⬝ᵥ
            (star ((Ψt t ht).eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec w = star w ⬝ᵥ w := by
          rw [Matrix.dotProduct_mulVec]
          have hvec : star ((star ((Ψt t ht).eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec w) ᵥ*
              star ((Ψt t ht).eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) =
              star w ᵥ* (((Ψt t ht).eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
                star ((Ψt t ht).eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)) := by
            ext k
            simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply, Matrix.star_apply,
              Matrix.mul_apply, star_sum, star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring
          have hUmul : ((Ψt t ht).eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
              star ((Ψt t ht).eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) = 1 :=
            Unitary.coe_mul_star_self (Ψt t ht).eigUnitary
          rw [hvec, hUmul, Matrix.vecMul_one]
        have h2 : star w ⬝ᵥ w = star v ⬝ᵥ v := by
          simp only [w, Matrix.dotProduct_mulVec]
          have hvec : star ((star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v) ᵥ*
              star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) =
              star v ᵥ* ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) *
                star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)) := by
            ext k
            simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply, Matrix.star_apply,
              Matrix.mul_apply, star_sum, star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring
          have hZmul : (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) *
              star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) = 1 :=
            Unitary.coe_mul_star_self (pauliZTensorI d)
          rw [hvec, hZmul, Matrix.vecMul_one]
        have h3 : (star v ⬝ᵥ v).re = 1 := by
          have h := congr_arg Complex.re (congr_fun (congr_fun (Unitary.coe_star_mul_self τ.eigUnitary) j) j)
          simpa [v, dotProduct, Pi.star_apply, Matrix.mul_apply, Matrix.star_apply] using h
        have hre := congr_arg Complex.re (h1.trans h2)
        rw [h3] at hre
        simp only [dotProduct, Pi.star_apply, Complex.re_sum] at hre
        rw [← hre]; apply Finset.sum_congr rfl; intro k _
        have hsq : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z ↦ by
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [hsq, Complex.ofReal_re]
      calc lam_min = lam_min * ∑ k, ‖((star ((Ψt t ht).eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec w) k‖ ^ 2 := by
            rw [hw_norm, mul_one]
        _ = ∑ k, lam_min * ‖((star ((Ψt t ht).eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec w) k‖ ^ 2 :=
            Finset.mul_sum _ _ _
        _ ≤ _ := Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right (heig_ge t ht k) (sq_nonneg _)
    have hD1 := hD_ub (Ψt t ht) (DensityOp.conjUnitary (pauliZTensorI d) (Ψt t ht)) hpd_t hpd_t' heig_ge'
    have hD2 := hD_ub (DensityOp.conjUnitary (pauliZTensorI d) (Ψt t ht)) (Ψt t ht) hpd_t' hpd_t (heig_ge t ht)
    have h1me : 1 - Real.exp (-h) ≤ h := by linarith [Real.add_one_le_exp (-h)]
    have h1me_nn : 0 ≤ 1 - Real.exp (-h) := by linarith [Real.exp_le_one_iff.mpr (by linarith : -h ≤ 0)]
    have hloglam_nn : 0 ≤ -Real.log lam_min := neg_nonneg.mpr (Real.log_nonpos (le_of_lt hlam_pos) hlam_le1)
    have hmul : (C t - C (t + h)) * Real.log 2 ≤ (-Real.log lam_min) * h := by
      have hA : (C t - C (t + h)) * Real.log 2 ≤
          ((1 - Real.exp (-h)) / 4) *
            ((relEntropy (Ψt t ht) (DensityOp.conjUnitary (pauliZTensorI d) (Ψt t ht))).toReal * Real.log 2 +
             (relEntropy (DensityOp.conjUnitary (pauliZTensorI d) (Ψt t ht)) (Ψt t ht)).toReal * Real.log 2) := by
        dsimp only [Ψt] at hdiff_C ⊢
        rw [hdiff_C, ← add_mul]
        linarith
      have hB : ((relEntropy (Ψt t ht) (DensityOp.conjUnitary (pauliZTensorI d) (Ψt t ht))).toReal * Real.log 2 +
             (relEntropy (DensityOp.conjUnitary (pauliZTensorI d) (Ψt t ht)) (Ψt t ht)).toReal * Real.log 2) ≤
            2 * (-Real.log lam_min) := by linarith
      nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact hmul
  -- Apply `ode_log_contraction` to obtain `1 - 2 h₂⁻¹(1 - C(T)) ≤ e^{-T} (1 - 2 h₂⁻¹(1 - C(0)))`
  have hx_main : 1 - 2 * h2Inv (1 - C T) ≤ Real.exp (-T) * (1 - 2 * h2Inv (1 - C 0)) :=
    ode_log_contraction C T L hT_nn hL_nn hC_bounds hstep_lower hstep_upper
  -- Convert `x(T) ≤ exp(-T) * x(0)` back to `C(p) ≤ 1 - h2 (h2Inv (1 - C(0)) * p)`
  have hexp_eq : Real.exp (-T) = 1 - 2 * p := by
    simp only [T, neg_neg, Real.exp_log h12p_pos]
  rw [hexp_eq] at hx_main
  rw [hCT, hC0] at hx_main
  have hconv_id : (1 - 2 * p) * (1 - 2 * h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) =
      1 - 2 * binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) p := by
    unfold binConv; ring
  rw [hconv_id] at hx_main
  have hinv_ge : binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) p ≤
      h2Inv (1 - dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) Ψ) := by linarith
  have hconv_mem : binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) p ∈ Icc (0 : ℝ) (1 / 2) := by
    have h0m : h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ) ∈ Icc (0 : ℝ) (1 / 2) :=
      h2Inv_mem_Icc ⟨by linarith [(hC_bounds 0 le_rfl).2, hC0], by linarith [(hC_bounds 0 le_rfl).1, hC0]⟩
    unfold binConv; constructor <;> nlinarith [h0m.1, h0m.2]
  have hinvT_mem : h2Inv (1 - dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) Ψ) ∈ Icc (0 : ℝ) (1 / 2) :=
    h2Inv_mem_Icc ⟨by linarith [(hC_bounds T hT_nn).2, hCT], by linarith [(hC_bounds T hT_nn).1, hCT]⟩
  have hh2_le := strictMonoOn_h2.monotoneOn hconv_mem hinvT_mem hinv_ge
  rw [h2_h2Inv ⟨by linarith [(hC_bounds T hT_nn).2, hCT], by linarith [(hC_bounds T hT_nn).1, hCT]⟩] at hh2_le
  linarith

/-! ### Part 3: Theorem 1.3 for All Bipartite Density Operators and Equatorial Tightness -/

/-- **Theorem 1.3 (Nonlinear SDPI for Qubit Dephasing)**:
For every bipartite density operator `Ψ ∈ D(ℂ² ⊗ H_B)` and every dephasing parameter `p ∈ [0, 1/2]`,
`C(p) ≤ 1 - h₂(h₂⁻¹(1 - C(0)) * p)`. -/
theorem theorem_1_3_dephasing_sdpi (Ψ : DensityOp (Bool × d))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) Ψ ≤
      1 - h2 (binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) p) := by
  haveI : Nonempty (Bool × d) := by
    by_contra h0
    haveI : IsEmpty (Bool × d) := not_nonempty_iff.mp h0
    have htr := Ψ.trace_one
    simp [Matrix.trace] at htr
  -- Perturb `Ψ` by `Ψ_ε = (1 - ε) Ψ + ε I/(2|d|)` for `ε ∈ (0, 1)`
  let Ψε : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → DensityOp (Bool × d) :=
    fun ε h0 h1 ↦ DensityOp.mix ε h0 h1 Ψ (maxMixedState (Bool × d))
  -- Dephasing commutes with mixing with `maxMixedState` since `(Z ⊗ I) I (Z ⊗ I) = I`
  have hdeph_mix : ∀ (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1),
      (dephaseState q hq0 (le_trans hq1 (by norm_num)) (Ψε ε hε0 hε1)).mat =
        (DensityOp.mix ε hε0 hε1 (dephaseState q hq0 (le_trans hq1 (by norm_num)) Ψ) (maxMixedState (Bool × d))).mat := by
    intro q hq0 hq1 ε hε0 hε1
    have hZ_mul : (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) *
        star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) = 1 :=
      Unitary.coe_mul_star_self (pauliZTensorI d)
    have hZ_I : (DensityOp.conjUnitary (pauliZTensorI d) (maxMixedState (Bool × d))).mat =
        (maxMixedState (Bool × d)).mat := by
      simp only [DensityOp.conjUnitary, maxMixedState, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hZ_mul]
    ext i j
    simp only [Ψε, dephaseState, DensityOp.mix, DensityOp.conjUnitary, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    rw [show (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) * (maxMixedState (Bool × d)).mat *
        star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) = (maxMixedState (Bool × d)).mat from hZ_I]
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast; ring
  -- Define `fL(ε) = C_{Ψ_ε}(p)` and `fR(ε) = 1 - h2(binConv(h2Inv(1 - C_{Ψ_ε}(0)), p))`
  have hΨε_pd : ∀ (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1), (Ψε ε (le_of_lt hε0) (le_of_lt hε1)).mat.PosDef := by
    intro ε hε0 hε1
    have h1 : ((1 - ε : ℝ) • Ψ.mat).PosSemidef := Ψ.posSemidef.smul (by linarith)
    have h2 : (ε • (maxMixedState (Bool × d)).mat).PosDef := (maxMixedState_posDef' (Bool × d)).smul hε0
    simpa [Ψε, DensityOp.mix, add_comm] using h2.add_posSemidef h1
  let fC : ℝ → ℝ → ℝ := fun q ε ↦
    if h : 0 ≤ ε ∧ ε ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1 / 2 then
      dephaseCoherence q h.2.2.1 (le_trans h.2.2.2 (by norm_num)) (Ψε ε h.1 h.2.1)
    else 0
  have hfC_tendsto : ∀ (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2),
      Tendsto (fC q) (𝓝[>] (0 : ℝ)) (𝓝 (dephaseCoherence q hq0 (le_trans hq1 (by norm_num)) Ψ)) := by
    intro q hq0 hq1
    have h1 := tendsto_vonNeumannEntropy_mix_maxMixed (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)
    have h2 := tendsto_vonNeumannEntropy_mix_maxMixed (dephaseState q hq0 (le_trans hq1 (by norm_num)) Ψ)
    have hsub := h1.sub h2
    refine hsub.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have hε01 : 0 ≤ ε ∧ ε ≤ 1 := ⟨le_of_lt hε.1, le_of_lt hε.2⟩
    have hcond : 0 ≤ ε ∧ ε ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1 / 2 := ⟨le_of_lt hε.1, le_of_lt hε.2, hq0, hq1⟩
    dsimp only [fC]; rw [dif_pos hε01, dif_pos hε01, dif_pos hcond]; unfold dephaseCoherence
    have hm1 := hdeph_mix (1 / 2) (by norm_num) le_rfl ε (le_of_lt hε.1) (le_of_lt hε.2)
    have hm2 := hdeph_mix q hq0 hq1 ε (le_of_lt hε.1) (le_of_lt hε.2)
    rw [vonNeumannEntropy_eq_of_mat_eq hm1, vonNeumannEntropy_eq_of_mat_eq hm2]
  have hfL : Tendsto (fC p) (𝓝[>] (0 : ℝ)) (𝓝 (dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) Ψ)) :=
    hfC_tendsto p hp0 hp1
  have hf0 : Tendsto (fC 0) (𝓝[>] (0 : ℝ)) (𝓝 (dephaseCoherence 0 le_rfl (by norm_num) Ψ)) :=
    hfC_tendsto 0 le_rfl (by norm_num)
  have hC0_mem : 1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ ∈ Icc (0 : ℝ) 1 := by
    have hle1 : dephaseCoherence 0 le_rfl (by norm_num) Ψ ≤ 1 := by
      refine le_of_tendsto hf0 ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      have hcond : 0 ≤ ε ∧ ε ≤ 1 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 / 2 := ⟨le_of_lt hε.1, le_of_lt hε.2, le_rfl, by norm_num⟩
      dsimp only [fC]; rw [dif_pos hcond, dephaseCoherence_eq_qjs]
      have hpd1 := dephaseState_posDef (hΨε_pd ε hε.1 hε.2) le_rfl (by norm_num)
      have hpd2 := conjUnitary_posDef hpd1 (pauliZTensorI d)
      exact le_of_lt (qjs_lt_one_posDef hpd1 hpd2)
    have hnn : 0 ≤ dephaseCoherence 0 le_rfl (by norm_num) Ψ := by
      refine ge_of_tendsto hf0 ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      have hcond : 0 ≤ ε ∧ ε ≤ 1 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 / 2 := ⟨le_of_lt hε.1, le_of_lt hε.2, le_rfl, by norm_num⟩
      dsimp only [fC]; rw [dif_pos hcond, dephaseCoherence_eq_qjs]
      have hpd1 := dephaseState_posDef (hΨε_pd ε hε.1 hε.2) le_rfl (by norm_num)
      have hpd2 := conjUnitary_posDef hpd1 (pauliZTensorI d)
      exact (qjs_eq_half_relEntropy_midpoint hpd1 hpd2).1
    exact ⟨by linarith, by linarith⟩
  have hfR : Tendsto (fun ε ↦ 1 - h2 (binConv (h2Inv (1 - fC 0 ε)) p)) (𝓝[>] (0 : ℝ))
      (𝓝 (1 - h2 (binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) p))) := by
    have h1 : Tendsto (fun ε ↦ 1 - fC 0 ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) :=
      tendsto_const_nhds.sub hf0
    have hmem_ae : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 1 - fC 0 ε ∈ Icc (0 : ℝ) 1 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      have hcond : 0 ≤ ε ∧ ε ≤ 1 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 / 2 := ⟨le_of_lt hε.1, le_of_lt hε.2, le_rfl, by norm_num⟩
      dsimp only [fC]; rw [dif_pos hcond, dephaseCoherence_eq_qjs]
      have hpd1 := dephaseState_posDef (hΨε_pd ε hε.1 hε.2) le_rfl (by norm_num)
      have hpd2 := conjUnitary_posDef hpd1 (pauliZTensorI d)
      have hnn := (qjs_eq_half_relEntropy_midpoint hpd1 hpd2).1
      have hlt1 := qjs_lt_one_posDef hpd1 hpd2
      exact ⟨by linarith, by linarith⟩
    have h2 : Tendsto (fun ε ↦ h2Inv (1 - fC 0 ε)) (𝓝[>] (0 : ℝ))
        (𝓝 (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ))) :=
      (continuousOn_h2Inv _ hC0_mem).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 hmem_ae)
    have h3 : Tendsto (fun ε ↦ binConv (h2Inv (1 - fC 0 ε)) p) (𝓝[>] (0 : ℝ))
        (𝓝 (binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) p)) := by
      unfold binConv
      exact (h2.mul tendsto_const_nhds).add ((tendsto_const_nhds.sub h2).mul tendsto_const_nhds)
    exact tendsto_const_nhds.sub ((continuous_h2.tendsto _).comp h3)
  refine le_of_tendsto_of_tendsto hfL hfR ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  have hcond1 : 0 ≤ ε ∧ ε ≤ 1 ∧ 0 ≤ p ∧ p ≤ 1 / 2 := ⟨le_of_lt hε.1, le_of_lt hε.2, hp0, hp1⟩
  have hcond0 : 0 ≤ ε ∧ ε ≤ 1 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 / 2 := ⟨le_of_lt hε.1, le_of_lt hε.2, le_rfl, by norm_num⟩
  dsimp only [fC]; rw [dif_pos hcond1, dif_pos hcond0]
  exact theorem_1_3_dephasing_sdpi_posDef (hΨε_pd ε hε.1 hε.2) hp0 hp1

/-- Equatorial single-qubit state `Ψ_A(x) = ½ (I + x X)` on `Bool × Unit` for `x ∈ [0, 1]`. -/
noncomputable def equatorialState (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : DensityOp (Bool × Unit) where
  mat := Matrix.of fun p q ↦ if p.1 = q.1 then ((1 / 2 : ℝ) : ℂ) else ((x / 2 : ℝ) : ℂ)
  posSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · ext ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩; cases a <;> cases b <;> simp
    · intro v
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
        Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
      set a := v (false, ())
      set b := v (true, ())
      have hre_id : (star b * (↑(1 / 2 : ℝ) * b + ↑(x / 2 : ℝ) * a) +
          star a * (↑(x / 2 : ℝ) * b + ↑(1 / 2 : ℝ) * a)) =
          (((1 - x) / 2 : ℝ) : ℂ) * (star a * a + star b * b) +
          ((x / 2 : ℝ) : ℂ) * (star (a + b) * (a + b)) := by
        simp only [star_add]; push_cast; ring
      have hnn1 : (0 : ℂ) ≤ (((1 - x) / 2 : ℝ) : ℂ) * (star a * a + star b * b) := by
        have h1 : (0 : ℂ) ≤ (((1 - x) / 2 : ℝ) : ℂ) := by exact_mod_cast (by linarith : (0 : ℝ) ≤ (1 - x) / 2)
        have h2 : (0 : ℂ) ≤ star a * a := by
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          exact_mod_cast sq_nonneg ‖a‖
        have h3 : (0 : ℂ) ≤ star b * b := by
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          exact_mod_cast sq_nonneg ‖b‖
        exact mul_nonneg h1 (add_nonneg h2 h3)
      have hnn2 : (0 : ℂ) ≤ ((x / 2 : ℝ) : ℂ) * (star (a + b) * (a + b)) := by
        have h1 : (0 : ℂ) ≤ ((x / 2 : ℝ) : ℂ) := by exact_mod_cast (by linarith : (0 : ℝ) ≤ x / 2)
        have h2 : (0 : ℂ) ≤ star (a + b) * (a + b) := by
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          exact_mod_cast sq_nonneg ‖a + b‖
        exact mul_nonneg h1 h2
      simpa only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, a, b] using
        (by rw [hre_id]; exact add_nonneg hnn1 hnn2)
  trace_one := by
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_unique,
      Fintype.sum_bool, ↓reduceIte]
    push_cast; ring

/-- **Theorem 1.3 (Equatorial Equality)**: Every equatorial single-qubit state `½ (I + x X)`
(`x ∈ [0, 1]`) attains equality in Theorem 1.3 for every `p ∈ [0, 1/2]`. -/
theorem theorem_1_3_equatorial_equality {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1) =
      1 - h2 (binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) (equatorialState x hx0 hx1))) p) := by
  have hS_eq : ∀ (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
      vonNeumannEntropy (equatorialState r hr0 hr1) = h2 ((1 - r) / 2) := by
    intro r hr0 hr1
    -- Diagonalize `½ (I + r X)` via Hadamard `H`
    let H : Matrix.unitaryGroup (Bool × Unit) ℂ :=
      ⟨Matrix.of fun a b ↦ ((Real.sqrt 2 : ℂ)⁻¹) * (if a.1 = true ∧ b.1 = true then -1 else 1), by
        have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
          rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
            ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          push_cast; ring
        have hstar : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
          rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
        rw [Matrix.mem_unitaryGroup_iff']
        ext ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩
        simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply,
          Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
        cases a <;> cases b <;> simp [star_mul', hstar] <;>
          (have hm : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by rw [hstar] at hsq2; exact hsq2
           rw [hm]; ring)⟩
    have hdiag : (DensityOp.conjUnitary H (equatorialState r hr0 hr1)).mat =
        Matrix.diagonal (Complex.ofReal ∘ fun q : Bool × Unit ↦ if q.1 = false then (1 + r) / 2 else (1 - r) / 2) := by
      have hsq2 : ((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
        rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
          ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        push_cast; ring
      have hstar : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
        rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
      have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
        rw [hstar] at hsq2; exact hsq2
      ext ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩
      simp only [DensityOp.conjUnitary, equatorialState, H, Matrix.mul_apply, Matrix.star_apply,
        Matrix.of_apply, Matrix.diagonal_apply, Function.comp_apply,
        Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
      cases a <;> cases b <;>
        (simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, and_self, and_true, and_false,
          true_and, false_and, mul_one, mul_neg, neg_mul, star_mul', star_neg, star_one, hstar,
          Prod.mk.injEq, and_true];
         ring_nf;
         try (simp only [show ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) by rw [sq, hmul2]]; push_cast; ring))
    have hD : (Matrix.diagonal (Complex.ofReal ∘ fun q : Bool × Unit ↦
        if q.1 = false then (1 + r) / 2 else (1 - r) / 2)).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext q; simp
    rw [← vonNeumannEntropy_conjUnitary H (equatorialState r hr0 hr1)]
    unfold vonNeumannEntropy DensityOp.eigvals
    rw [h2_eq_negMulLog]; congr 1
    trans ∑ q : Bool × Unit, Real.negMulLog (hD.eigenvalues q)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow (DensityOp.conjUnitary H _).isHermitian hD
        (k := 0) (l := 0) (by rw [pow_zero, mul_one, mul_one, hdiag]) (by simp [Real.negMulLog])
    · rw [spectral_sum_diagonal _ hD (by simp [Real.negMulLog]), Fintype.sum_prod_type,
        Fintype.sum_bool]; simp only [Fintype.sum_unique]
      simp only [Bool.true_eq_false, ↓reduceIte]
      have h1m : 1 - (1 - r) / 2 = (1 + r) / 2 := by ring
      rw [h1m]
  have hdeph_eq : ∀ (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2),
      (dephaseState q hq0 (le_trans hq1 (by norm_num)) (equatorialState x hx0 hx1)).mat =
        (equatorialState ((1 - 2 * q) * x) (mul_nonneg (by linarith) hx0) (by nlinarith)).mat := by
    intro q hq0 hq1
    ext ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩
    simp only [dephaseState, DensityOp.mix, DensityOp.conjUnitary, pauliZTensorI, equatorialState,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
      Matrix.of_apply, Complex.real_smul, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
    cases a <;> cases b <;> simp <;> push_cast <;> ring
  have hC_val : ∀ (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2),
      dephaseCoherence q hq0 (le_trans hq1 (by norm_num)) (equatorialState x hx0 hx1) = 1 - h2 ((1 - (1 - 2 * q) * x) / 2) := by
    intro q hq0 hq1
    unfold dephaseCoherence
    rw [vonNeumannEntropy_eq_of_mat_eq (hdeph_eq (1 / 2) (by norm_num) le_rfl),
      vonNeumannEntropy_eq_of_mat_eq (hdeph_eq q hq0 hq1), hS_eq, hS_eq]
    have h0 : (1 - (1 - 2 * (1 / 2)) * x) / 2 = 1 / 2 := by ring
    rw [h0, h2_half]
  rw [hC_val p hp0 hp1, hC_val 0 le_rfl (by norm_num)]
  have h0 : (1 - (1 - 2 * 0) * x) / 2 = (1 - x) / 2 := by ring
  rw [h0, sub_sub_cancel, h2Inv_h2 ⟨by linarith, by linarith⟩]
  congr 2; unfold binConv; ring

end PolarCodes
