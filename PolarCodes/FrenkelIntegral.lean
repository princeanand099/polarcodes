/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.FrenkelHelpers

/-!
# Frenkel's Integral Formula (Theorem 6 / Eq. 3.7)

Proves **Frenkel's Integral Formula (Eq. 3.7)** (`relEntropy_frenkel_integral`) for full-rank
density operators `ρ, σ ≻ 0`:
`D(ρ ‖ σ) * log 2 = ∫⁻ t : ℝ, Tr(((1 - t) ρ + t σ)_-) / (|t| (t - 1)²) dt`.
-/

open Matrix BigOperators Real Set Filter Topology MeasureTheory
open scoped ComplexOrder ENNReal

namespace PolarCodes

variable {d : Type*} [Fintype d] [DecidableEq d]

set_option maxHeartbeats 8000000 in
/-- **Frenkel's Integral Formula (Theorem 6 / Eq. 3.7)** for full-rank density operators `ρ, σ ≻ 0`:
`D(ρ ‖ σ) * log 2 = ∫⁻ t : ℝ, Tr(((1 - t) ρ + t σ)_-) / (|t| (t - 1)²) dt`. -/
theorem relEntropy_frenkel_integral {ρ σ : DensityOp d}
    (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    relEntropy ρ σ * ENNReal.ofReal (Real.log 2) =
      ∫⁻ t : ℝ, ENNReal.ofReal (negPartTrace (show (((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat).IsHermitian by
        have h1 : (((1 - t : ℝ) : ℂ) • ρ.mat).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, ρ.isHermitian.eq]
        have h2 : ((t : ℂ) • σ.mat).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, σ.isHermitian.eq]
        exact h1.add h2) / (|t| * (t - 1) ^ 2)) ∂volume := by
  set α : d → ℝ := ρ.eigvals
  set β : d → ℝ := σ.eigvals
  set Uρ : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
  set Uσ : Matrix d d ℂ := (σ.eigUnitary : Matrix d d ℂ)
  set V : Matrix d d ℂ := star Uσ * Uρ
  have hα_pos : ∀ i : d, 0 < α i := fun i ↦ hρ.eigenvalues_pos i
  have hβ_pos : ∀ j : d, 0 < β j := fun j ↦ hσ.eigenvalues_pos j
  have hUρ_mul : Uρ * star Uρ = 1 := Unitary.coe_mul_star_self ρ.eigUnitary
  have hUρ_star : star Uρ * Uρ = 1 := Unitary.coe_star_mul_self ρ.eigUnitary
  have hUσ_mul : Uσ * star Uσ = 1 := Unitary.coe_mul_star_self σ.eigUnitary
  have hUσ_star : star Uσ * Uσ = 1 := Unitary.coe_star_mul_self σ.eigUnitary
  have hV_star_mul : star V * V = 1 := by
    simp only [V, star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uσ (star Uσ), hUσ_mul, Matrix.one_mul, hUρ_star]
  have hV_mul_star : V * star V = 1 := by
    simp only [V, star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uρ (star Uρ), hUρ_mul, Matrix.one_mul, hUσ_star]
  have hV_col : ∀ i : d, ∑ j : d, ‖V j i‖ ^ 2 = 1 := by
    intro i
    have h := congr_arg Complex.re (congr_fun (congr_fun hV_star_mul i) i)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at h
    convert h using 1
    apply Finset.sum_congr rfl; intro j _
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hV_row : ∀ j : d, ∑ i : d, ‖V j i‖ ^ 2 = 1 := by
    intro j
    have h := congr_arg Complex.re (congr_fun (congr_fun hV_mul_star j) j)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at h
    convert h using 1
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  -- Define shifted relative entropy `F(r)` and `g(r) = -F'(r)` for `r ≥ 0`
  let F : ℝ → ℝ := fun r ↦
    ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * ((α i + r) * (Real.log (α i + r) - Real.log (β j + r)))
  let g : ℝ → ℝ := fun r ↦
    (∑ j : d, Real.log (β j + r) - ∑ i : d, Real.log (α i + r)) -
      (Fintype.card d : ℝ) + ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * ((α i + r) / (β j + r))
  -- Step 1: `F(0) = relEntropy ρ σ * log 2`
  have hF0_eq : ENNReal.ofReal (F 0) = relEntropy ρ σ * ENNReal.ofReal (Real.log 2) := by
    have hsupp : suppSubset ρ σ := by
      intro i j _ hβ0; exact absurd hβ0 (ne_of_gt (hβ_pos j))
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    unfold relEntropy
    rw [if_pos hsupp, ← ENNReal.ofReal_mul (by
      have hnn : 0 ≤ F 0 := by
        have hterm : ∀ i j : d, α i - β j ≤ α i * (Real.log (α i) - Real.log (β j)) := by
          intro i j
          have hlog := Real.add_one_le_exp (Real.log (β j) - Real.log (α i))
          rw [Real.exp_sub, Real.exp_log (hβ_pos j), Real.exp_log (hα_pos i)] at hlog
          have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt (hα_pos i))
          have hcancel : α i * (β j / α i) = β j := mul_div_cancel₀ _ (ne_of_gt (hα_pos i))
          linarith
        calc (0 : ℝ) = ∑ i : d, α i - ∑ j : d, β j := by
              have h1 := ρ.sum_eigvals; have h2 := σ.sum_eigvals; linarith
          _ = ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * (α i - β j) := by
              simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hV_col, one_mul]
              congr 1; rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro j _
              rw [← Finset.sum_mul, hV_row, one_mul]
          _ ≤ F 0 := by
              apply Finset.sum_le_sum; intro i _
              apply Finset.sum_le_sum; intro j _
              simp only [add_zero]
              exact mul_le_mul_of_nonneg_left (hterm i j) (sq_nonneg _)
      exact div_nonneg (by simpa [F, α, β, V, Uρ, Uσ] using hnn) (le_of_lt hlog2_pos))]
    congr 1
    rw [div_mul_cancel₀ _ (ne_of_gt hlog2_pos)]
    simp [F, α, β, V, Uρ, Uσ]
  -- Step 2: `HasDerivAt F (-g r) r` and `ContinuousOn g (Ici 0)`
  have hF_deriv : ∀ r ≥ (0 : ℝ), HasDerivAt F (-g r) r := by
    intro r hr
    have hterm : ∀ i j : d, HasDerivAt
        (fun s : ℝ ↦ ‖V j i‖ ^ 2 * ((α i + s) * (Real.log (α i + s) - Real.log (β j + s))))
        (‖V j i‖ ^ 2 * (Real.log (α i + r) - Real.log (β j + r) + 1 - (α i + r) / (β j + r))) r := by
      intro i j
      have hαr : 0 < α i + r := by linarith [hα_pos i]
      have hβr : 0 < β j + r := by linarith [hβ_pos j]
      have h1 : HasDerivAt (fun s : ℝ ↦ α i + s) 1 r := by
        simpa using (hasDerivAt_const r (α i)).fun_add (hasDerivAt_id' r)
      have h2 : HasDerivAt (fun s : ℝ ↦ Real.log (α i + s)) (1 / (α i + r)) r := by
        simpa using h1.log (ne_of_gt hαr)
      have h3 : HasDerivAt (fun s : ℝ ↦ β j + s) 1 r := by
        simpa using (hasDerivAt_const r (β j)).fun_add (hasDerivAt_id' r)
      have h4 : HasDerivAt (fun s : ℝ ↦ Real.log (β j + s)) (1 / (β j + r)) r := by
        simpa using h3.log (ne_of_gt hβr)
      have hprod := h1.fun_mul (h2.fun_sub h4)
      convert hprod.const_mul (‖V j i‖ ^ 2) using 1
      field_simp [ne_of_gt hαr, ne_of_gt hβr]; ring
    have hsum : HasDerivAt F
        (∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 *
          (Real.log (α i + r) - Real.log (β j + r) + 1 - (α i + r) / (β j + r))) r := by
      have houter := HasDerivAt.fun_sum (u := Finset.univ)
        (fun i _ ↦ HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hterm i j))
      exact houter
    convert hsum using 1
    simp only [g]
    have hsplit : (∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 *
        (Real.log (α i + r) - Real.log (β j + r) + 1 - (α i + r) / (β j + r))) =
        (∑ i : d, Real.log (α i + r)) - (∑ j : d, Real.log (β j + r)) +
        (Fintype.card d : ℝ) - ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * ((α i + r) / (β j + r)) := by
      have h1 : ∀ i j : d, ‖V j i‖ ^ 2 * (Real.log (α i + r) - Real.log (β j + r) + 1 - (α i + r) / (β j + r)) =
          (‖V j i‖ ^ 2 * Real.log (α i + r) - ‖V j i‖ ^ 2 * Real.log (β j + r)) +
          (‖V j i‖ ^ 2 - ‖V j i‖ ^ 2 * ((α i + r) / (β j + r))) := fun i j ↦ by ring
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have ha : ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * Real.log (α i + r) = ∑ i : d, Real.log (α i + r) := by
        apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_mul, hV_col, one_mul]
      have hb : ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * Real.log (β j + r) = ∑ j : d, Real.log (β j + r) := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [← Finset.sum_mul, hV_row, one_mul]
      have hc : ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 = (Fintype.card d : ℝ) := by
        simp_rw [hV_col]; simp
      rw [ha, hb, hc]; ring
    linarith
  have hg_cont : ContinuousOn g (Ici 0) := by
    have hcont_sum : ∀ (s : Finset d) (f : d → ℝ → ℝ) (x : ℝ),
        (∀ i ∈ s, ContinuousAt (f i) x) → ContinuousAt (fun y ↦ ∑ i ∈ s, f i y) x := by
      intro s f x hf
      induction s using Finset.induction_on with
      | empty => simpa using continuousAt_const
      | @insert a s ha ih =>
        have heq : (fun y ↦ ∑ i ∈ insert a s, f i y) = fun y ↦ f a y + ∑ i ∈ s, f i y := by
          ext y; exact Finset.sum_insert ha
        rw [heq]
        exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
    intro r hr
    have h1 : ContinuousAt (fun s : ℝ ↦ ∑ j : d, Real.log (β j + s)) r :=
      hcont_sum Finset.univ _ r fun j _ ↦
        (Real.continuousAt_log (ne_of_gt (by linarith [hβ_pos j, Set.mem_Ici.mp hr] : 0 < β j + r))).comp
          (continuousAt_const.add continuousAt_id)
    have h2 : ContinuousAt (fun s : ℝ ↦ ∑ i : d, Real.log (α i + s)) r :=
      hcont_sum Finset.univ _ r fun i _ ↦
        (Real.continuousAt_log (ne_of_gt (by linarith [hα_pos i, Set.mem_Ici.mp hr] : 0 < α i + r))).comp
          (continuousAt_const.add continuousAt_id)
    have h3 : ContinuousAt (fun s : ℝ ↦ ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * ((α i + s) / (β j + s))) r :=
      hcont_sum Finset.univ _ r fun i _ ↦ hcont_sum Finset.univ _ r fun j _ ↦
        continuousAt_const.mul ((continuousAt_const.add continuousAt_id).div
          (continuousAt_const.add continuousAt_id)
          (ne_of_gt (by linarith [hβ_pos j, Set.mem_Ici.mp hr] : 0 < β j + r)))
    exact (((h1.sub h2).sub continuousAt_const).add h3).continuousWithinAt
  -- Step 3: `F(r) → 0` as `r → ∞`
  have hF_tendsto : Tendsto F atTop (𝓝 0) := by
    have hterm : ∀ i j : d, Tendsto
        (fun r : ℝ ↦ ‖V j i‖ ^ 2 * ((α i + r) * (Real.log (α i + r) - Real.log (β j + r))))
        atTop (𝓝 (‖V j i‖ ^ 2 * (α i - β j))) := by
      intro i j
      apply Tendsto.const_mul
      have hlo : ∀ᶠ r : ℝ in atTop,
          (α i + r) * ((α i - β j) / (α i + r)) ≤ (α i + r) * (Real.log (α i + r) - Real.log (β j + r)) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
        have hαr : 0 < α i + r := by linarith [hα_pos i]
        have hβr : 0 < β j + r := by linarith [hβ_pos j]
        have h1 : (β j + r) / (α i + r) ≤ Real.exp ((β j + r) / (α i + r) - 1) := by
          have := Real.add_one_le_exp ((β j + r) / (α i + r) - 1); linarith
        have h2 : Real.log ((β j + r) / (α i + r)) ≤ (β j + r) / (α i + r) - 1 := by
          have := Real.log_le_log (div_pos hβr hαr) h1
          rwa [Real.log_exp] at this
        rw [Real.log_div (ne_of_gt hβr) (ne_of_gt hαr)] at h2
        have h3 : (α i - β j) / (α i + r) ≤ Real.log (α i + r) - Real.log (β j + r) := by
          have : 1 - (β j + r) / (α i + r) = (α i - β j) / (α i + r) := by
            field_simp [ne_of_gt hαr]; ring
          linarith
        exact mul_le_mul_of_nonneg_left h3 (le_of_lt hαr)
      have hhi : ∀ᶠ r : ℝ in atTop,
          (α i + r) * (Real.log (α i + r) - Real.log (β j + r)) ≤ (α i + r) * ((α i - β j) / (β j + r)) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
        have hαr : 0 < α i + r := by linarith [hα_pos i]
        have hβr : 0 < β j + r := by linarith [hβ_pos j]
        have h1 : (α i + r) / (β j + r) ≤ Real.exp ((α i + r) / (β j + r) - 1) := by
          have := Real.add_one_le_exp ((α i + r) / (β j + r) - 1); linarith
        have h2 : Real.log ((α i + r) / (β j + r)) ≤ (α i + r) / (β j + r) - 1 := by
          have := Real.log_le_log (div_pos hαr hβr) h1
          rwa [Real.log_exp] at this
        rw [Real.log_div (ne_of_gt hαr) (ne_of_gt hβr)] at h2
        have h3 : Real.log (α i + r) - Real.log (β j + r) ≤ (α i - β j) / (β j + r) := by
          have : (α i + r) / (β j + r) - 1 = (α i - β j) / (β j + r) := by
            field_simp [ne_of_gt hβr]; ring
          linarith
        exact mul_le_mul_of_nonneg_left h3 (le_of_lt hαr)
      have hlo_lim : Tendsto (fun r : ℝ ↦ (α i + r) * ((α i - β j) / (α i + r))) atTop (𝓝 (α i - β j)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
        exact (mul_div_cancel₀ _ (ne_of_gt (by linarith [hα_pos i]))).symm
      have hhi_lim : Tendsto (fun r : ℝ ↦ (α i + r) * ((α i - β j) / (β j + r))) atTop (𝓝 (α i - β j)) := by
        have hrew : ∀ᶠ r : ℝ in atTop,
            (α i + r) * ((α i - β j) / (β j + r)) = (α i - β j) * (1 + (α i - β j) / (β j + r)) := by
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
          field_simp [ne_of_gt (by linarith [hβ_pos j] : 0 < β j + r)]; ring
        rw [tendsto_congr' hrew]
        have hinv : Tendsto (fun r : ℝ ↦ (α i - β j) / (β j + r)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_left atTop (β j) tendsto_id)
        simpa using (tendsto_const_nhds (x := α i - β j)).mul ((tendsto_const_nhds (x := (1 : ℝ))).add hinv)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_lim hhi_lim hlo hhi
    have hsum_lim := tendsto_finset_sum Finset.univ (fun i _ ↦
      tendsto_finset_sum Finset.univ (fun j _ ↦ hterm i j))
    have hsum_zero : ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * (α i - β j) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hV_col, one_mul]
      have h2 : ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * β j = ∑ j : d, β j := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [← Finset.sum_mul, hV_row, one_mul]
      rw [h2, ρ.sum_eigvals, σ.sum_eigvals, sub_self]
    rwa [hsum_zero] at hsum_lim
  -- Step 4: Spectral congruence `X(t, r) = S(r) (I + t M(r)) S(r)` for each `r > 0`
  have hg_pos_and_lintegral : ∀ r : ℝ, 0 < r →
      0 ≤ g r ∧
      ENNReal.ofReal (g r) =
        ∫⁻ t : ℝ, (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) *
          ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) ∂volume := by
    intro r hr
    let S : Matrix d d ℂ := Uρ * Matrix.diagonal (fun i ↦ ((Real.sqrt (α i + r) : ℝ) : ℂ)) * star Uρ
    let Sinv : Matrix d d ℂ := Uρ * Matrix.diagonal (fun i ↦ (((Real.sqrt (α i + r))⁻¹ : ℝ) : ℂ)) * star Uρ
    let Qinv : Matrix d d ℂ := Uσ * Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ)) * star Uσ
    have hS_herm : S.IsHermitian := by
      simp only [S, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
      congr 2; ext i j; simp [Matrix.diagonal_apply]
    have hSinv_herm : Sinv.IsHermitian := by
      simp only [Sinv, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
      congr 2; ext i j; simp [Matrix.diagonal_apply]
    have hdiag_r : Matrix.diagonal (fun _ : d ↦ (r : ℂ)) = (r : ℂ) • (1 : Matrix d d ℂ) := by
      ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]
    have hS_mul_Sinv : S * Sinv = 1 := by
      simp only [S, Sinv, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star Uρ) Uρ, hUρ_star, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      have hd : Matrix.diagonal (fun i : d ↦ ((Real.sqrt (α i + r) : ℝ) : ℂ) * (((Real.sqrt (α i + r))⁻¹ : ℝ) : ℂ)) = 1 := by
        rw [← Matrix.diagonal_one]; congr 1; ext i
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by linarith [hα_pos i]))), Complex.ofReal_one]
      rw [hd, Matrix.one_mul, hUρ_mul]
    have hSinv_mul_S : Sinv * S = 1 := by
      simp only [S, Sinv, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star Uρ) Uρ, hUρ_star, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      have hd : Matrix.diagonal (fun i : d ↦ (((Real.sqrt (α i + r))⁻¹ : ℝ) : ℂ) * ((Real.sqrt (α i + r) : ℝ) : ℂ)) = 1 := by
        rw [← Matrix.diagonal_one]; congr 1; ext i
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by linarith [hα_pos i]))), Complex.ofReal_one]
      rw [hd, Matrix.one_mul, hUρ_mul]
    have hS_sq : S * S = ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ) := by
      have hρ_spec : ρ.mat = Uρ * Matrix.diagonal (Complex.ofReal ∘ α) * star Uρ := by
        simpa [Uρ, α, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
      have hI_spec : (r : ℂ) • (1 : Matrix d d ℂ) = Uρ * Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star Uρ := by
        rw [hdiag_r, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUρ_mul]
      simp only [S, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star Uρ) Uρ, hUρ_star, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      have hd : Matrix.diagonal (fun i : d ↦ ((Real.sqrt (α i + r) : ℝ) : ℂ) * ((Real.sqrt (α i + r) : ℝ) : ℂ)) =
          Matrix.diagonal (Complex.ofReal ∘ α) + Matrix.diagonal (fun _ : d ↦ (r : ℂ)) := by
        ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
        split_ifs
        · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith [hα_pos i]), Complex.ofReal_add]
        · simp
      rw [hd, Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hρ_spec, ← hI_spec]
    have hQ_mul_Qinv : (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Qinv = 1 := by
      have hσ_spec : σ.mat = Uσ * Matrix.diagonal (Complex.ofReal ∘ β) * star Uσ := by
        simpa [Uσ, β, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
      have hI_spec : (r : ℂ) • (1 : Matrix d d ℂ) = Uσ * Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star Uσ := by
        rw [hdiag_r, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUσ_mul]
      have hQ_spec : σ.mat + (r : ℂ) • (1 : Matrix d d ℂ) =
          Uσ * Matrix.diagonal (fun j ↦ ((β j + r : ℝ) : ℂ)) * star Uσ := by
        rw [hσ_spec, hI_spec, ← Matrix.add_mul, ← Matrix.mul_add]
        congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
        split_ifs <;> simp [Complex.ofReal_add]
      rw [hQ_spec]
      simp only [Qinv, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star Uσ) Uσ, hUσ_star, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      have hd : Matrix.diagonal (fun j : d ↦
          ((β j + r : ℝ) : ℂ) * (((β j + r)⁻¹ : ℝ) : ℂ)) = 1 := by
        rw [← Matrix.diagonal_one]; congr 1; ext j
        rw [← Complex.ofReal_mul,
          mul_inv_cancel₀ (ne_of_gt (by linarith [hβ_pos j] : 0 < β j + r)), Complex.ofReal_one]
      rw [hd, Matrix.one_mul, hUσ_mul]
    let M : Matrix d d ℂ := Sinv * (σ.mat - ρ.mat) * Sinv
    have hM_herm : M.IsHermitian := by
      simp only [M, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
        hSinv_herm.eq, σ.isHermitian.eq, ρ.isHermitian.eq, Matrix.mul_assoc]
    have hUM_mul : (hM_herm.eigenvectorUnitary : Matrix d d ℂ) * star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_mul_star_self hM_herm.eigenvectorUnitary
    have hUM_star : star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) * (hM_herm.eigenvectorUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_star_mul_self hM_herm.eigenvectorUnitary
    have h1pM : 1 + M = Sinv * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Sinv := by
      have h1 : (1 : Matrix d d ℂ) = Sinv * (ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Sinv := by
        calc (1 : Matrix d d ℂ) = (Sinv * S) * (S * Sinv) := by rw [hSinv_mul_S, hS_mul_Sinv, Matrix.mul_one]
          _ = Sinv * (S * S) * Sinv := by simp [Matrix.mul_assoc]
          _ = Sinv * (ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Sinv := by rw [hS_sq]
      conv_lhs => rw [h1]
      simp only [M, ← Matrix.add_mul, ← Matrix.mul_add]
      congr 2; abel
    have h1pM_herm : (1 + M).IsHermitian := Matrix.isHermitian_one.add hM_herm
    have h1pM_pos : (1 + M).PosDef := by
      rw [h1pM, Matrix.posDef_iff_dotProduct_mulVec]
      refine ⟨h1pM ▸ h1pM_herm, fun x hx ↦ ?_⟩
      have hQ_pos : (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).PosDef := by
        have hrI_herm : ((r : ℂ) • (1 : Matrix d d ℂ)).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
            Complex.star_def, Complex.conj_ofReal]
        rw [Matrix.posDef_iff_dotProduct_mulVec]
        refine ⟨σ.isHermitian.add hrI_herm, fun y hy ↦ ?_⟩
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
          dotProduct_smul, smul_eq_mul]
        have hσ_y := (Matrix.posDef_iff_dotProduct_mulVec.mp hσ).2 hy
        have hy_pos : (0 : ℂ) < star y ⬝ᵥ y := by
          rw [Complex.pos_iff]
          have hre : (star y ⬝ᵥ y).re = ∑ i : d, ‖y i‖ ^ 2 := by
            simp only [dotProduct, Pi.star_apply, Complex.re_sum]
            apply Finset.sum_congr rfl; intro i _
            rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
          have him : (star y ⬝ᵥ y).im = 0 := by
            simp only [dotProduct, Pi.star_apply, Complex.im_sum]
            apply Finset.sum_eq_zero; intro i _
            rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_im]
          have hre_pos : 0 < (star y ⬝ᵥ y).re := by
            rw [hre]
            obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
              by_contra h; exact hy (funext fun i ↦ by_contra fun hi ↦ h ⟨i, hi⟩)
            exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hi))
              (Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖y j‖) (Finset.mem_univ i))
          exact ⟨hre_pos, him.symm⟩
        have hr_c : (0 : ℂ) < (r : ℂ) := by rw [Complex.pos_iff]; exact ⟨hr, rfl⟩
        exact add_pos hσ_y (mul_pos hr_c hy_pos)
      have hSinv_x : Sinv.mulVec x ≠ 0 := by
        intro h0
        have := congr_arg (Matrix.mulVec S) h0
        rw [Matrix.mulVec_mulVec, hS_mul_Sinv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
        exact hx this
      have hquad : star x ⬝ᵥ (Sinv * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Sinv).mulVec x =
          star (Sinv.mulVec x) ⬝ᵥ (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).mulVec (Sinv.mulVec x) := by
        have hstar_Sinv : star (Sinv.mulVec x) = (star x) ᵥ* Sinv := by
          ext i
          simp only [Pi.star_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, star_sum, star_mul']
          apply Finset.sum_congr rfl; intro j _
          have hji : star (Sinv i j) = Sinv j i := by
            have := congr_fun (congr_fun hSinv_herm.eq j) i
            simpa [Matrix.conjTranspose_apply] using this
          rw [hji]; ring
        calc star x ⬝ᵥ (Sinv * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Sinv).mulVec x
            = star x ⬝ᵥ Sinv.mulVec (((σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Sinv).mulVec x) := by
                rw [Matrix.mul_assoc Sinv, Matrix.mulVec_mulVec]
          _ = ((star x) ᵥ* Sinv) ⬝ᵥ (((σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Sinv).mulVec x) := by
                rw [Matrix.dotProduct_mulVec]
          _ = star (Sinv.mulVec x) ⬝ᵥ (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).mulVec (Sinv.mulVec x) := by
                rw [← hstar_Sinv, Matrix.mulVec_mulVec]
      rw [hquad]
      exact (Matrix.posDef_iff_dotProduct_mulVec.mp hQ_pos).2 hSinv_x
    have hlam_gt : ∀ k : d, -1 < hM_herm.eigenvalues k := by
      intro k
      let v : d → ℂ := fun i ↦ (hM_herm.eigenvectorUnitary : Matrix d d ℂ) i k
      have hv_ne : v ≠ 0 := by
        intro h0
        have hu := congr_fun (congr_fun (hUM_star) k) k
        simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hu
        have hzero : ∑ i : d, star ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) i k) *
            (hM_herm.eigenvectorUnitary : Matrix d d ℂ) i k = 0 := by
          apply Finset.sum_eq_zero; intro i _; have := congr_fun h0 i; simp [v] at this; simp [this]
        rw [hzero] at hu; exact zero_ne_one hu
      have hpos_v := (Matrix.posDef_iff_dotProduct_mulVec.mp h1pM_pos).2 hv_ne
      have hval_v : (star v ⬝ᵥ (1 + M).mulVec v).re = 1 + hM_herm.eigenvalues k := by
        rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.add_re]
        have h1 : (star v ⬝ᵥ v).re = 1 := by
          have hu := congr_arg Complex.re (congr_fun (congr_fun (hUM_star) k) k)
          simpa [dotProduct, Matrix.mul_apply, Matrix.star_apply, Pi.star_apply, v] using hu
        have h2 : (star v ⬝ᵥ M.mulVec v).re = hM_herm.eigenvalues k := by
          rw [re_quadForm_spectral hM_herm v]
          have horth : ∀ i : d, ((star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)).mulVec v) i =
              if i = k then 1 else 0 := by
            intro i
            have hu := congr_fun (congr_fun (hUM_star) i) k
            simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply, v, Matrix.one_apply] using hu
          simp_rw [horth]
          rw [Finset.sum_eq_single k]
          · simp
          · intro i _ hik; simp [hik]
          · intro h; exact absurd (Finset.mem_univ k) h
        linarith
      have hre_pos : 0 < (star v ⬝ᵥ (1 + M).mulVec v).re := (Complex.pos_iff.mp hpos_v).1
      linarith
    have hg_spectral : g r = ∑ k : d, (Real.log (1 + hM_herm.eigenvalues k) -
        hM_herm.eigenvalues k / (1 + hM_herm.eigenvalues k)) := by
      have hdet_eq : ∏ k : d, (1 + hM_herm.eigenvalues k) =
          (∏ j : d, (β j + r)) / (∏ i : d, (α i + r)) := by
        have h1 : (1 + M).det = (∏ k : d, ((1 + hM_herm.eigenvalues k : ℝ) : ℂ)) := by
          have hspec : 1 + M = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
              Matrix.diagonal (fun k ↦ ((1 + hM_herm.eigenvalues k : ℝ) : ℂ)) *
              star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
            have hM_spec : M = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                Matrix.diagonal (Complex.ofReal ∘ hM_herm.eigenvalues) *
                star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
              simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM_herm.spectral_theorem
            have hI_spec : (1 : Matrix d d ℂ) = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
                star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
              rw [Matrix.diagonal_one, Matrix.mul_one, hUM_mul]
            calc (1 : Matrix d d ℂ) + M
                = ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) * Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
                    star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)) +
                  ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                    Matrix.diagonal (Complex.ofReal ∘ hM_herm.eigenvalues) *
                    star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)) := congr_arg₂ (· + ·) hI_spec hM_spec
              _ = _ := by
                  rw [← Matrix.add_mul, ← Matrix.mul_add]
                  congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
                  split_ifs <;> simp [Complex.ofReal_add]
          conv_lhs => rw [hspec]
          rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
            hUM_mul, Matrix.det_one, one_mul,
            Matrix.det_diagonal]
        have h2 : (1 + M).det * (ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det =
            (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det := by
          have hdet1 : (Sinv * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Sinv).det =
              Sinv.det * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det * Sinv.det := by
            rw [Matrix.det_mul (Sinv * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ))) Sinv,
              Matrix.det_mul Sinv (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ))]
          have hdet2 : (S * S).det = S.det * S.det := Matrix.det_mul S S
          rw [h1pM, ← hS_sq, hdet1, hdet2]
          calc Sinv.det * (σ.mat + (r : ℂ) • 1).det * Sinv.det * (S.det * S.det)
              = (Sinv.det * S.det) * (Sinv.det * S.det) * (σ.mat + (r : ℂ) • 1).det := by ring
            _ = (Sinv * S).det * (Sinv * S).det * (σ.mat + (r : ℂ) • 1).det := by rw [← Matrix.det_mul Sinv S]
            _ = (σ.mat + (r : ℂ) • 1).det := by rw [hSinv_mul_S, Matrix.det_one]; ring
        have hdetP : (ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det = ∏ i : d, ((α i + r : ℝ) : ℂ) := by
          have hP_spec : ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ) =
              Uρ * Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * star Uρ := by
            have hρ_spec : ρ.mat = Uρ * Matrix.diagonal (Complex.ofReal ∘ α) * star Uρ := by
              simpa [Uρ, α, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
                Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
            have hI_spec : (r : ℂ) • (1 : Matrix d d ℂ) = Uρ * Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star Uρ := by
              rw [hdiag_r, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUρ_mul]
            rw [hρ_spec, hI_spec, ← Matrix.add_mul, ← Matrix.mul_add]
            congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
            split_ifs <;> simp [Complex.ofReal_add]
          rw [hP_spec, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
            hUρ_mul, Matrix.det_one, one_mul, Matrix.det_diagonal]
        have hdetQ : (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det = ∏ j : d, ((β j + r : ℝ) : ℂ) := by
          have hQ_spec : σ.mat + (r : ℂ) • (1 : Matrix d d ℂ) =
              Uσ * Matrix.diagonal (fun j ↦ ((β j + r : ℝ) : ℂ)) * star Uσ := by
            have hσ_spec : σ.mat = Uσ * Matrix.diagonal (Complex.ofReal ∘ β) * star Uσ := by
              simpa [Uσ, β, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
                Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
            have hI_spec : (r : ℂ) • (1 : Matrix d d ℂ) = Uσ * Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star Uσ := by
              rw [hdiag_r, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUσ_mul]
            rw [hσ_spec, hI_spec, ← Matrix.add_mul, ← Matrix.mul_add]
            congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
            split_ifs <;> simp [Complex.ofReal_add]
          rw [hQ_spec, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
            hUσ_mul, Matrix.det_one, one_mul, Matrix.det_diagonal]
        rw [h1, hdetP, hdetQ] at h2
        have h2_re := congr_arg Complex.re h2
        simp only [← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_re] at h2_re
        have hP_pos : 0 < ∏ i : d, (α i + r) := Finset.prod_pos fun i _ ↦ by linarith [hα_pos i]
        exact (eq_div_iff (ne_of_gt hP_pos)).mpr h2_re
      have hlog_sum : ∑ k : d, Real.log (1 + hM_herm.eigenvalues k) =
          ∑ j : d, Real.log (β j + r) - ∑ i : d, Real.log (α i + r) := by
        rw [← Real.log_prod (fun k _ ↦ ne_of_gt (by linarith [hlam_gt k])), hdet_eq,
          Real.log_div (ne_of_gt (Finset.prod_pos fun j _ ↦ by linarith [hβ_pos j]))
            (ne_of_gt (Finset.prod_pos fun i _ ↦ by linarith [hα_pos i])),
          Real.log_prod (fun j _ ↦ ne_of_gt (by linarith [hβ_pos j])),
          Real.log_prod (fun i _ ↦ ne_of_gt (by linarith [hα_pos i]))]
      have htr_inv : ∑ k : d, (1 + hM_herm.eigenvalues k)⁻¹ =
          ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * ((α i + r) / (β j + r)) := by
        let inv1pM : Matrix d d ℂ := (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
          Matrix.diagonal (fun k ↦ (((1 + hM_herm.eigenvalues k)⁻¹ : ℝ) : ℂ)) *
          star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)
        have hinv_eq : inv1pM = S * Qinv * S := by
          have h1 : (1 + M) * inv1pM = 1 := by
            have hspec : 1 + M = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                Matrix.diagonal (fun k ↦ ((1 + hM_herm.eigenvalues k : ℝ) : ℂ)) *
                star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
              have hM_spec : M = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                  Matrix.diagonal (Complex.ofReal ∘ hM_herm.eigenvalues) *
                  star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
                simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM_herm.spectral_theorem
              have hI_spec : (1 : Matrix d d ℂ) = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                  Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
                  star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
                rw [Matrix.diagonal_one, Matrix.mul_one, hUM_mul]
              calc (1 : Matrix d d ℂ) + M
                  = ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) * Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
                      star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)) +
                    ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                      Matrix.diagonal (Complex.ofReal ∘ hM_herm.eigenvalues) *
                      star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)) := congr_arg₂ (· + ·) hI_spec hM_spec
                _ = _ := by
                    rw [← Matrix.add_mul, ← Matrix.mul_add]
                    congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
                    split_ifs <;> simp [Complex.ofReal_add]
            rw [hspec]
            simp only [inv1pM, Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)),
              hUM_star, Matrix.one_mul,
              ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
            have hd : Matrix.diagonal (fun k : d ↦
                ((1 + hM_herm.eigenvalues k : ℝ) : ℂ) * (((1 + hM_herm.eigenvalues k)⁻¹ : ℝ) : ℂ)) = 1 := by
              rw [← Matrix.diagonal_one]; congr 1; ext k
              rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt (by linarith [hlam_gt k])), Complex.ofReal_one]
            rw [hd, Matrix.one_mul, hUM_mul]
          have h2 : (S * Qinv * S) * (1 + M) = 1 := by
            rw [h1pM]
            calc S * Qinv * S * (Sinv * (σ.mat + (r : ℂ) • 1) * Sinv)
                = S * Qinv * (S * Sinv) * (σ.mat + (r : ℂ) • 1) * Sinv := by simp [Matrix.mul_assoc]
              _ = S * (Qinv * (σ.mat + (r : ℂ) • 1)) * Sinv := by rw [hS_mul_Sinv, Matrix.mul_one]; simp [Matrix.mul_assoc]
              _ = S * 1 * Sinv := by
                  have hQinv_Q : Qinv * (σ.mat + (r : ℂ) • 1) = 1 := by
                    have hσ_spec : σ.mat = Uσ * Matrix.diagonal (Complex.ofReal ∘ β) * star Uσ := by
                      simpa [Uσ, β, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
                        Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
                    have hI_spec : (r : ℂ) • (1 : Matrix d d ℂ) = Uσ * Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star Uσ := by
                      rw [hdiag_r, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUσ_mul]
                    have hQ_spec : σ.mat + (r : ℂ) • (1 : Matrix d d ℂ) =
                        Uσ * Matrix.diagonal (fun j ↦ ((β j + r : ℝ) : ℂ)) * star Uσ := by
                      rw [hσ_spec, hI_spec, ← Matrix.add_mul, ← Matrix.mul_add]
                      congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
                      split_ifs <;> simp [Complex.ofReal_add]
                    rw [hQ_spec]
                    simp only [Qinv, Matrix.mul_assoc]
                    rw [← Matrix.mul_assoc (star Uσ) Uσ, hUσ_star, Matrix.one_mul,
                      ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
                    have hd : Matrix.diagonal (fun j : d ↦
                        (((β j + r)⁻¹ : ℝ) : ℂ) * ((β j + r : ℝ) : ℂ)) = 1 := by
                      rw [← Matrix.diagonal_one]; congr 1; ext j
                      rw [← Complex.ofReal_mul,
                        inv_mul_cancel₀ (ne_of_gt (by linarith [hβ_pos j] : 0 < β j + r)), Complex.ofReal_one]
                    rw [hd, Matrix.one_mul, hUσ_mul]
                  rw [hQinv_Q]
              _ = 1 := by rw [Matrix.mul_one, hS_mul_Sinv]
          calc inv1pM = 1 * inv1pM := (Matrix.one_mul _).symm
            _ = ((S * Qinv * S) * (1 + M)) * inv1pM := by rw [h2]
            _ = (S * Qinv * S) * ((1 + M) * inv1pM) := Matrix.mul_assoc _ _ _
            _ = S * Qinv * S := by rw [h1, Matrix.mul_one]
        have htr1 : inv1pM.trace = ∑ k : d, (((1 + hM_herm.eigenvalues k)⁻¹ : ℝ) : ℂ) := by
          simp only [inv1pM]
          rw [Matrix.trace_mul_cycle, hUM_star,
            Matrix.one_mul, Matrix.trace_diagonal]
        have htr2 : (S * Qinv * S).trace =
            ∑ i : d, ∑ j : d, ((‖V j i‖ ^ 2 * ((α i + r) / (β j + r)) : ℝ) : ℂ) := by
          rw [Matrix.trace_mul_cycle, hS_sq]
          have hP_spec : ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ) =
              Uρ * Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * star Uρ := by
            have hρ_spec : ρ.mat = Uρ * Matrix.diagonal (Complex.ofReal ∘ α) * star Uρ := by
              simpa [Uρ, α, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
                Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
            have hI_spec : (r : ℂ) • (1 : Matrix d d ℂ) = Uρ * Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star Uρ := by
              rw [hdiag_r, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUρ_mul]
            rw [hρ_spec, hI_spec, ← Matrix.add_mul, ← Matrix.mul_add]
            congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
            split_ifs <;> simp [Complex.ofReal_add]
          rw [hP_spec]
          simp only [Qinv]
          have hcyc : (Uρ * Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * star Uρ *
              (Uσ * Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ)) * star Uσ)).trace =
              (Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * (star V) *
                Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ)) * V).trace := by
            have hVstar : star V = star Uρ * Uσ := by simp [V, star_mul]
            rw [hVstar]
            calc (Uρ * Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * star Uρ *
                  (Uσ * Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ)) * star Uσ)).trace
                = (Uρ * (Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * star Uρ *
                    Uσ * Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ))) * star Uσ).trace := by
                    simp [Matrix.mul_assoc]
              _ = (star Uσ * Uρ * (Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * star Uρ *
                    Uσ * Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ)))).trace := by
                    rw [Matrix.trace_mul_cycle]
              _ = (Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * (star Uρ * Uσ) *
                    Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ)) * (star Uσ * Uρ)).trace := by
                    rw [Matrix.trace_mul_comm]; simp [Matrix.mul_assoc]
          rw [hcyc]
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
            ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
            Finset.sum_ite_eq]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Complex.ofReal_mul, Complex.ofReal_div, div_eq_mul_inv]
          have hnorm : star (V j i) * V j i = ((‖V j i‖ ^ 2 : ℝ) : ℂ) := by
            rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          calc ((α i + r : ℝ) : ℂ) * star (V j i) * (((β j + r)⁻¹ : ℝ) : ℂ) * V j i
              = (star (V j i) * V j i) * (((α i + r : ℝ) : ℂ) * (((β j + r : ℝ) : ℂ)⁻¹)) := by
                  rw [Complex.ofReal_inv]; ring
            _ = _ := by rw [hnorm]
        have htr_re := congr_arg Complex.re (htr1.symm.trans (congr_arg Matrix.trace hinv_eq |>.trans htr2))
        simp only [← Complex.ofReal_sum, Complex.ofReal_re] at htr_re
        exact htr_re
      simp only [g, ← hlog_sum, ← htr_inv]
      have hterm_eq : ∀ k : d, hM_herm.eigenvalues k / (1 + hM_herm.eigenvalues k) =
          1 - (1 + hM_herm.eigenvalues k)⁻¹ := by
        intro k
        have hpos : 0 < 1 + hM_herm.eigenvalues k := by linarith [hlam_gt k]
        field_simp [ne_of_gt hpos]; ring
      simp_rw [hterm_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      ring
    have hg_nn : 0 ≤ g r := by
      rw [hg_spectral]
      apply Finset.sum_nonneg; intro k _
      have hpos : 0 < 1 + hM_herm.eigenvalues k := by linarith [hlam_gt k]
      have hlog := Real.add_one_le_exp (-Real.log (1 + hM_herm.eigenvalues k))
      rw [Real.exp_neg, Real.exp_log hpos] at hlog
      have h1 : 1 - (1 + hM_herm.eigenvalues k)⁻¹ = hM_herm.eigenvalues k / (1 + hM_herm.eigenvalues k) := by
        field_simp [ne_of_gt hpos]; ring
      linarith
    refine ⟨hg_nn, ?_⟩
    have hneg_eq : ∀ t : ℝ,
        (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) =
          ∑ k : d, if 1 + t * hM_herm.eigenvalues k < 0 then (1 : ℝ≥0∞) else 0 := by
      intro t
      have h1ptM_herm : (1 + (t : ℂ) • M).IsHermitian := by
        have htM : ((t : ℂ) • M).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hM_herm.eq]
        exact Matrix.isHermitian_one.add htM
      have hcong_mat : S * (1 + (t : ℂ) • M) * Sᴴ =
          ((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat + (r : ℂ) • (1 : Matrix d d ℂ) := by
        rw [hS_herm.eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hS_sq,
          Matrix.mul_smul, Matrix.smul_mul]
        have hSMS : S * M * S = σ.mat - ρ.mat := by
          simp only [M, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc S Sinv, hS_mul_Sinv, Matrix.one_mul, hSinv_mul_S, Matrix.mul_one]
        rw [hSMS]
        ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
        push_cast; ring
      have hneg1 : negEigCount (isHermitian_pencil ρ σ r t) = negEigCount h1ptM_herm := by
        have hcong_herm : (S * (1 + (t : ℂ) • M) * Sᴴ).IsHermitian :=
          hcong_mat.symm ▸ isHermitian_pencil ρ σ r t
        calc negEigCount (isHermitian_pencil ρ σ r t)
            = negEigCount hcong_herm := negEigCount_eq_of_eq _ _ hcong_mat.symm
          _ = negEigCount h1ptM_herm := negEigCount_congruence h1ptM_herm hS_mul_Sinv hSinv_mul_S hcong_herm
      let D : Matrix d d ℂ := Matrix.diagonal (fun k ↦ ((1 + t * hM_herm.eigenvalues k : ℝ) : ℂ))
      have hD_herm : D.IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext k; simp
      have h1ptM_eq : (hM_herm.eigenvectorUnitary : Matrix d d ℂ) * D *
          (hM_herm.eigenvectorUnitary : Matrix d d ℂ)ᴴ = 1 + (t : ℂ) • M := by
        have hM_spec : M = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
            Matrix.diagonal (Complex.ofReal ∘ hM_herm.eigenvalues) *
            star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
          simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM_herm.spectral_theorem
        have hI_spec : (1 : Matrix d d ℂ) = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
            Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
            star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
          rw [Matrix.diagonal_one, Matrix.mul_one, hUM_mul]
        symm
        calc (1 : Matrix d d ℂ) + (t : ℂ) • M
            = ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) * Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
                star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)) +
              (t : ℂ) • ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                Matrix.diagonal (Complex.ofReal ∘ hM_herm.eigenvalues) *
                star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)) :=
                  congr_arg₂ (· + ·) hI_spec (congr_arg ((t : ℂ) • ·) hM_spec)
          _ = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) * D *
                (hM_herm.eigenvectorUnitary : Matrix d d ℂ)ᴴ := by
                  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add]
                  simp only [D, Matrix.star_eq_conjTranspose]
                  congr 2; ext i j
                  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply,
                    Complex.real_smul]
                  split_ifs <;> simp [Complex.ofReal_add, Complex.ofReal_mul]
      have hneg2 : negEigCount h1ptM_herm = negEigCount hD_herm := by
        have hUDU_herm : ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) * D *
            (hM_herm.eigenvectorUnitary : Matrix d d ℂ)ᴴ).IsHermitian :=
          h1ptM_eq.symm ▸ h1ptM_herm
        calc negEigCount h1ptM_herm
            = negEigCount hUDU_herm := negEigCount_eq_of_eq _ _ h1ptM_eq.symm
          _ = negEigCount hD_herm := negEigCount_congruence hD_herm hUM_mul hUM_star hUDU_herm
      have hneg3 : negEigCount hD_herm = (Finset.univ.filter (fun k : d ↦ 1 + t * hM_herm.eigenvalues k < 0)).card := by
        have hsum_ind : ∑ k : d, (if hD_herm.eigenvalues k < 0 then (1 : ℝ) else 0) =
            ∑ k : d, (if 1 + t * hM_herm.eigenvalues k < 0 then (1 : ℝ) else 0) :=
          spectral_sum_diagonal (fun k ↦ 1 + t * hM_herm.eigenvalues k) hD_herm
            (f := fun x : ℝ ↦ if x < 0 then (1 : ℝ) else 0) (if_neg (lt_irrefl 0))
        have hcard1 : (Finset.univ.filter (fun k : d ↦ hD_herm.eigenvalues k < 0)).card =
            ((∑ k : d, if hD_herm.eigenvalues k < 0 then (1 : ℝ) else 0) : ℝ) := by
          simp [Finset.sum_boole]
        have hcard2 : (Finset.univ.filter (fun k : d ↦ 1 + t * hM_herm.eigenvalues k < 0)).card =
            ((∑ k : d, if 1 + t * hM_herm.eigenvalues k < 0 then (1 : ℝ) else 0) : ℝ) := by
          simp [Finset.sum_boole]
        exact Nat.cast_injective (R := ℝ) (hcard1.trans (hsum_ind.trans hcard2.symm))
      rw [hneg1, hneg2, hneg3]
      simp [Finset.sum_boole]
    have hlhs : ∫⁻ t : ℝ, (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) *
        ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) ∂volume =
        ∑ k : d, ENNReal.ofReal (Real.log (1 + hM_herm.eigenvalues k) -
          hM_herm.eigenvalues k / (1 + hM_herm.eigenvalues k)) := by
      simp_rw [hneg_eq, Finset.sum_mul]
      rw [MeasureTheory.lintegral_finset_sum]
      · apply Finset.sum_congr rfl; intro k _
        have hite : ∀ t : ℝ, (if 1 + t * hM_herm.eigenvalues k < 0 then (1 : ℝ≥0∞) else 0) *
            ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) =
            if 1 + t * hM_herm.eigenvalues k < 0 then ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) else 0 := by
          intro t; split_ifs <;> simp
        simp_rw [hite]
        exact lintegral_indicator_inv_abs_mul_sq_sub_one (hlam_gt k)
      · intro k _
        have hmeas_set : MeasurableSet {t : ℝ | 1 + t * hM_herm.eigenvalues k < 0} :=
          measurableSet_lt (measurable_const.add (measurable_id.mul measurable_const)) measurable_const
        have hmeas_w : Measurable (fun t : ℝ ↦ ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2))) :=
          ENNReal.measurable_ofReal.comp (measurable_const.div
            (continuous_abs.measurable.mul ((measurable_id.sub measurable_const).pow_const 2)))
        exact (Measurable.ite hmeas_set measurable_const measurable_const).mul hmeas_w
    rw [hlhs, hg_spectral, ENNReal.ofReal_sum_of_nonneg]
    intro k _
    have hpos : 0 < 1 + hM_herm.eigenvalues k := by linarith [hlam_gt k]
    have hlog := Real.add_one_le_exp (-Real.log (1 + hM_herm.eigenvalues k))
    rw [Real.exp_neg, Real.exp_log hpos] at hlog
    have h1 : 1 - (1 + hM_herm.eigenvalues k)⁻¹ = hM_herm.eigenvalues k / (1 + hM_herm.eigenvalues k) := by
      field_simp [ne_of_gt hpos]; ring
    linarith
  -- Step 5: `∫⁻ r in Ioi 0, ENNReal.ofReal (g r) = ENNReal.ofReal (F 0)` via FTC + MCT
  have hint_g : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (g r) ∂volume = ENNReal.ofReal (F 0) := by
    have hunion : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioc (0 : ℝ) ((n : ℝ) + 1) := by
      ext r; simp only [mem_Ioi, mem_iUnion, mem_Ioc]
      constructor
      · intro hr; obtain ⟨n, hn⟩ := exists_nat_gt r; exact ⟨n, hr, by linarith⟩
      · rintro ⟨n, h1, _⟩; exact h1
    have hmono_sets : Monotone (fun n : ℕ ↦ Ioc (0 : ℝ) ((n : ℝ) + 1)) := by
      intro m n hmn r ⟨h1, h2⟩
      exact ⟨h1, by linarith [show (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmn]⟩
    have hlim_int : Tendsto (fun n : ℕ ↦ ∫⁻ r in Ioc (0 : ℝ) ((n : ℝ) + 1),
        ENNReal.ofReal (g r) ∂volume) atTop
        (𝓝 (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (g r) ∂volume)) := by
      rw [hunion]
      have hg_meas : Measurable (fun r : ℝ ↦ ENNReal.ofReal (g r)) := by
        apply ENNReal.measurable_ofReal.comp
        have h1 : Measurable (fun r : ℝ ↦ ∑ j : d, Real.log (β j + r)) :=
          Finset.measurable_sum _ fun j _ ↦ Real.measurable_log.comp (measurable_const.add measurable_id)
        have h2 : Measurable (fun r : ℝ ↦ ∑ i : d, Real.log (α i + r)) :=
          Finset.measurable_sum _ fun i _ ↦ Real.measurable_log.comp (measurable_const.add measurable_id)
        have h3 : Measurable (fun r : ℝ ↦ ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * ((α i + r) / (β j + r))) :=
          Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
            measurable_const.mul ((measurable_const.add measurable_id).div (measurable_const.add measurable_id))
        exact ((h1.sub h2).sub measurable_const).add h3
      exact tendsto_setLIntegral_monotone hmono_sets (fun _ ↦ measurableSet_Ioc) hg_meas
    have hval_n : ∀ n : ℕ, ∫⁻ r in Ioc (0 : ℝ) ((n : ℝ) + 1), ENNReal.ofReal (g r) ∂volume =
        ENNReal.ofReal (F 0 - F ((n : ℝ) + 1)) := by
      intro n
      have hle : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      have hint : IntervalIntegrable g volume 0 ((n : ℝ) + 1) :=
        (hg_cont.mono (fun r hr ↦ hr.1)).intervalIntegrable_of_Icc hle
      have hftc : ∫ r in (0 : ℝ)..((n : ℝ) + 1), g r = F 0 - F ((n : ℝ) + 1) := by
        have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun r ↦ -F r) (f' := g)
          (fun r hr ↦ by
            rw [uIcc_of_le hle] at hr
            simpa using (hF_deriv r hr.1).fun_neg) hint
        linarith
      rw [← hftc, intervalIntegral.integral_of_le hle,
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint.1]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact (hg_pos_and_lintegral r hr.1).1
    have hlim_rhs : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (F 0 - F ((n : ℝ) + 1))) atTop
        (𝓝 (ENNReal.ofReal (F 0 - 0))) := by
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      exact tendsto_const_nhds.sub
        (hF_tendsto.comp (Filter.tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
    simp_rw [hval_n] at hlim_int
    simpa using tendsto_nhds_unique hlim_int hlim_rhs
  -- Step 6: Swap integrals via Tonelli (`lintegral_lintegral_swap`) and apply layer-cake!
  rw [← hF0_eq, ← hint_g]
  have h1 : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (g r) ∂volume =
      ∫⁻ r in Ioi (0 : ℝ), ∫⁻ t : ℝ,
        (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) *
          ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) ∂volume ∂volume := by
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    intro r hr; exact (hg_pos_and_lintegral r hr).2
  rw [h1]
  have hmeas_prod : Measurable (fun p : ℝ × ℝ ↦
      (negEigCount (isHermitian_pencil ρ σ p.1 p.2) : ℝ≥0∞) *
        ENNReal.ofReal (1 / (|p.2| * (p.2 - 1) ^ 2))) :=
    (measurable_negEigCount_pencil ρ σ).mul
      (ENNReal.measurable_ofReal.comp (measurable_const.div
        ((continuous_abs.measurable.comp measurable_snd).mul
          ((measurable_snd.sub measurable_const).pow_const 2))))
  rw [MeasureTheory.lintegral_lintegral_swap hmeas_prod.aemeasurable]
  apply MeasureTheory.lintegral_congr
  intro t
  have hmeas_t : Measurable (fun x : ℝ ↦ (negEigCount (isHermitian_pencil ρ σ x t) : ℝ≥0∞)) :=
    (measurable_negEigCount_pencil ρ σ).comp (measurable_id.prodMk measurable_const)
  rw [MeasureTheory.lintegral_mul_const _ hmeas_t]
  have hA_t : (((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat).IsHermitian := by
    have h1 : (((1 - t : ℝ) : ℂ) • ρ.mat).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, ρ.isHermitian.eq]
    have h2 : ((t : ℂ) • σ.mat).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, σ.isHermitian.eq]
    exact h1.add h2
  have hlc := lintegral_negEigCount_eq_negPartTrace hA_t
  rw [hlc, ← ENNReal.ofReal_mul (negPartTrace_nonneg hA_t), mul_one_div]

end PolarCodes
