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

/-! ### Shifted Relative Entropy `frenkelF` and Negative Derivative `frenkelG` -/

private lemma eigUnitary_mul_star (ρ : DensityOp d) :
    (ρ.eigUnitary : Matrix d d ℂ) * star (ρ.eigUnitary : Matrix d d ℂ) = 1 :=
  Unitary.coe_mul_star_self ρ.eigUnitary

private lemma eigUnitary_star_mul (ρ : DensityOp d) :
    star (ρ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ) = 1 :=
  Unitary.coe_star_mul_self ρ.eigUnitary

private lemma eigvals_pos {ρ : DensityOp d} (hρ : ρ.mat.PosDef) (i : d) : 0 < ρ.eigvals i :=
  hρ.eigenvalues_pos i

private noncomputable def frenkelV (ρ σ : DensityOp d) : Matrix d d ℂ :=
  star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)

private lemma frenkelV_star_mul (ρ σ : DensityOp d) :
    star (frenkelV ρ σ) * frenkelV ρ σ = 1 := by
  simp only [frenkelV, star_mul, star_star, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (σ.eigUnitary : Matrix d d ℂ) (star (σ.eigUnitary : Matrix d d ℂ)),
    eigUnitary_mul_star σ, Matrix.one_mul, eigUnitary_star_mul ρ]

private lemma frenkelV_mul_star (ρ σ : DensityOp d) :
    frenkelV ρ σ * star (frenkelV ρ σ) = 1 := by
  simp only [frenkelV, star_mul, star_star, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (ρ.eigUnitary : Matrix d d ℂ) (star (ρ.eigUnitary : Matrix d d ℂ)),
    eigUnitary_mul_star ρ, Matrix.one_mul, eigUnitary_star_mul σ]

private lemma frenkelV_col_sum (ρ σ : DensityOp d) (i : d) :
    ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 = 1 := by
  have h := congr_arg Complex.re (congr_fun (congr_fun (frenkelV_star_mul ρ σ) i) i)
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at h
  convert h using 1
  apply Finset.sum_congr rfl; intro j _
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

private lemma frenkelV_row_sum (ρ σ : DensityOp d) (j : d) :
    ∑ i : d, ‖frenkelV ρ σ j i‖ ^ 2 = 1 := by
  have h := congr_arg Complex.re (congr_fun (congr_fun (frenkelV_mul_star ρ σ) j) j)
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at h
  convert h using 1
  apply Finset.sum_congr rfl; intro i _
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

private noncomputable def frenkelF (ρ σ : DensityOp d) (r : ℝ) : ℝ :=
  ∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 *
    ((ρ.eigvals i + r) * (Real.log (ρ.eigvals i + r) - Real.log (σ.eigvals j + r)))

private noncomputable def frenkelG (ρ σ : DensityOp d) (r : ℝ) : ℝ :=
  (∑ j : d, Real.log (σ.eigvals j + r) - ∑ i : d, Real.log (ρ.eigvals i + r)) -
    (Fintype.card d : ℝ) + ∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 *
      ((ρ.eigvals i + r) / (σ.eigvals j + r))

private lemma frenkelF_zero_eq {ρ σ : DensityOp d} (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    ENNReal.ofReal (frenkelF ρ σ 0) = relEntropy ρ σ * ENNReal.ofReal (Real.log 2) := by
  have hα_pos : ∀ i : d, 0 < ρ.eigvals i := eigvals_pos hρ
  have hβ_pos : ∀ j : d, 0 < σ.eigvals j := eigvals_pos hσ
  have hsupp : suppSubset ρ σ := fun _ j _ hβ0 ↦ absurd hβ0 (ne_of_gt (hβ_pos j))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : 0 ≤ frenkelF ρ σ 0 := by
    have hterm : ∀ i j : d, ρ.eigvals i - σ.eigvals j ≤
        ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j)) := by
      intro i j
      have hlog := Real.add_one_le_exp (Real.log (σ.eigvals j) - Real.log (ρ.eigvals i))
      rw [Real.exp_sub, Real.exp_log (hβ_pos j), Real.exp_log (hα_pos i)] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt (hα_pos i))
      have hcancel : ρ.eigvals i * (σ.eigvals j / ρ.eigvals i) = σ.eigvals j :=
        mul_div_cancel₀ _ (ne_of_gt (hα_pos i))
      linarith
    calc (0 : ℝ) = ∑ i : d, ρ.eigvals i - ∑ j : d, σ.eigvals j := by
          have h1 := ρ.sum_eigvals; have h2 := σ.sum_eigvals; linarith
      _ = ∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 * (ρ.eigvals i - σ.eigvals j) := by
          simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, frenkelV_col_sum, one_mul]
          congr 1; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro j _
          rw [← Finset.sum_mul, frenkelV_row_sum, one_mul]
      _ ≤ frenkelF ρ σ 0 := by
          unfold frenkelF
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          simp only [add_zero]
          exact mul_le_mul_of_nonneg_left (hterm i j) (sq_nonneg _)
  unfold relEntropy
  rw [if_pos hsupp, ← ENNReal.ofReal_mul (div_nonneg (by simpa [frenkelF, frenkelV] using hnn) (le_of_lt hlog2_pos))]
  congr 1
  rw [div_mul_cancel₀ _ (ne_of_gt hlog2_pos)]
  simp [frenkelF, frenkelV]

private lemma frenkelF_hasDerivAt {ρ σ : DensityOp d} (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef)
    {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (frenkelF ρ σ) (-frenkelG ρ σ r) r := by
  have hα_pos : ∀ i : d, 0 < ρ.eigvals i := eigvals_pos hρ
  have hβ_pos : ∀ j : d, 0 < σ.eigvals j := eigvals_pos hσ
  have hterm : ∀ i j : d, HasDerivAt
      (fun s : ℝ ↦ ‖frenkelV ρ σ j i‖ ^ 2 *
        ((ρ.eigvals i + s) * (Real.log (ρ.eigvals i + s) - Real.log (σ.eigvals j + s))))
      (‖frenkelV ρ σ j i‖ ^ 2 *
        (Real.log (ρ.eigvals i + r) - Real.log (σ.eigvals j + r) + 1 -
          (ρ.eigvals i + r) / (σ.eigvals j + r))) r := by
    intro i j
    have hαr : 0 < ρ.eigvals i + r := by linarith [hα_pos i]
    have hβr : 0 < σ.eigvals j + r := by linarith [hβ_pos j]
    have h1 : HasDerivAt (fun s : ℝ ↦ ρ.eigvals i + s) 1 r := by
      simpa using (hasDerivAt_const r (ρ.eigvals i)).fun_add (hasDerivAt_id' r)
    have h2 : HasDerivAt (fun s : ℝ ↦ Real.log (ρ.eigvals i + s)) (1 / (ρ.eigvals i + r)) r := by
      simpa using h1.log (ne_of_gt hαr)
    have h3 : HasDerivAt (fun s : ℝ ↦ σ.eigvals j + s) 1 r := by
      simpa using (hasDerivAt_const r (σ.eigvals j)).fun_add (hasDerivAt_id' r)
    have h4 : HasDerivAt (fun s : ℝ ↦ Real.log (σ.eigvals j + s)) (1 / (σ.eigvals j + r)) r := by
      simpa using h3.log (ne_of_gt hβr)
    convert (h1.fun_mul (h2.fun_sub h4)).const_mul (‖frenkelV ρ σ j i‖ ^ 2) using 1
    field_simp [ne_of_gt hαr, ne_of_gt hβr]; ring
  have hsum : HasDerivAt (frenkelF ρ σ)
      (∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 *
        (Real.log (ρ.eigvals i + r) - Real.log (σ.eigvals j + r) + 1 -
          (ρ.eigvals i + r) / (σ.eigvals j + r))) r :=
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ ↦ HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hterm i j))
  convert hsum using 1
  simp only [frenkelG]
  have hsplit : (∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 *
      (Real.log (ρ.eigvals i + r) - Real.log (σ.eigvals j + r) + 1 -
        (ρ.eigvals i + r) / (σ.eigvals j + r))) =
      (∑ i : d, Real.log (ρ.eigvals i + r)) - (∑ j : d, Real.log (σ.eigvals j + r)) +
      (Fintype.card d : ℝ) - ∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 *
        ((ρ.eigvals i + r) / (σ.eigvals j + r)) := by
    have h1 : ∀ i j : d, ‖frenkelV ρ σ j i‖ ^ 2 *
        (Real.log (ρ.eigvals i + r) - Real.log (σ.eigvals j + r) + 1 -
          (ρ.eigvals i + r) / (σ.eigvals j + r)) =
        (‖frenkelV ρ σ j i‖ ^ 2 * Real.log (ρ.eigvals i + r) -
          ‖frenkelV ρ σ j i‖ ^ 2 * Real.log (σ.eigvals j + r)) +
        (‖frenkelV ρ σ j i‖ ^ 2 -
          ‖frenkelV ρ σ j i‖ ^ 2 * ((ρ.eigvals i + r) / (σ.eigvals j + r))) := fun _ _ ↦ by ring
    simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have ha : ∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 * Real.log (ρ.eigvals i + r) =
        ∑ i : d, Real.log (ρ.eigvals i + r) := by
      apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_mul, frenkelV_col_sum, one_mul]
    have hb : ∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 * Real.log (σ.eigvals j + r) =
        ∑ j : d, Real.log (σ.eigvals j + r) := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
      rw [← Finset.sum_mul, frenkelV_row_sum, one_mul]
    have hc : ∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 = (Fintype.card d : ℝ) := by
      simp_rw [frenkelV_col_sum]; simp
    rw [ha, hb, hc]; ring
  linarith

private lemma frenkelG_continuousOn {ρ σ : DensityOp d} (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    ContinuousOn (frenkelG ρ σ) (Ici 0) := by
  have hα_pos : ∀ i : d, 0 < ρ.eigvals i := eigvals_pos hρ
  have hβ_pos : ∀ j : d, 0 < σ.eigvals j := eigvals_pos hσ
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
  have h1 : ContinuousAt (fun s : ℝ ↦ ∑ j : d, Real.log (σ.eigvals j + s)) r :=
    hcont_sum Finset.univ _ r fun j _ ↦
      (Real.continuousAt_log (ne_of_gt (by linarith [hβ_pos j, Set.mem_Ici.mp hr] : 0 < σ.eigvals j + r))).comp
        (continuousAt_const.add continuousAt_id)
  have h2 : ContinuousAt (fun s : ℝ ↦ ∑ i : d, Real.log (ρ.eigvals i + s)) r :=
    hcont_sum Finset.univ _ r fun i _ ↦
      (Real.continuousAt_log (ne_of_gt (by linarith [hα_pos i, Set.mem_Ici.mp hr] : 0 < ρ.eigvals i + r))).comp
        (continuousAt_const.add continuousAt_id)
  have h3 : ContinuousAt (fun s : ℝ ↦ ∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 *
      ((ρ.eigvals i + s) / (σ.eigvals j + s))) r :=
    hcont_sum Finset.univ _ r fun i _ ↦ hcont_sum Finset.univ _ r fun j _ ↦
      continuousAt_const.mul ((continuousAt_const.add continuousAt_id).div
        (continuousAt_const.add continuousAt_id)
        (ne_of_gt (by linarith [hβ_pos j, Set.mem_Ici.mp hr] : 0 < σ.eigvals j + r)))
  exact (((h1.sub h2).sub continuousAt_const).add h3).continuousWithinAt

private lemma frenkelF_tendsto_zero {ρ σ : DensityOp d} (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    Tendsto (frenkelF ρ σ) atTop (𝓝 0) := by
  have hα_pos : ∀ i : d, 0 < ρ.eigvals i := eigvals_pos hρ
  have hβ_pos : ∀ j : d, 0 < σ.eigvals j := eigvals_pos hσ
  have hterm : ∀ i j : d, Tendsto
      (fun r : ℝ ↦ ‖frenkelV ρ σ j i‖ ^ 2 *
        ((ρ.eigvals i + r) * (Real.log (ρ.eigvals i + r) - Real.log (σ.eigvals j + r))))
      atTop (𝓝 (‖frenkelV ρ σ j i‖ ^ 2 * (ρ.eigvals i - σ.eigvals j))) := by
    intro i j
    apply Tendsto.const_mul
    have hlo : ∀ᶠ r : ℝ in atTop,
        (ρ.eigvals i + r) * ((ρ.eigvals i - σ.eigvals j) / (ρ.eigvals i + r)) ≤
          (ρ.eigvals i + r) * (Real.log (ρ.eigvals i + r) - Real.log (σ.eigvals j + r)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      have hαr : 0 < ρ.eigvals i + r := by linarith [hα_pos i]
      have hβr : 0 < σ.eigvals j + r := by linarith [hβ_pos j]
      have h1 : (σ.eigvals j + r) / (ρ.eigvals i + r) ≤
          Real.exp ((σ.eigvals j + r) / (ρ.eigvals i + r) - 1) := by
        have := Real.add_one_le_exp ((σ.eigvals j + r) / (ρ.eigvals i + r) - 1); linarith
      have h2 : Real.log ((σ.eigvals j + r) / (ρ.eigvals i + r)) ≤
          (σ.eigvals j + r) / (ρ.eigvals i + r) - 1 := by
        have := Real.log_le_log (div_pos hβr hαr) h1; rwa [Real.log_exp] at this
      rw [Real.log_div (ne_of_gt hβr) (ne_of_gt hαr)] at h2
      have h3 : (ρ.eigvals i - σ.eigvals j) / (ρ.eigvals i + r) ≤
          Real.log (ρ.eigvals i + r) - Real.log (σ.eigvals j + r) := by
        have : 1 - (σ.eigvals j + r) / (ρ.eigvals i + r) =
            (ρ.eigvals i - σ.eigvals j) / (ρ.eigvals i + r) := by
          field_simp [ne_of_gt hαr]; ring
        linarith
      exact mul_le_mul_of_nonneg_left h3 (le_of_lt hαr)
    have hhi : ∀ᶠ r : ℝ in atTop,
        (ρ.eigvals i + r) * (Real.log (ρ.eigvals i + r) - Real.log (σ.eigvals j + r)) ≤
          (ρ.eigvals i + r) * ((ρ.eigvals i - σ.eigvals j) / (σ.eigvals j + r)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      have hαr : 0 < ρ.eigvals i + r := by linarith [hα_pos i]
      have hβr : 0 < σ.eigvals j + r := by linarith [hβ_pos j]
      have h1 : (ρ.eigvals i + r) / (σ.eigvals j + r) ≤
          Real.exp ((ρ.eigvals i + r) / (σ.eigvals j + r) - 1) := by
        have := Real.add_one_le_exp ((ρ.eigvals i + r) / (σ.eigvals j + r) - 1); linarith
      have h2 : Real.log ((ρ.eigvals i + r) / (σ.eigvals j + r)) ≤
          (ρ.eigvals i + r) / (σ.eigvals j + r) - 1 := by
        have := Real.log_le_log (div_pos hαr hβr) h1; rwa [Real.log_exp] at this
      rw [Real.log_div (ne_of_gt hαr) (ne_of_gt hβr)] at h2
      have h3 : Real.log (ρ.eigvals i + r) - Real.log (σ.eigvals j + r) ≤
          (ρ.eigvals i - σ.eigvals j) / (σ.eigvals j + r) := by
        have : (ρ.eigvals i + r) / (σ.eigvals j + r) - 1 =
            (ρ.eigvals i - σ.eigvals j) / (σ.eigvals j + r) := by
          field_simp [ne_of_gt hβr]; ring
        linarith
      exact mul_le_mul_of_nonneg_left h3 (le_of_lt hαr)
    have hlo_lim : Tendsto (fun r : ℝ ↦ (ρ.eigvals i + r) *
        ((ρ.eigvals i - σ.eigvals j) / (ρ.eigvals i + r))) atTop (𝓝 (ρ.eigvals i - σ.eigvals j)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      exact (mul_div_cancel₀ _ (ne_of_gt (by linarith [hα_pos i]))).symm
    have hhi_lim : Tendsto (fun r : ℝ ↦ (ρ.eigvals i + r) *
        ((ρ.eigvals i - σ.eigvals j) / (σ.eigvals j + r))) atTop (𝓝 (ρ.eigvals i - σ.eigvals j)) := by
      have hrew : ∀ᶠ r : ℝ in atTop,
          (ρ.eigvals i + r) * ((ρ.eigvals i - σ.eigvals j) / (σ.eigvals j + r)) =
            (ρ.eigvals i - σ.eigvals j) * (1 + (ρ.eigvals i - σ.eigvals j) / (σ.eigvals j + r)) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
        field_simp [ne_of_gt (by linarith [hβ_pos j] : 0 < σ.eigvals j + r)]; ring
      rw [tendsto_congr' hrew]
      have hinv : Tendsto (fun r : ℝ ↦ (ρ.eigvals i - σ.eigvals j) / (σ.eigvals j + r)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_left atTop (σ.eigvals j) tendsto_id)
      simpa using (tendsto_const_nhds (x := ρ.eigvals i - σ.eigvals j)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add hinv)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_lim hhi_lim hlo hhi
  have hsum_lim := tendsto_finset_sum Finset.univ (fun i _ ↦
    tendsto_finset_sum Finset.univ (fun j _ ↦ hterm i j))
  have hsum_zero : ∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 * (ρ.eigvals i - σ.eigvals j) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, frenkelV_col_sum, one_mul]
    have h2 : ∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 * σ.eigvals j = ∑ j : d, σ.eigvals j := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
      rw [← Finset.sum_mul, frenkelV_row_sum, one_mul]
    rw [h2, ρ.sum_eigvals, σ.sum_eigvals, sub_self]
  rwa [hsum_zero] at hsum_lim

/-! ### Spectral Congruence `X(t, r) = S(r) (I + t M(r)) S(r)` -/

private noncomputable def frenkelS (ρ : DensityOp d) (r : ℝ) : Matrix d d ℂ :=
  (ρ.eigUnitary : Matrix d d ℂ) *
    Matrix.diagonal (fun i ↦ ((Real.sqrt (ρ.eigvals i + r) : ℝ) : ℂ)) *
    star (ρ.eigUnitary : Matrix d d ℂ)

private noncomputable def frenkelSinv (ρ : DensityOp d) (r : ℝ) : Matrix d d ℂ :=
  (ρ.eigUnitary : Matrix d d ℂ) *
    Matrix.diagonal (fun i ↦ (((Real.sqrt (ρ.eigvals i + r))⁻¹ : ℝ) : ℂ)) *
    star (ρ.eigUnitary : Matrix d d ℂ)

private noncomputable def frenkelQinv (σ : DensityOp d) (r : ℝ) : Matrix d d ℂ :=
  (σ.eigUnitary : Matrix d d ℂ) *
    Matrix.diagonal (fun j ↦ (((σ.eigvals j + r)⁻¹ : ℝ) : ℂ)) *
    star (σ.eigUnitary : Matrix d d ℂ)

private noncomputable def frenkelM (ρ σ : DensityOp d) (r : ℝ) : Matrix d d ℂ :=
  frenkelSinv ρ r * (σ.mat - ρ.mat) * frenkelSinv ρ r

private lemma frenkelS_isHermitian (ρ : DensityOp d) (r : ℝ) : (frenkelS ρ r).IsHermitian := by
  simp only [frenkelS, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  congr 2; ext i j; simp [Matrix.diagonal_apply]

private lemma frenkelSinv_isHermitian (ρ : DensityOp d) (r : ℝ) : (frenkelSinv ρ r).IsHermitian := by
  simp only [frenkelSinv, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  congr 2; ext i j; simp [Matrix.diagonal_apply]

private lemma frenkelM_isHermitian (ρ σ : DensityOp d) (r : ℝ) : (frenkelM ρ σ r).IsHermitian := by
  simp only [frenkelM, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    (frenkelSinv_isHermitian ρ r).eq, σ.isHermitian.eq, ρ.isHermitian.eq, Matrix.mul_assoc]

private lemma frenkelS_mul_Sinv {ρ : DensityOp d} (hρ : ρ.mat.PosDef) {r : ℝ} (hr : 0 < r) :
    frenkelS ρ r * frenkelSinv ρ r = 1 := by
  simp only [frenkelS, frenkelSinv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (ρ.eigUnitary : Matrix d d ℂ)) (ρ.eigUnitary : Matrix d d ℂ),
    eigUnitary_star_mul ρ, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  have hd : Matrix.diagonal (fun i : d ↦
      ((Real.sqrt (ρ.eigvals i + r) : ℝ) : ℂ) * (((Real.sqrt (ρ.eigvals i + r))⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [← Matrix.diagonal_one]; congr 1; ext i
    rw [← Complex.ofReal_mul,
      mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by linarith [eigvals_pos hρ i]))),
      Complex.ofReal_one]
  rw [hd, Matrix.one_mul, eigUnitary_mul_star ρ]

private lemma frenkelSinv_mul_S {ρ : DensityOp d} (hρ : ρ.mat.PosDef) {r : ℝ} (hr : 0 < r) :
    frenkelSinv ρ r * frenkelS ρ r = 1 := by
  simp only [frenkelS, frenkelSinv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (ρ.eigUnitary : Matrix d d ℂ)) (ρ.eigUnitary : Matrix d d ℂ),
    eigUnitary_star_mul ρ, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  have hd : Matrix.diagonal (fun i : d ↦
      (((Real.sqrt (ρ.eigvals i + r))⁻¹ : ℝ) : ℂ) * ((Real.sqrt (ρ.eigvals i + r) : ℝ) : ℂ)) = 1 := by
    rw [← Matrix.diagonal_one]; congr 1; ext i
    rw [← Complex.ofReal_mul,
      inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by linarith [eigvals_pos hρ i]))),
      Complex.ofReal_one]
  rw [hd, Matrix.one_mul, eigUnitary_mul_star ρ]

private lemma densityOp_add_smul_spectral (ρ : DensityOp d) (r : ℝ) :
    ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ) =
      (ρ.eigUnitary : Matrix d d ℂ) *
        Matrix.diagonal (fun i ↦ ((ρ.eigvals i + r : ℝ) : ℂ)) *
        star (ρ.eigUnitary : Matrix d d ℂ) := by
  have hdiag_r : Matrix.diagonal (fun _ : d ↦ (r : ℂ)) = (r : ℂ) • (1 : Matrix d d ℂ) := by
    ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]
  have hρ_spec : ρ.mat = (ρ.eigUnitary : Matrix d d ℂ) *
      Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star (ρ.eigUnitary : Matrix d d ℂ) := by
    simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
  have hI_spec : (r : ℂ) • (1 : Matrix d d ℂ) = (ρ.eigUnitary : Matrix d d ℂ) *
      Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star (ρ.eigUnitary : Matrix d d ℂ) := by
    rw [hdiag_r, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, eigUnitary_mul_star ρ]
  rw [hρ_spec, hI_spec, ← Matrix.add_mul, ← Matrix.mul_add]
  congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
  split_ifs <;> simp [Complex.ofReal_add]

private lemma frenkelS_sq {ρ : DensityOp d} (hρ : ρ.mat.PosDef) {r : ℝ} (hr : 0 < r) :
    frenkelS ρ r * frenkelS ρ r = ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ) := by
  rw [densityOp_add_smul_spectral ρ r]
  simp only [frenkelS, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (ρ.eigUnitary : Matrix d d ℂ)) (ρ.eigUnitary : Matrix d d ℂ),
    eigUnitary_star_mul ρ, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  congr 2; ext i j; simp only [Matrix.diagonal_apply]
  split_ifs
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith [eigvals_pos hρ i])]
  · simp

private lemma frenkelQinv_mul_Q {σ : DensityOp d} (hσ : σ.mat.PosDef) {r : ℝ} (hr : 0 < r) :
    frenkelQinv σ r * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) = 1 := by
  rw [densityOp_add_smul_spectral σ r]
  simp only [frenkelQinv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (σ.eigUnitary : Matrix d d ℂ)) (σ.eigUnitary : Matrix d d ℂ),
    eigUnitary_star_mul σ, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  have hd : Matrix.diagonal (fun j : d ↦
      (((σ.eigvals j + r)⁻¹ : ℝ) : ℂ) * ((σ.eigvals j + r : ℝ) : ℂ)) = 1 := by
    rw [← Matrix.diagonal_one]; congr 1; ext j
    rw [← Complex.ofReal_mul,
      inv_mul_cancel₀ (ne_of_gt (by linarith [eigvals_pos hσ j] : 0 < σ.eigvals j + r)),
      Complex.ofReal_one]
  rw [hd, Matrix.one_mul, eigUnitary_mul_star σ]

private lemma frenkelM_one_add {ρ σ : DensityOp d} (hρ : ρ.mat.PosDef) {r : ℝ} (hr : 0 < r) :
    1 + frenkelM ρ σ r = frenkelSinv ρ r * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * frenkelSinv ρ r := by
  have h1 : (1 : Matrix d d ℂ) = frenkelSinv ρ r * (ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * frenkelSinv ρ r := by
    calc (1 : Matrix d d ℂ) = (frenkelSinv ρ r * frenkelS ρ r) * (frenkelS ρ r * frenkelSinv ρ r) := by
          rw [frenkelSinv_mul_S hρ hr, frenkelS_mul_Sinv hρ hr, Matrix.mul_one]
      _ = frenkelSinv ρ r * (frenkelS ρ r * frenkelS ρ r) * frenkelSinv ρ r := by simp [Matrix.mul_assoc]
      _ = frenkelSinv ρ r * (ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * frenkelSinv ρ r := by rw [frenkelS_sq hρ hr]
  conv_lhs => rw [h1]
  simp only [frenkelM, ← Matrix.add_mul, ← Matrix.mul_add]
  congr 2; abel

private lemma frenkelM_eigenvalues_gt_neg_one {ρ σ : DensityOp d}
    (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) {r : ℝ} (hr : 0 < r) (k : d) :
    -1 < (frenkelM_isHermitian ρ σ r).eigenvalues k := by
  set hM := frenkelM_isHermitian ρ σ r
  have h1pM := frenkelM_one_add (σ := σ) hρ hr
  have h1pM_herm : (1 + frenkelM ρ σ r).IsHermitian := Matrix.isHermitian_one.add hM
  have h1pM_pos : (1 + frenkelM ρ σ r).PosDef := by
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
      exact add_pos hσ_y (mul_pos (by rw [Complex.pos_iff]; exact ⟨hr, rfl⟩) hy_pos)
    have hSinv_x : (frenkelSinv ρ r).mulVec x ≠ 0 := by
      intro h0
      have := congr_arg (Matrix.mulVec (frenkelS ρ r)) h0
      rw [Matrix.mulVec_mulVec, frenkelS_mul_Sinv hρ hr, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact hx this
    have hquad : star x ⬝ᵥ (frenkelSinv ρ r * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * frenkelSinv ρ r).mulVec x =
        star ((frenkelSinv ρ r).mulVec x) ⬝ᵥ (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).mulVec ((frenkelSinv ρ r).mulVec x) := by
      have hstar_Sinv : star ((frenkelSinv ρ r).mulVec x) = (star x) ᵥ* frenkelSinv ρ r := by
        ext i
        simp only [Pi.star_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, star_sum, star_mul']
        apply Finset.sum_congr rfl; intro j _
        have hji : star (frenkelSinv ρ r i j) = frenkelSinv ρ r j i := by
          have := congr_fun (congr_fun (frenkelSinv_isHermitian ρ r).eq j) i
          simpa [Matrix.conjTranspose_apply] using this
        rw [hji]; ring
      calc star x ⬝ᵥ (frenkelSinv ρ r * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * frenkelSinv ρ r).mulVec x
          = star x ⬝ᵥ (frenkelSinv ρ r).mulVec (((σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * frenkelSinv ρ r).mulVec x) := by
              rw [Matrix.mul_assoc (frenkelSinv ρ r), Matrix.mulVec_mulVec]
        _ = ((star x) ᵥ* frenkelSinv ρ r) ⬝ᵥ (((σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * frenkelSinv ρ r).mulVec x) := by
              rw [Matrix.dotProduct_mulVec]
        _ = star ((frenkelSinv ρ r).mulVec x) ⬝ᵥ (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).mulVec ((frenkelSinv ρ r).mulVec x) := by
              rw [← hstar_Sinv, Matrix.mulVec_mulVec]
    rw [hquad]
    exact (Matrix.posDef_iff_dotProduct_mulVec.mp hQ_pos).2 hSinv_x
  have hUM_star : star (hM.eigenvectorUnitary : Matrix d d ℂ) * (hM.eigenvectorUnitary : Matrix d d ℂ) = 1 :=
    Unitary.coe_star_mul_self hM.eigenvectorUnitary
  let v : d → ℂ := fun i ↦ (hM.eigenvectorUnitary : Matrix d d ℂ) i k
  have hv_ne : v ≠ 0 := by
    intro h0
    have hu := congr_fun (congr_fun hUM_star k) k
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hu
    have hzero : ∑ i : d, star ((hM.eigenvectorUnitary : Matrix d d ℂ) i k) *
        (hM.eigenvectorUnitary : Matrix d d ℂ) i k = 0 := by
      apply Finset.sum_eq_zero; intro i _; have := congr_fun h0 i; simp [v] at this; simp [this]
    rw [hzero] at hu; exact zero_ne_one hu
  have hpos_v := (Matrix.posDef_iff_dotProduct_mulVec.mp h1pM_pos).2 hv_ne
  have hval_v : (star v ⬝ᵥ (1 + frenkelM ρ σ r).mulVec v).re = 1 + hM.eigenvalues k := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.add_re]
    have h1 : (star v ⬝ᵥ v).re = 1 := by
      have hu := congr_arg Complex.re (congr_fun (congr_fun hUM_star k) k)
      simpa [dotProduct, Matrix.mul_apply, Matrix.star_apply, Pi.star_apply, v] using hu
    have h2 : (star v ⬝ᵥ (frenkelM ρ σ r).mulVec v).re = hM.eigenvalues k := by
      rw [re_quadForm_spectral hM v]
      have horth : ∀ i : d, ((star (hM.eigenvectorUnitary : Matrix d d ℂ)).mulVec v) i =
          if i = k then 1 else 0 := by
        intro i
        have hu := congr_fun (congr_fun hUM_star i) k
        simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply, v, Matrix.one_apply] using hu
      simp_rw [horth]
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hik; simp [hik]
      · intro h; exact absurd (Finset.mem_univ k) h
    linarith
  have hre_pos : 0 < (star v ⬝ᵥ (1 + frenkelM ρ σ r).mulVec v).re := (Complex.pos_iff.mp hpos_v).1
  linarith

private lemma frenkelG_eq_spectral_sum {ρ σ : DensityOp d}
    (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) {r : ℝ} (hr : 0 < r) :
    frenkelG ρ σ r = ∑ k : d, (Real.log (1 + (frenkelM_isHermitian ρ σ r).eigenvalues k) -
      (frenkelM_isHermitian ρ σ r).eigenvalues k / (1 + (frenkelM_isHermitian ρ σ r).eigenvalues k)) := by
  set hM := frenkelM_isHermitian ρ σ r
  have hlam_gt : ∀ k : d, -1 < hM.eigenvalues k := frenkelM_eigenvalues_gt_neg_one hρ hσ hr
  have hUM_mul : (hM.eigenvectorUnitary : Matrix d d ℂ) * star (hM.eigenvectorUnitary : Matrix d d ℂ) = 1 :=
    Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hUM_star : star (hM.eigenvectorUnitary : Matrix d d ℂ) * (hM.eigenvectorUnitary : Matrix d d ℂ) = 1 :=
    Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have h1pM_spec : 1 + frenkelM ρ σ r = (hM.eigenvectorUnitary : Matrix d d ℂ) *
      Matrix.diagonal (fun k ↦ ((1 + hM.eigenvalues k : ℝ) : ℂ)) *
      star (hM.eigenvectorUnitary : Matrix d d ℂ) := by
    have hM_spec : frenkelM ρ σ r = (hM.eigenvectorUnitary : Matrix d d ℂ) *
        Matrix.diagonal (Complex.ofReal ∘ hM.eigenvalues) *
        star (hM.eigenvectorUnitary : Matrix d d ℂ) := by
      simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM.spectral_theorem
    have hI_spec : (1 : Matrix d d ℂ) = (hM.eigenvectorUnitary : Matrix d d ℂ) *
        Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
        star (hM.eigenvectorUnitary : Matrix d d ℂ) := by
      rw [Matrix.diagonal_one, Matrix.mul_one, hUM_mul]
    calc (1 : Matrix d d ℂ) + frenkelM ρ σ r
        = ((hM.eigenvectorUnitary : Matrix d d ℂ) * Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
            star (hM.eigenvectorUnitary : Matrix d d ℂ)) +
          ((hM.eigenvectorUnitary : Matrix d d ℂ) *
            Matrix.diagonal (Complex.ofReal ∘ hM.eigenvalues) *
            star (hM.eigenvectorUnitary : Matrix d d ℂ)) := congr_arg₂ (· + ·) hI_spec hM_spec
      _ = _ := by
          rw [← Matrix.add_mul, ← Matrix.mul_add]
          congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
          split_ifs <;> simp [Complex.ofReal_add]
  have hdet_eq : ∏ k : d, (1 + hM.eigenvalues k) =
      (∏ j : d, (σ.eigvals j + r)) / (∏ i : d, (ρ.eigvals i + r)) := by
    have h1 : (1 + frenkelM ρ σ r).det = ∏ k : d, ((1 + hM.eigenvalues k : ℝ) : ℂ) := by
      conv_lhs => rw [h1pM_spec]
      rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
        hUM_mul, Matrix.det_one, one_mul, Matrix.det_diagonal]
    have h2 : (1 + frenkelM ρ σ r).det * (ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det =
        (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det := by
      rw [frenkelM_one_add hρ hr, ← frenkelS_sq hρ hr, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
      calc (frenkelSinv ρ r).det * (σ.mat + (r : ℂ) • 1).det * (frenkelSinv ρ r).det *
            ((frenkelS ρ r).det * (frenkelS ρ r).det)
          = ((frenkelSinv ρ r).det * (frenkelS ρ r).det) *
            ((frenkelSinv ρ r).det * (frenkelS ρ r).det) * (σ.mat + (r : ℂ) • 1).det := by ring
        _ = (frenkelSinv ρ r * frenkelS ρ r).det * (frenkelSinv ρ r * frenkelS ρ r).det *
            (σ.mat + (r : ℂ) • 1).det := by rw [← Matrix.det_mul]
        _ = (σ.mat + (r : ℂ) • 1).det := by rw [frenkelSinv_mul_S hρ hr, Matrix.det_one]; ring
    have hdetP : (ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det = ∏ i : d, ((ρ.eigvals i + r : ℝ) : ℂ) := by
      rw [densityOp_add_smul_spectral ρ r, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
        ← Matrix.det_mul, eigUnitary_mul_star ρ, Matrix.det_one, one_mul, Matrix.det_diagonal]
    have hdetQ : (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det = ∏ j : d, ((σ.eigvals j + r : ℝ) : ℂ) := by
      rw [densityOp_add_smul_spectral σ r, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
        ← Matrix.det_mul, eigUnitary_mul_star σ, Matrix.det_one, one_mul, Matrix.det_diagonal]
    rw [h1, hdetP, hdetQ] at h2
    have h2_re := congr_arg Complex.re h2
    simp only [← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_re] at h2_re
    have hP_pos : 0 < ∏ i : d, (ρ.eigvals i + r) := Finset.prod_pos fun i _ ↦ by linarith [eigvals_pos hρ i]
    exact (eq_div_iff (ne_of_gt hP_pos)).mpr h2_re
  have hlog_sum : ∑ k : d, Real.log (1 + hM.eigenvalues k) =
      ∑ j : d, Real.log (σ.eigvals j + r) - ∑ i : d, Real.log (ρ.eigvals i + r) := by
    rw [← Real.log_prod (fun k _ ↦ ne_of_gt (by linarith [hlam_gt k])), hdet_eq,
      Real.log_div (ne_of_gt (Finset.prod_pos fun j _ ↦ by linarith [eigvals_pos hσ j]))
        (ne_of_gt (Finset.prod_pos fun i _ ↦ by linarith [eigvals_pos hρ i])),
      Real.log_prod (fun j _ ↦ ne_of_gt (by linarith [eigvals_pos hσ j])),
      Real.log_prod (fun i _ ↦ ne_of_gt (by linarith [eigvals_pos hρ i]))]
  have htr_inv : ∑ k : d, (1 + hM.eigenvalues k)⁻¹ =
      ∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 * ((ρ.eigvals i + r) / (σ.eigvals j + r)) := by
    let inv1pM : Matrix d d ℂ := (hM.eigenvectorUnitary : Matrix d d ℂ) *
      Matrix.diagonal (fun k ↦ (((1 + hM.eigenvalues k)⁻¹ : ℝ) : ℂ)) *
      star (hM.eigenvectorUnitary : Matrix d d ℂ)
    have hinv_eq : inv1pM = frenkelS ρ r * frenkelQinv σ r * frenkelS ρ r := by
      have h1 : (1 + frenkelM ρ σ r) * inv1pM = 1 := by
        rw [h1pM_spec]
        simp only [inv1pM, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star (hM.eigenvectorUnitary : Matrix d d ℂ)),
          hUM_star, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
        have hd : Matrix.diagonal (fun k : d ↦
            ((1 + hM.eigenvalues k : ℝ) : ℂ) * (((1 + hM.eigenvalues k)⁻¹ : ℝ) : ℂ)) = 1 := by
          rw [← Matrix.diagonal_one]; congr 1; ext k
          rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt (by linarith [hlam_gt k])), Complex.ofReal_one]
        rw [hd, Matrix.one_mul, hUM_mul]
      have h2 : (frenkelS ρ r * frenkelQinv σ r * frenkelS ρ r) * (1 + frenkelM ρ σ r) = 1 := by
        rw [frenkelM_one_add hρ hr]
        calc frenkelS ρ r * frenkelQinv σ r * frenkelS ρ r *
              (frenkelSinv ρ r * (σ.mat + (r : ℂ) • 1) * frenkelSinv ρ r)
            = frenkelS ρ r * frenkelQinv σ r * (frenkelS ρ r * frenkelSinv ρ r) *
              (σ.mat + (r : ℂ) • 1) * frenkelSinv ρ r := by simp [Matrix.mul_assoc]
          _ = frenkelS ρ r * (frenkelQinv σ r * (σ.mat + (r : ℂ) • 1)) * frenkelSinv ρ r := by
              rw [frenkelS_mul_Sinv hρ hr, Matrix.mul_one]; simp [Matrix.mul_assoc]
          _ = 1 := by rw [frenkelQinv_mul_Q hσ hr, Matrix.mul_one, frenkelS_mul_Sinv hρ hr]
      calc inv1pM = 1 * inv1pM := (Matrix.one_mul _).symm
        _ = ((frenkelS ρ r * frenkelQinv σ r * frenkelS ρ r) * (1 + frenkelM ρ σ r)) * inv1pM := by rw [h2]
        _ = (frenkelS ρ r * frenkelQinv σ r * frenkelS ρ r) * ((1 + frenkelM ρ σ r) * inv1pM) := Matrix.mul_assoc _ _ _
        _ = frenkelS ρ r * frenkelQinv σ r * frenkelS ρ r := by rw [h1, Matrix.mul_one]
    have htr1 : inv1pM.trace = ∑ k : d, (((1 + hM.eigenvalues k)⁻¹ : ℝ) : ℂ) := by
      simp only [inv1pM]
      rw [Matrix.trace_mul_cycle, hUM_star, Matrix.one_mul, Matrix.trace_diagonal]
    have htr2 : (frenkelS ρ r * frenkelQinv σ r * frenkelS ρ r).trace =
        ∑ i : d, ∑ j : d, ((‖frenkelV ρ σ j i‖ ^ 2 * ((ρ.eigvals i + r) / (σ.eigvals j + r)) : ℝ) : ℂ) := by
      rw [Matrix.trace_mul_cycle, frenkelS_sq hρ hr, densityOp_add_smul_spectral ρ r]
      simp only [frenkelQinv]
      have hcyc : ((ρ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun i ↦ ((ρ.eigvals i + r : ℝ) : ℂ)) *
          star (ρ.eigUnitary : Matrix d d ℂ) *
          ((σ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun j ↦ (((σ.eigvals j + r)⁻¹ : ℝ) : ℂ)) *
          star (σ.eigUnitary : Matrix d d ℂ))).trace =
          (Matrix.diagonal (fun i ↦ ((ρ.eigvals i + r : ℝ) : ℂ)) * star (frenkelV ρ σ) *
            Matrix.diagonal (fun j ↦ (((σ.eigvals j + r)⁻¹ : ℝ) : ℂ)) * frenkelV ρ σ).trace := by
        have hVstar : star (frenkelV ρ σ) = star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ) := by
          simp [frenkelV, star_mul]
        rw [hVstar]
        calc ((ρ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun i ↦ ((ρ.eigvals i + r : ℝ) : ℂ)) *
              star (ρ.eigUnitary : Matrix d d ℂ) *
              ((σ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun j ↦ (((σ.eigvals j + r)⁻¹ : ℝ) : ℂ)) *
              star (σ.eigUnitary : Matrix d d ℂ))).trace
            = ((ρ.eigUnitary : Matrix d d ℂ) * (Matrix.diagonal (fun i ↦ ((ρ.eigvals i + r : ℝ) : ℂ)) *
                star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ) *
                Matrix.diagonal (fun j ↦ (((σ.eigvals j + r)⁻¹ : ℝ) : ℂ))) *
                star (σ.eigUnitary : Matrix d d ℂ)).trace := by simp [Matrix.mul_assoc]
          _ = (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ) *
                (Matrix.diagonal (fun i ↦ ((ρ.eigvals i + r : ℝ) : ℂ)) *
                star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ) *
                Matrix.diagonal (fun j ↦ (((σ.eigvals j + r)⁻¹ : ℝ) : ℂ)))).trace := by
                rw [Matrix.trace_mul_cycle]
          _ = (Matrix.diagonal (fun i ↦ ((ρ.eigvals i + r : ℝ) : ℂ)) *
                (star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ)) *
                Matrix.diagonal (fun j ↦ (((σ.eigvals j + r)⁻¹ : ℝ) : ℂ)) * frenkelV ρ σ).trace := by
                rw [Matrix.trace_mul_comm]; simp [frenkelV, Matrix.mul_assoc]
      rw [hcyc]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
        ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        Finset.sum_ite_eq]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Complex.ofReal_mul, Complex.ofReal_div, div_eq_mul_inv]
      have hnorm : star (frenkelV ρ σ j i) * frenkelV ρ σ j i = ((‖frenkelV ρ σ j i‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc ((ρ.eigvals i + r : ℝ) : ℂ) * star (frenkelV ρ σ j i) * (((σ.eigvals j + r)⁻¹ : ℝ) : ℂ) * frenkelV ρ σ j i
          = (star (frenkelV ρ σ j i) * frenkelV ρ σ j i) *
              (((ρ.eigvals i + r : ℝ) : ℂ) * (((σ.eigvals j + r : ℝ) : ℂ)⁻¹)) := by
              rw [Complex.ofReal_inv]; ring
        _ = _ := by rw [hnorm]
    have htr_re := congr_arg Complex.re (htr1.symm.trans (congr_arg Matrix.trace hinv_eq |>.trans htr2))
    simp only [← Complex.ofReal_sum, Complex.ofReal_re] at htr_re
    exact htr_re
  simp only [frenkelG, ← hlog_sum, ← htr_inv]
  have hterm_eq : ∀ k : d, hM.eigenvalues k / (1 + hM.eigenvalues k) = 1 - (1 + hM.eigenvalues k)⁻¹ := by
    intro k; have hpos : 0 < 1 + hM.eigenvalues k := by linarith [hlam_gt k]
    field_simp [ne_of_gt hpos]; ring
  simp_rw [hterm_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

private lemma frenkel_negEigCount_eq {ρ σ : DensityOp d} (hρ : ρ.mat.PosDef) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) =
      ∑ k : d, if 1 + t * (frenkelM_isHermitian ρ σ r).eigenvalues k < 0 then (1 : ℝ≥0∞) else 0 := by
  set hM := frenkelM_isHermitian ρ σ r
  have hUM_mul : (hM.eigenvectorUnitary : Matrix d d ℂ) * star (hM.eigenvectorUnitary : Matrix d d ℂ) = 1 :=
    Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hUM_star : star (hM.eigenvectorUnitary : Matrix d d ℂ) * (hM.eigenvectorUnitary : Matrix d d ℂ) = 1 :=
    Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have h1ptM_herm : (1 + (t : ℂ) • frenkelM ρ σ r).IsHermitian := by
    have htM : ((t : ℂ) • frenkelM ρ σ r).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hM.eq]
    exact Matrix.isHermitian_one.add htM
  have hcong_mat : frenkelS ρ r * (1 + (t : ℂ) • frenkelM ρ σ r) * (frenkelS ρ r)ᴴ =
      ((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat + (r : ℂ) • (1 : Matrix d d ℂ) := by
    rw [(frenkelS_isHermitian ρ r).eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      frenkelS_sq hρ hr, Matrix.mul_smul, Matrix.smul_mul]
    have hSMS : frenkelS ρ r * frenkelM ρ σ r * frenkelS ρ r = σ.mat - ρ.mat := by
      simp only [frenkelM, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (frenkelS ρ r) (frenkelSinv ρ r), frenkelS_mul_Sinv hρ hr,
        Matrix.one_mul, frenkelSinv_mul_S hρ hr, Matrix.mul_one]
    rw [hSMS]
    ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast; ring
  have hneg1 : negEigCount (isHermitian_pencil ρ σ r t) = negEigCount h1ptM_herm := by
    have hcong_herm : (frenkelS ρ r * (1 + (t : ℂ) • frenkelM ρ σ r) * (frenkelS ρ r)ᴴ).IsHermitian :=
      hcong_mat.symm ▸ isHermitian_pencil ρ σ r t
    calc negEigCount (isHermitian_pencil ρ σ r t)
        = negEigCount hcong_herm := negEigCount_eq_of_eq _ _ hcong_mat.symm
      _ = negEigCount h1ptM_herm :=
          negEigCount_congruence h1ptM_herm (frenkelS_mul_Sinv hρ hr) (frenkelSinv_mul_S hρ hr) hcong_herm
  let D : Matrix d d ℂ := Matrix.diagonal (fun k ↦ ((1 + t * hM.eigenvalues k : ℝ) : ℂ))
  have hD_herm : D.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext k; simp
  have h1ptM_eq : (hM.eigenvectorUnitary : Matrix d d ℂ) * D *
      (hM.eigenvectorUnitary : Matrix d d ℂ)ᴴ = 1 + (t : ℂ) • frenkelM ρ σ r := by
    have hM_spec : frenkelM ρ σ r = (hM.eigenvectorUnitary : Matrix d d ℂ) *
        Matrix.diagonal (Complex.ofReal ∘ hM.eigenvalues) *
        star (hM.eigenvectorUnitary : Matrix d d ℂ) := by
      simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM.spectral_theorem
    have hI_spec : (1 : Matrix d d ℂ) = (hM.eigenvectorUnitary : Matrix d d ℂ) *
        Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
        star (hM.eigenvectorUnitary : Matrix d d ℂ) := by
      rw [Matrix.diagonal_one, Matrix.mul_one, hUM_mul]
    symm
    calc (1 : Matrix d d ℂ) + (t : ℂ) • frenkelM ρ σ r
        = ((hM.eigenvectorUnitary : Matrix d d ℂ) * Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
            star (hM.eigenvectorUnitary : Matrix d d ℂ)) +
          (t : ℂ) • ((hM.eigenvectorUnitary : Matrix d d ℂ) *
            Matrix.diagonal (Complex.ofReal ∘ hM.eigenvalues) *
            star (hM.eigenvectorUnitary : Matrix d d ℂ)) :=
              congr_arg₂ (· + ·) hI_spec (congr_arg ((t : ℂ) • ·) hM_spec)
      _ = (hM.eigenvectorUnitary : Matrix d d ℂ) * D * (hM.eigenvectorUnitary : Matrix d d ℂ)ᴴ := by
          rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add]
          simp only [D, Matrix.star_eq_conjTranspose]
          congr 2; ext i j
          simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply,
            Complex.real_smul]
          split_ifs <;> simp [Complex.ofReal_add, Complex.ofReal_mul]
  have hneg2 : negEigCount h1ptM_herm = negEigCount hD_herm := by
    have hUDU_herm : ((hM.eigenvectorUnitary : Matrix d d ℂ) * D *
        (hM.eigenvectorUnitary : Matrix d d ℂ)ᴴ).IsHermitian :=
      h1ptM_eq.symm ▸ h1ptM_herm
    calc negEigCount h1ptM_herm
        = negEigCount hUDU_herm := negEigCount_eq_of_eq _ _ h1ptM_eq.symm
      _ = negEigCount hD_herm := negEigCount_congruence hD_herm hUM_mul hUM_star hUDU_herm
  have hneg3 : negEigCount hD_herm = (Finset.univ.filter (fun k : d ↦ 1 + t * hM.eigenvalues k < 0)).card := by
    have hsum_ind : ∑ k : d, (if hD_herm.eigenvalues k < 0 then (1 : ℝ) else 0) =
        ∑ k : d, (if 1 + t * hM.eigenvalues k < 0 then (1 : ℝ) else 0) :=
      spectral_sum_diagonal (fun k ↦ 1 + t * hM.eigenvalues k) hD_herm
        (f := fun x : ℝ ↦ if x < 0 then (1 : ℝ) else 0) (if_neg (lt_irrefl 0))
    have hcard1 : ((Finset.univ.filter (fun k : d ↦ hD_herm.eigenvalues k < 0)).card : ℝ) =
        ∑ k : d, if hD_herm.eigenvalues k < 0 then (1 : ℝ) else 0 := by simp [Finset.sum_boole]
    have hcard2 : ((Finset.univ.filter (fun k : d ↦ 1 + t * hM.eigenvalues k < 0)).card : ℝ) =
        ∑ k : d, if 1 + t * hM.eigenvalues k < 0 then (1 : ℝ) else 0 := by simp [Finset.sum_boole]
    exact Nat.cast_injective (R := ℝ) (hcard1.trans (hsum_ind.trans hcard2.symm))
  rw [hneg1, hneg2, hneg3]
  simp [Finset.sum_boole]

private lemma frenkelG_pos_and_lintegral {ρ σ : DensityOp d}
    (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) {r : ℝ} (hr : 0 < r) :
    0 ≤ frenkelG ρ σ r ∧
    ENNReal.ofReal (frenkelG ρ σ r) =
      ∫⁻ t : ℝ, (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) *
        ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) ∂volume := by
  set hM := frenkelM_isHermitian ρ σ r
  have hlam_gt : ∀ k : d, -1 < hM.eigenvalues k := frenkelM_eigenvalues_gt_neg_one hρ hσ hr
  have hg_spec := frenkelG_eq_spectral_sum hρ hσ hr
  have hterm_nn : ∀ k : d, 0 ≤ Real.log (1 + hM.eigenvalues k) -
      hM.eigenvalues k / (1 + hM.eigenvalues k) := by
    intro k
    have hpos : 0 < 1 + hM.eigenvalues k := by linarith [hlam_gt k]
    have hlog := Real.add_one_le_exp (-Real.log (1 + hM.eigenvalues k))
    rw [Real.exp_neg, Real.exp_log hpos] at hlog
    have h1 : 1 - (1 + hM.eigenvalues k)⁻¹ = hM.eigenvalues k / (1 + hM.eigenvalues k) := by
      field_simp [ne_of_gt hpos]; ring
    linarith
  refine ⟨by rw [hg_spec]; exact Finset.sum_nonneg fun k _ ↦ hterm_nn k, ?_⟩
  rw [hg_spec, ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ hterm_nn k)]
  symm
  simp_rw [frenkel_negEigCount_eq hρ hr, Finset.sum_mul]
  rw [MeasureTheory.lintegral_finset_sum]
  · apply Finset.sum_congr rfl; intro k _
    have hite : ∀ t : ℝ, (if 1 + t * hM.eigenvalues k < 0 then (1 : ℝ≥0∞) else 0) *
        ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) =
        if 1 + t * hM.eigenvalues k < 0 then ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) else 0 := by
      intro t; split_ifs <;> simp
    simp_rw [hite]
    exact lintegral_indicator_inv_abs_mul_sq_sub_one (hlam_gt k)
  · intro k _
    have hmeas_set : MeasurableSet {t : ℝ | 1 + t * hM.eigenvalues k < 0} :=
      measurableSet_lt (measurable_const.add (measurable_id.mul measurable_const)) measurable_const
    have hmeas_w : Measurable (fun t : ℝ ↦ ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2))) :=
      ENNReal.measurable_ofReal.comp (measurable_const.div
        (continuous_abs.measurable.mul ((measurable_id.sub measurable_const).pow_const 2)))
    exact (Measurable.ite hmeas_set measurable_const measurable_const).mul hmeas_w

/-! ### FTC + MCT and Tonelli Swap -/

private lemma frenkel_integral_g_eq_F0 {ρ σ : DensityOp d}
    (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (frenkelG ρ σ r) ∂volume =
      ENNReal.ofReal (frenkelF ρ σ 0) := by
  have hunion : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioc (0 : ℝ) ((n : ℝ) + 1) := by
    ext r; simp only [mem_Ioi, mem_iUnion, mem_Ioc]
    constructor
    · intro hr; obtain ⟨n, hn⟩ := exists_nat_gt r; exact ⟨n, hr, by linarith⟩
    · rintro ⟨n, h1, _⟩; exact h1
  have hmono_sets : Monotone (fun n : ℕ ↦ Ioc (0 : ℝ) ((n : ℝ) + 1)) := by
    intro m n hmn r ⟨h1, h2⟩
    exact ⟨h1, by linarith [show (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmn]⟩
  have hlim_int : Tendsto (fun n : ℕ ↦ ∫⁻ r in Ioc (0 : ℝ) ((n : ℝ) + 1),
      ENNReal.ofReal (frenkelG ρ σ r) ∂volume) atTop
      (𝓝 (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (frenkelG ρ σ r) ∂volume)) := by
    rw [hunion]
    have hg_meas : Measurable (fun r : ℝ ↦ ENNReal.ofReal (frenkelG ρ σ r)) := by
      apply ENNReal.measurable_ofReal.comp
      have h1 : Measurable (fun r : ℝ ↦ ∑ j : d, Real.log (σ.eigvals j + r)) :=
        Finset.measurable_sum _ fun j _ ↦ Real.measurable_log.comp (measurable_const.add measurable_id)
      have h2 : Measurable (fun r : ℝ ↦ ∑ i : d, Real.log (ρ.eigvals i + r)) :=
        Finset.measurable_sum _ fun i _ ↦ Real.measurable_log.comp (measurable_const.add measurable_id)
      have h3 : Measurable (fun r : ℝ ↦ ∑ i : d, ∑ j : d, ‖frenkelV ρ σ j i‖ ^ 2 *
          ((ρ.eigvals i + r) / (σ.eigvals j + r))) :=
        Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
          measurable_const.mul ((measurable_const.add measurable_id).div (measurable_const.add measurable_id))
      exact ((h1.sub h2).sub measurable_const).add h3
    exact tendsto_setLIntegral_monotone hmono_sets (fun _ ↦ measurableSet_Ioc) hg_meas
  have hval_n : ∀ n : ℕ, ∫⁻ r in Ioc (0 : ℝ) ((n : ℝ) + 1), ENNReal.ofReal (frenkelG ρ σ r) ∂volume =
      ENNReal.ofReal (frenkelF ρ σ 0 - frenkelF ρ σ ((n : ℝ) + 1)) := by
    intro n
    have hle : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hint : IntervalIntegrable (frenkelG ρ σ) volume 0 ((n : ℝ) + 1) :=
      ((frenkelG_continuousOn hρ hσ).mono (fun r hr ↦ hr.1)).intervalIntegrable_of_Icc hle
    have hftc : ∫ r in (0 : ℝ)..((n : ℝ) + 1), frenkelG ρ σ r =
        frenkelF ρ σ 0 - frenkelF ρ σ ((n : ℝ) + 1) := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun r ↦ -frenkelF ρ σ r) (f' := frenkelG ρ σ)
        (fun r hr ↦ by
          rw [uIcc_of_le hle] at hr
          simpa using (frenkelF_hasDerivAt hρ hσ hr.1).fun_neg) hint
      linarith
    rw [← hftc, intervalIntegral.integral_of_le hle,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint.1]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (frenkelG_pos_and_lintegral hρ hσ hr.1).1
  have hlim_rhs : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (frenkelF ρ σ 0 - frenkelF ρ σ ((n : ℝ) + 1))) atTop
      (𝓝 (ENNReal.ofReal (frenkelF ρ σ 0 - 0))) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    exact tendsto_const_nhds.sub
      ((frenkelF_tendsto_zero hρ hσ).comp
        (Filter.tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
  simp_rw [hval_n] at hlim_int
  simpa using tendsto_nhds_unique hlim_int hlim_rhs

private lemma frenkel_tonelli_swap (ρ σ : DensityOp d) :
    (∫⁻ r in Ioi (0 : ℝ), ∫⁻ t : ℝ,
        (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) *
          ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) ∂volume ∂volume) =
      ∫⁻ t : ℝ, (∫⁻ r in Ioi (0 : ℝ),
        (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) ∂volume) *
          ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) ∂volume := by
  have hmeas_prod : Measurable (fun p : ℝ × ℝ ↦
      (negEigCount (isHermitian_pencil ρ σ p.1 p.2) : ℝ≥0∞) *
        ENNReal.ofReal (1 / (|p.2| * (p.2 - 1) ^ 2))) :=
    (measurable_negEigCount_pencil ρ σ).mul
      (ENNReal.measurable_ofReal.comp (measurable_const.div
        ((continuous_abs.measurable.comp measurable_snd).mul
          ((measurable_snd.sub measurable_const).pow_const 2))))
  rw [MeasureTheory.lintegral_lintegral_swap
    (f := fun r t ↦ (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) *
      ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2))) hmeas_prod.aemeasurable]
  apply MeasureTheory.lintegral_congr
  intro t
  have hmeas_t : Measurable (fun x : ℝ ↦ (negEigCount (isHermitian_pencil ρ σ x t) : ℝ≥0∞)) :=
    (measurable_negEigCount_pencil ρ σ).comp (measurable_id.prodMk measurable_const)
  exact MeasureTheory.lintegral_mul_const _ hmeas_t

/-! ### Main Theorem: Frenkel's Integral Formula (Eq. 3.7) -/

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
  calc relEntropy ρ σ * ENNReal.ofReal (Real.log 2)
      = ENNReal.ofReal (frenkelF ρ σ 0) := (frenkelF_zero_eq hρ hσ).symm
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (frenkelG ρ σ r) ∂volume :=
        (frenkel_integral_g_eq_F0 hρ hσ).symm
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ t : ℝ,
          (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) *
            ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) ∂volume ∂volume :=
        MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
          (fun r hr ↦ (frenkelG_pos_and_lintegral hρ hσ hr).2)
    _ = ∫⁻ t : ℝ, (∫⁻ r in Ioi (0 : ℝ),
          (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) ∂volume) *
            ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) ∂volume :=
        frenkel_tonelli_swap ρ σ
    _ = _ := by
        apply MeasureTheory.lintegral_congr
        intro t
        have hA_t : (((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat).IsHermitian := by
          have h1 : (((1 - t : ℝ) : ℂ) • ρ.mat).IsHermitian := by
            rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, ρ.isHermitian.eq]
          have h2 : ((t : ℂ) • σ.mat).IsHermitian := by
            rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, σ.isHermitian.eq]
          exact h1.add h2
        have hpt : ∀ x : ℝ, (negEigCount (isHermitian_pencil ρ σ x t) : ℝ≥0∞) =
            (negEigCount (hA_t.add (show ((x : ℂ) • (1 : Matrix d d ℂ)).IsHermitian by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
                Complex.star_def, Complex.conj_ofReal])) : ℝ≥0∞) :=
          fun x ↦ congr_arg Nat.cast (negEigCount_eq_of_eq _ _ rfl)
        simp_rw [hpt]
        rw [lintegral_negEigCount_eq_negPartTrace hA_t,
          ← ENNReal.ofReal_mul (negPartTrace_nonneg hA_t), mul_one_div]

end PolarCodes
