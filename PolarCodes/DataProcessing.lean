/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.FrenkelIntegral

/-!
# Data Processing Inequality and Lemma 5.1(a)

This module proves:
1. **Data Processing Inequality (DPI)** for `relEntropy` under `partialTrace₂` for full-rank states
   (`relEntropy_partialTrace₂_le`), via Frenkel's integral formula (`relEntropy_frenkel_integral`)
   and Frenkel's Lemma 8 (`negPartTrace_map_le`).
2. **Data Processing Inequality (DPI)** for `qjs` under `partialTrace₂` for ALL density operators
   (`qjs_partialTrace₂_le`), via `qjs_eq_half_relEntropy_midpoint` and `ε ↓ 0` perturbation with
   the maximally mixed state `maxMixedState`.
3. **Roga–Fannes–Życzkowski** (`condEntropy_ge_one_sub_h2`) and **Lemma 5.1(a)**
   (`fidelityParam_le_sqrt_condEntropy`).
-/

open Matrix BigOperators Real Set Filter Topology MeasureTheory
open scoped ComplexOrder ENNReal

namespace PolarCodes

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-! ### Data Processing Inequality for `relEntropy` and `qjs` under `partialTrace₂` -/

private lemma partialTrace₂_posDef {ρ : DensityOp (d₁ × d₂)} (hρ : ρ.mat.PosDef) :
    (partialTrace₂ ρ).mat.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨(partialTrace₂ ρ).isHermitian, fun x hx ↦ ?_⟩
  have hsum' : star x ⬝ᵥ (partialTrace₂ ρ).mat.mulVec x =
      ∑ k : d₂, star (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) ⬝ᵥ
        ρ.mat.mulVec (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) := by
    trans ∑ k : d₂, ∑ i : d₁, star (x i) * ∑ j : d₁, ρ.mat (i, k) (j, k) * x j
    · simp only [partialTrace₂, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    · apply Finset.sum_congr rfl; intro k _
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro i _
      simp only [apply_ite star, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      congr 1; apply Finset.sum_congr rfl; intro j _
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hsum']
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : d₁, x i₀ ≠ 0 := by
    by_contra hall; push Not at hall; exact hx (funext hall)
  have hne_d₂ : Nonempty d₂ := by
    by_contra hemp
    have h0 : ρ.mat.trace = 0 := by
      simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
      apply Finset.sum_eq_zero; intro i _
      exact Finset.sum_eq_zero fun k _ ↦ absurd ⟨k⟩ hemp
    rw [ρ.trace_one] at h0; exact one_ne_zero h0
  obtain ⟨k₀⟩ := hne_d₂
  have hv_ne : (fun p : d₁ × d₂ ↦ if p.2 = k₀ then x p.1 else 0) ≠ 0 := by
    intro h0; exact hi₀ (by simpa using congr_fun h0 (i₀, k₀))
  have hpos₀ := (Matrix.posDef_iff_dotProduct_mulVec.mp hρ).2 hv_ne
  have hnn : ∀ k : d₂, 0 ≤ star (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) ⬝ᵥ
      ρ.mat.mulVec (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) :=
    fun k ↦ (Matrix.posSemidef_iff_dotProduct_mulVec.mp ρ.posSemidef).2 _
  have hsplit := Finset.add_sum_erase Finset.univ (fun k : d₂ ↦
    star (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) ⬝ᵥ
      ρ.mat.mulVec (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0)) (Finset.mem_univ k₀)
  have hrest : 0 ≤ ∑ k ∈ Finset.univ.erase k₀,
      star (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) ⬝ᵥ
        ρ.mat.mulVec (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) :=
    Finset.sum_nonneg fun k _ ↦ hnn k
  rw [← hsplit]; exact lt_of_lt_of_le hpos₀ (le_add_of_nonneg_right hrest)

/-- **Data Processing Inequality for `relEntropy`** under `partialTrace₂` (full-rank states):
`D(Tr₂ ρ ‖ Tr₂ σ) ≤ D(ρ ‖ σ)`. -/
theorem relEntropy_partialTrace₂_le {ρ σ : DensityOp (d₁ × d₂)}
    (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    relEntropy (partialTrace₂ ρ) (partialTrace₂ σ) ≤ relEntropy ρ σ := by
  have hρ' : (partialTrace₂ ρ).mat.PosDef := partialTrace₂_posDef hρ
  have hσ' : (partialTrace₂ σ).mat.PosDef := partialTrace₂_posDef hσ
  have hlog2_pos : 0 < ENNReal.ofReal (Real.log 2) := ENNReal.ofReal_pos.mpr (Real.log_pos (by norm_num))
  have hlog2_top : ENNReal.ofReal (Real.log 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine (ENNReal.mul_le_mul_iff_left (ne_of_gt hlog2_pos) hlog2_top).mp ?_
  rw [relEntropy_frenkel_integral hρ' hσ', relEntropy_frenkel_integral hρ hσ]
  apply MeasureTheory.lintegral_mono
  intro t
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (mul_nonneg (abs_nonneg t) (sq_nonneg _))
  have hlin : ((1 - t : ℝ) : ℂ) • (partialTrace₂ ρ).mat + (t : ℂ) • (partialTrace₂ σ).mat =
      partialTrace₂Mat d₁ d₂ (((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat) := by
    rw [map_add, map_smul, map_smul]; rfl
  have hA : (((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat).IsHermitian := by
    have h1 : (((1 - t : ℝ) : ℂ) • ρ.mat).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, ρ.isHermitian.eq]
    have h2 : ((t : ℂ) • σ.mat).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, σ.isHermitian.eq]
    exact h1.add h2
  have hB : (((1 - t : ℝ) : ℂ) • (partialTrace₂ ρ).mat + (t : ℂ) • (partialTrace₂ σ).mat).IsHermitian := by
    have h1 : (((1 - t : ℝ) : ℂ) • (partialTrace₂ ρ).mat).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
        (partialTrace₂ ρ).isHermitian.eq]
    have h2 : ((t : ℂ) • (partialTrace₂ σ).mat).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
        (partialTrace₂ σ).isHermitian.eq]
    exact h1.add h2
  have hB' : (partialTrace₂Mat d₁ d₂ (((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat)).IsHermitian :=
    hlin ▸ hB
  rw [negPartTrace_eq_of_eq hB hB' hlin]
  exact negPartTrace_map_le (partialTrace₂Mat d₁ d₂)
    (fun X hX ↦ partialTrace₂Mat_posSemidef hX)
    (fun X _ ↦ by rw [partialTrace₂Mat_trace]) hA hB'

private lemma unitary_overlap_col_sum (m τ : DensityOp d) (i : d) :
    ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 = 1 := by
  set W : Matrix d d ℂ := star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)
  have hW : star W * W = 1 := by
    have hm : (m.eigUnitary : Matrix d d ℂ) * star (m.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_mul_star_self m.eigUnitary
    have hτ : star (τ.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_star_mul_self τ.eigUnitary
    simp only [W, star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (m.eigUnitary : Matrix d d ℂ), hm, Matrix.one_mul, hτ]
  have h := congr_arg Complex.re (congr_fun (congr_fun hW i) i)
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at h
  convert h using 1
  apply Finset.sum_congr rfl; intro j _
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

private lemma unitary_overlap_row_sum (m τ : DensityOp d) (j : d) :
    ∑ i : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 = 1 := by
  set W : Matrix d d ℂ := star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)
  have hW : W * star W = 1 := by
    have hτ : (τ.eigUnitary : Matrix d d ℂ) * star (τ.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_mul_star_self τ.eigUnitary
    have hm : star (m.eigUnitary : Matrix d d ℂ) * (m.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_star_mul_self m.eigUnitary
    simp only [W, star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (τ.eigUnitary : Matrix d d ℂ), hτ, Matrix.one_mul, hm]
  have h := congr_arg Complex.re (congr_fun (congr_fun hW j) j)
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at h
  convert h using 1
  apply Finset.sum_congr rfl; intro i _
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- For full-rank states `ρ, σ ≻ 0`, `QJS(ρ, σ) = ½ (D(ρ ‖ m) + D(σ ‖ m))` where `m = (ρ + σ) / 2`. -/
lemma qjs_eq_half_relEntropy_midpoint {ρ σ : DensityOp d} (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    0 ≤ qjs ρ σ ∧ ENNReal.ofReal (qjs ρ σ) =
      (relEntropy ρ (DensityOp.midpoint ρ σ) + relEntropy σ (DensityOp.midpoint ρ σ)) / 2 := by
  set m := DensityOp.midpoint ρ σ
  have hm : m.mat.PosDef := by
    have h1 : ((1 - (1 / 2 : ℝ)) • ρ.mat).PosDef := hρ.smul (by norm_num : (0 : ℝ) < 1 - 1 / 2)
    have h2 : ((1 / 2 : ℝ) • σ.mat).PosSemidef := σ.posSemidef.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exact h1.add_posSemidef h2
  have hm_pos : ∀ j : d, 0 < m.eigvals j := hm.eigenvalues_pos
  have hsupp₁ : suppSubset ρ m := fun _ j _ hmj ↦ absurd hmj (ne_of_gt (hm_pos j))
  have hsupp₂ : suppSubset σ m := fun _ j _ hmj ↦ absurd hmj (ne_of_gt (hm_pos j))
  have hcross : ∀ (τ : DensityOp d),
      (∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (τ.eigvals i * (Real.log (τ.eigvals i) - Real.log (m.eigvals j)))) =
        -(∑ i : d, Real.negMulLog (τ.eigvals i)) -
          ∑ j : d, ((star (m.eigUnitary : Matrix d d ℂ) * τ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re *
            Real.log (m.eigvals j) := by
    intro τ
    have hdiag : ∀ j : d, ((star (m.eigUnitary : Matrix d d ℂ) * τ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re =
        ∑ i : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 * τ.eigvals i := by
      intro j
      have hspec : τ.mat = (τ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ τ.eigvals) *
          star (τ.eigUnitary : Matrix d d ℂ) := by
        simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using τ.isHermitian.spectral_theorem
      set W : Matrix d d ℂ := star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)
      have hmul : star (m.eigUnitary : Matrix d d ℂ) * τ.mat * (m.eigUnitary : Matrix d d ℂ) =
          W * Matrix.diagonal (Complex.ofReal ∘ τ.eigvals) * star W := by
        rw [hspec]; simp only [W, Matrix.star_mul, star_star, Matrix.mul_assoc]
      rw [hmul]
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, Function.comp_apply,
        mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [mul_right_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    congr 1
    · simp only [Real.negMulLog, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_mul, unitary_overlap_col_sum m τ i, one_mul]; ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [hdiag j, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _; ring
  have hD_nn : ∀ (τ : DensityOp d), τ.mat.PosDef →
      0 ≤ (∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (τ.eigvals i * (Real.log (τ.eigvals i) - Real.log (m.eigvals j)))) / Real.log 2 := by
    intro τ hτ
    apply div_nonneg _ (le_of_lt (Real.log_pos (by norm_num)))
    have hklein : ∀ i j : d,
        τ.eigvals i - m.eigvals j ≤ τ.eigvals i * (Real.log (τ.eigvals i) - Real.log (m.eigvals j)) := by
      intro i j
      have hx : 0 < τ.eigvals i := hτ.eigenvalues_pos i
      have hy : 0 < m.eigvals j := hm_pos j
      have hlog := Real.add_one_le_exp (Real.log (m.eigvals j / τ.eigvals i))
      rw [Real.exp_log (div_pos hy hx), Real.log_div (ne_of_gt hy) (ne_of_gt hx)] at hlog
      have := mul_le_mul_of_nonneg_left hlog (le_of_lt hx)
      have hsimp : τ.eigvals i * (m.eigvals j / τ.eigvals i) = m.eigvals j := mul_div_cancel₀ _ (ne_of_gt hx)
      linarith
    have hsum_ge : (∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
        (τ.eigvals i - m.eigvals j)) ≤ _ :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (hklein i j) (sq_nonneg _)
    have hzero : (∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
        (τ.eigvals i - m.eigvals j)) = 0 := by
      have ha : ∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          τ.eigvals i = ∑ i : d, τ.eigvals i := by
        apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_mul, unitary_overlap_col_sum, one_mul]
      have hb : ∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          m.eigvals j = ∑ j : d, m.eigvals j := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
        rw [← Finset.sum_mul, unitary_overlap_row_sum, one_mul]
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [ha, hb, τ.sum_eigvals, m.sum_eigvals, sub_self]
    linarith
  suffices hreal : qjs ρ σ =
      ((∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (m.eigvals j)))) / Real.log 2 +
       (∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (σ.eigvals i * (Real.log (σ.eigvals i) - Real.log (m.eigvals j)))) / Real.log 2) / 2 by
    refine ⟨by rw [hreal]; linarith [hD_nn ρ hρ, hD_nn σ hσ], ?_⟩
    unfold relEntropy
    rw [if_pos hsupp₁, if_pos hsupp₂, ← ENNReal.ofReal_add (hD_nn ρ hρ) (hD_nn σ hσ),
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), hreal]
  rw [hcross ρ, hcross σ]
  have hmid_diag : ∀ j : d,
      (((star (m.eigUnitary : Matrix d d ℂ) * ρ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re +
       ((star (m.eigUnitary : Matrix d d ℂ) * σ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re) / 2 =
      m.eigvals j := by
    intro j
    have hm_star : star (m.eigUnitary : Matrix d d ℂ) * (m.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_star_mul_self m.eigUnitary
    have h1 : star (m.eigUnitary : Matrix d d ℂ) * m.mat * (m.eigUnitary : Matrix d d ℂ) =
        Matrix.diagonal (Complex.ofReal ∘ m.eigvals) := by
      have hspec : m.mat = (m.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ m.eigvals) *
          star (m.eigUnitary : Matrix d d ℂ) := by
        simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using m.isHermitian.spectral_theorem
      rw [hspec]; simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star (m.eigUnitary : Matrix d d ℂ)), hm_star,
        Matrix.one_mul, Matrix.mul_one]
    have h2 := congr_arg Complex.re (congr_fun (congr_fun h1 j) j)
    have h3 : (star (m.eigUnitary : Matrix d d ℂ) * m.mat * (m.eigUnitary : Matrix d d ℂ)) j j =
        ((1 / 2 : ℝ) : ℂ) * (star (m.eigUnitary : Matrix d d ℂ) * ρ.mat * (m.eigUnitary : Matrix d d ℂ)) j j +
        ((1 / 2 : ℝ) : ℂ) * (star (m.eigUnitary : Matrix d d ℂ) * σ.mat * (m.eigUnitary : Matrix d d ℂ)) j j := by
      have hm_eq : m.mat = (1 / 2 : ℝ) • ρ.mat + (1 / 2 : ℝ) • σ.mat := by
        simp only [m, DensityOp.midpoint, DensityOp.mix]; norm_num
      rw [hm_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
        Complex.real_smul, Complex.real_smul]
    rw [h3, Complex.add_re] at h2
    simp only [Matrix.diagonal_apply_eq, Function.comp_apply, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at h2
    linarith
  have hsum_add :
      (∑ j : d, ((star (m.eigUnitary : Matrix d d ℂ) * ρ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re * Real.log (m.eigvals j)) +
      (∑ j : d, ((star (m.eigUnitary : Matrix d d ℂ) * σ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re * Real.log (m.eigvals j)) =
      -2 * ∑ j : d, Real.negMulLog (m.eigvals j) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    unfold Real.negMulLog
    have := hmid_diag j
    linarith [show (((star (m.eigUnitary : Matrix d d ℂ) * ρ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re +
      ((star (m.eigUnitary : Matrix d d ℂ) * σ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re) *
      Real.log (m.eigvals j) = 2 * m.eigvals j * Real.log (m.eigvals j) by rw [← this]; ring]
  unfold qjs vonNeumannEntropy
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog2]
  change (∑ i : d, Real.negMulLog (m.eigvals i)) * 2 -
      (∑ i : d, Real.negMulLog (ρ.eigvals i) + ∑ i : d, Real.negMulLog (σ.eigvals i)) = _
  linarith [hsum_add]

/-- Maximally mixed density operator `I / d` on any nonempty finite Hilbert space. -/
noncomputable def maxMixedState (d : Type*) [Fintype d] [DecidableEq d] [Nonempty d] : DensityOp d where
  mat := ((Fintype.card d : ℝ)⁻¹ : ℝ) • (1 : Matrix d d ℂ)
  posSemidef :=
    (Matrix.PosSemidef.one (n := d) (R := ℂ)).smul (inv_nonneg.mpr (Nat.cast_nonneg _))
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_one, Complex.real_smul, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
      Complex.ofReal_one]

/-- Continuity of `vonNeumannEntropy ((1 - ε) ρ + ε I/d)` as `ε → 0+`. -/
lemma tendsto_vonNeumannEntropy_mix_maxMixed [Nonempty d] (ρ : DensityOp d) :
    Tendsto (fun ε : ℝ ↦
      if h : 0 ≤ ε ∧ ε ≤ 1 then vonNeumannEntropy (DensityOp.mix ε h.1 h.2 ρ (maxMixedState d))
      else vonNeumannEntropy ρ) (𝓝[>] 0) (𝓝 (vonNeumannEntropy ρ)) := by
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (if h : 0 ≤ ε ∧ ε ≤ 1 then vonNeumannEntropy (DensityOp.mix ε h.1 h.2 ρ (maxMixedState d))
        else vonNeumannEntropy ρ) =
      (∑ i : d, Real.negMulLog ((1 - ε) * ρ.eigvals i + ε * (Fintype.card d : ℝ)⁻¹)) / Real.log 2 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
    have h01 : 0 ≤ ε ∧ ε ≤ 1 := ⟨le_of_lt hε.1, le_of_lt hε.2⟩
    rw [dif_pos h01]
    set τ := DensityOp.mix ε h01.1 h01.2 ρ (maxMixedState d)
    set U : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
    have hU_mul : U * star U = 1 := Unitary.coe_mul_star_self ρ.eigUnitary
    have hU_star : star U * U = 1 := Unitary.coe_star_mul_self ρ.eigUnitary
    let lam : d → ℝ := fun i ↦ (1 - ε) * ρ.eigvals i + ε * (Fintype.card d : ℝ)⁻¹
    have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext i; simp
    have hτ_eq : τ.mat = U * Matrix.diagonal (Complex.ofReal ∘ lam) * star U := by
      have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by
        simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
      have h1 : (1 : Matrix d d ℂ) = U * 1 * star U := by
        rw [Matrix.mul_one, hU_mul]
      have hterm1 : (1 - ε) • ρ.mat = U * ((1 - ε) • Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals)) * star U := by
        rw [hspec, Matrix.mul_smul, Matrix.smul_mul]
      have hterm2 : ε • (maxMixedState d).mat = U * ((ε * (Fintype.card d : ℝ)⁻¹) • (1 : Matrix d d ℂ)) * star U := by
        simp only [maxMixedState, smul_smul]
        conv_lhs => rw [h1]
        rw [Matrix.mul_smul, Matrix.smul_mul]
      show (1 - ε) • ρ.mat + ε • (maxMixedState d).mat = _
      rw [hterm1, hterm2, ← Matrix.add_mul, ← Matrix.mul_add]
      congr 2; ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
        Function.comp_apply, lam, Complex.real_smul]
      split_ifs
      · push_cast; ring
      · simp
    have hcp : τ.mat.charpoly = (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
      rw [hτ_eq, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU_star, Matrix.one_mul]
    unfold vonNeumannEntropy DensityOp.eigvals
    congr 1
    trans ∑ i : d, Real.negMulLog (hD_herm.eigenvalues i)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow τ.isHermitian hD_herm (k := 0) (l := 0)
        (by rw [pow_zero, mul_one, mul_one, hcp]) (by simp [Real.negMulLog])
    · exact spectral_sum_diagonal lam hD_herm (by simp [Real.negMulLog])
  rw [tendsto_congr' heq]
  have hcont : Continuous (fun ε : ℝ ↦
      (∑ i : d, Real.negMulLog ((1 - ε) * ρ.eigvals i + ε * (Fintype.card d : ℝ)⁻¹)) / Real.log 2) :=
    (continuous_finset_sum _ fun i _ ↦
      Real.continuous_negMulLog.comp
        (((continuous_const.sub continuous_id).mul continuous_const).add
          (continuous_id.mul continuous_const))).div_const _
  simpa [vonNeumannEntropy] using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

private lemma tendsto_qjs_mix_maxMixed {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (a b : DensityOp α) :
    Tendsto (fun ε : ℝ ↦
      if h : 0 ≤ ε ∧ ε ≤ 1 then
        qjs (DensityOp.mix ε h.1 h.2 a (maxMixedState α))
            (DensityOp.mix ε h.1 h.2 b (maxMixedState α))
      else qjs a b) (𝓝[>] 0) (𝓝 (qjs a b)) := by
  have hmid_mix : ∀ (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1),
      (DensityOp.midpoint (DensityOp.mix ε h0 h1 a (maxMixedState α))
          (DensityOp.mix ε h0 h1 b (maxMixedState α))).mat =
        (DensityOp.mix ε h0 h1 (DensityOp.midpoint a b) (maxMixedState α)).mat := by
    intro ε h0 h1; ext i j
    simp only [DensityOp.midpoint, DensityOp.mix, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast; ring
  have heq : (fun ε : ℝ ↦
      if h : 0 ≤ ε ∧ ε ≤ 1 then
        qjs (DensityOp.mix ε h.1 h.2 a (maxMixedState α))
            (DensityOp.mix ε h.1 h.2 b (maxMixedState α))
      else qjs a b) =
      fun ε : ℝ ↦
        (if h : 0 ≤ ε ∧ ε ≤ 1 then vonNeumannEntropy (DensityOp.mix ε h.1 h.2 (DensityOp.midpoint a b) (maxMixedState α))
          else vonNeumannEntropy (DensityOp.midpoint a b)) -
        ((if h : 0 ≤ ε ∧ ε ≤ 1 then vonNeumannEntropy (DensityOp.mix ε h.1 h.2 a (maxMixedState α))
          else vonNeumannEntropy a) +
         (if h : 0 ≤ ε ∧ ε ≤ 1 then vonNeumannEntropy (DensityOp.mix ε h.1 h.2 b (maxMixedState α))
          else vonNeumannEntropy b)) / 2 := by
    ext ε; by_cases h : 0 ≤ ε ∧ ε ≤ 1
    · rw [dif_pos h, dif_pos h, dif_pos h, dif_pos h]
      simp only [qjs]
      rw [vonNeumannEntropy_eq_of_mat_eq (hmid_mix ε h.1 h.2)]
    · rw [dif_neg h, dif_neg h, dif_neg h, dif_neg h]; rfl
  rw [heq]
  exact (tendsto_vonNeumannEntropy_mix_maxMixed (DensityOp.midpoint a b)).sub
    (((tendsto_vonNeumannEntropy_mix_maxMixed a).add (tendsto_vonNeumannEntropy_mix_maxMixed b)).div_const 2)

private lemma mix_maxMixedState_posDef {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (τ : DensityOp α) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (DensityOp.mix ε (le_of_lt h0) h1 τ (maxMixedState α)).mat.PosDef := by
  have hA : ((1 - ε) • τ.mat).PosSemidef := τ.posSemidef.smul (by linarith)
  have hB : (ε • (maxMixedState α).mat).PosDef := by
    simp only [maxMixedState, smul_smul]
    exact (Matrix.PosDef.one (n := α) (R := ℂ)).smul
      (mul_pos h0 (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)))
  simpa [DensityOp.mix, add_comm] using hB.add_posSemidef hA

/-- **Data Processing Inequality for QJS** under `partialTrace₂` (for ALL density operators `ρ, σ`):
`QJS(Tr₂ ρ, Tr₂ σ) ≤ QJS(ρ, σ)`. -/
theorem qjs_partialTrace₂_le (ρ σ : DensityOp (d₁ × d₂)) :
    qjs (partialTrace₂ ρ) (partialTrace₂ σ) ≤ qjs ρ σ := by
  have hne : Nonempty (d₁ × d₂) := by
    by_contra hemp
    have h0 : ρ.mat.trace = 0 := by
      simp only [Matrix.trace, Matrix.diag]
      exact Finset.sum_eq_zero fun p _ ↦ absurd ⟨p⟩ hemp
    rw [ρ.trace_one] at h0; exact one_ne_zero h0
  haveI : Nonempty (d₁ × d₂) := hne
  haveI : Nonempty d₁ := ⟨(Classical.arbitrary (d₁ × d₂)).1⟩
  haveI : Nonempty d₂ := ⟨(Classical.arbitrary (d₁ × d₂)).2⟩
  have hpt_mix : ∀ (τ : DensityOp (d₁ × d₂)) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1),
      (partialTrace₂ (DensityOp.mix ε h0 h1 τ (maxMixedState (d₁ × d₂)))).mat =
        (DensityOp.mix ε h0 h1 (partialTrace₂ τ) (maxMixedState d₁)).mat := by
    intro τ ε h0 h1
    ext i j
    simp only [partialTrace₂, DensityOp.mix, maxMixedState, Matrix.of_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Complex.real_smul, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Prod.mk.injEq, true_and, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_prod, Nat.cast_mul, mul_inv]
      have hd2 : (Fintype.card d₂ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      push_cast; field_simp [hd2]
    · simp only [hij, ↓reduceIte, Prod.mk.injEq, false_and, Finset.sum_const_zero, mul_zero]
  have hpt_mid : ∀ (a b : DensityOp (d₁ × d₂)),
      (partialTrace₂ (DensityOp.midpoint a b)).mat = (DensityOp.midpoint (partialTrace₂ a) (partialTrace₂ b)).mat := by
    intro a b; ext i j
    simp [partialTrace₂, DensityOp.midpoint, DensityOp.mix, Complex.real_smul, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hle_eps : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (if h : 0 ≤ ε ∧ ε ≤ 1 then
        qjs (DensityOp.mix ε h.1 h.2 (partialTrace₂ ρ) (maxMixedState d₁))
            (DensityOp.mix ε h.1 h.2 (partialTrace₂ σ) (maxMixedState d₁))
        else qjs (partialTrace₂ ρ) (partialTrace₂ σ)) ≤
      (if h : 0 ≤ ε ∧ ε ≤ 1 then
        qjs (DensityOp.mix ε h.1 h.2 ρ (maxMixedState (d₁ × d₂)))
            (DensityOp.mix ε h.1 h.2 σ (maxMixedState (d₁ × d₂)))
        else qjs ρ σ) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
    have h01 : 0 ≤ ε ∧ ε ≤ 1 := ⟨le_of_lt hε.1, le_of_lt hε.2⟩
    rw [dif_pos h01, dif_pos h01]
    set ρ_ε := DensityOp.mix ε h01.1 h01.2 ρ (maxMixedState (d₁ × d₂))
    set σ_ε := DensityOp.mix ε h01.1 h01.2 σ (maxMixedState (d₁ × d₂))
    have hρ_pd : ρ_ε.mat.PosDef := mix_maxMixedState_posDef ρ hε.1 (le_of_lt hε.2)
    have hσ_pd : σ_ε.mat.PosDef := mix_maxMixedState_posDef σ hε.1 (le_of_lt hε.2)
    have hptρ : partialTrace₂ ρ_ε = DensityOp.mix ε h01.1 h01.2 (partialTrace₂ ρ) (maxMixedState d₁) := by
      cases h : partialTrace₂ ρ_ε; cases h' : DensityOp.mix ε h01.1 h01.2 (partialTrace₂ ρ) (maxMixedState d₁)
      have hm := hpt_mix ρ ε h01.1 h01.2
      rw [h, h'] at hm; congr
    have hptσ : partialTrace₂ σ_ε = DensityOp.mix ε h01.1 h01.2 (partialTrace₂ σ) (maxMixedState d₁) := by
      cases h : partialTrace₂ σ_ε; cases h' : DensityOp.mix ε h01.1 h01.2 (partialTrace₂ σ) (maxMixedState d₁)
      have hm := hpt_mix σ ε h01.1 h01.2
      rw [h, h'] at hm; congr
    rw [← hptρ, ← hptσ]
    have hm_pd : (DensityOp.midpoint ρ_ε σ_ε).mat.PosDef :=
      (hρ_pd.smul (by norm_num : (0 : ℝ) < 1 - 1 / 2)).add_posSemidef
        (σ_ε.posSemidef.smul (by norm_num : (0 : ℝ) ≤ 1 / 2))
    have hdpi1 := relEntropy_partialTrace₂_le hρ_pd hm_pd
    have hdpi2 := relEntropy_partialTrace₂_le hσ_pd hm_pd
    have hmid_eq : partialTrace₂ (DensityOp.midpoint ρ_ε σ_ε) =
        DensityOp.midpoint (partialTrace₂ ρ_ε) (partialTrace₂ σ_ε) := by
      cases h : partialTrace₂ (DensityOp.midpoint ρ_ε σ_ε)
      cases h' : DensityOp.midpoint (partialTrace₂ ρ_ε) (partialTrace₂ σ_ε)
      have hm := hpt_mid ρ_ε σ_ε; rw [h, h'] at hm; congr
    rw [hmid_eq] at hdpi1 hdpi2
    have hptρ_pd : (partialTrace₂ ρ_ε).mat.PosDef := by
      rw [hptρ]; exact mix_maxMixedState_posDef (partialTrace₂ ρ) hε.1 (le_of_lt hε.2)
    have hptσ_pd : (partialTrace₂ σ_ε).mat.PosDef := by
      rw [hptσ]; exact mix_maxMixedState_posDef (partialTrace₂ σ) hε.1 (le_of_lt hε.2)
    have henn : ENNReal.ofReal (qjs (partialTrace₂ ρ_ε) (partialTrace₂ σ_ε)) ≤
        ENNReal.ofReal (qjs ρ_ε σ_ε) := by
      rw [(qjs_eq_half_relEntropy_midpoint hptρ_pd hptσ_pd).2, (qjs_eq_half_relEntropy_midpoint hρ_pd hσ_pd).2]
      exact ENNReal.div_le_div_right (add_le_add hdpi1 hdpi2) 2
    have hqjs_nn : 0 ≤ qjs ρ_ε σ_ε := (qjs_eq_half_relEntropy_midpoint hρ_pd hσ_pd).1
    exact (ENNReal.ofReal_le_ofReal_iff hqjs_nn).mp henn
  exact le_of_tendsto_of_tendsto (tendsto_qjs_mix_maxMixed (partialTrace₂ ρ) (partialTrace₂ σ))
    (tendsto_qjs_mix_maxMixed ρ σ) hle_eps

/-! ### Lemma 5.1(a): Roga–Fannes–Życzkowski and Fidelity–Entropy Relations -/

/-- Exact QJS of two pure states `|ψ₀⟩⟨ψ₀|` and `|ψ₁⟩⟨ψ₁|` with overlap `f = ‖⟨ψ₀|ψ₁⟩‖`:
`QJS(|ψ₀⟩⟨ψ₀|, |ψ₁⟩⟨ψ₁|) = h₂((1 - f) / 2)`. -/
lemma qjs_pureState (ψ₀ ψ₁ : d → ℂ)
    (hψ₀ : ∑ k : d, ‖ψ₀ k‖ ^ 2 = 1) (hψ₁ : ∑ k : d, ‖ψ₁ k‖ ^ 2 = 1) :
    qjs (pureState ψ₀ hψ₀) (pureState ψ₁ hψ₁) =
      h2 ((1 - ‖∑ k : d, star (ψ₀ k) * ψ₁ k‖) / 2) := by
  set f : ℝ := ‖∑ k : d, star (ψ₀ k) * ψ₁ k‖
  have hS_pure : ∀ (ψ : d → ℂ) (hψ : ∑ k : d, ‖ψ k‖ ^ 2 = 1), vonNeumannEntropy (pureState ψ hψ) = 0 := by
    intro ψ hψ
    let M : Matrix d Unit ℂ := Matrix.of fun k _ ↦ ψ k
    have hMMH : M * Mᴴ = (pureState ψ hψ).mat := by
      ext i j; simp [M, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hMHM : Mᴴ * M = 1 := by
      ext _ _
      simp only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply_eq]
      have hterm : ∀ k : d, star (ψ k) * ψ k = ((‖ψ k‖ ^ 2 : ℝ) : ℂ) := by
        intro k; rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp_rw [hterm, ← Complex.ofReal_sum, hψ, Complex.ofReal_one]
    have hcp := charpoly_mul_conjTranspose_eq M
    rw [hMMH, hMHM] at hcp
    unfold vonNeumannEntropy DensityOp.eigvals
    have hsum := spectral_sum_eq_of_charpoly_mul_X_pow (pureState ψ hψ).isHermitian
      (Matrix.isHermitian_one (n := Unit) (α := ℂ)) hcp (f := Real.negMulLog) Real.negMulLog_zero
    have h1 : ∑ i : Unit, Real.negMulLog ((Matrix.isHermitian_one (n := Unit) (α := ℂ)).eigenvalues i) = 0 := by
      have hdiag : (1 : Matrix Unit Unit ℂ) = Matrix.diagonal (Complex.ofReal ∘ fun _ : Unit ↦ (1 : ℝ)) := by
        ext _ _; simp
      have hsum2 := spectral_sum_diagonal (fun _ : Unit ↦ (1 : ℝ))
        (by rw [← hdiag]; exact Matrix.isHermitian_one) (f := Real.negMulLog) Real.negMulLog_zero
      simpa [Real.negMulLog] using hsum2
    rw [hsum, h1, zero_div]
  unfold qjs
  rw [hS_pure ψ₀ hψ₀, hS_pure ψ₁ hψ₁, add_zero, zero_div, sub_zero]
  let A : Matrix d Bool ℂ := Matrix.of fun k b ↦ ((Real.sqrt 2 : ℂ)⁻¹) * if b = false then ψ₀ k else ψ₁ k
  have hsq2' : ((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; push_cast; ring
  have hAAH : A * Aᴴ = (DensityOp.midpoint (pureState ψ₀ hψ₀) (pureState ψ₁ hψ₁)).mat := by
    ext i j
    simp only [A, DensityOp.midpoint, DensityOp.mix, pureState, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
      Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false, Complex.real_smul, star_mul']
    have hrew : ∀ a b : ℂ,
        (Real.sqrt 2 : ℂ)⁻¹ * a * (star ((Real.sqrt 2 : ℂ)⁻¹) * star b) = (1 / 2 : ℂ) * (a * star b) := by
      intro a b
      calc _
          = ((Real.sqrt 2 : ℂ)⁻¹ * star ((Real.sqrt 2 : ℂ)⁻¹)) * (a * star b) := by ring
        _ = (1 / 2 : ℂ) * (a * star b) := by rw [hsq2']
    rw [hrew, hrew]; push_cast; ring
  set z : ℂ := ∑ k : d, star (ψ₀ k) * ψ₁ k
  have hAHA : Aᴴ * A = Matrix.of fun a b : Bool ↦
      if a = b then (1 / 2 : ℂ) else if a = false then (1 / 2 : ℂ) * z else (1 / 2 : ℂ) * star z := by
    have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by rw [mul_comm, hsq2']
    have hφ : ∀ (ψ : d → ℂ) (hψ : ∑ k : d, ‖ψ k‖ ^ 2 = 1), ∑ k : d, star (ψ k) * ψ k = 1 := by
      intro ψ hψ
      have ht : ∀ k : d, star (ψ k) * ψ k = ((‖ψ k‖ ^ 2 : ℝ) : ℂ) := by
        intro k; rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp_rw [ht, ← Complex.ofReal_sum, hψ, Complex.ofReal_one]
    ext a b
    simp only [A, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul']
    cases a <;> cases b
    · simp only [↓reduceIte]
      calc _
          = (1 / 2 : ℂ) * ∑ k : d, star (ψ₀ k) * ψ₀ k := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
            calc _
                = (star ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹) * (star (ψ₀ k) * ψ₀ k) := by ring
              _ = (1 / 2 : ℂ) * (star (ψ₀ k) * ψ₀ k) := by rw [hsq2]
        _ = 1 / 2 := by rw [hφ ψ₀ hψ₀, mul_one]
    · simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, z]
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
      calc _
          = (star ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹) * (star (ψ₀ k) * ψ₁ k) := by ring
        _ = (1 / 2 : ℂ) * (star (ψ₀ k) * ψ₁ k) := by rw [hsq2]
    · simp only [Bool.true_eq_false, ↓reduceIte, z, star_sum, star_mul', star_star]
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
      calc _
          = (star ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹) * (star (ψ₁ k) * ψ₀ k) := by ring
        _ = (1 / 2 : ℂ) * (ψ₀ k * star (ψ₁ k)) := by rw [hsq2]; ring
    · simp only [Bool.true_eq_false, ↓reduceIte]
      calc _
          = (1 / 2 : ℂ) * ∑ k : d, star (ψ₁ k) * ψ₁ k := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
            calc _
                = (star ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹) * (star (ψ₁ k) * ψ₁ k) := by ring
              _ = (1 / 2 : ℂ) * (star (ψ₁ k) * ψ₁ k) := by rw [hsq2]
        _ = 1 / 2 := by rw [hφ ψ₁ hψ₁, mul_one]
  let lam : Bool → ℝ := fun b ↦ if b = false then (1 - f) / 2 else (1 + f) / 2
  have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext b; simp
  have hcp_AHA : (Aᴴ * A).charpoly = (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
    rw [charpoly_diagonal_complex, Fintype.prod_bool]
    simp only [lam, Function.comp_apply, ↓reduceIte, Bool.true_eq_false]
    rw [hAHA, Matrix.charpoly, Matrix.charmatrix, Matrix.det_apply]
    have hperm : (Finset.univ : Finset (Equiv.Perm Bool)) = {1, Equiv.swap false true} := by
      ext σ; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      by_cases h : σ false = false
      · left; ext b; cases b
        · exact h
        · have hne : σ true ≠ σ false := σ.injective.ne (by decide)
          rw [h] at hne; cases h' : σ true <;> simp_all
      · right; ext b; cases b
        · cases h' : σ false <;> simp_all
        · have h1 : σ false = true := by cases h' : σ false <;> simp_all
          have hne : σ true ≠ σ false := σ.injective.ne (by decide)
          rw [h1] at hne; cases h' : σ true <;> simp_all
    rw [hperm, Finset.sum_pair (by decide)]
    simp only [Equiv.Perm.sign_one, Equiv.Perm.sign_swap (by decide : false ≠ true),
      Units.val_one, Units.val_neg, one_smul, neg_smul, Fintype.prod_bool,
      Equiv.Perm.coe_one, id_eq, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.of_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false,
      zero_sub, sub_zero, map_mul, mul_neg, neg_mul, neg_neg]
    have hzz : Polynomial.C (1 / 2 : ℂ) * Polynomial.C z *
        (Polynomial.C (1 / 2 : ℂ) * Polynomial.C (star z)) =
        Polynomial.C ((f / 2 : ℝ) : ℂ) * Polynomial.C ((f / 2 : ℝ) : ℂ) := by
      simp only [← map_mul]; congr 1
      have h1 : z * star z = ((f ^ 2 : ℝ) : ℂ) := by
        simp only [f, z]; rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc (1 / 2 : ℂ) * z * ((1 / 2 : ℂ) * star z) = (1 / 4 : ℂ) * (z * star z) := by ring
        _ = (1 / 4 : ℂ) * ((f ^ 2 : ℝ) : ℂ) := by rw [h1]
        _ = _ := by push_cast; ring
    have h1 : Polynomial.C (((1 + f) / 2 : ℝ) : ℂ) = Polynomial.C (1 / 2 : ℂ) + Polynomial.C ((f / 2 : ℝ) : ℂ) := by
      rw [← map_add]; congr 1; push_cast; ring
    have h2 : Polynomial.C (((1 - f) / 2 : ℝ) : ℂ) = Polynomial.C (1 / 2 : ℂ) - Polynomial.C ((f / 2 : ℝ) : ℂ) := by
      rw [← map_sub]; congr 1; push_cast; ring
    rw [h1, h2, hzz]
    simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_one]
    ring
  have hcp_all : (DensityOp.midpoint (pureState ψ₀ hψ₀) (pureState ψ₁ hψ₁)).mat.charpoly * Polynomial.X ^ (Fintype.card Bool) =
      (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly * Polynomial.X ^ (Fintype.card d) := by
    have h := charpoly_mul_conjTranspose_eq A
    rwa [hAAH, hcp_AHA] at h
  unfold vonNeumannEntropy DensityOp.eigvals
  have hsum : ∑ i : d, Real.negMulLog ((DensityOp.midpoint (pureState ψ₀ hψ₀) (pureState ψ₁ hψ₁)).isHermitian.eigenvalues i) =
      ∑ b : Bool, Real.negMulLog (lam b) := by
    trans ∑ b : Bool, Real.negMulLog (hD_herm.eigenvalues b)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow
        (DensityOp.midpoint (pureState ψ₀ hψ₀) (pureState ψ₁ hψ₁)).isHermitian
        hD_herm hcp_all (f := Real.negMulLog) Real.negMulLog_zero
    · exact spectral_sum_diagonal lam hD_herm (f := Real.negMulLog) Real.negMulLog_zero
  rw [hsum, Fintype.sum_bool, h2_eq_negMulLog]
  simp only [lam, ↓reduceIte, Bool.true_eq_false]
  congr 1; rw [show 1 - (1 - f) / 2 = (1 + f) / 2 by ring, add_comm]

/-- **Roga–Fannes–Życzkowski Inequality** (`1 - H(W) ≤ h₂((1 - Z(W)) / 2)`):
For every binary-input c-q channel `W`, `H(W) ≥ 1 - h₂((1 - Z(W)) / 2)`. -/
theorem condEntropy_ge_one_sub_h2 (W : CQChannel d) :
    1 - h2 ((1 - W.fidelityParam) / 2) ≤ W.condEntropy := by
  obtain ⟨ψ₀, ψ₁, hψ₀, hψ₁, htr₀, htr₁, hover⟩ :=
    exists_uhlmann_purification (W.out false) (W.out true)
  have hdpi := qjs_partialTrace₂_le (pureState ψ₀ hψ₀) (pureState ψ₁ hψ₁)
  have hpt₀ : partialTrace₂ (pureState ψ₀ hψ₀) = W.out false := by
    cases h : partialTrace₂ (pureState ψ₀ hψ₀); cases h' : W.out false
    rw [h, h'] at htr₀; congr
  have hpt₁ : partialTrace₂ (pureState ψ₁ hψ₁) = W.out true := by
    cases h : partialTrace₂ (pureState ψ₁ hψ₁); cases h' : W.out true
    rw [h, h'] at htr₁; congr
  rw [hpt₀, hpt₁, qjs_pureState ψ₀ ψ₁ hψ₀ hψ₁, hover] at hdpi
  unfold CQChannel.condEntropy CQChannel.fidelityParam
  linarith

/-- Scalar Pinsker-type bound: `z² / (2 ln 2) ≤ 1 - h₂((1 - z) / 2)` for `z ∈ [0, 1]`. -/
lemma sq_div_two_log_two_le_one_sub_h2 {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    z ^ 2 / (2 * Real.log 2) ≤ 1 - h2 ((1 - z) / 2) := by
  let f : ℝ → ℝ := fun x ↦ 1 - h2 ((1 - x) / 2) - x ^ 2 / (2 * Real.log 2)
  have hf0 : f 0 = 0 := by
    simp only [f, sub_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div]
    rw [h2_half]; ring
  have hmono : MonotoneOn f (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · unfold f
      exact (continuous_const.sub (continuous_h2.comp (by fun_prop))).sub
        ((continuous_pow 2).div_const _) |>.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have hc : HasDerivAt cParam ((1 / 2) * Real.logb 2 ((1 + x) / (1 - x))) x :=
        hasDerivAt_cParam hx.1 hx.2
      have hsq : HasDerivAt (fun s : ℝ ↦ s ^ 2 / (2 * Real.log 2)) (x / Real.log 2) x := by
        convert ((hasDerivAt_pow 2 x).div_const (2 * Real.log 2)) using 1; ring
      exact (hc.fun_sub hsq).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hc : HasDerivAt cParam ((1 / 2) * Real.logb 2 ((1 + x) / (1 - x))) x :=
        hasDerivAt_cParam hx.1 hx.2
      have hsq : HasDerivAt (fun s : ℝ ↦ s ^ 2 / (2 * Real.log 2)) (x / Real.log 2) x := by
        convert ((hasDerivAt_pow 2 x).div_const (2 * Real.log 2)) using 1; ring
      have hfun : f = fun s ↦ cParam s - s ^ 2 / (2 * Real.log 2) := rfl
      rw [hfun, (hc.fun_sub hsq).deriv, Real.logb]
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      rw [sub_nonneg, show (1 / 2 : ℝ) * (Real.log ((1 + x) / (1 - x)) / Real.log 2) =
        (Real.log ((1 + x) / (1 - x)) / 2) / Real.log 2 by ring,
        div_le_div_iff_of_pos_right hlog2]
      have h2x : 2 * x ≤ Real.log ((1 + x) / (1 - x)) := by
        let g : ℝ → ℝ := fun s ↦ Real.log ((1 + s) / (1 - s)) - 2 * s
        have hg0 : g 0 = 0 := by simp [g]
        have hgm : MonotoneOn g (Ico 0 1) := by
          apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
          · intro s hs
            have h1 : ContinuousAt (fun r : ℝ ↦ (1 + r) / (1 - r)) s :=
              (continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id)
                (by linarith [hs.2])
            have h2 : ContinuousAt (fun r : ℝ ↦ Real.log ((1 + r) / (1 - r))) s :=
              h1.log (ne_of_gt (div_pos (by linarith [hs.1]) (by linarith [hs.2])))
            exact (h2.sub (continuousAt_const.mul continuousAt_id)).continuousWithinAt
          · intro s hs; rw [interior_Ico] at hs
            have hq : HasDerivAt (fun r : ℝ ↦ (1 + r) / (1 - r)) (2 / (1 - s) ^ 2) s := by
              have h1 : HasDerivAt (fun r : ℝ ↦ 1 + r) 1 s := (hasDerivAt_id' s).const_add 1
              have h2 : HasDerivAt (fun r : ℝ ↦ 1 - r) (-1) s := (hasDerivAt_id' s).const_sub 1
              convert h1.fun_div h2 (by linarith [hs.2]) using 1; ring
            exact ((hq.log (ne_of_gt (div_pos (by linarith [hs.1]) (by linarith [hs.2])))).fun_sub
              (by simpa using (hasDerivAt_id' s).const_mul 2)).differentiableAt.differentiableWithinAt
          · intro s hs; rw [interior_Ico] at hs
            have hq : HasDerivAt (fun r : ℝ ↦ (1 + r) / (1 - r)) (2 / (1 - s) ^ 2) s := by
              have h1 : HasDerivAt (fun r : ℝ ↦ 1 + r) 1 s := (hasDerivAt_id' s).const_add 1
              have h2 : HasDerivAt (fun r : ℝ ↦ 1 - r) (-1) s := (hasDerivAt_id' s).const_sub 1
              convert h1.fun_div h2 (by linarith [hs.2]) using 1; ring
            have hlog : HasDerivAt (fun r : ℝ ↦ Real.log ((1 + r) / (1 - r))) (2 / (1 - s ^ 2)) s := by
              convert hq.log (ne_of_gt (div_pos (by linarith [hs.1]) (by linarith [hs.2]))) using 1
              have hne1 : 1 - s ≠ 0 := by linarith [hs.2]
              have hne2 : 1 + s ≠ 0 := by linarith [hs.1]
              have hne3 : 1 - s ^ 2 ≠ 0 := by nlinarith [hs.1, hs.2]
              field_simp [hne1, hne2, hne3]; ring
            rw [(hlog.fun_sub (by simpa using (hasDerivAt_id' s).const_mul 2)).deriv, sub_nonneg,
              le_div_iff₀ (by nlinarith [hs.1, hs.2] : 0 < 1 - s ^ 2)]
            nlinarith [sq_nonneg s]
        have := hgm ⟨le_rfl, zero_lt_one⟩ ⟨le_of_lt hx.1, hx.2⟩ (le_of_lt hx.1)
        simp only [g] at this hg0; linarith
      linarith
  have hge := hmono ⟨le_rfl, zero_le_one⟩ ⟨hz0, hz1⟩ hz0
  simp only [f] at hge hf0; linarith

/-- **Lemma 5.1(a)**: For every binary-input c-q channel `W`,
`Z(W) ≤ √((2 ln 2) H(W))`. -/
theorem fidelityParam_le_sqrt_condEntropy (W : CQChannel d) :
    W.fidelityParam ≤ Real.sqrt ((2 * Real.log 2) * W.condEntropy) := by
  have hz0 : 0 ≤ W.fidelityParam := Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _
  have hz1 : W.fidelityParam ≤ 1 := by
    obtain ⟨ψ₀, ψ₁, hψ₀, hψ₁, _, _, hover⟩ := exists_uhlmann_purification (W.out false) (W.out true)
    show rootFidelity (W.out false) (W.out true) ≤ 1
    rw [← hover]
    have h1 : ‖∑ p : d × d, star (ψ₀ p) * ψ₁ p‖ ≤ ∑ p : d × d, ‖ψ₀ p‖ * ‖ψ₁ p‖ :=
      le_trans (norm_sum_le _ _) (by simp [norm_mul])
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun p ↦ ‖ψ₀ p‖) (fun p ↦ ‖ψ₁ p‖)
    rw [hψ₀, hψ₁, Real.sqrt_one, mul_one] at h2
    exact le_trans h1 h2
  have h1 := sq_div_two_log_two_le_one_sub_h2 hz0 hz1
  have h2 := condEntropy_ge_one_sub_h2 W
  have hlog2 : 0 < 2 * Real.log 2 := mul_pos two_pos (Real.log_pos (by norm_num))
  have hsq : W.fidelityParam ^ 2 ≤ (2 * Real.log 2) * W.condEntropy := by
    have := (div_le_iff₀ hlog2).mp (le_trans h1 h2)
    linarith
  calc W.fidelityParam = Real.sqrt (W.fidelityParam ^ 2) := (Real.sqrt_sq hz0).symm
    _ ≤ Real.sqrt ((2 * Real.log 2) * W.condEntropy) := Real.sqrt_le_sqrt hsq

end PolarCodes
