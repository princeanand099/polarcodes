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

/-- **Data Processing Inequality for `relEntropy`** under `partialTrace₂` (full-rank states):
`D(Tr₂ ρ ‖ Tr₂ σ) ≤ D(ρ ‖ σ)`. -/
theorem relEntropy_partialTrace₂_le {ρ σ : DensityOp (d₁ × d₂)}
    (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    relEntropy (partialTrace₂ ρ) (partialTrace₂ σ) ≤ relEntropy ρ σ := by
  have hρ' : (partialTrace₂ ρ).mat.PosDef := by
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
      by_contra hall; push_neg at hall; exact hx (funext hall)
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
    have hpos₀ := (Matrix.posDef_iff_dotProduct_mulVec.mp hρ).2 _ hv_ne
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
  have hσ' : (partialTrace₂ σ).mat.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨(partialTrace₂ σ).isHermitian, fun x hx ↦ ?_⟩
    have hsum' : star x ⬝ᵥ (partialTrace₂ σ).mat.mulVec x =
        ∑ k : d₂, star (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) ⬝ᵥ
          σ.mat.mulVec (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) := by
      trans ∑ k : d₂, ∑ i : d₁, star (x i) * ∑ j : d₁, σ.mat (i, k) (j, k) * x j
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
      by_contra hall; push_neg at hall; exact hx (funext hall)
    have hne_d₂ : Nonempty d₂ := by
      by_contra hemp
      have h0 : σ.mat.trace = 0 := by
        simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
        apply Finset.sum_eq_zero; intro i _
        exact Finset.sum_eq_zero fun k _ ↦ absurd ⟨k⟩ hemp
      rw [σ.trace_one] at h0; exact one_ne_zero h0
    obtain ⟨k₀⟩ := hne_d₂
    have hv_ne : (fun p : d₁ × d₂ ↦ if p.2 = k₀ then x p.1 else 0) ≠ 0 := by
      intro h0; exact hi₀ (by simpa using congr_fun h0 (i₀, k₀))
    have hpos₀ := (Matrix.posDef_iff_dotProduct_mulVec.mp hσ).2 _ hv_ne
    have hnn : ∀ k : d₂, 0 ≤ star (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) ⬝ᵥ
        σ.mat.mulVec (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) :=
      fun k ↦ (Matrix.posSemidef_iff_dotProduct_mulVec.mp σ.posSemidef).2 _
    have hsplit := Finset.add_sum_erase Finset.univ (fun k : d₂ ↦
      star (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) ⬝ᵥ
        σ.mat.mulVec (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0)) (Finset.mem_univ k₀)
    have hrest : 0 ≤ ∑ k ∈ Finset.univ.erase k₀,
        star (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) ⬝ᵥ
          σ.mat.mulVec (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) :=
      Finset.sum_nonneg fun k _ ↦ hnn k
    rw [← hsplit]; exact lt_of_lt_of_le hpos₀ (le_add_of_nonneg_right hrest)
  have hlog2_pos : 0 < ENNReal.ofReal (Real.log 2) := ENNReal.ofReal_pos.mpr (Real.log_pos (by norm_num))
  have hlog2_top : ENNReal.ofReal (Real.log 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← ENNReal.mul_le_mul_right (ne_of_gt hlog2_pos) hlog2_top,
    relEntropy_frenkel_integral hρ' hσ', relEntropy_frenkel_integral hρ hσ]
  apply MeasureTheory.lintegral_mono
  intro t
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (mul_nonneg (abs_nonneg t) (sq_nonneg _))
  have hlin : ((1 - t : ℝ) : ℂ) • (partialTrace₂ ρ).mat + (t : ℂ) • (partialTrace₂ σ).mat =
      partialTrace₂Mat d₁ d₂ (((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat) := by
    rw [map_add, map_smul, map_smul]; rfl
  rw [negPartTrace_eq_of_eq _ (by rw [← hlin]; exact _) hlin]
  exact negPartTrace_map_le (partialTrace₂Mat d₁ d₂)
    (fun X hX ↦ partialTrace₂Mat_posSemidef hX)
    (fun X _ ↦ by rw [partialTrace₂Mat_trace]) _ _

/-- For full-rank states `ρ, σ ≻ 0`, `QJS(ρ, σ) = ½ (D(ρ ‖ m) + D(σ ‖ m))` where `m = (ρ + σ) / 2`. -/
lemma qjs_eq_half_relEntropy_midpoint {ρ σ : DensityOp d} (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    0 ≤ qjs ρ σ ∧ ENNReal.ofReal (qjs ρ σ) =
      (relEntropy ρ (DensityOp.midpoint ρ σ) + relEntropy σ (DensityOp.midpoint ρ σ)) / 2 := by
  set m := DensityOp.midpoint ρ σ
  have hm : m.mat.PosDef := by
    have h1 : (((1 - (1 / 2 : ℝ) : ℝ) : ℂ) • ρ.mat).PosDef := by
      simpa [Complex.real_smul] using hρ.smul (by norm_num : (0 : ℝ) < 1 - 1 / 2)
    have h2 : (((1 / 2 : ℝ) : ℂ) • σ.mat).PosSemidef := by
      simpa [Complex.real_smul] using σ.posSemidef.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exact h1.add_posSemidef h2
  have hρ_pos : ∀ i : d, 0 < ρ.eigvals i := hρ.eigenvalues_pos
  have hσ_pos : ∀ i : d, 0 < σ.eigvals i := hσ.eigenvalues_pos
  have hm_pos : ∀ j : d, 0 < m.eigvals j := hm.eigenvalues_pos
  have hsupp₁ : suppSubset ρ m := fun _ j _ hmj ↦ absurd hmj (ne_of_gt (hm_pos j))
  have hsupp₂ : suppSubset σ m := fun _ j _ hmj ↦ absurd hmj (ne_of_gt (hm_pos j))
  -- Helper: `∑ i, ∑ j, ‖(U_m† U_τ)_{ji}‖² τ_i log m_j = ∑ j, (U_m† τ U_m)_{jj}.re * log m_j`
  have hcross : ∀ (τ : DensityOp d),
      (∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (τ.eigvals i * (Real.log (τ.eigvals i) - Real.log (m.eigvals j)))) =
        -(∑ i : d, Real.negMulLog (τ.eigvals i)) -
          ∑ j : d, ((star (m.eigUnitary : Matrix d d ℂ) * τ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re *
            Real.log (m.eigvals j) := by
    intro τ
    have hrow : ∀ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 = 1 := by
      intro i
      have h1 := congr_fun (congr_fun (Unitary.coe_star_mul_self (star m.eigUnitary * τ.eigUnitary)) i) i
      have hre := congr_arg Complex.re h1
      have ht : ∀ j : d, (star ((star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i) *
          (star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i).re =
          ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 := by
        intro j; rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      simpa [Matrix.mul_apply, Matrix.star_apply, Complex.re_sum, ht] using hre
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
      rw [← Finset.sum_mul, hrow i, one_mul]; ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [hdiag j, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _; ring
  -- Nonnegativity of `relEntropy` real parts (from `relEntropy_frenkel_integral` or directly!)
  have hD_nn : ∀ (τ : DensityOp d), τ.mat.PosDef →
      0 ≤ (∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (τ.eigvals i * (Real.log (τ.eigvals i) - Real.log (m.eigvals j)))) / Real.log 2 := by
    intro τ hτ
    -- Directly: `x * (log x - log y) ≥ x - y` for `x, y > 0` (Klein's inequality)!
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
    have hrow : ∀ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 = 1 := by
      intro i
      have h1 := congr_fun (congr_fun (Unitary.coe_star_mul_self (star m.eigUnitary * τ.eigUnitary)) i) i
      have hre := congr_arg Complex.re h1
      have ht : ∀ j : d, (star ((star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i) *
          (star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i).re =
          ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 := by
        intro j; rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      simpa [Matrix.mul_apply, Matrix.star_apply, Complex.re_sum, ht] using hre
    have hcol : ∀ j : d, ∑ i : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 = 1 := by
      intro j
      have h1 := congr_fun (congr_fun (Unitary.coe_mul_star_self (star m.eigUnitary * τ.eigUnitary)) j) j
      have hre := congr_arg Complex.re h1
      have ht : ∀ i : d, ((star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i *
          star ((star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i)).re =
          ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 := by
        intro i; rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      simpa [Matrix.mul_apply, Matrix.star_apply, Complex.re_sum, ht] using hre
    have hsum_ge : (∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
        (τ.eigvals i - m.eigvals j)) ≤ _ :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (hklein i j) (sq_nonneg _)
    have hzero : (∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
        (τ.eigvals i - m.eigvals j)) = 0 := by
      have h1 : (∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (τ.eigvals i - m.eigvals j)) =
          (∑ i : d, (∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2) * τ.eigvals i) -
          (∑ j : d, (∑ i : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (τ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2) * m.eigvals j) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]; congr 1; rw [Finset.sum_comm]
      rw [h1]; simp_rw [hrow, hcol, one_mul, τ.sum_eigvals, m.sum_eigvals, sub_self]
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
    have h1 : star (m.eigUnitary : Matrix d d ℂ) * m.mat * (m.eigUnitary : Matrix d d ℂ) =
        Matrix.diagonal (Complex.ofReal ∘ m.eigvals) := by
      have hspec : m.mat = (m.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ m.eigvals) *
          star (m.eigUnitary : Matrix d d ℂ) := by
        simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using m.isHermitian.spectral_theorem
      rw [hspec]; simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star (m.eigUnitary : Matrix d d ℂ)), Unitary.coe_star_mul_self m.eigUnitary,
        Matrix.one_mul, Unitary.coe_star_mul_self m.eigUnitary, Matrix.mul_one]
    have h2 := congr_arg Complex.re (congr_fun (congr_fun h1 j) j)
    have h3 : (star (m.eigUnitary : Matrix d d ℂ) * m.mat * (m.eigUnitary : Matrix d d ℂ)) j j =
        ((1 / 2 : ℝ) : ℂ) * (star (m.eigUnitary : Matrix d d ℂ) * ρ.mat * (m.eigUnitary : Matrix d d ℂ)) j j +
        ((1 / 2 : ℝ) : ℂ) * (star (m.eigUnitary : Matrix d d ℂ) * σ.mat * (m.eigUnitary : Matrix d d ℂ)) j j := by
      have hm_eq : m.mat = ((1 / 2 : ℝ) : ℂ) • ρ.mat + ((1 / 2 : ℝ) : ℂ) • σ.mat := by
        simp only [m, DensityOp.midpoint, DensityOp.mix]; norm_num
      rw [hm_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
        smul_eq_mul, smul_eq_mul]
    rw [h3, Complex.add_re] at h2
    simp only [Matrix.diagonal_apply_eq, Function.comp_apply, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at h2
    linarith
  have hsum_m : ∑ j : d,
      (((star (m.eigUnitary : Matrix d d ℂ) * ρ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re * Real.log (m.eigvals j) +
       ((star (m.eigUnitary : Matrix d d ℂ) * σ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re * Real.log (m.eigvals j)) =
      -2 * ∑ j : d, Real.negMulLog (m.eigvals j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    unfold Real.negMulLog
    have := hmid_diag j
    linarith [show (((star (m.eigUnitary : Matrix d d ℂ) * ρ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re +
      ((star (m.eigUnitary : Matrix d d ℂ) * σ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re) *
      Real.log (m.eigvals j) = 2 * m.eigvals j * Real.log (m.eigvals j) by rw [← this]; ring]
  unfold qjs vonNeumannEntropy
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [← add_div, ← div_div, show (-∑ i, Real.negMulLog (ρ.eigvals i) -
      ∑ j, ((star (m.eigUnitary : Matrix d d ℂ) * ρ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re * Real.log (m.eigvals j)) +
      (-∑ i, Real.negMulLog (σ.eigvals i) -
      ∑ j, ((star (m.eigUnitary : Matrix d d ℂ) * σ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re * Real.log (m.eigvals j)) =
      -(∑ i, Real.negMulLog (ρ.eigvals i) + ∑ i, Real.negMulLog (σ.eigvals i)) -
      ∑ j, (((star (m.eigUnitary : Matrix d d ℂ) * ρ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re * Real.log (m.eigvals j) +
        ((star (m.eigUnitary : Matrix d d ℂ) * σ.mat * (m.eigUnitary : Matrix d d ℂ)) j j).re * Real.log (m.eigvals j)) by
        rw [Finset.sum_add_distrib]; ring, hsum_m]
  field_simp [hlog2]; ring

/-- Maximally mixed density operator `I / d` on any nonempty finite Hilbert space. -/
noncomputable def maxMixedState (d : Type*) [Fintype d] [DecidableEq d] [Nonempty d] : DensityOp d where
  mat := (((Fintype.card d : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix d d ℂ)
  posSemidef := by
    have hpos : (0 : ℝ) ≤ (Fintype.card d : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    simpa [Complex.real_smul] using (Matrix.PosSemidef.one (n := d) (R := ℂ)).smul hpos
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, ← Complex.ofReal_natCast,
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
    let lam : d → ℝ := fun i ↦ (1 - ε) * ρ.eigvals i + ε * (Fintype.card d : ℝ)⁻¹
    have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext i; simp
    have hτ_eq : τ.mat = U * Matrix.diagonal (Complex.ofReal ∘ lam) * star U := by
      have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by
        simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
      have h1 : (1 : Matrix d d ℂ) = U * 1 * star U := by
        rw [Matrix.mul_one, Unitary.coe_mul_star_self ρ.eigUnitary]
      simp only [τ, DensityOp.mix, maxMixedState]
      conv_lhs => rw [hspec, h1]
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add]
      congr 2; ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
        Function.comp_apply, lam, smul_eq_mul]
      split_ifs

      · push_cast; ring

      · simp
    have hcp : τ.mat.charpoly = (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
      rw [hτ_eq, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
        Unitary.coe_star_mul_self ρ.eigUnitary, Matrix.one_mul]
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
  simpa [vonNeumannEntropy] using hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

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
    simp only [DensityOp.midpoint, DensityOp.mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
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
    · simp only [h, ↓reduceDIte, qjs]
      rw [vonNeumannEntropy_eq_of_mat_eq (hmid_mix ε h.1 h.2)]
    · simp only [h, ↓reduceDIte, qjs]
  rw [heq]
  exact (tendsto_vonNeumannEntropy_mix_maxMixed (DensityOp.midpoint a b)).sub
    (((tendsto_vonNeumannEntropy_mix_maxMixed a).add (tendsto_vonNeumannEntropy_mix_maxMixed b)).div_const 2)

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
  -- For `ε ∈ (0, 1)`, `ρ_ε = (1-ε)ρ + ε I/(d₁ d₂)` is `PosDef` and `Tr₂(ρ_ε) = (1-ε) Tr₂ ρ + ε I/d₁`!
  have hpt_mix : ∀ (τ : DensityOp (d₁ × d₂)) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1),
      (partialTrace₂ (DensityOp.mix ε h0 h1 τ (maxMixedState (d₁ × d₂)))).mat =
        (DensityOp.mix ε h0 h1 (partialTrace₂ τ) (maxMixedState d₁)).mat := by
    intro τ ε h0 h1
    ext i j
    simp only [partialTrace₂, DensityOp.mix, maxMixedState, Matrix.of_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    simp only [Prod.mk.injEq, and_true, Finset.sum_ite_eq', Finset.mem_univ]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
        Nat.cast_mul, mul_inv]
      have hd2 : (Fintype.card d₂ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      push_cast; field_simp [hd2]
    · simp [hij]
  have hpt_mid : ∀ (a b : DensityOp (d₁ × d₂)),
      (partialTrace₂ (DensityOp.midpoint a b)).mat = (DensityOp.midpoint (partialTrace₂ a) (partialTrace₂ b)).mat := by
    intro a b; ext i j
    simp [partialTrace₂, DensityOp.midpoint, DensityOp.mix, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hmix_pd : ∀ (τ : DensityOp (d₁ × d₂)) (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1),
      (DensityOp.mix ε (le_of_lt h0) h1 τ (maxMixedState (d₁ × d₂))).mat.PosDef := by
    intro τ ε h0 h1
    have hA : (((1 - ε : ℝ) : ℂ) • τ.mat).PosSemidef := by
      simpa [Complex.real_smul] using τ.posSemidef.smul (by linarith : 0 ≤ 1 - ε)
    have hB : ((ε : ℂ) • (maxMixedState (d₁ × d₂)).mat).PosDef := by
      simp only [maxMixedState, smul_smul]
      have hpos : 0 < ε * (Fintype.card (d₁ × d₂) : ℝ)⁻¹ :=
        mul_pos h0 (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
      simpa [Complex.real_smul, ← Complex.ofReal_mul] using
        (Matrix.PosDef.one (n := d₁ × d₂) (R := ℂ)).smul hpos
    simpa [DensityOp.mix, add_comm] using hB.add_posSemidef hA
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
    have hρ_pd : ρ_ε.mat.PosDef := hmix_pd ρ ε hε.1 (le_of_lt hε.2)
    have hσ_pd : σ_ε.mat.PosDef := hmix_pd σ ε hε.1 (le_of_lt hε.2)
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
      (by simpa [Complex.real_smul] using hρ_pd.smul (by norm_num : (0 : ℝ) < 1 - 1 / 2)).add_posSemidef
        (by simpa [Complex.real_smul] using σ_ε.posSemidef.smul (by norm_num : (0 : ℝ) ≤ 1 / 2))
    have hdpi1 := relEntropy_partialTrace₂_le hρ_pd hm_pd
    have hdpi2 := relEntropy_partialTrace₂_le hσ_pd hm_pd
    have hmid_eq : partialTrace₂ (DensityOp.midpoint ρ_ε σ_ε) =
        DensityOp.midpoint (partialTrace₂ ρ_ε) (partialTrace₂ σ_ε) := by
      cases h : partialTrace₂ (DensityOp.midpoint ρ_ε σ_ε)
      cases h' : DensityOp.midpoint (partialTrace₂ ρ_ε) (partialTrace₂ σ_ε)
      have hm := hpt_mid ρ_ε σ_ε; rw [h, h'] at hm; congr
    rw [hmid_eq] at hdpi1 hdpi2
    have hptρ_pd : (partialTrace₂ ρ_ε).mat.PosDef := by
      rw [hptρ]
      have hA : (((1 - ε : ℝ) : ℂ) • (partialTrace₂ ρ).mat).PosSemidef := by
        simpa [Complex.real_smul] using (partialTrace₂ ρ).posSemidef.smul (by linarith [hε.2] : 0 ≤ 1 - ε)
      have hB : ((ε : ℂ) • (maxMixedState d₁).mat).PosDef := by
        simp only [maxMixedState, smul_smul]
        simpa [Complex.real_smul, ← Complex.ofReal_mul] using
          (Matrix.PosDef.one (n := d₁) (R := ℂ)).smul (mul_pos hε.1 (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)))
      simpa [DensityOp.mix, add_comm] using hB.add_posSemidef hA
    have hptσ_pd : (partialTrace₂ σ_ε).mat.PosDef := by
      rw [hptσ]
      have hA : (((1 - ε : ℝ) : ℂ) • (partialTrace₂ σ).mat).PosSemidef := by
        simpa [Complex.real_smul] using (partialTrace₂ σ).posSemidef.smul (by linarith [hε.2] : 0 ≤ 1 - ε)
      have hB : ((ε : ℂ) • (maxMixedState d₁).mat).PosDef := by
        simp only [maxMixedState, smul_smul]
        simpa [Complex.real_smul, ← Complex.ofReal_mul] using
          (Matrix.PosDef.one (n := d₁) (R := ℂ)).smul (mul_pos hε.1 (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)))
      simpa [DensityOp.mix, add_comm] using hB.add_posSemidef hA
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
  -- Use `lemma_4_1_gram_dephasing` with trivial 1-dimensional `d₁ = Unit`!
  let oneOp : DensityOp Unit :=
    ⟨1, Matrix.PosSemidef.one, by simp [Matrix.trace]⟩
  have h41 := lemma_4_1_gram_dephasing oneOp oneOp ψ₀ ψ₁ hψ₀ hψ₁
  -- Actually simpler: direct 2×2 Gram matrix `M = [[1/2, z/2], [z̄/2, 1/2]]` has eigenvalues `(1±f)/2`!
  set f : ℝ := ‖∑ k : d, star (ψ₀ k) * ψ₁ k‖
  have hf_le : f ≤ 1 := by
    have h1 : ‖∑ k : d, star (ψ₀ k) * ψ₁ k‖ ≤ ∑ k : d, ‖ψ₀ k‖ * ‖ψ₁ k‖ :=
      le_trans (norm_sum_le _ _) (by simp [norm_mul])
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k ↦ ‖ψ₀ k‖) (fun k ↦ ‖ψ₁ k‖)
    rw [hψ₀, hψ₁, Real.sqrt_one, mul_one] at h2
    exact le_trans h1 h2
  -- First show `S(pureState ψ) = 0` via `M : Matrix d Unit ℂ`
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
      (Matrix.isHermitian_one (n := Unit) (R := ℂ)) hcp (by simp [Real.negMulLog])
    have h1 : ∑ i : Unit, Real.negMulLog ((Matrix.isHermitian_one (n := Unit) (R := ℂ)).eigenvalues i) = 0 := by
      have hdiag : (1 : Matrix Unit Unit ℂ) = Matrix.diagonal (Complex.ofReal ∘ fun _ : Unit ↦ (1 : ℝ)) := by
        ext _ _; simp
      have hsum2 := spectral_sum_diagonal (fun _ : Unit ↦ (1 : ℝ))
        (by rw [← hdiag]; exact Matrix.isHermitian_one) (by simp [Real.negMulLog])
      simpa [Real.negMulLog] using hsum2
    rw [hsum, h1, zero_div]
  unfold qjs
  rw [hS_pure ψ₀ hψ₀, hS_pure ψ₁ hψ₁, add_zero, zero_div, sub_zero]
  -- Now `S(midpoint |ψ₀⟩⟨ψ₀| |ψ₁⟩⟨ψ₁|) = S(dephaseState ((1-f)/2) (gramState oneOp oneOp))`
  -- Compute directly via `A : Matrix d Bool ℂ` with columns `ψ₀ / √2` and `ψ₁ / √2`!
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
        (Real.sqrt 2 : ℂ)⁻¹ * a * (star b * star ((Real.sqrt 2 : ℂ)⁻¹)) = (1 / 2 : ℂ) * (a * star b) := by
      intro a b
      calc _
          = ((Real.sqrt 2 : ℂ)⁻¹ * star ((Real.sqrt 2 : ℂ)⁻¹)) * (a * star b) := by ring
        _ = (1 / 2 : ℂ) * (a * star b) := by rw [hsq2']
    rw [hrew, hrew]; push_cast; ring
  -- `Aᴴ * A` is the 2×2 matrix `[[1/2, z/2], [z̄/2, 1/2]]`, whose charpoly is `(X - (1+f)/2)(X - (1-f)/2)`!
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
    · simp only [Bool.false_eq_true, ↓reduceIte, z]
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
      calc _
          = (star ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹) * (star (ψ₀ k) * ψ₁ k) := by ring
        _ = (1 / 2 : ℂ) * (star (ψ₀ k) * ψ₁ k) := by rw [hsq2]
    · simp only [Bool.true_eq_false, ↓reduceIte, z, star_sum, star_mul', star_star]
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
      calc _
          = (star ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹) * (star (ψ₁ k) * ψ₀ k) := by ring
        _ = (1 / 2 : ℂ) * (ψ₀ k * star (ψ₁ k)) := by rw [hsq2]; ring
    · simp only [↓reduceIte]
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
    rw [hAHA, Matrix.charpoly, Matrix.charmatrix]
    -- 2×2 determinant over `Bool`
    rw [Matrix.det_apply]
    -- Simpler: compute directly on `Equiv.Perm Bool` (only 2 elements: `1` and `Equiv.swap false true`)
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
    have hzz : Polynomial.C ((1 / 2 : ℂ) * z) * Polynomial.C ((1 / 2 : ℂ) * star z) =
        Polynomial.C (((1 / 4 : ℝ) * f ^ 2 : ℝ) : ℂ) := by
      rw [← map_mul]; congr 1
      have h1 : z * star z = ((f ^ 2 : ℝ) : ℂ) := by
        simp only [f, z]; rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc (1 / 2 : ℂ) * z * ((1 / 2 : ℂ) * star z) = (1 / 4 : ℂ) * (z * star z) := by ring
        _ = (1 / 4 : ℂ) * ((f ^ 2 : ℝ) : ℂ) := by rw [h1]
        _ = _ := by push_cast; ring
    have h1 : Polynomial.C (((1 + f) / 2 : ℝ) : ℂ) = Polynomial.C (1 / 2 : ℂ) + Polynomial.C ((f / 2 : ℝ) : ℂ) := by
      rw [← map_add]; congr 1; push_cast; ring
    have h2 : Polynomial.C (((1 - f) / 2 : ℝ) : ℂ) = Polynomial.C (1 / 2 : ℂ) - Polynomial.C ((f / 2 : ℝ) : ℂ) := by
      rw [← map_sub]; congr 1; push_cast; ring
    have hsq : Polynomial.C ((f / 2 : ℝ) : ℂ) * Polynomial.C ((f / 2 : ℝ) : ℂ) =
        Polynomial.C (((1 / 4 : ℝ) * f ^ 2 : ℝ) : ℂ) := by
      rw [← map_mul]; congr 1; push_cast; ring
    rw [h1, h2, ← hsq] at *
    have hswap : Polynomial.C ((1 / 2 : ℂ) * star z) * Polynomial.C ((1 / 2 : ℂ) * z) =
        Polynomial.C ((f / 2 : ℝ) : ℂ) * Polynomial.C ((f / 2 : ℝ) : ℂ) := by
      rw [mul_comm, hzz, hsq]
    rw [hswap]; ring
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
        hD_herm hcp_all (by simp [Real.negMulLog])
    · exact spectral_sum_diagonal lam hD_herm (by simp [Real.negMulLog])
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
  have hf0 : f 0 = 0 := by simp [f, h2_half]
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
      -- `2 x ≤ log ((1 + x) / (1 - x))`
      have h2x : 2 * x ≤ Real.log ((1 + x) / (1 - x)) := by
        let g : ℝ → ℝ := fun s ↦ Real.log ((1 + s) / (1 - s)) - 2 * s
        have hg0 : g 0 = 0 := by simp [g]
        have hgm : MonotoneOn g (Ico 0 1) := by
          apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
          · exact ((continuousOn_const.add continuousOn_id).div (continuousOn_const.sub continuousOn_id)
              (fun s hs ↦ by linarith [hs.2])).log
              (fun s hs ↦ ne_of_gt (div_pos (by linarith [hs.1]) (by linarith [hs.2]))) |>.sub
              (continuousOn_const.mul continuousOn_id)
          · intro s hs; rw [interior_Ico] at hs
            have hq : HasDerivAt (fun r : ℝ ↦ (1 + r) / (1 - r)) (2 / (1 - s) ^ 2) s := by
              convert ((hasDerivAt_id s).const_add 1).fun_div ((hasDerivAt_id s).const_sub 1) (by linarith [hs.2]) using 1; ring
            exact ((hq.log (ne_of_gt (div_pos (by linarith [hs.1]) (by linarith [hs.2])))).fun_sub
              (by simpa using (hasDerivAt_id s).const_mul 2)).differentiableAt.differentiableWithinAt
          · intro s hs; rw [interior_Ico] at hs
            have hq : HasDerivAt (fun r : ℝ ↦ (1 + r) / (1 - r)) (2 / (1 - s) ^ 2) s := by
              convert ((hasDerivAt_id s).const_add 1).fun_div ((hasDerivAt_id s).const_sub 1) (by linarith [hs.2]) using 1; ring
            have hlog : HasDerivAt (fun r : ℝ ↦ Real.log ((1 + r) / (1 - r))) (2 / (1 - s ^ 2)) s := by
              convert hq.log (ne_of_gt (div_pos (by linarith [hs.1]) (by linarith [hs.2]))) using 1
              have hne1 : 1 - s ≠ 0 := by linarith [hs.2]
              have hne2 : 1 + s ≠ 0 := by linarith [hs.1]
              have hne3 : 1 - s ^ 2 ≠ 0 := by nlinarith [hs.1, hs.2]
              field_simp [hne1, hne2, hne3]; ring
            rw [(hlog.fun_sub (by simpa using (hasDerivAt_id s).const_mul 2)).deriv, sub_nonneg,
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
    have := le_trans h1 h2
    rwa [div_le_iff₀ hlog2, mul_comm] at this
  calc W.fidelityParam = Real.sqrt (W.fidelityParam ^ 2) := (Real.sqrt_sq hz0).symm
    _ ≤ Real.sqrt ((2 * Real.log 2) * W.condEntropy) := Real.sqrt_le_sqrt hsq

end PolarCodes
