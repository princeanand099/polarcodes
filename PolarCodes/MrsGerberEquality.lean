/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.ChannelDuality
import PolarCodes.DataProcessing

/-!
# Equality Cases for Theorem 1.2(a)

This module formalizes the remark following Theorem 1.2(a) of the manuscript:
1. `theorem_1_2a_bsc_equality`: equality in Eq. (1.5) for pairs of binary symmetric channels
   (`bscChannel`).
2. `theorem_1_2a_pure_equality`: equality in Eq. (1.4) for pairs of pure-state channels
   (`pureChannel`).
-/

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodes

/-- Equality in Eq. (1.5) (Remark after Theorem 1.2(a)) for pairs of binary symmetric channels. -/
theorem theorem_1_2a_bsc_equality {p₁ p₂ : ℝ}
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ ≤ 1 / 2) (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ ≤ 1 / 2) :
    let W₁ := bscChannel p₁ hp₁0 (by linarith)
    let W₂ := bscChannel p₂ hp₂0 (by linarith)
    (CQChannel.checkCombine W₁ W₂).condEntropy = gc W₁.condEntropy W₂.condEntropy := by
  intro W₁ W₂
  set q : ℝ := binConv p₁ p₂
  have hq0 : 0 ≤ q := by dsimp only [q, binConv]; nlinarith
  have hq1 : q ≤ 1 := by dsimp only [q, binConv]; nlinarith
  have hdiag4 : ∀ (v : Bool × Bool → ℝ) (ρ : DensityOp (Bool × Bool)),
      ρ.mat = Matrix.diagonal (Complex.ofReal ∘ v) →
      vonNeumannEntropy ρ = (∑ p : Bool × Bool, Real.negMulLog (v p)) / Real.log 2 := by
    intro v ρ hmat
    have hD : (Matrix.diagonal (Complex.ofReal ∘ v)).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext b; simp
    unfold vonNeumannEntropy DensityOp.eigvals
    congr 1
    trans ∑ b : Bool × Bool, Real.negMulLog (hD.eigenvalues b)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow ρ.isHermitian hD (k := 0) (l := 0)
        (by rw [pow_zero, mul_one, mul_one, hmat]) (by simp [Real.negMulLog])
    · exact spectral_sum_diagonal v hD (by simp [Real.negMulLog])
  have hnegMulLog_half : ∀ x : ℝ, 0 ≤ x →
      Real.negMulLog (x / 2) = (Real.negMulLog x + x * Real.log 2) / 2 := by
    intro x hx
    rcases eq_or_lt_of_le hx with rfl | hxpos
    · simp [Real.negMulLog]
    · unfold Real.negMulLog
      rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)]
      ring
  have hS_pair : (2 * Real.negMulLog ((1 - q) / 2) + 2 * Real.negMulLog (q / 2)) / Real.log 2 =
      1 + h2 q := by
    rw [hnegMulLog_half (1 - q) (by linarith), hnegMulLog_half q hq0, h2_eq_negMulLog]
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp [hlog2]; ring
  have hS0 : vonNeumannEntropy ((CQChannel.checkCombine W₁ W₂).out false) = 1 + h2 q := by
    rw [hdiag4 (fun p ↦ if p.1 = p.2 then (1 - q) / 2 else q / 2) _ (by
      ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
      simp only [CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
        W₁, W₂, bscChannel, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
        Matrix.diagonal_apply, Function.comp_apply, Complex.real_smul, q, binConv]
      cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring)]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true]
    have hadd : (Real.negMulLog ((1 - q) / 2) + Real.negMulLog (q / 2) +
        (Real.negMulLog (q / 2) + Real.negMulLog ((1 - q) / 2))) / Real.log 2 =
        (2 * Real.negMulLog ((1 - q) / 2) + 2 * Real.negMulLog (q / 2)) / Real.log 2 := by ring
    rw [hadd, hS_pair]
  have hS1 : vonNeumannEntropy ((CQChannel.checkCombine W₁ W₂).out true) = 1 + h2 q := by
    rw [hdiag4 (fun p ↦ if p.1 = p.2 then q / 2 else (1 - q) / 2) _ (by
      ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
      simp only [CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
        W₁, W₂, bscChannel, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
        Matrix.diagonal_apply, Function.comp_apply, Complex.real_smul, q, binConv]
      cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring)]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true]
    have hadd : (Real.negMulLog (q / 2) + Real.negMulLog ((1 - q) / 2) +
        (Real.negMulLog ((1 - q) / 2) + Real.negMulLog (q / 2))) / Real.log 2 =
        (2 * Real.negMulLog ((1 - q) / 2) + 2 * Real.negMulLog (q / 2)) / Real.log 2 := by ring
    rw [hadd, hS_pair]
  have hSmid : vonNeumannEntropy (DensityOp.midpoint ((CQChannel.checkCombine W₁ W₂).out false)
      ((CQChannel.checkCombine W₁ W₂).out true)) = 2 := by
    rw [hdiag4 (fun _ ↦ 1 / 4) _ (by
      ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
      simp only [CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
        W₁, W₂, bscChannel, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
        Matrix.diagonal_apply, Function.comp_apply, Complex.real_smul]
      cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring)]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    unfold Real.negMulLog
    have hlog4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
      rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    rw [hlog4]
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp [hlog2]; ring
  have hLHS : (CQChannel.checkCombine W₁ W₂).condEntropy = h2 q := by
    unfold CQChannel.condEntropy qjs
    rw [hS0, hS1, hSmid]; ring
  have hRHS : gc W₁.condEntropy W₂.condEntropy = h2 q := by
    unfold gc
    rw [condEntropy_bscChannel, condEntropy_bscChannel,
      h2Inv_h2 ⟨hp₁0, hp₁1⟩, h2Inv_h2 ⟨hp₂0, hp₂1⟩]
  rw [hLHS, hRHS]

/-- Equality in Eq. (1.4) (Remark after Theorem 1.2(a)) for pairs of pure-state channels. -/
theorem theorem_1_2a_pure_equality {f₁ f₂ : ℝ}
    (hf₁0 : 0 ≤ f₁) (hf₁1 : f₁ ≤ 1) (hf₂0 : 0 ≤ f₂) (hf₂1 : f₂ ≤ 1) :
    let W₁ := pureChannel f₁ hf₁0 hf₁1
    let W₂ := pureChannel f₂ hf₂0 hf₂1
    (CQChannel.varCombine W₁ W₂).condEntropy =
      1 - gc (1 - W₁.condEntropy) (1 - W₂.condEntropy) ∧
    (CQChannel.checkCombine W₁ W₂).condEntropy =
      W₁.condEntropy + W₂.condEntropy - 1 + gc (1 - W₁.condEntropy) (1 - W₂.condEntropy) := by
  intro W₁ W₂
  let φ₀ : Bool → ℂ := fun b ↦ if b = false then (Real.sqrt ((1 + f₁) / 2) : ℂ) else (Real.sqrt ((1 - f₁) / 2) : ℂ)
  let φ₁ : Bool → ℂ := fun b ↦ if b = false then (Real.sqrt ((1 + f₁) / 2) : ℂ) else -(Real.sqrt ((1 - f₁) / 2) : ℂ)
  let ψ₀ : Bool → ℂ := fun b ↦ if b = false then (Real.sqrt ((1 + f₂) / 2) : ℂ) else (Real.sqrt ((1 - f₂) / 2) : ℂ)
  let ψ₁ : Bool → ℂ := fun b ↦ if b = false then (Real.sqrt ((1 + f₂) / 2) : ℂ) else -(Real.sqrt ((1 - f₂) / 2) : ℂ)
  have hnorm : ∀ (a b : Bool → ℂ), (∑ i : Bool, ‖a i‖ ^ 2 = 1) → (∑ j : Bool, ‖b j‖ ^ 2 = 1) →
      ∑ p : Bool × Bool, ‖a p.1 * b p.2‖ ^ 2 = 1 := by
    intro a b ha hb
    rw [Fintype.sum_prod_type]
    simp_rw [norm_mul, mul_pow, ← Finset.mul_sum, hb, mul_one, ha]
  have hφ₀ : ∑ b : Bool, ‖φ₀ b‖ ^ 2 = 1 := by
    rw [Fintype.sum_bool]; simp only [φ₀, ↓reduceIte, Bool.true_eq_false, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by linarith : 0 ≤ (1 + f₁) / 2),
      Real.sq_sqrt (by linarith : 0 ≤ (1 - f₁) / 2)]; ring
  have hφ₁ : ∑ b : Bool, ‖φ₁ b‖ ^ 2 = 1 := by
    rw [Fintype.sum_bool]; simp only [φ₁, ↓reduceIte, Bool.true_eq_false, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by linarith : 0 ≤ (1 + f₁) / 2),
      Real.sq_sqrt (by linarith : 0 ≤ (1 - f₁) / 2)]; ring
  have hψ₀ : ∑ b : Bool, ‖ψ₀ b‖ ^ 2 = 1 := by
    rw [Fintype.sum_bool]; simp only [ψ₀, ↓reduceIte, Bool.true_eq_false, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by linarith : 0 ≤ (1 + f₂) / 2),
      Real.sq_sqrt (by linarith : 0 ≤ (1 - f₂) / 2)]; ring
  have hψ₁ : ∑ b : Bool, ‖ψ₁ b‖ ^ 2 = 1 := by
    rw [Fintype.sum_bool]; simp only [ψ₁, ↓reduceIte, Bool.true_eq_false, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by linarith : 0 ≤ (1 + f₂) / 2),
      Real.sq_sqrt (by linarith : 0 ≤ (1 - f₂) / 2)]; ring
  have htensor_pure : ∀ (a b : Bool → ℂ) (ha : ∑ i, ‖a i‖ ^ 2 = 1) (hb : ∑ j, ‖b j‖ ^ 2 = 1),
      (DensityOp.tensor (pureState a ha) (pureState b hb)).mat =
        (pureState (fun p : Bool × Bool ↦ a p.1 * b p.2) (hnorm a b ha hb)).mat := by
    intro a b ha hb; ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [DensityOp.tensor, pureState, Matrix.kroneckerMap_apply, Matrix.of_apply, star_mul']
    ring
  have hqjs_tensor : ∀ (a₀ a₁ b₀ b₁ : Bool → ℂ) (ha₀ : ∑ i, ‖a₀ i‖ ^ 2 = 1)
      (ha₁ : ∑ i, ‖a₁ i‖ ^ 2 = 1) (hb₀ : ∑ j, ‖b₀ j‖ ^ 2 = 1) (hb₁ : ∑ j, ‖b₁ j‖ ^ 2 = 1),
      qjs (DensityOp.tensor (pureState a₀ ha₀) (pureState b₀ hb₀))
          (DensityOp.tensor (pureState a₁ ha₁) (pureState b₁ hb₁)) =
        h2 ((1 - ‖(∑ i : Bool, star (a₀ i) * a₁ i) * (∑ j : Bool, star (b₀ j) * b₁ j)‖) / 2) := by
    intro a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
    have h0 := htensor_pure a₀ b₀ ha₀ hb₀
    have h1 := htensor_pure a₁ b₁ ha₁ hb₁
    have hm : (DensityOp.midpoint (DensityOp.tensor (pureState a₀ ha₀) (pureState b₀ hb₀))
        (DensityOp.tensor (pureState a₁ ha₁) (pureState b₁ hb₁))).mat =
        (DensityOp.midpoint (pureState (fun p : Bool × Bool ↦ a₀ p.1 * b₀ p.2) (hnorm a₀ b₀ ha₀ hb₀))
          (pureState (fun p : Bool × Bool ↦ a₁ p.1 * b₁ p.2) (hnorm a₁ b₁ ha₁ hb₁))).mat := by
      simp only [DensityOp.midpoint, DensityOp.mix, h0, h1]
    have hq : qjs (DensityOp.tensor (pureState a₀ ha₀) (pureState b₀ hb₀))
        (DensityOp.tensor (pureState a₁ ha₁) (pureState b₁ hb₁)) =
        qjs (pureState (fun p : Bool × Bool ↦ a₀ p.1 * b₀ p.2) (hnorm a₀ b₀ ha₀ hb₀))
            (pureState (fun p : Bool × Bool ↦ a₁ p.1 * b₁ p.2) (hnorm a₁ b₁ ha₁ hb₁)) := by
      unfold qjs
      rw [vonNeumannEntropy_eq_of_mat_eq hm, vonNeumannEntropy_eq_of_mat_eq h0,
        vonNeumannEntropy_eq_of_mat_eq h1]
    rw [hq, qjs_pureState]
    congr 3
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [star_mul']; ring
  have hφ_in : ∑ i : Bool, star (φ₀ i) * φ₁ i = (f₁ : ℂ) := by
    rw [Fintype.sum_bool]
    simp only [φ₀, φ₁, ↓reduceIte, Bool.true_eq_false, Complex.star_def, Complex.conj_ofReal,
      mul_neg, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith : 0 ≤ (1 + f₁) / 2),
      Real.mul_self_sqrt (by linarith : 0 ≤ (1 - f₁) / 2)]
    push_cast; ring
  have hφ_in' : ∑ i : Bool, star (φ₁ i) * φ₀ i = (f₁ : ℂ) := by
    rw [Fintype.sum_bool]
    simp only [φ₀, φ₁, ↓reduceIte, Bool.true_eq_false, star_neg, Complex.star_def, Complex.conj_ofReal,
      neg_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith : 0 ≤ (1 + f₁) / 2),
      Real.mul_self_sqrt (by linarith : 0 ≤ (1 - f₁) / 2)]
    push_cast; ring
  have hψ_in : ∑ j : Bool, star (ψ₀ j) * ψ₁ j = (f₂ : ℂ) := by
    rw [Fintype.sum_bool]
    simp only [ψ₀, ψ₁, ↓reduceIte, Bool.true_eq_false, Complex.star_def, Complex.conj_ofReal,
      mul_neg, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith : 0 ≤ (1 + f₂) / 2),
      Real.mul_self_sqrt (by linarith : 0 ≤ (1 - f₂) / 2)]
    push_cast; ring
  have hnorm_prod : ‖(f₁ : ℂ) * (f₂ : ℂ)‖ = f₁ * f₂ := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hf₁0 hf₂0)]
  have hvar : (CQChannel.varCombine W₁ W₂).condEntropy = 1 - h2 ((1 - f₁ * f₂) / 2) := by
    rw [condEntropy_varCombine_eq]
    change (1 - qjs (DensityOp.tensor (pureState φ₀ hφ₀) (pureState ψ₀ hψ₀))
          (DensityOp.tensor (pureState φ₁ hφ₁) (pureState ψ₁ hψ₁))) / 2 +
        (1 - qjs (DensityOp.tensor (pureState φ₁ hφ₁) (pureState ψ₀ hψ₀))
          (DensityOp.tensor (pureState φ₀ hφ₀) (pureState ψ₁ hψ₁))) / 2 = _
    rw [hqjs_tensor, hqjs_tensor, hφ_in, hφ_in', hψ_in, hnorm_prod]
    ring
  have hgc : gc (1 - W₁.condEntropy) (1 - W₂.condEntropy) = h2 ((1 - f₁ * f₂) / 2) := by
    unfold gc
    rw [condEntropy_pureChannel, condEntropy_pureChannel, sub_sub_cancel, sub_sub_cancel,
      h2Inv_h2 ⟨by linarith, by linarith⟩, h2Inv_h2 ⟨by linarith, by linarith⟩]
    congr 1; unfold binConv; ring
  have h1 : (CQChannel.varCombine W₁ W₂).condEntropy =
      1 - gc (1 - W₁.condEntropy) (1 - W₂.condEntropy) := by
    rw [hvar, hgc]
  refine ⟨h1, ?_⟩
  have hcons := entropy_conservation W₁ W₂
  linarith

end PolarCodes
