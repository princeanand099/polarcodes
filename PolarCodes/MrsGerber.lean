/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.MrsGerberClassical

/-!
# General Quantum Mrs. Gerber Bounds (Proposition 4.2 & Theorem 1.2(b))

This module completes Section 4 of the manuscript (building on `MrsGerberHybrid` and
`MrsGerberClassical`):
1. **Fidelity–Entropy Upper Bound** (`condEntropy_le_logb_one_add_fidelityParam`):
   `H(W) ≤ log₂(1 + F(W))` for every binary-input c-q channel `W`.
2. **Proposition 4.2 — Four-Branch Purification Bound** (`prop_4_2_four_branch`):
   for all independent binary-input c-q channels `W₁, W₂`,
   `H(W₁ ⊠ W₂) ≥ max { H₁ + Δ(1 - H₁, 1 - 2^{H₂ - 1}), H₂ + Δ(1 - H₂, 1 - 2^{H₁ - 1}),
                        H₂ + Δ(H₁, 1 - 2^{-H₂}), H₁ + Δ(H₂, 1 - 2^{-H₁}) }`.
3. **Theorem 1.2(b) — Linear-Scaling Splitting & Uniform Potential Contraction**
   (`theorem_1_2b_linear_splitting`, `theorem_1_2b_potential_contraction`):
   for every binary-input c-q channel `W`,
   `H(W⁻) - H(W) = H(W) - H(W⁺) ≥ θ₀ H(W)(1 - H(W))` and
   `½ (T(W⁻) + T(W⁺)) ≤ Λ₀ T(W)` with `Λ₀ = √(1 - θ₀²/4) < 1`.
-/

open Matrix BigOperators Real Filter Topology Set
open scoped ComplexOrder

namespace PolarCodes

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-! ### Part 3: Proposition 4.2 — Four-Branch Purification Bound -/

/-- **Fidelity–Entropy Upper Bound** (Hirche–Reeb Theorem V.3 / Renes–Wilde):
For every binary-input c-q channel `W`, `H(W) ≤ log₂(1 + F(W))`. -/
lemma condEntropy_le_logb_one_add_fidelityParam (W : CQChannel d) :
    W.condEntropy ≤ Real.logb 2 (1 + W.fidelityParam) := by
  set ρ₀ := W.out false
  set ρ₁ := W.out true
  set σ := DensityOp.midpoint ρ₀ ρ₁
  let V₀ : Matrix d d ℂ := star (σ.eigUnitary : Matrix d d ℂ) * (ρ₀.eigUnitary : Matrix d d ℂ)
  let V₁ : Matrix d d ℂ := star (σ.eigUnitary : Matrix d d ℂ) * (ρ₁.eigUnitary : Matrix d d ℂ)
  let T₀ : d → d → ℝ := fun i j ↦ ‖V₀ j i‖ ^ 2
  let T₁ : d → d → ℝ := fun i j ↦ ‖V₁ j i‖ ^ 2
  have hT_unit : ∀ (ρ : DensityOp d) (V : Matrix d d ℂ),
      V = star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ) →
      (∀ i, ∑ j : d, ‖V j i‖ ^ 2 = 1) ∧
      (∀ j, ∑ i : d, ‖V j i‖ ^ 2 = 1) ∧
      (∀ j, ∑ i : d, ρ.eigvals i * ‖V j i‖ ^ 2 =
        ((star (σ.eigUnitary : Matrix d d ℂ) * ρ.mat * (σ.eigUnitary : Matrix d d ℂ)) j j).re) ∧
      (∑ i : d, ∑ j : d, Real.sqrt (ρ.eigvals i) * Real.sqrt (σ.eigvals j) * ‖V j i‖ ^ 2 =
        (ρ.sqrtMat * σ.sqrtMat).trace.re) := by
    intro ρ V hV
    have hUs_mul : (σ.eigUnitary : Matrix d d ℂ) * star (σ.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_mul_star_self σ.eigUnitary
    have hUs_star : star (σ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_star_mul_self σ.eigUnitary
    have hUr_mul : (ρ.eigUnitary : Matrix d d ℂ) * star (ρ.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_mul_star_self ρ.eigUnitary
    have hUr_star : star (ρ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_star_mul_self ρ.eigUnitary
    have hV_star : star V * V = 1 := by
      rw [hV, star_mul, star_star]
      calc star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ) *
            (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ))
          = star (ρ.eigUnitary : Matrix d d ℂ) *
            (((σ.eigUnitary : Matrix d d ℂ) * star (σ.eigUnitary : Matrix d d ℂ)) *
              (ρ.eigUnitary : Matrix d d ℂ)) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hUs_mul, Matrix.one_mul, hUr_star]
    have hV_mul : V * star V = 1 := by
      rw [hV, star_mul, star_star]
      calc star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ) *
            (star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ))
          = star (σ.eigUnitary : Matrix d d ℂ) *
            (((ρ.eigUnitary : Matrix d d ℂ) * star (ρ.eigUnitary : Matrix d d ℂ)) *
              (σ.eigUnitary : Matrix d d ℂ)) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hUr_mul, Matrix.one_mul, hUs_star]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      have h1 := congr_arg Complex.re (congr_fun (congr_fun hV_star i) i)
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, ↓reduceIte,
        Complex.one_re, Complex.re_sum] at h1
      rw [← h1]; apply Finset.sum_congr rfl; intro j _
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    · intro j
      have h1 := congr_arg Complex.re (congr_fun (congr_fun hV_mul j) j)
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, ↓reduceIte,
        Complex.one_re, Complex.re_sum] at h1
      rw [← h1]; apply Finset.sum_congr rfl; intro i _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    · intro j
      have hspec : ρ.mat = (ρ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *
          star (ρ.eigUnitary : Matrix d d ℂ) := by
        simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
      have heq : star (σ.eigUnitary : Matrix d d ℂ) * ρ.mat * (σ.eigUnitary : Matrix d d ℂ) =
          V * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star V := by
        rw [hspec, hV, star_mul, star_star]; simp only [Matrix.mul_assoc]
      rw [heq]
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, Function.comp_apply,
        mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _
      have hmul : V j i * (ρ.eigvals i : ℂ) * star (V j i) = ((ρ.eigvals i * ‖V j i‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm (V j i), mul_assoc, Complex.star_def, Complex.mul_conj,
          Complex.normSq_eq_norm_sq, Complex.ofReal_mul]
      rw [hmul, Complex.ofReal_re]
    · have htr : (ρ.sqrtMat * σ.sqrtMat).trace =
          (Matrix.diagonal (fun i ↦ (Real.sqrt (ρ.eigvals i) : ℂ)) * star V *
            Matrix.diagonal (fun j ↦ (Real.sqrt (σ.eigvals j) : ℂ)) * V).trace := by
        unfold DensityOp.sqrtMat
        calc ((ρ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun i ↦ (Real.sqrt (ρ.eigvals i) : ℂ)) *
                star (ρ.eigUnitary : Matrix d d ℂ) *
                ((σ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun j ↦ (Real.sqrt (σ.eigvals j) : ℂ)) *
                  star (σ.eigUnitary : Matrix d d ℂ))).trace
            = (Matrix.diagonal (fun i ↦ (Real.sqrt (ρ.eigvals i) : ℂ)) *
                (star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ)) *
                Matrix.diagonal (fun j ↦ (Real.sqrt (σ.eigvals j) : ℂ)) *
                (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ))).trace := by
                simp only [Matrix.mul_assoc]
                rw [Matrix.trace_mul_comm (ρ.eigUnitary : Matrix d d ℂ)]
                simp only [Matrix.mul_assoc]
          _ = (Matrix.diagonal (fun i ↦ (Real.sqrt (ρ.eigvals i) : ℂ)) * star V *
                Matrix.diagonal (fun j ↦ (Real.sqrt (σ.eigvals j) : ℂ)) * V).trace := by
                rw [hV, star_mul, star_star]
      rw [htr]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
        Matrix.star_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      have hmul : (Real.sqrt (ρ.eigvals i) : ℂ) * star (V j i) * (Real.sqrt (σ.eigvals j) : ℂ) * V j i =
          ((Real.sqrt (ρ.eigvals i) * Real.sqrt (σ.eigvals j) * ‖V j i‖ ^ 2 : ℝ) : ℂ) := by
        have hsq : star (V j i) * V j i = ((‖V j i‖ ^ 2 : ℝ) : ℂ) := by
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        calc (Real.sqrt (ρ.eigvals i) : ℂ) * star (V j i) * (Real.sqrt (σ.eigvals j) : ℂ) * V j i
            = (Real.sqrt (ρ.eigvals i) : ℂ) * (Real.sqrt (σ.eigvals j) : ℂ) * (star (V j i) * V j i) := by ring
          _ = ((Real.sqrt (ρ.eigvals i) * Real.sqrt (σ.eigvals j) * ‖V j i‖ ^ 2 : ℝ) : ℂ) := by
              rw [hsq]; push_cast; ring
      rw [hmul, Complex.ofReal_re]
  obtain ⟨hT0_j, hT0_i, hT0_diag, hT0_tr⟩ := hT_unit ρ₀ V₀ rfl
  obtain ⟨hT1_j, hT1_i, hT1_diag, hT1_tr⟩ := hT_unit ρ₁ V₁ rfl
  have hmid_diag : ∀ j : d, (∑ i : d, ρ₀.eigvals i * T₀ i j) / 2 + (∑ i : d, ρ₁.eigvals i * T₁ i j) / 2 =
      σ.eigvals j := by
    intro j
    rw [hT0_diag j, hT1_diag j]
    have hUs_star : star (σ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_star_mul_self σ.eigUnitary
    have hσ_diag : star (σ.eigUnitary : Matrix d d ℂ) * σ.mat * (σ.eigUnitary : Matrix d d ℂ) =
        Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) := by
      have hspec : σ.mat = (σ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) *
          star (σ.eigUnitary : Matrix d d ℂ) := by
        simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
      conv_lhs => rw [hspec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star (σ.eigUnitary : Matrix d d ℂ)) (σ.eigUnitary : Matrix d d ℂ),
        hUs_star, Matrix.one_mul, Matrix.mul_one]
    have hj := congr_arg Complex.re (congr_fun (congr_fun hσ_diag j) j)
    have hlin : star (σ.eigUnitary : Matrix d d ℂ) * σ.mat * (σ.eigUnitary : Matrix d d ℂ) =
        (1 / 2 : ℝ) • (star (σ.eigUnitary : Matrix d d ℂ) * ρ₀.mat * (σ.eigUnitary : Matrix d d ℂ)) +
        (1 / 2 : ℝ) • (star (σ.eigUnitary : Matrix d d ℂ) * ρ₁.mat * (σ.eigUnitary : Matrix d d ℂ)) := by
      simp only [σ, DensityOp.midpoint, DensityOp.mix, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul]
      norm_num
    rw [hlin] at hj
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply,
      ↓reduceIte, Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hj
    linarith
  set c : ℝ := ((ρ₀.sqrtMat * σ.sqrtMat).trace.re + (ρ₁.sqrtMat * σ.sqrtMat).trace.re) / 2
  have hc_eq : c = (∑ i : d, ∑ j : d, Real.sqrt (ρ₀.eigvals i) * Real.sqrt (σ.eigvals j) * T₀ i j) / 2 +
      (∑ i : d, ∑ j : d, Real.sqrt (ρ₁.eigvals i) * Real.sqrt (σ.eigvals j) * T₁ i j) / 2 := by
    simp only [c, hT0_tr, hT1_tr, T₀, T₁]; ring
  have hc_pos : 0 < c := by
    rw [hc_eq]
    have hsum_σ : ∑ j : d, σ.eigvals j = 1 := σ.sum_eigvals
    have hex_j : ∃ j₀ : d, 0 < σ.eigvals j₀ := by
      by_contra hall; push Not at hall
      have : ∑ j : d, σ.eigvals j ≤ 0 := Finset.sum_nonpos fun j _ ↦ hall j
      linarith
    rcases hex_j with ⟨j₀, hj₀⟩
    have hmid0 := hmid_diag j₀
    have hnn0 : ∀ i j, 0 ≤ Real.sqrt (ρ₀.eigvals i) * Real.sqrt (σ.eigvals j) * T₀ i j :=
      fun i j ↦ mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (sq_nonneg _)
    have hnn1 : ∀ i j, 0 ≤ Real.sqrt (ρ₁.eigvals i) * Real.sqrt (σ.eigvals j) * T₁ i j :=
      fun i j ↦ mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (sq_nonneg _)
    have hsum_nn0 : 0 ≤ ∑ i : d, ∑ j : d, Real.sqrt (ρ₀.eigvals i) * Real.sqrt (σ.eigvals j) * T₀ i j :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnn0 i j
    have hsum_nn1 : 0 ≤ ∑ i : d, ∑ j : d, Real.sqrt (ρ₁.eigvals i) * Real.sqrt (σ.eigvals j) * T₁ i j :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnn1 i j
    by_cases h0pos : 0 < ∑ i : d, ρ₀.eigvals i * T₀ i j₀
    · have hex_i : ∃ i₀ : d, 0 < ρ₀.eigvals i₀ * T₀ i₀ j₀ := by
        by_contra hall; push Not at hall
        have : ∑ i : d, ρ₀.eigvals i * T₀ i j₀ ≤ 0 := Finset.sum_nonpos fun i _ ↦ hall i
        linarith
      rcases hex_i with ⟨i₀, hi₀⟩
      have hp0 : 0 < ρ₀.eigvals i₀ := by
        rcases eq_or_lt_of_le (ρ₀.eigvals_nonneg i₀) with h | h
        · rw [← h, zero_mul] at hi₀; linarith
        · exact h
      have hT_pos : 0 < T₀ i₀ j₀ := by
        rcases eq_or_lt_of_le (sq_nonneg (‖V₀ j₀ i₀‖)) with h | h
        · change 0 = T₀ i₀ j₀ at h; rw [← h, mul_zero] at hi₀; linarith
        · exact h
      have hterm_pos : 0 < Real.sqrt (ρ₀.eigvals i₀) * Real.sqrt (σ.eigvals j₀) * T₀ i₀ j₀ :=
        mul_pos (mul_pos (Real.sqrt_pos.mpr hp0) (Real.sqrt_pos.mpr hj₀)) hT_pos
      have hle : Real.sqrt (ρ₀.eigvals i₀) * Real.sqrt (σ.eigvals j₀) * T₀ i₀ j₀ ≤
          ∑ i : d, ∑ j : d, Real.sqrt (ρ₀.eigvals i) * Real.sqrt (σ.eigvals j) * T₀ i j :=
        le_trans (Finset.single_le_sum (fun j _ ↦ hnn0 i₀ j) (Finset.mem_univ j₀))
          (Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnn0 i j) (Finset.mem_univ i₀))
      linarith
    · push Not at h0pos
      have h1pos : 0 < ∑ i : d, ρ₁.eigvals i * T₁ i j₀ := by linarith
      have hex_i : ∃ i₀ : d, 0 < ρ₁.eigvals i₀ * T₁ i₀ j₀ := by
        by_contra hall; push Not at hall
        have : ∑ i : d, ρ₁.eigvals i * T₁ i j₀ ≤ 0 := Finset.sum_nonpos fun i _ ↦ hall i
        linarith
      rcases hex_i with ⟨i₀, hi₀⟩
      have hp1 : 0 < ρ₁.eigvals i₀ := by
        rcases eq_or_lt_of_le (ρ₁.eigvals_nonneg i₀) with h | h
        · rw [← h, zero_mul] at hi₀; linarith
        · exact h
      have hT_pos : 0 < T₁ i₀ j₀ := by
        rcases eq_or_lt_of_le (sq_nonneg (‖V₁ j₀ i₀‖)) with h | h
        · change 0 = T₁ i₀ j₀ at h; rw [← h, mul_zero] at hi₀; linarith
        · exact h
      have hterm_pos : 0 < Real.sqrt (ρ₁.eigvals i₀) * Real.sqrt (σ.eigvals j₀) * T₁ i₀ j₀ :=
        mul_pos (mul_pos (Real.sqrt_pos.mpr hp1) (Real.sqrt_pos.mpr hj₀)) hT_pos
      have hle : Real.sqrt (ρ₁.eigvals i₀) * Real.sqrt (σ.eigvals j₀) * T₁ i₀ j₀ ≤
          ∑ i : d, ∑ j : d, Real.sqrt (ρ₁.eigvals i) * Real.sqrt (σ.eigvals j) * T₁ i j :=
        le_trans (Finset.single_le_sum (fun j _ ↦ hnn1 i₀ j) (Finset.mem_univ j₀))
          (Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnn1 i j) (Finset.mem_univ i₀))
      linarith
  have hpoint : ∀ (p q t : ℝ), 0 ≤ p → 0 ≤ q → 0 ≤ t → (q = 0 → p * t = 0) →
      -2 * (p * t) * Real.log c + 2 * (p * t) - (2 / c) * (Real.sqrt p * Real.sqrt q * t) ≤
        -(Real.negMulLog p * t) - (p * t) * Real.log q := by
    intro p q t hp hq ht hsupp
    by_cases hpt : p * t = 0
    · rcases mul_eq_zero.mp hpt with rfl | rfl <;> simp [Real.negMulLog]
    · have hp_pos : 0 < p := lt_of_le_of_ne hp (fun h ↦ hpt (by rw [← h, zero_mul]))
      have ht_pos : 0 < t := lt_of_le_of_ne ht (fun h ↦ hpt (by rw [← h, mul_zero]))
      have hq_pos : 0 < q := lt_of_le_of_ne hq (fun h ↦ hpt (hsupp h.symm))
      have hlog := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt (q / p) / c by positivity)
      rw [Real.log_div (ne_of_gt (Real.sqrt_pos.mpr (div_pos hq_pos hp_pos))) (ne_of_gt hc_pos),
        Real.log_sqrt (le_of_lt (div_pos hq_pos hp_pos)),
        Real.log_div (ne_of_gt hq_pos) (ne_of_gt hp_pos)] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * (p * t) by positivity)
      have hsq : p * Real.sqrt (q / p) = Real.sqrt p * Real.sqrt q := by
        rw [Real.sqrt_div hq, ← mul_div_assoc, mul_comm p, mul_div_assoc,
          Real.div_sqrt, mul_comm]
      have hterm : 2 * (p * t) * (Real.sqrt (q / p) / c) = (2 / c) * (Real.sqrt p * Real.sqrt q * t) := by
        calc 2 * (p * t) * (Real.sqrt (q / p) / c)
            = (2 / c) * ((p * Real.sqrt (q / p)) * t) := by ring
          _ = (2 / c) * (Real.sqrt p * Real.sqrt q * t) := by rw [hsq]
      unfold Real.negMulLog
      linarith
  have hsum_pt : ∀ (ρ : DensityOp d) (T : d → d → ℝ),
      (∀ i j, 0 ≤ T i j) → (∀ i, ∑ j : d, T i j = 1) →
      (∀ i j, σ.eigvals j = 0 → ρ.eigvals i * T i j = 0) →
      -2 * Real.log c + 2 - (2 / c) * (∑ i : d, ∑ j : d, Real.sqrt (ρ.eigvals i) * Real.sqrt (σ.eigvals j) * T i j) ≤
        -(∑ i : d, Real.negMulLog (ρ.eigvals i)) - ∑ j : d, (∑ i : d, ρ.eigvals i * T i j) * Real.log (σ.eigvals j) := by
    intro ρ T hTnn hTj hsupp
    have hle : ∑ i : d, ∑ j : d,
          (-2 * (ρ.eigvals i * T i j) * Real.log c + 2 * (ρ.eigvals i * T i j) -
            (2 / c) * (Real.sqrt (ρ.eigvals i) * Real.sqrt (σ.eigvals j) * T i j)) ≤
        ∑ i : d, ∑ j : d, (-(Real.negMulLog (ρ.eigvals i) * T i j) - (ρ.eigvals i * T i j) * Real.log (σ.eigvals j)) :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        hpoint (ρ.eigvals i) (σ.eigvals j) (T i j) (ρ.eigvals_nonneg i) (σ.eigvals_nonneg j) (hTnn i j) (hsupp i j)
    have hLHS : (∑ i : d, ∑ j : d,
          (-2 * (ρ.eigvals i * T i j) * Real.log c + 2 * (ρ.eigvals i * T i j) -
            (2 / c) * (Real.sqrt (ρ.eigvals i) * Real.sqrt (σ.eigvals j) * T i j))) =
        -2 * Real.log c + 2 - (2 / c) * (∑ i : d, ∑ j : d, Real.sqrt (ρ.eigvals i) * Real.sqrt (σ.eigvals j) * T i j) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have h1 : (∑ i : d, ∑ j : d, -2 * (ρ.eigvals i * T i j) * Real.log c) = -2 * Real.log c := by
        have : ∀ i j, -2 * (ρ.eigvals i * T i j) * Real.log c = (-2 * Real.log c) * (ρ.eigvals i * T i j) :=
          fun i j ↦ by ring
        simp_rw [this, ← Finset.mul_sum, hTj, mul_one, ρ.sum_eigvals, mul_one]
      have h2 : (∑ i : d, ∑ j : d, 2 * (ρ.eigvals i * T i j)) = 2 := by
        simp_rw [← Finset.mul_sum, hTj, mul_one, ρ.sum_eigvals, mul_one]
      have h3 : (∑ i : d, ∑ j : d, (2 / c) * (Real.sqrt (ρ.eigvals i) * Real.sqrt (σ.eigvals j) * T i j)) =
          (2 / c) * ∑ i : d, ∑ j : d, Real.sqrt (ρ.eigvals i) * Real.sqrt (σ.eigvals j) * T i j := by
        simp_rw [← Finset.mul_sum]
      rw [h1, h2, h3]
    have hRHS : (∑ i : d, ∑ j : d, (-(Real.negMulLog (ρ.eigvals i) * T i j) -
          (ρ.eigvals i * T i j) * Real.log (σ.eigvals j))) =
        -(∑ i : d, Real.negMulLog (ρ.eigvals i)) - ∑ j : d, (∑ i : d, ρ.eigvals i * T i j) * Real.log (σ.eigvals j) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      congr 1
      · congr 1; apply Finset.sum_congr rfl; intro i _; rw [← Finset.mul_sum, hTj i, mul_one]
      · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_mul]
    linarith
  have hsupp0 : ∀ i j, σ.eigvals j = 0 → ρ₀.eigvals i * T₀ i j = 0 := by
    intro i j hq0
    have hmid0 := hmid_diag j
    rw [hq0] at hmid0
    have hnn0 : ∀ k, 0 ≤ ρ₀.eigvals k * T₀ k j := fun k ↦ mul_nonneg (ρ₀.eigvals_nonneg k) (sq_nonneg _)
    have hnn1 : ∀ k, 0 ≤ ρ₁.eigvals k * T₁ k j := fun k ↦ mul_nonneg (ρ₁.eigvals_nonneg k) (sq_nonneg _)
    have hs0 : ∑ k : d, ρ₀.eigvals k * T₀ k j = 0 := by
      have h1 : 0 ≤ ∑ k : d, ρ₀.eigvals k * T₀ k j := Finset.sum_nonneg fun k _ ↦ hnn0 k
      have h2 : 0 ≤ ∑ k : d, ρ₁.eigvals k * T₁ k j := Finset.sum_nonneg fun k _ ↦ hnn1 k
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ hnn0 k).mp hs0 i (Finset.mem_univ i)
  have hsupp1 : ∀ i j, σ.eigvals j = 0 → ρ₁.eigvals i * T₁ i j = 0 := by
    intro i j hq0
    have hmid0 := hmid_diag j
    rw [hq0] at hmid0
    have hnn0 : ∀ k, 0 ≤ ρ₀.eigvals k * T₀ k j := fun k ↦ mul_nonneg (ρ₀.eigvals_nonneg k) (sq_nonneg _)
    have hnn1 : ∀ k, 0 ≤ ρ₁.eigvals k * T₁ k j := fun k ↦ mul_nonneg (ρ₁.eigvals_nonneg k) (sq_nonneg _)
    have hs1 : ∑ k : d, ρ₁.eigvals k * T₁ k j = 0 := by
      have h1 : 0 ≤ ∑ k : d, ρ₀.eigvals k * T₀ k j := Finset.sum_nonneg fun k _ ↦ hnn0 k
      have h2 : 0 ≤ ∑ k : d, ρ₁.eigvals k * T₁ k j := Finset.sum_nonneg fun k _ ↦ hnn1 k
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ hnn1 k).mp hs1 i (Finset.mem_univ i)
  have hpt0 := hsum_pt ρ₀ T₀ (fun _ _ ↦ sq_nonneg _) hT0_j hsupp0
  have hpt1 := hsum_pt ρ₁ T₁ (fun _ _ ↦ sq_nonneg _) hT1_j hsupp1
  have hqjs_lb : -2 * Real.log c ≤ qjs ρ₀ ρ₁ * Real.log 2 := by
    have havg : -2 * Real.log c + 2 - (2 / c) * c ≤
        -((∑ i : d, Real.negMulLog (ρ₀.eigvals i)) + (∑ i : d, Real.negMulLog (ρ₁.eigvals i))) / 2 +
          ∑ j : d, Real.negMulLog (σ.eigvals j) := by
      have hcomb_σ : (∑ j : d, (∑ i : d, ρ₀.eigvals i * T₀ i j) * Real.log (σ.eigvals j)) / 2 +
          (∑ j : d, (∑ i : d, ρ₁.eigvals i * T₁ i j) * Real.log (σ.eigvals j)) / 2 =
          -(∑ j : d, Real.negMulLog (σ.eigvals j)) := by
        rw [← add_div, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro j _
        unfold Real.negMulLog
        rw [show ((∑ i : d, ρ₀.eigvals i * T₀ i j) * Real.log (σ.eigvals j) +
            (∑ i : d, ρ₁.eigvals i * T₁ i j) * Real.log (σ.eigvals j)) / 2 =
            ((∑ i : d, ρ₀.eigvals i * T₀ i j) / 2 + (∑ i : d, ρ₁.eigvals i * T₁ i j) / 2) *
              Real.log (σ.eigvals j) by ring, hmid_diag j]
        ring
      have h2c : (2 / c) * c =
          ((2 / c) * (∑ i : d, ∑ j : d, Real.sqrt (ρ₀.eigvals i) * Real.sqrt (σ.eigvals j) * T₀ i j) +
           (2 / c) * (∑ i : d, ∑ j : d, Real.sqrt (ρ₁.eigvals i) * Real.sqrt (σ.eigvals j) * T₁ i j)) / 2 := by
        rw [hc_eq]; ring
      linarith [hpt0, hpt1, h2c, hcomb_σ]
    have hcancel : (2 / c) * c = 2 := div_mul_cancel₀ 2 (ne_of_gt hc_pos)
    rw [hcancel] at havg
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hqjs_eq : qjs ρ₀ ρ₁ * Real.log 2 =
        ∑ j : d, Real.negMulLog (σ.eigvals j) -
          ((∑ i : d, Real.negMulLog (ρ₀.eigvals i)) + (∑ i : d, Real.negMulLog (ρ₁.eigvals i))) / 2 := by
      unfold qjs vonNeumannEntropy; dsimp only [σ]; field_simp [hlog2]
    linarith
  have hc_sq_le : c ^ 2 ≤ (1 + W.fidelityParam) / 2 := by
    let A : Matrix d d ℂ := ((1 / 2 : ℝ) : ℂ) • ρ₀.sqrtMat + ((1 / 2 : ℝ) : ℂ) • ρ₁.sqrtMat
    have hA_herm : A.IsHermitian := by
      rw [Matrix.IsHermitian]
      simp only [A, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Complex.star_def,
        Complex.conj_ofReal, ρ₀.sqrtMat_isHermitian.eq, ρ₁.sqrtMat_isHermitian.eq]
    have hc_tr : c = (A * σ.sqrtMat).trace.re := by
      simp only [c, A, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
        Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      ring
    have hc_le_sum : c ≤ ∑ p : d × d, ‖A p.1 p.2‖ * ‖σ.sqrtMat p.1 p.2‖ := by
      rw [hc_tr]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum, Fintype.sum_prod_type]
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      calc (A i j * σ.sqrtMat j i).re
          ≤ ‖A i j * σ.sqrtMat j i‖ := Complex.re_le_norm _
        _ = ‖A i j‖ * ‖σ.sqrtMat j i‖ := norm_mul _ _
        _ = ‖A i j‖ * ‖σ.sqrtMat i j‖ := by
            have hsym := congr_fun (congr_fun σ.sqrtMat_isHermitian.eq j) i
            simp only [Matrix.conjTranspose_apply] at hsym
            rw [← hsym, Complex.star_def, Complex.norm_conj]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := fun p : d × d ↦ ‖A p.1 p.2‖) (g := fun p : d × d ↦ ‖σ.sqrtMat p.1 p.2‖)
    have hnorm_tr : ∀ (M : Matrix d d ℂ), M.IsHermitian →
        ∑ p : d × d, ‖M p.1 p.2‖ ^ 2 = (M * M).trace.re := by
      intro M hM
      simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      have hsym := congr_fun (congr_fun hM.eq j) i
      simp only [Matrix.conjTranspose_apply] at hsym
      rw [← hsym, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    have hσ_tr : ∑ p : d × d, ‖σ.sqrtMat p.1 p.2‖ ^ 2 = 1 := by
      rw [hnorm_tr σ.sqrtMat σ.sqrtMat_isHermitian, σ.sqrtMat_mul_self, σ.trace_one, Complex.one_re]
    have hA_tr : ∑ p : d × d, ‖A p.1 p.2‖ ^ 2 ≤ (1 + W.fidelityParam) / 2 := by
      rw [hnorm_tr A hA_herm]
      have hAA : (A * A).trace.re = (1 + (ρ₀.sqrtMat * ρ₁.sqrtMat).trace.re) / 2 := by
        have h1 : A * A = ((1 / 4 : ℝ) : ℂ) • ρ₀.mat + ((1 / 4 : ℝ) : ℂ) • ρ₁.mat +
            ((1 / 4 : ℝ) : ℂ) • (ρ₀.sqrtMat * ρ₁.sqrtMat) +
            ((1 / 4 : ℝ) : ℂ) • (ρ₁.sqrtMat * ρ₀.sqrtMat) := by
          ext i j
          simp only [A, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
            ρ₀.sqrtMat_mul_self, ρ₁.sqrtMat_mul_self, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
          push_cast; ring
        rw [h1, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
          Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
          ρ₀.trace_one, ρ₁.trace_one, Matrix.trace_mul_comm ρ₁.sqrtMat ρ₀.sqrtMat]
        simp only [Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.one_re, Complex.one_im, zero_mul, sub_zero, mul_zero]
        ring
      rw [hAA]
      have hfid := re_trace_unitary_mul_le_traceNorm (1 : Matrix.unitaryGroup d ℂ) (ρ₀.sqrtMat * ρ₁.sqrtMat)
      simp only [OneMemClass.coe_one, Matrix.conjTranspose_one, Matrix.one_mul, traceNorm_sqrt_mul_sqrt] at hfid
      unfold CQChannel.fidelityParam
      linarith
    have hc_sq : c ^ 2 ≤ (∑ p : d × d, ‖A p.1 p.2‖ * ‖σ.sqrtMat p.1 p.2‖) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hc_pos) hc_le_sum 2
    rw [hσ_tr, mul_one] at hcs
    linarith
  have hF_nn : 0 ≤ W.fidelityParam := Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _
  have hlog_c2 : 2 * Real.log c ≤ Real.log ((1 + W.fidelityParam) / 2) := by
    have h1 : 2 * Real.log c = Real.log (c ^ 2) := by rw [Real.log_pow]; ring
    rw [h1]
    exact Real.log_le_log (sq_pos_of_pos hc_pos) hc_sq_le
  have hlog_rhs : Real.log ((1 + W.fidelityParam) / 2) = Real.log (1 + W.fidelityParam) - Real.log 2 :=
    Real.log_div (by linarith) (by norm_num)
  rw [hlog_rhs] at hlog_c2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold CQChannel.condEntropy Real.logb
  rw [le_div_iff₀ hlog2_pos]
  linarith

/-- Helper: Branch 1 of Proposition 4.2 for arbitrary `W₁, W₂`:
`H(W₁ ⊠ W₂) ≥ H(W₁) + Δ(1 - H(W₁), 1 - 2^(H(W₂) - 1))`. -/
private lemma prop_4_2_branch1 (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    W₁.condEntropy + deltaGap (1 - W₁.condEntropy) (1 - (2 : ℝ) ^ (W₂.condEntropy - 1)) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy := by
  obtain ⟨φ₀, φ₁, hφ₀, hφ₁, htr₀, htr₁, hov⟩ := exists_uhlmann_purification (W₂.out false) (W₂.out true)
  let W₂p : CQChannel (d₂ × d₂) :=
    { out := fun b ↦ match b with | false => pureState φ₀ hφ₀ | true => pureState φ₁ hφ₁ }
  have hW₂p_pure : W₂p.IsPureState := ⟨φ₀, φ₁, hφ₀, hφ₁, rfl, rfl⟩
  have hdpi : (CQChannel.checkCombine W₁ W₂p).condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy := by
    let e : (d₁ × d₂) × d₂ ≃ d₁ × (d₂ × d₂) := Equiv.prodAssoc d₁ d₂ d₂
    let reidx : DensityOp (d₁ × (d₂ × d₂)) → DensityOp ((d₁ × d₂) × d₂) := fun ρ ↦
      { mat := Matrix.of fun p q ↦ ρ.mat (e p) (e q)
        posSemidef := by
          rw [Matrix.posSemidef_iff_dotProduct_mulVec]
          refine ⟨?_, fun x ↦ ?_⟩
          · ext p q
            have hh := congr_fun (congr_fun ρ.isHermitian.eq (e p)) (e q)
            simpa [Matrix.conjTranspose_apply] using hh
          · have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp ρ.posSemidef).2 (fun a ↦ x (e.symm a))
            have heq : star x ⬝ᵥ (Matrix.of fun p q ↦ ρ.mat (e p) (e q)).mulVec x =
                star (fun a ↦ x (e.symm a)) ⬝ᵥ ρ.mat.mulVec (fun a ↦ x (e.symm a)) := by
              simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.of_apply]
              rw [← e.sum_comp]
              apply Finset.sum_congr rfl; intro p _
              simp only [Equiv.symm_apply_apply]
              congr 1
              rw [← e.sum_comp]
              apply Finset.sum_congr rfl; intro q _
              simp only [Equiv.symm_apply_apply]
            rw [heq]; exact hq
        trace_one := by
          rw [← ρ.trace_one]
          simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
          exact e.sum_comp (fun a ↦ ρ.mat a a) }
    have hS_reidx : ∀ ρ : DensityOp (d₁ × (d₂ × d₂)), vonNeumannEntropy (reidx ρ) = vonNeumannEntropy ρ := by
      intro ρ
      let P : Matrix ((d₁ × d₂) × d₂) (d₁ × (d₂ × d₂)) ℂ := Matrix.of fun p q ↦ if e p = q then 1 else 0
      have hPHP : Pᴴ * P = 1 := by
        ext p q
        simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
        rw [Finset.sum_eq_single (e.symm p)]
        · simp [e.symm_apply_eq, eq_comm]
        · intro r _ hr; simp [show e r ≠ p from fun h ↦ hr (e.symm_apply_eq.mpr h.symm).symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hmat : (reidx ρ).mat = P * ρ.mat * Pᴴ := by
        ext p q
        simp only [reidx, P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
        rw [Finset.sum_eq_single (e q)]
        · rw [Finset.sum_eq_single (e p)]
          · simp
          · intro r _ hr; simp [Ne.symm hr]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro r _ hr; simp [Ne.symm hr]
        · intro h; exact absurd (Finset.mem_univ _) h
      unfold vonNeumannEntropy DensityOp.eigvals
      congr 1
      let M : Matrix ((d₁ × d₂) × d₂) (d₁ × (d₂ × d₂)) ℂ := P * ρ.sqrtMat
      have hMMH : M * Mᴴ = (reidx ρ).mat := by
        calc M * Mᴴ = P * (ρ.sqrtMat * ρ.sqrtMat) * Pᴴ := by
              simp only [M, Matrix.conjTranspose_mul, ρ.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
          _ = P * ρ.mat * Pᴴ := by rw [ρ.sqrtMat_mul_self]
          _ = (reidx ρ).mat := hmat.symm
      have hMHM : Mᴴ * M = ρ.mat := by
        calc Mᴴ * M = ρ.sqrtMat * ((Pᴴ * P) * ρ.sqrtMat) := by
              simp only [M, Matrix.conjTranspose_mul, ρ.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
          _ = ρ.mat := by rw [hPHP, Matrix.one_mul, ρ.sqrtMat_mul_self]
      have hcp := charpoly_mul_conjTranspose_eq M
      rw [hMMH, hMHM] at hcp
      exact spectral_sum_eq_of_charpoly_mul_X_pow (reidx ρ).isHermitian ρ.isHermitian hcp (by simp [Real.negMulLog])
    have hpt0 : (partialTrace₂ (reidx ((CQChannel.checkCombine W₁ W₂p).out false))).mat =
        ((CQChannel.checkCombine W₁ W₂).out false).mat := by
      ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
      simp only [partialTrace₂, reidx, CQChannel.checkCombine, W₂p, Bool.not_false, DensityOp.midpoint,
        DensityOp.mix, DensityOp.tensor, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.kroneckerMap_apply, Complex.real_smul, e, Equiv.prodAssoc_apply, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      have h0 : ∑ k : d₂, (pureState φ₀ hφ₀).mat (i₂, k) (j₂, k) = (W₂.out false).mat i₂ j₂ := by
        have := congr_fun (congr_fun htr₀ i₂) j₂; simpa [partialTrace₂] using this
      have h1 : ∑ k : d₂, (pureState φ₁ hφ₁).mat (i₂, k) (j₂, k) = (W₂.out true).mat i₂ j₂ := by
        have := congr_fun (congr_fun htr₁ i₂) j₂; simpa [partialTrace₂] using this
      rw [h0, h1]
    have hpt1 : (partialTrace₂ (reidx ((CQChannel.checkCombine W₁ W₂p).out true))).mat =
        ((CQChannel.checkCombine W₁ W₂).out true).mat := by
      ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
      simp only [partialTrace₂, reidx, CQChannel.checkCombine, W₂p, Bool.not_true, DensityOp.midpoint,
        DensityOp.mix, DensityOp.tensor, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.kroneckerMap_apply, Complex.real_smul, e, Equiv.prodAssoc_apply, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      have h0 : ∑ k : d₂, (pureState φ₀ hφ₀).mat (i₂, k) (j₂, k) = (W₂.out false).mat i₂ j₂ := by
        have := congr_fun (congr_fun htr₀ i₂) j₂; simpa [partialTrace₂] using this
      have h1 : ∑ k : d₂, (pureState φ₁ hφ₁).mat (i₂, k) (j₂, k) = (W₂.out true).mat i₂ j₂ := by
        have := congr_fun (congr_fun htr₁ i₂) j₂; simpa [partialTrace₂] using this
      rw [h0, h1]
    have hq_le := qjs_partialTrace₂_le
      (reidx ((CQChannel.checkCombine W₁ W₂p).out false))
      (reidx ((CQChannel.checkCombine W₁ W₂p).out true))
    have hq_eq1 : qjs (partialTrace₂ (reidx ((CQChannel.checkCombine W₁ W₂p).out false)))
        (partialTrace₂ (reidx ((CQChannel.checkCombine W₁ W₂p).out true))) =
        qjs ((CQChannel.checkCombine W₁ W₂).out false) ((CQChannel.checkCombine W₁ W₂).out true) := by
      unfold qjs
      have hm : (DensityOp.midpoint (partialTrace₂ (reidx ((CQChannel.checkCombine W₁ W₂p).out false)))
          (partialTrace₂ (reidx ((CQChannel.checkCombine W₁ W₂p).out true)))).mat =
          (DensityOp.midpoint ((CQChannel.checkCombine W₁ W₂).out false) ((CQChannel.checkCombine W₁ W₂).out true)).mat := by
        simp [DensityOp.midpoint, DensityOp.mix, hpt0, hpt1]
      rw [vonNeumannEntropy_eq_of_mat_eq hm, vonNeumannEntropy_eq_of_mat_eq hpt0,
        vonNeumannEntropy_eq_of_mat_eq hpt1]
    have hq_eq2 : qjs (reidx ((CQChannel.checkCombine W₁ W₂p).out false))
        (reidx ((CQChannel.checkCombine W₁ W₂p).out true)) =
        qjs ((CQChannel.checkCombine W₁ W₂p).out false) ((CQChannel.checkCombine W₁ W₂p).out true) := by
      unfold qjs
      have hm : (DensityOp.midpoint (reidx ((CQChannel.checkCombine W₁ W₂p).out false))
          (reidx ((CQChannel.checkCombine W₁ W₂p).out true))).mat =
          (reidx (DensityOp.midpoint ((CQChannel.checkCombine W₁ W₂p).out false)
            ((CQChannel.checkCombine W₁ W₂p).out true))).mat := by
        ext p q; simp [reidx, DensityOp.midpoint, DensityOp.mix]
      rw [vonNeumannEntropy_eq_of_mat_eq hm, hS_reidx, hS_reidx, hS_reidx]
    unfold CQChannel.condEntropy
    linarith
  have hpure := (theorem_1_2a_pure W₁ W₂p hW₂p_pure).2.1
  have hF2 : W₂.fidelityParam = ‖∑ i : d₂ × d₂, star (φ₀ i) * φ₁ i‖ := by
    unfold CQChannel.fidelityParam; exact hov.symm
  have hF2_nn : 0 ≤ W₂.fidelityParam := by rw [hF2]; exact norm_nonneg _
  have hF2_le1 : W₂.fidelityParam ≤ 1 := by
    rw [hF2]; exact norm_inner_le_one hφ₀ hφ₁
  have hH₂p : W₂p.condEntropy = 1 - h2 ((1 - W₂.fidelityParam) / 2) := by
    unfold CQChannel.condEntropy W₂p
    dsimp only
    rw [qjs_pureState φ₀ φ₁ hφ₀ hφ₁, ← hF2]
  have hinv_p : h2Inv (1 - W₂p.condEntropy) = (1 - W₂.fidelityParam) / 2 := by
    rw [hH₂p, sub_sub_cancel, h2Inv_h2 ⟨by linarith, by linarith⟩]
  have hdelta_eq : W₁.condEntropy + W₂p.condEntropy - 1 + gc (1 - W₁.condEntropy) (1 - W₂p.condEntropy) =
      W₁.condEntropy + deltaGap (1 - W₁.condEntropy) ((1 - W₂.fidelityParam) / 2) := by
    unfold deltaGap gc
    rw [hinv_p, hH₂p]
    ring
  have hfid_ent := condEntropy_le_logb_one_add_fidelityParam W₂
  have hH₂_mem := condEntropy_mem_Icc W₂
  have h2pow_le : (2 : ℝ) ^ W₂.condEntropy ≤ 1 + W₂.fidelityParam := by
    have h1 : Real.logb 2 ((2 : ℝ) ^ W₂.condEntropy) ≤ Real.logb 2 (1 + W₂.fidelityParam) := by
      rwa [Real.logb_rpow (by norm_num) (by norm_num)]
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog_le : Real.log ((2 : ℝ) ^ W₂.condEntropy) ≤ Real.log (1 + W₂.fidelityParam) := by
      unfold Real.logb at h1
      exact (div_le_div_iff_of_pos_right hlog2_pos).mp h1
    exact (Real.log_le_log_iff (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)).mp hlog_le
  have hp_le : (1 - W₂.fidelityParam) / 2 ≤ 1 - (2 : ℝ) ^ (W₂.condEntropy - 1) := by
    have hpow : (2 : ℝ) ^ (W₂.condEntropy - 1) = (2 : ℝ) ^ W₂.condEntropy / 2 := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    linarith
  have h2pow_mem : 1 - (2 : ℝ) ^ (W₂.condEntropy - 1) ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    have h1 : (2 : ℝ) ^ (W₂.condEntropy - 1) ≤ (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hH₂_mem.2])
    have h2 : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (W₂.condEntropy - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hH₂_mem.1])
    rw [Real.rpow_zero] at h1
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_one] at h2
    exact ⟨by linarith, by linarith⟩
  have hH₁_mem := condEntropy_mem_Icc W₁
  have hanti := antitoneOn_deltaGap (u := 1 - W₁.condEntropy)
    ⟨by linarith [hH₁_mem.2], by linarith [hH₁_mem.1]⟩
    (show (1 - W₂.fidelityParam) / 2 ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨by linarith, by linarith⟩)
    h2pow_mem hp_le
  linarith

/-- **Proposition 4.2 (Four-Branch Purification Bound, Eq. 1.6)**:
For all independent binary-input c-q channels `W₁, W₂`,
`H(W₁ ⊠ W₂) ≥ max { H₁ + Δ(1 - H₁, 1 - 2^(H₂ - 1)), H₂ + Δ(1 - H₂, 1 - 2^(H₁ - 1)),
                    H₂ + Δ(H₁, 1 - 2^(-H₂)),        H₁ + Δ(H₂, 1 - 2^(-H₁)) }`. -/
theorem prop_4_2_four_branch (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    max (max (W₁.condEntropy + deltaGap (1 - W₁.condEntropy) (1 - (2 : ℝ) ^ (W₂.condEntropy - 1)))
             (W₂.condEntropy + deltaGap (1 - W₂.condEntropy) (1 - (2 : ℝ) ^ (W₁.condEntropy - 1))))
        (max (W₂.condEntropy + deltaGap W₁.condEntropy (1 - (2 : ℝ) ^ (-W₂.condEntropy)))
             (W₁.condEntropy + deltaGap W₂.condEntropy (1 - (2 : ℝ) ^ (-W₁.condEntropy)))) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy := by
  have hb1 := prop_4_2_branch1 W₁ W₂
  have hb2 : W₂.condEntropy + deltaGap (1 - W₂.condEntropy) (1 - (2 : ℝ) ^ (W₁.condEntropy - 1)) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy := by
    rw [condEntropy_checkCombine_comm]; exact prop_4_2_branch1 W₂ W₁
  have hD1_1 := prop_2_2_D1 W₁
  have hD1_2 := prop_2_2_D1 W₂
  have h29 := checkCombine_duality W₁ W₂
  have hb3 : W₂.condEntropy + deltaGap W₁.condEntropy (1 - (2 : ℝ) ^ (-W₂.condEntropy)) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy := by
    have h := prop_4_2_branch1 W₁.dual W₂.dual
    have h1 : 1 - W₁.dual.condEntropy = W₁.condEntropy := by linarith
    have h2 : W₂.dual.condEntropy - 1 = -W₂.condEntropy := by linarith
    rw [h1, h2] at h
    linarith
  have hb4 : W₁.condEntropy + deltaGap W₂.condEntropy (1 - (2 : ℝ) ^ (-W₁.condEntropy)) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy := by
    have h := prop_4_2_branch1 W₂.dual W₁.dual
    rw [condEntropy_checkCombine_comm] at h
    have h1 : 1 - W₂.dual.condEntropy = W₂.condEntropy := by linarith
    have h2 : W₁.dual.condEntropy - 1 = -W₁.condEntropy := by linarith
    rw [h1, h2] at h
    linarith
  exact max_le (max_le hb1 hb2) (max_le hb3 hb4)

/-! ### Part 4: Theorem 1.2(b) — Linear-Scaling Splitting & Potential Contraction -/

/-- **Theorem 1.2(b), Eq. (1.7) (Linear-Scaling Polarization Splitting)**:
For every binary-input c-q channel `W`,
`H(W⁻) - H(W) = H(W) - H(W⁺) ≥ θ₀ H(W)(1 - H(W))` where `θ₀ > 0.05673`. -/
theorem theorem_1_2b_linear_splitting (W : CQChannel d) :
    W.minusChannel.condEntropy - W.condEntropy = W.condEntropy - W.plusChannel.condEntropy ∧
    theta0 * W.condEntropy * (1 - W.condEntropy) ≤ W.minusChannel.condEntropy - W.condEntropy := by
  have hcons := entropy_conservation W W
  have heq : W.minusChannel.condEntropy - W.condEntropy = W.condEntropy - W.plusChannel.condEntropy := by
    unfold CQChannel.minusChannel CQChannel.plusChannel; linarith
  refine ⟨heq, ?_⟩
  have hH_mem := condEntropy_mem_Icc W
  have hfb := prop_4_2_four_branch W W
  have hb1 : W.condEntropy + deltaGap (1 - W.condEntropy) (1 - (2 : ℝ) ^ (W.condEntropy - 1)) ≤
      W.minusChannel.condEntropy :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hfb
  have hb3 : W.condEntropy + deltaGap W.condEntropy (1 - (2 : ℝ) ^ (-W.condEntropy)) ≤
      W.minusChannel.condEntropy :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hfb
  rcases eq_or_lt_of_le hH_mem.1 with h0 | h0_pos
  · rw [← h0]; have hHm := condEntropy_mem_Icc W.minusChannel; linarith [hHm.1]
  · rcases eq_or_lt_of_le hH_mem.2 with h1 | h1_lt
    · rw [h1]; have hHp := condEntropy_mem_Icc W.plusChannel; linarith [hHp.2]
    · rcases le_or_gt (1 / 2 : ℝ) W.condEntropy with hge | hlt
      · have hsc := prop_4_3_scalar hge h1_lt
        linarith
      · have hsc := prop_4_3_scalar (H := 1 - W.condEntropy) (by linarith) (by linarith)
        have h1 : 1 - (1 - W.condEntropy) = W.condEntropy := by ring
        have h2 : (1 - W.condEntropy) - 1 = -W.condEntropy := by ring
        rw [h1, h2] at hsc
        linarith

/-- **Theorem 1.2(b), Eq. (1.9) (Uniform Potential Contraction)**:
For every binary-input c-q channel `W`,
`½ (T(W⁻) + T(W⁺)) ≤ Λ₀ T(W)` where `T(W) = √(H(W)(1 - H(W)))` and `Λ₀ = √(1 - θ₀²/4) < 1`. -/
theorem theorem_1_2b_potential_contraction (W : CQChannel d) :
    (W.minusChannel.potential + W.plusChannel.potential) / 2 ≤ Lambda0 * W.potential := by
  have hH := condEntropy_mem_Icc W
  have hHm := condEntropy_mem_Icc W.minusChannel
  have hHp := condEntropy_mem_Icc W.plusChannel
  have hsplit := theorem_1_2b_linear_splitting W
  unfold CQChannel.potential Lambda0
  have h := prop_4_4_potential_contraction_general hH hHp hHm
    (by linarith [hsplit.1]) (le_of_lt theta0_pos) theta0_lt_one hsplit.2
  linarith

end PolarCodes
