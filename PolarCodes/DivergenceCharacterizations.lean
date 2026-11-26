/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.PhiAndFuchs
import PolarCodes.QuantumChannels

/-!
# Section 2.1 Divergence Characterizations and RelEntropy Finiteness

This module proves:
1. General-state QJS–relative-entropy identity (`qjs_eq_avg_relEntropy`).
2. Klein's inequality equality characterization (`relEntropy_eq_zero_iff`).
3. QJS range and equality characterizations (`qjs_mem_Icc`, `qjs_eq_zero_iff`, `qjs_eq_one_iff`).
4. General finite-distribution block-diagonal additivity of `rootFidelity` (`rootFidelity_block_diagonal`).
5. Explicit finiteness lemmas for dephasing relative entropy (`relEntropy_dephaseState_ne_top`),
   Umegaki relative-entropy form of Lemma 4.1 Part 4 (`lemma_4_1_gram_dephasing_relEntropy`),
   and explicit-finiteness Theorem 1.3 relative-entropy statements.
-/

open Matrix BigOperators Real Set Filter Polynomial
open scoped ComplexOrder ENNReal

namespace PolarCodes

section Section2Characterizations

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- General-state identity `QJS(ρ, σ) = (D(ρ ‖ m).toReal + D(σ ‖ m).toReal) / 2` where
`m = (ρ + σ) / 2`, valid for all finite-dimensional density operators `ρ, σ` (including
rank-deficient states). -/
theorem qjs_eq_avg_relEntropy (ρ σ : DensityOp d) :
    relEntropy ρ (DensityOp.midpoint ρ σ) ≠ ⊤ ∧
    relEntropy σ (DensityOp.midpoint ρ σ) ≠ ⊤ ∧
    qjs ρ σ = ((relEntropy ρ (DensityOp.midpoint ρ σ)).toReal +
      (relEntropy σ (DensityOp.midpoint ρ σ)).toReal) / 2 := by
  let m := DensityOp.midpoint ρ σ
  have hm_eq : m.mat = ((1 / 2 : ℝ) : ℂ) • ρ.mat + ((1 / 2 : ℝ) : ℂ) • σ.mat := by
    simp only [m, DensityOp.midpoint, DensityOp.mix]; norm_num
  have hsupp_left : ∀ (A B : DensityOp d),
      let M := DensityOp.midpoint A B
      suppSubset A M := by
    intro A B M i j hi hj
    set v : d → ℂ := fun k ↦ (M.eigUnitary : Matrix d d ℂ) k j
    have hMv : M.mat *ᵥ v = 0 := by
      rw [density_spectral_eq M]
      simp only [Matrix.mulVec_mulVec]
      have h1 : star (M.eigUnitary : Matrix d d ℂ) *ᵥ v = Pi.single j 1 := by
        ext k
        have h := congr_fun (congr_fun (Unitary.coe_star_mul_self M.eigUnitary) k) j
        simpa [v, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply,
          eq_comm] using h
      rw [h1]
      have h2 : Matrix.diagonal (Complex.ofReal ∘ M.eigvals) *ᵥ Pi.single j (1 : ℂ) = 0 := by
        ext k
        simp only [Matrix.mulVec_diagonal, Pi.single_apply, Function.comp_apply, mul_ite, mul_one,
          mul_zero]
        split_ifs with hk
        · subst hk; simp [hj]
        · rfl
      rw [h2, Matrix.mulVec_zero]
    have hdot0 : star v ⬝ᵥ (M.mat *ᵥ v) = 0 := by rw [hMv, dotProduct_zero]
    have hdot_split : star v ⬝ᵥ (M.mat *ᵥ v) =
        ((1 / 2 : ℝ) : ℂ) * (star v ⬝ᵥ (A.mat *ᵥ v)) +
        ((1 / 2 : ℝ) : ℂ) * (star v ⬝ᵥ (B.mat *ᵥ v)) := by
      simp only [M, DensityOp.midpoint, DensityOp.mix, Matrix.add_mulVec, Matrix.smul_mulVec,
        dotProduct_add, dotProduct_smul, smul_eq_mul]
      norm_num
    have hA_nn := (Matrix.posSemidef_iff_dotProduct_mulVec.mp A.posSemidef).2 v
    have hB_nn := (Matrix.posSemidef_iff_dotProduct_mulVec.mp B.posSemidef).2 v
    rw [hdot_split] at hdot0
    have hA0 : star v ⬝ᵥ (A.mat *ᵥ v) = 0 := by
      have hre := congr_arg Complex.re hdot0
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.zero_re] at hre
      rw [Complex.le_def] at hA_nn hB_nn
      simp only [Complex.zero_re, Complex.zero_im] at hA_nn hB_nn
      apply Complex.ext
      · simp; linarith [hA_nn.1, hB_nn.1]
      · exact hA_nn.2.symm
    have hAv : A.mat *ᵥ v = 0 := by
      have h1 : (A.sqrtMat *ᵥ v) = 0 := by
        have hdot_sq : star (A.sqrtMat *ᵥ v) ⬝ᵥ (A.sqrtMat *ᵥ v) = 0 := by
          calc star (A.sqrtMat *ᵥ v) ⬝ᵥ (A.sqrtMat *ᵥ v)
              = star v ⬝ᵥ (A.sqrtMatᴴ *ᵥ (A.sqrtMat *ᵥ v)) := by
                simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.conjTranspose_apply,
                  star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl; intro a _
                apply Finset.sum_congr rfl; intro b _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro c _; ring
            _ = star v ⬝ᵥ ((A.sqrtMat * A.sqrtMat) *ᵥ v) := by
                rw [A.sqrtMat_isHermitian.eq, Matrix.mulVec_mulVec]
            _ = star v ⬝ᵥ (A.mat *ᵥ v) := by rw [A.sqrtMat_mul_self]
            _ = 0 := hA0
        ext k
        have hsum0 : ∑ a : d, ‖(A.sqrtMat *ᵥ v) a‖ ^ 2 = 0 := by
          have hre := congr_arg Complex.re hdot_sq
          simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.zero_re] at hre
          rw [← hre]
          apply Finset.sum_congr rfl; intro a _
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
        have hk0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ ↦ sq_nonneg ‖(A.sqrtMat *ᵥ v) a‖)).mp
          hsum0 k (Finset.mem_univ k)
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hk0)
      rw [← A.sqrtMat_mul_self, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
    have hcoeff : ((star (A.eigUnitary : Matrix d d ℂ) *ᵥ v) i) = 0 := by
      have h3 : (star (A.eigUnitary : Matrix d d ℂ) *ᵥ (A.mat *ᵥ v)) i = 0 := by
        rw [hAv, Matrix.mulVec_zero]; rfl
      rw [density_spectral_eq A] at h3
      simp only [Matrix.mulVec_mulVec] at h3
      rw [← Matrix.mul_assoc (star (A.eigUnitary : Matrix d d ℂ)),
        Unitary.coe_star_mul_self A.eigUnitary, Matrix.one_mul,
        Matrix.mulVec_diagonal] at h3
      simp only [Function.comp_apply, mul_eq_zero, Complex.ofReal_eq_zero] at h3
      exact h3.resolve_left hi
    have hst : (star (M.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i =
        star ((star (A.eigUnitary : Matrix d d ℂ) *ᵥ v) i) := by
      simp [v, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.star_apply, mul_comm]
    rw [hst, hcoeff, star_zero]
  have hsupp1 : suppSubset ρ m := hsupp_left ρ σ
  have hsupp2 : suppSubset σ m := by
    have hmsym : (DensityOp.midpoint σ ρ).mat = m.mat := by
      simp only [m, DensityOp.midpoint, DensityOp.mix]; norm_num; rw [add_comm]
    have h := hsupp_left σ ρ
    intro i j hi hj
    have heq : DensityOp.midpoint σ ρ = m := by
      rcases m with ⟨m₁, p₁, t₁⟩
      cases hmsym' : DensityOp.midpoint σ ρ with
      | mk m₂ p₂ t₂ =>
        simp only [hmsym'] at hmsym; subst hmsym; rfl
    rw [heq] at h
    exact h i j hi hj
  have hne1 : relEntropy ρ m ≠ ⊤ := by unfold relEntropy; rw [if_pos hsupp1]; exact ENNReal.ofReal_ne_top
  have hne2 : relEntropy σ m ≠ ⊤ := by unfold relEntropy; rw [if_pos hsupp2]; exact ENNReal.ofReal_ne_top
  have hval : ∀ (A : DensityOp d) (hsuppA : suppSubset A m),
      (relEntropy A m).toReal = -vonNeumannEntropy A -
        ((A.mat * ((m.eigUnitary : Matrix d d ℂ) *
          Matrix.diagonal (fun j ↦ if m.eigvals j = 0 then (0 : ℂ) else (Real.log (m.eigvals j) : ℂ)) *
          star (m.eigUnitary : Matrix d d ℂ))).trace).re / Real.log 2 := by
    intro A hsuppA
    have hcol : ∀ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 = 1 := by
      intro i
      have hW : (star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ))ᴴ *
          (star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) = 1 := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (star (m.eigUnitary : Matrix d d ℂ))ᴴ,
          ← Matrix.star_eq_conjTranspose, star_star, Unitary.coe_mul_star_self m.eigUnitary,
          Matrix.one_mul, ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self A.eigUnitary]
      have h := congr_arg Complex.re (congr_fun (congr_fun hW i) i)
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
        Complex.re_sum, Complex.one_re] at h
      rw [← h]; apply Finset.sum_congr rfl; intro j _
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    have hrow : ∀ j : d, ∑ i : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 = 1 := by
      intro j
      have hW : (star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) *
          (star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ))ᴴ = 1 := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (A.eigUnitary : Matrix d d ℂ),
          ← Matrix.star_eq_conjTranspose, Unitary.coe_mul_star_self A.eigUnitary,
          Matrix.one_mul, ← Matrix.star_eq_conjTranspose, star_star, Unitary.coe_star_mul_self m.eigUnitary]
      have h := congr_arg Complex.re (congr_fun (congr_fun hW j) j)
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
        Complex.re_sum, Complex.one_re] at h
      rw [← h]; apply Finset.sum_congr rfl; intro i _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    have htrA : ∑ i : d, A.eigvals i = 1 := by
      have h := congr_arg Complex.re (A.isHermitian.trace_eq_sum_eigenvalues.symm.trans A.trace_one)
      simpa [DensityOp.eigvals, Complex.re_sum] using h
    have htrm : ∑ j : d, m.eigvals j = 1 := by
      have h := congr_arg Complex.re (m.isHermitian.trace_eq_sum_eigenvalues.symm.trans m.trace_one)
      simpa [DensityOp.eigvals, Complex.re_sum] using h
    have hsum_nn : 0 ≤ (∑ i : d, ∑ j : d,
        ‖(star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (A.eigvals i * (Real.log (A.eigvals i) - Real.log (m.eigvals j)))) / Real.log 2 := by
      have hge0 : 0 ≤ ∑ i : d, ∑ j : d,
          ‖(star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
            (A.eigvals i * (Real.log (A.eigvals i) - Real.log (m.eigvals j)) - (A.eigvals i - m.eigvals j)) := by
        apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
        by_cases hAi : A.eigvals i = 0
        · rw [hAi]; simp only [zero_mul, zero_sub, neg_neg]
          exact mul_nonneg (sq_nonneg _) (m.eigvals_nonneg j)
        · by_cases hmj : m.eigvals j = 0
          · rw [hsuppA i j hAi hmj]; simp
          · have hAp : 0 < A.eigvals i := lt_of_le_of_ne (A.eigvals_nonneg i) (Ne.symm hAi)
            have hmp : 0 < m.eigvals j := lt_of_le_of_ne (m.eigvals_nonneg j) (Ne.symm hmj)
            apply mul_nonneg (sq_nonneg _)
            have hlog := Real.log_le_sub_one_of_pos (div_pos hmp hAp)
            rw [Real.log_div (ne_of_gt hmp) (ne_of_gt hAp)] at hlog
            have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hAp)
            have hsimp : A.eigvals i * (m.eigvals j / A.eigvals i - 1) = m.eigvals j - A.eigvals i := by
              field_simp [ne_of_gt hAp]
            linarith
      have hsum_diff : ∑ i : d, ∑ j : d,
          ‖(star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
            (A.eigvals i - m.eigvals j) = 0 := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hcol, one_mul]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, hrow, one_mul, htrA, htrm, sub_self]
      simp_rw [mul_sub, Finset.sum_sub_distrib] at hge0
      rw [hsum_diff, sub_zero] at hge0
      exact div_nonneg hge0 (le_of_lt (Real.log_pos (by norm_num)))
    unfold relEntropy
    rw [if_pos hsuppA, ENNReal.toReal_ofReal hsum_nn]
    set L_m : Matrix d d ℂ := (m.eigUnitary : Matrix d d ℂ) *
      Matrix.diagonal (fun j ↦ if m.eigvals j = 0 then (0 : ℂ) else (Real.log (m.eigvals j) : ℂ)) *
      star (m.eigUnitary : Matrix d d ℂ)
    have htr_L : ((A.mat * L_m).trace).re =
        ∑ i : d, ∑ j : d,
          ‖(star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
            (A.eigvals i * Real.log (m.eigvals j)) := by
      have hW_def : (A.mat * L_m).trace =
          ∑ i : d, ∑ j : d,
            ((‖(star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 : ℝ) : ℂ) *
              ((A.eigvals i : ℂ) * (if m.eigvals j = 0 then (0 : ℂ) else (Real.log (m.eigvals j) : ℂ))) := by
        rw [density_spectral_eq A]
        simp only [L_m, Matrix.mul_assoc]
        rw [Matrix.trace_mul_cycle]
        simp only [Matrix.mul_assoc]
        set W := star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)
        have hW_star : star (A.eigUnitary : Matrix d d ℂ) * (m.eigUnitary : Matrix d d ℂ) = Wᴴ := by
          simp [W, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose]
        have hcy : (star (m.eigUnitary : Matrix d d ℂ) * ((A.eigUnitary : Matrix d d ℂ) *
            (Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * (star (A.eigUnitary : Matrix d d ℂ) *
            ((m.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun j ↦ if m.eigvals j = 0 then (0 : ℂ) else (Real.log (m.eigvals j) : ℂ))))) )).trace =
            (W * Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * Wᴴ *
              Matrix.diagonal (fun j ↦ if m.eigvals j = 0 then (0 : ℂ) else (Real.log (m.eigvals j) : ℂ))).trace := by
          simp only [Matrix.mul_assoc, W, hW_star]
        rw [hcy]
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.mul_diagonal,
          Matrix.diagonal_mul, Matrix.conjTranspose_apply, Function.comp_apply]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [mul_comm (W j i) (A.eigvals i : ℂ), mul_assoc, ← mul_assoc (W j i),
          Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        ring
      rw [hW_def, Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl; intro j _
      by_cases hmj : m.eigvals j = 0 <;> simp [hmj]
    rw [htr_L]
    unfold vonNeumannEntropy
    have hsplit : ∑ i : d, ∑ j : d,
        ‖(star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (A.eigvals i * (Real.log (A.eigvals i) - Real.log (m.eigvals j))) =
        (∑ i : d, A.eigvals i * Real.log (A.eigvals i)) -
        (∑ i : d, ∑ j : d, ‖(star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (A.eigvals i * Real.log (m.eigvals j))) := by
      have h1 : ∀ i j, ‖(star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (A.eigvals i * (Real.log (A.eigvals i) - Real.log (m.eigvals j))) =
          ‖(star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
            (A.eigvals i * Real.log (A.eigvals i)) -
          ‖(star (m.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
            (A.eigvals i * Real.log (m.eigvals j)) := fun _ _ ↦ by ring
      simp_rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul, hcol, one_mul]
    rw [hsplit, sub_div]
    have hneg : -(∑ i : d, Real.negMulLog (A.eigvals i)) / Real.log 2 =
        (∑ i : d, A.eigvals i * Real.log (A.eigvals i)) / Real.log 2 := by
      congr 1; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; simp [Real.negMulLog]
    linarith
  refine ⟨hne1, hne2, ?_⟩
  rw [hval ρ hsupp1, hval σ hsupp2]
  set L_m : Matrix d d ℂ := (m.eigUnitary : Matrix d d ℂ) *
    Matrix.diagonal (fun j ↦ if m.eigvals j = 0 then (0 : ℂ) else (Real.log (m.eigvals j) : ℂ)) *
    star (m.eigUnitary : Matrix d d ℂ)
  have htr_m : ((m.mat * L_m).trace).re / Real.log 2 = -vonNeumannEntropy m := by
    rw [density_spectral_eq m]
    simp only [L_m, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (m.eigUnitary : Matrix d d ℂ)), Unitary.coe_star_mul_self m.eigUnitary,
      Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self m.eigUnitary, Matrix.one_mul,
      Matrix.trace_diagonal, Complex.re_sum]
    unfold vonNeumannEntropy
    rw [← neg_div, ← Finset.sum_neg_distrib]
    congr 1; apply Finset.sum_congr rfl; intro j _
    by_cases hmj : m.eigvals j = 0 <;> simp [hmj, Real.negMulLog]
  have htr_mid : (((ρ.mat * L_m).trace).re + ((σ.mat * L_m).trace).re) / 2 = ((m.mat * L_m).trace).re := by
    rw [hm_eq, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  unfold qjs
  change vonNeumannEntropy m - (vonNeumannEntropy ρ + vonNeumannEntropy σ) / 2 = _
  have hdiv_mid : (((ρ.mat * L_m).trace).re / Real.log 2 + ((σ.mat * L_m).trace).re / Real.log 2) / 2 =
      -vonNeumannEntropy m := by
    rw [← add_div, div_right_comm, htr_mid, htr_m]
  linarith

/-- **Klein's Inequality Equality Characterization (Section 2.1)**:
`D(ρ ‖ σ) = 0 ↔ ρ = σ`. -/
theorem relEntropy_eq_zero_iff (ρ σ : DensityOp d) :
    relEntropy ρ σ = 0 ↔ ρ = σ := by
  constructor
  · intro h0
    have hsupp : suppSubset ρ σ := by
      by_contra hns
      unfold relEntropy at h0
      rw [if_neg hns] at h0
      exact ENNReal.top_ne_zero h0
    unfold relEntropy at h0
    rw [if_pos hsupp] at h0
    have hle0 : (∑ i : d, ∑ j : d,
        ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j)))) / Real.log 2 ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp h0
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hsum_le0 : ∑ i : d, ∑ j : d,
        ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j))) ≤ 0 := by
      have h := (div_le_iff₀ hlog2).mp hle0
      linarith
    have hcol : ∀ i : d, ∑ j : d, ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 = 1 := by
      intro i
      have hW : (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ))ᴴ *
          (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) = 1 := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (star (σ.eigUnitary : Matrix d d ℂ))ᴴ,
          ← Matrix.star_eq_conjTranspose, star_star, Unitary.coe_mul_star_self σ.eigUnitary,
          Matrix.one_mul, ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self ρ.eigUnitary]
      have h := congr_arg Complex.re (congr_fun (congr_fun hW i) i)
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
        Complex.re_sum, Complex.one_re] at h
      rw [← h]; apply Finset.sum_congr rfl; intro j _
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    have hrow : ∀ j : d, ∑ i : d, ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 = 1 := by
      intro j
      have hW : (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) *
          (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ))ᴴ = 1 := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (ρ.eigUnitary : Matrix d d ℂ),
          ← Matrix.star_eq_conjTranspose, Unitary.coe_mul_star_self ρ.eigUnitary,
          Matrix.one_mul, ← Matrix.star_eq_conjTranspose, star_star, Unitary.coe_star_mul_self σ.eigUnitary]
      have h := congr_arg Complex.re (congr_fun (congr_fun hW j) j)
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
        Complex.re_sum, Complex.one_re] at h
      rw [← h]; apply Finset.sum_congr rfl; intro i _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    have htrρ : ∑ i : d, ρ.eigvals i = 1 := by
      have h := congr_arg Complex.re (ρ.isHermitian.trace_eq_sum_eigenvalues.symm.trans ρ.trace_one)
      simpa [DensityOp.eigvals, Complex.re_sum] using h
    have htrσ : ∑ j : d, σ.eigvals j = 1 := by
      have h := congr_arg Complex.re (σ.isHermitian.trace_eq_sum_eigenvalues.symm.trans σ.trace_one)
      simpa [DensityOp.eigvals, Complex.re_sum] using h
    let term : d → d → ℝ := fun i j ↦
      ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
        (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j)) - (ρ.eigvals i - σ.eigvals j))
    have hterm_nn : ∀ i j, 0 ≤ term i j := by
      intro i j; simp only [term]
      by_cases hρi : ρ.eigvals i = 0
      · rw [hρi]; simp only [zero_mul, zero_sub, neg_neg]
        exact mul_nonneg (sq_nonneg _) (σ.eigvals_nonneg j)
      · by_cases hσj : σ.eigvals j = 0
        · rw [hsupp i j hρi hσj]; simp
        · have hρp : 0 < ρ.eigvals i := lt_of_le_of_ne (ρ.eigvals_nonneg i) (Ne.symm hρi)
          have hσp : 0 < σ.eigvals j := lt_of_le_of_ne (σ.eigvals_nonneg j) (Ne.symm hσj)
          apply mul_nonneg (sq_nonneg _)
          have hlog := Real.log_le_sub_one_of_pos (div_pos hσp hρp)
          rw [Real.log_div (ne_of_gt hσp) (ne_of_gt hρp)] at hlog
          have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hρp)
          have hsimp : ρ.eigvals i * (σ.eigvals j / ρ.eigvals i - 1) = σ.eigvals j - ρ.eigvals i := by
            field_simp [ne_of_gt hρp]
          linarith
    have hsum_term_eq : ∑ i : d, ∑ j : d, term i j =
        ∑ i : d, ∑ j : d,
          ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
            (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j))) := by
      simp only [term, mul_sub, Finset.sum_sub_distrib]
      have hdiff : ∑ i : d, ∑ j : d,
          ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
            (ρ.eigvals i - σ.eigvals j) = 0 := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hcol, one_mul]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, hrow, one_mul, htrρ, htrσ, sub_self]
      rw [hdiff, sub_zero]
    have hsum_zero : ∑ i : d, ∑ j : d, term i j = 0 :=
      le_antisymm (by rw [hsum_term_eq]; exact hsum_le0)
        (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hterm_nn i j)
    have hterm_zero : ∀ i j, term i j = 0 := by
      intro i j
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ hterm_nn a b)).mp
        hsum_zero i (Finset.mem_univ i)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ ↦ hterm_nn i b)).mp hi j (Finset.mem_univ j)
    have hcomm_entry : ∀ i j,
        (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i * (ρ.eigvals i : ℂ) =
        (σ.eigvals j : ℂ) * (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i := by
      intro i j
      by_cases hW : (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i = 0
      · simp [hW]
      · have hWsq : ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 ≠ 0 :=
          pow_ne_zero 2 (norm_ne_zero_iff.mpr hW)
        have h0 := hterm_zero i j
        simp only [term, mul_eq_zero] at h0
        have heq_inner := h0.resolve_left hWsq
        have heig : ρ.eigvals i = σ.eigvals j := by
          by_cases hρi : ρ.eigvals i = 0
          · rw [hρi] at heq_inner; simp only [zero_mul, zero_sub, neg_eq_zero] at heq_inner
            exact heq_inner.symm
          · by_cases hσj : σ.eigvals j = 0
            · exact absurd (hsupp i j hρi hσj) hW
            · have hρp : 0 < ρ.eigvals i := lt_of_le_of_ne (ρ.eigvals_nonneg i) (Ne.symm hρi)
              have hσp : 0 < σ.eigvals j := lt_of_le_of_ne (σ.eigvals_nonneg j) (Ne.symm hσj)
              have hlog_eq : Real.log (σ.eigvals j / ρ.eigvals i) = σ.eigvals j / ρ.eigvals i - 1 := by
                rw [Real.log_div (ne_of_gt hσp) (ne_of_gt hρp)]
                have h1 : ρ.eigvals i * (Real.log (σ.eigvals j) - Real.log (ρ.eigvals i)) =
                    ρ.eigvals i * (σ.eigvals j / ρ.eigvals i - 1) := by
                  have : ρ.eigvals i * (σ.eigvals j / ρ.eigvals i - 1) = σ.eigvals j - ρ.eigvals i := by
                    field_simp [ne_of_gt hρp]
                  linarith
                exact mul_left_cancel₀ (ne_of_gt hρp) h1
              by_contra hne
              have hne1 : σ.eigvals j / ρ.eigvals i ≠ 1 := by
                intro h1; exact hne ((div_eq_one_iff_eq (ne_of_gt hρp)).mp h1).symm
              have hlt := Real.log_lt_sub_one_of_pos (div_pos hσp hρp) hne1
              linarith
        rw [heig, mul_comm]
    have hmat_eq : ρ.mat = σ.mat := by
      set Uρ : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
      set Uσ : Matrix d d ℂ := (σ.eigUnitary : Matrix d d ℂ)
      have hM : (star Uσ * Uρ) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) =
          Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) * (star Uσ * Uρ) := by
        ext j i
        simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply]
        exact hcomm_entry i j
      rw [density_spectral_eq ρ, density_spectral_eq σ]
      calc Uρ * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star Uρ
          = (Uσ * star Uσ) * Uρ * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star Uρ := by
            rw [Unitary.coe_mul_star_self σ.eigUnitary, Matrix.one_mul]
        _ = Uσ * ((star Uσ * Uρ) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals)) * star Uρ := by
            simp only [Matrix.mul_assoc]
        _ = Uσ * (Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) * (star Uσ * Uρ)) * star Uρ := by
            rw [hM]
        _ = Uσ * Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) * star Uσ * (Uρ * star Uρ) := by
            simp only [Matrix.mul_assoc]
        _ = Uσ * Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) * star Uσ := by
            rw [Unitary.coe_mul_star_self ρ.eigUnitary, Matrix.mul_one]
    rcases ρ with ⟨m₁, p₁, t₁⟩
    rcases σ with ⟨m₂, p₂, t₂⟩
    dsimp only at hmat_eq; subst hmat_eq; rfl
  · rintro rfl
    have hsupp : suppSubset ρ ρ := by
      intro i j hi hj
      have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) j) i
      have hne : j ≠ i := fun hji ↦ hi (hji ▸ hj)
      simpa [Matrix.one_apply, hne] using h
    unfold relEntropy
    rw [if_pos hsupp]
    have h0 : (∑ i : d, ∑ j : d,
        ‖(star (ρ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (ρ.eigvals j)))) / Real.log 2 = 0 := by
      rw [div_eq_zero_iff]; left
      apply Finset.sum_eq_zero; intro i _
      apply Finset.sum_eq_zero; intro j _
      by_cases hji : j = i
      · subst hji; simp
      · have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) j) i
        simp only [Matrix.one_apply, hji, ↓reduceIte] at h
        rw [h]; simp
    rw [h0, ENNReal.ofReal_zero]

/-- **QJS Range Characterization (Section 2.1)**: `0 ≤ QJS(ρ, σ) ≤ 1`. -/
theorem qjs_mem_Icc (ρ σ : DensityOp d) :
    0 ≤ qjs ρ σ ∧ qjs ρ σ ≤ 1 := by
  let W : CQChannel d := ⟨fun b ↦ if b = false then ρ else σ⟩
  have h := condEntropy_mem_Icc W
  unfold CQChannel.condEntropy at h
  simp only [W, ↓reduceIte, Bool.true_eq_false] at h
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- **QJS Zero Characterization (Section 2.1)**: `QJS(ρ, σ) = 0 ↔ ρ = σ`. -/
theorem qjs_eq_zero_iff (ρ σ : DensityOp d) :
    qjs ρ σ = 0 ↔ ρ = σ := by
  constructor
  · intro h0
    obtain ⟨hne1, hne2, havg⟩ := qjs_eq_avg_relEntropy ρ σ
    have hnn1 : 0 ≤ (relEntropy ρ (DensityOp.midpoint ρ σ)).toReal := ENNReal.toReal_nonneg
    have hnn2 : 0 ≤ (relEntropy σ (DensityOp.midpoint ρ σ)).toReal := ENNReal.toReal_nonneg
    have hr1 : (relEntropy ρ (DensityOp.midpoint ρ σ)).toReal = 0 := by linarith
    have hr2 : (relEntropy σ (DensityOp.midpoint ρ σ)).toReal = 0 := by linarith
    have heq1 : relEntropy ρ (DensityOp.midpoint ρ σ) = 0 :=
      (ENNReal.toReal_eq_zero_iff _).mp hr1 |>.resolve_right hne1
    have heq2 : relEntropy σ (DensityOp.midpoint ρ σ) = 0 :=
      (ENNReal.toReal_eq_zero_iff _).mp hr2 |>.resolve_right hne2
    have h1 := (relEntropy_eq_zero_iff ρ (DensityOp.midpoint ρ σ)).mp heq1
    have h2 := (relEntropy_eq_zero_iff σ (DensityOp.midpoint ρ σ)).mp heq2
    exact h1.trans h2.symm
  · rintro rfl
    have hm : (DensityOp.midpoint ρ ρ).mat = ρ.mat := by
      ext i j; simp [DensityOp.midpoint, DensityOp.mix]; ring
    unfold qjs
    rw [vonNeumannEntropy_eq_of_mat_eq hm]; ring

/-- **QJS Maximum Characterization (Section 2.1)**: `QJS(ρ, σ) = 1 ↔ ρ σ = 0` (orthogonal supports). -/
theorem qjs_eq_one_iff (ρ σ : DensityOp d) :
    qjs ρ σ = 1 ↔ ρ.mat * σ.mat = 0 := by
  constructor
  · intro h1
    let W : CQChannel d := ⟨fun b ↦ if b = false then ρ else σ⟩
    have hF_le := fidelityParam_le_sqrt_condEntropy W
    unfold CQChannel.fidelityParam CQChannel.condEntropy at hF_le
    simp only [W, ↓reduceIte, Bool.true_eq_false] at hF_le
    rw [h1, sub_self, Real.sqrt_zero] at hF_le
    have hF_nn : 0 ≤ rootFidelity ρ σ := Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _
    have hF0 : rootFidelity ρ σ = 0 := le_antisymm hF_le hF_nn
    set M := ρ.sqrtMat * σ.mat * ρ.sqrtMat
    have hM_psd : M.PosSemidef := posSemidef_sqrt_mul_sqrt ρ σ
    have hM_eig0 : ∀ i : d, hM_psd.isHermitian.eigenvalues i = 0 := by
      intro i
      have hsq0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ Real.sqrt_nonneg _)).mp hF0 i (Finset.mem_univ i)
      exact (Real.sqrt_eq_zero (hM_psd.eigenvalues_nonneg i)).mp hsq0
    have hM0 : M = 0 := by
      have hspec : M = (hM_psd.isHermitian.eigenvectorUnitary : Matrix d d ℂ) *
          Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues) *
          star (hM_psd.isHermitian.eigenvectorUnitary : Matrix d d ℂ) := by
        simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM_psd.isHermitian.spectral_theorem
      rw [hspec]
      have hd0 : Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues) = 0 := by
        ext i j; simp [Matrix.diagonal_apply, hM_eig0]
      rw [hd0, Matrix.mul_zero, Matrix.zero_mul]
    have hprod0 : σ.sqrtMat * ρ.sqrtMat = 0 := by
      have htr0 : ((σ.sqrtMat * ρ.sqrtMat)ᴴ * (σ.sqrtMat * ρ.sqrtMat)).trace = 0 := by
        have heq : (σ.sqrtMat * ρ.sqrtMat)ᴴ * (σ.sqrtMat * ρ.sqrtMat) = M := by
          simp only [M, Matrix.conjTranspose_mul, ρ.sqrtMat_isHermitian.eq, σ.sqrtMat_isHermitian.eq,
            Matrix.mul_assoc, ← Matrix.mul_assoc σ.sqrtMat σ.sqrtMat, σ.sqrtMat_mul_self]
        rw [heq, hM0, Matrix.trace_zero]
      have hsum0 : ∑ i : d, ∑ j : d, ‖(σ.sqrtMat * ρ.sqrtMat) i j‖ ^ 2 = 0 := by
        have hre := congr_arg Complex.re htr0
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Complex.re_sum, Complex.zero_re] at hre
        rw [Finset.sum_comm, ← hre]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      ext i j
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ sq_nonneg _)).mp
        hsum0 i (Finset.mem_univ i)
      have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ ↦ sq_nonneg _)).mp hi j (Finset.mem_univ j)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hj)
    have hprod0' : ρ.sqrtMat * σ.sqrtMat = 0 := by
      have h := congr_arg Matrix.conjTranspose hprod0
      simpa [Matrix.conjTranspose_mul, ρ.sqrtMat_isHermitian.eq, σ.sqrtMat_isHermitian.eq] using h
    calc ρ.mat * σ.mat
        = (ρ.sqrtMat * ρ.sqrtMat) * (σ.sqrtMat * σ.sqrtMat) := by rw [ρ.sqrtMat_mul_self, σ.sqrtMat_mul_self]
      _ = ρ.sqrtMat * (ρ.sqrtMat * σ.sqrtMat) * σ.sqrtMat := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hprod0', Matrix.mul_zero, Matrix.zero_mul]
  · intro horth
    have hsqrt_orth : ρ.sqrtMat * σ.sqrtMat = 0 := by
      have hsq : (ρ.sqrtMat * σ.sqrtMat)ᴴ * (ρ.sqrtMat * σ.sqrtMat) = 0 := by
        have htr : ((ρ.sqrtMat * σ.sqrtMat)ᴴ * (ρ.sqrtMat * σ.sqrtMat)).trace = 0 := by
          have heq : ((ρ.sqrtMat * σ.sqrtMat)ᴴ * (ρ.sqrtMat * σ.sqrtMat)).trace = (ρ.mat * σ.mat).trace := by
            rw [Matrix.conjTranspose_mul, ρ.sqrtMat_isHermitian.eq, σ.sqrtMat_isHermitian.eq,
              Matrix.mul_assoc, ← Matrix.mul_assoc ρ.sqrtMat ρ.sqrtMat, ρ.sqrtMat_mul_self,
              Matrix.trace_mul_cycle, Matrix.mul_assoc, σ.sqrtMat_mul_self]
          rw [heq, horth, Matrix.trace_zero]
        have hpsd := Matrix.posSemidef_conjTranspose_mul_self (ρ.sqrtMat * σ.sqrtMat)
        have heig0 : ∀ i : d, hpsd.isHermitian.eigenvalues i = 0 := by
          have hsum : ∑ i : d, hpsd.isHermitian.eigenvalues i = 0 := by
            have h := congr_arg Complex.re (hpsd.isHermitian.trace_eq_sum_eigenvalues.symm.trans htr)
            simpa [Complex.re_sum] using h
          intro i
          exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ hpsd.eigenvalues_nonneg k)).mp hsum i (Finset.mem_univ i)
        have hspec : (ρ.sqrtMat * σ.sqrtMat)ᴴ * (ρ.sqrtMat * σ.sqrtMat) =
            (hpsd.isHermitian.eigenvectorUnitary : Matrix d d ℂ) *
            Matrix.diagonal (Complex.ofReal ∘ hpsd.isHermitian.eigenvalues) *
            star (hpsd.isHermitian.eigenvectorUnitary : Matrix d d ℂ) := by
          simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hpsd.isHermitian.spectral_theorem
        rw [hspec]
        have hd0 : Matrix.diagonal (Complex.ofReal ∘ hpsd.isHermitian.eigenvalues) = 0 := by
          ext i j; simp [Matrix.diagonal_apply, heig0]
        rw [hd0, Matrix.mul_zero, Matrix.zero_mul]
      have hsum0 : ∑ i : d, ∑ j : d, ‖(ρ.sqrtMat * σ.sqrtMat) i j‖ ^ 2 = 0 := by
        have hre := congr_arg Complex.re (congr_arg Matrix.trace hsq)
        simp only [Matrix.trace_zero, Complex.zero_re, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Complex.re_sum] at hre
        rw [Finset.sum_comm, ← hre]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      ext i j
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ sq_nonneg _)).mp
        hsum0 i (Finset.mem_univ i)
      have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ ↦ sq_nonneg _)).mp hi j (Finset.mem_univ j)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hj)
    have hsqrt_orth' : σ.sqrtMat * ρ.sqrtMat = 0 := by
      have h := congr_arg Matrix.conjTranspose hsqrt_orth
      simpa [Matrix.conjTranspose_mul, ρ.sqrtMat_isHermitian.eq, σ.sqrtMat_isHermitian.eq] using h
    let A : Matrix d (Bool × d) ℂ := Matrix.of fun i p ↦
      ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then ρ.sqrtMat i p.2 else σ.sqrtMat i p.2)
    have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
    have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; push_cast; ring
    have hAAH : A * Aᴴ = (DensityOp.midpoint ρ σ).mat := by
      ext i j
      simp only [A, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
        star_mul', hstar2, DensityOp.midpoint, DensityOp.mix, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul]
      have h0 : ∑ k : d, ((Real.sqrt 2 : ℂ)⁻¹) * ρ.sqrtMat i k * (((Real.sqrt 2 : ℂ)⁻¹) * star (ρ.sqrtMat j k)) =
          (1 / 2 : ℂ) * ρ.mat i j := by
        have h := congr_fun (congr_fun ρ.sqrtMat_mul_self i) j
        rw [← h, Matrix.mul_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        have hh := congr_fun (congr_fun ρ.sqrtMat_isHermitian.eq k) j
        simp only [Matrix.conjTranspose_apply] at hh
        rw [← hh]
        calc ((Real.sqrt 2 : ℂ)⁻¹) * ρ.sqrtMat i k * (((Real.sqrt 2 : ℂ)⁻¹) * ρ.sqrtMat k j)
            = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (ρ.sqrtMat i k * ρ.sqrtMat k j) := by ring
          _ = _ := by rw [hmul2]
      have h1 : ∑ k : d, ((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat i k * (((Real.sqrt 2 : ℂ)⁻¹) * star (σ.sqrtMat j k)) =
          (1 / 2 : ℂ) * σ.mat i j := by
        have h := congr_fun (congr_fun σ.sqrtMat_mul_self i) j
        rw [← h, Matrix.mul_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        have hh := congr_fun (congr_fun σ.sqrtMat_isHermitian.eq k) j
        simp only [Matrix.conjTranspose_apply] at hh
        rw [← hh]
        calc ((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat i k * (((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat k j)
            = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (σ.sqrtMat i k * σ.sqrtMat k j) := by ring
          _ = _ := by rw [hmul2]
      rw [h0, h1]; push_cast; ring
    let B : DensityOp (Bool × d) := DensityOp.midpoint
      (DensityOp.tensor (CQChannel.ketBraBool false) ρ)
      (DensityOp.tensor (CQChannel.ketBraBool true) σ)
    have hAHA : Aᴴ * A = B.mat := by
      ext ⟨a, i⟩ ⟨b, j⟩
      simp only [A, B, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        star_mul', hstar2, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
        CQChannel.ketBraBool, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
        smul_eq_mul]
      cases a <;> cases b <;> simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true,
        and_self, and_false, false_and, one_mul, zero_mul, mul_zero, add_zero, zero_add]
      · have h := congr_fun (congr_fun ρ.sqrtMat_mul_self i) j
        rw [← h, Matrix.mul_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        have hh := congr_fun (congr_fun ρ.sqrtMat_isHermitian.eq i) k
        simp only [Matrix.conjTranspose_apply] at hh; rw [hh]
        calc ((Real.sqrt 2 : ℂ)⁻¹) * ρ.sqrtMat i k * (((Real.sqrt 2 : ℂ)⁻¹) * ρ.sqrtMat k j)
            = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (ρ.sqrtMat i k * ρ.sqrtMat k j) := by ring
          _ = _ := by rw [hmul2]; push_cast; ring
      · have h := congr_fun (congr_fun hsqrt_orth i) j
        simp only [Matrix.mul_apply, Matrix.zero_apply] at h
        have hsum : ∑ k : d, ((Real.sqrt 2 : ℂ)⁻¹) * star (ρ.sqrtMat k i) *
            (((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat k j) =
            (1 / 2 : ℂ) * ∑ k : d, ρ.sqrtMat i k * σ.sqrtMat k j := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
          have hh := congr_fun (congr_fun ρ.sqrtMat_isHermitian.eq i) k
          simp only [Matrix.conjTranspose_apply] at hh; rw [hh]
          calc ((Real.sqrt 2 : ℂ)⁻¹) * ρ.sqrtMat i k * (((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat k j)
              = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (ρ.sqrtMat i k * σ.sqrtMat k j) := by ring
            _ = _ := by rw [hmul2]
        rw [hsum, h, mul_zero]
      · have h := congr_fun (congr_fun hsqrt_orth' i) j
        simp only [Matrix.mul_apply, Matrix.zero_apply] at h
        have hsum : ∑ k : d, ((Real.sqrt 2 : ℂ)⁻¹) * star (σ.sqrtMat k i) *
            (((Real.sqrt 2 : ℂ)⁻¹) * ρ.sqrtMat k j) =
            (1 / 2 : ℂ) * ∑ k : d, σ.sqrtMat i k * ρ.sqrtMat k j := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
          have hh := congr_fun (congr_fun σ.sqrtMat_isHermitian.eq i) k
          simp only [Matrix.conjTranspose_apply] at hh; rw [hh]
          calc ((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat i k * (((Real.sqrt 2 : ℂ)⁻¹) * ρ.sqrtMat k j)
              = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (σ.sqrtMat i k * ρ.sqrtMat k j) := by ring
            _ = _ := by rw [hmul2]
        rw [hsum, h, mul_zero]
      · have h := congr_fun (congr_fun σ.sqrtMat_mul_self i) j
        rw [← h, Matrix.mul_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        have hh := congr_fun (congr_fun σ.sqrtMat_isHermitian.eq i) k
        simp only [Matrix.conjTranspose_apply] at hh; rw [hh]
        calc ((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat i k * (((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat k j)
            = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (σ.sqrtMat i k * σ.sqrtMat k j) := by ring
          _ = _ := by rw [hmul2]; push_cast; ring
    have hS_eq : vonNeumannEntropy (DensityOp.midpoint ρ σ) = vonNeumannEntropy B := by
      unfold vonNeumannEntropy DensityOp.eigvals
      congr 1
      have hcp := charpoly_mul_conjTranspose_eq A
      rw [hAAH, hAHA] at hcp
      exact spectral_sum_eq_of_charpoly_mul_X_pow (DensityOp.midpoint ρ σ).isHermitian B.isHermitian
        hcp (by simp [Real.negMulLog])
    unfold qjs
    rw [hS_eq, vonNeumannEntropy_block_midpoint]
    ring

/-- Block-diagonal classical–quantum density operator `⊕_x p_x ρ_x` on `ι × d`. -/
noncomputable def blockDiagState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp_nn : ∀ x, 0 ≤ p x) (hp_sum : ∑ x, p x = 1)
    (ρ : ι → DensityOp d) : DensityOp (ι × d) where
  mat := Matrix.of fun a b ↦ if a.1 = b.1 then (p a.1 : ℂ) * (ρ a.1).mat a.2 b.2 else 0
  posSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · ext ⟨x₁, i₁⟩ ⟨x₂, i₂⟩
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
      by_cases h : x₂ = x₁
      · subst h
        have hh := congr_fun (congr_fun (ρ x₂).isHermitian.eq i₁) i₂
        simp only [Matrix.conjTranspose_apply] at hh
        simp [Complex.star_def, Complex.conj_ofReal, hh]
      · simp [h, Ne.symm h]
    · intro v
      have hsum : star v ⬝ᵥ ((Matrix.of fun a b : ι × d ↦
          if a.1 = b.1 then (p a.1 : ℂ) * (ρ a.1).mat a.2 b.2 else 0) *ᵥ v) =
          ∑ x : ι, (p x : ℂ) * (star (fun i ↦ v (x, i)) ⬝ᵥ ((ρ x).mat *ᵥ fun i ↦ v (x, i))) := by
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_eq_single x]
        · simp only [↓reduceIte, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
        · intro y _ hne; apply Finset.sum_eq_zero; intro j _; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ x) h
      rw [hsum]
      exact Finset.sum_nonneg fun x _ ↦
        mul_nonneg (by exact_mod_cast hp_nn x)
          ((Matrix.posSemidef_iff_dotProduct_mulVec.mp (ρ x).posSemidef).2 (fun i ↦ v (x, i)))
  trace_one := by
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type, ↓reduceIte]
    have h1 : ∀ x : ι, ∑ i : d, (p x : ℂ) * (ρ x).mat i i = (p x : ℂ) := fun x ↦ by
      rw [← Finset.mul_sum]
      have htr : ∑ i : d, (ρ x).mat i i = 1 := (ρ x).trace_one
      rw [htr, mul_one]
    simp_rw [h1, ← Complex.ofReal_sum, hp_sum, Complex.ofReal_one]

/-- **General Finite-Distribution Block-Diagonal Additivity of Root Fidelity (Section 2.1)**:
For any finite probability distribution `{p_x}` and families of density operators `{ρ_x}, {σ_x}`,
`F(⊕_x p_x ρ_x, ⊕_x p_x σ_x) = ∑_x p_x F(ρ_x, σ_x)`. -/
theorem rootFidelity_block_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp_nn : ∀ x, 0 ≤ p x) (hp_sum : ∑ x, p x = 1)
    (ρ σ : ι → DensityOp d) :
    rootFidelity (blockDiagState p hp_nn hp_sum ρ) (blockDiagState p hp_nn hp_sum σ) =
      ∑ x : ι, p x * rootFidelity (ρ x) (σ x) := by
  set R := blockDiagState p hp_nn hp_sum ρ
  set S := blockDiagState p hp_nn hp_sum σ
  let lam : ι × d → ℝ := fun a ↦
    p a.1 ^ 2 * (posSemidef_sqrt_mul_sqrt (ρ a.1) (σ a.1)).isHermitian.eigenvalues a.2
  have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext a; simp
  have hRS_eq : R.mat * S.mat =
      Matrix.blockDiagonal (fun x : ι ↦ ((p x ^ 2 : ℝ) : ℂ) • ((ρ x).mat * (σ x).mat)) := by
    ext ⟨x₁, i₁⟩ ⟨x₂, i₂⟩
    simp only [R, S, blockDiagState, Matrix.mul_apply, Matrix.of_apply, Matrix.blockDiagonal_apply,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
    by_cases hx : x₁ = x₂
    · subst hx
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single x₁]
      · simp only [↓reduceIte, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; push_cast; ring
      · intro y _ hne; apply Finset.sum_eq_zero; intro k _; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ x₁) h
    · simp only [hx, ↓reduceIte]
      apply Finset.sum_eq_zero; intro y _
      apply Finset.sum_eq_zero; intro k _
      by_cases hy : x₁ = y
      · subst hy; simp [hx]
      · simp [hy]
  have hcp_RS : (R.sqrtMat * S.mat * R.sqrtMat).charpoly =
      (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
    have hcp1 : (R.sqrtMat * S.mat * R.sqrtMat).charpoly = (R.mat * S.mat).charpoly := by
      have h := Matrix.charpoly_mul_comm R.sqrtMat (S.mat * R.sqrtMat)
      rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, R.sqrtMat_mul_self]
      exact Matrix.charpoly_mul_comm S.mat R.mat
    rw [hcp1, hRS_eq, Matrix.charpoly_blockDiagonal, charpoly_diagonal_complex, Fintype.prod_prod_type]
    apply Finset.prod_congr rfl; intro x _
    have hx_cp : (((p x ^ 2 : ℝ) : ℂ) • ((ρ x).mat * (σ x).mat)).charpoly =
        (((p x ^ 2 : ℝ) : ℂ) • ((ρ x).sqrtMat * (σ x).mat * (ρ x).sqrtMat)).charpoly := by
      have h1 : ((p x ^ 2 : ℝ) : ℂ) • ((ρ x).mat * (σ x).mat) =
          (((p x ^ 2 : ℝ) : ℂ) • (ρ x).sqrtMat) * ((ρ x).sqrtMat * (σ x).mat) := by
        simp only [Matrix.smul_mul, ← Matrix.mul_assoc, (ρ x).sqrtMat_mul_self]
      have h2 : ((p x ^ 2 : ℝ) : ℂ) • ((ρ x).sqrtMat * (σ x).mat * (ρ x).sqrtMat) =
          ((ρ x).sqrtMat * (σ x).mat) * (((p x ^ 2 : ℝ) : ℂ) • (ρ x).sqrtMat) := by
        simp only [Matrix.mul_smul, Matrix.mul_assoc]
      rw [h1, h2]
      exact Matrix.charpoly_mul_comm _ _
    rw [hx_cp]
    set A := (ρ x).sqrtMat * (σ x).mat * (ρ x).sqrtMat
    have hA := (posSemidef_sqrt_mul_sqrt (ρ x) (σ x)).isHermitian
    set U : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
    have hspec : ((p x ^ 2 : ℝ) : ℂ) • A =
        U * Matrix.diagonal (fun i ↦ ((lam (x, i) : ℝ) : ℂ)) * star U := by
      have hs : A = U * Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) * star U := by
        simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
      conv_lhs => rw [hs]
      simp only [Matrix.smul_mul, Matrix.mul_smul]
      congr 2; ext i j; simp only [Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply,
        smul_eq_mul, lam]
      split_ifs with hij
      · subst hij; rw [← Complex.ofReal_mul]
      · simp
    rw [hspec, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self hA.eigenvectorUnitary,
      Matrix.one_mul, charpoly_diagonal_complex]
    rfl
  unfold rootFidelity
  have hsum := spectral_sum_eq_of_charpoly_mul_X_pow
    (posSemidef_sqrt_mul_sqrt R S).isHermitian hD_herm (by rw [hcp_RS]) (by simp)
  rw [hsum, spectral_sum_diagonal lam hD_herm (by simp), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  simp only [lam]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hp_nn x)]

end Section2Characterizations

theorem relEntropy_dephaseState_ne_top {d : Type*} [Fintype d] [DecidableEq d]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Ψ : DensityOp (Bool × d)) :
    relEntropy (dephaseState p hp0 hp1 Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) ≠ ⊤ := by
  rw [relEntropy_dephaseState_eq p hp0 hp1 Ψ]
  exact ENNReal.ofReal_ne_top

/-- **Lemma 4.1 Part 4 (Umegaki Relative-Entropy Form)**:
`D((Z_0 ⊗ id)(Ψ₁) ‖ (Z_{1/2} ⊗ id)(Ψ₁))` is finite and equals `1 - QJS(ρ₀, ρ₁)`. -/
theorem lemma_4_1_gram_dephasing_relEntropy {d : Type*} [Fintype d] [DecidableEq d]
    (ρ₀ ρ₁ : DensityOp d) :
    relEntropy (dephaseState 0 le_rfl (by norm_num) (gramState ρ₀ ρ₁))
      (dephaseState (1 / 2) (by norm_num) (by norm_num) (gramState ρ₀ ρ₁)) ≠ ⊤ ∧
    (relEntropy (dephaseState 0 le_rfl (by norm_num) (gramState ρ₀ ρ₁))
      (dephaseState (1 / 2) (by norm_num) (by norm_num) (gramState ρ₀ ρ₁))).toReal =
      1 - qjs ρ₀ ρ₁ := by
  refine ⟨relEntropy_dephaseState_ne_top 0 le_rfl (by norm_num) (gramState ρ₀ ρ₁), ?_⟩
  rw [relEntropy_dephaseState_toReal_eq]
  exact (lemma_4_1_gram_dephasing ρ₀ ρ₁ (fun _ : Unit ↦ (1 : ℂ)) (fun _ : Unit ↦ (1 : ℂ))
    (by simp) (by simp)).2.2.2

/-- Explicit-finiteness Theorem 1.3 (Nonlinear Dephasing SDPI, Umegaki Relative-Entropy Form). -/
theorem theorem_1_3_dephasing_sdpi_relEntropy_finite {d : Type*} [Fintype d] [DecidableEq d]
    (Ψ : DensityOp (Bool × d)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) ≠ ⊤ ∧
    relEntropy (dephaseState 0 le_rfl (by norm_num) Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) ≠ ⊤ ∧
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal ≤
      1 - h2 (binConv (h2Inv (1 -
        (relEntropy (dephaseState 0 le_rfl (by norm_num) Ψ)
          (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal)) p) :=
  ⟨relEntropy_dephaseState_ne_top p hp0 (le_trans hp1 (by norm_num)) Ψ,
   relEntropy_dephaseState_ne_top 0 le_rfl (by norm_num) Ψ,
   theorem_1_3_dephasing_sdpi_relEntropy Ψ hp0 hp1⟩

/-- Explicit-finiteness Theorem 1.3 (Equatorial Equality, Umegaki Relative-Entropy Form). -/
theorem theorem_1_3_equatorial_equality_relEntropy_finite {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1))
      (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1)) ≠ ⊤ ∧
    relEntropy (dephaseState 0 le_rfl (by norm_num) (equatorialState x hx0 hx1))
      (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1)) ≠ ⊤ ∧
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1))
      (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal =
      1 - h2 (binConv (h2Inv (1 -
        (relEntropy (dephaseState 0 le_rfl (by norm_num) (equatorialState x hx0 hx1))
          (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal)) p) :=
  ⟨relEntropy_dephaseState_ne_top p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1),
   relEntropy_dephaseState_ne_top 0 le_rfl (by norm_num) (equatorialState x hx0 hx1),
   theorem_1_3_equatorial_equality_relEntropy hx0 hx1 hp0 hp1⟩

end PolarCodes
