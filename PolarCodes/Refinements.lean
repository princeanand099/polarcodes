/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.QuantumChannels
import PolarCodes.QJJS
import PolarCodes.DephasingSDPI
import PolarCodes.MrsGerber

/-!
# Refinements of Intermediate Propositions and Theorems

This module closes the intermediate formalization refinements matching the manuscript:
1. **Equal-Support Lemma 3.2** (`lemma_3_2_hockeyStick_measure_equalSupport`): Extends the
   simultaneous hockey-stick probability measure representation from strictly positive definite
   states to all density-operator pairs with equal support (`suppSubset ρ σ ∧ suppSubset σ ρ`).
2. **Proposition 3.3 Classical Equality** (`prop_3_3_qjjs_classical_equality`): Proves that
   every symmetric classical binary pair `diag((1+x)/2, (1-x)/2)` vs `diag((1-x)/2, (1+x)/2)`
   attains equality in Proposition 3.3 for all `x ∈ [0, 1]` (including `x = 1`, where both
   sides equal `⊤`).
3. **Relative-Entropy Theorem 1.3** (`relEntropy_dephaseState_eq`,
   `theorem_1_3_dephasing_sdpi_relEntropy`, `theorem_1_3_equatorial_equality_relEntropy`):
   Establishes `supp(Ψ_p) ⊆ supp(Ψ_{1/2})` and `D(Ψ_p ‖ Ψ_{1/2}) = S(Ψ_{1/2}) - S(Ψ_p)`
   directly via Umegaki relative entropy, stating Theorem 1.3 and equatorial equality in terms
   of `(relEntropy (dephaseState p ...) (dephaseState (1/2) ...)).toReal`.
-/

open Matrix BigOperators Real MeasureTheory Set Filter
open scoped ComplexOrder ENNReal Topology

namespace PolarCodes

universe u

/-! ### Helper Lemmas on Support, Diagonalization, and Relative Entropy -/

section Helpers

variable {d : Type*} [Fintype d] [DecidableEq d]

lemma density_spectral_eq (ρ : DensityOp d) :
    ρ.mat = (ρ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *
      star (ρ.eigUnitary : Matrix d d ℂ) := by
  simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
    Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem

private lemma posSemidef_mulVec_eq_zero_of_dot {A : Matrix d d ℂ} (hA : A.PosSemidef)
    {v : d → ℂ} (hv : star v ⬝ᵥ (A *ᵥ v) = 0) : A *ᵥ v = 0 := by
  have hspec : A = (hA.isHermitian.eigenvectorUnitary : Matrix d d ℂ) *
      Matrix.diagonal (Complex.ofReal ∘ hA.isHermitian.eigenvalues) *
      star (hA.isHermitian.eigenvectorUnitary : Matrix d d ℂ) := by
    simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.isHermitian.spectral_theorem
  set U := (hA.isHermitian.eigenvectorUnitary : Matrix d d ℂ)
  set w := star U *ᵥ v
  have hsum : ∑ j : d, hA.isHermitian.eigenvalues j * ‖w j‖ ^ 2 = 0 := by
    have hre : (star v ⬝ᵥ (A *ᵥ v)).re = ∑ j : d, hA.isHermitian.eigenvalues j * ‖w j‖ ^ 2 := by
      rw [hspec]
      have hassoc : (U * Matrix.diagonal (Complex.ofReal ∘ hA.isHermitian.eigenvalues) * star U) *ᵥ v =
          U *ᵥ (Matrix.diagonal (Complex.ofReal ∘ hA.isHermitian.eigenvalues) *ᵥ w) := by
        simp [w, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [hassoc, Matrix.dotProduct_mulVec]
      have hvec : star v ᵥ* U = star w := by
        ext j; simp [w, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.star_apply, mul_comm]
      rw [hvec, dotProduct]
      simp only [Matrix.mulVec_diagonal, Function.comp_apply, Complex.re_sum]
      apply Finset.sum_congr rfl; intro j _
      have hsq : star (w j) * w j = ((‖w j‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc (star (w j) * ((hA.isHermitian.eigenvalues j : ℂ) * w j)).re
          = (((hA.isHermitian.eigenvalues j : ℂ) * (star (w j) * w j))).re := by ring_nf
        _ = (((hA.isHermitian.eigenvalues j * ‖w j‖ ^ 2 : ℝ) : ℂ)).re := by rw [hsq]; push_cast; ring_nf
        _ = hA.isHermitian.eigenvalues j * ‖w j‖ ^ 2 := Complex.ofReal_re _
    rw [← hre, hv, Complex.zero_re]
  rw [hspec]
  have hassoc : (U * Matrix.diagonal (Complex.ofReal ∘ hA.isHermitian.eigenvalues) * star U) *ᵥ v =
      U *ᵥ (Matrix.diagonal (Complex.ofReal ∘ hA.isHermitian.eigenvalues) *ᵥ w) := by
    simp [w, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hassoc]
  have hdiag0 : Matrix.diagonal (Complex.ofReal ∘ hA.isHermitian.eigenvalues) *ᵥ w = 0 := by
    ext j
    simp only [Matrix.mulVec_diagonal, Function.comp_apply, Pi.zero_apply]
    have hterm : hA.isHermitian.eigenvalues j * ‖w j‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦
        mul_nonneg (hA.eigenvalues_nonneg k) (sq_nonneg _))).mp hsum j (Finset.mem_univ j)
    rcases mul_eq_zero.mp hterm with h0 | h0
    · simp [h0]
    · simp [norm_eq_zero.mp (sq_eq_zero_iff.mp h0)]
  rw [hdiag0, Matrix.mulVec_zero]

private lemma suppSubset_ker_aux {ρ σ : DensityOp d} (hsupp : suppSubset ρ σ)
    {v : d → ℂ} (hv : σ.mat *ᵥ v = 0) : ρ.mat *ᵥ v = 0 := by
  have h1 : star v ⬝ᵥ (σ.mat *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
  have hspec_σ := density_spectral_eq σ
  set w := star (σ.eigUnitary : Matrix d d ℂ) *ᵥ v
  have hsum_σ : ∑ j : d, σ.eigvals j * ‖w j‖ ^ 2 = 0 := by
    have hre : (star v ⬝ᵥ (σ.mat *ᵥ v)).re = ∑ j : d, σ.eigvals j * ‖w j‖ ^ 2 := by
      rw [hspec_σ]
      have hassoc : ((σ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) *
          star (σ.eigUnitary : Matrix d d ℂ)) *ᵥ v =
          (σ.eigUnitary : Matrix d d ℂ) *ᵥ (Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) *ᵥ w) := by
        simp [w, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [hassoc, Matrix.dotProduct_mulVec]
      have hvec : star v ᵥ* (σ.eigUnitary : Matrix d d ℂ) = star w := by
        ext j; simp [w, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.star_apply, mul_comm]
      rw [hvec, dotProduct]
      simp only [Matrix.mulVec_diagonal, Function.comp_apply, Complex.re_sum]
      apply Finset.sum_congr rfl; intro j _
      have hsq : star (w j) * w j = ((‖w j‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc (star (w j) * ((σ.eigvals j : ℂ) * w j)).re
          = (((σ.eigvals j : ℂ) * (star (w j) * w j))).re := by ring_nf
        _ = (((σ.eigvals j * ‖w j‖ ^ 2 : ℝ) : ℂ)).re := by rw [hsq]; push_cast; ring_nf
        _ = σ.eigvals j * ‖w j‖ ^ 2 := Complex.ofReal_re _
    rw [← hre, h1, Complex.zero_re]
  have hw_zero : ∀ j : d, σ.eigvals j ≠ 0 → w j = 0 := by
    intro j hj
    have hterm : σ.eigvals j * ‖w j‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦
        mul_nonneg (σ.eigvals_nonneg k) (sq_nonneg _))).mp hsum_σ j (Finset.mem_univ j)
    rcases mul_eq_zero.mp hterm with h0 | h0
    · exact absurd h0 hj
    · exact norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
  have hsum_ρ : star v ⬝ᵥ (ρ.mat *ᵥ v) = 0 := by
    have hspec_ρ := density_spectral_eq ρ
    set u := star (ρ.eigUnitary : Matrix d d ℂ) *ᵥ v
    have hu_expr : ∀ i : d, u i = ∑ j : d,
        ((star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ)) i j) * w j := by
      intro i
      have hUσ : (σ.eigUnitary : Matrix d d ℂ) * star (σ.eigUnitary : Matrix d d ℂ) = 1 :=
        Unitary.coe_mul_star_self σ.eigUnitary
      have hv_eq : v = (σ.eigUnitary : Matrix d d ℂ) *ᵥ w := by
        simp [w, Matrix.mulVec_mulVec, hUσ]
      calc u i = (star (ρ.eigUnitary : Matrix d d ℂ) *ᵥ ((σ.eigUnitary : Matrix d d ℂ) *ᵥ w)) i := by
              rw [← hv_eq]
        _ = ((star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ)) *ᵥ w) i := by
              rw [Matrix.mulVec_mulVec]
        _ = _ := rfl
    have hρu : ∀ i : d, ρ.eigvals i ≠ 0 → u i = 0 := by
      intro i hi
      rw [hu_expr i]
      apply Finset.sum_eq_zero; intro j _
      by_cases hj : σ.eigvals j = 0
      · have hW0 : (star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ)) i j = 0 := by
          have h := hsupp i j hi hj
          have hst : (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i =
              star ((star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ)) i j) := by
            simp [Matrix.mul_apply, Matrix.star_apply, mul_comm]
          rw [hst] at h
          exact star_eq_zero.mp h
        rw [hW0, zero_mul]
      · rw [hw_zero j hj, mul_zero]
    rw [hspec_ρ]
    have hassoc : ((ρ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *
        star (ρ.eigUnitary : Matrix d d ℂ)) *ᵥ v =
        (ρ.eigUnitary : Matrix d d ℂ) *ᵥ (Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *ᵥ u) := by
      simp [u, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hassoc, Matrix.dotProduct_mulVec]
    have hvec : star v ᵥ* (ρ.eigUnitary : Matrix d d ℂ) = star u := by
      ext i; simp [u, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.star_apply, mul_comm]
    rw [hvec, dotProduct]
    apply Finset.sum_eq_zero; intro i _
    simp only [Matrix.mulVec_diagonal, Function.comp_apply]
    by_cases hi : ρ.eigvals i = 0
    · simp [hi]
    · simp [hρu i hi]
  exact posSemidef_mulVec_eq_zero_of_dot ρ.posSemidef hsum_ρ

private lemma relEntropy_eq_trace_log {α : Type*} [Fintype α] [DecidableEq α]
    (A B : DensityOp α) (hsupp : suppSubset A B) :
    let L_B : Matrix α α ℂ :=
      (B.eigUnitary : Matrix α α ℂ) *
      Matrix.diagonal (fun j ↦ if B.eigvals j = 0 then (0 : ℂ) else (Real.log (B.eigvals j) : ℂ)) *
      star (B.eigUnitary : Matrix α α ℂ)
    relEntropy A B = ENNReal.ofReal (-vonNeumannEntropy A - (A.mat * L_B).trace.re / Real.log 2) := by
  intro L_B
  unfold relEntropy
  rw [if_pos hsupp]
  congr 1
  set W : Matrix α α ℂ := star (B.eigUnitary : Matrix α α ℂ) * (A.eigUnitary : Matrix α α ℂ)
  have hW_col : ∀ i : α, ∑ j : α, ‖W j i‖ ^ 2 = 1 := by
    intro i
    have hWW : star W * W = 1 := by
      simp only [W, star_mul, star_star, Matrix.mul_assoc]
      have h1 : (B.eigUnitary : Matrix α α ℂ) * star (B.eigUnitary : Matrix α α ℂ) = 1 :=
        Unitary.coe_mul_star_self B.eigUnitary
      have h2 : star (A.eigUnitary : Matrix α α ℂ) * (A.eigUnitary : Matrix α α ℂ) = 1 :=
        Unitary.coe_star_mul_self A.eigUnitary
      rw [← Matrix.mul_assoc (B.eigUnitary : Matrix α α ℂ), h1, Matrix.one_mul, h2]
    have hdiag := congr_fun (congr_fun hWW i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hdiag
    have hre := congr_arg Complex.re hdiag
    simp only [Complex.one_re, Complex.re_sum] at hre
    rw [← hre]
    apply Finset.sum_congr rfl; intro j _
    have hsq : star (W j i) * W j i = ((‖W j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hsq, Complex.ofReal_re]
  have hsplit : ∑ i : α, ∑ j : α,
      (‖W j i‖ ^ 2 * (A.eigvals i * (Real.log (A.eigvals i) - Real.log (B.eigvals j)))) =
      (∑ i : α, A.eigvals i * Real.log (A.eigvals i)) -
      (∑ i : α, ∑ j : α, A.eigvals i * Real.log (B.eigvals j) * ‖W j i‖ ^ 2) := by
    have hrew : ∀ i j, ‖W j i‖ ^ 2 * (A.eigvals i * (Real.log (A.eigvals i) - Real.log (B.eigvals j))) =
        A.eigvals i * Real.log (A.eigvals i) * ‖W j i‖ ^ 2 - A.eigvals i * Real.log (B.eigvals j) * ‖W j i‖ ^ 2 := by
      intro i j; ring
    simp_rw [hrew, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.mul_sum, hW_col i, mul_one]
  have hS : (∑ i : α, A.eigvals i * Real.log (A.eigvals i)) / Real.log 2 = -vonNeumannEntropy A := by
    unfold vonNeumannEntropy
    rw [← neg_div, ← Finset.sum_neg_distrib]
    congr 1; apply Finset.sum_congr rfl; intro i _
    simp [Real.negMulLog]
  have hcross : (A.mat * L_B).trace.re =
      ∑ i : α, ∑ j : α, A.eigvals i * Real.log (B.eigvals j) * ‖W j i‖ ^ 2 := by
    have hspec_A := density_spectral_eq A
    let dB : α → ℂ := fun j ↦ if B.eigvals j = 0 then 0 else (Real.log (B.eigvals j) : ℂ)
    have htr : (A.mat * L_B).trace =
        (Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * (star W * Matrix.diagonal dB * W)).trace := by
      rw [hspec_A]
      have h1 : ((A.eigUnitary : Matrix α α ℂ) * Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *
          star (A.eigUnitary : Matrix α α ℂ)) * L_B =
          (A.eigUnitary : Matrix α α ℂ) * (Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *
          (star (A.eigUnitary : Matrix α α ℂ) * L_B)) := by simp [Matrix.mul_assoc]
      rw [h1, Matrix.trace_mul_comm]
      have h2 : Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *
          (star (A.eigUnitary : Matrix α α ℂ) * L_B) * (A.eigUnitary : Matrix α α ℂ) =
          Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *
          (star W * Matrix.diagonal dB * W) := by
        simp only [L_B, W, dB, star_mul, star_star, Matrix.mul_assoc]
      rw [h2]
    rw [htr, Matrix.trace]
    simp only [Matrix.diag_apply, Complex.re_sum, Matrix.mul_apply, Matrix.diagonal_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Function.comp_apply]
    apply Finset.sum_congr rfl; intro i _
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl; intro j _
    simp only [Matrix.star_apply, dB]
    have hsq : star (W j i) * W j i = ((‖W j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    by_cases hj : B.eigvals j = 0
    · simp [hj, Real.log_zero]
    · simp only [hj, ↓reduceIte]
      have hcalc : (A.eigvals i : ℂ) * (star (W j i) * (Real.log (B.eigvals j) : ℂ) * W j i) =
          ((A.eigvals i * Real.log (B.eigvals j) * ‖W j i‖ ^ 2 : ℝ) : ℂ) := by
        calc _ = (A.eigvals i : ℂ) * (Real.log (B.eigvals j) : ℂ) * (star (W j i) * W j i) := by ring
          _ = _ := by rw [hsq]; push_cast; ring
      rw [hcalc, Complex.ofReal_re]
  rw [hsplit, sub_div, hS, hcross]

/-- Functional calculus intertwining under an isometric embedding `A = V A' Vᴴ` (`Vᴴ V = I`). -/
private lemma isom_func_eq {d d' : Type*} [Fintype d] [DecidableEq d]
    [Fintype d'] [DecidableEq d']
    (V : Matrix d d' ℂ) (hVHV : Vᴴ * V = 1)
    (A : DensityOp d) (A' : DensityOp d') (hA : V * A'.mat * Vᴴ = A.mat)
    (f : ℝ → ℂ) (hf0 : f 0 = 0) :
    (A.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun i ↦ f (A.eigvals i)) *
      star (A.eigUnitary : Matrix d d ℂ) =
    V * ((A'.eigUnitary : Matrix d' d' ℂ) * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) *
      star (A'.eigUnitary : Matrix d' d' ℂ)) * Vᴴ := by
  set Q : Matrix d d' ℂ := star (A.eigUnitary : Matrix d d ℂ) * V * (A'.eigUnitary : Matrix d' d' ℂ)
  have hQ_intertwine : ∀ i k, (A.eigvals i : ℂ) * Q i k = Q i k * (A'.eigvals k : ℂ) := by
    intro i k
    have h1 : Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * Q =
        Q * Matrix.diagonal (Complex.ofReal ∘ A'.eigvals) := by
      have hspecA := density_spectral_eq A
      have hspecA' := density_spectral_eq A'
      have hAV : A.mat * V = V * A'.mat := by
        rw [← hA]; calc (V * A'.mat * Vᴴ) * V = V * A'.mat * (Vᴴ * V) := by simp [Matrix.mul_assoc]
          _ = V * A'.mat := by rw [hVHV, Matrix.mul_one]
      have hUA_l : star (A.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ) = 1 :=
        Unitary.coe_star_mul_self A.eigUnitary
      have hUA'_l : star (A'.eigUnitary : Matrix d' d' ℂ) * (A'.eigUnitary : Matrix d' d' ℂ) = 1 :=
        Unitary.coe_star_mul_self A'.eigUnitary
      calc Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * Q
          = (star (A.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) *
            Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *
            (star (A.eigUnitary : Matrix d d ℂ) * V * (A'.eigUnitary : Matrix d' d' ℂ)) := by
              rw [hUA_l, Matrix.one_mul]
        _ = star (A.eigUnitary : Matrix d d ℂ) * (A.mat * V) * (A'.eigUnitary : Matrix d' d' ℂ) := by
              rw [hspecA]; simp [Matrix.mul_assoc]
        _ = star (A.eigUnitary : Matrix d d ℂ) * (V * A'.mat) * (A'.eigUnitary : Matrix d' d' ℂ) := by
              rw [hAV]
        _ = Q * Matrix.diagonal (Complex.ofReal ∘ A'.eigvals) *
            (star (A'.eigUnitary : Matrix d' d' ℂ) * (A'.eigUnitary : Matrix d' d' ℂ)) := by
              rw [hspecA']; simp [Q, Matrix.mul_assoc]
        _ = Q * Matrix.diagonal (Complex.ofReal ∘ A'.eigvals) := by rw [hUA'_l, Matrix.mul_one]
    have := congr_fun (congr_fun h1 i) k
    simpa [Matrix.mul_apply, Matrix.diagonal_apply] using this
  have hQ_zero : ∀ i k, A.eigvals i ≠ A'.eigvals k → Q i k = 0 := by
    intro i k hne
    have hsub : ((A.eigvals i - A'.eigvals k : ℝ) : ℂ) * Q i k = 0 := by
      push_cast; linear_combination hQ_intertwine i k
    rcases mul_eq_zero.mp hsub with h0 | h0
    · exact absurd (sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h0)) hne
    · exact h0
  have hQQ : Q * Qᴴ = star (A.eigUnitary : Matrix d d ℂ) * (V * Vᴴ) * (A.eigUnitary : Matrix d d ℂ) := by
    have h1 : (A'.eigUnitary : Matrix d' d' ℂ) * (A'.eigUnitary : Matrix d' d' ℂ)ᴴ = 1 :=
      Unitary.coe_mul_star_self A'.eigUnitary
    calc Q * Qᴴ
        = star (A.eigUnitary : Matrix d d ℂ) * V *
          ((A'.eigUnitary : Matrix d' d' ℂ) * (A'.eigUnitary : Matrix d' d' ℂ)ᴴ) *
          Vᴴ * (A.eigUnitary : Matrix d d ℂ) := by
            simp [Q, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]; simp [Matrix.mul_assoc]
  have hQQ_diag : Matrix.diagonal (fun i ↦ f (A.eigvals i)) * (Q * Qᴴ) =
      Matrix.diagonal (fun i ↦ f (A.eigvals i)) := by
    have hVV_A : (V * Vᴴ) * A.mat = A.mat := by
      rw [← hA]; calc (V * Vᴴ) * (V * A'.mat * Vᴴ) = V * (Vᴴ * V) * A'.mat * Vᴴ := by simp [Matrix.mul_assoc]
        _ = V * A'.mat * Vᴴ := by rw [hVHV, Matrix.mul_one]
    have hQQ_A : (Q * Qᴴ) * Matrix.diagonal (Complex.ofReal ∘ A.eigvals) =
        Matrix.diagonal (Complex.ofReal ∘ A.eigvals) := by
      rw [hQQ]
      have hspecA := density_spectral_eq A
      have hUA_l : star (A.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ) = 1 :=
        Unitary.coe_star_mul_self A.eigUnitary
      have hUA_r : (A.eigUnitary : Matrix d d ℂ) * star (A.eigUnitary : Matrix d d ℂ) = 1 :=
        Unitary.coe_mul_star_self A.eigUnitary
      calc star (A.eigUnitary : Matrix d d ℂ) * (V * Vᴴ) * (A.eigUnitary : Matrix d d ℂ) *
            Matrix.diagonal (Complex.ofReal ∘ A.eigvals)
          = star (A.eigUnitary : Matrix d d ℂ) * ((V * Vᴴ) * A.mat) * (A.eigUnitary : Matrix d d ℂ) := by
              rw [hspecA]; simp only [Matrix.mul_assoc]
              rw [← Matrix.mul_assoc (star (A.eigUnitary : Matrix d d ℂ)) (A.eigUnitary : Matrix d d ℂ),
                  hUA_l, Matrix.one_mul]
        _ = star (A.eigUnitary : Matrix d d ℂ) * A.mat * (A.eigUnitary : Matrix d d ℂ) := by rw [hVV_A]
        _ = Matrix.diagonal (Complex.ofReal ∘ A.eigvals) := by
              rw [hspecA]; simp only [Matrix.mul_assoc]
              rw [← Matrix.mul_assoc (star (A.eigUnitary : Matrix d d ℂ)) (A.eigUnitary : Matrix d d ℂ),
                  hUA_l, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _),
                  hUA_l, Matrix.mul_one]
    ext i j
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    by_cases hi : A.eigvals i = 0
    · simp [hi, hf0]
    · have h := congr_fun (congr_fun hQQ_A j) i
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Function.comp_apply] at h
      have hji : (Q * Qᴴ) j i = if j = i then 1 else 0 :=
        mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hi) (by simpa [mul_ite] using h)
      have hij : (Q * Qᴴ) i j = if i = j then 1 else 0 := by
        have hherm : (Q * Qᴴ)ᴴ = Q * Qᴴ := by simp [Matrix.conjTranspose_mul]
        have hst := congr_fun (congr_fun hherm i) j
        simp only [Matrix.conjTranspose_apply] at hst
        rw [← hst, hji]; split_ifs with h1 h2 <;> simp_all
      rw [hij]; split_ifs <;> simp
  have hMQ : Matrix.diagonal (fun i ↦ f (A.eigvals i)) * Q =
      Q * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    by_cases h : A.eigvals i = A'.eigvals k
    · rw [h, mul_comm]
    · rw [hQ_zero i k h, mul_zero, zero_mul]
  have hcore : Matrix.diagonal (fun i ↦ f (A.eigvals i)) =
      Q * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) * Qᴴ := by
    calc Matrix.diagonal (fun i ↦ f (A.eigvals i))
        = Matrix.diagonal (fun i ↦ f (A.eigvals i)) * (Q * Qᴴ) := hQQ_diag.symm
      _ = (Matrix.diagonal (fun i ↦ f (A.eigvals i)) * Q) * Qᴴ := by rw [Matrix.mul_assoc]
      _ = Q * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) * Qᴴ := by rw [hMQ]
  have hUA_r : (A.eigUnitary : Matrix d d ℂ) * star (A.eigUnitary : Matrix d d ℂ) = 1 :=
    Unitary.coe_mul_star_self A.eigUnitary
  rw [hcore]
  calc (A.eigUnitary : Matrix d d ℂ) * (Q * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) * Qᴴ) *
        star (A.eigUnitary : Matrix d d ℂ)
      = ((A.eigUnitary : Matrix d d ℂ) * star (A.eigUnitary : Matrix d d ℂ)) *
        V * ((A'.eigUnitary : Matrix d' d' ℂ) * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) *
        star (A'.eigUnitary : Matrix d' d' ℂ)) * Vᴴ *
        ((A.eigUnitary : Matrix d d ℂ) * star (A.eigUnitary : Matrix d d ℂ)) := by
          simp [Q, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hUA_r, Matrix.one_mul, Matrix.mul_one]

end Helpers

/-! ### Part 1: Equal-Support Lemma 3.2 (Gap 5.2) -/

section EqualSupportLemma32

/-- Isometric embedding `H = V H' Vᴴ` with `Vᴴ V = I` preserves `posPartTrace`. -/
lemma posPartTrace_eq_of_isom {d d' : Type*} [Fintype d] [DecidableEq d]
    [Fintype d'] [DecidableEq d']
    {H : Matrix d d ℂ} {H' : Matrix d' d' ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (V : Matrix d d' ℂ) (hVHV : Vᴴ * V = 1) (hmat : V * H' * Vᴴ = H) :
    posPartTrace hH = posPartTrace hH' := by
  have hle1 : posPartTrace hH ≤ posPartTrace hH' := by
    have hP_psd : (V * posPartMat hH' * Vᴴ).PosSemidef :=
      (posPartMat_posSemidef hH').mul_mul_conjTranspose_same V
    have hdiff_psd : (V * posPartMat hH' * Vᴴ - H).PosSemidef := by
      rw [← hmat]
      have hsub : V * posPartMat hH' * Vᴴ - V * H' * Vᴴ = V * negPartMat hH' * Vᴴ := by
        rw [← Matrix.sub_mul, ← Matrix.mul_sub]
        have hdecomp := posPartMat_sub_negPartMat hH'
        have heq : posPartMat hH' - H' = negPartMat hH' :=
          sub_eq_of_eq_add' (eq_add_of_sub_eq hdecomp).symm
        rw [heq]
      rw [hsub]
      exact (negPartMat_posSemidef hH').mul_mul_conjTranspose_same V
    have hle := posPartTrace_le_trace_of_le hH hP_psd hdiff_psd
    have htr : (V * posPartMat hH' * Vᴴ).trace = (posPartMat hH').trace := by
      rw [Matrix.trace_mul_cycle, hVHV, Matrix.one_mul]
    rw [htr, posPartTrace_eq_trace hH'] at hle
    exact hle
  have hH'_eq : Vᴴ * H * V = H' := by
    rw [← hmat]
    calc Vᴴ * (V * H' * Vᴴ) * V = (Vᴴ * V) * H' * (Vᴴ * V) := by simp [Matrix.mul_assoc]
      _ = H' := by rw [hVHV, Matrix.one_mul, Matrix.mul_one]
  have hle2 : posPartTrace hH' ≤ posPartTrace hH := by
    have hP_psd : (Vᴴ * posPartMat hH * V).PosSemidef :=
      (posPartMat_posSemidef hH).conjTranspose_mul_mul_same V
    have hdiff_psd : (Vᴴ * posPartMat hH * V - H').PosSemidef := by
      rw [← hH'_eq]
      have hsub : Vᴴ * posPartMat hH * V - Vᴴ * H * V = Vᴴ * negPartMat hH * V := by
        rw [← Matrix.sub_mul, ← Matrix.mul_sub]
        have hdecomp := posPartMat_sub_negPartMat hH
        have heq : posPartMat hH - H = negPartMat hH :=
          sub_eq_of_eq_add' (eq_add_of_sub_eq hdecomp).symm
        rw [heq]
      rw [hsub]
      exact (negPartMat_posSemidef hH).conjTranspose_mul_mul_same V
    have hle := posPartTrace_le_trace_of_le hH' hP_psd hdiff_psd
    have htr : (Vᴴ * posPartMat hH * V).trace.re ≤ (posPartMat hH).trace.re := by
      have hVV_le : (1 - V * Vᴴ).PosSemidef := by
        have hproj : (1 - V * Vᴴ) = (1 - V * Vᴴ)ᴴ * (1 - V * Vᴴ) := by
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_one, Matrix.one_mul]
          have hsq : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
            calc V * Vᴴ * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp [Matrix.mul_assoc]
              _ = V * Vᴴ := by rw [hVHV, Matrix.mul_one]
          rw [hsq]; abel
        rw [hproj]
        exact Matrix.posSemidef_conjTranspose_mul_self _
      have htr_eq : (Vᴴ * posPartMat hH * V).trace = (posPartMat hH * (V * Vᴴ)).trace := by
        rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
      have hdiff : ((posPartMat hH).trace - (Vᴴ * posPartMat hH * V).trace).re =
          (posPartMat hH * (1 - V * Vᴴ)).trace.re := by
        rw [htr_eq, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
      have hnn : 0 ≤ (posPartMat hH * (1 - V * Vᴴ)).trace.re :=
        trace_mul_posSemidef_nonneg (posPartMat_posSemidef hH) hVV_le
      rw [Complex.sub_re] at hdiff
      linarith
    rw [posPartTrace_eq_trace hH] at htr
    exact le_trans hle htr
  exact le_antisymm hle1 hle2

/-- **Lemma 3.2 (Simultaneous Hockey-Stick Representation under Equal Support)**:
For any finite-dimensional density operators `ρ, σ` with equal support
(`suppSubset ρ σ ∧ suppSubset σ ρ`), there exists a Borel probability measure `μ` supported
on a compact subinterval `[a, b] ⊂ (0, ∞)` with `∫ t dμ = 1` simultaneously representing
`E_s(ρ ‖ σ)`, `D(ρ ‖ σ)`, `D(σ ‖ ρ)`, and `QJS(ρ, σ)`. -/
theorem lemma_3_2_hockeyStick_measure_equalSupport {d : Type*} [Fintype d] [DecidableEq d]
    {ρ σ : DensityOp d} (hsupp : suppSubset ρ σ ∧ suppSubset σ ρ) :
    ∃ (a b : ℝ) (μ : Measure ℝ),
      0 < a ∧ a ≤ b ∧ IsProbabilityMeasure μ ∧ μ (Icc a b)ᶜ = 0 ∧
      (∀ s : ℝ, hockeyStick s ρ σ = ∫ t, max (t - s) 0 ∂μ) ∧
      (∫ t, t ∂μ = 1) ∧
      ((relEntropy ρ σ).toReal = ∫ t, (t * Real.logb 2 t - (t - 1) / Real.log 2) ∂μ) ∧
      ((relEntropy σ ρ).toReal = ∫ t, (-Real.logb 2 t + (t - 1) / Real.log 2) ∂μ) ∧
      (qjs ρ σ = ∫ t, (t / 2 * Real.logb 2 (2 * t / (1 + t)) +
        1 / 2 * Real.logb 2 (2 / (1 + t))) ∂μ) := by
  set S_pos : Finset d := Finset.univ.filter fun i : d ↦ 0 < ρ.eigvals i
  let d' := {i : d // i ∈ S_pos}
  set U : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
  have hU_mul : U * star U = 1 := Unitary.coe_mul_star_self ρ.eigUnitary
  have hU_star : star U * U = 1 := Unitary.coe_star_mul_self ρ.eigUnitary
  let V : Matrix d d' ℂ := Matrix.of fun r k ↦ U r k.1
  have hVHV : Vᴴ * V = 1 := by
    ext j k
    simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    have h := congr_fun (congr_fun hU_star j.1) k.1
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h
    by_cases hjk : j = k
    · subst hjk; simp at h ⊢; exact h
    · have hjk' : j.1 ≠ k.1 := fun heq ↦ hjk (Subtype.ext heq)
      simp [hjk, hjk'] at h ⊢; exact h
  have hρ_ker : ∀ i ∉ S_pos, ρ.mat *ᵥ (fun r ↦ U r i) = 0 := by
    intro i hi
    have hi0 : ρ.eigvals i = 0 :=
      le_antisymm (not_lt.mp (by simpa [S_pos] using hi)) (ρ.eigvals_nonneg i)
    have hspec := density_spectral_eq ρ
    rw [hspec]
    have hvec : star U *ᵥ (fun r ↦ U r i) = Pi.single i 1 := by
      ext j
      have h := congr_fun (congr_fun hU_star j) i
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply, eq_comm] using h
    calc (U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U) *ᵥ (fun r ↦ U r i)
        = U *ᵥ (Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *ᵥ (star U *ᵥ (fun r ↦ U r i))) := by
            simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = U *ᵥ (Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *ᵥ Pi.single i 1) := by rw [hvec]
      _ = 0 := by
            have h0 : Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *ᵥ Pi.single i 1 = 0 := by
              ext j; simp only [Matrix.mulVec_diagonal, Pi.single_apply, Function.comp_apply, Pi.zero_apply]
              by_cases hji : j = i <;> simp [hji, hi0]
            rw [h0, Matrix.mulVec_zero]
  have hσ_ker : ∀ i ∉ S_pos, σ.mat *ᵥ (fun r ↦ U r i) = 0 :=
    fun i hi ↦ suppSubset_ker_aux hsupp.2 (hρ_ker i hi)
  have hcompress : ∀ (τ : DensityOp d), (∀ i ∉ S_pos, τ.mat *ᵥ (fun r ↦ U r i) = 0) →
      V * (Vᴴ * τ.mat * V) * Vᴴ = τ.mat := by
    intro τ hker
    have hVV : V * Vᴴ = U * Matrix.diagonal (fun i : d ↦ if i ∈ S_pos then (1 : ℂ) else 0) * star U := by
      ext r s
      simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.diagonal_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ↓reduceIte, Matrix.star_apply]
      simp only [ite_mul, zero_mul]
      rw [← Finset.sum_coe_sort S_pos (fun i ↦ U r i * star (U s i))]
      rw [← Finset.sum_filter]
      rfl
    have hPτ : (V * Vᴴ) * τ.mat = τ.mat := by
      rw [hVV]
      ext r s
      have hτU : ∀ i ∉ S_pos, (star U * τ.mat) i s = 0 := by
        intro i hi
        have hherm : τ.matᴴ = τ.mat := τ.posSemidef.isHermitian
        have hcol := congr_fun (hker i hi) s
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hcol
        have hconj : star (∑ x : d, τ.mat s x * U x i) = 0 := by rw [hcol, star_zero]
        simp only [star_sum, star_mul'] at hconj
        have hentry : (star U * τ.mat) i s = ∑ x : d, star (U x i) * τ.mat x s := by
          simp [Matrix.mul_apply, Matrix.star_apply]
        rw [hentry]
        convert hconj using 2 with x
        have hxs : star (τ.mat s x) = τ.mat x s := by
          have := congr_fun (congr_fun hherm x) s
          simpa [Matrix.conjTranspose_apply] using this
        rw [hxs, mul_comm]
      calc ((U * Matrix.diagonal (fun i : d ↦ if i ∈ S_pos then (1 : ℂ) else 0) * star U) * τ.mat) r s
          = (U * (Matrix.diagonal (fun i : d ↦ if i ∈ S_pos then (1 : ℂ) else 0) * (star U * τ.mat))) r s := by
              simp [Matrix.mul_assoc]
        _ = ∑ i : d, U r i * (if i ∈ S_pos then (star U * τ.mat) i s else 0) := by
              simp [Matrix.mul_apply, Matrix.diagonal_apply]
        _ = ∑ i : d, U r i * (star U * τ.mat) i s := by
              apply Finset.sum_congr rfl; intro i _
              split_ifs with hi
              · rfl
              · rw [hτU i hi, mul_zero]
        _ = (U * (star U * τ.mat)) r s := by simp [Matrix.mul_apply]
        _ = τ.mat r s := by rw [← Matrix.mul_assoc, hU_mul, Matrix.one_mul]
    have hτP : τ.mat * (V * Vᴴ) = τ.mat := by
      have h1 := congr_arg Matrix.conjTranspose hPτ
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        τ.posSemidef.isHermitian.eq] at h1
      simpa [Matrix.mul_assoc] using h1
    calc V * (Vᴴ * τ.mat * V) * Vᴴ = (V * Vᴴ) * τ.mat * (V * Vᴴ) := by simp [Matrix.mul_assoc]
      _ = τ.mat := by rw [hPτ, hτP]
  have hρ_comp := hcompress ρ hρ_ker
  have hσ_comp := hcompress σ hσ_ker
  let ρ' : DensityOp d' :=
    { mat := Vᴴ * ρ.mat * V
      posSemidef := ρ.posSemidef.conjTranspose_mul_mul_same V
      trace_one := by
        have htr : (Vᴴ * ρ.mat * V).trace = (V * (Vᴴ * ρ.mat * V) * Vᴴ).trace := by
          calc (Vᴴ * ρ.mat * V).trace = (1 * (Vᴴ * ρ.mat * V)).trace := by rw [Matrix.one_mul]
            _ = (Vᴴ * V * (Vᴴ * ρ.mat * V)).trace := by rw [hVHV]
            _ = (V * (Vᴴ * ρ.mat * V) * Vᴴ).trace := by rw [Matrix.trace_mul_cycle]; simp [Matrix.mul_assoc]
        rw [htr, hρ_comp, ρ.trace_one] }
  let σ' : DensityOp d' :=
    { mat := Vᴴ * σ.mat * V
      posSemidef := σ.posSemidef.conjTranspose_mul_mul_same V
      trace_one := by
        have htr : (Vᴴ * σ.mat * V).trace = (V * (Vᴴ * σ.mat * V) * Vᴴ).trace := by
          calc (Vᴴ * σ.mat * V).trace = (1 * (Vᴴ * σ.mat * V)).trace := by rw [Matrix.one_mul]
            _ = (Vᴴ * V * (Vᴴ * σ.mat * V)).trace := by rw [hVHV]
            _ = (V * (Vᴴ * σ.mat * V) * Vᴴ).trace := by rw [Matrix.trace_mul_cycle]; simp [Matrix.mul_assoc]
        rw [htr, hσ_comp, σ.trace_one] }
  have hρ'_pd : ρ'.mat.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨ρ'.posSemidef.isHermitian, fun x hx ↦ ?_⟩
    have hρ'_diag : ρ'.mat = Matrix.diagonal (fun k : d' ↦ (ρ.eigvals k.1 : ℂ)) := by
      have hspec := density_spectral_eq ρ
      have hVU : Vᴴ * U = Matrix.of fun (a : d') (b : d) ↦ if a.1 = b then 1 else 0 := by
        ext a b
        have h := congr_fun (congr_fun hU_star a.1) b
        simpa [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.star_apply,
          Matrix.one_apply] using h
      have hUV : star U * V = Matrix.of fun (a : d) (b : d') ↦ if a = b.1 then 1 else 0 := by
        ext a b
        have h := congr_fun (congr_fun hU_star a) b.1
        simpa [V, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h
      calc ρ'.mat = Vᴴ * (U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U) * V := by
              rw [← hspec]
        _ = (Vᴴ * U) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * (star U * V) := by
              simp [Matrix.mul_assoc]
        _ = Matrix.diagonal (fun k : d' ↦ (ρ.eigvals k.1 : ℂ)) := by
              rw [hVU, hUV]
              ext j k
              simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply, ite_mul,
                zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
                Finset.mem_univ, ↓reduceIte, Function.comp_apply, one_mul, mul_one]
              by_cases hjk : j = k
              · subst hjk; simp
              · have hjk' : j.1 ≠ k.1 := fun heq ↦ hjk (Subtype.ext heq)
                simp [hjk, hjk']
    rw [hρ'_diag]
    have hsum : star x ⬝ᵥ (Matrix.diagonal (fun k : d' ↦ (ρ.eigvals k.1 : ℂ)) *ᵥ x) =
        ((∑ k : d', ρ.eigvals k.1 * ‖x k‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Matrix.mulVec_diagonal, Complex.ofReal_sum, Complex.ofReal_mul]
      apply Finset.sum_congr rfl; intro k _
      have hsq : star (x k) * x k = ((‖x k‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc star (x k) * ((ρ.eigvals k.1 : ℂ) * x k)
          = (ρ.eigvals k.1 : ℂ) * (star (x k) * x k) := by ring
        _ = (ρ.eigvals k.1 : ℂ) * ((‖x k‖ ^ 2 : ℝ) : ℂ) := by rw [hsq]
        _ = _ := by push_cast; ring
    rw [hsum]
    have hpos : (0 : ℝ) < ∑ k : d', ρ.eigvals k.1 * ‖x k‖ ^ 2 := by
      obtain ⟨k₀, hk₀⟩ := Function.ne_iff.mp hx
      apply Finset.sum_pos' (fun k _ ↦ mul_nonneg (ρ.eigvals_nonneg k.1) (sq_nonneg _))
      refine ⟨k₀, Finset.mem_univ k₀, mul_pos ?_ (sq_pos_of_pos (norm_pos_iff.mpr hk₀))⟩
      exact (Finset.mem_filter.mp k₀.2).2
    exact Complex.zero_lt_real.mpr hpos
  have hσ'_pd : σ'.mat.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨σ'.posSemidef.isHermitian, fun x hx ↦ ?_⟩
    have hnn := σ'.posSemidef.dotProduct_mulVec_nonneg x
    by_contra hnot
    have h0 : star x ⬝ᵥ (σ'.mat *ᵥ x) = 0 := by
      have hre0 : (star x ⬝ᵥ (σ'.mat *ᵥ x)).re = 0 := by
        have hle : ¬ (0 < (star x ⬝ᵥ (σ'.mat *ᵥ x)).re) := by
          intro hpos
          apply hnot
          exact (Complex.lt_def.mpr ⟨hpos, (Complex.le_def.mp hnn).2.symm⟩)
        linarith [(Complex.le_def.mp hnn).1]
      exact Complex.ext hre0 (Complex.le_def.mp hnn).2.symm
    have hσVx : star (V *ᵥ x) ⬝ᵥ (σ.mat *ᵥ (V *ᵥ x)) = 0 := by
      have hvec : star (V *ᵥ x) ⬝ᵥ (σ.mat *ᵥ (V *ᵥ x)) = star x ⬝ᵥ (σ'.mat *ᵥ x) := by
        have hst : star (V *ᵥ x) = star x ᵥ* Vᴴ := by
          ext j; simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, mul_comm]
        calc star (V *ᵥ x) ⬝ᵥ (σ.mat *ᵥ (V *ᵥ x))
            = (star x ᵥ* Vᴴ) ⬝ᵥ (σ.mat *ᵥ (V *ᵥ x)) := by rw [hst]
          _ = star x ⬝ᵥ (Vᴴ *ᵥ (σ.mat *ᵥ (V *ᵥ x))) := (Matrix.dotProduct_mulVec _ _ _).symm
          _ = star x ⬝ᵥ (σ'.mat *ᵥ x) := by simp [σ', Matrix.mulVec_mulVec]
      rw [hvec, h0]
    have hσ_zero : σ.mat *ᵥ (V *ᵥ x) = 0 := posSemidef_mulVec_eq_zero_of_dot σ.posSemidef hσVx
    have hρ_zero : ρ.mat *ᵥ (V *ᵥ x) = 0 := suppSubset_ker_aux hsupp.1 hσ_zero
    have hρ'_zero : ρ'.mat *ᵥ x = 0 := by
      calc ρ'.mat *ᵥ x = Vᴴ *ᵥ (ρ.mat *ᵥ (V *ᵥ x)) := by simp [ρ', Matrix.mulVec_mulVec]
        _ = 0 := by rw [hρ_zero, Matrix.mulVec_zero]
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hρ'_pd).2 x hx
    rw [hρ'_zero, dotProduct_zero] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨a, b, μ, ha, hab, hprob, hsuppμ, hhs, hint, hD1, hD2, hqjs⟩ :=
    lemma_3_2_hockeyStick_measure hρ'_pd hσ'_pd
  have hhs_eq : ∀ s : ℝ, hockeyStick s ρ σ = hockeyStick s ρ' σ' := fun s ↦ by
    rw [hockeyStick_eq_posPartTrace, hockeyStick_eq_posPartTrace]
    apply posPartTrace_eq_of_isom (hockeyStick_isHermitian s ρ σ) (hockeyStick_isHermitian s ρ' σ') V hVHV
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hρ_comp, hσ_comp]
  have hiso_ent : ∀ (A B : DensityOp d) (A' B' : DensityOp d'),
      V * A'.mat * Vᴴ = A.mat → V * B'.mat * Vᴴ = B.mat →
      A'.mat.PosDef → B'.mat.PosDef →
      relEntropy A B = relEntropy A' B' ∧ vonNeumannEntropy A = vonNeumannEntropy A' := by
    intro A B A' B' hA hB hA'_pd hB'_pd
    have hS_eq : vonNeumannEntropy A = vonNeumannEntropy A' := by
      let f : ℝ → ℂ := fun t ↦ (Real.negMulLog t : ℂ)
      have hf0 : f 0 = 0 := by simp [f, Real.negMulLog]
      have htr := congr_arg Matrix.trace (isom_func_eq V hVHV A A' hA f hf0)
      have htrL : ((A.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun i ↦ f (A.eigvals i)) *
          star (A.eigUnitary : Matrix d d ℂ)).trace = ∑ i : d, f (A.eigvals i) := by
        rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
      have htrR : (V * ((A'.eigUnitary : Matrix d' d' ℂ) * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) *
          star (A'.eigUnitary : Matrix d' d' ℂ)) * Vᴴ).trace = ∑ k : d', f (A'.eigvals k) := by
        rw [Matrix.trace_mul_cycle, hVHV, Matrix.one_mul, Matrix.trace_mul_cycle,
          Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
      rw [htrL, htrR] at htr
      have hre := congr_arg Complex.re htr
      simp only [Complex.re_sum, f, Complex.ofReal_re] at hre
      unfold vonNeumannEntropy
      rw [hre]
    have hD_eq : relEntropy A B = relEntropy A' B' := by
      have hsuppAB : suppSubset A B := by
        intro i j hi hj
        have hBi : B.mat *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j) = 0 := by
          rw [density_spectral_eq B]
          have hvec : star (B.eigUnitary : Matrix d d ℂ) *ᵥ
              (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j) = Pi.single j 1 := by
            ext k
            have h := congr_fun (congr_fun (Unitary.coe_star_mul_self B.eigUnitary) k) j
            simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
              Matrix.one_apply, Pi.single_apply, eq_comm] using h
          calc ((B.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ B.eigvals) *
                star (B.eigUnitary : Matrix d d ℂ)) *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j)
              = (B.eigUnitary : Matrix d d ℂ) *ᵥ (Matrix.diagonal (Complex.ofReal ∘ B.eigvals) *ᵥ
                Pi.single j 1) := by simp [Matrix.mulVec_mulVec, Matrix.mul_assoc, hvec]
            _ = 0 := by
                have h0 : Matrix.diagonal (Complex.ofReal ∘ B.eigvals) *ᵥ Pi.single j 1 = 0 := by
                  ext k; simp only [Matrix.mulVec_diagonal, Pi.single_apply, Function.comp_apply, Pi.zero_apply]
                  by_cases hkj : k = j <;> simp [hkj, hj]
                rw [h0, Matrix.mulVec_zero]
        have hVHB : Vᴴ *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j) = 0 := by
          by_contra hne
          have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hB'_pd).2 _ hne
          have hzero : B'.mat *ᵥ (Vᴴ *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j)) = 0 := by
            have hBV : Vᴴ * B.mat = B'.mat * Vᴴ := by
              rw [← hB]; simp [Matrix.mul_assoc, hVHV]
            calc B'.mat *ᵥ (Vᴴ *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j))
                = (B'.mat * Vᴴ) *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j) := by
                    rw [Matrix.mulVec_mulVec]
              _ = (Vᴴ * B.mat) *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j) := by rw [← hBV]
              _ = Vᴴ *ᵥ (B.mat *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j)) := by
                    rw [Matrix.mulVec_mulVec]
              _ = 0 := by rw [hBi, Matrix.mulVec_zero]
          rw [hzero, dotProduct_zero] at hpos
          exact lt_irrefl 0 hpos
        have hAi : A.mat *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j) = 0 := by
          rw [← hA]
          calc (V * A'.mat * Vᴴ) *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j)
              = (V * A'.mat) *ᵥ (Vᴴ *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j)) := by
                  simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
            _ = 0 := by rw [hVHB, Matrix.mulVec_zero]
        have h0 := congr_fun (congr_arg (fun v ↦ star (A.eigUnitary : Matrix d d ℂ) *ᵥ v) hAi) i
        rw [density_spectral_eq A] at h0
        simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero, Pi.zero_apply] at h0
        have h2 : (Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *ᵥ
            (star (A.eigUnitary : Matrix d d ℂ) *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j))) i = 0 := by
          simpa [Matrix.mul_assoc, Unitary.coe_star_mul_self] using h0
        simp only [Matrix.mulVec_diagonal, Function.comp_apply] at h2
        rcases mul_eq_zero.mp h2 with hλ | hw
        · exact absurd (Complex.ofReal_eq_zero.mp hλ) hi
        · have hst : (star (B.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i =
              star ((star (A.eigUnitary : Matrix d d ℂ) *ᵥ
                (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j)) i) := by
            simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.star_apply, mul_comm]
          rw [hst, hw, star_zero]
      have hsuppA'B' : suppSubset A' B' := fun _ j _ hj ↦
        absurd hj (ne_of_gt (B'.eigvals_pos_of_posDef hB'_pd j))
      rw [relEntropy_eq_trace_log A B hsuppAB, relEntropy_eq_trace_log A' B' hsuppA'B', hS_eq]
      have hcommB := isom_func_eq V hVHV B B' hB
        (fun t ↦ if t = 0 then (0 : ℂ) else (Real.log t : ℂ)) (by simp)
      have htr_eq : (A.mat * ((B.eigUnitary : Matrix d d ℂ) *
            Matrix.diagonal (fun j ↦ if B.eigvals j = 0 then (0 : ℂ) else (Real.log (B.eigvals j) : ℂ)) *
            star (B.eigUnitary : Matrix d d ℂ))).trace =
          (A'.mat * ((B'.eigUnitary : Matrix d' d' ℂ) *
            Matrix.diagonal (fun k ↦ if B'.eigvals k = 0 then (0 : ℂ) else (Real.log (B'.eigvals k) : ℂ)) *
            star (B'.eigUnitary : Matrix d' d' ℂ))).trace := by
        rw [← hA, hcommB]
        set L' := (B'.eigUnitary : Matrix d' d' ℂ) *
          Matrix.diagonal (fun k ↦ if B'.eigvals k = 0 then (0 : ℂ) else (Real.log (B'.eigvals k) : ℂ)) *
          star (B'.eigUnitary : Matrix d' d' ℂ)
        calc (V * A'.mat * Vᴴ * (V * L' * Vᴴ)).trace
            = (V * (A'.mat * (Vᴴ * V) * L') * Vᴴ).trace := by simp [Matrix.mul_assoc]
          _ = (V * (A'.mat * L') * Vᴴ).trace := by rw [hVHV, Matrix.mul_one]
          _ = (Vᴴ * V * (A'.mat * L')).trace := by rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
          _ = (A'.mat * L').trace := by rw [hVHV, Matrix.one_mul]
      rw [htr_eq]
    exact ⟨hD_eq, hS_eq⟩
  have h1 := hiso_ent ρ σ ρ' σ' hρ_comp hσ_comp hρ'_pd hσ'_pd
  have h2 := hiso_ent σ ρ σ' ρ' hσ_comp hρ_comp hσ'_pd hρ'_pd
  have hmid_comp : V * (DensityOp.midpoint ρ' σ').mat * Vᴴ = (DensityOp.midpoint ρ σ).mat := by
    simp only [DensityOp.midpoint, DensityOp.mix, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, hρ_comp, hσ_comp]
  have hmid'_pd : (DensityOp.midpoint ρ' σ').mat.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨(DensityOp.midpoint ρ' σ').posSemidef.isHermitian, fun x hx ↦ ?_⟩
    have h1x := (Matrix.posDef_iff_dotProduct_mulVec.mp hρ'_pd).2 x hx
    have h2x := (Matrix.posDef_iff_dotProduct_mulVec.mp hσ'_pd).2 x hx
    simp only [DensityOp.midpoint, DensityOp.mix, Matrix.add_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hpos1 : (0 : ℂ) < ((1 - 1 / 2 : ℝ) : ℂ) * (star x ⬝ᵥ (ρ'.mat *ᵥ x)) := by
      rw [Complex.lt_def] at h1x ⊢
      refine ⟨by simp [Complex.mul_re]; linarith [h1x.1], by simp [Complex.mul_im, h1x.2.symm]⟩
    have hpos2 : (0 : ℂ) < ((1 / 2 : ℝ) : ℂ) * (star x ⬝ᵥ (σ'.mat *ᵥ x)) := by
      rw [Complex.lt_def] at h2x ⊢
      refine ⟨by simp [Complex.mul_re]; linarith [h2x.1], by simp [Complex.mul_im, h2x.2.symm]⟩
    exact add_pos hpos1 hpos2
  have h3 := hiso_ent (DensityOp.midpoint ρ σ) ρ (DensityOp.midpoint ρ' σ') ρ'
    hmid_comp hρ_comp hmid'_pd hρ'_pd
  have hqjs_eq : qjs ρ σ = qjs ρ' σ' := by
    unfold qjs
    rw [h3.2, h1.2, h2.2]
  refine ⟨a, b, μ, ha, hab, hprob, hsuppμ, fun s ↦ by rw [hhs_eq s]; exact hhs s, hint,
    by rw [h1.1]; exact hD1, by rw [h2.1]; exact hD2, by rw [hqjs_eq]; exact hqjs⟩

end EqualSupportLemma32

/-! ### Part 2: Proposition 3.3 Classical Equality (Gap 5.1) -/

section Prop33Equality

/-- Symmetric classical binary state `diag((1+x)/2, (1-x)/2)` for `x ∈ [0, 1]`. -/
noncomputable def symClassicalPair0 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : DensityOp Bool where
  mat := Matrix.diagonal fun b : Bool ↦ if b = false then (((1 + x) / 2 : ℝ) : ℂ) else (((1 - x) / 2 : ℝ) : ℂ)
  posSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro b; cases b <;> simp only [↓reduceIte, Bool.true_eq_false] <;>
      exact Complex.zero_le_real.mpr (by linarith)
  trace_one := by
    rw [Matrix.trace_diagonal, Fintype.sum_bool]
    simp; push_cast; ring

/-- Symmetric classical binary state `diag((1-x)/2, (1+x)/2)` for `x ∈ [0, 1]`. -/
noncomputable def symClassicalPair1 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : DensityOp Bool where
  mat := Matrix.diagonal fun b : Bool ↦ if b = false then (((1 - x) / 2 : ℝ) : ℂ) else (((1 + x) / 2 : ℝ) : ℂ)
  posSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro b; cases b <;> simp only [↓reduceIte, Bool.true_eq_false] <;>
      exact Complex.zero_le_real.mpr (by linarith)
  trace_one := by
    rw [Matrix.trace_diagonal, Fintype.sum_bool]
    simp; push_cast; ring

/-- **Proposition 3.3 (Classical Equality)**: Every symmetric classical binary pair
`ρ = diag((1+x)/2, (1-x)/2)`, `σ = diag((1-x)/2, (1+x)/2)` attains equality in Proposition 3.3
for all `x ∈ [0, 1]` (including `x = 1`, where both sides equal `⊤ : ℝ≥0∞`). -/
theorem prop_3_3_qjjs_classical_equality {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    phiExt (qjs (symClassicalPair0 x hx0 hx1) (symClassicalPair1 x hx0 hx1)) =
      (1 / 4 : ℝ≥0∞) *
        (relEntropy (symClassicalPair0 x hx0 hx1) (symClassicalPair1 x hx0 hx1) +
         relEntropy (symClassicalPair1 x hx0 hx1) (symClassicalPair0 x hx0 hx1)) := by
  set ρ := symClassicalPair0 x hx0 hx1
  set σ := symClassicalPair1 x hx0 hx1
  set p := (1 - x) / 2
  have hp0 : 0 ≤ p := by linarith
  have hp1 : p ≤ 1 / 2 := by linarith
  have hp1' : p ≤ 1 := by linarith
  have hρ_bsc : ρ.mat = ((bscChannel p hp0 hp1').out false).mat := by
    ext i j; cases i <;> cases j <;> simp [ρ, symClassicalPair0, bscChannel, p] <;>
      (push_cast; ring)
  have hσ_bsc : σ.mat = ((bscChannel p hp0 hp1').out true).mat := by
    ext i j; cases i <;> cases j <;> simp [σ, symClassicalPair1, bscChannel, p] <;>
      (push_cast; ring)
  have hqjs_val : qjs ρ σ = 1 - h2 p := by
    have hcond := condEntropy_bscChannel p hp0 hp1'
    have hqjs_bsc : qjs ((bscChannel p hp0 hp1').out false) ((bscChannel p hp0 hp1').out true) =
        1 - (bscChannel p hp0 hp1').condEntropy := by
      unfold CQChannel.condEntropy; ring
    have hSρ : vonNeumannEntropy ρ = vonNeumannEntropy ((bscChannel p hp0 hp1').out false) := by
      cases ρ; cases ((bscChannel p hp0 hp1').out false); simp_all
    have hSσ : vonNeumannEntropy σ = vonNeumannEntropy ((bscChannel p hp0 hp1').out true) := by
      cases σ; cases ((bscChannel p hp0 hp1').out true); simp_all
    have hSmid : vonNeumannEntropy (DensityOp.midpoint ρ σ) =
        vonNeumannEntropy (DensityOp.midpoint ((bscChannel p hp0 hp1').out false)
          ((bscChannel p hp0 hp1').out true)) := by
      have hmat : (DensityOp.midpoint ρ σ).mat =
          (DensityOp.midpoint ((bscChannel p hp0 hp1').out false)
            ((bscChannel p hp0 hp1').out true)).mat := by
        simp [DensityOp.midpoint, DensityOp.mix, hρ_bsc, hσ_bsc]
      cases DensityOp.midpoint ρ σ
      cases DensityOp.midpoint ((bscChannel p hp0 hp1').out false) ((bscChannel p hp0 hp1').out true)
      simp_all
    unfold qjs at hqjs_bsc ⊢
    rw [hSmid, hSρ, hSσ, hqjs_bsc, hcond]
  by_cases hx_eq1 : x = 1
  · have hp_zero : p = 0 := by simp [p, hx_eq1]
    have hqjs1 : qjs ρ σ = 1 := by rw [hqjs_val, hp_zero, h2_zero]; ring
    have hnsupp : ¬ suppSubset ρ σ := by
      intro hsupp
      have hv : σ.mat *ᵥ (fun b : Bool ↦ if b = false then (1 : ℂ) else 0) = 0 := by
        ext b; cases b <;> simp [σ, symClassicalPair1, hx_eq1, Matrix.mulVec, dotProduct]
      have hρv := suppSubset_ker_aux hsupp hv
      have h0 := congr_fun hρv false
      simp [ρ, symClassicalPair0, hx_eq1, Matrix.mulVec, dotProduct] at h0
    have hDtop : relEntropy ρ σ = ⊤ := by unfold relEntropy; rw [if_neg hnsupp]
    rw [hqjs1, hDtop]
    simp [phiExt]
  · have hx_lt1 : x < 1 := lt_of_le_of_ne hx1 hx_eq1
    have hp_pos : 0 < p := by linarith
    have h1mp_pos : 0 < 1 - p := by linarith
    have hq_lt1 : qjs ρ σ < 1 := by
      rw [hqjs_val]
      have hh2_pos : 0 < h2 p := by
        unfold h2
        have h1 : 0 < -p * Real.logb 2 p := by
          have hl : Real.logb 2 p < 0 := Real.logb_neg (by norm_num) hp_pos (by linarith)
          nlinarith
        have h2' : 0 < -(1 - p) * Real.logb 2 (1 - p) := by
          have hl : Real.logb 2 (1 - p) < 0 := Real.logb_neg (by norm_num) h1mp_pos (by linarith)
          nlinarith
        linarith
      linarith
    have hrel_diag : ∀ (a b : Bool → ℝ) (A B : DensityOp Bool),
        (∀ i, 0 < a i) → (∀ i, 0 < b i) →
        A.mat = Matrix.diagonal (Complex.ofReal ∘ a) →
        B.mat = Matrix.diagonal (Complex.ofReal ∘ b) →
        relEntropy A B = ENNReal.ofReal ((∑ i : Bool, a i * (Real.log (a i) - Real.log (b i))) / Real.log 2) := by
      intro a b A B ha hb hA hB
      have hB_pd : B.mat.PosDef := by
        rw [hB, Matrix.posDef_diagonal_iff]
        intro i; exact Complex.zero_lt_real.mpr (hb i)
      have hsupp : suppSubset A B := fun _ j _ hj ↦
        absurd hj (ne_of_gt (B.eigvals_pos_of_posDef hB_pd j))
      rw [relEntropy_eq_trace_log A B hsupp]
      have hSA : vonNeumannEntropy A = -∑ i : Bool, a i * Real.logb 2 (a i) := by
        have hspecA := density_spectral_eq A
        set UA := (A.eigUnitary : Matrix Bool Bool ℂ)
        have hcomm : UA * Matrix.diagonal (Complex.ofReal ∘ A.eigvals) =
            Matrix.diagonal (Complex.ofReal ∘ a) * UA := by
          calc UA * Matrix.diagonal (Complex.ofReal ∘ A.eigvals)
              = (UA * Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * star UA) * UA := by
                  simp [Matrix.mul_assoc, Unitary.coe_star_mul_self]
            _ = A.mat * UA := by rw [← hspecA]
            _ = Matrix.diagonal (Complex.ofReal ∘ a) * UA := by rw [hA]
        have hcomm_f : UA * Matrix.diagonal (fun j ↦ (Real.negMulLog (A.eigvals j) : ℂ)) =
            Matrix.diagonal (fun i : Bool ↦ (Real.negMulLog (a i) : ℂ)) * UA := by
          ext i j
          have hij := congr_fun (congr_fun hcomm i) j
          simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
            Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Function.comp_apply] at hij ⊢
          by_cases hU0 : UA i j = 0
          · simp [hU0]
          · have heq : A.eigvals j = a i := by
              have hsub : ((A.eigvals j - a i : ℝ) : ℂ) * UA i j = 0 := by
                push_cast; linear_combination hij
              rcases mul_eq_zero.mp hsub with h0 | h0
              · exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h0)
              · exact absurd h0 hU0
            rw [heq, mul_comm]
        have htr : (UA * Matrix.diagonal (fun j ↦ (Real.negMulLog (A.eigvals j) : ℂ)) * star UA).trace =
            (Matrix.diagonal (fun i : Bool ↦ (Real.negMulLog (a i) : ℂ))).trace := by
          rw [hcomm_f, Matrix.mul_assoc, Unitary.coe_mul_star_self, Matrix.mul_one]
        rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
            Matrix.trace_diagonal, Matrix.trace_diagonal] at htr
        have hre := congr_arg Complex.re htr
        simp only [Complex.re_sum, Complex.ofReal_re] at hre
        unfold vonNeumannEntropy
        rw [hre, ← Finset.sum_neg_distrib, ← Finset.sum_div]
        apply Finset.sum_congr rfl; intro i _
        simp [Real.negMulLog, Real.logb]; ring
      have hLB : (B.eigUnitary : Matrix Bool Bool ℂ) *
            Matrix.diagonal (fun j ↦ if B.eigvals j = 0 then (0 : ℂ) else (Real.log (B.eigvals j) : ℂ)) *
            star (B.eigUnitary : Matrix Bool Bool ℂ) =
          Matrix.diagonal (fun i : Bool ↦ (Real.log (b i) : ℂ)) := by
        have hspecB := density_spectral_eq B
        set UB := (B.eigUnitary : Matrix Bool Bool ℂ)
        have hcomm : UB * Matrix.diagonal (Complex.ofReal ∘ B.eigvals) =
            Matrix.diagonal (Complex.ofReal ∘ b) * UB := by
          calc UB * Matrix.diagonal (Complex.ofReal ∘ B.eigvals)
              = (UB * Matrix.diagonal (Complex.ofReal ∘ B.eigvals) * star UB) * UB := by
                  simp [Matrix.mul_assoc, Unitary.coe_star_mul_self]
            _ = B.mat * UB := by rw [← hspecB]
            _ = Matrix.diagonal (Complex.ofReal ∘ b) * UB := by rw [hB]
        have hcomm_log : UB * Matrix.diagonal (fun j ↦ if B.eigvals j = 0 then (0 : ℂ) else (Real.log (B.eigvals j) : ℂ)) =
            Matrix.diagonal (fun i : Bool ↦ (Real.log (b i) : ℂ)) * UB := by
          ext i j
          have hij := congr_fun (congr_fun hcomm i) j
          simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
            Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Function.comp_apply] at hij ⊢
          by_cases hU0 : UB i j = 0
          · simp [hU0]
          · have heq : B.eigvals j = b i := by
              have hsub : ((B.eigvals j - b i : ℝ) : ℂ) * UB i j = 0 := by
                push_cast; linear_combination hij
              rcases mul_eq_zero.mp hsub with h0 | h0
              · exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h0)
              · exact absurd h0 hU0
            rw [heq, if_neg (ne_of_gt (hb i)), mul_comm]
        rw [hcomm_log, Matrix.mul_assoc, Unitary.coe_mul_star_self, Matrix.mul_one]
      rw [hLB, hA, hSA]
      congr 1
      have htr : (Matrix.diagonal (Complex.ofReal ∘ a) *
          Matrix.diagonal (fun i : Bool ↦ (Real.log (b i) : ℂ))).trace.re =
          ∑ i : Bool, a i * Real.log (b i) := by
        rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
        simp only [Complex.re_sum, Function.comp_apply]
        apply Finset.sum_congr rfl; intro i _
        rw [← Complex.ofReal_mul, Complex.ofReal_re]
      rw [htr]
      simp only [Real.logb, Fintype.sum_bool]
      ring
    have hD1 : relEntropy ρ σ = ENNReal.ofReal (x * Real.logb 2 ((1 + x) / (1 - x))) := by
      have h := hrel_diag
        (fun b ↦ if b = false then (1 + x) / 2 else (1 - x) / 2)
        (fun b ↦ if b = false then (1 - x) / 2 else (1 + x) / 2) ρ σ
        (fun b ↦ by cases b <;> simp <;> linarith)
        (fun b ↦ by cases b <;> simp <;> linarith)
        (by ext i j; cases i <;> cases j <;> simp [ρ, symClassicalPair0])
        (by ext i j; cases i <;> cases j <;> simp [σ, symClassicalPair1])
      rw [h]; congr 1
      rw [Fintype.sum_bool]
      simp only [↓reduceIte, Bool.true_eq_false]
      have h1px : 0 < 1 + x := by linarith
      have h1mx : 0 < 1 - x := by linarith
      rw [Real.log_div (ne_of_gt h1px) (by norm_num),
          Real.log_div (ne_of_gt h1mx) (by norm_num),
          Real.logb, Real.log_div (ne_of_gt h1px) (ne_of_gt h1mx)]
      ring
    have hD2 : relEntropy σ ρ = ENNReal.ofReal (x * Real.logb 2 ((1 + x) / (1 - x))) := by
      have h := hrel_diag
        (fun b ↦ if b = false then (1 - x) / 2 else (1 + x) / 2)
        (fun b ↦ if b = false then (1 + x) / 2 else (1 - x) / 2) σ ρ
        (fun b ↦ by cases b <;> simp <;> linarith)
        (fun b ↦ by cases b <;> simp <;> linarith)
        (by ext i j; cases i <;> cases j <;> simp [σ, symClassicalPair1])
        (by ext i j; cases i <;> cases j <;> simp [ρ, symClassicalPair0])
      rw [h]; congr 1
      rw [Fintype.sum_bool]
      simp only [↓reduceIte, Bool.true_eq_false]
      have h1px : 0 < 1 + x := by linarith
      have h1mx : 0 < 1 - x := by linarith
      rw [Real.log_div (ne_of_gt h1px) (by norm_num),
          Real.log_div (ne_of_gt h1mx) (by norm_num),
          Real.logb, Real.log_div (ne_of_gt h1px) (ne_of_gt h1mx)]
      ring
    have hnn : 0 ≤ x * Real.logb 2 ((1 + x) / (1 - x)) := by
      apply mul_nonneg hx0
      exact Real.logb_nonneg (by norm_num) (by rw [one_le_div (by linarith)]; linarith)
    rw [phiExt, if_pos hq_lt1, hD1, hD2, ← ENNReal.ofReal_add hnn hnn]
    have hquarter : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) := by norm_num
    rw [hquarter, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    have hphi_val : phi (qjs ρ σ) = phiParam x := by
      rw [hqjs_val]
      unfold phi
      have hinv : h2Inv (1 - (1 - h2 p)) = p := by
        rw [sub_sub_cancel]
        exact h2Inv_h2 hp0 hp1
      rw [hinv]
      have h1 : 1 - 2 * p = x := by simp [p]; ring
      rw [h1]
    rw [hphi_val]
    unfold phiParam
    ring

end Prop33Equality

/-! ### Part 3: Relative-Entropy Definition of `C(p)` in Theorem 1.3 (Gap 3) -/

section RelEntropyTheorem13

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- For every bipartite state `Ψ ∈ D(ℂ² ⊗ H_B)` and every `p ∈ [0, 1]`,
`supp((Z_p ⊗ id)(Ψ)) ⊆ supp((Z_{1/2} ⊗ id)(Ψ))`. -/
lemma suppSubset_dephaseState_half (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) :
    suppSubset (dephaseState p hp0 hp1 Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) := by
  set A := dephaseState p hp0 hp1 Ψ
  set M := dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ
  set Z := pauliZTensorI d
  have hM_eq : M.mat = (1 / 2 : ℂ) • A.mat + (1 / 2 : ℂ) • (DensityOp.conjUnitary Z A).mat := by
    ext ⟨b₁, i⟩ ⟨b₂, j⟩
    simp only [M, A, Z, dephaseState, DensityOp.mix, DensityOp.conjUnitary, pauliZTensorI,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.star_apply, smul_eq_mul, ite_mul, zero_mul, mul_ite, mul_zero,
      map_ite, map_zero, map_neg, map_one,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring
  intro i j hi hj
  set v : Bool × d → ℂ := fun r ↦ (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) r j
  have hMv : M.mat *ᵥ v = 0 := by
    rw [density_spectral_eq M]
    have hvec : star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *ᵥ v = Pi.single j 1 := by
      ext k
      have h := congr_fun (congr_fun (Unitary.coe_star_mul_self M.eigUnitary) k) j
      simpa [v, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
        Matrix.one_apply, Pi.single_apply, eq_comm] using h
    calc ((M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
          Matrix.diagonal (Complex.ofReal ∘ M.eigvals) *
          star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)) *ᵥ v
        = (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *ᵥ
          (Matrix.diagonal (Complex.ofReal ∘ M.eigvals) *ᵥ Pi.single j 1) := by
            simp [Matrix.mulVec_mulVec, Matrix.mul_assoc, hvec]
      _ = 0 := by
            have h0 : Matrix.diagonal (Complex.ofReal ∘ M.eigvals) *ᵥ Pi.single j 1 = 0 := by
              ext k; simp only [Matrix.mulVec_diagonal, Pi.single_apply, Function.comp_apply, Pi.zero_apply]
              by_cases hkj : k = j <;> simp [hkj, hj]
            rw [h0, Matrix.mulVec_zero]
  have hdot : star v ⬝ᵥ (M.mat *ᵥ v) = 0 := by rw [hMv, dotProduct_zero]
  rw [hM_eq, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hdot
  have hnn1 := A.posSemidef.dotProduct_mulVec_nonneg v
  have hnn2 := (DensityOp.conjUnitary Z A).posSemidef.dotProduct_mulVec_nonneg v
  have hre := congr_arg Complex.re hdot
  simp only [Complex.add_re, Complex.mul_re, Complex.zero_re] at hre
  have h1re : (star v ⬝ᵥ (A.mat *ᵥ v)).re = 0 := by
    have h1 := (Complex.le_def.mp hnn1).1
    have h2 := (Complex.le_def.mp hnn2).1
    norm_num at hre
    linarith
  have hAv0 : star v ⬝ᵥ (A.mat *ᵥ v) = 0 :=
    Complex.ext h1re (Complex.le_def.mp hnn1).2.symm
  have hAv : A.mat *ᵥ v = 0 := posSemidef_mulVec_eq_zero_of_dot A.posSemidef hAv0
  have h0 := congr_fun (congr_arg (fun w ↦ star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *ᵥ w) hAv) i
  rw [density_spectral_eq A] at h0
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero, Pi.zero_apply] at h0
  have h2 : (Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *ᵥ
      (star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *ᵥ v)) i = 0 := by
    simpa [Matrix.mul_assoc, Unitary.coe_star_mul_self] using h0
  simp only [Matrix.mulVec_diagonal, Function.comp_apply] at h2
  rcases mul_eq_zero.mp h2 with hλ | hw
  · exact absurd (Complex.ofReal_eq_zero.mp hλ) hi
  · have hst : (star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
        (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)) j i =
        star ((star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *ᵥ v) i) := by
      simp [v, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.star_apply, mul_comm]
    rw [hst, hw, star_zero]

/-- **Umegaki Relative-Entropy Identity for Dephasing Coherence**:
`D((Z_p ⊗ id)(Ψ) ‖ (Z_{1/2} ⊗ id)(Ψ)) = S((Z_{1/2} ⊗ id)(Ψ)) - S((Z_p ⊗ id)(Ψ))`. -/
theorem relEntropy_dephaseState_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) :
    relEntropy (dephaseState p hp0 hp1 Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) =
      ENNReal.ofReal
        (vonNeumannEntropy (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) -
         vonNeumannEntropy (dephaseState p hp0 hp1 Ψ)) := by
  set A := dephaseState p hp0 hp1 Ψ
  set M := dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ
  set Z : Matrix (Bool × d) (Bool × d) ℂ := (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)
  have hZZ : Z * Z = 1 := by
    ext ⟨b₁, i⟩ ⟨b₂, j⟩
    simp only [Z, pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    split_ifs with h
    · cases b₁ <;> norm_num
    · rfl
  have hZMZ : Z * M.mat * Z = M.mat := by
    ext ⟨b₁, i⟩ ⟨b₂, j⟩
    simp only [M, Z, dephaseState, DensityOp.mix, DensityOp.conjUnitary, pauliZTensorI,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.star_apply, smul_eq_mul, ite_mul, zero_mul, mul_ite, mul_zero,
      map_ite, map_zero, map_neg, map_one,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring
  have hZM_comm : Z * M.mat = M.mat * Z := by
    calc Z * M.mat = Z * M.mat * (Z * Z) := by rw [hZZ, Matrix.mul_one]
      _ = (Z * M.mat * Z) * Z := by simp [Matrix.mul_assoc]
      _ = M.mat * Z := by rw [hZMZ]
  have hM_avg : M.mat = (1 / 2 : ℂ) • A.mat + (1 / 2 : ℂ) • (Z * A.mat * Z) := by
    ext ⟨b₁, i⟩ ⟨b₂, j⟩
    simp only [M, A, Z, dephaseState, DensityOp.mix, DensityOp.conjUnitary, pauliZTensorI,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.star_apply, smul_eq_mul, ite_mul, zero_mul, mul_ite, mul_zero,
      map_ite, map_zero, map_neg, map_one,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring
  set L_M : Matrix (Bool × d) (Bool × d) ℂ :=
    (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
    Matrix.diagonal (fun j ↦ if M.eigvals j = 0 then (0 : ℂ) else (Real.log (M.eigvals j) : ℂ)) *
    star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)
  have hZL_comm : Z * L_M * Z = L_M := by
    set UM := (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)
    set Z' := star UM * Z * UM
    have hUM_l : star UM * UM = 1 := Unitary.coe_star_mul_self M.eigUnitary
    have hUM_r : UM * star UM = 1 := Unitary.coe_mul_star_self M.eigUnitary
    have hZ'_comm : Z' * Matrix.diagonal (Complex.ofReal ∘ M.eigvals) =
        Matrix.diagonal (Complex.ofReal ∘ M.eigvals) * Z' := by
      have hspec := density_spectral_eq M
      calc Z' * Matrix.diagonal (Complex.ofReal ∘ M.eigvals)
          = star UM * (Z * M.mat) * UM := by
              rw [hspec]; simp only [Z', UM, Matrix.mul_assoc]
              rw [← Matrix.mul_assoc (star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ))
                (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ),
                Unitary.coe_star_mul_self, Matrix.one_mul]
        _ = star UM * (M.mat * Z) * UM := by rw [hZM_comm]
        _ = Matrix.diagonal (Complex.ofReal ∘ M.eigvals) * Z' := by
              rw [hspec]; simp only [Z', UM, Matrix.mul_assoc]
              rw [← Matrix.mul_assoc (star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ))
                (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ),
                Unitary.coe_star_mul_self, Matrix.one_mul]
    let f : ℝ → ℂ := fun t ↦ if t = 0 then 0 else (Real.log t : ℂ)
    have hZ'_f : Z' * Matrix.diagonal (fun j ↦ f (M.eigvals j)) =
        Matrix.diagonal (fun j ↦ f (M.eigvals j)) * Z' := by
      ext i j
      have hij := congr_fun (congr_fun hZ'_comm i) j
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Function.comp_apply] at hij ⊢
      by_cases h0 : Z' i j = 0
      · simp [h0]
      · have heq : M.eigvals j = M.eigvals i := by
          have hsub : ((M.eigvals j - M.eigvals i : ℝ) : ℂ) * Z' i j = 0 := by
            push_cast; linear_combination hij
          rcases mul_eq_zero.mp hsub with h1 | h1
          · exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h1)
          · exact absurd h1 h0
        rw [heq, mul_comm]
    have hZL : Z * L_M = L_M * Z := by
      calc Z * L_M = (UM * star UM) * Z * (UM * Matrix.diagonal (fun j ↦ f (M.eigvals j)) * star UM) := by
              rw [hUM_r, Matrix.one_mul]; rfl
        _ = UM * (Z' * Matrix.diagonal (fun j ↦ f (M.eigvals j))) * star UM := by
              simp [Z', Matrix.mul_assoc]
        _ = UM * (Matrix.diagonal (fun j ↦ f (M.eigvals j)) * Z') * star UM := by rw [hZ'_f]
        _ = (UM * Matrix.diagonal (fun j ↦ f (M.eigvals j)) * star UM) * Z * (UM * star UM) := by
              simp [Z', Matrix.mul_assoc]
        _ = L_M * Z := by rw [hUM_r, Matrix.mul_one]; rfl
    calc Z * L_M * Z = L_M * (Z * Z) := by rw [hZL, Matrix.mul_assoc]
      _ = L_M := by rw [hZZ, Matrix.mul_one]
  have htr_ZA : ((Z * A.mat * Z) * L_M).trace = (A.mat * L_M).trace := by
    calc ((Z * A.mat * Z) * L_M).trace
        = (Z * (A.mat * (Z * L_M))).trace := by simp [Matrix.mul_assoc]
      _ = (A.mat * (Z * L_M) * Z).trace := Matrix.trace_mul_comm _ _
      _ = (A.mat * (Z * L_M * Z)).trace := by simp [Matrix.mul_assoc]
      _ = (A.mat * L_M).trace := by rw [hZL_comm]
  have htr_eq : (A.mat * L_M).trace = (M.mat * L_M).trace := by
    rw [hM_avg, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_add,
        Matrix.trace_smul, Matrix.trace_smul, htr_ZA]
    simp [smul_eq_mul]; ring
  have htr_M : (M.mat * L_M).trace.re / Real.log 2 = -vonNeumannEntropy M := by
    have htr : (M.mat * L_M).trace =
        ∑ j : Bool × d, (M.eigvals j : ℂ) *
          (if M.eigvals j = 0 then (0 : ℂ) else (Real.log (M.eigvals j) : ℂ)) := by
      rw [density_spectral_eq M]
      have h1 : ((M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
          Matrix.diagonal (Complex.ofReal ∘ M.eigvals) *
          star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)) * L_M =
          (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
          (Matrix.diagonal (Complex.ofReal ∘ M.eigvals) *
           Matrix.diagonal (fun j ↦ if M.eigvals j = 0 then (0 : ℂ) else (Real.log (M.eigvals j) : ℂ))) *
          star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) := by
        simp only [L_M, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)),
            Unitary.coe_star_mul_self, Matrix.one_mul]
      rw [h1, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
          Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      rfl
    rw [htr]
    simp only [Complex.re_sum]
    unfold vonNeumannEntropy
    rw [← neg_div, ← Finset.sum_neg_distrib]
    congr 1; apply Finset.sum_congr rfl; intro j _
    by_cases hj : M.eigvals j = 0
    · simp [hj, Real.negMulLog]
    · simp only [hj, ↓reduceIte, ← Complex.ofReal_mul, Complex.ofReal_re, Real.negMulLog]; ring
  rw [relEntropy_eq_trace_log A M (suppSubset_dephaseState_half p hp0 hp1 Ψ), htr_eq, htr_M]
  congr 1; ring

/-- `(relEntropy (dephaseState p ...) (dephaseState (1/2) ...)).toReal = dephaseCoherence p ... Ψ`. -/
theorem relEntropy_dephaseState_toReal_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) :
    (relEntropy (dephaseState p hp0 hp1 Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal =
      dephaseCoherence p hp0 hp1 Ψ := by
  rw [relEntropy_dephaseState_eq p hp0 hp1 Ψ]
  have hnn : 0 ≤ vonNeumannEntropy (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) -
      vonNeumannEntropy (dephaseState p hp0 hp1 Ψ) := by
    have hqjs := dephaseCoherence_eq_qjs p hp0 hp1 Ψ
    have hcond := (condEntropy_mem_Icc
      ({ out := fun b ↦ if b = false then dephaseState p hp0 hp1 Ψ
          else DensityOp.conjUnitary (pauliZTensorI d) (dephaseState p hp0 hp1 Ψ) } :
        CQChannel (Bool × d))).2
    unfold CQChannel.condEntropy at hcond
    unfold dephaseCoherence at hqjs
    simp only [↓reduceIte, Bool.true_eq_false] at hcond
    linarith
  exact ENNReal.toReal_ofReal hnn

/-- **Theorem 1.3 (Nonlinear SDPI for Qubit Dephasing, Relative-Entropy Form)**:
With `C(p) := D((Z_p ⊗ id)(Ψ) ‖ (Z_{1/2} ⊗ id)(Ψ))`, for every bipartite density operator
`Ψ ∈ D(ℂ² ⊗ H_B)` and every `p ∈ [0, 1/2]`,
`C(p) ≤ 1 - h₂(h₂⁻¹(1 - C(0)) * p)`. -/
theorem theorem_1_3_dephasing_sdpi_relEntropy (Ψ : DensityOp (Bool × d))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal ≤
      1 - h2 (binConv (h2Inv (1 -
        (relEntropy (dephaseState 0 le_rfl (by norm_num) Ψ)
          (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal)) p) := by
  rw [relEntropy_dephaseState_toReal_eq, relEntropy_dephaseState_toReal_eq]
  exact theorem_1_3_dephasing_sdpi Ψ hp0 hp1

/-- **Theorem 1.3 (Equatorial Equality, Relative-Entropy Form)**:
Every equatorial single-qubit state `½ (I + x X)` (`x ∈ [0, 1]`) attains equality in
Theorem 1.3 (stated via Umegaki relative entropy) for every `p ∈ [0, 1/2]`. -/
theorem theorem_1_3_equatorial_equality_relEntropy {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1))
      (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal =
      1 - h2 (binConv (h2Inv (1 -
        (relEntropy (dephaseState 0 le_rfl (by norm_num) (equatorialState x hx0 hx1))
          (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal)) p) := by
  rw [relEntropy_dephaseState_toReal_eq, relEntropy_dephaseState_toReal_eq]
  exact theorem_1_3_equatorial_equality hx0 hx1 hp0 hp1

end RelEntropyTheorem13

end PolarCodes
