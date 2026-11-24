/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Polynomial.Roots
import PolarCodes.Channels

/-!
# Spectral Invariance, Tensor Additivity, Entropy Conservation, and Fidelity Evolution

This module establishes the core finite-dimensional operator-algebraic identities used across
Sections 2, 4, and 5:
- Characteristic-polynomial spectral sum invariance (`spectral_sum_eq_of_charpoly_mul_X_pow`)
- Sylvester nonzero-spectrum invariance `S(M M†) = S(M† M)` (`spectral_sum_mul_conjTranspose`)
- Unitary invariance, tensor additivity, and block-diagonal formulas for `vonNeumannEntropy`
  and `rootFidelity`
- **Eq. (2.7)** (`condEntropy_varCombine_eq`) and **Eq. (2.8)** (`entropy_conservation`):
  `H(W₁ ⊠ W₂) + H(W₁ ⊛ W₂) = H(W₁) + H(W₂)`
- **Lemma 5.1(b) (plus channel)**: `Z(W⁺) = Z(W)²` (`fidelityParam_plusChannel`)
-/

open Matrix BigOperators Real Polynomial
open scoped ComplexOrder

namespace PolarCodes

/-! ### Characteristic Polynomial and Nonzero-Spectrum Sum Invariance -/

/-- Characteristic polynomial of a diagonal matrix over `ℂ` equals `∏ i, (X - C (v i))`. -/
lemma charpoly_diagonal_complex {d : Type*} [Fintype d] [DecidableEq d] (v : d → ℂ) :
    (Matrix.diagonal v).charpoly = ∏ i : d, (Polynomial.X - Polynomial.C (v i)) := by
  unfold Matrix.charpoly Matrix.charmatrix
  have hdiag : Matrix.scalar d Polynomial.X - Polynomial.C.mapMatrix (Matrix.diagonal v) =
      Matrix.diagonal (fun i ↦ Polynomial.X - Polynomial.C (v i)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.scalar_apply, Matrix.diagonal_apply]
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply, h]
  rw [hdiag, Matrix.det_diagonal]

/-- Characteristic polynomial of a Hermitian matrix factors over its real eigenvalues. -/
lemma isHermitian_charpoly {d : Type*} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    A.charpoly = ∏ i : d, (Polynomial.X - Polynomial.C (hA.eigenvalues i : ℂ)) := by
  set U : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
  set D : Matrix d d ℂ := Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues)
  have hspec : A = U * D * star U := by
    have h := hA.spectral_theorem
    simpa [U, D, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using h
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  conv_lhs => rw [hspec]
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
    charpoly_diagonal_complex]
  rfl

private lemma roots_charpoly_mul_X_pow {d : Type*} [Fintype d] [DecidableEq d]
    {M : Matrix d d ℂ} (hM : M.IsHermitian) (m : ℕ) :
    (M.charpoly * Polynomial.X ^ m).roots.filter (· ≠ (0 : ℂ)) =
      (Finset.univ.val.map (fun i : d ↦ (hM.eigenvalues i : ℂ))).filter (· ≠ (0 : ℂ)) := by
  have hcpM := isHermitian_charpoly hM
  have hne1 : M.charpoly ≠ 0 := by
    rw [hcpM]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Polynomial.X_sub_C_ne_zero _
  have hne2 : (Polynomial.X : ℂ[X]) ^ m ≠ 0 := pow_ne_zero m Polynomial.X_ne_zero
  rw [Polynomial.roots_mul (mul_ne_zero hne1 hne2), Multiset.filter_add]
  have hX : ((Polynomial.X : ℂ[X]) ^ m).roots.filter (· ≠ (0 : ℂ)) = 0 := by
    rw [Polynomial.roots_X_pow, Multiset.filter_eq_nil]
    intro z hz
    simp only [Multiset.mem_nsmul, Multiset.mem_singleton] at hz
    simp [hz.2]
  rw [hX, add_zero, hcpM]
  have hprod_ne : (∏ i : d, (Polynomial.X - Polynomial.C (hM.eigenvalues i : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ Polynomial.X_sub_C_ne_zero _
  rw [Polynomial.roots_prod _ Finset.univ hprod_ne]
  congr 1
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]

private lemma sum_eq_sum_filter_ne_zero {d : Type*} [Fintype d] [DecidableEq d]
    (v : d → ℝ) {f : ℝ → ℝ} (hf0 : f 0 = 0) :
    ∑ i : d, f (v i) =
      (((Finset.univ.val.map (fun i : d ↦ (v i : ℂ))).filter (· ≠ (0 : ℂ))).map
        (fun z : ℂ ↦ f z.re)).sum := by
  have h1 : ∑ i : d, f (v i) =
      ((Finset.univ.val.map (fun i : d ↦ (v i : ℂ))).map (fun z : ℂ ↦ f z.re)).sum := by
    rw [Multiset.map_map]
    simp only [Function.comp_def, Complex.ofReal_re]
    rfl
  rw [h1]
  have hpart := (Multiset.filter_add_not (fun z : ℂ ↦ z ≠ 0)
    (Finset.univ.val.map (fun i : d ↦ (v i : ℂ)))).symm
  conv_lhs => rw [hpart]
  rw [Multiset.map_add, Multiset.sum_add]
  have hzero : ((Multiset.filter (fun z : ℂ ↦ ¬ z ≠ 0)
      (Finset.univ.val.map (fun i : d ↦ (v i : ℂ)))).map (fun z : ℂ ↦ f z.re)).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro r hr
    rcases Multiset.mem_map.mp hr with ⟨z, hz, rfl⟩
    rw [Multiset.mem_filter] at hz
    have hz0 : z = 0 := not_not.mp hz.2
    rw [hz0, Complex.zero_re, hf0]
  rw [hzero, add_zero]

private lemma charpoly_zero_complex (d : Type*) [Fintype d] [DecidableEq d] :
    (0 : Matrix d d ℂ).charpoly = Polynomial.X ^ (Fintype.card d) := by
  have h0 : (0 : Matrix d d ℂ) = Matrix.diagonal (fun _ : d ↦ (0 : ℂ)) := by
    ext i j; simp [Matrix.diagonal_apply]
  rw [h0, charpoly_diagonal_complex]
  simp [Finset.prod_const]

private lemma charpoly_sqrt_mul_sqrt {d : Type*} [Fintype d] [DecidableEq d] (ρ σ : DensityOp d) :
    (ρ.sqrtMat * σ.mat * ρ.sqrtMat).charpoly = (ρ.mat * σ.mat).charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ρ.sqrtMat_mul_self]

/-- Master nonzero-spectrum invariance theorem: if two Hermitian matrices `A, B` (possibly of
different dimensions `d₁, d₂`) satisfy `A.charpoly * X^k = B.charpoly * X^l`, then for every
function `f : ℝ → ℝ` with `f 0 = 0`, their spectral sums coincide. -/
theorem spectral_sum_eq_of_charpoly_mul_X_pow
    {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    {A : Matrix d₁ d₁ ℂ} {B : Matrix d₂ d₂ ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    {k l : ℕ} (hcp : A.charpoly * Polynomial.X ^ k = B.charpoly * Polynomial.X ^ l)
    {f : ℝ → ℝ} (hf0 : f 0 = 0) :
    ∑ i : d₁, f (hA.eigenvalues i) = ∑ j : d₂, f (hB.eigenvalues j) := by
  have hfilt : (Finset.univ.val.map (fun i : d₁ ↦ (hA.eigenvalues i : ℂ))).filter (· ≠ (0 : ℂ)) =
      (Finset.univ.val.map (fun j : d₂ ↦ (hB.eigenvalues j : ℂ))).filter (· ≠ (0 : ℂ)) := by
    rw [← roots_charpoly_mul_X_pow hA k, ← roots_charpoly_mul_X_pow hB l, hcp]
  rw [sum_eq_sum_filter_ne_zero hA.eigenvalues hf0,
    sum_eq_sum_filter_ne_zero hB.eigenvalues hf0, hfilt]

/-- Sylvester's characteristic polynomial identity for arbitrary rectangular matrices
`M : Matrix d₁ d₂ ℂ`: `(M * Mᴴ).charpoly * X^(|d₂|) = (Mᴴ * M).charpoly * X^(|d₁|)`. -/
lemma charpoly_mul_conjTranspose_eq {d₁ d₂ : Type*}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (M : Matrix d₁ d₂ ℂ) :
    (M * Mᴴ).charpoly * Polynomial.X ^ (Fintype.card d₂) =
      (Mᴴ * M).charpoly * Polynomial.X ^ (Fintype.card d₁) := by
  let P : Matrix (d₁ ⊕ d₂) (d₁ ⊕ d₂) ℂ := Matrix.fromBlocks 0 M 0 0
  let Q : Matrix (d₁ ⊕ d₂) (d₁ ⊕ d₂) ℂ := Matrix.fromBlocks 0 0 Mᴴ 0
  have hPQ : P * Q = Matrix.fromBlocks (M * Mᴴ) 0 0 0 := by
    simp [P, Q, Matrix.fromBlocks_multiply]
  have hQP : Q * P = Matrix.fromBlocks 0 0 0 (Mᴴ * M) := by
    simp [P, Q, Matrix.fromBlocks_multiply]
  have hcomm := Matrix.charpoly_mul_comm P Q
  rw [hPQ, hQP, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_fromBlocks_zero₁₂,
    charpoly_zero_complex d₂, charpoly_zero_complex d₁, mul_comm (Polynomial.X ^ Fintype.card d₁)]
    at hcomm
  exact hcomm

/-- Nonzero-spectrum invariance for `M * Mᴴ` vs `Mᴴ * M` for any rectangular `M : Matrix d₁ d₂ ℂ`. -/
theorem spectral_sum_mul_conjTranspose {d₁ d₂ : Type*}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (M : Matrix d₁ d₂ ℂ)
    (h1 : (M * Mᴴ).IsHermitian := by simp [Matrix.IsHermitian])
    (h2 : (Mᴴ * M).IsHermitian := by simp [Matrix.IsHermitian])
    {f : ℝ → ℝ} (hf0 : f 0 = 0) :
    ∑ i : d₁, f (h1.eigenvalues i) = ∑ j : d₂, f (h2.eigenvalues j) :=
  spectral_sum_eq_of_charpoly_mul_X_pow h1 h2 (charpoly_mul_conjTranspose_eq M) hf0

/-- Spectral sum of a real diagonal Hermitian matrix equals `∑ i, f (v i)`. -/
lemma spectral_sum_diagonal {d : Type*} [Fintype d] [DecidableEq d]
    (v : d → ℝ) (hH : (Matrix.diagonal (Complex.ofReal ∘ v)).IsHermitian)
    {f : ℝ → ℝ} (hf0 : f 0 = 0) :
    ∑ i : d, f (hH.eigenvalues i) = ∑ i : d, f (v i) := by
  have hcp := isHermitian_charpoly hH
  have hcp2 := charpoly_diagonal_complex (Complex.ofReal ∘ v)
  have hroots : (Finset.univ.val.map (fun i : d ↦ (hH.eigenvalues i : ℂ))).filter (· ≠ 0) =
      (Finset.univ.val.map (fun i : d ↦ (v i : ℂ))).filter (· ≠ 0) := by
    have hprod_eq : (∏ i : d, (Polynomial.X - Polynomial.C (hH.eigenvalues i : ℂ))) =
        ∏ i : d, (Polynomial.X - Polynomial.C (v i : ℂ)) := by
      rw [← hcp, hcp2]; rfl
    have hne1 : (∏ i : d, (Polynomial.X - Polynomial.C (hH.eigenvalues i : ℂ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ Polynomial.X_sub_C_ne_zero _
    have hne2 : (∏ i : d, (Polynomial.X - Polynomial.C (v i : ℂ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ Polynomial.X_sub_C_ne_zero _
    have hr := congr_arg Polynomial.roots hprod_eq
    rw [Polynomial.roots_prod _ Finset.univ hne1, Polynomial.roots_prod _ Finset.univ hne2] at hr
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton] at hr
    exact congr_arg (Multiset.filter (· ≠ (0 : ℂ))) hr
  rw [sum_eq_sum_filter_ne_zero hH.eigenvalues hf0,
    sum_eq_sum_filter_ne_zero v hf0, hroots]

/-- Spectral sum of `U * A * star U` equals spectral sum of `A` for any unitary `U`. -/
lemma spectral_sum_conjUnitary {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) {A : Matrix d d ℂ} (hA : A.IsHermitian)
    (hUA : ((U : Matrix d d ℂ) * A * star (U : Matrix d d ℂ)).IsHermitian)
    {f : ℝ → ℝ} (hf0 : f 0 = 0) :
    ∑ i : d, f (hUA.eigenvalues i) = ∑ i : d, f (hA.eigenvalues i) := by
  apply spectral_sum_eq_of_charpoly_mul_X_pow hUA hA (k := 0) (l := 0) _ hf0
  rw [pow_zero, mul_one, mul_one, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self U, Matrix.one_mul]

/-- The eigenvalues of a density operator sum to `1`. -/
lemma DensityOp.sum_eigvals {d : Type*} [Fintype d] [DecidableEq d] (ρ : DensityOp d) :
    ∑ i : d, ρ.eigvals i = 1 := by
  have htr : ρ.mat.trace = ∑ i : d, (ρ.eigvals i : ℂ) := by
    have hspec := ρ.isHermitian.spectral_theorem
    have h1 : ρ.mat = (ρ.eigUnitary : Matrix d d ℂ) *
        Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star (ρ.eigUnitary : Matrix d d ℂ) := by
      simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
        Unitary.conjStarAlgAut_apply] using hspec
    rw [h1, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self ρ.eigUnitary, Matrix.one_mul,
      Matrix.trace_diagonal]
    rfl
  have h1 : (∑ i : d, (ρ.eigvals i : ℂ)) = 1 := by rw [← htr, ρ.trace_one]
  have hre := congr_arg Complex.re h1
  simpa using hre

/-! ### Core Properties of Von Neumann Entropy and QJS -/

lemma vonNeumannEntropy_eq_of_mat_eq {d : Type*} [Fintype d] [DecidableEq d]
    {ρ σ : DensityOp d} (h : ρ.mat = σ.mat) :
    vonNeumannEntropy ρ = vonNeumannEntropy σ := by
  unfold vonNeumannEntropy DensityOp.eigvals
  congr 1
  apply spectral_sum_eq_of_charpoly_mul_X_pow ρ.isHermitian σ.isHermitian (k := 0) (l := 0)
  · rw [h]
  · simp [Real.negMulLog]

lemma vonNeumannEntropy_conjUnitary {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (ρ : DensityOp d) :
    vonNeumannEntropy (DensityOp.conjUnitary U ρ) = vonNeumannEntropy ρ := by
  unfold vonNeumannEntropy DensityOp.eigvals
  congr 1
  exact spectral_sum_conjUnitary U ρ.isHermitian (DensityOp.conjUnitary U ρ).isHermitian
    (by simp [Real.negMulLog])

lemma qjs_symm {d : Type*} [Fintype d] [DecidableEq d] (ρ σ : DensityOp d) :
    qjs ρ σ = qjs σ ρ := by
  unfold qjs
  have hmid : (DensityOp.midpoint ρ σ).mat = (DensityOp.midpoint σ ρ).mat := by
    simp only [DensityOp.midpoint, DensityOp.mix]
    ring_nf; rw [add_comm]
  rw [vonNeumannEntropy_eq_of_mat_eq hmid]
  ring

lemma qjs_conjUnitary {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (ρ σ : DensityOp d) :
    qjs (DensityOp.conjUnitary U ρ) (DensityOp.conjUnitary U σ) = qjs ρ σ := by
  unfold qjs
  rw [vonNeumannEntropy_conjUnitary, vonNeumannEntropy_conjUnitary]
  have hmid : (DensityOp.midpoint (DensityOp.conjUnitary U ρ) (DensityOp.conjUnitary U σ)).mat =
      (DensityOp.conjUnitary U (DensityOp.midpoint ρ σ)).mat := by
    simp only [DensityOp.midpoint, DensityOp.mix, DensityOp.conjUnitary]
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [vonNeumannEntropy_eq_of_mat_eq hmid, vonNeumannEntropy_conjUnitary]

/-- **Tensor additivity of von Neumann entropy**: `S(ρ ⊗ σ) = S(ρ) + S(σ)`. -/
theorem vonNeumannEntropy_tensor {d₁ d₂ : Type*}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ : DensityOp d₁) (σ : DensityOp d₂) :
    vonNeumannEntropy (DensityOp.tensor ρ σ) =
      vonNeumannEntropy ρ + vonNeumannEntropy σ := by
  set U₁ : Matrix d₁ d₁ ℂ := (ρ.eigUnitary : Matrix d₁ d₁ ℂ)
  set U₂ : Matrix d₂ d₂ ℂ := (σ.eigUnitary : Matrix d₂ d₂ ℂ)
  set D₁ : Matrix d₁ d₁ ℂ := Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals)
  set D₂ : Matrix d₂ d₂ ℂ := Matrix.diagonal (Complex.ofReal ∘ σ.eigvals)
  have hspec₁ : ρ.mat = U₁ * D₁ * star U₁ := by
    simpa [U₁, D₁, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
  have hspec₂ : σ.mat = U₂ * D₂ * star U₂ := by
    simpa [U₂, D₂, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
  let U : Matrix (d₁ × d₂) (d₁ × d₂) ℂ := Matrix.kroneckerMap (· * ·) U₁ U₂
  have hU_star : star U = Matrix.kroneckerMap (· * ·) (star U₁) (star U₂) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp [U, Matrix.star_apply, Matrix.kroneckerMap_apply, star_mul, mul_comm]
  have hU_mul : star U * U = 1 := by
    rw [hU_star, ← Matrix.mul_kronecker_mul, Unitary.coe_star_mul_self ρ.eigUnitary,
      Unitary.coe_star_mul_self σ.eigUnitary, Matrix.one_kronecker_one]
  have hD_eq : Matrix.kroneckerMap (· * ·) D₁ D₂ =
      Matrix.diagonal (Complex.ofReal ∘ fun p : d₁ × d₂ ↦ ρ.eigvals p.1 * σ.eigvals p.2) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [D₁, D₂, Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Function.comp_apply]
    by_cases h1 : i₁ = j₁ <;> by_cases h2 : i₂ = j₂ <;> simp [h1, h2]
  have htensor : (DensityOp.tensor ρ σ).mat =
      U * Matrix.diagonal (Complex.ofReal ∘ fun p : d₁ × d₂ ↦ ρ.eigvals p.1 * σ.eigvals p.2) *
        star U := by
    simp only [DensityOp.tensor, hspec₁, hspec₂, U, hU_star, ← hD_eq]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  have hcp : (DensityOp.tensor ρ σ).mat.charpoly =
      (Matrix.diagonal (Complex.ofReal ∘ fun p : d₁ × d₂ ↦ ρ.eigvals p.1 * σ.eigvals p.2)).charpoly := by
    rw [htensor, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU_mul, Matrix.one_mul]
  have hD_herm : (Matrix.diagonal (Complex.ofReal ∘
      fun p : d₁ × d₂ ↦ ρ.eigvals p.1 * σ.eigvals p.2)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1; ext p; simp
  have hsum : ∑ p : d₁ × d₂, Real.negMulLog ((DensityOp.tensor ρ σ).eigvals p) =
      ∑ p : d₁ × d₂, Real.negMulLog (ρ.eigvals p.1 * σ.eigvals p.2) := by
    trans ∑ p : d₁ × d₂, Real.negMulLog (hD_herm.eigenvalues p)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow (DensityOp.tensor ρ σ).isHermitian hD_herm
        (k := 0) (l := 0) (by rw [pow_zero, mul_one, mul_one, hcp]) (by simp [Real.negMulLog])
    · exact spectral_sum_diagonal (fun p : d₁ × d₂ ↦ ρ.eigvals p.1 * σ.eigvals p.2)
        hD_herm (by simp [Real.negMulLog])
  unfold vonNeumannEntropy
  rw [hsum, ← add_div]
  congr 1
  rw [Fintype.sum_prod_type]
  have hmul : ∀ i j, Real.negMulLog (ρ.eigvals i * σ.eigvals j) =
      Real.negMulLog (ρ.eigvals i) * σ.eigvals j + ρ.eigvals i * Real.negMulLog (σ.eigvals j) := by
    intro i j
    rw [Real.negMulLog_mul]
    ring
  simp_rw [hmul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    ρ.sum_eigvals, σ.sum_eigvals, mul_one, one_mul]

/-- **Block-diagonal entropy**:
`S(½ |0⟩⟨0| ⊗ ρ₀ + ½ |1⟩⟨1| ⊗ ρ₁) = 1 + ½ (S(ρ₀) + S(ρ₁))`. -/
theorem vonNeumannEntropy_block_midpoint {d : Type*} [Fintype d] [DecidableEq d]
    (ρ₀ ρ₁ : DensityOp d) :
    vonNeumannEntropy (DensityOp.midpoint
      (DensityOp.tensor (CQChannel.ketBraBool false) ρ₀)
      (DensityOp.tensor (CQChannel.ketBraBool true) ρ₁)) =
      1 + (vonNeumannEntropy ρ₀ + vonNeumannEntropy ρ₁) / 2 := by
  set M := DensityOp.midpoint
    (DensityOp.tensor (CQChannel.ketBraBool false) ρ₀)
    (DensityOp.tensor (CQChannel.ketBraBool true) ρ₁)
  set U₀ : Matrix d d ℂ := (ρ₀.eigUnitary : Matrix d d ℂ)
  set U₁ : Matrix d d ℂ := (ρ₁.eigUnitary : Matrix d d ℂ)
  let U : Matrix (Bool × d) (Bool × d) ℂ := Matrix.of fun p q ↦
    if p.1 = q.1 then (if p.1 = false then U₀ p.2 q.2 else U₁ p.2 q.2) else 0
  let lam : Bool × d → ℝ := fun p ↦ if p.1 = false then ρ₀.eigvals p.2 / 2 else ρ₁.eigvals p.2 / 2
  have hU_star_mul : star U * U = 1 := by
    ext ⟨b₁, i₁⟩ ⟨b₂, i₂⟩
    simp only [U, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fintype.sum_bool]
    cases b₁ <;> cases b₂
    · simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, star_zero, mul_zero, zero_mul,
        zero_add, add_zero, Finset.sum_const_zero, Prod.mk.injEq, true_and]
      have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ₀.eigUnitary) i₁) i₂
      simpa [U₀, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h
    · simp
    · simp
    · simp only [Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte, star_zero, mul_zero, zero_mul,
        zero_add, add_zero, Finset.sum_const_zero, Prod.mk.injEq, true_and]
      have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ₁.eigUnitary) i₁) i₂
      simpa [U₁, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h
  have hspec₀ : ρ₀.mat = U₀ * Matrix.diagonal (Complex.ofReal ∘ ρ₀.eigvals) * star U₀ := by
    simpa [U₀, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using ρ₀.isHermitian.spectral_theorem
  have hspec₁ : ρ₁.mat = U₁ * Matrix.diagonal (Complex.ofReal ∘ ρ₁.eigvals) * star U₁ := by
    simpa [U₁, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using ρ₁.isHermitian.spectral_theorem
  have hM_eq : M.mat = U * Matrix.diagonal (Complex.ofReal ∘ lam) * star U := by
    ext ⟨b₁, i₁⟩ ⟨b₂, i₂⟩
    simp only [M, U, lam, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, CQChannel.ketBraBool,
      Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.of_apply,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, Function.comp_apply,
      Fintype.sum_prod_type, Fintype.sum_bool, smul_eq_mul]
    cases b₁ <;> cases b₂
    · simp only [↓reduceIte, and_self, one_mul, Bool.false_eq_true, Bool.true_eq_false,
        Prod.mk.injEq, true_and, false_and, ite_false, ite_true, zero_mul, mul_zero, smul_zero,
        star_zero, add_zero, zero_add, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ]
      have h := congr_fun (congr_fun hspec₀ i₁) i₂
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
        Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
      rw [h, Complex.real_smul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      push_cast; ring
    · simp
    · simp
    · simp only [Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte, and_self,
        Prod.mk.injEq, true_and, false_and, ite_false, ite_true, zero_mul, mul_zero, smul_zero,
        star_zero, add_zero, zero_add, one_mul, Finset.sum_const_zero, Finset.sum_ite_eq',
        Finset.mem_univ]
      have h := congr_fun (congr_fun hspec₁ i₁) i₂
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
        Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
      rw [h, Complex.real_smul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      push_cast; ring
  have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1; ext p; simp
  have hcp : M.mat.charpoly = (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
    rw [hM_eq, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU_star_mul, Matrix.one_mul]
  have hsum : ∑ p : Bool × d, Real.negMulLog (M.eigvals p) = ∑ p : Bool × d, Real.negMulLog (lam p) := by
    trans ∑ p : Bool × d, Real.negMulLog (hD_herm.eigenvalues p)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow M.isHermitian hD_herm (k := 0) (l := 0)
        (by rw [pow_zero, mul_one, mul_one, hcp]) (by simp [Real.negMulLog])
    · exact spectral_sum_diagonal lam hD_herm (by simp [Real.negMulLog])
  unfold vonNeumannEntropy
  rw [hsum, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [lam, ↓reduceIte, Bool.true_eq_false]
  have hhalf : ∀ x : ℝ, Real.negMulLog (x / 2) =
      Real.negMulLog x / 2 + x * Real.log 2 / 2 := by
    intro x
    rw [div_eq_mul_inv, Real.negMulLog_mul]
    unfold Real.negMulLog
    rw [Real.log_inv]
    ring
  simp_rw [hhalf, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    ρ₀.sum_eigvals, ρ₁.sum_eigvals, one_mul]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog2]
  ring

/-! ### Equations (2.7) and (2.8): Variable-Node Entropy & Conservation of Entropy -/

/-- **Eq. (2.7)**: Conditional entropy of `W₁ ⊛ W₂` equals the average of its two `U₁`-branches. -/
theorem condEntropy_varCombine_eq {d₁ d₂ : Type*}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    (CQChannel.varCombine W₁ W₂).condEntropy =
      (1 - qjs (DensityOp.tensor (W₁.out false) (W₂.out false))
        (DensityOp.tensor (W₁.out true) (W₂.out true))) / 2 +
      (1 - qjs (DensityOp.tensor (W₁.out true) (W₂.out false))
        (DensityOp.tensor (W₁.out false) (W₂.out true))) / 2 := by
  unfold CQChannel.condEntropy CQChannel.varCombine qjs
  simp only [Bool.not_false, Bool.not_true]
  have hmid_eq : (DensityOp.midpoint
      (DensityOp.midpoint
        (DensityOp.tensor (CQChannel.ketBraBool false) (DensityOp.tensor (W₁.out false) (W₂.out false)))
        (DensityOp.tensor (CQChannel.ketBraBool true) (DensityOp.tensor (W₁.out true) (W₂.out false))))
      (DensityOp.midpoint
        (DensityOp.tensor (CQChannel.ketBraBool false) (DensityOp.tensor (W₁.out true) (W₂.out true)))
        (DensityOp.tensor (CQChannel.ketBraBool true) (DensityOp.tensor (W₁.out false) (W₂.out true))))).mat =
    (DensityOp.midpoint
      (DensityOp.tensor (CQChannel.ketBraBool false)
        (DensityOp.midpoint (DensityOp.tensor (W₁.out false) (W₂.out false))
          (DensityOp.tensor (W₁.out true) (W₂.out true))))
      (DensityOp.tensor (CQChannel.ketBraBool true)
        (DensityOp.midpoint (DensityOp.tensor (W₁.out true) (W₂.out false))
          (DensityOp.tensor (W₁.out false) (W₂.out true))))).mat := by
    ext ⟨b₁, i₁, i₂⟩ ⟨c₁, j₁, j₂⟩
    simp only [DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, Matrix.add_apply,
      Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul]
    push_cast; ring
  rw [vonNeumannEntropy_eq_of_mat_eq hmid_eq,
    vonNeumannEntropy_block_midpoint,
    vonNeumannEntropy_block_midpoint,
    vonNeumannEntropy_block_midpoint]
  ring

/-- **Eq. (2.8) (Conservation of Entropy)**:
`H(W₁ ⊠ W₂) + H(W₁ ⊛ W₂) = H(W₁) + H(W₂)` for all independent binary-input c-q channels `W₁, W₂`. -/
theorem entropy_conservation {d₁ d₂ : Type*}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    (CQChannel.checkCombine W₁ W₂).condEntropy + (CQChannel.varCombine W₁ W₂).condEntropy =
      W₁.condEntropy + W₂.condEntropy := by
  rw [condEntropy_varCombine_eq]
  unfold CQChannel.condEntropy CQChannel.checkCombine qjs
  simp only [Bool.not_false, Bool.not_true]
  have hmid_check : (DensityOp.midpoint
      (DensityOp.midpoint (DensityOp.tensor (W₁.out false) (W₂.out false))
        (DensityOp.tensor (W₁.out true) (W₂.out true)))
      (DensityOp.midpoint (DensityOp.tensor (W₁.out true) (W₂.out false))
        (DensityOp.tensor (W₁.out false) (W₂.out true)))).mat =
    (DensityOp.tensor (DensityOp.midpoint (W₁.out false) (W₁.out true))
      (DensityOp.midpoint (W₂.out false) (W₂.out true))).mat := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, Matrix.add_apply,
      Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul]
    push_cast; ring
  rw [vonNeumannEntropy_eq_of_mat_eq hmid_check,
    vonNeumannEntropy_tensor, vonNeumannEntropy_tensor, vonNeumannEntropy_tensor,
    vonNeumannEntropy_tensor, vonNeumannEntropy_tensor]
  ring

/-! ### Core Properties of Root Fidelity and Lemma 5.1(b) (`Z(W⁺) = Z(W)²`) -/

lemma rootFidelity_eq_of_mat_eq {d : Type*} [Fintype d] [DecidableEq d]
    {ρ₁ ρ₂ σ₁ σ₂ : DensityOp d} (hρ : ρ₁.mat = ρ₂.mat) (hσ : σ₁.mat = σ₂.mat) :
    rootFidelity ρ₁ σ₁ = rootFidelity ρ₂ σ₂ := by
  have hρeq : ρ₁ = ρ₂ := by cases ρ₁; cases ρ₂; congr
  have hσeq : σ₁ = σ₂ := by cases σ₁; cases σ₂; congr
  rw [hρeq, hσeq]

/-- Symmetry of Uhlmann root fidelity: `F(ρ, σ) = F(σ, ρ)`. -/
lemma rootFidelity_symm {d : Type*} [Fintype d] [DecidableEq d] (ρ σ : DensityOp d) :
    rootFidelity ρ σ = rootFidelity σ ρ := by
  unfold rootFidelity
  have h1 : ρ.sqrtMat * σ.mat * ρ.sqrtMat = (ρ.sqrtMat * σ.sqrtMat) * (ρ.sqrtMat * σ.sqrtMat)ᴴ := by
    rw [Matrix.conjTranspose_mul, ρ.sqrtMat_isHermitian.eq, σ.sqrtMat_isHermitian.eq,
      ← σ.sqrtMat_mul_self]
    simp only [Matrix.mul_assoc]
  have h2 : σ.sqrtMat * ρ.mat * σ.sqrtMat = (ρ.sqrtMat * σ.sqrtMat)ᴴ * (ρ.sqrtMat * σ.sqrtMat) := by
    rw [Matrix.conjTranspose_mul, ρ.sqrtMat_isHermitian.eq, σ.sqrtMat_isHermitian.eq,
      ← ρ.sqrtMat_mul_self]
    simp only [Matrix.mul_assoc]
  have hcp := charpoly_mul_conjTranspose_eq (ρ.sqrtMat * σ.sqrtMat)
  rw [← h1, ← h2] at hcp
  exact spectral_sum_eq_of_charpoly_mul_X_pow
    (posSemidef_sqrt_mul_sqrt ρ σ).isHermitian
    (posSemidef_sqrt_mul_sqrt σ ρ).isHermitian hcp Real.sqrt_zero

/-- Multiplicativity of root fidelity under tensor products:
`F(ρ₁ ⊗ ρ₂, σ₁ ⊗ σ₂) = F(ρ₁, σ₁) * F(ρ₂, σ₂)`. -/
theorem rootFidelity_tensor {d₁ d₂ : Type*}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ₁ σ₁ : DensityOp d₁) (ρ₂ σ₂ : DensityOp d₂) :
    rootFidelity (DensityOp.tensor ρ₁ ρ₂) (DensityOp.tensor σ₁ σ₂) =
      rootFidelity ρ₁ σ₁ * rootFidelity ρ₂ σ₂ := by
  set A₁ := ρ₁.sqrtMat * σ₁.mat * ρ₁.sqrtMat
  set A₂ := ρ₂.sqrtMat * σ₂.mat * ρ₂.sqrtMat
  have hA₁ := (posSemidef_sqrt_mul_sqrt ρ₁ σ₁).isHermitian
  have hA₂ := (posSemidef_sqrt_mul_sqrt ρ₂ σ₂).isHermitian
  set U₁ : Matrix d₁ d₁ ℂ := (hA₁.eigenvectorUnitary : Matrix d₁ d₁ ℂ)
  set U₂ : Matrix d₂ d₂ ℂ := (hA₂.eigenvectorUnitary : Matrix d₂ d₂ ℂ)
  let U : Matrix (d₁ × d₂) (d₁ × d₂) ℂ := Matrix.kroneckerMap (· * ·) U₁ U₂
  have hU_star : star U = Matrix.kroneckerMap (· * ·) (star U₁) (star U₂) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp [U, Matrix.star_apply, Matrix.kroneckerMap_apply, star_mul, mul_comm]
  have hU_mul : star U * U = 1 := by
    rw [hU_star, ← Matrix.mul_kronecker_mul, Unitary.coe_star_mul_self hA₁.eigenvectorUnitary,
      Unitary.coe_star_mul_self hA₂.eigenvectorUnitary, Matrix.one_kronecker_one]
  let lam : d₁ × d₂ → ℝ := fun p ↦ hA₁.eigenvalues p.1 * hA₂.eigenvalues p.2
  have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext p; simp
  have hK_eq : Matrix.kroneckerMap (· * ·) A₁ A₂ =
      U * Matrix.diagonal (Complex.ofReal ∘ lam) * star U := by
    have hs1 : A₁ = U₁ * Matrix.diagonal (Complex.ofReal ∘ hA₁.eigenvalues) * star U₁ := by
      simpa [U₁, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA₁.spectral_theorem
    have hs2 : A₂ = U₂ * Matrix.diagonal (Complex.ofReal ∘ hA₂.eigenvalues) * star U₂ := by
      simpa [U₂, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA₂.spectral_theorem
    have hD : Matrix.kroneckerMap (· * ·)
        (Matrix.diagonal (Complex.ofReal ∘ hA₁.eigenvalues))
        (Matrix.diagonal (Complex.ofReal ∘ hA₂.eigenvalues)) =
        Matrix.diagonal (Complex.ofReal ∘ lam) := by
      ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
      simp only [Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Function.comp_apply, lam]
      by_cases h1 : i₁ = j₁ <;> by_cases h2 : i₂ = j₂ <;> simp [h1, h2]
    rw [hs1, hs2, ← hD]
    simp only [U, hU_star, ← Matrix.mul_kronecker_mul]
  have hcp_eq : ((DensityOp.tensor ρ₁ ρ₂).sqrtMat * (DensityOp.tensor σ₁ σ₂).mat *
      (DensityOp.tensor ρ₁ ρ₂).sqrtMat).charpoly =
      (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
    rw [charpoly_sqrt_mul_sqrt]
    have hK_AB : (DensityOp.tensor ρ₁ ρ₂).mat * (DensityOp.tensor σ₁ σ₂).mat =
        Matrix.kroneckerMap (· * ·) (ρ₁.mat * σ₁.mat) (ρ₂.mat * σ₂.mat) := by
      simp only [DensityOp.tensor, ← Matrix.mul_kronecker_mul]
    rw [hK_AB]
    have hK_sqrt : Matrix.kroneckerMap (· * ·) A₁ A₂ =
        Matrix.kroneckerMap (· * ·) ρ₁.sqrtMat ρ₂.sqrtMat *
          Matrix.kroneckerMap (· * ·) σ₁.mat σ₂.mat *
          Matrix.kroneckerMap (· * ·) ρ₁.sqrtMat ρ₂.sqrtMat := by
      simp only [A₁, A₂, ← Matrix.mul_kronecker_mul]
    have hcp_K : (Matrix.kroneckerMap (· * ·) A₁ A₂).charpoly =
        (Matrix.kroneckerMap (· * ·) (ρ₁.mat * σ₁.mat) (ρ₂.mat * σ₂.mat)).charpoly := by
      rw [hK_sqrt, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul,
        ρ₁.sqrtMat_mul_self, ρ₂.sqrtMat_mul_self, ← Matrix.mul_kronecker_mul]
    rw [← hcp_K, hK_eq, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU_mul, Matrix.one_mul]
  unfold rootFidelity
  trans ∑ p : d₁ × d₂, Real.sqrt (lam p)
  · trans ∑ p : d₁ × d₂, Real.sqrt (hD_herm.eigenvalues p)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow
        (posSemidef_sqrt_mul_sqrt (DensityOp.tensor ρ₁ ρ₂) (DensityOp.tensor σ₁ σ₂)).isHermitian
        hD_herm (k := 0) (l := 0) (by rw [pow_zero, mul_one, mul_one, hcp_eq]) Real.sqrt_zero
    · exact spectral_sum_diagonal lam hD_herm Real.sqrt_zero
  · rw [Fintype.sum_prod_type]
    have hnn₁ : ∀ i, 0 ≤ hA₁.eigenvalues i := (posSemidef_sqrt_mul_sqrt ρ₁ σ₁).eigenvalues_nonneg
    simp_rw [lam, Real.sqrt_mul (hnn₁ _), ← Finset.mul_sum, ← Finset.sum_mul]

/-- Additivity of root fidelity over orthogonal classical blocks:
`F(½ |0⟩⟨0| ⊗ ρ₀ + ½ |1⟩⟨1| ⊗ ρ₁, ½ |0⟩⟨0| ⊗ σ₀ + ½ |1⟩⟨1| ⊗ σ₁) = ½ F(ρ₀, σ₀) + ½ F(ρ₁, σ₁)`. -/
theorem rootFidelity_block_midpoint {d : Type*} [Fintype d] [DecidableEq d]
    (ρ₀ ρ₁ σ₀ σ₁ : DensityOp d) :
    rootFidelity
      (DensityOp.midpoint
        (DensityOp.tensor (CQChannel.ketBraBool false) ρ₀)
        (DensityOp.tensor (CQChannel.ketBraBool true) ρ₁))
      (DensityOp.midpoint
        (DensityOp.tensor (CQChannel.ketBraBool false) σ₀)
        (DensityOp.tensor (CQChannel.ketBraBool true) σ₁)) =
      (rootFidelity ρ₀ σ₀ + rootFidelity ρ₁ σ₁) / 2 := by
  set R := DensityOp.midpoint
    (DensityOp.tensor (CQChannel.ketBraBool false) ρ₀)
    (DensityOp.tensor (CQChannel.ketBraBool true) ρ₁)
  set S := DensityOp.midpoint
    (DensityOp.tensor (CQChannel.ketBraBool false) σ₀)
    (DensityOp.tensor (CQChannel.ketBraBool true) σ₁)
  set A₀ := ρ₀.sqrtMat * σ₀.mat * ρ₀.sqrtMat
  set A₁ := ρ₁.sqrtMat * σ₁.mat * ρ₁.sqrtMat
  have hA₀ := (posSemidef_sqrt_mul_sqrt ρ₀ σ₀).isHermitian
  have hA₁ := (posSemidef_sqrt_mul_sqrt ρ₁ σ₁).isHermitian
  let lam : Bool × d → ℝ := fun p ↦
    if p.1 = false then hA₀.eigenvalues p.2 / 4 else hA₁.eigenvalues p.2 / 4
  have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext p; simp
  let e : (Bool × d) ≃ (d ⊕ d) :=
    { toFun := fun p ↦ if p.1 = false then Sum.inl p.2 else Sum.inr p.2
      invFun := fun s ↦ match s with | Sum.inl i => (false, i) | Sum.inr i => (true, i)
      left_inv := fun ⟨b, i⟩ ↦ by cases b <;> rfl
      right_inv := fun s ↦ by cases s <;> rfl }
  have hRS_block : (R.mat * S.mat).reindex e e =
      Matrix.fromBlocks (((1 / 4 : ℝ) : ℂ) • (ρ₀.mat * σ₀.mat)) 0 0
        (((1 / 4 : ℝ) : ℂ) • (ρ₁.mat * σ₁.mat)) := by
    ext s₁ s₂
    cases s₁ with
    | inl i =>
      cases s₂ with
      | inl j =>
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
          e, Equiv.coe_fn_symm_mk, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
          R, S, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, CQChannel.ketBraBool,
          Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.of_apply,
          ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, and_self, true_and, and_true,
          false_and, and_false, ite_false, ite_true, one_mul, zero_mul, smul_zero, add_zero,
          zero_add, mul_zero, Finset.sum_const_zero, smul_eq_mul, Complex.real_smul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; push_cast; ring
      | inr j =>
        simp [e, R, S, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, CQChannel.ketBraBool,
          Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool]
    | inr i =>
      cases s₂ with
      | inl j =>
        simp [e, R, S, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, CQChannel.ketBraBool,
          Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool]
      | inr j =>
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂,
          e, Equiv.coe_fn_symm_mk, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
          R, S, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, CQChannel.ketBraBool,
          Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.of_apply,
          ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, and_self, true_and, and_true,
          false_and, and_false, ite_false, ite_true, one_mul, zero_mul, smul_zero, zero_add,
          add_zero, mul_zero, Finset.sum_const_zero, smul_eq_mul, Complex.real_smul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; push_cast; ring
  have hD_block : (Matrix.diagonal (Complex.ofReal ∘ lam)).reindex e e =
      Matrix.fromBlocks (Matrix.diagonal (fun i ↦ ((hA₀.eigenvalues i / 4 : ℝ) : ℂ))) 0 0
        (Matrix.diagonal (fun i ↦ ((hA₁.eigenvalues i / 4 : ℝ) : ℂ))) := by
    ext s₁ s₂
    cases s₁ <;> cases s₂ <;> simp [e, lam, Matrix.diagonal_apply]
  have hcp_smul : ∀ (ρ σ : DensityOp d) (hA : (ρ.sqrtMat * σ.mat * ρ.sqrtMat).IsHermitian),
      (((1 / 4 : ℝ) : ℂ) • (ρ.mat * σ.mat)).charpoly =
        (Matrix.diagonal (fun i ↦ ((hA.eigenvalues i / 4 : ℝ) : ℂ))).charpoly := by
    intro ρ σ hA
    have h1 : (((1 / 4 : ℝ) : ℂ) • (ρ.mat * σ.mat)).charpoly =
        (((1 / 4 : ℝ) : ℂ) • (ρ.sqrtMat * σ.mat * ρ.sqrtMat)).charpoly := by
      have hsq : ((1 / 4 : ℝ) : ℂ) • (ρ.sqrtMat * σ.mat * ρ.sqrtMat) =
          (((1 / 4 : ℝ) : ℂ) • (ρ.sqrtMat * σ.mat)) * ρ.sqrtMat := by
        simp [Matrix.smul_mul]
      rw [hsq, Matrix.charpoly_mul_comm, Matrix.mul_smul, ← Matrix.mul_assoc, ρ.sqrtMat_mul_self]
    rw [h1]
    set U : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
    have hspec : ρ.sqrtMat * σ.mat * ρ.sqrtMat =
        U * Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) * star U := by
      simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
    conv_lhs => rw [hspec]
    rw [← Matrix.smul_mul, Matrix.charpoly_mul_comm, Matrix.mul_smul, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self hA.eigenvectorUnitary, Matrix.one_mul]
    congr 1
    ext i j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply, smul_eq_mul]
    split_ifs <;> [· push_cast; ring; · simp]
  have hcp : (R.sqrtMat * S.mat * R.sqrtMat).charpoly =
      (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
    rw [charpoly_sqrt_mul_sqrt, ← Matrix.charpoly_reindex e (R.mat * S.mat),
      ← Matrix.charpoly_reindex e (Matrix.diagonal (Complex.ofReal ∘ lam)),
      hRS_block, hD_block, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_fromBlocks_zero₁₂,
      hcp_smul ρ₀ σ₀ hA₀, hcp_smul ρ₁ σ₁ hA₁]
  unfold rootFidelity
  trans ∑ p : Bool × d, Real.sqrt (lam p)
  · trans ∑ p : Bool × d, Real.sqrt (hD_herm.eigenvalues p)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow (posSemidef_sqrt_mul_sqrt R S).isHermitian
        hD_herm (k := 0) (l := 0) (by rw [pow_zero, mul_one, mul_one, hcp]) Real.sqrt_zero
    · exact spectral_sum_diagonal lam hD_herm Real.sqrt_zero
  · rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [lam, ↓reduceIte, Bool.true_eq_false]
    have h4 : ∀ x : ℝ, Real.sqrt (x / 4) = Real.sqrt x / 2 := by
      intro x
      rw [Real.sqrt_div' x (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    simp_rw [h4, ← Finset.sum_div, add_div]
    rw [add_comm]

/-- **Lemma 5.1(b) (plus channel)**: `Z(W⁺) = Z(W)²` for every binary-input c-q channel `W`. -/
theorem fidelityParam_plusChannel {d : Type*} [Fintype d] [DecidableEq d] (W : CQChannel d) :
    (CQChannel.plusChannel W).fidelityParam = W.fidelityParam ^ 2 := by
  unfold CQChannel.fidelityParam CQChannel.plusChannel CQChannel.varCombine
  simp only [Bool.not_false, Bool.not_true]
  rw [rootFidelity_block_midpoint, rootFidelity_tensor, rootFidelity_tensor,
    rootFidelity_symm (W.out true) (W.out false)]
  ring

end PolarCodes
