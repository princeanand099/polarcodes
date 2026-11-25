/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.Bhattacharyya
import PolarCodes.QuantumProps

/-!
# Binary Helstrom Bound, Powers–Størmer Inequality, and Noncommutative Union Bound

This module establishes the operator-theoretic ingredients for the Quantum Successive-Cancellation
(QSC) polar decoder and Wilde–Guha's error bound ([12, Proposition 4]):
- `helstromProjector`: the positive spectral projector `Π = {ρ₀ - ρ₁ ≥ 0}` of `ρ₀ - ρ₁`
- `powers_stormer_traceNorm`: Powers–Størmer inequality `2 - 2 Re Tr(√ρ₀ √ρ₁) ≤ ‖ρ₀ - ρ₁‖₁`
- `helstrom_error_le_fidelity`: Holevo–Helstrom bound
  `(1 / 2) (Tr((1 - Π) ρ₀) + Tr(Π ρ₁)) ≤ (1 / 2) F(ρ₀, ρ₁)`
- `gao_union_bound_density`: Gao's sharp quantum union bound
  `1 - Tr(P_m ⋯ P_1 ρ P_1 ⋯ P_m) ≤ 4 ∑_k Tr((1 - P_k) ρ)` (via the O'Donnell–Venkateswaran proof)
- `sen_noncommutative_union_bound`: Sen's noncommutative union bound
  `1 - Tr(P_m ⋯ P_1 ρ P_1 ⋯ P_m) ≤ 2 √(∑_k Tr((1 - P_k) ρ))`
- `vonNeumannEntropy_of_reindex` and `rootFidelity_of_reindex`: invariance of von Neumann entropy
  and root fidelity under basis bijections `e : α ≃ β`.
-/

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodes

universe u

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-! ### Orthogonal Projectors and Density-Operator Square-Root Positivity -/

/-- An orthogonal projector `P` on `ℂ^α`: Hermitian (`Pᴴ = P`) and idempotent (`P * P = P`). -/
def IsProjector (P : Matrix α α ℂ) : Prop :=
  Pᴴ = P ∧ P * P = P

lemma isProjector_one : IsProjector (1 : Matrix α α ℂ) :=
  ⟨Matrix.conjTranspose_one, Matrix.one_mul 1⟩

lemma IsProjector.sub_one {P : Matrix α α ℂ} (hP : IsProjector P) : IsProjector (1 - P) := by
  refine ⟨?_, ?_⟩
  · simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.1]
  · simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, hP.2]

lemma IsProjector.posSemidef {P : Matrix α α ℂ} (hP : IsProjector P) : P.PosSemidef := by
  have : P = Pᴴ * P := by rw [hP.1, hP.2]
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self P

lemma DensityOp.sqrtMat_posSemidef (ρ : DensityOp α) : ρ.sqrtMat.PosSemidef := by
  let U : Matrix α α ℂ := (ρ.eigUnitary : Matrix α α ℂ)
  let A : Matrix α α ℂ :=
    Matrix.diagonal (fun i : α ↦ (Real.sqrt (Real.sqrt (ρ.eigvals i)) : ℂ)) * star U
  have hA : Aᴴ * A = ρ.sqrtMat := by
    have hd : (Matrix.diagonal (fun i : α ↦ (Real.sqrt (Real.sqrt (ρ.eigvals i)) : ℂ)))ᴴ =
        Matrix.diagonal (fun i : α ↦ (Real.sqrt (Real.sqrt (ρ.eigvals i)) : ℂ)) := by
      ext i j; by_cases h : i = j
      · subst h; simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]
      · simp [h, Ne.symm h, Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne]
    have hmul : Matrix.diagonal (fun i : α ↦ (Real.sqrt (Real.sqrt (ρ.eigvals i)) : ℂ)) *
        Matrix.diagonal (fun i : α ↦ (Real.sqrt (Real.sqrt (ρ.eigvals i)) : ℂ)) =
        Matrix.diagonal (fun i : α ↦ (Real.sqrt (ρ.eigvals i) : ℂ)) := by
      rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Real.sqrt_nonneg _)]
    calc Aᴴ * A = U * (Matrix.diagonal (fun i : α ↦ (Real.sqrt (Real.sqrt (ρ.eigvals i)) : ℂ)) *
            Matrix.diagonal (fun i : α ↦ (Real.sqrt (Real.sqrt (ρ.eigvals i)) : ℂ))) * star U := by
              simp only [A, Matrix.conjTranspose_mul, hd, Matrix.star_eq_conjTranspose,
                Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = U * Matrix.diagonal (fun i : α ↦ (Real.sqrt (ρ.eigvals i) : ℂ)) * star U := by rw [hmul]
      _ = ρ.sqrtMat := rfl
  rw [← hA]
  exact Matrix.posSemidef_conjTranspose_mul_self A

private lemma posSemidef_diag_re_nonneg {M : Matrix α α ℂ} (hM : M.PosSemidef) (i : α) :
    0 ≤ (M i i).re := by
  set V : Matrix α α ℂ := (hM.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
  have hspec : M = V * Matrix.diagonal (Complex.ofReal ∘ hM.isHermitian.eigenvalues) * star V := by
    simpa [V, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM.isHermitian.spectral_theorem
  have hval : M i i = ∑ k : α, ((hM.isHermitian.eigenvalues k : ℝ) : ℂ) * (V i k * star (V i k)) := by
    conv_lhs => rw [hspec]
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro k _
    rw [Matrix.mul_diagonal, Matrix.star_apply, Function.comp_apply]
    ring
  rw [hval, Complex.re_sum]
  apply Finset.sum_nonneg; intro k _
  have hnorm : V i k * star (V i k) = ((‖V i k‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hnorm, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (hM.eigenvalues_nonneg k) (sq_nonneg _)

/-! ### Trace Norm of Hermitian Matrices and Helstrom Projector -/

private lemma traceNorm_hermitian_eq_sum_abs {Δ : Matrix α α ℂ} (hΔ : Δ.IsHermitian) :
    traceNorm Δ = ∑ i : α, |hΔ.eigenvalues i| := by
  set U : Matrix α α ℂ := (hΔ.eigenvectorUnitary : Matrix α α ℂ)
  have hspec : Δ = U * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues) * star U := by
    simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hΔ.spectral_theorem
  have hU_mul : U * star U = 1 := Unitary.coe_mul_star_self hΔ.eigenvectorUnitary
  have hU_star : star U * U = 1 := Unitary.coe_star_mul_self hΔ.eigenvectorUnitary
  let sgn : α → ℂ := fun i ↦ if 0 ≤ hΔ.eigenvalues i then 1 else -1
  let S : Matrix α α ℂ := U * Matrix.diagonal sgn * star U
  have hS_herm : Sᴴ = S := by
    have hd : (Matrix.diagonal sgn)ᴴ = Matrix.diagonal sgn := by
      ext i j; by_cases h : i = j
      · subst h; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq, sgn]
        split_ifs <;> simp
      · simp [h, Ne.symm h, Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne]
    simp only [S, Matrix.conjTranspose_mul, Matrix.mul_assoc, hd, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  have hS_mem : S ∈ Matrix.unitaryGroup α ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hS_herm]
    have hsgn_mul : Matrix.diagonal sgn * Matrix.diagonal sgn = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j; by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, sgn]; split_ifs <;> ring
      · simp [h, Matrix.diagonal_apply_ne, Matrix.one_apply_ne]
    calc S * S = U * (Matrix.diagonal sgn * (star U * U) * Matrix.diagonal sgn) * star U := by
            simp only [S, Matrix.mul_assoc]
      _ = U * star U := by rw [hU_star, Matrix.mul_one, hsgn_mul, Matrix.mul_one]
      _ = 1 := hU_mul
  have hge : ∑ i : α, |hΔ.eigenvalues i| ≤ traceNorm Δ := by
    have hle := re_trace_unitary_mul_le_traceNorm ⟨S, hS_mem⟩ Δ
    have htr : (Sᴴ * Δ).trace = ∑ i : α, ((|hΔ.eigenvalues i| : ℝ) : ℂ) := by
      rw [hS_herm]
      conv_lhs => rw [hspec]
      have h1 : S * (U * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues) * star U) =
          U * (Matrix.diagonal sgn * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues)) * star U := by
        calc (U * Matrix.diagonal sgn * star U) * (U * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues) * star U)
            = U * (Matrix.diagonal sgn * (star U * U) * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues)) * star U := by
                simp only [Matrix.mul_assoc]
          _ = U * (Matrix.diagonal sgn * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues)) * star U := by
                rw [hU_star, Matrix.mul_one]
      rw [h1, Matrix.trace_mul_cycle, hU_star, Matrix.one_mul, Matrix.diagonal_mul_diagonal,
        Matrix.trace_diagonal]
      apply Finset.sum_congr rfl; intro i _
      simp only [sgn, Function.comp_apply]
      split_ifs with hi
      · rw [one_mul, abs_of_nonneg hi]
      · rw [neg_one_mul, abs_of_neg (lt_of_not_ge hi), Complex.ofReal_neg]
    have hre : ((Sᴴ * Δ).trace).re = ∑ i : α, |hΔ.eigenvalues i| := by
      rw [htr, Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _; exact Complex.ofReal_re _
    linarith
  have hle : traceNorm Δ ≤ ∑ i : α, |hΔ.eigenvalues i| := by
    obtain ⟨W, hW⟩ := exists_unitary_trace_eq_traceNorm Δ
    have htr_re : (((W : Matrix α α ℂ)ᴴ * Δ).trace).re = traceNorm Δ := by
      rw [hW, Complex.ofReal_re]
    let Q_unit : Matrix.unitaryGroup α ℂ := star hΔ.eigenvectorUnitary * star W * hΔ.eigenvectorUnitary
    let Q : Matrix α α ℂ := (Q_unit : Matrix α α ℂ)
    have htrQ : ((W : Matrix α α ℂ)ᴴ * Δ).trace =
        (Q * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues)).trace := by
      conv_lhs => rw [hspec]
      have hQ : Q = star U * (W : Matrix α α ℂ)ᴴ * U := by
        simp [Q, Q_unit, U, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
      rw [hQ]
      calc ((W : Matrix α α ℂ)ᴴ * (U * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues) * star U)).trace
          = (star U * ((W : Matrix α α ℂ)ᴴ * U * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues))).trace := by
              simp only [← Matrix.mul_assoc]; rw [Matrix.trace_mul_cycle]; simp only [Matrix.mul_assoc]
        _ = (star U * (W : Matrix α α ℂ)ᴴ * U * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues)).trace := by
              simp only [Matrix.mul_assoc]
    rw [← htr_re, htrQ]
    have htr_sum : (Q * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues)).trace =
        ∑ i : α, Q i i * (hΔ.eigenvalues i : ℂ) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
        Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [htr_sum, Complex.re_sum]
    apply Finset.sum_le_sum; intro i _
    have hre : (Q i i * (hΔ.eigenvalues i : ℂ)).re = (Q i i).re * hΔ.eigenvalues i := by simp
    rw [hre]
    have hQ_abs : |(Q i i).re| ≤ 1 := by
      have hcol := congr_fun (congr_fun (Unitary.coe_star_mul_self Q_unit) i) i
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hcol
      have hre_col := congr_arg Complex.re hcol
      have hterm : ∀ j : α, (star (Q j i) * Q j i).re = ‖Q j i‖ ^ 2 := by
        intro j
        have : star (Q j i) * Q j i = ((‖Q j i‖ ^ 2 : ℝ) : ℂ) := by
          rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [this, Complex.ofReal_re]
      have hsum_sq : ∑ j : α, ‖Q j i‖ ^ 2 = 1 := by
        rw [Complex.re_sum, Complex.one_re] at hre_col
        rw [← hre_col]
        apply Finset.sum_congr rfl; intro j _
        exact (hterm j).symm
      have hle_sq : ‖Q i i‖ ^ 2 ≤ 1 := by
        rw [← hsum_sq]
        exact Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖Q j i‖) (Finset.mem_univ i)
      have hre_le : |(Q i i).re| ≤ ‖Q i i‖ := Complex.abs_re_le_norm (Q i i)
      nlinarith [abs_nonneg (Q i i).re, norm_nonneg (Q i i)]
    calc (Q i i).re * hΔ.eigenvalues i
        ≤ |(Q i i).re * hΔ.eigenvalues i| := le_abs_self _
      _ = |(Q i i).re| * |hΔ.eigenvalues i| := abs_mul _ _
      _ ≤ 1 * |hΔ.eigenvalues i| := mul_le_mul_of_nonneg_right hQ_abs (abs_nonneg _)
      _ = |hΔ.eigenvalues i| := one_mul _
  exact le_antisymm hle hge

/-- The binary Helstrom projector `Π = {ρ₀ - ρ₁ ≥ 0}` for discriminating `ρ₀` vs `ρ₁`. -/
noncomputable def helstromProjector (ρ₀ ρ₁ : DensityOp α) : Matrix α α ℂ :=
  let hΔ := (ρ₀.isHermitian.sub ρ₁.isHermitian)
  let U : Matrix α α ℂ := (hΔ.eigenvectorUnitary : Matrix α α ℂ)
  U * Matrix.diagonal (fun i : α ↦ if 0 ≤ hΔ.eigenvalues i then (1 : ℂ) else 0) * star U

lemma helstromProjector_isProjector (ρ₀ ρ₁ : DensityOp α) :
    IsProjector (helstromProjector ρ₀ ρ₁) := by
  set hΔ := (ρ₀.isHermitian.sub ρ₁.isHermitian)
  set U : Matrix α α ℂ := (hΔ.eigenvectorUnitary : Matrix α α ℂ)
  set D : Matrix α α ℂ := Matrix.diagonal (fun i : α ↦ if 0 ≤ hΔ.eigenvalues i then (1 : ℂ) else 0)
  have hD_herm : Dᴴ = D := by
    ext i j; by_cases h : i = j
    · subst h; simp only [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]
      split_ifs <;> simp
    · simp [D, h, Ne.symm h, Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne]
  have hD_idem : D * D = D := by
    rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · change (U * D * star U)ᴴ = U * D * star U
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hD_herm,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  · calc (U * D * star U) * (U * D * star U)
        = U * (D * (star U * U) * D) * star U := by simp only [Matrix.mul_assoc]
      _ = U * D * star U := by rw [Unitary.coe_star_mul_self hΔ.eigenvectorUnitary, Matrix.mul_one, hD_idem]

/-- Exact Helstrom discrimination error formula:
`Tr((1 - Π) ρ₀) + Tr(Π ρ₁) = 1 - (1 / 2) ‖ρ₀ - ρ₁‖₁`. -/
theorem helstrom_error_eq (ρ₀ ρ₁ : DensityOp α) :
    (((1 - helstromProjector ρ₀ ρ₁) * ρ₀.mat).trace).re +
      ((helstromProjector ρ₀ ρ₁ * ρ₁.mat).trace).re =
      1 - (1 / 2) * traceNorm (ρ₀.mat - ρ₁.mat) := by
  set hΔ := (ρ₀.isHermitian.sub ρ₁.isHermitian)
  set U : Matrix α α ℂ := (hΔ.eigenvectorUnitary : Matrix α α ℂ)
  have hspec : ρ₀.mat - ρ₁.mat = U * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues) * star U := by
    simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hΔ.spectral_theorem
  have htr_zero : ∑ i : α, hΔ.eigenvalues i = 0 := by
    have h1 := hΔ.trace_eq_sum_eigenvalues
    have h2 : (ρ₀.mat - ρ₁.mat).trace = 0 := by
      rw [Matrix.trace_sub, ρ₀.trace_one, ρ₁.trace_one, sub_self]
    rw [h2] at h1
    exact Complex.ofReal_eq_zero.mp (by simpa using h1.symm)
  have htr_PΔ : ((helstromProjector ρ₀ ρ₁ * (ρ₀.mat - ρ₁.mat)).trace).re =
      (1 / 2) * traceNorm (ρ₀.mat - ρ₁.mat) := by
    have hmul : helstromProjector ρ₀ ρ₁ * (ρ₀.mat - ρ₁.mat) =
        U * Matrix.diagonal (fun i : α ↦ if 0 ≤ hΔ.eigenvalues i then (hΔ.eigenvalues i : ℂ) else 0) * star U := by
      conv_lhs => rw [hspec]
      calc (U * Matrix.diagonal (fun i : α ↦ if 0 ≤ hΔ.eigenvalues i then (1 : ℂ) else 0) * star U) *
            (U * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues) * star U)
          = U * (Matrix.diagonal (fun i : α ↦ if 0 ≤ hΔ.eigenvalues i then (1 : ℂ) else 0) *
              (star U * U) * Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues)) * star U := by
                simp only [Matrix.mul_assoc]
        _ = U * (Matrix.diagonal (fun i : α ↦ if 0 ≤ hΔ.eigenvalues i then (1 : ℂ) else 0) *
              Matrix.diagonal (Complex.ofReal ∘ hΔ.eigenvalues)) * star U := by
                rw [Unitary.coe_star_mul_self hΔ.eigenvectorUnitary, Matrix.mul_one]
        _ = U * Matrix.diagonal (fun i : α ↦ if 0 ≤ hΔ.eigenvalues i then (hΔ.eigenvalues i : ℂ) else 0) * star U := by
              refine congr_arg (fun Z ↦ U * Z * star U) ?_
              rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; simp only [Function.comp_apply]
              split_ifs <;> simp
    rw [hmul, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self hΔ.eigenvectorUnitary,
      Matrix.one_mul, Matrix.trace_diagonal, Complex.re_sum, traceNorm_hermitian_eq_sum_abs hΔ]
    have hterm : ∀ i : α,
        ((if 0 ≤ hΔ.eigenvalues i then (hΔ.eigenvalues i : ℂ) else 0)).re =
          (hΔ.eigenvalues i + |hΔ.eigenvalues i|) / 2 := by
      intro i; split_ifs with hi
      · rw [Complex.ofReal_re, abs_of_nonneg hi]; ring
      · rw [Complex.zero_re, abs_of_neg (lt_of_not_ge hi)]; ring
    simp_rw [hterm]
    rw [← Finset.sum_div, Finset.sum_add_distrib, htr_zero, zero_add]
    ring
  have halg : ((1 - helstromProjector ρ₀ ρ₁) * ρ₀.mat).trace +
      (helstromProjector ρ₀ ρ₁ * ρ₁.mat).trace =
      1 - (helstromProjector ρ₀ ρ₁ * (ρ₀.mat - ρ₁.mat)).trace := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub,
      ρ₀.trace_one]
    ring
  have hre := congr_arg Complex.re halg
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re] at hre
  linarith

set_option maxHeartbeats 400000 in
/-- **Powers–Størmer Inequality** for density operators:
`2 - 2 Re Tr(√ρ₀ √ρ₁) ≤ ‖ρ₀ - ρ₁‖₁`. -/
theorem powers_stormer_traceNorm (ρ₀ ρ₁ : DensityOp α) :
    2 - 2 * ((ρ₀.sqrtMat * ρ₁.sqrtMat).trace).re ≤ traceNorm (ρ₀.mat - ρ₁.mat) := by
  set A := ρ₀.sqrtMat
  set B := ρ₁.sqrtMat
  set X := A - B
  set Y := A + B
  have hX : X.IsHermitian := ρ₀.sqrtMat_isHermitian.sub ρ₁.sqrtMat_isHermitian
  set U : Matrix α α ℂ := (hX.eigenvectorUnitary : Matrix α α ℂ)
  have hU_mul : U * star U = 1 := Unitary.coe_mul_star_self hX.eigenvectorUnitary
  have hU_star : star U * U = 1 := Unitary.coe_star_mul_self hX.eigenvectorUnitary
  have hX_spec : X = U * Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues) * star U := by
    simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hX.spectral_theorem
  let sgn : α → ℂ := fun i ↦ if 0 ≤ hX.eigenvalues i then 1 else -1
  set S : Matrix α α ℂ := U * Matrix.diagonal sgn * star U
  have hS_herm : Sᴴ = S := by
    have hd : (Matrix.diagonal sgn)ᴴ = Matrix.diagonal sgn := by
      ext i j; by_cases h : i = j
      · subst h; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq, sgn]
        split_ifs <;> simp
      · simp [h, Ne.symm h, Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne]
    simp only [S, Matrix.conjTranspose_mul, Matrix.mul_assoc, hd, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  have hS_mem : S ∈ Matrix.unitaryGroup α ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hS_herm]
    have hsgn_mul : Matrix.diagonal sgn * Matrix.diagonal sgn = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j; by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, sgn]; split_ifs <;> ring
      · simp [h, Matrix.diagonal_apply_ne, Matrix.one_apply_ne]
    calc S * S = U * (Matrix.diagonal sgn * (star U * U) * Matrix.diagonal sgn) * star U := by
            simp only [S, Matrix.mul_assoc]
      _ = U * star U := by rw [hU_star, Matrix.mul_one, hsgn_mul, Matrix.mul_one]
      _ = 1 := hU_mul
  have hdiff : ρ₀.mat - ρ₁.mat = (1 / 2 : ℂ) • (X * Y + Y * X) := by
    rw [← ρ₀.sqrtMat_mul_self, ← ρ₁.sqrtMat_mul_self]
    ext i j
    simp only [X, Y, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hSX : S * X = U * Matrix.diagonal (fun i : α ↦ ((|hX.eigenvalues i| : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hX_spec]
    calc (U * Matrix.diagonal sgn * star U) * (U * Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues) * star U)
        = U * (Matrix.diagonal sgn * (star U * U) * Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues)) * star U := by
            simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal sgn * Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues)) * star U := by
            rw [hU_star, Matrix.mul_one]
      _ = _ := by
            refine congr_arg (fun Z ↦ U * Z * star U) ?_
            rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; simp only [sgn, Function.comp_apply]
            split_ifs with hi
            · rw [one_mul, abs_of_nonneg hi]
            · rw [neg_one_mul, abs_of_neg (lt_of_not_ge hi), Complex.ofReal_neg]
  have hXS : X * S = S * X := by
    rw [hSX]
    conv_lhs => rw [hX_spec]
    calc (U * Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues) * star U) * (U * Matrix.diagonal sgn * star U)
        = U * (Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues) * (star U * U) * Matrix.diagonal sgn) * star U := by
            simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues) * Matrix.diagonal sgn) * star U := by
            rw [hU_star, Matrix.mul_one]
      _ = _ := by
            refine congr_arg (fun Z ↦ U * Z * star U) ?_
            rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; simp only [sgn, Function.comp_apply]
            split_ifs with hi
            · rw [mul_one, abs_of_nonneg hi]
            · rw [mul_neg_one, abs_of_neg (lt_of_not_ge hi), Complex.ofReal_neg]
  have htr_eq : (Sᴴ * (ρ₀.mat - ρ₁.mat)).trace =
      ∑ i : α, ((|hX.eigenvalues i| : ℝ) : ℂ) * (star U * Y * U) i i := by
    rw [hS_herm, hdiff, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add]
    have h1 : (S * (X * Y)).trace = ((S * X) * Y).trace :=
      congr_arg Matrix.trace (Matrix.mul_assoc S X Y).symm
    have h2 : (S * (Y * X)).trace = ((S * X) * Y).trace := by
      have ha : (S * (Y * X)).trace = ((S * Y) * X).trace :=
        congr_arg Matrix.trace (Matrix.mul_assoc S Y X).symm
      have hb : ((S * Y) * X).trace = (X * (S * Y)).trace := Matrix.trace_mul_comm (S * Y) X
      have hc : (X * (S * Y)).trace = ((X * S) * Y).trace :=
        congr_arg Matrix.trace (Matrix.mul_assoc X S Y).symm
      rw [ha, hb, hc, hXS]
    rw [h1, h2]
    have hhalf : (1 / 2 : ℂ) • (((S * X) * Y).trace + ((S * X) * Y).trace) = ((S * X) * Y).trace := by
      simp only [smul_eq_mul]; ring
    rw [hhalf, hSX]
    calc (U * Matrix.diagonal (fun i : α ↦ ((|hX.eigenvalues i| : ℝ) : ℂ)) * star U * Y).trace
        = (U * (Matrix.diagonal (fun i : α ↦ ((|hX.eigenvalues i| : ℝ) : ℂ)) * star U * Y)).trace := by
            simp only [Matrix.mul_assoc]
      _ = (Matrix.diagonal (fun i : α ↦ ((|hX.eigenvalues i| : ℝ) : ℂ)) * star U * Y * U).trace := by
            rw [Matrix.trace_mul_comm]
      _ = (Matrix.diagonal (fun i : α ↦ ((|hX.eigenvalues i| : ℝ) : ℂ)) * (star U * Y * U)).trace := by
            simp only [Matrix.mul_assoc]
      _ = ∑ i : α, ((|hX.eigenvalues i| : ℝ) : ℂ) * (star U * Y * U) i i := by
            simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
              ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hdiag_nn : ∀ (M : Matrix α α ℂ), M.PosSemidef → ∀ i : α, 0 ≤ ((star U * M * U) i i).re := by
    intro M hM i
    have hpsd : (star U * M * U).PosSemidef := by
      rw [Matrix.star_eq_conjTranspose]
      exact hM.conjTranspose_mul_mul_same U
    exact posSemidef_diag_re_nonneg hpsd i
  have hA_nn : ∀ i : α, 0 ≤ ((star U * A * U) i i).re := hdiag_nn A ρ₀.sqrtMat_posSemidef
  have hB_nn : ∀ i : α, 0 ≤ ((star U * B * U) i i).re := hdiag_nn B ρ₁.sqrtMat_posSemidef
  have hY_ge : ∀ i : α, |hX.eigenvalues i| ≤ ((star U * Y * U) i i).re := by
    intro i
    have hsub : ((star U * A * U) i i).re - ((star U * B * U) i i).re = hX.eigenvalues i := by
      have h1 : star U * X * U = Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues) := by
        conv_lhs => rw [hX_spec]
        calc star U * (U * Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues) * star U) * U
            = (star U * U) * Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues) * (star U * U) := by
                simp only [Matrix.mul_assoc]
          _ = _ := by rw [hU_star, Matrix.one_mul, Matrix.mul_one]
      have h2 : (star U * A * U) i i - (star U * B * U) i i = (hX.eigenvalues i : ℂ) := by
        have := congr_fun (congr_fun h1 i) i
        simp only [X, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply,
          Matrix.diagonal_apply_eq, Function.comp_apply] at this
        exact this
      have := congr_arg Complex.re h2
      simpa using this
    have hadd : ((star U * Y * U) i i).re = ((star U * A * U) i i).re + ((star U * B * U) i i).re := by
      have : (star U * Y * U) i i = (star U * A * U) i i + (star U * B * U) i i := by
        simp [Y, Matrix.mul_add, Matrix.add_mul]
      simpa using congr_arg Complex.re this
    rw [hadd, ← hsub, abs_le]
    constructor <;> linarith [hA_nn i, hB_nn i]
  have htr_XX : ∑ i : α, hX.eigenvalues i ^ 2 = 2 - 2 * ((A * B).trace).re := by
    have hXX : (X * X).trace = ∑ i : α, ((hX.eigenvalues i ^ 2 : ℝ) : ℂ) := by
      conv_lhs => rw [hX_spec]
      calc (U * Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues) * star U *
              (U * Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues) * star U)).trace
          = (U * (Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues) * (star U * U) *
              Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues)) * star U).trace := by
                simp only [Matrix.mul_assoc]
        _ = (Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues) *
              Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues)).trace := by
                rw [hU_star, Matrix.mul_one, Matrix.trace_mul_cycle, hU_star, Matrix.one_mul]
        _ = ∑ i : α, ((hX.eigenvalues i ^ 2 : ℝ) : ℂ) := by
              rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
              apply Finset.sum_congr rfl; intro i _; simp [sq]
    have hXX_re : ((X * X).trace).re = ∑ i : α, hX.eigenvalues i ^ 2 := by
      rw [hXX, Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _; exact Complex.ofReal_re _
    have hXX_expand : (X * X).trace = 2 - 2 * (A * B).trace := by
      have h1 : X * X = ρ₀.mat - A * B - B * A + ρ₁.mat := by
        rw [← ρ₀.sqrtMat_mul_self, ← ρ₁.sqrtMat_mul_self]
        simp only [X, Matrix.sub_mul, Matrix.mul_sub]; abel
      rw [h1, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, ρ₀.trace_one, ρ₁.trace_one,
        Matrix.trace_mul_comm B A]
      ring
    have hre2 := congr_arg Complex.re hXX_expand
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero] at hre2
    linarith
  have hle_norm := re_trace_unitary_mul_le_traceNorm ⟨S, hS_mem⟩ (ρ₀.mat - ρ₁.mat)
  have hre_S : ((Sᴴ * (ρ₀.mat - ρ₁.mat)).trace).re =
      ∑ i : α, |hX.eigenvalues i| * ((star U * Y * U) i i).re := by
    rw [htr_eq, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _; simp
  calc 2 - 2 * ((A * B).trace).re
      = ∑ i : α, hX.eigenvalues i ^ 2 := htr_XX.symm
    _ = ∑ i : α, |hX.eigenvalues i| * |hX.eigenvalues i| := by
          apply Finset.sum_congr rfl; intro i _; rw [← sq, sq_abs]
    _ ≤ ∑ i : α, |hX.eigenvalues i| * ((star U * Y * U) i i).re := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_left (hY_ge i) (abs_nonneg _)
    _ = ((Sᴴ * (ρ₀.mat - ρ₁.mat)).trace).re := hre_S.symm
    _ ≤ traceNorm (ρ₀.mat - ρ₁.mat) := hle_norm

/-- **Holevo–Helstrom Fidelity Bound**:
`(1 / 2) * (Tr((1 - Π) ρ₀) + Tr(Π ρ₁)) ≤ (1 / 2) * F(ρ₀, ρ₁)`. -/
theorem helstrom_error_le_fidelity (ρ₀ ρ₁ : DensityOp α) :
    (1 / 2) * ((((1 - helstromProjector ρ₀ ρ₁) * ρ₀.mat).trace).re +
      ((helstromProjector ρ₀ ρ₁ * ρ₁.mat).trace).re) ≤
      (1 / 2) * rootFidelity ρ₀ ρ₁ := by
  rw [helstrom_error_eq]
  have hps := powers_stormer_traceNorm ρ₀ ρ₁
  have hfid : ((ρ₀.sqrtMat * ρ₁.sqrtMat).trace).re ≤ rootFidelity ρ₀ ρ₁ := by
    rw [← traceNorm_sqrt_mul_sqrt ρ₀ ρ₁]
    have h := re_trace_unitary_mul_le_traceNorm (1 : Matrix.unitaryGroup α ℂ) (ρ₀.sqrtMat * ρ₁.sqrtMat)
    simpa [Matrix.conjTranspose_one, Matrix.one_mul] using h
  linarith

/-! ### Gao's Sharp Quantum Union Bound & Sen's Noncommutative Union Bound -/

/-- Sequential left-product of a list of operators: `[P₁, ..., P_m] ↦ P_m ⋯ P_1`. -/
def seqProd : List (Matrix α α ℂ) → Matrix α α ℂ
  | [] => 1
  | P :: Ps => seqProd Ps * P

lemma seqProd_nil : seqProd ([] : List (Matrix α α ℂ)) = 1 := rfl
lemma seqProd_cons (P : Matrix α α ℂ) (Ps : List (Matrix α α ℂ)) :
    seqProd (P :: Ps) = seqProd Ps * P := rfl

private noncomputable def vecNormSq (v : α → ℂ) : ℝ := ∑ i : α, ‖v i‖ ^ 2
private def vecInner (u v : α → ℂ) : ℂ := ∑ i : α, star (u i) * v i

private lemma vecNormSq_nonneg (v : α → ℂ) : 0 ≤ vecNormSq v :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

private lemma vecInner_self_re (v : α → ℂ) : (vecInner v v).re = vecNormSq v := by
  unfold vecInner vecNormSq
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro i _
  have : star (v i) * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [this, Complex.ofReal_re]

private lemma vecInner_mulVec_left (M : Matrix α α ℂ) (u v : α → ℂ) :
    vecInner (M.mulVec u) v = vecInner u (Mᴴ.mulVec v) := by
  unfold vecInner
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, star_mul',
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro i _
  ring

private lemma vecInner_add_left (u₁ u₂ v : α → ℂ) :
    vecInner (u₁ + u₂) v = vecInner u₁ v + vecInner u₂ v := by
  unfold vecInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  simp [add_mul]

private lemma vecInner_sub_left (u₁ u₂ v : α → ℂ) :
    vecInner (u₁ - u₂) v = vecInner u₁ v - vecInner u₂ v := by
  unfold vecInner
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  simp [sub_mul]

private lemma vecInner_re_le (u v : α → ℂ) :
    (vecInner u v).re ≤ Real.sqrt (vecNormSq u) * Real.sqrt (vecNormSq v) := by
  have h1 : (vecInner u v).re ≤ ∑ i : α, ‖u i‖ * ‖v i‖ := by
    unfold vecInner
    rw [Complex.re_sum]
    apply Finset.sum_le_sum; intro i _
    calc (star (u i) * v i).re ≤ ‖star (u i) * v i‖ := Complex.re_le_norm _
      _ = ‖u i‖ * ‖v i‖ := by rw [norm_mul, norm_star]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : α ↦ ‖u i‖) (fun i : α ↦ ‖v i‖)
  have h2 : ∑ i : α, ‖u i‖ * ‖v i‖ ≤ Real.sqrt (vecNormSq u) * Real.sqrt (vecNormSq v) := by
    rw [← Real.sqrt_mul (vecNormSq_nonneg u)]
    exact Real.le_sqrt_of_sq_le hcs
  exact le_trans h1 h2

private lemma projector_mulVec_add (P : Matrix α α ℂ) (v : α → ℂ) (i : α) :
    (P.mulVec v) i + ((1 - P).mulVec v) i = v i := by
  have h1 := congr_fun (Matrix.add_mulVec P (1 - P) v) i
  simp only [add_sub_cancel, Matrix.one_mulVec, Pi.add_apply] at h1
  exact h1.symm

private lemma projector_pythagoras {P : Matrix α α ℂ} (hP : IsProjector P) (v : α → ℂ) :
    vecNormSq (P.mulVec v) + vecNormSq ((1 - P).mulVec v) = vecNormSq v := by
  rw [← vecInner_self_re, ← vecInner_self_re, ← vecInner_self_re, ← Complex.add_re]
  congr 1
  have h1 : vecInner (P.mulVec v) (P.mulVec v) = vecInner v (P.mulVec v) := by
    rw [vecInner_mulVec_left, hP.1, Matrix.mulVec_mulVec, hP.2]
  have h2 : vecInner ((1 - P).mulVec v) ((1 - P).mulVec v) = vecInner v ((1 - P).mulVec v) := by
    rw [vecInner_mulVec_left, hP.sub_one.1, Matrix.mulVec_mulVec, hP.sub_one.2]
  rw [h1, h2]
  unfold vecInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← mul_add, projector_mulVec_add P v i]

/-- Vector form of **Gao's Sharp Quantum Union Bound** (via O'Donnell–Venkateswaran):
for any vector `ψ` with `‖ψ‖² = 1` and any list of orthogonal projectors `Ps`,
`1 - ‖(seqProd Ps) ψ‖² ≤ 4 ∑_{P ∈ Ps} ‖(1 - P) ψ‖²`. -/
private lemma gao_union_bound_vec (Ps : List (Matrix α α ℂ))
    (hPs : ∀ P ∈ Ps, IsProjector P) (ψ : α → ℂ) (hψ : vecNormSq ψ = 1) :
    1 - vecNormSq ((seqProd Ps).mulVec ψ) ≤
      4 * (Ps.map (fun P ↦ vecNormSq ((1 - P).mulVec ψ))).sum := by
  have hstep : ∀ (Qs : List (Matrix α α ℂ)), (∀ P ∈ Qs, IsProjector P) →
      ∀ (v : α → ℂ),
        vecNormSq v - vecNormSq ((seqProd Qs).mulVec v) ≥ 0 ∧
        (vecInner (v - (seqProd Qs).mulVec v) ψ).re ≤
          Real.sqrt (vecNormSq v - vecNormSq ((seqProd Qs).mulVec v)) *
          Real.sqrt ((Qs.map (fun P ↦ vecNormSq ((1 - P).mulVec ψ))).sum) := by
    intro Qs
    induction Qs with
    | nil =>
      intro _ v
      simp [seqProd, vecInner]
    | cons P Qs ih =>
      intro hQs v
      have hP : IsProjector P := hQs P (List.mem_cons_self ..)
      have hQs' : ∀ Q ∈ Qs, IsProjector Q := fun Q hQ ↦ hQs Q (List.mem_cons_of_mem P hQ)
      obtain ⟨hnn_rest, hre_rest⟩ := ih hQs' (P.mulVec v)
      have hpyth := projector_pythagoras hP v
      have hseq : (seqProd (P :: Qs)).mulVec v = (seqProd Qs).mulVec (P.mulVec v) := by
        rw [seqProd_cons, Matrix.mulVec_mulVec]
      have hdiff_eq : vecNormSq v - vecNormSq ((seqProd (P :: Qs)).mulVec v) =
          vecNormSq ((1 - P).mulVec v) +
            (vecNormSq (P.mulVec v) - vecNormSq ((seqProd Qs).mulVec (P.mulVec v))) := by
        rw [hseq]; linarith
      refine ⟨by rw [hdiff_eq]; linarith [vecNormSq_nonneg ((1 - P).mulVec v)], ?_⟩
      have hv_split : v - (seqProd (P :: Qs)).mulVec v =
          (1 - P).mulVec v + (P.mulVec v - (seqProd Qs).mulVec (P.mulVec v)) := by
        ext i
        have h1 := projector_mulVec_add P v i
        rw [hseq]; simp only [Pi.sub_apply, Pi.add_apply]; linear_combination -h1
      have hfirst : (vecInner ((1 - P).mulVec v) ψ).re ≤
          Real.sqrt (vecNormSq ((1 - P).mulVec v)) * Real.sqrt (vecNormSq ((1 - P).mulVec ψ)) := by
        have heq : vecInner ((1 - P).mulVec v) ψ = vecInner ((1 - P).mulVec v) ((1 - P).mulVec ψ) := by
          rw [vecInner_mulVec_left, hP.sub_one.1, vecInner_mulVec_left (1 - P), hP.sub_one.1,
            Matrix.mulVec_mulVec, hP.sub_one.2]
        rw [heq]
        exact vecInner_re_le _ _
      rw [hv_split, vecInner_add_left, Complex.add_re]
      set a₁ := vecNormSq ((1 - P).mulVec v)
      set a₂ := vecNormSq (P.mulVec v) - vecNormSq ((seqProd Qs).mulVec (P.mulVec v))
      set b₁ := vecNormSq ((1 - P).mulVec ψ)
      set b₂ := (Qs.map (fun Q ↦ vecNormSq ((1 - Q).mulVec ψ))).sum
      have ha₁ : 0 ≤ a₁ := vecNormSq_nonneg _
      have hb₁ : 0 ≤ b₁ := vecNormSq_nonneg _
      have hb₂ : 0 ≤ b₂ := List.sum_nonneg (by intro x hx; simp only [List.mem_map] at hx; rcases hx with ⟨Q, _, rfl⟩; exact vecNormSq_nonneg _)
      have hcs2 : Real.sqrt a₁ * Real.sqrt b₁ + Real.sqrt a₂ * Real.sqrt b₂ ≤
          Real.sqrt (a₁ + a₂) * Real.sqrt (b₁ + b₂) := by
        have hsq : (Real.sqrt a₁ * Real.sqrt b₁ + Real.sqrt a₂ * Real.sqrt b₂) ^ 2 ≤
            (a₁ + a₂) * (b₁ + b₂) := by
          have h1 : Real.sqrt a₁ ^ 2 = a₁ := Real.sq_sqrt ha₁
          have h2 : Real.sqrt a₂ ^ 2 = a₂ := Real.sq_sqrt hnn_rest
          have h3 : Real.sqrt b₁ ^ 2 = b₁ := Real.sq_sqrt hb₁
          have h4 : Real.sqrt b₂ ^ 2 = b₂ := Real.sq_sqrt hb₂
          nlinarith [sq_nonneg (Real.sqrt a₁ * Real.sqrt b₂ - Real.sqrt a₂ * Real.sqrt b₁)]
        have hmul_rt : Real.sqrt (a₁ + a₂) * Real.sqrt (b₁ + b₂) = Real.sqrt ((a₁ + a₂) * (b₁ + b₂)) :=
          (Real.sqrt_mul (by linarith) (b₁ + b₂)).symm
        rw [hmul_rt]
        exact Real.le_sqrt_of_sq_le hsq
      have hmap : ((P :: Qs).map (fun Q ↦ vecNormSq ((1 - Q).mulVec ψ))).sum = b₁ + b₂ := by
        simp [b₁, b₂]
      rw [hdiff_eq, hmap]
      linarith
  obtain ⟨hnn, hre⟩ := hstep Ps hPs ψ
  set y := vecNormSq ((seqProd Ps).mulVec ψ)
  set S := (Ps.map (fun P ↦ vecNormSq ((1 - P).mulVec ψ))).sum
  have hy_nn : 0 ≤ y := vecNormSq_nonneg _
  have hy_le : y ≤ 1 := by linarith
  have hS_nn : 0 ≤ S := List.sum_nonneg (by intro x hx; simp only [List.mem_map] at hx; rcases hx with ⟨Q, _, rfl⟩; exact vecNormSq_nonneg _)
  have hinner_le : (vecInner ((seqProd Ps).mulVec ψ) ψ).re ≤ Real.sqrt y := by
    have h := vecInner_re_le ((seqProd Ps).mulVec ψ) ψ
    rw [hψ, Real.sqrt_one, mul_one] at h
    exact h
  have hsub_ge : 1 - Real.sqrt y ≤ (vecInner (ψ - (seqProd Ps).mulVec ψ) ψ).re := by
    rw [vecInner_sub_left, Complex.sub_re, vecInner_self_re, hψ]
    linarith
  rw [hψ] at hre
  have hkey : 1 - Real.sqrt y ≤ Real.sqrt (1 - y) * Real.sqrt S := le_trans hsub_ge hre
  have h1my : 1 - y = (1 + Real.sqrt y) * (1 - Real.sqrt y) := by
    nlinarith [Real.sq_sqrt hy_nn]
  have hsq_le : 1 - y ≤ 2 * Real.sqrt (1 - y) * Real.sqrt S := by
    have hrt_le : Real.sqrt y ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hy_le
    have h1my_nn : 0 ≤ 1 - Real.sqrt y := by linarith
    calc 1 - y = (1 + Real.sqrt y) * (1 - Real.sqrt y) := h1my
      _ ≤ 2 * (1 - Real.sqrt y) := by nlinarith
      _ ≤ 2 * (Real.sqrt (1 - y) * Real.sqrt S) := by linarith
      _ = 2 * Real.sqrt (1 - y) * Real.sqrt S := by ring
  by_cases h0 : 1 - y = 0
  · linarith
  · have hpos : 0 < Real.sqrt (1 - y) := Real.sqrt_pos.mpr (lt_of_le_of_ne (by linarith) (Ne.symm h0))
    have hrt_bound : Real.sqrt (1 - y) ≤ 2 * Real.sqrt S := by
      have : Real.sqrt (1 - y) * Real.sqrt (1 - y) ≤ Real.sqrt (1 - y) * (2 * Real.sqrt S) := by
        rw [Real.mul_self_sqrt (by linarith)]; linarith
      exact le_of_mul_le_mul_left this hpos
    have hsq2 : (Real.sqrt (1 - y)) ^ 2 ≤ (2 * Real.sqrt S) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (1 - y), Real.sqrt_nonneg S]
    rw [Real.sq_sqrt (by linarith), mul_pow, Real.sq_sqrt hS_nn] at hsq2
    linarith

/-- **Gao's Sharp Quantum Union Bound** for density operators:
for any density operator `ρ` and any list of orthogonal projectors `Ps`,
`1 - Tr(seqProd(Ps) ρ seqProd(Ps)ᴴ) ≤ 4 ∑_{P ∈ Ps} Tr((1 - P) ρ)`. -/
theorem gao_union_bound_density (ρ : DensityOp α) (Ps : List (Matrix α α ℂ))
    (hPs : ∀ P ∈ Ps, IsProjector P) :
    1 - ((seqProd Ps * ρ.mat * (seqProd Ps)ᴴ).trace).re ≤
      4 * (Ps.map (fun P ↦ (((1 - P) * ρ.mat).trace).re)).sum := by
  set U : Matrix α α ℂ := (ρ.eigUnitary : Matrix α α ℂ)
  have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by
    simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
  let col : α → (α → ℂ) := fun a i ↦ U i a
  have hcol_unit : ∀ a : α, vecNormSq (col a) = 1 := by
    intro a
    have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) a) a
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
    have hre := congr_arg Complex.re h
    rw [Complex.re_sum, Complex.one_re] at hre
    unfold vecNormSq col
    rw [← hre]
    apply Finset.sum_congr rfl; intro i _
    have : star (U i a) * U i a = ((‖U i a‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this, Complex.ofReal_re]
  have hquad_tr : ∀ (M : Matrix α α ℂ),
      ((M * ρ.mat * Mᴴ).trace).re = ∑ a : α, ρ.eigvals a * vecNormSq (M.mulVec (col a)) := by
    intro M
    have h1 : (M * ρ.mat * Mᴴ).trace =
        ∑ a : α, (ρ.eigvals a : ℂ) * vecInner (M.mulVec (col a)) (M.mulVec (col a)) := by
      conv_lhs => rw [hspec]
      calc (M * (U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U) * Mᴴ).trace
          = ((M * U) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * (M * U)ᴴ).trace := by
              simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
        _ = ((M * U)ᴴ * (M * U) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals)).trace := by
              rw [Matrix.trace_mul_cycle]; simp only [Matrix.mul_assoc]
        _ = ∑ a : α, (ρ.eigvals a : ℂ) * vecInner (M.mulVec (col a)) (M.mulVec (col a)) := by
              rw [Matrix.trace]
              apply Finset.sum_congr rfl; intro a _
              simp only [Matrix.diag, Matrix.mul_diagonal, Function.comp_apply]
              rw [mul_comm]
              congr 1
              simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, vecInner, Matrix.mulVec,
                dotProduct, col]
    rw [h1, Complex.re_sum]
    apply Finset.sum_congr rfl; intro a _
    simp [vecInner_self_re]
  have hproj_tr : ∀ (P : Matrix α α ℂ), IsProjector P →
      (((1 - P) * ρ.mat).trace).re = ∑ a : α, ρ.eigvals a * vecNormSq ((1 - P).mulVec (col a)) := by
    intro P hP
    have h1 : ((1 - P) * ρ.mat).trace = ((1 - P) * ρ.mat * (1 - P)ᴴ).trace := by
      rw [Matrix.trace_mul_cycle, hP.sub_one.1, hP.sub_one.2]
    rw [h1]
    exact hquad_tr (1 - P)
  have hsum_eig : ∑ a : α, ρ.eigvals a = 1 := ρ.sum_eigvals
  have hLHS : 1 - ((seqProd Ps * ρ.mat * (seqProd Ps)ᴴ).trace).re =
      ∑ a : α, ρ.eigvals a * (1 - vecNormSq ((seqProd Ps).mulVec (col a))) := by
    rw [hquad_tr (seqProd Ps)]
    have : ∑ a : α, ρ.eigvals a * (1 - vecNormSq ((seqProd Ps).mulVec (col a))) =
        (∑ a : α, ρ.eigvals a) - ∑ a : α, ρ.eigvals a * vecNormSq ((seqProd Ps).mulVec (col a)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro a _; ring
    rw [this, hsum_eig]
  have hRHS : (Ps.map (fun P ↦ (((1 - P) * ρ.mat).trace).re)).sum =
      ∑ a : α, ρ.eigvals a * (Ps.map (fun P ↦ vecNormSq ((1 - P).mulVec (col a)))).sum := by
    have hlist : ∀ (Qs : List (Matrix α α ℂ)), (∀ P ∈ Qs, IsProjector P) →
        (Qs.map (fun P ↦ (((1 - P) * ρ.mat).trace).re)).sum =
        ∑ a : α, ρ.eigvals a * (Qs.map (fun P ↦ vecNormSq ((1 - P).mulVec (col a)))).sum := by
      intro Qs
      induction Qs with
      | nil => intro _; simp
      | cons P Qs ih =>
        intro hQs
        have hP := hQs P (List.mem_cons_self ..)
        have hQs' := fun Q hQ ↦ hQs Q (List.mem_cons_of_mem P hQ)
        simp only [List.map_cons, List.sum_cons, hproj_tr P hP, ih hQs']
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro a _; ring
    exact hlist Ps hPs
  rw [hLHS, hRHS, Finset.mul_sum]
  apply Finset.sum_le_sum; intro a _
  have hvec := gao_union_bound_vec Ps hPs (col a) (hcol_unit a)
  calc ρ.eigvals a * (1 - vecNormSq ((seqProd Ps).mulVec (col a)))
      ≤ ρ.eigvals a * (4 * (Ps.map (fun P ↦ vecNormSq ((1 - P).mulVec (col a)))).sum) :=
        mul_le_mul_of_nonneg_left hvec (ρ.eigvals_nonneg a)
    _ = 4 * (ρ.eigvals a * (Ps.map (fun P ↦ vecNormSq ((1 - P).mulVec (col a)))).sum) := by ring

/-- **Sen's Noncommutative Union Bound** (Sen 2012, Lemma 3 / Wilde–Guha [12, Prop. 4]):
for any density operator `ρ` and any list of orthogonal projectors `Ps`,
`1 - Tr(seqProd(Ps) ρ seqProd(Ps)ᴴ) ≤ 2 √(∑_{P ∈ Ps} Tr((1 - P) ρ))`. -/
theorem sen_noncommutative_union_bound (ρ : DensityOp α) (Ps : List (Matrix α α ℂ))
    (hPs : ∀ P ∈ Ps, IsProjector P) :
    1 - ((seqProd Ps * ρ.mat * (seqProd Ps)ᴴ).trace).re ≤
      2 * Real.sqrt (Ps.map (fun P ↦ (((1 - P) * ρ.mat).trace).re)).sum := by
  set S := (Ps.map (fun P ↦ (((1 - P) * ρ.mat).trace).re)).sum
  have hS_nn : 0 ≤ S := by
    apply List.sum_nonneg
    intro x hx
    simp only [List.mem_map] at hx
    rcases hx with ⟨P, hP_mem, rfl⟩
    have hP := hPs P hP_mem
    have htr : ((1 - P) * ρ.mat).trace = ((1 - P) * ρ.mat * (1 - P)ᴴ).trace := by
      rw [Matrix.trace_mul_cycle, hP.sub_one.1, hP.sub_one.2]
    rw [htr]
    have hpsd := ρ.posSemidef.mul_mul_conjTranspose_same (1 - P)
    have heq := hpsd.isHermitian.trace_eq_sum_eigenvalues
    have hre : (((1 - P) * ρ.mat * (1 - P)ᴴ).trace).re = ∑ i : α, hpsd.isHermitian.eigenvalues i := by
      rw [heq, Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _; exact Complex.ofReal_re _
    rw [hre]
    exact Finset.sum_nonneg fun i _ ↦ hpsd.eigenvalues_nonneg i
  have hgao := gao_union_bound_density ρ Ps hPs
  have htr_nn : 0 ≤ ((seqProd Ps * ρ.mat * (seqProd Ps)ᴴ).trace).re := by
    have hpsd := ρ.posSemidef.mul_mul_conjTranspose_same (seqProd Ps)
    have heq := hpsd.isHermitian.trace_eq_sum_eigenvalues
    have hre : ((seqProd Ps * ρ.mat * (seqProd Ps)ᴴ).trace).re =
        ∑ i : α, hpsd.isHermitian.eigenvalues i := by
      rw [heq, Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _; exact Complex.ofReal_re _
    rw [hre]
    exact Finset.sum_nonneg fun i _ ↦ hpsd.eigenvalues_nonneg i
  by_cases hS : S ≤ 1 / 4
  · have h2S : 2 * S ≤ Real.sqrt S := by
      rw [Real.le_sqrt (by linarith) hS_nn]
      nlinarith
    linarith
  · have h1 : (1 : ℝ) ≤ 2 * Real.sqrt S := by
      have : (1 / 2 : ℝ) ≤ Real.sqrt S := by
        rw [Real.le_sqrt (by norm_num) hS_nn]; linarith
      linarith
    linarith

/-! ### Reindexing Invariance of von Neumann Entropy and Root Fidelity -/

/-- Reindexing a `DensityOp` by a bijection `e : α ≃ β` preserves `vonNeumannEntropy`. -/
lemma vonNeumannEntropy_of_reindex (e : α ≃ β) (ρ : DensityOp α) (σ : DensityOp β)
    (heq : ∀ i j : α, σ.mat (e i) (e j) = ρ.mat i j) :
    vonNeumannEntropy σ = vonNeumannEntropy ρ := by
  have hmat : σ.mat = Matrix.reindex e e ρ.mat := by
    ext x y
    simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using heq (e.symm x) (e.symm y)
  unfold vonNeumannEntropy
  congr 1
  exact spectral_sum_eq_of_charpoly_mul_X_pow σ.isHermitian ρ.isHermitian (k := 0) (l := 0)
    (by rw [pow_zero, mul_one, mul_one, hmat, Matrix.charpoly_reindex])
    (by simp [Real.negMulLog])

/-- Reindexing a pair of `DensityOp`s by a bijection `e : α ≃ β` preserves `rootFidelity`. -/
lemma rootFidelity_of_reindex (e : α ≃ β) (ρ₁ ρ₂ : DensityOp α) (σ₁ σ₂ : DensityOp β)
    (heq₁ : ∀ i j : α, σ₁.mat (e i) (e j) = ρ₁.mat i j)
    (heq₂ : ∀ i j : α, σ₂.mat (e i) (e j) = ρ₂.mat i j) :
    rootFidelity σ₁ σ₂ = rootFidelity ρ₁ ρ₂ := by
  have hmat₁ : σ₁.mat = Matrix.reindex e e ρ₁.mat := by
    ext x y; simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using heq₁ (e.symm x) (e.symm y)
  have hmat₂ : σ₂.mat = Matrix.reindex e e ρ₂.mat := by
    ext x y; simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using heq₂ (e.symm x) (e.symm y)
  let R : Matrix β β ℂ := Matrix.reindex e e ρ₁.sqrtMat
  have hR_sq : R * R = σ₁.mat := by
    rw [hmat₁, ← ρ₁.sqrtMat_mul_self]
    exact ((Matrix.reindexAlgEquiv ℂ ℂ e).map_mul ρ₁.sqrtMat ρ₁.sqrtMat).symm
  have hR_psd : R.PosSemidef := by
    let P : Matrix β α ℂ := Matrix.of fun y x ↦ if y = e x then 1 else 0
    have hPR : R = P * ρ₁.sqrtMat * Pᴴ := by
      ext y₁ y₂
      simp only [R, P, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.of_apply]
      rw [Finset.sum_eq_single (e.symm y₂)]
      · rw [Finset.sum_eq_single (e.symm y₁)]
        · simp
        · intro x₁ _ hne; have : y₁ ≠ e x₁ := fun h ↦ hne (by rw [h, e.symm_apply_apply])
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro x₂ _ hne; have : y₂ ≠ e x₂ := fun h ↦ hne (by rw [h, e.symm_apply_apply])
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hPR]
    exact ρ₁.sqrtMat_posSemidef.mul_mul_conjTranspose_same P
  have hR_eq : R = σ₁.sqrtMat := by
    set U := (σ₁.eigUnitary : Matrix β β ℂ)
    have hU_star : star U * U = 1 := Unitary.coe_star_mul_self σ₁.eigUnitary
    have hU_mul : U * star U = 1 := Unitary.coe_mul_star_self σ₁.eigUnitary
    have hspec : σ₁.mat = U * Matrix.diagonal (Complex.ofReal ∘ σ₁.eigvals) * star U := by
      simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
        Unitary.conjStarAlgAut_apply] using σ₁.isHermitian.spectral_theorem
    let M : Matrix β β ℂ := star U * R * U
    have hM_psd : M.PosSemidef := by
      change (star U * R * U).PosSemidef
      rw [Matrix.star_eq_conjTranspose]
      exact hR_psd.conjTranspose_mul_mul_same U
    have hM_sq : M * M = Matrix.diagonal (Complex.ofReal ∘ σ₁.eigvals) := by
      calc M * M = star U * (R * (U * star U) * R) * U := by simp only [M, Matrix.mul_assoc]
        _ = star U * σ₁.mat * U := by rw [hU_mul, Matrix.mul_one, hR_sq]
        _ = Matrix.diagonal (Complex.ofReal ∘ σ₁.eigvals) := by
              conv_lhs => rw [hspec]
              calc star U * (U * Matrix.diagonal (Complex.ofReal ∘ σ₁.eigvals) * star U) * U
                  = (star U * U) * Matrix.diagonal (Complex.ofReal ∘ σ₁.eigvals) * (star U * U) := by
                      simp only [Matrix.mul_assoc]
                _ = _ := by rw [hU_star, Matrix.one_mul, Matrix.mul_one]
    have hM_diag : M = Matrix.diagonal (fun i : β ↦ (Real.sqrt (σ₁.eigvals i) : ℂ)) := by
      set V := (hM_psd.isHermitian.eigenvectorUnitary : Matrix β β ℂ)
      have hV_star : star V * V = 1 := Unitary.coe_star_mul_self hM_psd.isHermitian.eigenvectorUnitary
      have hV_mul : V * star V = 1 := Unitary.coe_mul_star_self hM_psd.isHermitian.eigenvectorUnitary
      have hM_spec : M = V * Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues) * star V := by
        simpa [V, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using
          hM_psd.isHermitian.spectral_theorem
      have hM_sq_spec : V * Matrix.diagonal (fun k : β ↦ ((hM_psd.isHermitian.eigenvalues k ^ 2 : ℝ) : ℂ)) * star V =
          Matrix.diagonal (Complex.ofReal ∘ σ₁.eigvals) := by
        rw [← hM_sq]
        conv_rhs => rw [hM_spec]
        calc V * Matrix.diagonal (fun k : β ↦ ((hM_psd.isHermitian.eigenvalues k ^ 2 : ℝ) : ℂ)) * star V
            = V * (Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues) *
                Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues)) * star V := by
                  refine congr_arg (fun Z ↦ V * Z * star V) ?_
                  rw [Matrix.diagonal_mul_diagonal]; congr 1; funext k; simp [sq]
          _ = V * (Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues) * (star V * V) *
                Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues)) * star V := by
                  rw [hV_star, Matrix.mul_one]
          _ = _ := by simp only [Matrix.mul_assoc]
      have hV_eig : ∀ i k : β,
          V i k * ((hM_psd.isHermitian.eigenvalues k : ℝ) : ℂ) =
          V i k * (Real.sqrt (σ₁.eigvals i) : ℂ) := by
        intro i k
        have h1 : (V * Matrix.diagonal (fun k : β ↦ ((hM_psd.isHermitian.eigenvalues k ^ 2 : ℝ) : ℂ))) i k =
            (Matrix.diagonal (Complex.ofReal ∘ σ₁.eigvals) * V) i k := by
          have := congr_arg (fun X ↦ X * V) hM_sq_spec
          simp only [Matrix.mul_assoc, hV_star, Matrix.mul_one] at this
          exact congr_fun (congr_fun this i) k
        simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply] at h1
        by_cases hVik : V i k = 0
        · simp [hVik]
        · have hsq_eq : hM_psd.isHermitian.eigenvalues k ^ 2 = σ₁.eigvals i := by
            have h2 : ((hM_psd.isHermitian.eigenvalues k ^ 2 : ℝ) : ℂ) = (σ₁.eigvals i : ℂ) := by
              have : V i k * ((hM_psd.isHermitian.eigenvalues k ^ 2 : ℝ) : ℂ) =
                  V i k * (σ₁.eigvals i : ℂ) := by linear_combination h1
              exact mul_left_cancel₀ hVik this
            exact Complex.ofReal_injective h2
          have hval : hM_psd.isHermitian.eigenvalues k = Real.sqrt (σ₁.eigvals i) := by
            rw [← hsq_eq, Real.sqrt_sq (hM_psd.eigenvalues_nonneg k)]
          rw [hval]
      ext i j
      conv_lhs => rw [hM_spec]
      rw [Matrix.mul_apply]
      have hterm : ∀ k : β,
          (V * Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues)) i k * (star V) k j =
          V i k * (hM_psd.isHermitian.eigenvalues k : ℂ) * star (V j k) := by
        intro k; rw [Matrix.mul_diagonal, Matrix.star_apply, Function.comp_apply]
      simp_rw [hterm]
      simp only [Matrix.diagonal_apply]
      calc ∑ k : β, V i k * (hM_psd.isHermitian.eigenvalues k : ℂ) * star (V j k)
          = ∑ k : β, (Real.sqrt (σ₁.eigvals i) : ℂ) * (V i k * star (V j k)) := by
              apply Finset.sum_congr rfl; intro k _
              rw [hV_eig i k]; ring
        _ = (Real.sqrt (σ₁.eigvals i) : ℂ) * (V * star V) i j := by
              rw [← Finset.mul_sum]; simp [Matrix.mul_apply, Matrix.star_apply]
        _ = if i = j then (Real.sqrt (σ₁.eigvals i) : ℂ) else 0 := by
              rw [hV_mul, Matrix.one_apply]
              split_ifs <;> simp
    calc R = (U * star U) * R * (U * star U) := by rw [hU_mul, Matrix.one_mul, Matrix.mul_one]
      _ = U * M * star U := by simp only [M, Matrix.mul_assoc]
      _ = U * Matrix.diagonal (fun i : β ↦ (Real.sqrt (σ₁.eigvals i) : ℂ)) * star U := by rw [hM_diag]
      _ = σ₁.sqrtMat := rfl
  have hprod : σ₁.sqrtMat * σ₂.mat * σ₁.sqrtMat =
      Matrix.reindex e e (ρ₁.sqrtMat * ρ₂.mat * ρ₁.sqrtMat) := by
    rw [← hR_eq, hmat₂]
    have h1 := (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul ρ₁.sqrtMat ρ₂.mat
    have h2 := (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul (ρ₁.sqrtMat * ρ₂.mat) ρ₁.sqrtMat
    simpa [R, Matrix.reindexAlgEquiv_apply] using (h2.trans (by rw [h1])).symm
  unfold rootFidelity
  apply spectral_sum_eq_of_charpoly_mul_X_pow
    (posSemidef_sqrt_mul_sqrt σ₁ σ₂).isHermitian
    (posSemidef_sqrt_mul_sqrt ρ₁ ρ₂).isHermitian (k := 0) (l := 0)
  · rw [pow_zero, mul_one, mul_one, hprod, Matrix.charpoly_reindex]
  · exact Real.sqrt_zero

end PolarCodes
