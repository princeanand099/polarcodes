/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.Bhattacharyya

/-!
# Frenkel's Integral Formula, Data Processing Inequality, and Lemma 5.1(a)

This module proves:
1. Positive/negative spectral trace parts `posPartTrace`, `negPartTrace` and Frenkel's
   contraction lemma (`negPartTrace_map_le`) for positive trace-nonincreasing linear maps,
   instantiated on the partial trace `partialTrace₂Mat`.
2. Sylvester's Law of Inertia (`negEigCount_congruence`) for Hermitian matrices under
   invertible congruence `P * A * Pᴴ`.
3. **Frenkel's Integral Formula (Eq. 3.7)** (`relEntropy_frenkel_integral`) and its
   **Hockey-Stick Form (Eq. 3.8)** (`relEntropy_hockeyStick_integral`) for full-rank states,
   proved purely real-analytically via the congruence `X(t, r) = (ρ + r I)^{1/2}(I + t M(r))(ρ + r I)^{1/2}`,
   Sylvester's inertia, layer-cake representation, elementary partial fractions, and Tonelli's theorem.
4. **Data Processing Inequality (DPI)** for `relEntropy` and `qjs` under `partialTrace₂`
   (`relEntropy_partialTrace₂_le`, `qjs_partialTrace₂_le`).
5. **Lemma 5.1(a)** (`condEntropy_ge_one_sub_h2`, `fidelityParam_le_sqrt_condEntropy`,
   `condEntropy_le_logb_one_add_fidelityParam`).
-/

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodes

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-! ### Positive and Negative Spectral Trace Parts -/

/-- Positive spectral trace `Tr(A_+)` of a Hermitian matrix `A`. -/
noncomputable def posPartTrace {A : Matrix d d ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i : d, max (hA.eigenvalues i) 0

/-- Negative spectral trace `Tr(A_-)` of a Hermitian matrix `A`. -/
noncomputable def negPartTrace {A : Matrix d d ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i : d, max (-hA.eigenvalues i) 0

/-- Positive spectral part `A_+ = U diag(max(λ_i, 0)) U†` of a Hermitian matrix `A`. -/
noncomputable def posPartMat {A : Matrix d d ℂ} (hA : A.IsHermitian) : Matrix d d ℂ :=
  (hA.eigenvectorUnitary : Matrix d d ℂ) *
    Matrix.diagonal (fun i ↦ ((max (hA.eigenvalues i) 0 : ℝ) : ℂ)) *
    star (hA.eigenvectorUnitary : Matrix d d ℂ)

/-- Negative spectral part `A_- = U diag(max(-λ_i, 0)) U†` of a Hermitian matrix `A`. -/
noncomputable def negPartMat {A : Matrix d d ℂ} (hA : A.IsHermitian) : Matrix d d ℂ :=
  (hA.eigenvectorUnitary : Matrix d d ℂ) *
    Matrix.diagonal (fun i ↦ ((max (-hA.eigenvalues i) 0 : ℝ) : ℂ)) *
    star (hA.eigenvectorUnitary : Matrix d d ℂ)

lemma posPartTrace_nonneg {A : Matrix d d ℂ} (hA : A.IsHermitian) : 0 ≤ posPartTrace hA :=
  Finset.sum_nonneg fun _ _ ↦ le_max_right _ _

lemma negPartTrace_nonneg {A : Matrix d d ℂ} (hA : A.IsHermitian) : 0 ≤ negPartTrace hA :=
  Finset.sum_nonneg fun _ _ ↦ le_max_right _ _

lemma posPartTrace_eq_of_eq {A B : Matrix d d ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : posPartTrace hA = posPartTrace hB := by
  subst h; rfl

lemma negPartTrace_eq_of_eq {A B : Matrix d d ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : negPartTrace hA = negPartTrace hB := by
  subst h; rfl

lemma posPartMat_posSemidef {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    (posPartMat hA).PosSemidef := by
  unfold posPartMat
  have hD : (Matrix.diagonal (fun i : d ↦ ((max (hA.eigenvalues i) 0 : ℝ) : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i; exact_mod_cast le_max_right (hA.eigenvalues i) 0
  simpa [Matrix.star_eq_conjTranspose] using
    hD.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix d d ℂ)

lemma negPartMat_posSemidef {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    (negPartMat hA).PosSemidef := by
  unfold negPartMat
  have hD : (Matrix.diagonal (fun i : d ↦ ((max (-hA.eigenvalues i) 0 : ℝ) : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i; exact_mod_cast le_max_right (-hA.eigenvalues i) 0
  simpa [Matrix.star_eq_conjTranspose] using
    hD.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix d d ℂ)

lemma posPartMat_sub_negPartMat {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    posPartMat hA - negPartMat hA = A := by
  unfold posPartMat negPartMat
  set U : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  have hD : Matrix.diagonal (fun i : d ↦ ((max (hA.eigenvalues i) 0 : ℝ) : ℂ)) -
      Matrix.diagonal (fun i : d ↦ ((max (-hA.eigenvalues i) 0 : ℝ) : ℂ)) =
      Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.diagonal_apply, Function.comp_apply]
    split_ifs
    · rw [← Complex.ofReal_sub]; congr 1
      rcases le_or_gt 0 (hA.eigenvalues i) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right (le_of_lt h), max_eq_left (by linarith)]; ring
    · simp
  rw [hD]
  have hspec := hA.spectral_theorem
  simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hspec.symm

lemma trace_posPartMat {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    (posPartMat hA).trace = (posPartTrace hA : ℂ) := by
  unfold posPartMat posPartTrace
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self hA.eigenvectorUnitary,
    Matrix.one_mul, Matrix.trace_diagonal, Complex.ofReal_sum]

lemma trace_negPartMat {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    (negPartMat hA).trace = (negPartTrace hA : ℂ) := by
  unfold negPartMat negPartTrace
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self hA.eigenvectorUnitary,
    Matrix.one_mul, Matrix.trace_diagonal, Complex.ofReal_sum]

lemma posPartTrace_sub_negPartTrace {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    posPartTrace hA - negPartTrace hA = (A.trace).re := by
  have h := congr_arg Matrix.trace (posPartMat_sub_negPartMat hA)
  rw [Matrix.trace_sub, trace_posPartMat, trace_negPartMat] at h
  have hre := congr_arg Complex.re h
  simpa using hre

lemma negPartTrace_eq_posPartTrace_neg {A : Matrix d d ℂ} (hA : A.IsHermitian)
    (hneg : (-A).IsHermitian := hA.neg) :
    negPartTrace hA = posPartTrace hneg := by
  unfold negPartTrace posPartTrace
  set U : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
  have hspec : A = U * Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) * star U := by
    simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  let lam : d → ℝ := fun i ↦ -hA.eigenvalues i
  have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext i; simp
  have hneg_eq : -A = U * Matrix.diagonal (Complex.ofReal ∘ lam) * star U := by
    rw [hspec, ← Matrix.neg_mul, ← Matrix.mul_neg]
    congr 2; ext i j
    simp only [Matrix.neg_apply, Matrix.diagonal_apply, Function.comp_apply, lam]
    split_ifs <;> simp
  have hcp : (-A).charpoly = (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
    rw [hneg_eq, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self hA.eigenvectorUnitary, Matrix.one_mul]
  symm
  trans ∑ i : d, max (hD_herm.eigenvalues i) 0
  · exact spectral_sum_eq_of_charpoly_mul_X_pow (f := fun x ↦ max x 0) hneg hD_herm (k := 0) (l := 0)
      (by rw [pow_zero, mul_one, mul_one, hcp]) (max_self 0)
  · exact spectral_sum_diagonal (f := fun x ↦ max x 0) lam hD_herm (max_self 0)

lemma posPartTrace_smul_nonneg {c : ℝ} (hc : 0 ≤ c) {A : Matrix d d ℂ} (hA : A.IsHermitian)
    (hcA : ((c : ℂ) • A).IsHermitian) :
    posPartTrace hcA = c * posPartTrace hA := by
  unfold posPartTrace
  set U : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
  have hspec : A = U * Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) * star U := by
    simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  let lam : d → ℝ := fun i ↦ c * hA.eigenvalues i
  have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext i; simp
  have hsmul_eq : (c : ℂ) • A = U * Matrix.diagonal (Complex.ofReal ∘ lam) * star U := by
    rw [hspec, ← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2; ext i j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply, lam, smul_eq_mul]
    split_ifs <;> simp
  have hcp : ((c : ℂ) • A).charpoly = (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
    rw [hsmul_eq, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self hA.eigenvectorUnitary, Matrix.one_mul]
  trans ∑ i : d, max (lam i) 0
  · trans ∑ i : d, max (hD_herm.eigenvalues i) 0
    · exact spectral_sum_eq_of_charpoly_mul_X_pow (f := fun x ↦ max x 0) hcA hD_herm (k := 0) (l := 0)
        (by rw [pow_zero, mul_one, mul_one, hcp]) (max_self 0)
    · exact spectral_sum_diagonal (f := fun x ↦ max x 0) lam hD_herm (max_self 0)
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    simp only [lam]
    rw [mul_max_of_nonneg _ _ hc, mul_zero]

lemma negPartTrace_smul_nonneg {c : ℝ} (hc : 0 ≤ c) {A : Matrix d d ℂ} (hA : A.IsHermitian)
    (hcA : ((c : ℂ) • A).IsHermitian) :
    negPartTrace hcA = c * negPartTrace hA := by
  have h1 := negPartTrace_eq_posPartTrace_neg hcA
  have h2 := negPartTrace_eq_posPartTrace_neg hA
  rw [h1, h2]
  have heq : -((c : ℂ) • A) = (c : ℂ) • (-A) := by simp
  rw [posPartTrace_eq_of_eq hcA.neg (by rw [← heq]; exact hcA.neg) heq]
  exact posPartTrace_smul_nonneg hc hA.neg _

/-- Trace of product of two positive semidefinite matrices has nonnegative real part. -/
lemma re_trace_mul_nonneg_of_posSemidef {X Y : Matrix d d ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ (X * Y).trace.re := by
  set U : Matrix d d ℂ := (hX.isHermitian.eigenvectorUnitary : Matrix d d ℂ)
  set D : Matrix d d ℂ := Matrix.diagonal (fun i : d ↦ ((Real.sqrt (hX.isHermitian.eigenvalues i) : ℝ) : ℂ))
  set S : Matrix d d ℂ := U * D * star U
  have hSS : S * S = X := by
    have hD : D * D = Matrix.diagonal (Complex.ofReal ∘ hX.isHermitian.eigenvalues) := by
      simp only [D, Matrix.diagonal_mul_diagonal]
      congr 1; ext i
      simp only [Function.comp_apply, ← Complex.ofReal_mul, Real.mul_self_sqrt (hX.eigenvalues_nonneg i)]
    calc S * S = U * (D * ((star U * U) * D)) * star U := by simp only [S, Matrix.mul_assoc]
      _ = U * (D * D) * star U := by rw [Unitary.coe_star_mul_self hX.isHermitian.eigenvectorUnitary, Matrix.one_mul]
      _ = U * Matrix.diagonal (Complex.ofReal ∘ hX.isHermitian.eigenvalues) * star U := by rw [hD]
      _ = X := by simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hX.isHermitian.spectral_theorem.symm
  have hSH : S.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      ← Matrix.star_eq_conjTranspose, star_star, Matrix.diagonal_conjTranspose]
    have hD' : (star (fun i : d ↦ ((Real.sqrt (hX.isHermitian.eigenvalues i) : ℝ) : ℂ))) =
        fun i : d ↦ ((Real.sqrt (hX.isHermitian.eigenvalues i) : ℝ) : ℂ) := by ext i; simp
    simp only [S, D, hD', Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have htr : (X * Y).trace = (S * Y * S).trace := by
    rw [← hSS, Matrix.mul_assoc, Matrix.trace_mul_comm S, ← Matrix.mul_assoc]
  have hPSD : (S * Y * S).PosSemidef := by
    simpa [hSH.eq] using hY.mul_mul_conjTranspose_same S
  rw [htr]
  have hsum : (S * Y * S).trace = ∑ i : d, (hPSD.isHermitian.eigenvalues i : ℂ) := by
    set V : Matrix d d ℂ := (hPSD.isHermitian.eigenvectorUnitary : Matrix d d ℂ)
    have hspec : S * Y * S = V * Matrix.diagonal (Complex.ofReal ∘ hPSD.isHermitian.eigenvalues) * star V := by
      simpa [V, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hPSD.isHermitian.spectral_theorem
    conv_lhs => rw [hspec]
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self hPSD.isHermitian.eigenvectorUnitary,
      Matrix.one_mul, Matrix.trace_diagonal]; rfl
  rw [hsum, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ ↦ by simpa using hPSD.eigenvalues_nonneg i

/-- **Variational upper bound for `posPartTrace`**: if `B ≽ 0` and `B - A ≽ 0`, then
`Tr(A_+) ≤ Re Tr(B)`. -/
lemma posPartTrace_le_trace_of_le {A B : Matrix d d ℂ} (hA : A.IsHermitian)
    (hB : B.PosSemidef) (hBA : (B - A).PosSemidef) :
    posPartTrace hA ≤ B.trace.re := by
  set U : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
  let indP : d → ℝ := fun i ↦ if 0 < hA.eigenvalues i then 1 else 0
  let P : Matrix d d ℂ := U * Matrix.diagonal (fun i ↦ (indP i : ℂ)) * star U
  let Q : Matrix d d ℂ := U * Matrix.diagonal (fun i ↦ ((1 - indP i : ℝ) : ℂ)) * star U
  have hP_psd : P.PosSemidef := by
    have hD : (Matrix.diagonal (fun i : d ↦ (indP i : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]; intro i
      simp only [indP]; split_ifs <;> norm_num
    simpa [P, Matrix.star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same U
  have hQ_psd : Q.PosSemidef := by
    have hD : (Matrix.diagonal (fun i : d ↦ ((1 - indP i : ℝ) : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]; intro i
      simp only [indP]; split_ifs <;> norm_num
    simpa [Q, Matrix.star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same U
  have hPQ : P + Q = 1 := by
    simp only [P, Q, ← Matrix.add_mul, ← Matrix.mul_add]
    have hD : Matrix.diagonal (fun i : d ↦ (indP i : ℂ)) +
        Matrix.diagonal (fun i : d ↦ ((1 - indP i : ℝ) : ℂ)) = 1 := by
      ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply]
      split_ifs
      · push_cast; ring
      · simp
    rw [hD, Matrix.mul_one]; exact Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hPA : (P * A).trace = (posPartTrace hA : ℂ) := by
    have hspec : A = U * Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) * star U := by
      simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
    have hmul : P * A = U * Matrix.diagonal (fun i : d ↦ ((max (hA.eigenvalues i) 0 : ℝ) : ℂ)) * star U := by
      calc P * A = U * (Matrix.diagonal (fun i ↦ (indP i : ℂ)) *
              ((star U * U) * Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues))) * star U := by
            conv_lhs => rw [hspec]
            simp only [P, Matrix.mul_assoc]
        _ = U * (Matrix.diagonal (fun i ↦ (indP i : ℂ)) *
              Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues)) * star U := by
            rw [Unitary.coe_star_mul_self hA.eigenvectorUnitary, Matrix.one_mul]
        _ = U * Matrix.diagonal (fun i : d ↦ ((max (hA.eigenvalues i) 0 : ℝ) : ℂ)) * star U := by
            congr 2; rw [Matrix.diagonal_mul_diagonal]; congr 1; ext i
            simp only [indP, Function.comp_apply]
            split_ifs with h
            · simp [max_eq_left (le_of_lt h)]
            · simp [max_eq_right (le_of_not_gt h)]
    rw [hmul, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self hA.eigenvectorUnitary,
      Matrix.one_mul, Matrix.trace_diagonal, posPartTrace, Complex.ofReal_sum]
  have hdiff : B.trace - (posPartTrace hA : ℂ) = (Q * B).trace + (P * (B - A)).trace := by
    have hBsplit : B.trace = (Q * B).trace + (P * B).trace := by
      rw [← Matrix.trace_add, ← Matrix.add_mul, add_comm Q P, hPQ, Matrix.one_mul]
    rw [← hPA, Matrix.mul_sub, Matrix.trace_sub, hBsplit]
    ring
  have hre := congr_arg Complex.re hdiff
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re] at hre
  have h1 := re_trace_mul_nonneg_of_posSemidef hQ_psd hB
  have h2 := re_trace_mul_nonneg_of_posSemidef hP_psd hBA
  linarith

/-- **Frenkel Lemma 8**: Any linear map `ℰ` preserving positive semidefiniteness and not increasing
the trace of PSD matrices contracts `posPartTrace` and `negPartTrace`. -/
lemma posPartTrace_map_le (ℰ : Matrix d₁ d₁ ℂ →ₗ[ℂ] Matrix d₂ d₂ ℂ)
    (hpos : ∀ X : Matrix d₁ d₁ ℂ, X.PosSemidef → (ℰ X).PosSemidef)
    (htr : ∀ X : Matrix d₁ d₁ ℂ, X.PosSemidef → (ℰ X).trace.re ≤ X.trace.re)
    {A : Matrix d₁ d₁ ℂ} (hA : A.IsHermitian) (hEA : (ℰ A).IsHermitian) :
    posPartTrace hEA ≤ posPartTrace hA := by
  have h1 : (ℰ (posPartMat hA)).PosSemidef := hpos _ (posPartMat_posSemidef hA)
  have h2 : (ℰ (posPartMat hA) - ℰ A).PosSemidef := by
    rw [← map_sub, show posPartMat hA - A = negPartMat hA by
      have hsub := posPartMat_sub_negPartMat hA
      calc posPartMat hA - A = posPartMat hA - (posPartMat hA - negPartMat hA) := by
            congr 1; exact hsub.symm
        _ = negPartMat hA := by abel]
    exact hpos _ (negPartMat_posSemidef hA)
  calc posPartTrace hEA
      ≤ (ℰ (posPartMat hA)).trace.re := posPartTrace_le_trace_of_le hEA h1 h2
    _ ≤ (posPartMat hA).trace.re := htr _ (posPartMat_posSemidef hA)
    _ = posPartTrace hA := by rw [trace_posPartMat, Complex.ofReal_re]

lemma negPartTrace_map_le (ℰ : Matrix d₁ d₁ ℂ →ₗ[ℂ] Matrix d₂ d₂ ℂ)
    (hpos : ∀ X : Matrix d₁ d₁ ℂ, X.PosSemidef → (ℰ X).PosSemidef)
    (htr : ∀ X : Matrix d₁ d₁ ℂ, X.PosSemidef → (ℰ X).trace.re ≤ X.trace.re)
    {A : Matrix d₁ d₁ ℂ} (hA : A.IsHermitian) (hEA : (ℰ A).IsHermitian) :
    negPartTrace hEA ≤ negPartTrace hA := by
  rw [negPartTrace_eq_posPartTrace_neg hEA, negPartTrace_eq_posPartTrace_neg hA]
  have hneg : -ℰ A = ℰ (-A) := (map_neg ℰ A).symm
  rw [posPartTrace_eq_of_eq hEA.neg (by rw [← hneg]; exact hEA.neg) hneg]
  exact posPartTrace_map_le ℰ hpos htr hA.neg _

/-- Partial trace as a `ℂ`-linear map on matrices. -/
def partialTrace₂Mat (d₁ d₂ : Type*) [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂] :
    Matrix (d₁ × d₂) (d₁ × d₂) ℂ →ₗ[ℂ] Matrix d₁ d₁ ℂ where
  toFun M := Matrix.of fun i j ↦ ∑ k : d₂, M (i, k) (j, k)
  map_add' A B := by ext i j; simp [Finset.sum_add_distrib]
  map_smul' c A := by ext i j; simp [Finset.mul_sum]

lemma partialTrace₂Mat_posSemidef {X : Matrix (d₁ × d₂) (d₁ × d₂) ℂ} (hX : X.PosSemidef) :
    (partialTrace₂Mat d₁ d₂ X).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_apply,
      Matrix.of_apply, star_sum]
    apply Finset.sum_congr rfl; intro k _
    have hh := congr_fun (congr_fun hX.isHermitian.eq (i, k)) (j, k)
    simpa [Matrix.conjTranspose_apply] using hh
  · intro x
    have hsum' : star x ⬝ᵥ (partialTrace₂Mat d₁ d₂ X).mulVec x =
        ∑ k : d₂, star (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) ⬝ᵥ
          X.mulVec (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) := by
      trans ∑ k : d₂, ∑ i : d₁, star (x i) * ∑ j : d₁, X (i, k) (j, k) * x j
      · simp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Matrix.mulVec,
          Matrix.of_apply, Pi.star_apply]
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
      · apply Finset.sum_congr rfl; intro k _
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl; intro i _
        simp only [apply_ite star, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte]
        congr 1
        apply Finset.sum_congr rfl; intro j _
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [hsum']
    exact Finset.sum_nonneg fun k _ ↦ (Matrix.posSemidef_iff_dotProduct_mulVec.mp hX).2 _

lemma partialTrace₂Mat_trace (X : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
    (partialTrace₂Mat d₁ d₂ X).trace = X.trace := by
  simp [partialTrace₂Mat, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

lemma partialTrace₂Mat_isHermitian {A : Matrix (d₁ × d₂) (d₁ × d₂) ℂ} (hA : A.IsHermitian) :
    (partialTrace₂Mat d₁ d₂ A).IsHermitian := by
  ext i j
  simp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_apply,
    Matrix.of_apply, star_sum]
  apply Finset.sum_congr rfl; intro k _
  have hh := congr_fun (congr_fun hA.eq (i, k)) (j, k)
  simpa [Matrix.conjTranspose_apply] using hh

/-! ### Sylvester's Law of Inertia (Negative Eigenvalue Count under Congruence) -/

/-- Number of strictly negative eigenvalues of a Hermitian matrix `A`. -/
noncomputable def negEigCount {A : Matrix d d ℂ} (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i : d ↦ hA.eigenvalues i < 0).card

lemma negEigCount_eq_of_eq {A B : Matrix d d ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : negEigCount hA = negEigCount hB := by
  subst h; rfl

/-- Helper: quadratic form of a Hermitian matrix `A` in its eigenvector basis. -/
lemma re_quadForm_spectral {A : Matrix d d ℂ} (hA : A.IsHermitian) (x : d → ℂ) :
    (star x ⬝ᵥ A.mulVec x).re =
      ∑ i : d, hA.eigenvalues i * ‖((star (hA.eigenvectorUnitary : Matrix d d ℂ)).mulVec x) i‖ ^ 2 := by
  set U : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
  have hspec : A = U * Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) * star U := by
    simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  set y : d → ℂ := (star U).mulVec x
  have hquad : star x ⬝ᵥ A.mulVec x = ∑ i : d, ((hA.eigenvalues i : ℝ) : ℂ) * ((‖y i‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : A.mulVec x = U.mulVec ((Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues)).mulVec y) := by
      conv_lhs => rw [hspec]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [h1, Matrix.dotProduct_mulVec, show star x ᵥ* U = star y by
      ext i
      simp only [y, Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply, Matrix.star_apply,
        star_sum, star_mul', star_star]
      apply Finset.sum_congr rfl; intro j _; ring]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Function.comp_apply]
    apply Finset.sum_congr rfl; intro i _
    rw [← mul_assoc, mul_comm (star (y i)), mul_assoc, mul_comm (star (y i)),
      Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hquad, Complex.re_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- Subspace criterion for `negEigCount`: if `W ⊆ (d → ℂ)` is a subspace on which
`Re ⟨x, A x⟩ < 0` for all `x ∈ W \ {0}`, then `finrank W ≤ negEigCount hA`. -/
lemma finrank_le_negEigCount {A : Matrix d d ℂ} (hA : A.IsHermitian)
    (W : Submodule ℂ (d → ℂ))
    (hneg : ∀ x ∈ W, x ≠ 0 → (star x ⬝ᵥ A.mulVec x).re < 0) :
    Module.finrank ℂ W ≤ negEigCount hA := by
  set U : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
  let S_pos : Finset d := Finset.univ.filter fun i : d ↦ 0 ≤ hA.eigenvalues i
  let V_pos : Submodule ℂ (d → ℂ) :=
    { carrier := {x : d → ℂ | ∀ i : d, hA.eigenvalues i < 0 → ((star U).mulVec x) i = 0}
      add_mem' := fun hx hy i hi ↦ by rw [Matrix.mulVec_add, Pi.add_apply, hx i hi, hy i hi, add_zero]
      zero_mem' := fun i _ ↦ by simp
      smul_mem' := fun c x hx i hi ↦ by rw [Matrix.mulVec_smul, Pi.smul_apply, hx i hi, smul_zero] }
  have hV_nonneg : ∀ x ∈ V_pos, 0 ≤ (star x ⬝ᵥ A.mulVec x).re := by
    intro x hx
    rw [re_quadForm_spectral hA x]
    apply Finset.sum_nonneg; intro i _
    by_cases hlt : hA.eigenvalues i < 0
    · rw [hx i hlt]; simp
    · exact mul_nonneg (le_of_not_gt hlt) (sq_nonneg _)
  have hinf : W ⊓ V_pos = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x ⟨hxW, hxV⟩
    by_contra hne
    linarith [hneg x hxW hne, hV_nonneg x hxV]
  let eU : (d → ℂ) ≃ₗ[ℂ] (d → ℂ) :=
    LinearEquiv.ofLinear (Matrix.toLin' (star U)) (Matrix.toLin' U)
      (LinearMap.ext fun v ↦ by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, U, Unitary.coe_star_mul_self hA.eigenvectorUnitary])
      (LinearMap.ext fun v ↦ by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, U, Unitary.coe_mul_star_self hA.eigenvectorUnitary])
  let K : Submodule ℂ (d → ℂ) :=
    { carrier := {y : d → ℂ | ∀ i : d, hA.eigenvalues i < 0 → y i = 0}
      add_mem' := fun hx hy i hi ↦ by simp [hx i hi, hy i hi]
      zero_mem' := fun _ _ ↦ rfl
      smul_mem' := fun c x hx i hi ↦ by simp [hx i hi] }
  have hV_eq : V_pos = K.comap eU.toLinearMap := by
    ext x; rfl
  have hK_finrank : Module.finrank ℂ K = S_pos.card := by
    let eK : K ≃ₗ[ℂ] ({i : d // i ∈ S_pos} → ℂ) :=
      { toFun := fun y i ↦ y.1 i.1
        invFun := fun f ↦ ⟨fun i ↦ if hi : i ∈ S_pos then f ⟨i, hi⟩ else 0, by
          intro i hi
          have hnot : i ∉ S_pos := by simp [S_pos]; linarith
          simp [hnot]⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        left_inv := fun y ↦ by
          ext i
          by_cases hi : i ∈ S_pos
          · simp [hi]
          · simp only [hi, ↓reduceDIte]
            have hlt : hA.eigenvalues i < 0 := by simp [S_pos] at hi; exact hi
            exact (y.2 i hlt).symm
        right_inv := fun f ↦ by ext ⟨i, hi⟩; simp [hi] }
    rw [eK.finrank_eq, Module.finrank_pi, Fintype.card_coe]
  have hV_finrank : Module.finrank ℂ V_pos = S_pos.card := by
    rw [hV_eq, ← hK_finrank]
    have hmc : Submodule.map eU.toLinearMap (K.comap eU.toLinearMap) = K :=
      Submodule.map_comap_eq_self (by rw [LinearMap.range_eq_top.mpr eU.surjective]; exact le_top)
    calc Module.finrank ℂ (K.comap eU.toLinearMap)
        = Module.finrank ℂ (Submodule.map eU.toLinearMap (K.comap eU.toLinearMap)) :=
          (Submodule.equivMapOfInjective eU.toLinearMap eU.injective (K.comap eU.toLinearMap)).finrank_eq
      _ = Module.finrank ℂ K := by rw [hmc]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W V_pos
  rw [hinf, finrank_bot, add_zero, hV_finrank] at hdim
  have hle : Module.finrank ℂ ↥(W ⊔ V_pos) ≤ Fintype.card d := by
    have h := Submodule.finrank_le (W ⊔ V_pos)
    rwa [Module.finrank_pi] at h
  have htot : S_pos.card + negEigCount hA = Fintype.card d := by
    unfold negEigCount
    have h : S_pos.card + (Finset.univ.filter fun i : d ↦ ¬ 0 ≤ hA.eigenvalues i).card = Fintype.card d := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ h2 h1)]
      have hunion : S_pos ∪ (Finset.univ.filter fun i : d ↦ ¬ 0 ≤ hA.eigenvalues i) = Finset.univ := by
        ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, S_pos]; exact em (0 ≤ hA.eigenvalues i)
      rw [hunion, Finset.card_univ]
    have hneg_eq : (Finset.univ.filter fun i : d ↦ ¬ 0 ≤ hA.eigenvalues i) =
        Finset.univ.filter fun i : d ↦ hA.eigenvalues i < 0 := by
      ext i; simp [not_le]
    rw [hneg_eq] at h
    exact h
  omega

/-- **Sylvester's Law of Inertia**: For any Hermitian `A` and invertible `P`, `P * A * Pᴴ` has the
same number of negative eigenvalues as `A`. -/
theorem negEigCount_congruence {A P Q : Matrix d d ℂ} (hA : A.IsHermitian)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hB : (P * A * Pᴴ).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]) :
    negEigCount hB = negEigCount hA := by
  have hle : ∀ {X Y M N : Matrix d d ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian),
      M * N = 1 → N * M = 1 → Y = M * X * Mᴴ → negEigCount hX ≤ negEigCount hY := by
    intro X Y M N hX hY hMN hNM hYeq
    set U : Matrix d d ℂ := (hX.eigenvectorUnitary : Matrix d d ℂ)
    let V_neg : Submodule ℂ (d → ℂ) :=
      { carrier := {x : d → ℂ | ∀ i : d, 0 ≤ hX.eigenvalues i → ((star U).mulVec x) i = 0}
        add_mem' := fun hx hy i hi ↦ by rw [Matrix.mulVec_add, Pi.add_apply, hx i hi, hy i hi, add_zero]
        zero_mem' := fun i _ ↦ by simp
        smul_mem' := fun c x hx i hi ↦ by rw [Matrix.mulVec_smul, Pi.smul_apply, hx i hi, smul_zero] }
    have hV_finrank : Module.finrank ℂ V_neg = negEigCount hX := by
      let S_neg : Finset d := Finset.univ.filter fun i : d ↦ hX.eigenvalues i < 0
      let eU : (d → ℂ) ≃ₗ[ℂ] (d → ℂ) :=
        LinearEquiv.ofLinear (Matrix.toLin' (star U)) (Matrix.toLin' U)
          (LinearMap.ext fun v ↦ by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, U, Unitary.coe_star_mul_self hX.eigenvectorUnitary])
          (LinearMap.ext fun v ↦ by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, U, Unitary.coe_mul_star_self hX.eigenvectorUnitary])
      let K : Submodule ℂ (d → ℂ) :=
        { carrier := {y : d → ℂ | ∀ i : d, 0 ≤ hX.eigenvalues i → y i = 0}
          add_mem' := fun hx hy i hi ↦ by simp [hx i hi, hy i hi]
          zero_mem' := fun _ _ ↦ rfl
          smul_mem' := fun c x hx i hi ↦ by simp [hx i hi] }
      have hK_fin : Module.finrank ℂ K = negEigCount hX := by
        let eK : K ≃ₗ[ℂ] ({i : d // i ∈ S_neg} → ℂ) :=
          { toFun := fun y i ↦ y.1 i.1
            invFun := fun f ↦ ⟨fun i ↦ if hi : i ∈ S_neg then f ⟨i, hi⟩ else 0, by
              intro i hi
              have hnot : i ∉ S_neg := by simp [S_neg]; linarith
              simp [hnot]⟩
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl
            left_inv := fun y ↦ by
              ext i
              by_cases hi : i ∈ S_neg
              · simp [hi]
              · simp only [hi, ↓reduceDIte]
                have hge : 0 ≤ hX.eigenvalues i := by simp [S_neg] at hi; exact hi
                exact (y.2 i hge).symm
            right_inv := fun f ↦ by ext ⟨i, hi⟩; simp [hi] }
        rw [eK.finrank_eq, Module.finrank_pi, Fintype.card_coe]; rfl
      have hV_eq : V_neg = K.comap eU.toLinearMap := by ext x; rfl
      rw [hV_eq, ← hK_fin]
      have hmc : Submodule.map eU.toLinearMap (K.comap eU.toLinearMap) = K :=
        Submodule.map_comap_eq_self (by rw [LinearMap.range_eq_top.mpr eU.surjective]; exact le_top)
      calc Module.finrank ℂ (K.comap eU.toLinearMap)
          = Module.finrank ℂ (Submodule.map eU.toLinearMap (K.comap eU.toLinearMap)) :=
            (Submodule.equivMapOfInjective eU.toLinearMap eU.injective (K.comap eU.toLinearMap)).finrank_eq
        _ = Module.finrank ℂ K := by rw [hmc]
    have hV_neg_strict : ∀ x ∈ V_neg, x ≠ 0 → (star x ⬝ᵥ X.mulVec x).re < 0 := by
      intro x hx hne
      rw [re_quadForm_spectral hX x]
      have hy_ne : (star U).mulVec x ≠ 0 := by
        intro hy0; apply hne
        have := congr_arg U.mulVec hy0
        rw [Matrix.mulVec_mulVec, show U * star U = 1 from Unitary.coe_mul_star_self hX.eigenvectorUnitary,
          Matrix.one_mulVec, Matrix.mulVec_zero] at this
        exact this
      obtain ⟨i₀, hi₀⟩ : ∃ i₀ : d, ((star U).mulVec x) i₀ ≠ 0 := by
        by_contra hall; push Not at hall; exact hy_ne (funext hall)
      have hlt₀ : hX.eigenvalues i₀ < 0 := by
        by_contra hge; exact hi₀ (hx i₀ (le_of_not_gt hge))
      have hterm_lt : hX.eigenvalues i₀ * ‖((star U).mulVec x) i₀‖ ^ 2 < 0 :=
        mul_neg_of_neg_of_pos hlt₀ (sq_pos_of_pos (norm_pos_iff.mpr hi₀))
      have hterm_le : ∀ i : d, hX.eigenvalues i * ‖((star U).mulVec x) i‖ ^ 2 ≤ 0 := by
        intro i
        by_cases hge : 0 ≤ hX.eigenvalues i
        · rw [hx i hge]; simp
        · exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hge)) (sq_nonneg _)
      have hsplit := Finset.add_sum_erase Finset.univ
        (fun i : d ↦ hX.eigenvalues i * ‖((star U).mulVec x) i‖ ^ 2) (Finset.mem_univ i₀)
      have hrest : ∑ i ∈ Finset.univ.erase i₀, hX.eigenvalues i * ‖((star U).mulVec x) i‖ ^ 2 ≤ 0 :=
        Finset.sum_nonpos fun i _ ↦ hterm_le i
      linarith
    let eN : (d → ℂ) ≃ₗ[ℂ] (d → ℂ) :=
      LinearEquiv.ofLinear (Matrix.toLin' Nᴴ) (Matrix.toLin' Mᴴ)
        (LinearMap.ext fun v ↦ by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul, hMN])
        (LinearMap.ext fun v ↦ by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul, hNM])
    let W := V_neg.map eN.toLinearMap
    have hW_fin : Module.finrank ℂ W = negEigCount hX := by
      rw [← hV_finrank]
      exact (Submodule.equivMapOfInjective eN.toLinearMap eN.injective V_neg).finrank_eq.symm
    rw [← hW_fin]
    apply finrank_le_negEigCount hY W
    intro w hw hne
    rcases hw with ⟨x, hx, rfl⟩
    have hx_ne : x ≠ 0 := by intro hx0; apply hne; simp [hx0]
    have hquad : star (eN.toLinearMap x) ⬝ᵥ Y.mulVec (eN.toLinearMap x) = star x ⬝ᵥ X.mulVec x := by
      simp only [eN, LinearEquiv.coe_toLinearMap, LinearEquiv.ofLinear_apply, Matrix.toLin'_apply]
      rw [hYeq, Matrix.mulVec_mulVec, Matrix.mul_assoc (M * X),
        show Mᴴ * Nᴴ = (N * M)ᴴ by rw [Matrix.conjTranspose_mul], hNM, Matrix.conjTranspose_one,
        Matrix.mul_one, Matrix.dotProduct_mulVec]
      have hvec : star (Nᴴ.mulVec x) ᵥ* M = star x := by
        ext j
        have hNM' : N * M = 1 := hNM
        simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply,
          Matrix.conjTranspose_apply, star_sum, star_mul', star_star]
        calc _ = ∑ i : d, star (x i) * (∑ k : d, N i k * M k j) := by
              simp_rw [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro k _; ring
          _ = ∑ i : d, star (x i) * (1 : Matrix d d ℂ) i j := by
              apply Finset.sum_congr rfl; intro i _
              have h := congr_fun (congr_fun hNM' i) j
              simpa [Matrix.mul_apply] using congr_arg (star (x i) * ·) h
          _ = star (x j) := by simp [Matrix.one_apply]
      rw [← Matrix.vecMul_vecMul, hvec, Matrix.dotProduct_mulVec]
    rw [hquad]
    exact hV_neg_strict x hx hx_ne
  apply le_antisymm
  · have hAeq : A = Q * (P * A * Pᴴ) * Qᴴ := by
      symm
      calc Q * (P * A * Pᴴ) * Qᴴ
          = (Q * P) * A * (Pᴴ * Qᴴ) := by simp only [Matrix.mul_assoc]
        _ = 1 * A * (1 : Matrix d d ℂ)ᴴ := by rw [← Matrix.conjTranspose_mul, hQP]
        _ = A := by rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    exact hle hB hA hQP hPQ hAeq
  · exact hle hA hB hPQ hQP rfl

end PolarCodes
