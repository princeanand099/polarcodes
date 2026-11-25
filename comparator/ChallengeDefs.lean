/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Standalone Challenge Definitions for `PolarCodes`

Self-contained Mathlib-only definitions of the public mathematical objects appearing in the
headline theorems of *Polynomial-Blocklength Quantum Polar Codes via Nonlinear Dephasing
Contraction* (Prince Anand, 2026), independent of the proof library `PolarCodes`.
-/

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodesChallenge

/-! ### Scalar Information-Theoretic Functions -/

/-- Binary entropy function `h₂(p) = -p log₂ p - (1 - p) log₂(1 - p)`. -/
noncomputable def h2 (p : ℝ) : ℝ :=
  -p * Real.logb 2 p - (1 - p) * Real.logb 2 (1 - p)

/-- Inverse binary entropy `h₂⁻¹ : [0, 1] → [0, 1/2]`. -/
noncomputable def h2Inv (u : ℝ) : ℝ :=
  sSup {p ∈ Set.Icc (0 : ℝ) (1 / 2) | h2 p ≤ u}

/-- Binary convolution `a * b := a(1 - b) + (1 - a)b`. -/
def binConv (a b : ℝ) : ℝ :=
  a * (1 - b) + (1 - a) * b

/-- Universal linear-splitting constant
`θ₀ := (32/3) h₂⁻¹(1/4) (1 - h₂(1 - 2^(-1/2))) > 0.05673`. -/
noncomputable def theta0 : ℝ :=
  (32 / 3) * h2Inv (1 / 4) * (1 - h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)))

/-- Universal potential contraction factor `Λ₀ := √(1 - θ₀²/4) < 0.99960`. -/
noncomputable def Lambda0 : ℝ :=
  Real.sqrt (1 - theta0 ^ 2 / 4)

/-! ### Finite-Dimensional Quantum States and Divergences -/

/-- A density operator (quantum state) on `ℂ^d`: positive semidefinite with trace `1`. -/
structure DensityOp (d : Type*) [Fintype d] [DecidableEq d] where
  mat : Matrix d d ℂ
  posSemidef : mat.PosSemidef
  trace_one : mat.trace = 1

namespace DensityOp

variable {d : Type*} [Fintype d] [DecidableEq d]

lemma isHermitian (ρ : DensityOp d) : ρ.mat.IsHermitian :=
  ρ.posSemidef.isHermitian

/-- Eigenvalues of a density operator `ρ`. -/
noncomputable def eigvals (ρ : DensityOp d) : d → ℝ :=
  ρ.isHermitian.eigenvalues

/-- Eigenvector unitary matrix of `ρ`. -/
noncomputable def eigUnitary (ρ : DensityOp d) : Matrix.unitaryGroup d ℂ :=
  ρ.isHermitian.eigenvectorUnitary

lemma eigvals_nonneg (ρ : DensityOp d) (i : d) : 0 ≤ ρ.eigvals i :=
  ρ.posSemidef.eigenvalues_nonneg i

/-- Positive semidefinite square root `√ρ`. -/
noncomputable def sqrtMat (ρ : DensityOp d) : Matrix d d ℂ :=
  (ρ.eigUnitary : Matrix d d ℂ) *
    Matrix.diagonal (fun i ↦ (Real.sqrt (ρ.eigvals i) : ℂ)) *
    star (ρ.eigUnitary : Matrix d d ℂ)

lemma sqrtMat_isHermitian (ρ : DensityOp d) : ρ.sqrtMat.IsHermitian := by
  unfold sqrtMat
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_star,
    Matrix.diagonal_conjTranspose]
  have hdiag : (star fun i ↦ (Real.sqrt (ρ.eigvals i) : ℂ)) =
      fun i ↦ (Real.sqrt (ρ.eigvals i) : ℂ) := by
    ext i; simp
  rw [hdiag, Matrix.mul_assoc]

lemma sqrtMat_mul_self (ρ : DensityOp d) : ρ.sqrtMat * ρ.sqrtMat = ρ.mat := by
  unfold sqrtMat
  set U : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
  set D : Matrix d d ℂ := Matrix.diagonal (fun i ↦ (Real.sqrt (ρ.eigvals i) : ℂ))
  have hU : star U * U = 1 := Unitary.coe_star_mul_self ρ.eigUnitary
  have hD : D * D = Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) := by
    simp only [D, Matrix.diagonal_mul_diagonal]
    congr 1; ext i
    simp only [Function.comp_apply, ← Complex.ofReal_mul, Real.mul_self_sqrt (ρ.eigvals_nonneg i)]
  have hspec : U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U = ρ.mat := by
    have h := ρ.isHermitian.spectral_theorem
    simpa [U, eigUnitary, eigvals, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply]
      using h.symm
  calc (U * D * star U) * (U * D * star U)
      = U * (D * ((star U * U) * D)) * star U := by simp only [Matrix.mul_assoc]
    _ = U * (D * D) * star U := by rw [hU, Matrix.one_mul]
    _ = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by rw [hD]
    _ = ρ.mat := hspec

/-- Convex mixture `(1 - p) ρ + p σ` for `p ∈ [0, 1]`. -/
noncomputable def mix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ σ : DensityOp d) : DensityOp d where
  mat := ((1 - p : ℝ) : ℂ) • ρ.mat + (p : ℂ) • σ.mat
  posSemidef := by
    have h1 : (((1 - p : ℝ) : ℂ) • ρ.mat).PosSemidef := by
      have : (((1 - p : ℝ) : ℂ) • ρ.mat) = (1 - p : ℝ) • ρ.mat := by
        ext i j; simp [Complex.real_smul]
      rw [this]; exact ρ.posSemidef.smul (by linarith : (0 : ℝ) ≤ 1 - p)
    have h2 : ((p : ℂ) • σ.mat).PosSemidef := by
      have : ((p : ℂ) • σ.mat) = p • σ.mat := by
        ext i j; simp [Complex.real_smul]
      rw [this]; exact σ.posSemidef.smul hp0
    exact h1.add h2
  trace_one := by
    simp [Matrix.trace_add, Matrix.trace_smul, ρ.trace_one, σ.trace_one]

/-- Uniform midpoint `(ρ + σ) / 2`. -/
noncomputable def midpoint (ρ σ : DensityOp d) : DensityOp d :=
  mix (1 / 2) (by norm_num) (by norm_num) ρ σ

/-- Tensor product `ρ ⊗ σ` on `d₁ × d₂`. -/
noncomputable def tensor {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (ρ : DensityOp d₁) (σ : DensityOp d₂) :
    DensityOp (d₁ × d₂) where
  mat := Matrix.kroneckerMap (· * ·) ρ.mat σ.mat
  posSemidef := by
    have hct : (Matrix.kroneckerMap (· * ·) ρ.sqrtMat σ.sqrtMat)ᴴ =
        Matrix.kroneckerMap (· * ·) ρ.sqrtMatᴴ σ.sqrtMatᴴ := by
      ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
      simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, star_mul, mul_comm]
    have hK : Matrix.kroneckerMap (· * ·) ρ.mat σ.mat =
        (Matrix.kroneckerMap (· * ·) ρ.sqrtMat σ.sqrtMat)ᴴ *
          Matrix.kroneckerMap (· * ·) ρ.sqrtMat σ.sqrtMat := by
      rw [hct, ρ.sqrtMat_isHermitian.eq, σ.sqrtMat_isHermitian.eq,
        ← Matrix.mul_kronecker_mul, ρ.sqrtMat_mul_self, σ.sqrtMat_mul_self]
    rw [hK]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  trace_one := by
    rw [Matrix.trace_kronecker, ρ.trace_one, σ.trace_one, mul_one]

/-- Unitary conjugation `U ρ U†`. -/
noncomputable def conjUnitary (U : Matrix.unitaryGroup d ℂ) (ρ : DensityOp d) : DensityOp d where
  mat := (U : Matrix d d ℂ) * ρ.mat * star (U : Matrix d d ℂ)
  posSemidef := by
    simpa [← Matrix.star_eq_conjTranspose] using
      ρ.posSemidef.mul_mul_conjTranspose_same (U : Matrix d d ℂ)
  trace_one := by
    rw [Matrix.trace_mul_cycle, show star (U : Matrix d d ℂ) * (U : Matrix d d ℂ) = 1 from
      Unitary.coe_star_mul_self U, Matrix.one_mul, ρ.trace_one]

end DensityOp

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Von Neumann entropy `S(ρ) := -Tr(ρ log₂ ρ)` in bits. -/
noncomputable def vonNeumannEntropy (ρ : DensityOp d) : ℝ :=
  (∑ i : d, Real.negMulLog (ρ.eigvals i)) / Real.log 2

/-- Quantum Jensen–Shannon divergence `QJS(ρ, σ) := S((ρ + σ)/2) - (S(ρ) + S(σ))/2`. -/
noncomputable def qjs (ρ σ : DensityOp d) : ℝ :=
  vonNeumannEntropy (DensityOp.midpoint ρ σ) -
    (vonNeumannEntropy ρ + vonNeumannEntropy σ) / 2

lemma posSemidef_sqrt_mul_sqrt (ρ σ : DensityOp d) :
    (ρ.sqrtMat * σ.mat * ρ.sqrtMat).PosSemidef := by
  simpa [ρ.sqrtMat_isHermitian.eq] using σ.posSemidef.mul_mul_conjTranspose_same ρ.sqrtMat

/-- Uhlmann root fidelity `F(ρ, σ) := Tr √(√ρ σ √ρ)`. -/
noncomputable def rootFidelity (ρ σ : DensityOp d) : ℝ :=
  ∑ i : d, Real.sqrt ((posSemidef_sqrt_mul_sqrt ρ σ).isHermitian.eigenvalues i)

/-! ### Qubit Dephasing Channel -/

/-- The Pauli-`Z` unitary `Z ⊗ I` on `ℂ² ⊗ ℂ^d`. -/
def pauliZTensorI (d : Type*) [Fintype d] [DecidableEq d] :
    Matrix.unitaryGroup (Bool × d) ℂ :=
  ⟨Matrix.diagonal (fun p : Bool × d ↦ if p.1 = false then (1 : ℂ) else -1), by
    rw [Matrix.mem_unitaryGroup_iff]
    ext p q
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hpq : p = q
    · subst hpq
      simp only [↓reduceIte, Finset.sum_ite_eq', Finset.mem_univ]
      cases p.1 <;> simp
    · simp only [hpq, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro r _
      by_cases h1 : p = r
      · subst h1; simp [Ne.symm hpq]
      · simp [h1]⟩

/-- Qubit dephasing channel `(Z_p ⊗ id)(Ψ) = (1 - p) Ψ + p (Z ⊗ I) Ψ (Z ⊗ I)`. -/
noncomputable def dephaseState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) : DensityOp (Bool × d) :=
  DensityOp.mix p hp0 hp1 Ψ (DensityOp.conjUnitary (pauliZTensorI d) Ψ)

/-- Relative-entropy coherence `C(p) := S((Z_{1/2} ⊗ id)(Ψ)) - S((Z_p ⊗ id)(Ψ))`. -/
noncomputable def dephaseCoherence (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) : ℝ :=
  vonNeumannEntropy (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) -
    vonNeumannEntropy (dephaseState p hp0 hp1 Ψ)

/-- Equatorial single-qubit state `½ (I + x X)` on `Bool × Unit` for `x ∈ [0, 1]`. -/
noncomputable def equatorialState (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    DensityOp (Bool × Unit) where
  mat := Matrix.of fun p q ↦ if p.1 = q.1 then ((1 / 2 : ℝ) : ℂ) else ((x / 2 : ℝ) : ℂ)
  posSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · ext ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩; cases a <;> cases b <;> simp
    · intro v
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
        Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
      set a := v (false, ())
      set b := v (true, ())
      have hre_id : (star b * (↑(1 / 2 : ℝ) * b + ↑(x / 2 : ℝ) * a) +
          star a * (↑(x / 2 : ℝ) * b + ↑(1 / 2 : ℝ) * a)) =
          (((1 - x) / 2 : ℝ) : ℂ) * (star a * a + star b * b) +
          ((x / 2 : ℝ) : ℂ) * (star (a + b) * (a + b)) := by
        simp only [star_add]; push_cast; ring
      have hnn1 : (0 : ℂ) ≤ (((1 - x) / 2 : ℝ) : ℂ) * (star a * a + star b * b) := by
        have h1 : (0 : ℂ) ≤ (((1 - x) / 2 : ℝ) : ℂ) := by
          exact_mod_cast (by linarith : (0 : ℝ) ≤ (1 - x) / 2)
        have h2 : (0 : ℂ) ≤ star a * a := by
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          exact_mod_cast sq_nonneg ‖a‖
        have h3 : (0 : ℂ) ≤ star b * b := by
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          exact_mod_cast sq_nonneg ‖b‖
        exact mul_nonneg h1 (add_nonneg h2 h3)
      have hnn2 : (0 : ℂ) ≤ ((x / 2 : ℝ) : ℂ) * (star (a + b) * (a + b)) := by
        have h1 : (0 : ℂ) ≤ ((x / 2 : ℝ) : ℂ) := by
          exact_mod_cast (by linarith : (0 : ℝ) ≤ x / 2)
        have h2 : (0 : ℂ) ≤ star (a + b) * (a + b) := by
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          exact_mod_cast sq_nonneg ‖a + b‖
        exact mul_nonneg h1 h2
      simpa only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, a, b] using
        (by rw [hre_id]; exact add_nonneg hnn1 hnn2)
  trace_one := by
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type,
      Fintype.sum_unique, Fintype.sum_bool, ↓reduceIte]
    push_cast; ring

/-! ### Binary-Input C-Q Channels and Arıkan Polar Tree -/

/-- A binary-input classical–quantum channel `W : Bool → DensityOp d`. -/
structure CQChannel (d : Type*) [Fintype d] [DecidableEq d] where
  out : Bool → DensityOp d

namespace CQChannel

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-- Conditional entropy `H(W) := 1 - QJS(ρ₀, ρ₁)`. -/
noncomputable def condEntropy (W : CQChannel d) : ℝ :=
  1 - qjs (W.out false) (W.out true)

/-- Symmetric Holevo capacity `I(W) := QJS(ρ₀, ρ₁)`. -/
noncomputable def symCapacity (W : CQChannel d) : ℝ :=
  qjs (W.out false) (W.out true)

/-- Fidelity (quantum Bhattacharyya) parameter `F(W) := F(ρ₀, ρ₁)`. -/
noncomputable def fidelityParam (W : CQChannel d) : ℝ :=
  rootFidelity (W.out false) (W.out true)

/-- Polarization potential `T(W) := √(H(W)(1 - H(W)))`. -/
noncomputable def potential (W : CQChannel d) : ℝ :=
  Real.sqrt (W.condEntropy * (1 - W.condEntropy))

/-- Classical register projection `|b⟩⟨b|` on `Bool`. -/
def ketBraBool (b : Bool) : DensityOp Bool where
  mat := Matrix.of (fun i j ↦ if i = b ∧ j = b then (1 : ℂ) else 0)
  posSemidef := by
    have hM : Matrix.of (fun i j ↦ if i = b ∧ j = b then (1 : ℂ) else 0) =
        (Matrix.of (fun i j ↦ if i = b ∧ j = b then (1 : ℂ) else 0))ᴴ *
          Matrix.of (fun i j ↦ if i = b ∧ j = b then (1 : ℂ) else 0) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
      rw [Fintype.sum_bool]
      cases b <;> cases i <;> cases j <;> simp
    rw [hM]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  trace_one := by
    cases b <;> simp [Matrix.trace, Matrix.diag]

/-- Check-node (minus) combination `W₁ ⊠ W₂`. -/
noncomputable def checkCombine (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    CQChannel (d₁ × d₂) where
  out u₁ := DensityOp.midpoint
    (DensityOp.tensor (W₁.out u₁) (W₂.out false))
    (DensityOp.tensor (W₁.out (!u₁)) (W₂.out true))

/-- Variable-node (plus) combination `W₁ ⊛ W₂`. -/
noncomputable def varCombine (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    CQChannel (Bool × (d₁ × d₂)) where
  out u₂ := DensityOp.midpoint
    (DensityOp.tensor (ketBraBool false) (DensityOp.tensor (W₁.out u₂) (W₂.out u₂)))
    (DensityOp.tensor (ketBraBool true) (DensityOp.tensor (W₁.out (!u₂)) (W₂.out u₂)))

/-- Check-node polarization `W⁻ := W ⊠ W`. -/
noncomputable def minusChannel (W : CQChannel d) : CQChannel (d × d) :=
  checkCombine W W

/-- Variable-node polarization `W⁺ := W ⊛ W`. -/
noncomputable def plusChannel (W : CQChannel d) : CQChannel (Bool × (d × d)) :=
  varCombine W W

end CQChannel

/-- Bundled finite-dimensional binary-input c-q channel for recursive polar-tree construction. -/
structure BundledCQChannel where
  dim : Type
  fintype : Fintype dim
  decEq : DecidableEq dim
  ch : CQChannel dim

attribute [instance] BundledCQChannel.fintype BundledCQChannel.decEq

/-- Recursive construction of Arıkan's depth-`t` synthetic channel `W^{(b)}`. -/
noncomputable def polarChannelTree {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) : (t : ℕ) → (Fin t → Bool) → BundledCQChannel
  | 0, _ => ⟨d, inferInstance, inferInstance, W⟩
  | t + 1, b =>
      if b (Fin.last t) = false then
        let S := polarChannelTree W t (Fin.init b)
        ⟨S.dim × S.dim, inferInstance, inferInstance, S.ch.minusChannel⟩
      else
        let S := polarChannelTree W t (Fin.init b)
        ⟨Bool × (S.dim × S.dim), inferInstance, inferInstance, S.ch.plusChannel⟩

/-- Fidelity parameter `F(W^{(b)})` of the depth-`t` synthetic channel along `b`. -/
noncomputable def polarFidelity {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (t : ℕ) (b : Fin t → Bool) : ℝ :=
  (polarChannelTree W t b).ch.fidelityParam

/-- Uniform probability of an event `P` on `Fin n → Bool`. -/
noncomputable def treeProb (n : ℕ) (P : (Fin n → Bool) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (2 : ℝ) ^ n

end PolarCodesChallenge
