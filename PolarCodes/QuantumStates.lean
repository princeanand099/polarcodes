/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Matrix.Kronecker
import PolarCodes.BinaryEntropy

/-!
# Finite-Dimensional Quantum States, Entropies, Divergences, and Distinguishability Measures

This module formalizes Section 2.1 of the manuscript on finite-dimensional complex Hilbert spaces
modeled via `Matrix d d ℂ` for `[Fintype d] [DecidableEq d]`:
- Density operators `DensityOp d` (`ρ ⪰ 0`, `Tr ρ = 1`)
- Von Neumann entropy `vonNeumannEntropy` (`S(ρ) = -Tr(ρ log₂ ρ)`)
- Umegaki quantum relative entropy `relEntropy` (`D(ρ ‖ σ) ∈ [0, ∞]`)
- Quantum Jensen–Shannon divergence `qjs` (`QJS(ρ, σ)`)
- Quantum hockey-stick divergence `hockeyStick` (`E_γ(ρ ‖ σ)`) and trace distance `traceDist`
- Uhlmann root fidelity `rootFidelity` (`F(ρ, σ) = Tr √(√ρ σ √ρ)`)
-/

open Matrix BigOperators Real

namespace PolarCodes

/-- A density operator (quantum state) on a finite-dimensional Hilbert space `ℂ^d`:
a positive semidefinite `d × d` complex matrix with trace `1`. -/
structure DensityOp (d : Type*) [Fintype d] [DecidableEq d] where
  mat : Matrix d d ℂ
  posSemidef : mat.PosSemidef
  trace_one : mat.trace = 1

namespace DensityOp

variable {d : Type*} [Fintype d] [DecidableEq d]

lemma isHermitian (ρ : DensityOp d) : ρ.mat.IsHermitian :=
  ρ.posSemidef.isHermitian

/-- Eigenvalues of a density operator `ρ` (all real and nonnegative). -/
noncomputable def eigvals (ρ : DensityOp d) : d → ℝ :=
  ρ.isHermitian.eigenvalues

/-- Eigenvector unitary matrix of `ρ`. -/
noncomputable def eigUnitary (ρ : DensityOp d) : Matrix.unitaryGroup d ℂ :=
  ρ.isHermitian.eigenvectorUnitary

lemma eigvals_nonneg (ρ : DensityOp d) (i : d) : 0 ≤ ρ.eigvals i :=
  ρ.posSemidef.eigenvalues_nonneg i

/-- Positive semidefinite square root `√ρ` constructed via spectral decomposition. -/
noncomputable def sqrtMat (ρ : DensityOp d) : Matrix d d ℂ :=
  (ρ.eigUnitary : Matrix d d ℂ) *
    Matrix.diagonal (fun i ↦ (Real.sqrt (ρ.eigvals i) : ℂ)) *
    star (ρ.eigUnitary : Matrix d d ℂ)

/-- Convex mixture `(1 - p) ρ + p σ` of two density operators for `p ∈ [0, 1]`. -/
noncomputable def mix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ σ : DensityOp d) : DensityOp d where
  mat := ((1 - p : ℝ) : ℂ) • ρ.mat + (p : ℂ) • σ.mat
  posSemidef := by
    have h1 : (((1 - p : ℝ) : ℂ) • ρ.mat).PosSemidef := by
      simpa [Complex.real_smul] using ρ.posSemidef.smul (by linarith : (0 : ℝ) ≤ 1 - p)
    have h2 : ((p : ℂ) • σ.mat).PosSemidef := by
      simpa [Complex.real_smul] using σ.posSemidef.smul hp0
    exact h1.add h2
  trace_one := by
    simp [Matrix.trace_add, Matrix.trace_smul, ρ.trace_one, σ.trace_one]

/-- Uniform midpoint `(ρ + σ) / 2` of two density operators. -/
noncomputable def midpoint (ρ σ : DensityOp d) : DensityOp d :=
  mix (1 / 2) (by norm_num) (by norm_num) ρ σ

/-- Tensor product `ρ ⊗ σ` of density operators on `d₁ × d₂`. -/
noncomputable def tensor {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (ρ : DensityOp d₁) (σ : DensityOp d₂) :
    DensityOp (d₁ × d₂) where
  mat := Matrix.kroneckerMap (· * ·) ρ.mat σ.mat
  posSemidef := ρ.posSemidef.kronecker σ.posSemidef
  trace_one := by
    rw [Matrix.trace_kronecker, ρ.trace_one, σ.trace_one, mul_one]

/-- Unitary conjugation `U ρ U†` of a density operator. -/
noncomputable def conjUnitary (U : Matrix.unitaryGroup d ℂ) (ρ : DensityOp d) : DensityOp d where
  mat := (U : Matrix d d ℂ) * ρ.mat * star (U : Matrix d d ℂ)
  posSemidef := by
    simpa [Matrix.conjTranspose_eq_star] using ρ.posSemidef.mul_mul_conjTranspose_same (U : Matrix d d ℂ)
  trace_one := by
    rw [Matrix.trace_mul_cycle, show star (U : Matrix d d ℂ) * (U : Matrix d d ℂ) = 1 from
      Unitary.coe_star_mul_self U, Matrix.one_mul, ρ.trace_one]

end DensityOp

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Von Neumann entropy `S(ρ) := -Tr(ρ log₂ ρ)` in bits, with `0 log₂ 0 = 0`. -/
noncomputable def vonNeumannEntropy (ρ : DensityOp d) : ℝ :=
  (∑ i : d, Real.negMulLog (ρ.eigvals i)) / Real.log 2

/-- Support inclusion condition `supp(ρ) ⊆ supp(σ)`:
every eigenvector of `ρ` with nonzero eigenvalue is orthogonal to the kernel of `σ`. -/
def suppSubset (ρ σ : DensityOp d) : Prop :=
  ∀ i j : d, ρ.eigvals i ≠ 0 → σ.eigvals j = 0 →
    (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i = 0

/-- Umegaki quantum relative entropy `D(ρ ‖ σ) ∈ [0, ∞]` in bits. -/
noncomputable def relEntropy (ρ σ : DensityOp d) : ENNReal :=
  if suppSubset ρ σ then
    ENNReal.ofReal
      ((∑ i : d, ∑ j : d,
        ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j)))) / Real.log 2)
  else
    ⊤

/-- Quantum Jensen–Shannon divergence `QJS(ρ, σ) := S((ρ + σ)/2) - (S(ρ) + S(σ))/2` (Eq. 2.1). -/
noncomputable def qjs (ρ σ : DensityOp d) : ℝ :=
  vonNeumannEntropy (DensityOp.midpoint ρ σ) -
    (vonNeumannEntropy ρ + vonNeumannEntropy σ) / 2

/-- Helper: `ρ - γ σ` is Hermitian for real `γ`. -/
lemma isHermitian_sub_smul (γ : ℝ) (ρ σ : DensityOp d) :
    (ρ.mat - (γ : ℂ) • σ.mat).IsHermitian := by
  have h1 := ρ.isHermitian
  have h2 : ((γ : ℂ) • σ.mat).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      σ.isHermitian.eq]
  exact h1.sub h2

/-- Quantum hockey-stick divergence of order `γ ≥ 0`: `E_γ(ρ ‖ σ) := Tr[(ρ - γσ)_+]` (Eq. 2.2). -/
noncomputable def hockeyStick (γ : ℝ) (ρ σ : DensityOp d) : ℝ :=
  ∑ i : d, max ((isHermitian_sub_smul γ ρ σ).eigenvalues i) 0

/-- Trace distance `T_tr(ρ, σ) := E_1(ρ ‖ σ) = ½ ‖ρ - σ‖₁`. -/
noncomputable def traceDist (ρ σ : DensityOp d) : ℝ :=
  hockeyStick 1 ρ σ

/-- Helper: `√ρ σ √ρ` is positive semidefinite. -/
lemma posSemidef_sqrt_mul_sqrt (ρ σ : DensityOp d) :
    (ρ.sqrtMat * σ.mat * ρ.sqrtMat).PosSemidef := by
  have hsqrtH : ρ.sqrtMat.IsHermitian := by
    unfold DensityOp.sqrtMat
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_eq_star, star_star, Matrix.diagonal_conjTranspose]
    have hdiag : (fun i ↦ star ((Real.sqrt (ρ.eigvals i) : ℂ))) =
        fun i ↦ (Real.sqrt (ρ.eigvals i) : ℂ) := by
      ext i; simp
    simp [hdiag, Matrix.mul_assoc]
  simpa [hsqrtH.eq] using σ.posSemidef.mul_mul_conjTranspose_same ρ.sqrtMat

/-- Uhlmann root fidelity `F(ρ, σ) := Tr √(√ρ σ √ρ)`. -/
noncomputable def rootFidelity (ρ σ : DensityOp d) : ℝ :=
  ∑ i : d, Real.sqrt ((posSemidef_sqrt_mul_sqrt ρ σ).isHermitian.eigenvalues i)

end PolarCodes
