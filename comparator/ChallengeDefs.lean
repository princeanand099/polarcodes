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
import Mathlib.Basic.ENNReal.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Kronecker

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodesChallenge

noncomputable def h2 (p : ℝ) : ℝ :=
  -p * Real.logb 2 p - (1 - p) * Real.logb 2 (1 - p)

noncomputable def h2Inv (u : ℝ) : ℝ :=
  sSup {p ∈ Set.Icc (0 : ℝ) (1 / 2) | h2 p ≤ u}

def binConv (a b : ℝ) : ℝ :=
  a * (1 - b) + (1 - a) * b

noncomputable def gc (u v : ℝ) : ℝ :=
  h2 (binConv (h2Inv u) (h2Inv v))

noncomputable def gq (u v : ℝ) : ℝ :=
  min (gc u v) (u + v - 1 + gc (1 - u) (1 - v))

noncomputable def deltaGap (u p : ℝ) : ℝ :=
  h2 (binConv (h2Inv u) p) - h2 p

noncomputable def theta0 : ℝ :=
  (32 / 3) * h2Inv (1 / 4) * (1 - h2 (1 - (2 : ℝ) ^ (-(1 : ℝ) / 2)))

noncomputable def Lambda0 : ℝ :=
  Real.sqrt (1 - theta0 ^ 2 / 4)

structure DensityOp (d : Type*) [Fintype d] [DecidableEq d] where
  mat : Matrix d d ℂ
  posSemidef : mat.PosSemidef
  trace_one : mat.trace = 1

namespace DensityOp

variable {d : Type*} [Fintype d] [DecidableEq d]

lemma isHermitian (ρ : DensityOp d) : ρ.mat.IsHermitian :=
  ρ.posSemidef.isHermitian

noncomputable def eigvals (ρ : DensityOp d) : d → ℝ :=
  ρ.isHermitian.eigenvalues

noncomputable def eigUnitary (ρ : DensityOp d) : Matrix.unitaryGroup d ℂ :=
  ρ.isHermitian.eigenvectorUnitary

lemma eigvals_nonneg (ρ : DensityOp d) (i : d) : 0 ≤ ρ.eigvals i :=
  ρ.posSemidef.eigenvalues_nonneg i

noncomputable def sqrtMat (ρ : DensityOp d) : Matrix d d ℂ :=
  (ρ.eigUnitary : Matrix d d ℂ) *
    Matrix.diagonal (fun i ↦ (Real.sqrt (ρ.eigvals i) : ℂ)) *
    star (ρ.eigUnitary : Matrix d d ℂ)

lemma sqrtMat_isHermitian (ρ : DensityOp d) : ρ.sqrtMat.IsHermitian := by
  unfold sqrtMat
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    ← Matrix.star_eq_conjTranspose, star_star, Matrix.diagonal_conjTranspose,
    ← Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  congr 2
  ext i j
  simp [Matrix.diagonal_apply]

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

noncomputable def mix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ σ : DensityOp d) : DensityOp d where
  mat := ((1 - p : ℝ) : ℂ) • ρ.mat + (p : ℂ) • σ.mat
  posSemidef := by
    have h1 : (((1 - p : ℝ) : ℂ) • ρ.mat).PosSemidef := by
      have : (((1 - p : ℝ) : ℂ) • ρ.mat) = (1 - p : ℝ) • ρ.mat := by
        ext i j; simp [Complex.real_smul]
      rw [this]; exact ρ.posSemidef.smul (by linarith)
    have h2 : ((p : ℂ) • σ.mat).PosSemidef := by
      have : ((p : ℂ) • σ.mat) = p • σ.mat := by
        ext i j; simp [Complex.real_smul]
      rw [this]; exact σ.posSemidef.smul hp0
    exact h1.add h2
  trace_one := by
    simp [Matrix.trace_add, Matrix.trace_smul, ρ.trace_one, σ.trace_one]

noncomputable def midpoint (ρ σ : DensityOp d) : DensityOp d :=
  mix (1 / 2) (by norm_num) (by norm_num) ρ σ

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

noncomputable def vonNeumannEntropy (ρ : DensityOp d) : ℝ :=
  (∑ i : d, Real.negMulLog (ρ.eigvals i)) / Real.log 2

def suppSubset (ρ σ : DensityOp d) : Prop :=
  ∀ i j : d, ρ.eigvals i ≠ 0 → σ.eigvals j = 0 →
    (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i = 0

open Classical in
noncomputable def relEntropy (ρ σ : DensityOp d) : ENNReal :=
  if suppSubset ρ σ then
    ENNReal.ofReal
      ((∑ i : d, ∑ j : d,
        ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
          (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j)))) / Real.log 2)
  else
    ⊤

noncomputable def qjs (ρ σ : DensityOp d) : ℝ :=
  vonNeumannEntropy (DensityOp.midpoint ρ σ) -
    (vonNeumannEntropy ρ + vonNeumannEntropy σ) / 2

lemma posSemidef_sqrt_mul_sqrt (ρ σ : DensityOp d) :
    (ρ.sqrtMat * σ.mat * ρ.sqrtMat).PosSemidef := by
  simpa [ρ.sqrtMat_isHermitian.eq] using σ.posSemidef.mul_mul_conjTranspose_same ρ.sqrtMat

noncomputable def rootFidelity (ρ σ : DensityOp d) : ℝ :=
  ∑ i : d, Real.sqrt ((posSemidef_sqrt_mul_sqrt ρ σ).isHermitian.eigenvalues i)

noncomputable def hockeyStick (γ : ℝ) (ρ σ : DensityOp d) : ℝ :=
  ∑ i : d, max ((ρ.isHermitian.sub (by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      σ.isHermitian.eq] : ((γ : ℂ) • σ.mat).IsHermitian)).eigenvalues i) 0

noncomputable def traceDist (ρ σ : DensityOp d) : ℝ :=
  hockeyStick 1 ρ σ

def pureState (φ : d → ℂ) (hφ : ∑ i : d, ‖φ i‖ ^ 2 = 1) : DensityOp d where
  mat := Matrix.of (fun i j ↦ φ i * star (φ j))
  posSemidef := by
    let M : Matrix d Unit ℂ := Matrix.of (fun i _ ↦ φ i)
    have hM : Matrix.of (fun i j ↦ φ i * star (φ j)) = M * Mᴴ := by
      ext i j; simp [M, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hM]
    simpa [Matrix.conjTranspose_conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self Mᴴ
  trace_one := by
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
    have hnorm : ∀ i : d, φ i * star (φ i) = ((‖φ i‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [hnorm, ← Complex.ofReal_sum, hφ, Complex.ofReal_one]

noncomputable def maxMixedState (d : Type*) [Fintype d] [DecidableEq d] [Nonempty d] :
    DensityOp d where
  mat := ((Fintype.card d : ℝ)⁻¹ : ℂ) • (1 : Matrix d d ℂ)
  posSemidef := by
    have hnn : (0 : ℝ) ≤ (Fintype.card d : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg _)
    have hEq : (((Fintype.card d : ℝ)⁻¹ : ℂ) • (1 : Matrix d d ℂ)) =
        ((Fintype.card d : ℝ)⁻¹ : ℝ) • (1 : Matrix d d ℂ) := by
      ext i j; simp [Complex.real_smul]
    rw [hEq]
    exact (Matrix.PosSemidef.one (n := d) (R := ℂ)).smul hnn
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Complex.ofReal_natCast]
    have hpos : (Fintype.card d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact inv_mul_cancel₀ hpos

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
      · subst h1; simp [hpq, Ne.symm hpq]
      · simp [h1]⟩

noncomputable def dephaseState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) : DensityOp (Bool × d) :=
  DensityOp.mix p hp0 hp1 Ψ (DensityOp.conjUnitary (pauliZTensorI d) Ψ)

noncomputable def dephaseCoherence (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) : ℝ :=
  vonNeumannEntropy (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) -
    vonNeumannEntropy (dephaseState p hp0 hp1 Ψ)

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

structure CQChannel (d : Type*) [Fintype d] [DecidableEq d] where
  out : Bool → DensityOp d

namespace CQChannel

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

noncomputable def condEntropy (W : CQChannel d) : ℝ :=
  1 - qjs (W.out false) (W.out true)

noncomputable def symCapacity (W : CQChannel d) : ℝ :=
  qjs (W.out false) (W.out true)

noncomputable def fidelityParam (W : CQChannel d) : ℝ :=
  rootFidelity (W.out false) (W.out true)

noncomputable def potential (W : CQChannel d) : ℝ :=
  Real.sqrt (W.condEntropy * (1 - W.condEntropy))

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

noncomputable def checkCombine (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    CQChannel (d₁ × d₂) where
  out u₁ := DensityOp.midpoint
    (DensityOp.tensor (W₁.out u₁) (W₂.out false))
    (DensityOp.tensor (W₁.out (!u₁)) (W₂.out true))

noncomputable def varCombine (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    CQChannel (Bool × (d₁ × d₂)) where
  out u₂ := DensityOp.midpoint
    (DensityOp.tensor (ketBraBool false) (DensityOp.tensor (W₁.out u₂) (W₂.out u₂)))
    (DensityOp.tensor (ketBraBool true) (DensityOp.tensor (W₁.out (!u₂)) (W₂.out u₂)))

noncomputable def minusChannel (W : CQChannel d) : CQChannel (d × d) :=
  checkCombine W W

noncomputable def plusChannel (W : CQChannel d) : CQChannel (Bool × (d × d)) :=
  varCombine W W

def IsPureState (W : CQChannel d) : Prop :=
  ∃ φ₀ φ₁ : d → ℂ,
    (∑ i, ‖φ₀ i‖ ^ 2 = 1) ∧ (∑ i, ‖φ₁ i‖ ^ 2 = 1) ∧
    (W.out false).mat = Matrix.of (fun i j ↦ φ₀ i * star (φ₀ j)) ∧
    (W.out true).mat = Matrix.of (fun i j ↦ φ₁ i * star (φ₁ j))

def IsClassical (W : CQChannel d) : Prop :=
  (W.out false).mat * (W.out true).mat = (W.out true).mat * (W.out false).mat

end CQChannel

noncomputable def gramFactor (ρ₀ ρ₁ : DensityOp d) : Matrix (Bool × d) d ℂ :=
  Matrix.of fun p k ↦
    ((Real.sqrt 2)⁻¹ : ℂ) * (if p.1 = false then ρ₀.sqrtMat p.2 k else ρ₁.sqrtMat p.2 k)

noncomputable def gramState (ρ₀ ρ₁ : DensityOp d) : DensityOp (Bool × d) where
  mat := gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ
  posSemidef := by
    simpa [Matrix.conjTranspose_conjTranspose] using
      Matrix.posSemidef_conjTranspose_mul_self (gramFactor ρ₀ ρ₁)ᴴ
  trace_one := by
    rw [Matrix.trace_mul_comm]
    have hprod : (gramFactor ρ₀ ρ₁)ᴴ * gramFactor ρ₀ ρ₁ = (DensityOp.midpoint ρ₀ ρ₁).mat := by
      ext i j
      simp only [gramFactor, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
        DensityOp.midpoint, DensityOp.mix, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
      have h0 : ∑ k : d, star (ρ₀.sqrtMat k i) * ρ₀.sqrtMat k j = ρ₀.mat i j := by
        have h := congr_fun (congr_fun ρ₀.sqrtMat_mul_self i) j
        rw [← h, Matrix.mul_apply]
        apply Finset.sum_congr rfl; intro k _
        have hh := congr_fun (congr_fun ρ₀.sqrtMat_isHermitian.eq i) k
        simp only [Matrix.conjTranspose_apply] at hh; rw [hh]
      have h1 : ∑ k : d, star (ρ₁.sqrtMat k i) * ρ₁.sqrtMat k j = ρ₁.mat i j := by
        have h := congr_fun (congr_fun ρ₁.sqrtMat_mul_self i) j
        rw [← h, Matrix.mul_apply]
        apply Finset.sum_congr rfl; intro k _
        have hh := congr_fun (congr_fun ρ₁.sqrtMat_isHermitian.eq i) k
        simp only [Matrix.conjTranspose_apply] at hh; rw [hh]
      have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
        rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
          ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        push_cast; ring
      have hsum0 : ∑ k : d, star (((Real.sqrt 2 : ℂ)⁻¹) * ρ₀.sqrtMat k i) *
          (((Real.sqrt 2 : ℂ)⁻¹) * ρ₀.sqrtMat k j) = (1 / 2 : ℂ) * ρ₀.mat i j := by
        rw [← h0, Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
        rw [star_mul', ← hsq2]; ring
      have hsum1 : ∑ k : d, star (((Real.sqrt 2 : ℂ)⁻¹) * ρ₁.sqrtMat k i) *
          (((Real.sqrt 2 : ℂ)⁻¹) * ρ₁.sqrtMat k j) = (1 / 2 : ℂ) * ρ₁.mat i j := by
        rw [← h1, Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
        rw [star_mul', ← hsq2]; ring
      rw [hsum0, hsum1]; push_cast; ring
    rw [hprod, (DensityOp.midpoint ρ₀ ρ₁).trace_one]

noncomputable def CQChannel.dual (W : CQChannel d) : CQChannel (Bool × d) where
  out
    | false => gramState (W.out false) (W.out true)
    | true => DensityOp.conjUnitary (pauliZTensorI d) (gramState (W.out false) (W.out true))

structure BundledCQChannel where
  dim : Type
  fintype : Fintype dim
  decEq : DecidableEq dim
  ch : CQChannel dim

attribute [instance] BundledCQChannel.fintype BundledCQChannel.decEq

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

noncomputable def polarFidelity {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (t : ℕ) (b : Fin t → Bool) : ℝ :=
  (polarChannelTree W t b).ch.fidelityParam

noncomputable def treeProb (n : ℕ) (P : (Fin n → Bool) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (2 : ℝ) ^ n

noncomputable def productStateMat {d : Type*} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (x : Fin (2 ^ n) → Bool) :
    Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ :=
  Matrix.of fun r s ↦ ∏ k : Fin (2 ^ n), (W.out (x k)).mat (r k) (s k)

def arikanEven (n : ℕ) (u : Fin (2 ^ (n + 1)) → Bool) : Fin (2 ^ n) → Bool :=
  fun j ↦ xor (u ⟨2 * j.val, by omega⟩) (u ⟨2 * j.val + 1, by omega⟩)

def arikanOdd (n : ℕ) (u : Fin (2 ^ (n + 1)) → Bool) : Fin (2 ^ n) → Bool :=
  fun j ↦ u ⟨2 * j.val + 1, by omega⟩

def arikanTransform : (n : ℕ) → (Fin (2 ^ n) → Bool) → (Fin (2 ^ n) → Bool)
  | 0, u => u
  | n + 1, u => fun k ↦
      if hk : k.val < 2 ^ n then
        arikanTransform n (arikanEven n u) ⟨k.val, hk⟩
      else
        arikanTransform n (arikanOdd n u) ⟨k.val - 2 ^ n, by omega⟩

lemma arikanTransform_injective : ∀ (n : ℕ), Function.Injective (arikanTransform n)
  | 0, u₁, u₂, h => h
  | n + 1, u₁, u₂, h => by
      have hev : arikanTransform n (arikanEven n u₁) = arikanTransform n (arikanEven n u₂) := by
        funext k
        have hk := congr_fun h ⟨k.val, by omega⟩
        simpa [arikanTransform, k.isLt] using hk
      have hodd : arikanTransform n (arikanOdd n u₁) = arikanTransform n (arikanOdd n u₂) := by
        funext k
        have hk := congr_fun h ⟨k.val + 2 ^ n, by omega⟩
        have hnot : ¬ (k.val + 2 ^ n < 2 ^ n) := by omega
        have hsub : (⟨k.val + 2 ^ n - 2 ^ n, by omega⟩ : Fin (2 ^ n)) = k := Fin.ext (by dsimp; omega)
        simpa [arikanTransform, hnot, hsub] using hk
      have h1 := arikanTransform_injective n hev
      have h2 := arikanTransform_injective n hodd
      funext i
      by_cases hp : i.val % 2 = 0
      · have he1 := congr_fun h1 ⟨i.val / 2, by omega⟩
        have ho1 := congr_fun h2 ⟨i.val / 2, by omega⟩
        simp only [arikanEven, arikanOdd] at he1 ho1
        have hidx : (⟨2 * (i.val / 2), by omega⟩ : Fin (2 ^ (n + 1))) = i := Fin.ext (by dsimp; omega)
        rw [hidx, ho1] at he1
        have hxor : ∀ a b c : Bool, xor a c = xor b c → a = b := by decide
        exact hxor _ _ _ he1
      · have ho1 := congr_fun h2 ⟨i.val / 2, by omega⟩
        simp only [arikanOdd] at ho1
        have hidx : (⟨2 * (i.val / 2) + 1, by omega⟩ : Fin (2 ^ (n + 1))) = i := Fin.ext (by dsimp; omega)
        rwa [hidx] at ho1

lemma arikanTransform_bijective (n : ℕ) : Function.Bijective (arikanTransform n) :=
  (Finite.injective_iff_bijective).mp (arikanTransform_injective n)

def embedMsg {N : ℕ} (infoSet : Finset (Fin N)) (frozen : Fin N → Bool)
    (m : {i : Fin N // i ∈ infoSet} → Bool) : Fin N → Bool :=
  fun i ↦ if hi : i ∈ infoSet then m ⟨i, hi⟩ else frozen i

def prefixOf {N : ℕ} (i : Fin N) (u : Fin N → Bool) : Fin i.val → Bool :=
  fun j ↦ u ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

noncomputable def synthBlockMat {d : Type*} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n))
    (p : Fin i.val → Bool) (b : Bool) :
    Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ prefixOf i u = p ∧ u i = b),
    productStateMat W n (arikanTransform n u)

noncomputable def condSynthStateMat {d : Type*} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n))
    (p : Fin i.val → Bool) (b : Bool) :
    Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ :=
  ((2 : ℂ) ^ (2 ^ n - 1 - i.val))⁻¹ • synthBlockMat W n i p b

lemma productStateMat_isHermitian {d : Type*} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (x : Fin (2 ^ n) → Bool) :
    (productStateMat W n x).IsHermitian := by
  ext r s
  simp only [Matrix.conjTranspose_apply, productStateMat, Matrix.of_apply, Complex.star_def,
    map_prod]
  apply Finset.prod_congr rfl; intro k _
  have h := congr_fun (congr_fun (W.out (x k)).isHermitian.eq (r k)) (s k)
  simpa [Matrix.conjTranspose_apply, Complex.star_def] using h

lemma condSynthStateMat_isHermitian {d : Type*} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n))
    (p : Fin i.val → Bool) (b : Bool) :
    (condSynthStateMat W n i p b).IsHermitian := by
  unfold condSynthStateMat synthBlockMat
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  have hc : star (((2 : ℂ) ^ (2 ^ n - 1 - i.val))⁻¹) = ((2 : ℂ) ^ (2 ^ n - 1 - i.val))⁻¹ := by
    simp
  rw [hc]
  congr 1
  apply Finset.sum_congr rfl; intro u _
  exact (productStateMat_isHermitian W n (arikanTransform n u)).eq

noncomputable def helstromProjectorMat {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Matrix α α ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) : Matrix α α ℂ :=
  let hΔ := hA.sub hB
  let U : Matrix α α ℂ := (hΔ.eigenvectorUnitary : Matrix α α ℂ)
  U * Matrix.diagonal (fun i : α ↦ if 0 ≤ hΔ.eigenvalues i then (1 : ℂ) else 0) * star U

noncomputable def qscStepProj {d : Type*} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n))
    (p : Fin i.val → Bool) (b : Bool) :
    Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ :=
  let P := helstromProjectorMat
    (condSynthStateMat_isHermitian W n i p false)
    (condSynthStateMat_isHermitian W n i p true)
  if b = false then P else 1 - P

def seqProd {α : Type*} [Fintype α] [DecidableEq α] : List (Matrix α α ℂ) → Matrix α α ℂ
  | [] => 1
  | P :: Ps => seqProd Ps * P

noncomputable def qscProjListPrefix {d : Type*} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (infoSet : Finset (Fin (2 ^ n))) :
    (k : ℕ) → k ≤ 2 ^ n → (Fin (2 ^ n) → Bool) →
      List (Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ)
  | 0, _, _ => []
  | k + 1, hk, u =>
      let i : Fin (2 ^ n) := ⟨k, by omega⟩
      qscProjListPrefix W n infoSet k (by omega) u ++
        [if i ∈ infoSet then qscStepProj W n i (prefixOf i u) (u i) else 1]

noncomputable def qscPrefixKraus {d : Type*} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (infoSet : Finset (Fin (2 ^ n)))
    (k : ℕ) (hk : k ≤ 2 ^ n) (u : Fin (2 ^ n) → Bool) :
    Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ :=
  seqProd (qscProjListPrefix W n infoSet k hk u)

structure CosetPolarCode {d : Type*} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) where
  infoSet : Finset (Fin (2 ^ n))
  frozenBits : Fin (2 ^ n) → Bool
  povm : ({i : Fin (2 ^ n) // i ∈ infoSet} → Bool) →
    Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ
  povm_posSemidef : ∀ m, (povm m).PosSemidef
  povm_sum_one : ∑ m, povm m = 1

namespace CosetPolarCode

noncomputable def rate {d : Type*} [Fintype d] [DecidableEq d]
    {W : CQChannel d} {n : ℕ} (C : CosetPolarCode W n) : ℝ :=
  (C.infoSet.card : ℝ) / ((2 : ℝ) ^ n)

def encode {d : Type*} [Fintype d] [DecidableEq d]
    {W : CQChannel d} {n : ℕ} (C : CosetPolarCode W n)
    (m : {i : Fin (2 ^ n) // i ∈ C.infoSet} → Bool) : Fin (2 ^ n) → Bool :=
  arikanTransform n (embedMsg C.infoSet C.frozenBits m)

noncomputable def avgBlockError {d : Type*} [Fintype d] [DecidableEq d]
    {W : CQChannel d} {n : ℕ} (C : CosetPolarCode W n) : ℝ :=
  ((2 : ℝ) ^ C.infoSet.card)⁻¹ *
    ∑ m : {i : Fin (2 ^ n) // i ∈ C.infoSet} → Bool,
      (1 - ((C.povm m * productStateMat W n (C.encode m)).trace).re)

def IsQSCDecoder {d : Type*} [Fintype d] [DecidableEq d]
    {W : CQChannel d} {n : ℕ} (C : CosetPolarCode W n) : Prop :=
  ∀ m : {i : Fin (2 ^ n) // i ∈ C.infoSet} → Bool,
    C.povm m =
      (qscPrefixKraus W n C.infoSet (2 ^ n) le_rfl (embedMsg C.infoSet C.frozenBits m))ᴴ *
        qscPrefixKraus W n C.infoSet (2 ^ n) le_rfl (embedMsg C.infoSet C.frozenBits m)

end CosetPolarCode

def partialTrace₂Mat (d₁ d₂ : Type*) [Fintype d₂]
    (M : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) : Matrix d₁ d₁ ℂ :=
  Matrix.of fun i j ↦ ∑ k : d₂, M (i, k) (j, k)

lemma partialTrace₂Mat_posSemidef {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] {M : Matrix (d₁ × d₂) (d₁ × d₂) ℂ} (hM : M.PosSemidef) :
    (partialTrace₂Mat d₁ d₂ M).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hM ⊢
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, partialTrace₂Mat, Matrix.of_apply, star_sum]
    apply Finset.sum_congr rfl; intro k _
    have h := congr_fun (congr_fun hM.1 (i, k)) (j, k)
    simpa [Matrix.conjTranspose_apply] using h
  · intro v
    have hsum : star v ⬝ᵥ (partialTrace₂Mat d₁ d₂ M *ᵥ v) =
        ∑ k : d₂, star (fun p : d₁ × d₂ ↦ if p.2 = k then v p.1 else 0) ⬝ᵥ
          (M *ᵥ fun p : d₁ × d₂ ↦ if p.2 = k then v p.1 else 0) := by
      simp only [dotProduct, Matrix.mulVec, partialTrace₂Mat, Matrix.of_apply, Pi.star_apply,
        Fintype.sum_prod_type]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_eq_single k]
      · simp only [↓reduceIte, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_eq_single k]
        · simp
        · intro k' _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ k) h
      · intro k' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hsum]
    exact Finset.sum_nonneg fun k _ ↦ hM.2 _

structure CPTPMap (d₁ : Type) (d₂ : Type) [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] where
  env : Type
  fintypeEnv : Fintype env
  decEqEnv : DecidableEq env
  isom : Matrix (d₂ × env) d₁ ℂ
  isom_eq : isomᴴ * isom = 1

attribute [instance] CPTPMap.fintypeEnv CPTPMap.decEqEnv

namespace CPTPMap

variable {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

def apply (𝒩 : CPTPMap d₁ d₂) (ρ : DensityOp d₁) : DensityOp d₂ where
  mat := partialTrace₂Mat d₂ 𝒩.env (𝒩.isom * ρ.mat * 𝒩.isomᴴ)
  posSemidef := partialTrace₂Mat_posSemidef (ρ.posSemidef.mul_mul_conjTranspose_same 𝒩.isom)
  trace_one := by
    have htr : (partialTrace₂Mat d₂ 𝒩.env (𝒩.isom * ρ.mat * 𝒩.isomᴴ)).trace =
        (𝒩.isom * ρ.mat * 𝒩.isomᴴ).trace := by
      simp [Matrix.trace, Matrix.diag, partialTrace₂Mat, Fintype.sum_prod_type]
    rw [htr, Matrix.trace_mul_cycle, 𝒩.isom_eq, Matrix.one_mul, ρ.trace_one]

def complementary (𝒩 : CPTPMap d₁ d₂) : CPTPMap d₁ 𝒩.env where
  env := d₂
  fintypeEnv := inferInstance
  decEqEnv := inferInstance
  isom := Matrix.of fun p a ↦ 𝒩.isom (p.2, p.1) a
  isom_eq := by
    ext i j
    have h := congr_fun (congr_fun 𝒩.isom_eq i) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type] at h ⊢
    rw [Finset.sum_comm]; exact h

def IsDegradable (𝒩 : CPTPMap d₁ d₂) : Prop :=
  ∃ 𝒟 : CPTPMap d₂ 𝒩.env, ∀ ρ : DensityOp d₁,
    (𝒟.apply (𝒩.apply ρ)).mat = (𝒩.complementary.apply ρ).mat

def id (d : Type) [Fintype d] [DecidableEq d] : CPTPMap d d where
  env := Unit
  fintypeEnv := inferInstance
  decEqEnv := inferInstance
  isom := Matrix.of fun p a ↦ if p.1 = a then (1 : ℂ) else 0
  isom_eq := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fintype.sum_unique]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ i) h

def tensor {d₃ d₄ : Type} [Fintype d₃] [DecidableEq d₃] [Fintype d₄] [DecidableEq d₄]
    (𝒩₁ : CPTPMap d₁ d₂) (𝒩₂ : CPTPMap d₃ d₄) : CPTPMap (d₁ × d₃) (d₂ × d₄) where
  env := 𝒩₁.env × 𝒩₂.env
  fintypeEnv := @instFintypeProd _ _ 𝒩₁.fintypeEnv 𝒩₂.fintypeEnv
  decEqEnv := @instDecidableEqProd _ _ 𝒩₁.decEqEnv 𝒩₂.decEqEnv
  isom := Matrix.of fun p a ↦ 𝒩₁.isom (p.1.1, p.2.1) a.1 * 𝒩₂.isom (p.1.2, p.2.2) a.2
  isom_eq := by
    letI := 𝒩₁.fintypeEnv; letI := 𝒩₁.decEqEnv
    letI := 𝒩₂.fintypeEnv; letI := 𝒩₂.decEqEnv
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type]
    have hfac : ∑ b₁ : d₂, ∑ b₂ : d₄, ∑ e₁ : 𝒩₁.env, ∑ e₂ : 𝒩₂.env,
        star (𝒩₁.isom (b₁, e₁) i₁ * 𝒩₂.isom (b₂, e₂) i₂) *
          (𝒩₁.isom (b₁, e₁) j₁ * 𝒩₂.isom (b₂, e₂) j₂) =
        (∑ b₁ : d₂, ∑ e₁ : 𝒩₁.env, star (𝒩₁.isom (b₁, e₁) i₁) * 𝒩₁.isom (b₁, e₁) j₁) *
        (∑ b₂ : d₄, ∑ e₂ : 𝒩₂.env, star (𝒩₂.isom (b₂, e₂) i₂) * 𝒩₂.isom (b₂, e₂) j₂) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro b₁ _
      rw [Finset.sum_mul, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro b₂ _
      rw [Finset.mul_sum]
      conv_rhs => arg 2; ext e₁; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro e₁ _
      apply Finset.sum_congr rfl; intro e₂ _
      rw [star_mul']; ring
    rw [hfac]
    have h1 := congr_fun (congr_fun 𝒩₁.isom_eq i₁) j₁
    have h2 := congr_fun (congr_fun 𝒩₂.isom_eq i₂) j₂
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fintype.sum_prod_type] at h1 h2
    rw [h1, h2]
    by_cases h12 : i₁ = j₁ ∧ i₂ = j₂
    · rcases h12 with ⟨rfl, rfl⟩; simp
    · rw [if_neg (fun h ↦ h12 (Prod.mk.inj h))]
      by_cases ha : i₁ = j₁
      · have hb : i₂ ≠ j₂ := fun h ↦ h12 ⟨ha, h⟩
        simp [ha, hb]
      · simp [ha]

noncomputable def tensorPow {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ) :
    CPTPMap (Fin (2 ^ n) → Bool) (Fin (2 ^ n) → d) where
  env := Fin (2 ^ n) → 𝒩.env
  fintypeEnv := inferInstance
  decEqEnv := inferInstance
  isom := Matrix.of fun p x ↦ ∏ i : Fin (2 ^ n), 𝒩.isom (p.1 i, p.2 i) (x i)
  isom_eq := by
    ext x₁ x₂
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    let e : ((Fin (2 ^ n) → d) × (Fin (2 ^ n) → 𝒩.env)) ≃ (Fin (2 ^ n) → d × 𝒩.env) :=
      { toFun := fun p i ↦ (p.1 i, p.2 i)
        invFun := fun q ↦ (fun i ↦ (q i).1, fun i ↦ (q i).2)
        left_inv := fun ⟨_, _⟩ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hsum : ∑ p : (Fin (2 ^ n) → d) × (Fin (2 ^ n) → 𝒩.env),
        star (∏ i : Fin (2 ^ n), 𝒩.isom (p.1 i, p.2 i) (x₁ i)) *
          ∏ i : Fin (2 ^ n), 𝒩.isom (p.1 i, p.2 i) (x₂ i) =
        ∑ q : Fin (2 ^ n) → d × 𝒩.env,
          ∏ i : Fin (2 ^ n), star (𝒩.isom (q i) (x₁ i)) * 𝒩.isom (q i) (x₂ i) := by
      rw [← Equiv.sum_comp e.symm]
      apply Finset.sum_congr rfl; intro q _
      rw [star_prod, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      rfl
    rw [hsum, ← Fintype.prod_sum (fun i (p : d × 𝒩.env) ↦ star (𝒩.isom p (x₁ i)) * 𝒩.isom p (x₂ i))]
    have hfac : ∀ i : Fin (2 ^ n),
        ∑ p : d × 𝒩.env, star (𝒩.isom p (x₁ i)) * 𝒩.isom p (x₂ i) =
          if x₁ i = x₂ i then (1 : ℂ) else 0 := by
      intro i
      have h := congr_fun (congr_fun 𝒩.isom_eq (x₁ i)) (x₂ i)
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
    simp_rw [hfac]
    by_cases hx : x₁ = x₂
    · subst hx; simp
    · rw [if_neg hx]
      have hne : ∃ i : Fin (2 ^ n), x₁ i ≠ x₂ i := by
        by_contra hall; push Not at hall; exact hx (funext hall)
      obtain ⟨i₀, hi₀⟩ := hne
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀)

noncomputable def tensorIdLeft (α : Type) [Fintype α] [DecidableEq α]
    {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (𝒩 : CPTPMap β γ) : CPTPMap (α × β) (α × γ) where
  env := 𝒩.env
  fintypeEnv := 𝒩.fintypeEnv
  decEqEnv := 𝒩.decEqEnv
  isom := Matrix.of fun p q ↦ if p.1.1 = q.1 then 𝒩.isom (p.1.2, p.2) q.2 else 0
  isom_eq := by
    ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type]
    have h1 : ∀ a : α, (∑ c : γ, ∑ e : 𝒩.env,
        star (if a = a₁ then 𝒩.isom (c, e) b₁ else 0) *
          (if a = a₂ then 𝒩.isom (c, e) b₂ else 0)) =
        if a = a₁ ∧ a = a₂ then (if b₁ = b₂ then (1 : ℂ) else 0) else 0 := by
      intro a
      by_cases h12 : a = a₁ ∧ a = a₂
      · rcases h12 with ⟨rfl, rfl⟩
        simp only [↓reduceIte, and_self]
        have h := congr_fun (congr_fun 𝒩.isom_eq b₁) b₂
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
          Matrix.one_apply] using h
      · rw [if_neg h12]
        apply Finset.sum_eq_zero; intro c _
        apply Finset.sum_eq_zero; intro e _
        by_cases ha1 : a = a₁
        · have ha2 : a ≠ a₂ := fun h ↦ h12 ⟨ha1, h⟩
          rw [if_pos ha1, if_neg ha2, mul_zero]
        · rw [if_neg ha1, star_zero, zero_mul]
    simp_rw [h1]
    by_cases ha : a₁ = a₂
    · subst ha
      rw [Finset.sum_eq_single a₁]
      · simp
      · intro a _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ a₁) h
    · rw [if_neg (fun h ↦ ha (congr_arg Prod.fst h))]
      apply Finset.sum_eq_zero; intro a _
      have hne : ¬ (a = a₁ ∧ a = a₂) := fun ⟨h1, h2⟩ ↦ ha (h1.symm.trans h2)
      simp [hne]

noncomputable def seqComp {α β γ : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (ℳ : CPTPMap β γ) (𝒩 : CPTPMap α β) : CPTPMap α γ where
  env := ℳ.env × 𝒩.env
  fintypeEnv := @instFintypeProd _ _ ℳ.fintypeEnv 𝒩.fintypeEnv
  decEqEnv := @instDecidableEqProd _ _ ℳ.decEqEnv 𝒩.decEqEnv
  isom := Matrix.of fun p x ↦ ∑ y : β, ℳ.isom (p.1, p.2.1) y * 𝒩.isom (y, p.2.2) x
  isom_eq := by
    letI := ℳ.fintypeEnv; letI := ℳ.decEqEnv
    letI := 𝒩.fintypeEnv; letI := 𝒩.decEqEnv
    ext x₁ x₂
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type]
    have hswap : ∑ z : γ, ∑ e₂ : ℳ.env, ∑ e₁ : 𝒩.env,
        star (∑ y₁ : β, ℳ.isom (z, e₂) y₁ * 𝒩.isom (y₁, e₁) x₁) *
          (∑ y₂ : β, ℳ.isom (z, e₂) y₂ * 𝒩.isom (y₂, e₁) x₂) =
        ∑ y₁ : β, ∑ y₂ : β,
          (∑ z : γ, ∑ e₂ : ℳ.env, star (ℳ.isom (z, e₂) y₁) * ℳ.isom (z, e₂) y₂) *
          (∑ e₁ : 𝒩.env, star (𝒩.isom (y₁, e₁) x₁) * 𝒩.isom (y₂, e₁) x₂) := by
      simp_rw [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
      calc ∑ z : γ, ∑ e₂ : ℳ.env, ∑ e₁ : 𝒩.env, ∑ y₁ : β, ∑ y₂ : β,
            star (𝒩.isom (y₁, e₁) x₁) * star (ℳ.isom (z, e₂) y₁) * (ℳ.isom (z, e₂) y₂ * 𝒩.isom (y₂, e₁) x₂)
          = ∑ z : γ, ∑ e₂ : ℳ.env, ∑ y₁ : β, ∑ y₂ : β, ∑ e₁ : 𝒩.env,
              (star (ℳ.isom (z, e₂) y₁) * ℳ.isom (z, e₂) y₂) *
              (star (𝒩.isom (y₁, e₁) x₁) * 𝒩.isom (y₂, e₁) x₂) := by
            apply Finset.sum_congr rfl; intro z _
            apply Finset.sum_congr rfl; intro e₂ _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y₁ _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y₂ _
            apply Finset.sum_congr rfl; intro e₁ _; ring
        _ = ∑ y₁ : β, ∑ y₂ : β, ∑ z : γ, ∑ e₂ : ℳ.env, ∑ e₁ : 𝒩.env,
              (star (ℳ.isom (z, e₂) y₁) * ℳ.isom (z, e₂) y₂) *
              (star (𝒩.isom (y₁, e₁) x₁) * 𝒩.isom (y₂, e₁) x₂) := by
            rw [Finset.sum_comm]
            conv_lhs =>
              arg 2; ext e₂
              rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y₁ _
            rw [Finset.sum_comm]
            conv_lhs =>
              arg 2; ext z
              rw [Finset.sum_comm]
            rw [Finset.sum_comm]
    rw [hswap]
    have hM : ∀ y₁ y₂ : β,
        ∑ z : γ, ∑ e₂ : ℳ.env, star (ℳ.isom (z, e₂) y₁) * ℳ.isom (z, e₂) y₂ =
          if y₁ = y₂ then (1 : ℂ) else 0 := by
      intro y₁ y₂
      have h := congr_fun (congr_fun ℳ.isom_eq y₁) y₂
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Matrix.one_apply] using h
    simp_rw [hM]
    have hdiag : ∑ y₁ : β, ∑ y₂ : β,
        (if y₁ = y₂ then (1 : ℂ) else 0) *
          ∑ e₁ : 𝒩.env, star (𝒩.isom (y₁, e₁) x₁) * 𝒩.isom (y₂, e₁) x₂ =
        ∑ y : β, ∑ e₁ : 𝒩.env, star (𝒩.isom (y, e₁) x₁) * 𝒩.isom (y, e₁) x₂ := by
      apply Finset.sum_congr rfl; intro y₁ _
      rw [Finset.sum_eq_single y₁]
      · simp
      · intro y₂ _ hne; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ y₁) h
    rw [hdiag]
    have hN := congr_fun (congr_fun 𝒩.isom_eq x₁) x₂
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.one_apply] using hN

end CPTPMap

noncomputable def symCoherentInfo {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) : ℝ :=
  vonNeumannEntropy (𝒩.apply (maxMixedState Bool)) -
    vonNeumannEntropy (𝒩.complementary.apply (maxMixedState Bool))

noncomputable def ampChannel {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) : CQChannel d where
  out z := 𝒩.apply (CQChannel.ketBraBool z)

noncomputable def choiFactor {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) : Matrix (Bool × d) 𝒩.env ℂ :=
  Matrix.of fun (a, b) e ↦ ((Real.sqrt 2 : ℂ)⁻¹) * 𝒩.isom (b, e) a

noncomputable def choiState {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) : DensityOp (Bool × d) where
  mat := choiFactor 𝒩 * (choiFactor 𝒩)ᴴ
  posSemidef := by
    simpa [Matrix.conjTranspose_conjTranspose] using
      Matrix.posSemidef_conjTranspose_mul_self (choiFactor 𝒩)ᴴ
  trace_one := by
    have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
    have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast; ring
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      choiFactor, Matrix.of_apply, Fintype.sum_prod_type, star_mul', hstar2]
    have hterm : ∀ (a : Bool) (b : d) (e : 𝒩.env),
        ((Real.sqrt 2 : ℂ)⁻¹) * 𝒩.isom (b, e) a * (((Real.sqrt 2 : ℂ)⁻¹) * star (𝒩.isom (b, e) a)) =
        (1 / 2 : ℂ) * (star (𝒩.isom (b, e) a) * 𝒩.isom (b, e) a) := fun a b e ↦ by
      calc _ = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (star (𝒩.isom (b, e) a) * 𝒩.isom (b, e) a) := by ring
        _ = _ := by rw [hmul2]
    simp_rw [hterm, ← Finset.mul_sum]
    have hcol : ∀ a : Bool, ∑ b : d, ∑ e : 𝒩.env, star (𝒩.isom (b, e) a) * 𝒩.isom (b, e) a = 1 := by
      intro a
      have h := congr_fun (congr_fun 𝒩.isom_eq a) a
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type] using h
    rw [Fintype.sum_bool, hcol true, hcol false]
    ring

noncomputable def phaseChannel {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) : CQChannel (Bool × d) where
  out b := match b with
    | false => choiState 𝒩
    | true => (choiState 𝒩).conjUnitary (pauliZTensorI d)

def bitPathInv : (n : ℕ) → (Fin n → Bool) → Fin (2 ^ n)
  | 0, _ => ⟨0, by norm_num⟩
  | n + 1, b =>
      ⟨2 * (bitPathInv n (Fin.init b)).val + if b (Fin.last n) then 1 else 0, by
        have h := (bitPathInv n (Fin.init b)).isLt
        cases b (Fin.last n) <;> simp <;> omega⟩

def bitPathFwd : (n : ℕ) → Fin (2 ^ n) → (Fin n → Bool)
  | 0, _ => Fin.elim0
  | n + 1, i => Fin.snoc (α := fun _ ↦ Bool) (bitPathFwd n ⟨i.val / 2, by omega⟩) (decide (i.val % 2 = 1))

private lemma bitPathInv_fwd : ∀ (n : ℕ) (i : Fin (2 ^ n)), bitPathInv n (bitPathFwd n i) = i
  | 0, i => Fin.ext (by dsimp; omega)
  | n + 1, i => by
    apply Fin.ext
    simp only [bitPathInv, bitPathFwd, Fin.init_snoc, Fin.snoc_last]
    rw [bitPathInv_fwd n ⟨i.val / 2, by omega⟩]
    dsimp only
    by_cases hmod : i.val % 2 = 1 <;> simp [hmod] <;> omega

private lemma bitPathFwd_inv : ∀ (n : ℕ) (b : Fin n → Bool), bitPathFwd n (bitPathInv n b) = b
  | 0, b => funext fun k ↦ Fin.elim0 k
  | n + 1, b => by
    have hsnoc : b = Fin.snoc (α := fun _ ↦ Bool) (Fin.init b) (b (Fin.last n)) :=
      (Fin.snoc_init_self b).symm
    conv_rhs => rw [hsnoc]
    simp only [bitPathFwd, bitPathInv]
    have hdiv : (2 * (bitPathInv n (Fin.init b)).val + if b (Fin.last n) then 1 else 0) / 2 =
        (bitPathInv n (Fin.init b)).val := by
      cases b (Fin.last n) <;> simp <;> omega
    have hmod : decide ((2 * (bitPathInv n (Fin.init b)).val + if b (Fin.last n) then 1 else 0) % 2 = 1) =
        b (Fin.last n) := by
      cases b (Fin.last n) <;> simp <;> omega
    have hfin : (⟨(2 * (bitPathInv n (Fin.init b)).val + if b (Fin.last n) then 1 else 0) / 2,
        by omega⟩ : Fin (2 ^ n)) = bitPathInv n (Fin.init b) := Fin.ext hdiv
    rw [hfin, bitPathFwd_inv n (Fin.init b)]
    exact congrArg (Fin.snoc (α := fun _ ↦ Bool) (Fin.init b)) hmod

def bitPath (n : ℕ) : Fin (2 ^ n) ≃ (Fin n → Bool) where
  toFun := bitPathFwd n
  invFun := bitPathInv n
  left_inv := bitPathInv_fwd n
  right_inv := bitPathFwd_inv n

def dualIndex (n : ℕ) (i : Fin (2 ^ n)) : Fin (2 ^ n) :=
  (bitPath n).symm (fun k ↦ !(bitPath n i k))

noncomputable def goodSet {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (δ : ℝ) : Finset (Fin (2 ^ n)) :=
  Finset.univ.filter (fun i ↦ polarFidelity W n (bitPath n i) ≤ δ)

noncomputable def veryNoisySet {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (δ : ℝ) : Finset (Fin (2 ^ n)) :=
  Finset.univ.filter (fun i ↦ polarFidelity W.dual n (bitPath n (dualIndex n i)) ≤ δ)

noncomputable def unpolarizedSet {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (δ : ℝ) : Finset (Fin (2 ^ n)) :=
  Finset.univ \ (goodSet W n δ ∪ veryNoisySet W n δ)

structure CSSPrivatePolarCode {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ) (thresh : ℝ) where
  ampCode : CosetPolarCode (ampChannel 𝒩) n
  phaseCode : CosetPolarCode (phaseChannel 𝒩) n
  infoSet_align : phaseCode.infoSet = ampCode.infoSet.image (dualIndex n)
  assistanceSet : Finset (Fin (2 ^ n))
  assistanceSet_spec : assistanceSet =
    Finset.univ.filter (fun i : Fin (2 ^ n) ↦
      i ∉ goodSet (ampChannel 𝒩) n thresh ∧
      dualIndex n i ∉ goodSet (phaseChannel 𝒩) n thresh)

noncomputable def CSSPrivatePolarCode.rate {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap Bool d} {n : ℕ} {thresh : ℝ} (C : CSSPrivatePolarCode 𝒩 n thresh) : ℝ :=
  C.ampCode.rate

noncomputable def CSSPrivatePolarCode.assistanceRate {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap Bool d} {n : ℕ} {thresh : ℝ} (C : CSSPrivatePolarCode 𝒩 n thresh) : ℝ :=
  (C.assistanceSet.card : ℝ) / (2 : ℝ) ^ n

noncomputable def CSSPrivatePolarCode.ampPhaseErrorSum {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap Bool d} {n : ℕ} {thresh : ℝ} (C : CSSPrivatePolarCode 𝒩 n thresh) : ℝ :=
  C.ampCode.avgBlockError + C.phaseCode.avgBlockError

noncomputable def uniformBlockDiag {κ α : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    [Fintype α] [DecidableEq α] (ρ : κ → DensityOp α) : DensityOp (κ × α) where
  mat := Matrix.of fun (k₁, i₁) (k₂, i₂) ↦
    if k₁ = k₂ then ((Fintype.card κ : ℂ)⁻¹) * (ρ k₁).mat i₁ i₂ else 0
  posSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · ext ⟨k₁, i₁⟩ ⟨k₂, i₂⟩
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
      by_cases hk : k₂ = k₁
      · subst hk
        simp only [↓reduceIte, star_mul', Complex.star_def, map_inv₀, Complex.conj_natCast]
        have hh := congr_fun (congr_fun (ρ k₂).isHermitian.eq i₁) i₂
        simpa [Matrix.conjTranspose_apply] using congr_arg (((Fintype.card κ : ℂ)⁻¹) * ·) hh
      · simp [hk, Ne.symm hk]
    · intro v
      have hsum : star v ⬝ᵥ ((Matrix.of fun (k₁, i₁) (k₂, i₂) ↦
          if k₁ = k₂ then ((Fintype.card κ : ℂ)⁻¹) * (ρ k₁).mat i₁ i₂ else 0) *ᵥ v) =
          ∑ k : κ, ((Fintype.card κ : ℂ)⁻¹) *
            (star (fun i ↦ v (k, i)) ⬝ᵥ ((ρ k).mat *ᵥ (fun i ↦ v (k, i)))) := by
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.of_apply, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_eq_single k]
        · simp only [↓reduceIte]
          have hpull : ∑ x : α, ((Fintype.card κ : ℂ)⁻¹) * (ρ k).mat i x * v (k, x) =
              ((Fintype.card κ : ℂ)⁻¹) * ∑ x : α, (ρ k).mat i x * v (k, x) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
          rw [hpull]; ring
        · intro k' _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ k) h
      rw [hsum]
      refine Finset.sum_nonneg fun k _ ↦ ?_
      have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (ρ k).posSemidef).2 (fun i ↦ v (k, i))
      have hc : (0 : ℂ) ≤ (((Fintype.card κ : ℝ)⁻¹ : ℝ) : ℂ) :=
        Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg _))
      have hceq : (((Fintype.card κ : ℝ)⁻¹ : ℝ) : ℂ) = ((Fintype.card κ : ℂ)⁻¹) := by
        push_cast; rfl
      rw [← hceq]
      exact mul_nonneg hc hq
  trace_one := by
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, ↓reduceIte, Fintype.sum_prod_type]
    have htr : ∀ k : κ, ∑ i : α, ((Fintype.card κ : ℂ)⁻¹) * (ρ k).mat i i = ((Fintype.card κ : ℂ)⁻¹) := by
      intro k
      rw [← Finset.mul_sum]
      have h1 : ∑ i : α, (ρ k).mat i i = 1 := (ρ k).trace_one
      rw [h1, mul_one]
    simp_rw [htr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hne : (Fintype.card κ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact mul_inv_cancel₀ hne

def wiretapWord {N : ℕ} (infoSet randSet assistSet : Finset (Fin N))
    (uF : Fin N → Bool) (m : infoSet → Bool) (r : randSet → Bool) (k : assistSet → Bool) :
    Fin N → Bool :=
  fun i ↦
    if h1 : i ∈ infoSet then m ⟨i, h1⟩
    else if h2 : i ∈ randSet then r ⟨i, h2⟩
    else if h3 : i ∈ assistSet then k ⟨i, h3⟩
    else uF i

def bobEffectiveFrozen {N : ℕ} (assistSet : Finset (Fin N))
    (uF : Fin N → Bool) (k : assistSet → Bool) : Fin N → Bool :=
  fun i ↦ if h : i ∈ assistSet then k ⟨i, h⟩ else uF i

lemma productStateMat_posSemidef {α : Type*} [Fintype α] [DecidableEq α]
    (W : CQChannel α) (n : ℕ) (x : Fin (2 ^ n) → Bool) :
    (productStateMat W n x).PosSemidef := by
  let S : Matrix (Fin (2 ^ n) → α) (Fin (2 ^ n) → α) ℂ :=
    Matrix.of fun r s ↦ ∏ k : Fin (2 ^ n), (W.out (x k)).sqrtMat (r k) (s k)
  have hS : productStateMat W n x = Sᴴ * S := by
    ext r s
    simp only [productStateMat, S, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    have h1 : ∑ t : Fin (2 ^ n) → α,
        star (∏ k : Fin (2 ^ n), (W.out (x k)).sqrtMat (t k) (r k)) *
          ∏ k : Fin (2 ^ n), (W.out (x k)).sqrtMat (t k) (s k) =
        ∑ t : Fin (2 ^ n) → α,
          ∏ k : Fin (2 ^ n),
            star ((W.out (x k)).sqrtMat (t k) (r k)) * (W.out (x k)).sqrtMat (t k) (s k) := by
      apply Finset.sum_congr rfl; intro t _
      rw [star_prod, ← Finset.prod_mul_distrib]
    rw [h1, ← Fintype.prod_sum (fun k (a : α) ↦
      star ((W.out (x k)).sqrtMat a (r k)) * (W.out (x k)).sqrtMat a (s k))]
    apply Finset.prod_congr rfl; intro k _
    have hmul := congr_fun (congr_fun (W.out (x k)).sqrtMat_mul_self (r k)) (s k)
    rw [← hmul, Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro a _
    have hh := congr_fun (congr_fun (W.out (x k)).sqrtMat_isHermitian.eq (r k)) a
    simp only [Matrix.conjTranspose_apply] at hh
    rw [hh]
  rw [hS]
  exact Matrix.posSemidef_conjTranspose_mul_self S

lemma productStateMat_trace_one {α : Type*} [Fintype α] [DecidableEq α]
    (W : CQChannel α) (n : ℕ) (x : Fin (2 ^ n) → Bool) :
    (productStateMat W n x).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, productStateMat, Matrix.of_apply]
  rw [← Fintype.prod_sum (fun k (a : α) ↦ (W.out (x k)).mat a a)]
  apply Finset.prod_eq_one; intro k _
  exact (W.out (x k)).trace_one

noncomputable def fixedSubsetAvgState {α : Type*} [Fintype α] [DecidableEq α]
    (W : CQChannel α) (n : ℕ) (S : Finset (Fin (2 ^ n))) (u : Fin (2 ^ n) → Bool) :
    DensityOp (Fin (2 ^ n) → α) where
  mat := ((2 : ℂ) ^ (2 ^ n - S.card))⁻¹ •
    ∑ v ∈ Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ S, v j = u j),
      productStateMat W n (arikanTransform n v)
  posSemidef := by
    have hc : (0 : ℝ) ≤ ((2 : ℝ) ^ (2 ^ n - S.card))⁻¹ := by positivity
    have hsum : (∑ v ∈ Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ S, v j = u j),
        productStateMat W n (arikanTransform n v)).PosSemidef :=
      Finset.sum_induction _ (fun M : Matrix _ _ ℂ ↦ M.PosSemidef)
        (fun _ _ ha hb ↦ ha.add hb) Matrix.PosSemidef.zero
        (fun v _ ↦ productStateMat_posSemidef W n (arikanTransform n v))
    have hsm : ((2 : ℂ) ^ (2 ^ n - S.card))⁻¹ •
        ∑ v ∈ Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ S, v j = u j),
          productStateMat W n (arikanTransform n v) =
        (((2 : ℝ) ^ (2 ^ n - S.card))⁻¹) •
        ∑ v ∈ Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ S, v j = u j),
          productStateMat W n (arikanTransform n v) := by
      ext i j; simp [Complex.real_smul]
    rw [hsm]; exact hsum.smul hc
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_sum]
    have htr : ∀ v : Fin (2 ^ n) → Bool, (productStateMat W n (arikanTransform n v)).trace = 1 :=
      fun v ↦ productStateMat_trace_one W n (arikanTransform n v)
    simp_rw [htr, Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul]
    have hcard : (Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ S, v j = u j)).card =
        2 ^ (2 ^ n - S.card) := by
      let e : {v : Fin (2 ^ n) → Bool // ∀ j ∈ S, v j = u j} ≃ ({j : Fin (2 ^ n) // j ∉ S} → Bool) :=
        { toFun := fun v j ↦ v.1 j.1
          invFun := fun w ↦ ⟨fun j ↦ if h : j ∈ S then u j else w ⟨j, h⟩,
            fun j hj ↦ by simp [hj]⟩
          left_inv := fun ⟨v, hv⟩ ↦ Subtype.ext (funext fun j ↦ by
            by_cases hj : j ∈ S
            · simp [hj, hv j hj]
            · simp [hj])
          right_inv := fun w ↦ funext fun ⟨j, hj⟩ ↦ by simp [hj] }
      rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool]
      congr 1
      rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
    rw [hcard]
    push_cast
    exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))

noncomputable def wiretapEveCondState {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (uF : Fin (2 ^ n) → Bool) (m : infoSet → Bool) :
    DensityOp (Fin (2 ^ n) → 𝒩.env) :=
  fixedSubsetAvgState (ampChannel 𝒩.complementary) n (randSet ∪ assistSet)ᶜ
    (fun i ↦ if h : i ∈ infoSet then m ⟨i, h⟩ else uF i)

noncomputable def wiretapEveJointState {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (uF : Fin (2 ^ n) → Bool) :
    DensityOp ((infoSet → Bool) × (Fin (2 ^ n) → 𝒩.env)) :=
  uniformBlockDiag (fun m ↦ wiretapEveCondState 𝒩 n infoSet randSet assistSet uF m)

noncomputable def wiretapIdealEveState {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ)
    (infoSet : Finset (Fin (2 ^ n))) :
    DensityOp ((infoSet → Bool) × (Fin (2 ^ n) → 𝒩.env)) :=
  uniformBlockDiag (fun _ : infoSet → Bool ↦
    fixedSubsetAvgState (ampChannel 𝒩.complementary) n ∅ (fun _ ↦ false))

noncomputable def wiretapSecrecyError {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (uF : Fin (2 ^ n) → Bool) : ℝ :=
  traceDist (wiretapEveJointState 𝒩 n infoSet randSet assistSet uF)
    (wiretapIdealEveState 𝒩 n infoSet)

noncomputable def qscAvgBlockError {d : Type*} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (infoSet : Finset (Fin (2 ^ n)))
    (frozen : Fin (2 ^ n) → Bool) : ℝ :=
  ((2 : ℝ) ^ infoSet.card)⁻¹ *
    ∑ m : {i : Fin (2 ^ n) // i ∈ infoSet} → Bool,
      (1 - (((qscPrefixKraus W n infoSet (2 ^ n) le_rfl (embedMsg infoSet frozen m))ᴴ *
        qscPrefixKraus W n infoSet (2 ^ n) le_rfl (embedMsg infoSet frozen m) *
        productStateMat W n (arikanTransform n (embedMsg infoSet frozen m))).trace).re)

noncomputable def wiretapBobError {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (uF : Fin (2 ^ n) → Bool) : ℝ :=
  ((2 : ℝ) ^ assistSet.card)⁻¹ *
    ∑ k : assistSet → Bool,
      qscAvgBlockError (ampChannel 𝒩) n (infoSet ∪ randSet)
        (bobEffectiveFrozen assistSet uF k)

structure OperationalPrivatePolarCode {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ) where
  infoSet : Finset (Fin (2 ^ n))
  randSet : Finset (Fin (2 ^ n))
  assistSet : Finset (Fin (2 ^ n))
  disjoint_info_rand : Disjoint infoSet randSet
  disjoint_info_assist : Disjoint infoSet assistSet
  disjoint_rand_assist : Disjoint randSet assistSet
  publicFrozen : Fin (2 ^ n) → Bool

noncomputable def OperationalPrivatePolarCode.rate {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap Bool d} {n : ℕ} (C : OperationalPrivatePolarCode 𝒩 n) : ℝ :=
  (C.infoSet.card : ℝ) / (2 : ℝ) ^ n

noncomputable def OperationalPrivatePolarCode.secretKeyRate {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap Bool d} {n : ℕ} (C : OperationalPrivatePolarCode 𝒩 n) : ℝ :=
  (C.assistSet.card : ℝ) / (2 : ℝ) ^ n

noncomputable def OperationalPrivatePolarCode.bobDecodingError {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap Bool d} {n : ℕ} (C : OperationalPrivatePolarCode 𝒩 n) : ℝ :=
  wiretapBobError 𝒩 n C.infoSet C.randSet C.assistSet C.publicFrozen

noncomputable def OperationalPrivatePolarCode.eveSecrecyError {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap Bool d} {n : ℕ} (C : OperationalPrivatePolarCode 𝒩 n) : ℝ :=
  wiretapSecrecyError 𝒩 n C.infoSet C.randSet C.assistSet C.publicFrozen

noncomputable def maxEntangledVec (α : Type) [Fintype α] [DecidableEq α] : α × α → ℂ :=
  fun p ↦ if p.1 = p.2 then ((Real.sqrt (Fintype.card α) : ℝ) : ℂ)⁻¹ else 0

lemma maxEntangledVec_norm (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] :
    ∑ p : α × α, ‖maxEntangledVec α p‖ ^ 2 = 1 := by
  rw [Fintype.sum_prod_type]
  have hrow : ∀ a : α, ∑ b : α, ‖maxEntangledVec α (a, b)‖ ^ 2 = (Fintype.card α : ℝ)⁻¹ := by
    intro a
    rw [Finset.sum_eq_single a]
    · simp only [maxEntangledVec, ↓reduceIte, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    · intro b _ hne; simp [maxEntangledVec, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ a) h
  simp_rw [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

noncomputable def maxEntangledState (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] :
    DensityOp (α × α) :=
  pureState (maxEntangledVec α) (maxEntangledVec_norm α)

def phaseSign {α : Type*} [Fintype α] (v r : α → Bool) : ℂ :=
  ∏ i : α, if v i && r i then (-1 : ℂ) else (1 : ℂ)

lemma phaseSign_star {α : Type*} [Fintype α] (v r : α → Bool) :
    star (phaseSign v r) = phaseSign v r := by
  simp only [phaseSign, star_prod]
  apply Finset.prod_congr rfl; intro i _
  cases v i <;> cases r i <;> simp

lemma phaseSign_mul_self {α : Type*} [Fintype α] (v r : α → Bool) :
    phaseSign v r * phaseSign v r = 1 := by
  simp only [phaseSign, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one; intro i _
  cases v i <;> cases r i <;> simp

noncomputable def cssPolarEncoderIsom (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (uF : Fin (2 ^ n) → Bool) (v : randSet → Bool) :
    Matrix (Fin (2 ^ n) → Bool) ((infoSet → Bool) × (assistSet → Bool)) ℂ :=
  Matrix.of fun x p ↦
    ((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹ *
      ∑ r : randSet → Bool,
        if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF p.1 r p.2) then
          phaseSign v r
        else 0

lemma cssPolarEncoderIsom_isometry (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (hdisj_ir : Disjoint infoSet randSet)
    (hdisj_ia : Disjoint infoSet assistSet)
    (hdisj_ra : Disjoint randSet assistSet)
    (uF : Fin (2 ^ n) → Bool) (v : randSet → Bool) :
    (cssPolarEncoderIsom n infoSet randSet assistSet uF v)ᴴ *
      cssPolarEncoderIsom n infoSet randSet assistSet uF v = 1 := by
  have hinj : ∀ m₁ m₂ r₁ r₂ a₁ a₂,
      arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) =
      arikanTransform n (wiretapWord infoSet randSet assistSet uF m₂ r₂ a₂) →
      m₁ = m₂ ∧ r₁ = r₂ ∧ a₁ = a₂ := by
    intro m₁ m₂ r₁ r₂ a₁ a₂ heq
    have hw := (arikanTransform_bijective n).injective heq
    refine ⟨?_, ?_, ?_⟩
    · funext ⟨i, hi⟩
      have h := congr_fun hw i
      simpa [wiretapWord, hi] using h
    · funext ⟨i, hi⟩
      have h := congr_fun hw i
      have hni : i ∉ infoSet := Finset.disjoint_right.mp hdisj_ir hi
      simpa [wiretapWord, hni, hi] using h
    · funext ⟨i, hi⟩
      have h := congr_fun hw i
      have hni : i ∉ infoSet := Finset.disjoint_right.mp hdisj_ia hi
      have hnr : i ∉ randSet := Finset.disjoint_right.mp hdisj_ra hi
      simpa [wiretapWord, hni, hnr, hi] using h
  ext ⟨m₁, a₁⟩ ⟨m₂, a₂⟩
  simp only [cssPolarEncoderIsom, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply, star_mul, star_sum, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hnorm : (((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹) *
      (((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹) =
      (((2 : ℝ) ^ randSet.card : ℝ) : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  calc ∑ x : Fin (2 ^ n) → Bool,
        (∑ r₁ : randSet → Bool, star (if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) then phaseSign v r₁ else 0)) *
          ((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹ *
        (((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹ *
          ∑ r₂ : randSet → Bool, if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m₂ r₂ a₂) then phaseSign v r₂ else 0)
      = (((2 : ℝ) ^ randSet.card : ℝ) : ℂ)⁻¹ *
          ∑ r₁ : randSet → Bool, ∑ r₂ : randSet → Bool,
            ∑ x : Fin (2 ^ n) → Bool,
              (if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) then phaseSign v r₁ else 0) *
              (if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m₂ r₂ a₂) then phaseSign v r₂ else 0) := by
        rw [Finset.mul_sum]
        conv_rhs => arg 2; ext r₁; rw [Finset.mul_sum]
        conv_rhs => arg 2; ext r₁; arg 2; ext r₂; rw [Finset.mul_sum]
        conv_rhs => arg 2; ext r₁; rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro x _
        have hst : ∀ r₁ : randSet → Bool,
            star (if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) then phaseSign v r₁ else 0) =
            if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) then phaseSign v r₁ else 0 := by
          intro r₁; split_ifs <;> simp [phaseSign_star]
        simp_rw [hst, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro r₁ _
        apply Finset.sum_congr rfl; intro r₂ _
        rw [← hnorm]; ring
    _ = (((2 : ℝ) ^ randSet.card : ℝ) : ℂ)⁻¹ *
          ∑ r₁ : randSet → Bool, ∑ r₂ : randSet → Bool,
            if arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) =
               arikanTransform n (wiretapWord infoSet randSet assistSet uF m₂ r₂ a₂) then
              phaseSign v r₁ * phaseSign v r₂
            else 0 := by
        congr 1; apply Finset.sum_congr rfl; intro r₁ _
        apply Finset.sum_congr rfl; intro r₂ _
        rw [Finset.sum_eq_single (arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁))]
        · simp [mul_ite]
        · intro x _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
    _ = if (m₁, a₁) = (m₂, a₂) then 1 else 0 := by
        by_cases hma : (m₁, a₁) = (m₂, a₂)
        · rw [if_pos hma]
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hma
          have hdiag : ∀ r₁ : randSet → Bool,
              ∑ r₂ : randSet → Bool,
                (if arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) =
                    arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₂ a₁) then
                  phaseSign v r₁ * phaseSign v r₂
                else 0) = 1 := by
            intro r₁
            rw [Finset.sum_eq_single r₁]
            · simp [phaseSign_mul_self]
            · intro r₂ _ hne; rw [if_neg]; intro heq; exact hne (hinj m₁ m₁ r₁ r₂ a₁ a₁ heq).2.1.symm
            · intro h; exact absurd (Finset.mem_univ r₁) h
          simp_rw [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_coe, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
          push_cast
          exact inv_mul_cancel₀ (by positivity)
        · rw [if_neg hma]
          have h0 : ∑ r₁ : randSet → Bool, ∑ r₂ : randSet → Bool,
              (if arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) =
                  arikanTransform n (wiretapWord infoSet randSet assistSet uF m₂ r₂ a₂) then
                phaseSign v r₁ * phaseSign v r₂
              else 0) = 0 := by
            apply Finset.sum_eq_zero; intro r₁ _
            apply Finset.sum_eq_zero; intro r₂ _
            rw [if_neg]; intro heq
            obtain ⟨hm, _, ha⟩ := hinj m₁ m₂ r₁ r₂ a₁ a₂ heq
            exact hma (Prod.ext hm ha)
          rw [h0, mul_zero]

noncomputable def cssPolarEncoder (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (hdisj_ir : Disjoint infoSet randSet)
    (hdisj_ia : Disjoint infoSet assistSet)
    (hdisj_ra : Disjoint randSet assistSet)
    (uF : Fin (2 ^ n) → Bool) (v : randSet → Bool) :
    CPTPMap ((infoSet → Bool) × (assistSet → Bool)) (Fin (2 ^ n) → Bool) where
  env := Unit
  fintypeEnv := inferInstance
  decEqEnv := inferInstance
  isom := Matrix.of fun p q ↦ cssPolarEncoderIsom n infoSet randSet assistSet uF v p.1 q
  isom_eq := by
    have h := cssPolarEncoderIsom_isometry n infoSet randSet assistSet hdisj_ir hdisj_ia hdisj_ra uF v
    ext q₁ q₂
    have hq := congr_fun (congr_fun h q₁) q₂
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type] using hq

noncomputable def entanglementChannelOutput {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ)
    (infoSet assistSet : Finset (Fin (2 ^ n)))
    (ℰ : CPTPMap ((infoSet → Bool) × (assistSet → Bool)) (Fin (2 ^ n) → Bool))
    (𝒟 : CPTPMap ((Fin (2 ^ n) → d) × (assistSet → Bool)) (infoSet → Bool)) :
    DensityOp ((infoSet → Bool) × (infoSet → Bool)) :=
  let initVec : (infoSet → Bool) × (((infoSet → Bool) × (assistSet → Bool)) × (assistSet → Bool)) → ℂ :=
    fun p ↦ maxEntangledVec (infoSet → Bool) (p.1, p.2.1.1) *
            maxEntangledVec (assistSet → Bool) (p.2.1.2, p.2.2)
  have hinit : ∑ p, ‖initVec p‖ ^ 2 = 1 := by
    simp only [initVec, norm_mul, mul_pow, Fintype.sum_prod_type]
    have h1 : ∀ m₁ m₂ : infoSet → Bool,
        ∑ a₁ : assistSet → Bool, ∑ a₂ : assistSet → Bool,
          ‖maxEntangledVec (infoSet → Bool) (m₁, m₂)‖ ^ 2 *
          ‖maxEntangledVec (assistSet → Bool) (a₁, a₂)‖ ^ 2 =
        ‖maxEntangledVec (infoSet → Bool) (m₁, m₂)‖ ^ 2 := by
      intro m₁ m₂
      simp_rw [← Finset.mul_sum]
      rw [← Fintype.sum_prod_type (f := fun p ↦ ‖maxEntangledVec (assistSet → Bool) p‖ ^ 2),
        maxEntangledVec_norm (assistSet → Bool), mul_one]
    simp_rw [h1]
    rw [← Fintype.sum_prod_type (f := fun p ↦ ‖maxEntangledVec (infoSet → Bool) p‖ ^ 2)]
    exact maxEntangledVec_norm (infoSet → Bool)
  let initState := pureState initVec hinit
  let aliceToBob : CPTPMap (((infoSet → Bool) × (assistSet → Bool)) × (assistSet → Bool))
      ((Fin (2 ^ n) → d) × (assistSet → Bool)) :=
    ((𝒩.tensorPow n).seqComp ℰ).tensor (CPTPMap.id (assistSet → Bool))
  let fullBob : CPTPMap (((infoSet → Bool) × (assistSet → Bool)) × (assistSet → Bool))
      (infoSet → Bool) :=
    𝒟.seqComp aliceToBob
  (CPTPMap.tensorIdLeft (infoSet → Bool) fullBob).apply initState

noncomputable def quantumEntanglementError {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ)
    (infoSet assistSet : Finset (Fin (2 ^ n)))
    (ℰ : CPTPMap ((infoSet → Bool) × (assistSet → Bool)) (Fin (2 ^ n) → Bool))
    (𝒟 : CPTPMap ((Fin (2 ^ n) → d) × (assistSet → Bool)) (infoSet → Bool)) : ℝ :=
  traceDist (entanglementChannelOutput 𝒩 n infoSet assistSet ℰ 𝒟)
    (maxEntangledState (infoSet → Bool))

structure OperationalQuantumPolarCode {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ) where
  infoSet : Finset (Fin (2 ^ n))
  randSet : Finset (Fin (2 ^ n))
  assistSet : Finset (Fin (2 ^ n))
  disj_ir : Disjoint infoSet randSet
  disj_ia : Disjoint infoSet assistSet
  disj_ra : Disjoint randSet assistSet
  publicFrozen : Fin (2 ^ n) → Bool
  phaseChoice : randSet → Bool
  decoder : CPTPMap ((Fin (2 ^ n) → d) × (assistSet → Bool)) (infoSet → Bool)

noncomputable def OperationalQuantumPolarCode.encoder {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap Bool d} {n : ℕ} (C : OperationalQuantumPolarCode 𝒩 n) :
    CPTPMap ((C.infoSet → Bool) × (C.assistSet → Bool)) (Fin (2 ^ n) → Bool) :=
  cssPolarEncoder n C.infoSet C.randSet C.assistSet C.disj_ir C.disj_ia C.disj_ra
    C.publicFrozen C.phaseChoice

noncomputable def OperationalQuantumPolarCode.entanglementError {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap Bool d} {n : ℕ} (C : OperationalQuantumPolarCode 𝒩 n) : ℝ :=
  quantumEntanglementError 𝒩 n C.infoSet C.assistSet C.encoder C.decoder

noncomputable def OperationalQuantumPolarCode.rate {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap Bool d} {n : ℕ} (C : OperationalQuantumPolarCode 𝒩 n) : ℝ :=
  (C.infoSet.card : ℝ) / ((2 : ℝ) ^ n)

noncomputable def OperationalQuantumPolarCode.assistanceRate {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap Bool d} {n : ℕ} (C : OperationalQuantumPolarCode 𝒩 n) : ℝ :=
  (C.assistSet.card : ℝ) / ((2 : ℝ) ^ n)

end PolarCodesChallenge
