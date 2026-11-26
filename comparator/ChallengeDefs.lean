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

def embedMsg {N : ℕ} (infoSet : Finset (Fin N)) (frozen : Fin N → Bool)
    (m : {i : Fin N // i ∈ infoSet} → Bool) : Fin N → Bool :=
  fun i ↦ if hi : i ∈ infoSet then m ⟨i, hi⟩ else frozen i

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
  | 0, i => Fin.ext (by omega)
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

end PolarCodesChallenge
