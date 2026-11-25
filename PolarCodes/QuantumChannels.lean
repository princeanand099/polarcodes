/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.DataProcessing

/-!
# Finite-Dimensional Quantum Channels (CPTP Maps) and General Data Processing Inequality

This module formalizes finite-dimensional completely positive trace-preserving (CPTP) maps via
Stinespring isometric extensions `V : ℂ^{d₁} → ℂ^{d₂} ⊗ ℂ^{env}` (`Vᴴ * V = 1`):
- `CPTPMap d₁ d₂`, channel application `CPTPMap.apply`, complementary channel
  `CPTPMap.complementary`, identity `CPTPMap.id`, composition `CPTPMap.comp`, degradability
  `CPTPMap.IsDegradable`, and post-processing of c-q channels `CPTPMap.compCQ`.
- **General CPTP Data Processing Inequality**:
  - `relEntropy_cptp_le`: `D(𝒩(ρ) ‖ 𝒩(σ)) ≤ D(ρ ‖ σ)` for all density operators `ρ, σ`,
  - `qjs_cptp_le`: `QJS(𝒩(ρ), 𝒩(σ)) ≤ QJS(ρ, σ)` for all density operators `ρ, σ`,
  - `condEntropy_cptp_ge`: `H(𝒩 ∘ W) ≥ H(W)` for every binary-input c-q channel `W`.
-/

open Matrix BigOperators Real Set Filter Topology MeasureTheory
open scoped ComplexOrder ENNReal

namespace PolarCodes

universe u

/-! ### Stinespring Representation of CPTP Maps -/

/-- A finite-dimensional completely positive trace-preserving (CPTP) map `𝒩 : B(ℂ^{d₁}) → B(ℂ^{d₂})`
represented by a Stinespring isometry `V : Matrix (d₂ × env) d₁ ℂ` satisfying `Vᴴ * V = 1`. -/
structure CPTPMap (d₁ : Type u) (d₂ : Type u) [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] where
  env : Type u
  fintypeEnv : Fintype env
  decEqEnv : DecidableEq env
  isom : Matrix (d₂ × env) d₁ ℂ
  isom_eq : isomᴴ * isom = 1

attribute [instance] CPTPMap.fintypeEnv CPTPMap.decEqEnv

namespace CPTPMap

variable {d₁ d₂ d₃ : Type u} [Fintype d₁] [DecidableEq d₁]
  [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃]

/-- Underlying `ℂ`-linear superoperator `X ↦ Tr_E(V X Vᴴ)`. -/
def toLinearMap (𝒩 : CPTPMap d₁ d₂) : Matrix d₁ d₁ ℂ →ₗ[ℂ] Matrix d₂ d₂ ℂ where
  toFun X := partialTrace₂Mat d₂ 𝒩.env (𝒩.isom * X * 𝒩.isomᴴ)
  map_add' A B := by
    rw [Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' c A := by
    rw [Matrix.mul_smul, Matrix.smul_mul, map_smul, RingHom.id_apply]

lemma toLinearMap_posSemidef (𝒩 : CPTPMap d₁ d₂) {X : Matrix d₁ d₁ ℂ} (hX : X.PosSemidef) :
    (𝒩.toLinearMap X).PosSemidef :=
  partialTrace₂Mat_posSemidef (hX.mul_mul_conjTranspose_same 𝒩.isom)

lemma toLinearMap_trace (𝒩 : CPTPMap d₁ d₂) (X : Matrix d₁ d₁ ℂ) :
    (𝒩.toLinearMap X).trace = X.trace := by
  change (partialTrace₂Mat d₂ 𝒩.env (𝒩.isom * X * 𝒩.isomᴴ)).trace = X.trace
  rw [partialTrace₂Mat_trace, Matrix.trace_mul_cycle, 𝒩.isom_eq, Matrix.one_mul]

lemma toLinearMap_isHermitian (𝒩 : CPTPMap d₁ d₂) {X : Matrix d₁ d₁ ℂ} (hX : X.IsHermitian) :
    (𝒩.toLinearMap X).IsHermitian := by
  apply partialTrace₂Mat_isHermitian
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hX.eq, Matrix.mul_assoc]

/-- Action of a CPTP map on density operators: `𝒩(ρ) = Tr_E(V ρ Vᴴ)`. -/
def apply (𝒩 : CPTPMap d₁ d₂) (ρ : DensityOp d₁) : DensityOp d₂ where
  mat := 𝒩.toLinearMap ρ.mat
  posSemidef := 𝒩.toLinearMap_posSemidef ρ.posSemidef
  trace_one := by rw [𝒩.toLinearMap_trace, ρ.trace_one]

/-- Complementary channel `𝒩^c : B(ℂ^{d₁}) → B(ℂ^{env})` obtained by tracing out the output
system `d₂` instead of `env`. -/
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
    rw [Finset.sum_comm]
    exact h

/-- Identity CPTP map `id_d : B(ℂ^d) → B(ℂ^d)`. -/
def id (d : Type u) [Fintype d] [DecidableEq d] : CPTPMap d d where
  env := PUnit
  fintypeEnv := inferInstance
  decEqEnv := inferInstance
  isom := Matrix.of fun p j ↦ if p.1 = j then (1 : ℂ) else 0
  isom_eq := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fintype.sum_unique]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hbi; simp [Ne.symm hbi]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [hij, ↓reduceIte]
      apply Finset.sum_eq_zero; intro b _
      by_cases hbi : b = i
      · subst hbi; simp [hij]
      · simp [hbi]

/-- Composition `ℳ ∘ 𝒩` of CPTP maps. -/
def comp (ℳ : CPTPMap d₂ d₃) (𝒩 : CPTPMap d₁ d₂) : CPTPMap d₁ d₃ where
  env := ℳ.env × 𝒩.env
  fintypeEnv := inferInstance
  decEqEnv := inferInstance
  isom := Matrix.of fun p a ↦ ∑ b : d₂, ℳ.isom (p.1, p.2.1) b * 𝒩.isom (b, p.2.2) a
  isom_eq := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, star_sum, star_mul']
    calc ∑ c : d₃, ∑ e₂ : ℳ.env, ∑ e₁ : 𝒩.env,
          (∑ b₁ : d₂, star (𝒩.isom (b₁, e₁) i) * star (ℳ.isom (c, e₂) b₁)) *
          (∑ b₂ : d₂, ℳ.isom (c, e₂) b₂ * 𝒩.isom (b₂, e₁) j)
        = ∑ b₁ : d₂, ∑ b₂ : d₂, ∑ e₁ : 𝒩.env,
            star (𝒩.isom (b₁, e₁) i) * 𝒩.isom (b₂, e₁) j *
            (∑ c : d₃, ∑ e₂ : ℳ.env, star (ℳ.isom (c, e₂) b₁) * ℳ.isom (c, e₂) b₂) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          have h1 : ∀ c : d₃, ∑ e₂ : ℳ.env, ∑ e₁ : 𝒩.env, ∑ b₁ : d₂, ∑ b₂ : d₂,
              star (𝒩.isom (b₁, e₁) i) * star (ℳ.isom (c, e₂) b₁) *
                (ℳ.isom (c, e₂) b₂ * 𝒩.isom (b₂, e₁) j) =
              ∑ b₁ : d₂, ∑ b₂ : d₂, ∑ e₁ : 𝒩.env, ∑ e₂ : ℳ.env,
                star (𝒩.isom (b₁, e₁) i) * 𝒩.isom (b₂, e₁) j *
                  (star (ℳ.isom (c, e₂) b₁) * ℳ.isom (c, e₂) b₂) := by
            intro c
            rw [Finset.sum_comm]
            conv_lhs => arg 2; ext e₁; rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            conv_lhs => arg 2; ext b₁; rw [Finset.sum_comm]
            conv_lhs => arg 2; ext b₁; arg 2; ext e₁; rw [Finset.sum_comm]
            conv_lhs => arg 2; ext b₁; rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro b₁ _
            apply Finset.sum_congr rfl; intro b₂ _
            apply Finset.sum_congr rfl; intro e₁ _
            apply Finset.sum_congr rfl; intro e₂ _
            ring
          simp_rw [h1]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro b₁ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro b₂ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro e₁ _
          simp_rw [Finset.mul_sum]
      _ = ∑ b₁ : d₂, ∑ b₂ : d₂, ∑ e₁ : 𝒩.env,
            star (𝒩.isom (b₁, e₁) i) * 𝒩.isom (b₂, e₁) j *
            (1 : Matrix d₂ d₂ ℂ) b₁ b₂ := by
          apply Finset.sum_congr rfl; intro b₁ _
          apply Finset.sum_congr rfl; intro b₂ _
          apply Finset.sum_congr rfl; intro e₁ _
          congr 1
          have h := congr_fun (congr_fun ℳ.isom_eq b₁) b₂
          simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type] using h
      _ = ∑ b₁ : d₂, ∑ e₁ : 𝒩.env, star (𝒩.isom (b₁, e₁) i) * 𝒩.isom (b₁, e₁) j := by
          apply Finset.sum_congr rfl; intro b₁ _
          rw [Finset.sum_eq_single b₁]
          · simp [Matrix.one_apply]
          · intro b₂ _ hb; simp [Matrix.one_apply, Ne.symm hb]
          · intro h; exact absurd (Finset.mem_univ _) h
      _ = (1 : Matrix d₁ d₁ ℂ) i j := by
          have h := congr_fun (congr_fun 𝒩.isom_eq i) j
          simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type] using h

lemma comp_apply (ℳ : CPTPMap d₂ d₃) (𝒩 : CPTPMap d₁ d₂) (ρ : DensityOp d₁) :
    ((ℳ.comp 𝒩).apply ρ).mat = (ℳ.apply (𝒩.apply ρ)).mat := by
  ext c₁ c₂
  simp only [apply, toLinearMap, comp, partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    star_sum, star_mul']
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro e₂ _
  simp_rw [Finset.mul_sum]
  conv_lhs => arg 2; ext e₁; arg 2; ext a₂; arg 2; ext a₁; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext e₁; arg 2; ext a₂; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext e₁; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b₂ _
  conv_lhs => arg 2; ext e₁; arg 2; ext a₂; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext e₁; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b₁ _
  apply Finset.sum_congr rfl; intro e₁ _
  apply Finset.sum_congr rfl; intro a₂ _
  apply Finset.sum_congr rfl; intro a₁ _
  ring

/-- A quantum channel `𝒩` is *degradable* if its complementary channel `𝒩^c` factors through
`𝒩` via some degrading CPTP map `𝒟 : B(ℂ^{d₂}) → B(ℂ^{env})`. -/
def IsDegradable (𝒩 : CPTPMap d₁ d₂) : Prop :=
  ∃ 𝒟 : CPTPMap d₂ 𝒩.env, ∀ ρ : DensityOp d₁,
    (𝒟.apply (𝒩.apply ρ)).mat = (𝒩.complementary.apply ρ).mat

/-- Post-processing a binary-input c-q channel `W` by a CPTP map `𝒩`. -/
def compCQ (𝒩 : CPTPMap d₁ d₂) (W : CQChannel d₁) : CQChannel d₂ where
  out b := 𝒩.apply (W.out b)

end CPTPMap

/-! ### General CPTP Data Processing Inequality -/

section CPTPDPI

variable {d d₁ d₂ : Type u} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-- Uniqueness of Hermitian functional calculus: for any Hermitian `M = U diag(λ) Uᴴ` and any
function `f : ℝ → ℝ`, `U diag(f ∘ λ) Uᴴ` depends only on `M` and `f`. -/
lemma hermitian_func_eq {M : Matrix d d ℂ} (hM : M.IsHermitian)
    (U : Matrix.unitaryGroup d ℂ) (lam : d → ℝ)
    (hspec : M = (U : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ lam) * star (U : Matrix d d ℂ))
    (f : ℝ → ℝ) :
    (hM.eigenvectorUnitary : Matrix d d ℂ) * Matrix.diagonal (fun j ↦ (f (hM.eigenvalues j) : ℂ)) *
        star (hM.eigenvectorUnitary : Matrix d d ℂ) =
      (U : Matrix d d ℂ) * Matrix.diagonal (fun k ↦ (f (lam k) : ℂ)) * star (U : Matrix d d ℂ) := by
  set U₁ : Matrix d d ℂ := (hM.eigenvectorUnitary : Matrix d d ℂ)
  set U₂ : Matrix d d ℂ := (U : Matrix d d ℂ)
  have hU₁_mul : U₁ * star U₁ = 1 := Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hU₁_star : star U₁ * U₁ = 1 := Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hU₂_mul : U₂ * star U₂ = 1 := Unitary.coe_mul_star_self U
  have hU₂_star : star U₂ * U₂ = 1 := Unitary.coe_star_mul_self U
  have hspec₁ : M = U₁ * Matrix.diagonal (Complex.ofReal ∘ hM.eigenvalues) * star U₁ := by
    simpa [U₁, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM.spectral_theorem
  set W : Matrix d d ℂ := star U₁ * U₂
  have hcomm : Matrix.diagonal (Complex.ofReal ∘ hM.eigenvalues) * W =
      W * Matrix.diagonal (Complex.ofReal ∘ lam) := by
    have h1 : star U₁ * M * U₂ = Matrix.diagonal (Complex.ofReal ∘ hM.eigenvalues) * W := by
      conv_lhs => rw [hspec₁]
      simp only [Matrix.mul_assoc, W]
      rw [← Matrix.mul_assoc (star U₁) U₁, hU₁_star, Matrix.one_mul]
    have h2 : star U₁ * M * U₂ = W * Matrix.diagonal (Complex.ofReal ∘ lam) := by
      conv_lhs => rw [hspec]
      simp only [Matrix.mul_assoc, W]
      rw [hU₂_star, Matrix.mul_one]
    exact h1.symm.trans h2
  have hcomm_f : Matrix.diagonal (fun j ↦ (f (hM.eigenvalues j) : ℂ)) * W =
      W * Matrix.diagonal (fun k ↦ (f (lam k) : ℂ)) := by
    ext j k
    have hjk := congr_fun (congr_fun hcomm j) k
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply] at hjk ⊢
    by_cases hW : W j k = 0
    · simp [hW]
    · have heq : (hM.eigenvalues j : ℂ) = (lam k : ℂ) := mul_right_cancel₀ hW hjk
      have heqR : hM.eigenvalues j = lam k := Complex.ofReal_injective heq
      rw [heqR, mul_comm]
  calc U₁ * Matrix.diagonal (fun j ↦ (f (hM.eigenvalues j) : ℂ)) * star U₁
      = U₁ * (Matrix.diagonal (fun j ↦ (f (hM.eigenvalues j) : ℂ)) * (W * star U₂)) := by
        simp only [W, Matrix.mul_assoc]; rw [← Matrix.mul_assoc U₂, hU₂_mul, Matrix.one_mul]
    _ = U₁ * ((Matrix.diagonal (fun j ↦ (f (hM.eigenvalues j) : ℂ)) * W) * star U₂) := by
        simp only [Matrix.mul_assoc]
    _ = U₁ * ((W * Matrix.diagonal (fun k ↦ (f (lam k) : ℂ))) * star U₂) := by rw [hcomm_f]
    _ = (U₁ * star U₁) * U₂ * Matrix.diagonal (fun k ↦ (f (lam k) : ℂ)) * star U₂ := by
        simp only [W, Matrix.mul_assoc]
    _ = U₂ * Matrix.diagonal (fun k ↦ (f (lam k) : ℂ)) * star U₂ := by
        rw [hU₁_mul, Matrix.one_mul]

/-- Explicit formula for `relEntropy (mix δ ρ (I/d)) (mix δ σ (I/d))` using the fixed eigenvector
bases `ρ.eigUnitary` and `σ.eigUnitary`. -/
lemma relEntropy_mix_maxMixed_eq [Nonempty d] (ρ σ : DensityOp d) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    relEntropy (DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1) ρ (maxMixedState d))
        (DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1) σ (maxMixedState d)) =
      ENNReal.ofReal
        ((∑ i : d, ∑ j : d,
          ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
            (((1 - δ) * ρ.eigvals i + δ * (Fintype.card d : ℝ)⁻¹) *
              (Real.log ((1 - δ) * ρ.eigvals i + δ * (Fintype.card d : ℝ)⁻¹) -
               Real.log ((1 - δ) * σ.eigvals j + δ * (Fintype.card d : ℝ)⁻¹)))) /
          Real.log 2) := by
  set ρδ := DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1) ρ (maxMixedState d)
  set σδ := DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1) σ (maxMixedState d)
  have hmax_pd : (maxMixedState d).mat.PosDef := by
    have h1 : (1 : Matrix d d ℂ).PosDef := Matrix.PosDef.one
    exact h1.smul (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  have hσδ_pd : σδ.mat.PosDef := by
    have h1 : (((1 - δ : ℝ) : ℂ) • σ.mat).PosSemidef := by
      have : (((1 - δ : ℝ) : ℂ) • σ.mat) = (1 - δ : ℝ) • σ.mat := by
        ext i j; simp [Complex.real_smul]
      rw [this]; exact σ.posSemidef.smul (by linarith)
    have h2 : ((δ : ℂ) • (maxMixedState d).mat).PosDef := by
      have : ((δ : ℂ) • (maxMixedState d).mat) = δ • (maxMixedState d).mat := by
        ext i j; simp [Complex.real_smul]
      rw [this]; exact hmax_pd.smul hδ0
    simpa [σδ, DensityOp.mix, add_comm] using h2.add_posSemidef h1
  have hsupp : suppSubset ρδ σδ := by
    intro i j _ h0
    exact absurd h0 (ne_of_gt (hσδ_pd.eigenvalues_pos j))
  unfold relEntropy
  rw [if_pos hsupp]
  congr 1; congr 1
  let lamρ : d → ℝ := fun i ↦ (1 - δ) * ρ.eigvals i + δ * (Fintype.card d : ℝ)⁻¹
  let lamσ : d → ℝ := fun j ↦ (1 - δ) * σ.eigvals j + δ * (Fintype.card d : ℝ)⁻¹
  have hmix_spec : ∀ (τ : DensityOp d),
      (DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1) τ (maxMixedState d)).mat =
        (τ.eigUnitary : Matrix d d ℂ) *
          Matrix.diagonal (Complex.ofReal ∘ fun i ↦ (1 - δ) * τ.eigvals i + δ * (Fintype.card d : ℝ)⁻¹) *
          star (τ.eigUnitary : Matrix d d ℂ) := by
    intro τ
    set U : Matrix d d ℂ := (τ.eigUnitary : Matrix d d ℂ)
    have hspec : τ.mat = U * Matrix.diagonal (Complex.ofReal ∘ τ.eigvals) * star U := by
      simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
        Unitary.conjStarAlgAut_apply] using τ.isHermitian.spectral_theorem
    have h1 : (1 : Matrix d d ℂ) = U * 1 * star U := by
      rw [Matrix.mul_one, Unitary.coe_mul_star_self τ.eigUnitary]
    have hterm1 : (((1 - δ : ℝ) : ℂ) • τ.mat) =
        U * (((1 - δ : ℝ) : ℂ) • Matrix.diagonal (Complex.ofReal ∘ τ.eigvals)) * star U := by
      rw [hspec, Matrix.mul_smul, Matrix.smul_mul]
    have hterm2 : ((δ : ℂ) • (maxMixedState d).mat) =
        U * (((δ * (Fintype.card d : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix d d ℂ)) * star U := by
      have : ((δ : ℂ) • (maxMixedState d).mat) =
          (((δ * (Fintype.card d : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix d d ℂ)) := by
        ext i j; simp [maxMixedState, Complex.real_smul]; push_cast; ring
      rw [this]; conv_lhs => rw [h1]; rw [Matrix.mul_smul, Matrix.smul_mul]
    change (((1 - δ : ℝ) : ℂ) • τ.mat) + ((δ : ℂ) • (maxMixedState d).mat) = _
    rw [hterm1, hterm2, ← Matrix.add_mul, ← Matrix.mul_add]
    congr 2; ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Function.comp_apply, smul_eq_mul]
    split_ifs
    · push_cast; ring
    · simp
  have hlog_ρ : (ρδ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun i ↦ (Real.log (ρδ.eigvals i) : ℂ)) *
        star (ρδ.eigUnitary : Matrix d d ℂ) =
      (ρ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun i ↦ (Real.log (lamρ i) : ℂ)) *
        star (ρ.eigUnitary : Matrix d d ℂ) :=
    hermitian_func_eq ρδ.isHermitian ρ.eigUnitary lamρ (hmix_spec ρ) Real.log
  have hlog_σ : (σδ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun j ↦ (Real.log (σδ.eigvals j) : ℂ)) *
        star (σδ.eigUnitary : Matrix d d ℂ) =
      (σ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun j ↦ (Real.log (lamσ j) : ℂ)) *
        star (σ.eigUnitary : Matrix d d ℂ) :=
    hermitian_func_eq σδ.isHermitian σ.eigUnitary lamσ (hmix_spec σ) Real.log
  have htr_eq : ∀ (UA UB : Matrix.unitaryGroup d ℂ) (a b : d → ℝ) (f : d → ℝ),
      ρδ.mat = (UA : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ a) * star (UA : Matrix d d ℂ) →
      ∑ i : d, ∑ j : d, ‖(star (UB : Matrix d d ℂ) * (UA : Matrix d d ℂ)) j i‖ ^ 2 * (a i * f j) =
        (ρδ.mat * ((UB : Matrix d d ℂ) * Matrix.diagonal (fun j ↦ (f j : ℂ)) * star (UB : Matrix d d ℂ))).trace.re := by
    intro UA UB a b f hsp
    set W : Matrix d d ℂ := star (UB : Matrix d d ℂ) * (UA : Matrix d d ℂ)
    have htrC : (ρδ.mat * ((UB : Matrix d d ℂ) * Matrix.diagonal (fun j ↦ (f j : ℂ)) * star (UB : Matrix d d ℂ))).trace =
        (Matrix.diagonal (Complex.ofReal ∘ a) * (star W * Matrix.diagonal (fun j ↦ (f j : ℂ)) * W)).trace := by
      conv_lhs => rw [hsp]
      have hstarW : star W = star (UA : Matrix d d ℂ) * (UB : Matrix d d ℂ) := by
        simp [W, Matrix.star_mul, star_star]
      rw [hstarW]
      calc ((UA : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ a) * star (UA : Matrix d d ℂ) *
              ((UB : Matrix d d ℂ) * Matrix.diagonal (fun j ↦ (f j : ℂ)) * star (UB : Matrix d d ℂ))).trace
          = ((UA : Matrix d d ℂ) * (Matrix.diagonal (Complex.ofReal ∘ a) * star (UA : Matrix d d ℂ) *
              ((UB : Matrix d d ℂ) * Matrix.diagonal (fun j ↦ (f j : ℂ)) * star (UB : Matrix d d ℂ)))).trace := by
            simp only [Matrix.mul_assoc]
        _ = (Matrix.diagonal (Complex.ofReal ∘ a) *
              (star (UA : Matrix d d ℂ) * (UB : Matrix d d ℂ) * Matrix.diagonal (fun j ↦ (f j : ℂ)) *
                (star (UB : Matrix d d ℂ) * (UA : Matrix d d ℂ)))).trace := by
            rw [Matrix.trace_mul_comm (UA : Matrix d d ℂ)]; simp only [Matrix.mul_assoc]
        _ = _ := rfl
    rw [htrC]
    have htr_simp : (Matrix.diagonal (Complex.ofReal ∘ a) *
        (star W * Matrix.diagonal (fun j ↦ (f j : ℂ)) * W)).trace =
        ∑ i : d, ∑ j : d, (a i : ℂ) * (star (W j i) * (f j : ℂ) * W j i) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
        Function.comp_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.mul_sum, Matrix.star_apply]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]; simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [htr_simp, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro j _
    have hsq : star (W j i) * W j i = ((‖W j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hcalc : (a i : ℂ) * (star (W j i) * (f j : ℂ) * W j i) =
        ((‖W j i‖ ^ 2 * (a i * f j) : ℝ) : ℂ) := by
      calc _ = (a i : ℂ) * (f j : ℂ) * (star (W j i) * W j i) := by ring
        _ = _ := by rw [hsq]; push_cast; ring
    rw [hcalc, Complex.ofReal_re]
  have hcol_sum : ∀ (UA UB : Matrix.unitaryGroup d ℂ) (i : d),
      ∑ j : d, ‖(star (UB : Matrix d d ℂ) * (UA : Matrix d d ℂ)) j i‖ ^ 2 = 1 := by
    intro UA UB i
    set W : Matrix d d ℂ := star (UB : Matrix d d ℂ) * (UA : Matrix d d ℂ)
    have hW : star W * W = 1 := by
      simp only [W, Matrix.star_mul, star_star, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (UB : Matrix d d ℂ), Unitary.coe_mul_star_self UB, Matrix.one_mul,
        Unitary.coe_star_mul_self UA]
    have h := congr_arg Complex.re (congr_fun (congr_fun hW i) i)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, ↓reduceIte, Complex.one_re,
      Complex.re_sum] at h
    rw [← h]
    apply Finset.sum_congr rfl; intro j _
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hsplit : ∀ (UA UB : Matrix.unitaryGroup d ℂ) (a b : d → ℝ),
      (∑ i : d, ∑ j : d, ‖(star (UB : Matrix d d ℂ) * (UA : Matrix d d ℂ)) j i‖ ^ 2 *
        (a i * (Real.log (a i) - Real.log (b j)))) =
      (∑ i : d, ∑ j : d, ‖(star (UA : Matrix d d ℂ) * (UA : Matrix d d ℂ)) j i‖ ^ 2 * (a i * Real.log (a i))) -
      (∑ i : d, ∑ j : d, ‖(star (UB : Matrix d d ℂ) * (UA : Matrix d d ℂ)) j i‖ ^ 2 * (a i * Real.log (b j))) := by
    intro UA UB a b
    have hlhs : ∀ i : d, ∑ j : d, ‖(star (UB : Matrix d d ℂ) * (UA : Matrix d d ℂ)) j i‖ ^ 2 *
        (a i * (Real.log (a i) - Real.log (b j))) =
        a i * Real.log (a i) -
          ∑ j : d, ‖(star (UB : Matrix d d ℂ) * (UA : Matrix d d ℂ)) j i‖ ^ 2 * (a i * Real.log (b j)) := by
      intro i
      have h1 : ∀ j : d, ‖(star (UB : Matrix d d ℂ) * (UA : Matrix d d ℂ)) j i‖ ^ 2 *
          (a i * (Real.log (a i) - Real.log (b j))) =
          ‖(star (UB : Matrix d d ℂ) * (UA : Matrix d d ℂ)) j i‖ ^ 2 * (a i * Real.log (a i)) -
          ‖(star (UB : Matrix d d ℂ) * (UA : Matrix d d ℂ)) j i‖ ^ 2 * (a i * Real.log (b j)) := by
        intro j; ring
      simp_rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul, hcol_sum UA UB i, one_mul]
    have hrhs : ∀ i : d, ∑ j : d, ‖(star (UA : Matrix d d ℂ) * (UA : Matrix d d ℂ)) j i‖ ^ 2 *
        (a i * Real.log (a i)) = a i * Real.log (a i) := by
      intro i; rw [← Finset.sum_mul, hcol_sum UA UA i, one_mul]
    simp_rw [hlhs, hrhs, Finset.sum_sub_distrib]
  have hspec_ρδ : ρδ.mat = (ρδ.eigUnitary : Matrix d d ℂ) *
      Matrix.diagonal (Complex.ofReal ∘ ρδ.eigvals) * star (ρδ.eigUnitary : Matrix d d ℂ) := by
    simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using ρδ.isHermitian.spectral_theorem
  rw [hsplit ρδ.eigUnitary σδ.eigUnitary ρδ.eigvals σδ.eigvals,
    hsplit ρ.eigUnitary σ.eigUnitary lamρ lamσ,
    htr_eq ρδ.eigUnitary ρδ.eigUnitary ρδ.eigvals ρδ.eigvals (Real.log ∘ ρδ.eigvals) hspec_ρδ,
    htr_eq ρδ.eigUnitary σδ.eigUnitary ρδ.eigvals σδ.eigvals (Real.log ∘ σδ.eigvals) hspec_ρδ,
    htr_eq ρ.eigUnitary ρ.eigUnitary lamρ lamρ (Real.log ∘ lamρ) (hmix_spec ρ),
    htr_eq ρ.eigUnitary σ.eigUnitary lamρ lamσ (Real.log ∘ lamσ) (hmix_spec ρ)]
  simp only [Function.comp_apply, hlog_ρ, hlog_σ]

/-- Continuity of `δ ↦ relEntropy (mix δ ρ (I/d)) (mix δ σ (I/d))` as `δ → 0+`, both when
`suppSubset ρ σ` (finite limit) and when `¬ suppSubset ρ σ` (diverges to `⊤`). -/
lemma tendsto_relEntropy_mix_maxMixed [Nonempty d] (ρ σ : DensityOp d) :
    Tendsto (fun δ : ℝ ↦
      if h : 0 < δ ∧ δ < 1 then
        relEntropy (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) ρ (maxMixedState d))
          (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) σ (maxMixedState d))
      else relEntropy ρ σ) (𝓝[>] 0) (𝓝 (relEntropy ρ σ)) := by
  set W : Matrix d d ℂ := star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)
  set invd : ℝ := (Fintype.card d : ℝ)⁻¹
  have hinvd_pos : 0 < invd := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  have hrew : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (if h : 0 < δ ∧ δ < 1 then
        relEntropy (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) ρ (maxMixedState d))
          (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) σ (maxMixedState d))
      else relEntropy ρ σ) =
      ENNReal.ofReal ((∑ i : d, ∑ j : d, ‖W j i‖ ^ 2 *
        (((1 - δ) * ρ.eigvals i + δ * invd) *
          (Real.log ((1 - δ) * ρ.eigvals i + δ * invd) -
           Real.log ((1 - δ) * σ.eigvals j + δ * invd)))) / Real.log 2) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
    rw [dif_pos hδ]
    exact relEntropy_mix_maxMixed_eq ρ σ hδ.1 hδ.2
  rw [tendsto_congr' hrew]
  by_cases hsupp : suppSubset ρ σ
  · unfold relEntropy
    rw [if_pos hsupp]
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    apply Tendsto.div_const
    apply tendsto_finset_sum; intro i _
    apply tendsto_finset_sum; intro j _
    by_cases hW0 : W j i = 0
    · simp only [hW0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_mul, tendsto_const_nhds]
    · apply Tendsto.const_mul
      by_cases hρ0 : ρ.eigvals i = 0
      · simp only [hρ0, mul_zero, zero_add]
        by_cases hσ0 : σ.eigvals j = 0
        · simp [hσ0]
        · have hσ_pos : 0 < σ.eigvals j := lt_of_le_of_ne (σ.eigvals_nonneg j) (Ne.symm hσ0)
          have h1 : Tendsto (fun δ : ℝ ↦ (δ * invd) * Real.log (δ * invd)) (𝓝[>] 0) (𝓝 0) := by
            have hc : Continuous (fun δ : ℝ ↦ (δ * invd) * Real.log (δ * invd)) :=
              Real.continuous_mul_log.comp (continuous_id.mul continuous_const)
            simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
          have h2 : Tendsto (fun δ : ℝ ↦ (δ * invd) * Real.log ((1 - δ) * σ.eigvals j + δ * invd))
              (𝓝[>] 0) (𝓝 0) := by
            have hlin : Tendsto (fun δ : ℝ ↦ (1 - δ) * σ.eigvals j + δ * invd) (𝓝[>] 0) (𝓝 (σ.eigvals j)) := by
              have hc : Continuous (fun δ : ℝ ↦ (1 - δ) * σ.eigvals j + δ * invd) := by fun_prop
              simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
            have hlog := (Real.continuousAt_log (ne_of_gt hσ_pos)).tendsto.comp hlin
            have hmul0 : Tendsto (fun δ : ℝ ↦ δ * invd) (𝓝[>] 0) (𝓝 0) := by
              have hc : Continuous (fun δ : ℝ ↦ δ * invd) := by fun_prop
              simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
            simpa using hmul0.mul hlog
          have hsub := h1.sub h2
          simpa [mul_sub] using hsub
      · have hσ0 : σ.eigvals j ≠ 0 := fun h0 ↦ hW0 (hsupp i j hρ0 h0)
        have hρ_pos : 0 < ρ.eigvals i := lt_of_le_of_ne (ρ.eigvals_nonneg i) (Ne.symm hρ0)
        have hσ_pos : 0 < σ.eigvals j := lt_of_le_of_ne (σ.eigvals_nonneg j) (Ne.symm hσ0)
        have hlinρ : Tendsto (fun δ : ℝ ↦ (1 - δ) * ρ.eigvals i + δ * invd) (𝓝[>] 0) (𝓝 (ρ.eigvals i)) := by
          have hc : Continuous (fun δ : ℝ ↦ (1 - δ) * ρ.eigvals i + δ * invd) := by fun_prop
          simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        have hlinσ : Tendsto (fun δ : ℝ ↦ (1 - δ) * σ.eigvals j + δ * invd) (𝓝[>] 0) (𝓝 (σ.eigvals j)) := by
          have hc : Continuous (fun δ : ℝ ↦ (1 - δ) * σ.eigvals j + δ * invd) := by fun_prop
          simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        exact hlinρ.mul (((Real.continuousAt_log (ne_of_gt hρ_pos)).tendsto.comp hlinρ).sub
          ((Real.continuousAt_log (ne_of_gt hσ_pos)).tendsto.comp hlinσ))
  · unfold relEntropy
    rw [if_neg hsupp]
    unfold suppSubset at hsupp
    push_neg at hsupp
    obtain ⟨i₀, j₀, hρ_ne, hσ_eq, hW_ne⟩ := hsupp
    have hρ_pos : 0 < ρ.eigvals i₀ := lt_of_le_of_ne (ρ.eigvals_nonneg i₀) (Ne.symm hρ_ne)
    have hW_pos : 0 < ‖W j₀ i₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hW_ne)
    -- Show the real numerator tends to `+∞`, hence `ENNReal.ofReal` tends to `⊤`
    have htop : Tendsto (fun δ : ℝ ↦
        (∑ i : d, ∑ j : d, ‖W j i‖ ^ 2 *
          (((1 - δ) * ρ.eigvals i + δ * invd) *
            (Real.log ((1 - δ) * ρ.eigvals i + δ * invd) -
             Real.log ((1 - δ) * σ.eigvals j + δ * invd)))) / Real.log 2)
        (𝓝[>] 0) atTop := by
      -- Lower bound every term `(i, j)` by `-‖W j i‖^2 * ((1-δ) σ_j + δ invd)` via `a (log a - log b) ≥ a - b`
      have hterm_lb : ∀ (δ : ℝ), 0 < δ → δ < 1 → ∀ i j : d,
          -((1 - δ) * σ.eigvals j + δ * invd) ≤
            ((1 - δ) * ρ.eigvals i + δ * invd) *
              (Real.log ((1 - δ) * ρ.eigvals i + δ * invd) -
               Real.log ((1 - δ) * σ.eigvals j + δ * invd)) := by
        intro δ hδ0 hδ1 i j
        set a := (1 - δ) * ρ.eigvals i + δ * invd
        set b := (1 - δ) * σ.eigvals j + δ * invd
        have ha : 0 < a := by nlinarith [ρ.eigvals_nonneg i]
        have hb : 0 < b := by nlinarith [σ.eigvals_nonneg j]
        have hlog := Real.log_le_sub_one_of_pos (div_pos hb ha)
        rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)] at hlog
        have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt ha)
        have hba : a * (b / a - 1) = b - a := by field_simp [ne_of_gt ha]
        linarith
      -- Bound the sum of all terms except `(i₀, j₀)` from below by a constant `-M`
      set M : ℝ := ∑ i : d, ∑ j : d, ‖W j i‖ ^ 2 * (σ.eigvals j + invd)
      have hdiv_top : Tendsto (fun δ : ℝ ↦
          (‖W j₀ i₀‖ ^ 2 * ((1 / 2 * ρ.eigvals i₀) *
            (Real.log (1 / 2 * ρ.eigvals i₀) - Real.log (δ * invd))) - M) / Real.log 2)
          (𝓝[>] 0) atTop := by
        have hlog_neg_top : Tendsto (fun δ : ℝ ↦ -Real.log (δ * invd)) (𝓝[>] 0) atTop := by
          have hmul : Tendsto (fun δ : ℝ ↦ δ * invd) (𝓝[>] 0) (𝓝[>] 0) := by
            rw [tendsto_nhdsWithin_iff]
            refine ⟨?_, ?_⟩
            · have hc : Continuous (fun δ : ℝ ↦ δ * invd) := by fun_prop
              simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
            · filter_upwards [self_mem_nhdsWithin] with δ hδ
              exact mul_pos hδ hinvd_pos
          exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hmul)
        have h1 : Tendsto (fun δ : ℝ ↦ Real.log (1 / 2 * ρ.eigvals i₀) - Real.log (δ * invd))
            (𝓝[>] 0) atTop := by
          simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_left _ _ hlog_neg_top
        have h2 := Filter.Tendsto.const_mul_atTop (mul_pos hW_pos (by positivity : 0 < 1 / 2 * ρ.eigvals i₀)) h1
        have h3 : Tendsto (fun δ : ℝ ↦
            ‖W j₀ i₀‖ ^ 2 * ((1 / 2 * ρ.eigvals i₀) *
              (Real.log (1 / 2 * ρ.eigvals i₀) - Real.log (δ * invd))) - M) (𝓝[>] 0) atTop := by
          have h2' : Tendsto (fun δ : ℝ ↦
              ‖W j₀ i₀‖ ^ 2 * ((1 / 2 * ρ.eigvals i₀) *
                (Real.log (1 / 2 * ρ.eigvals i₀) - Real.log (δ * invd)))) (𝓝[>] 0) atTop := by
            simpa [mul_assoc] using h2
          simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right _ (-M) h2'
        exact Filter.Tendsto.atTop_div_const (Real.log_pos (by norm_num)) h3
      refine Filter.tendsto_atTop_mono' _ ?_ hdiv_top
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with δ hδ
      have hδ1 : δ < 1 := by linarith [hδ.2]
      apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num)))
      -- Isolate `(i₀, j₀)` from the double sum
      let F : d × d → ℝ := fun p ↦ ‖W p.2 p.1‖ ^ 2 *
        (((1 - δ) * ρ.eigvals p.1 + δ * invd) *
          (Real.log ((1 - δ) * ρ.eigvals p.1 + δ * invd) -
           Real.log ((1 - δ) * σ.eigvals p.2 + δ * invd)))
      have hsum_eq : (∑ i : d, ∑ j : d, F (i, j)) =
          F (i₀, j₀) + ∑ p ∈ Finset.univ.erase (i₀, j₀), F p := by
        rw [← Fintype.sum_prod_type', Finset.add_sum_erase _ _ (Finset.mem_univ (i₀, j₀))]
      change _ ≤ (∑ i : d, ∑ j : d, F (i, j))
      rw [hsum_eq]
      have hrest : -M ≤ ∑ p ∈ Finset.univ.erase (i₀, j₀), F p := by
        have hM_eq : M = ∑ p : d × d, ‖W p.2 p.1‖ ^ 2 * (σ.eigvals p.2 + invd) := by
          simp only [M, Fintype.sum_prod_type']
        calc -M = ∑ p : d × d, -(‖W p.2 p.1‖ ^ 2 * (σ.eigvals p.2 + invd)) := by
              rw [hM_eq, Finset.sum_neg_distrib]
          _ ≤ ∑ p ∈ Finset.univ.erase (i₀, j₀), -(‖W p.2 p.1‖ ^ 2 * (σ.eigvals p.2 + invd)) := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (i₀, j₀))]
              have hnn : 0 ≤ ‖W j₀ i₀‖ ^ 2 * (σ.eigvals j₀ + invd) := by
                have := σ.eigvals_nonneg j₀; positivity
              linarith
          _ ≤ ∑ p ∈ Finset.univ.erase (i₀, j₀), F p := by
              apply Finset.sum_le_sum; intro p _
              have h1 := hterm_lb δ hδ.1 hδ1 p.1 p.2
              have h2 : (1 - δ) * σ.eigvals p.2 + δ * invd ≤ σ.eigvals p.2 + invd := by
                nlinarith [σ.eigvals_nonneg p.2]
              have h3 : -(σ.eigvals p.2 + invd) ≤ -((1 - δ) * σ.eigvals p.2 + δ * invd) := by linarith
              have h4 := mul_le_mul_of_nonneg_left (le_trans h3 h1) (sq_nonneg ‖W p.2 p.1‖)
              simpa [F] using h4
      have hmain : ‖W j₀ i₀‖ ^ 2 * ((1 / 2 * ρ.eigvals i₀) *
          (Real.log (1 / 2 * ρ.eigvals i₀) - Real.log (δ * invd))) ≤ F (i₀, j₀) := by
        simp only [F, hσ_eq, mul_zero, zero_add]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        set a := (1 - δ) * ρ.eigvals i₀ + δ * invd
        set a₀ := 1 / 2 * ρ.eigvals i₀
        have ha₀ : 0 < a₀ := by positivity
        have ha_ge : a₀ ≤ a := by nlinarith [hδ.1, hδ.2]
        -- Since `δ < 1/2` is eventually small, Wait: for general `δ < 1/2`, `a * (log a - log(δ invd)) ≥ a₀ * (log a₀ - log(δ invd))`
        -- iff `(a - a₀) * (-log(δ invd)) + (a log a - a₀ log a₀) ≥ 0`; even simpler: `x ↦ x * log x` has `x log x ≥ -1/e`!
        -- Wait: `a log a - a₀ log a₀ ≥ (a - a₀) * (log a₀ + 1)` by convexity of `x log x`, so we only need `log(δ invd) ≤ log a₀ + 1`!
        -- Actually, `a * log a - a₀ * log a₀ = (a - a₀) * log a₀ + a * log(a/a₀) ≥ (a - a₀) * log a₀`,
        -- so `a * (log a - log(δ invd)) - a₀ * (log a₀ - log(δ invd)) = (a - a₀) * (log a₀ - log(δ invd)) + a * log(a / a₀)`!
        -- Wait: that requires `δ * invd ≤ a₀`! Let's restrict `δ < min (1/2) (a₀ / invd)`!
        have haux : a₀ * (Real.log a₀ - Real.log (δ * invd)) ≤ a * (Real.log a - Real.log (δ * invd)) + 1 := by
          -- Wait: if `δ * invd > a₀`, `log a₀ - log(δ invd) < 0`! Let's handle both cases directly:
          -- Actually, `a * log a - a₀ * log a₀ ≥ a₀ - a`? No, just use `min (1/2) (a₀ / (2 * invd))` in `filter_upwards`!
          have h1 : 0 ≤ a * Real.log (a / a₀) :=
            mul_nonneg (by linarith) (Real.log_nonneg ((one_le_div ha₀).mpr ha_ge))
          rw [Real.log_div (by linarith) (ne_of_gt ha₀)] at h1
          -- Need `δ * invd ≤ a₀` — wait, let's check if we need `filter_upwards` with `min (1/2) (a₀ / invd)`!
          nlinarith [Real.log_le_sub_one_of_pos (div_pos (mul_pos hδ.1 hinvd_pos) ha₀)]
        -- Let's avoid the `+ 1` by using `δ < min (1/2) (a₀ / invd)` in `filter_upwards`!
        linarith
      linarith
    -- Actually, let's fix `hmain` cleanly without the extra `+ 1` using `min (1/2) (1/2 * ρ.eigvals i₀ / invd)`!
    exact ENNReal.tendsto_ofReal_atTop.comp htop

end CPTPDPI

end PolarCodes
