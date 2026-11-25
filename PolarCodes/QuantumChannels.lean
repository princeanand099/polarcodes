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
      · intro b _ hbi; simp [hbi]
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
          (∑ b₁ : d₂, star (ℳ.isom (c, e₂) b₁) * star (𝒩.isom (b₁, e₁) i)) *
          (∑ b₂ : d₂, ℳ.isom (c, e₂) b₂ * 𝒩.isom (b₂, e₁) j)
        = ∑ b₁ : d₂, ∑ b₂ : d₂, ∑ e₁ : 𝒩.env,
            star (𝒩.isom (b₁, e₁) i) * 𝒩.isom (b₂, e₁) j *
            (∑ c : d₃, ∑ e₂ : ℳ.env, star (ℳ.isom (c, e₂) b₁) * ℳ.isom (c, e₂) b₂) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          have h1 : ∀ c : d₃, ∑ e₂ : ℳ.env, ∑ e₁ : 𝒩.env, ∑ b₁ : d₂, ∑ b₂ : d₂,
              star (ℳ.isom (c, e₂) b₁) * star (𝒩.isom (b₁, e₁) i) *
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
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro e₁ _
            apply Finset.sum_congr rfl; intro e₂ _
            ring
          simp_rw [h1]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro b₁ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro b₂ _
          rw [Finset.sum_comm]
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
  unfold apply toLinearMap comp partialTrace₂Mat
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    star_sum, star_mul']
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro e₂ _
  conv_lhs => arg 2; ext e₁; arg 2; ext a₂; arg 2; ext a₁; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext e₁; arg 2; ext a₂; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext e₁; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b₂ _
  conv_lhs => arg 2; ext e₁; arg 2; ext a₂; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext e₁; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b₁ _
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
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
    · rw [mul_comm (W j k)] at hjk
      have heq : (hM.eigenvalues j : ℂ) = (lam k : ℂ) := mul_right_cancel₀ hW hjk
      have heqR : hM.eigenvalues j = lam k := Complex.ofReal_injective heq
      rw [heqR, mul_comm]
  calc U₁ * Matrix.diagonal (fun j ↦ (f (hM.eigenvalues j) : ℂ)) * star U₁
      = U₁ * (Matrix.diagonal (fun j ↦ (f (hM.eigenvalues j) : ℂ)) * (W * star U₂)) := by
        simp only [W, Matrix.mul_assoc]; rw [hU₂_mul, Matrix.mul_one]
    _ = U₁ * ((Matrix.diagonal (fun j ↦ (f (hM.eigenvalues j) : ℂ)) * W) * star U₂) := by
        simp only [Matrix.mul_assoc]
    _ = U₁ * ((W * Matrix.diagonal (fun k ↦ (f (lam k) : ℂ))) * star U₂) := by rw [hcomm_f]
    _ = (U₁ * star U₁) * U₂ * Matrix.diagonal (fun k ↦ (f (lam k) : ℂ)) * star U₂ := by
        simp only [W, Matrix.mul_assoc]
    _ = U₂ * Matrix.diagonal (fun k ↦ (f (lam k) : ℂ)) * star U₂ := by
        rw [hU₁_mul, Matrix.one_mul]

private lemma mix_maxMixed_posDef {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    (τ : DensityOp α) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1) τ (maxMixedState α)).mat.PosDef := by
  have h1 : (((1 - δ : ℝ) : ℂ) • τ.mat).PosSemidef := by
    have : (((1 - δ : ℝ) : ℂ) • τ.mat) = (1 - δ : ℝ) • τ.mat := by ext i j; simp [Complex.real_smul]
    rw [this]; exact τ.posSemidef.smul (by linarith)
  have h2 : ((δ : ℂ) • (maxMixedState α).mat).PosDef := by
    have : ((δ : ℂ) • (maxMixedState α).mat) = δ • (maxMixedState α).mat := by
      ext i j; simp [Complex.real_smul]
    rw [this]
    exact ((Matrix.PosDef.one (n := α) (R := ℂ)).smul
      (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))).smul hδ0
  change (((1 - δ : ℝ) : ℂ) • τ.mat + (δ : ℂ) • (maxMixedState α).mat).PosDef
  rw [add_comm]
  exact h2.add_posSemidef h1

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
  have hσδ_pd : σδ.mat.PosDef := mix_maxMixed_posDef σ hδ0 hδ1
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
    have hU : U * star U = 1 := Unitary.coe_mul_star_self τ.eigUnitary
    have hspec : τ.mat = U * Matrix.diagonal (Complex.ofReal ∘ τ.eigvals) * star U := by
      simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
        Unitary.conjStarAlgAut_apply] using τ.isHermitian.spectral_theorem
    have h1 : (1 : Matrix d d ℂ) = U * 1 * star U := by
      rw [Matrix.mul_one, hU]
    have hterm1 : (((1 - δ : ℝ) : ℂ) • τ.mat) =
        U * (((1 - δ : ℝ) : ℂ) • Matrix.diagonal (Complex.ofReal ∘ τ.eigvals)) * star U := by
      rw [hspec, ← Matrix.smul_mul, ← Matrix.mul_smul]
    have hterm2 : ((δ : ℂ) • (maxMixedState d).mat) =
        U * (((δ * (Fintype.card d : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix d d ℂ)) * star U := by
      have : ((δ : ℂ) • (maxMixedState d).mat) =
          (((δ * (Fintype.card d : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix d d ℂ)) := by
        ext i j; simp [maxMixedState, Complex.real_smul]; push_cast; ring
      rw [this]; conv_lhs => rw [h1]; rw [← Matrix.smul_mul, ← Matrix.mul_smul]
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
    have hUB : (UB : Matrix d d ℂ) * star (UB : Matrix d d ℂ) = 1 := Unitary.coe_mul_star_self UB
    have hUA : star (UA : Matrix d d ℂ) * (UA : Matrix d d ℂ) = 1 := Unitary.coe_star_mul_self UA
    have hW : star W * W = 1 := by
      simp only [W, Matrix.star_mul, star_star, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (UB : Matrix d d ℂ), hUB, Matrix.one_mul, hUA]
    have h := congr_arg Complex.re (congr_fun (congr_fun hW i) i)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, ↓reduceIte, Complex.one_re,
      Complex.re_sum] at h
    rw [← h]
    apply Finset.sum_congr rfl; intro j _
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hsplit : ∀ (UA UB : Matrix.unitaryGroup d ℂ) (a b : d → ℝ),
      (∑ i : d, ∑ j : d, ‖(star (UB : Matrix d d ℂ) * (UA : Matrix d d ℂ)) j i‖ ^ 2 *
        (a i * (Real.log (a i) - Real.log (b j)))) =
      (∑ i : d, ∑ j : d, ‖(star (UA : Matrix d d ℂ) * (UA : Matrix d d ℂ)) j i‖ ^ 2 * (a i * Real.log (a j))) -
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
        (a i * Real.log (a j)) = a i * Real.log (a i) := by
      intro i
      rw [Unitary.coe_star_mul_self UA]
      rw [Finset.sum_eq_single i]
      · simp [Matrix.one_apply]
      · intro j _ hji; simp [Matrix.one_apply, hji]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hlhs, hrhs, Finset.sum_sub_distrib]
  have hspec_ρδ : ρδ.mat = (ρδ.eigUnitary : Matrix d d ℂ) *
      Matrix.diagonal (Complex.ofReal ∘ ρδ.eigvals) * star (ρδ.eigUnitary : Matrix d d ℂ) := by
    simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using ρδ.isHermitian.spectral_theorem
  rw [hsplit ρδ.eigUnitary σδ.eigUnitary ρδ.eigvals σδ.eigvals,
    hsplit ρ.eigUnitary σ.eigUnitary lamρ lamσ,
    htr_eq ρδ.eigUnitary ρδ.eigUnitary ρδ.eigvals ρδ.eigvals (fun j ↦ Real.log (ρδ.eigvals j)) hspec_ρδ,
    htr_eq ρδ.eigUnitary σδ.eigUnitary ρδ.eigvals σδ.eigvals (fun j ↦ Real.log (σδ.eigvals j)) hspec_ρδ,
    htr_eq ρ.eigUnitary ρ.eigUnitary lamρ lamρ (fun j ↦ Real.log (lamρ j)) (hmix_spec ρ),
    htr_eq ρ.eigUnitary σ.eigUnitary lamρ lamσ (fun j ↦ Real.log (lamσ j)) (hmix_spec ρ)]
  rw [hlog_ρ, hlog_σ]

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
    rw [dif_pos ⟨hδ.1, hδ.2⟩]
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
    · have hW0' : (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i = 0 := hW0
      simp only [hW0, hW0', norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
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
    push Not at hsupp
    obtain ⟨i₀, j₀, hρ_ne, hσ_eq, hW_ne⟩ := hsupp
    have hρ_pos : 0 < ρ.eigvals i₀ := lt_of_le_of_ne (ρ.eigvals_nonneg i₀) (Ne.symm hρ_ne)
    have hW_pos : 0 < ‖W j₀ i₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hW_ne)
    set a₀ : ℝ := 1 / 2 * ρ.eigvals i₀
    have ha₀ : 0 < a₀ := by positivity
    have htop : Tendsto (fun δ : ℝ ↦
        (∑ i : d, ∑ j : d, ‖W j i‖ ^ 2 *
          (((1 - δ) * ρ.eigvals i + δ * invd) *
            (Real.log ((1 - δ) * ρ.eigvals i + δ * invd) -
             Real.log ((1 - δ) * σ.eigvals j + δ * invd)))) / Real.log 2)
        (𝓝[>] 0) atTop := by
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
      set M : ℝ := ∑ i : d, ∑ j : d, ‖W j i‖ ^ 2 * (σ.eigvals j + invd)
      have hdiv_top : Tendsto (fun δ : ℝ ↦
          (‖W j₀ i₀‖ ^ 2 * (a₀ * (Real.log a₀ - Real.log (δ * invd))) - M) / Real.log 2)
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
        have h1 : Tendsto (fun δ : ℝ ↦ Real.log a₀ - Real.log (δ * invd)) (𝓝[>] 0) atTop := by
          simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_left _ _ hlog_neg_top
        have h2 := Filter.Tendsto.const_mul_atTop (mul_pos hW_pos ha₀) h1
        have h3 : Tendsto (fun δ : ℝ ↦
            ‖W j₀ i₀‖ ^ 2 * (a₀ * (Real.log a₀ - Real.log (δ * invd))) - M) (𝓝[>] 0) atTop := by
          have h2' : Tendsto (fun δ : ℝ ↦
              ‖W j₀ i₀‖ ^ 2 * (a₀ * (Real.log a₀ - Real.log (δ * invd)))) (𝓝[>] 0) atTop := by
            simpa [mul_assoc] using h2
          simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right _ (-M) h2'
        exact Filter.Tendsto.atTop_div_const (Real.log_pos (by norm_num)) h3
      refine Filter.tendsto_atTop_mono' _ ?_ hdiv_top
      have hδ_cap : 0 < min (1 / 2 : ℝ) (a₀ / invd) := lt_min (by norm_num) (div_pos ha₀ hinvd_pos)
      filter_upwards [Ioo_mem_nhdsGT hδ_cap] with δ hδ
      have hδ_half : δ < 1 / 2 := lt_of_lt_of_le hδ.2 (min_le_left _ _)
      have hδ_a0 : δ * invd < a₀ := by
        have h := lt_of_lt_of_le hδ.2 (min_le_right _ _)
        exact (lt_div_iff₀ hinvd_pos).mp h
      have hδ1 : δ < 1 := by linarith
      apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num)))
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
        have hM_eq : M = ∑ p : d × d, ‖W p.2 p.1‖ ^ 2 * (σ.eigvals p.2 + invd) :=
          (Fintype.sum_prod_type' (fun i j : d ↦ ‖W j i‖ ^ 2 * (σ.eigvals j + invd))).symm
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
                nlinarith [σ.eigvals_nonneg p.2, hδ.1, hδ1, hinvd_pos]
              have h3 : -(σ.eigvals p.2 + invd) ≤ -((1 - δ) * σ.eigvals p.2 + δ * invd) := by linarith
              have h4 := mul_le_mul_of_nonneg_left (le_trans h3 h1) (sq_nonneg ‖W p.2 p.1‖)
              dsimp only [F]
              linarith
      have hmain : ‖W j₀ i₀‖ ^ 2 * (a₀ * (Real.log a₀ - Real.log (δ * invd))) ≤ F (i₀, j₀) := by
        simp only [F, hσ_eq, mul_zero, zero_add]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        set a := (1 - δ) * ρ.eigvals i₀ + δ * invd
        have ha_ge : a₀ ≤ a := by dsimp only [a, a₀]; nlinarith [hδ.1, hδ_half, hρ_pos, hinvd_pos]
        have hlog_ge : Real.log (δ * invd) ≤ Real.log a₀ :=
          Real.log_le_log (mul_pos hδ.1 hinvd_pos) (le_of_lt hδ_a0)
        have hlog_a : Real.log a₀ ≤ Real.log a := Real.log_le_log ha₀ ha_ge
        nlinarith
      linarith
    exact ENNReal.tendsto_ofReal_atTop.comp htop

/-- Lipschitz bound on `negPartTrace` under entrywise L1 matrix perturbation. -/
lemma negPartTrace_sub_le {A B : Matrix d d ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    negPartTrace hA ≤ negPartTrace hB + (Fintype.card d : ℝ) * (∑ i : d, ∑ j : d, ‖A i j - B i j‖) := by
  set C : ℝ := ∑ i : d, ∑ j : d, ‖A i j - B i j‖
  have hC_nn : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  have hdom : ((C : ℂ) • (1 : Matrix d d ℂ) - (B - A)).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · have h1 : ((C : ℂ) • (1 : Matrix d d ℂ)).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          Complex.star_def, Complex.conj_ofReal]
      exact h1.sub (hB.sub hA)
    · intro x
      set M : Matrix d d ℂ := (C : ℂ) • (1 : Matrix d d ℂ) - (B - A)
      have hH : M.IsHermitian := by
        have h1 : ((C : ℂ) • (1 : Matrix d d ℂ)).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
            Complex.star_def, Complex.conj_ofReal]
        exact h1.sub (hB.sub hA)
      have him : (star x ⬝ᵥ M.mulVec x).im = 0 := by
        have hconj : star (star x ⬝ᵥ M.mulVec x) = star x ⬝ᵥ M.mulVec x := by
          calc star (star x ⬝ᵥ M *ᵥ x)
              = star (M *ᵥ x) ⬝ᵥ x := by simp [dotProduct, star_sum, star_mul', mul_comm]
            _ = (star x ᵥ* Mᴴ) ⬝ᵥ x := by rw [Matrix.star_mulVec]
            _ = (star x ᵥ* M) ⬝ᵥ x := by rw [hH.eq]
            _ = star x ⬝ᵥ M *ᵥ x := (Matrix.dotProduct_mulVec (star x) M x).symm
        have h := congr_arg Complex.im hconj
        simp only [Complex.star_def, Complex.conj_im] at h
        linarith
      rw [Complex.le_def]
      refine ⟨?_, by exact him.symm⟩
      simp only [Complex.zero_re]
      have hsplit : star x ⬝ᵥ M.mulVec x =
          (C : ℂ) * (star x ⬝ᵥ x) - star x ⬝ᵥ ((B - A).mulVec x) := by
        simp only [M]
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
          dotProduct_smul, smul_eq_mul]
      rw [hsplit, Complex.sub_re, Complex.re_ofReal_mul]
      have hxx : (star x ⬝ᵥ x).re = ∑ k : d, ‖x k‖ ^ 2 := by
        simp only [dotProduct, Pi.star_apply, Complex.re_sum]
        apply Finset.sum_congr rfl; intro k _
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      rw [hxx]
      have hq : (star x ⬝ᵥ ((B - A).mulVec x)).re ≤ C * ∑ k : d, ‖x k‖ ^ 2 := by
        calc (star x ⬝ᵥ ((B - A).mulVec x)).re
            ≤ ‖star x ⬝ᵥ ((B - A).mulVec x)‖ := Complex.re_le_norm _
          _ ≤ ∑ i : d, ∑ j : d, ‖A i j - B i j‖ * (‖x i‖ * ‖x j‖) := by
              simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.sub_apply, Finset.mul_sum]
              calc ‖∑ i : d, ∑ j : d, star (x i) * ((B i j - A i j) * x j)‖
                  ≤ ∑ i : d, ‖∑ j : d, star (x i) * ((B i j - A i j) * x j)‖ := norm_sum_le _ _
                _ ≤ ∑ i : d, ∑ j : d, ‖star (x i) * ((B i j - A i j) * x j)‖ :=
                    Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _
                _ = ∑ i : d, ∑ j : d, ‖A i j - B i j‖ * (‖x i‖ * ‖x j‖) := by
                    apply Finset.sum_congr rfl; intro i _
                    apply Finset.sum_congr rfl; intro j _
                    rw [norm_mul, norm_mul, norm_star, norm_sub_rev]; ring
          _ ≤ ∑ i : d, ∑ j : d, ‖A i j - B i j‖ * (∑ k : d, ‖x k‖ ^ 2) := by
              apply Finset.sum_le_sum; intro i _
              apply Finset.sum_le_sum; intro j _
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
              have hab : ‖x i‖ * ‖x j‖ ≤ (‖x i‖ ^ 2 + ‖x j‖ ^ 2) / 2 := by
                nlinarith [sq_nonneg (‖x i‖ - ‖x j‖)]
              have hi : ‖x i‖ ^ 2 ≤ ∑ k : d, ‖x k‖ ^ 2 :=
                Finset.single_le_sum (f := fun k : d ↦ ‖x k‖ ^ 2) (fun k _ ↦ sq_nonneg _) (Finset.mem_univ i)
              have hj : ‖x j‖ ^ 2 ≤ ∑ k : d, ‖x k‖ ^ 2 :=
                Finset.single_le_sum (f := fun k : d ↦ ‖x k‖ ^ 2) (fun k _ ↦ sq_nonneg _) (Finset.mem_univ j)
              linarith
          _ = C * ∑ k : d, ‖x k‖ ^ 2 := by simp_rw [← Finset.sum_mul]; rfl
      linarith
  rw [negPartTrace_eq_posPartTrace_neg hA]
  have hB_psd : (negPartMat hB + (C : ℂ) • (1 : Matrix d d ℂ)).PosSemidef := by
    refine (negPartMat_posSemidef hB).add ?_
    have : ((C : ℂ) • (1 : Matrix d d ℂ)) = C • (1 : Matrix d d ℂ) := by
      ext i j; simp [Complex.real_smul]
    rw [this]; exact Matrix.PosSemidef.one.smul hC_nn
  have hBA_psd : (negPartMat hB + (C : ℂ) • (1 : Matrix d d ℂ) - (-A)).PosSemidef := by
    have heq : negPartMat hB + (C : ℂ) • (1 : Matrix d d ℂ) - (-A) =
        posPartMat hB + ((C : ℂ) • (1 : Matrix d d ℂ) - (B - A)) := by
      have hsub := posPartMat_sub_negPartMat hB
      calc negPartMat hB + (C : ℂ) • (1 : Matrix d d ℂ) - (-A)
          = (negPartMat hB + B) + ((C : ℂ) • (1 : Matrix d d ℂ) - (B - A)) := by abel
        _ = (negPartMat hB + (posPartMat hB - negPartMat hB)) +
            ((C : ℂ) • (1 : Matrix d d ℂ) - (B - A)) := by rw [hsub]
        _ = posPartMat hB + ((C : ℂ) • (1 : Matrix d d ℂ) - (B - A)) := by abel
    rw [heq]
    exact (posPartMat_posSemidef hB).add hdom
  have hle := posPartTrace_le_trace_of_le hA.neg hB_psd hBA_psd
  have htr : (negPartMat hB + (C : ℂ) • (1 : Matrix d d ℂ)).trace.re =
      negPartTrace hB + (Fintype.card d : ℝ) * C := by
    rw [Matrix.trace_add, trace_negPartMat, Matrix.trace_smul, Matrix.trace_one,
      smul_eq_mul, Complex.add_re, Complex.ofReal_re, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]
  linarith

/-- **General CPTP Data Processing Inequality (Umegaki Relative Entropy)**:
For every finite-dimensional CPTP map `𝒩 : B(ℂ^{d₁}) → B(ℂ^{d₂})` and all density operators
`ρ, σ ∈ D(ℂ^{d₁})`, `D(𝒩(ρ) ‖ 𝒩(σ)) ≤ D(ρ ‖ σ)`. -/
theorem relEntropy_cptp_le (𝒩 : CPTPMap d₁ d₂) (ρ σ : DensityOp d₁) :
    relEntropy (𝒩.apply ρ) (𝒩.apply σ) ≤ relEntropy ρ σ := by
  haveI : Nonempty d₁ := by
    by_contra h0; haveI : IsEmpty d₁ := not_nonempty_iff.mp h0
    have htr := ρ.trace_one; simp [Matrix.trace] at htr
  haveI : Nonempty d₂ := by
    by_contra h0; haveI : IsEmpty d₂ := not_nonempty_iff.mp h0
    have htr := (𝒩.apply ρ).trace_one; simp [Matrix.trace] at htr
  -- Step 1: For fixed `δ ∈ (0, 1)`, show `D(𝒩_δ(ρ) ‖ 𝒩_δ(σ)) ≤ D(ρ ‖ σ)`
  have hstep_δ : ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1),
      relEntropy (DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1) (𝒩.apply ρ) (maxMixedState d₂))
        (DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1) (𝒩.apply σ) (maxMixedState d₂)) ≤
      relEntropy ρ σ := by
    intro δ hδ0 hδ1
    let ℰδ : Matrix d₁ d₁ ℂ →ₗ[ℂ] Matrix d₂ d₂ ℂ :=
      ((1 - δ : ℝ) : ℂ) • 𝒩.toLinearMap +
      ((δ : ℝ) : ℂ) • ((Matrix.traceLinearMap d₁ ℂ ℂ).smulRight (maxMixedState d₂).mat)
    have hℰδ_pos : ∀ X : Matrix d₁ d₁ ℂ, X.PosSemidef → (ℰδ X).PosSemidef := by
      intro X hX
      have h1 : (((1 - δ : ℝ) : ℂ) • 𝒩.toLinearMap X).PosSemidef := by
        have : (((1 - δ : ℝ) : ℂ) • 𝒩.toLinearMap X) = (1 - δ : ℝ) • 𝒩.toLinearMap X := by
          ext i j; simp [Complex.real_smul]
        rw [this]; exact (𝒩.toLinearMap_posSemidef hX).smul (by linarith)
      have htrX : 0 ≤ X.trace.re ∧ X.trace.im = 0 := by
        set U : Matrix d₁ d₁ ℂ := (hX.isHermitian.eigenvectorUnitary : Matrix d₁ d₁ ℂ)
        have hspec : X = U * Matrix.diagonal (Complex.ofReal ∘ hX.isHermitian.eigenvalues) * star U := by
          simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hX.isHermitian.spectral_theorem
        have htr : X.trace = ∑ i : d₁, (hX.isHermitian.eigenvalues i : ℂ) := by
          conv_lhs => rw [hspec]
          rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self hX.isHermitian.eigenvectorUnitary,
            Matrix.one_mul, Matrix.trace_diagonal]; rfl
        rw [htr, Complex.re_sum, Complex.im_sum]
        exact ⟨Finset.sum_nonneg fun i _ ↦ by simpa using hX.eigenvalues_nonneg i, by simp⟩
      have h2 : (((δ : ℝ) : ℂ) • (X.trace • (maxMixedState d₂).mat)).PosSemidef := by
        have htrC : X.trace = (X.trace.re : ℂ) := Complex.ext rfl (by simp [htrX.2])
        have : (((δ : ℝ) : ℂ) • (X.trace • (maxMixedState d₂).mat)) =
            (δ * X.trace.re) • (maxMixedState d₂).mat := by
          ext i j; rw [htrC]; simp [Complex.real_smul]; push_cast; ring
        rw [this]; exact (maxMixedState d₂).posSemidef.smul (mul_nonneg (le_of_lt hδ0) htrX.1)
      exact h1.add h2
    have hℰδ_tr : ∀ X : Matrix d₁ d₁ ℂ, (ℰδ X).trace = X.trace := by
      intro X
      simp only [ℰδ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
        Matrix.traceLinearMap_apply, Matrix.trace_add, Matrix.trace_smul, 𝒩.toLinearMap_trace,
        (maxMixedState d₂).trace_one, smul_eq_mul, mul_one]
      push_cast; ring
    have hdpi_ε : ∀ (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1),
        relEntropy
          (DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1)
            (𝒩.apply (DensityOp.mix ε (le_of_lt hε0) (le_of_lt hε1) ρ (maxMixedState d₁))) (maxMixedState d₂))
          (DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1)
            (𝒩.apply (DensityOp.mix ε (le_of_lt hε0) (le_of_lt hε1) σ (maxMixedState d₁))) (maxMixedState d₂)) ≤
        relEntropy
          (DensityOp.mix ε (le_of_lt hε0) (le_of_lt hε1) ρ (maxMixedState d₁))
          (DensityOp.mix ε (le_of_lt hε0) (le_of_lt hε1) σ (maxMixedState d₁)) := by
      intro ε hε0 hε1
      set ρ' := DensityOp.mix ε (le_of_lt hε0) (le_of_lt hε1) ρ (maxMixedState d₁)
      set σ' := DensityOp.mix ε (le_of_lt hε0) (le_of_lt hε1) σ (maxMixedState d₁)
      set A' := DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1) (𝒩.apply ρ') (maxMixedState d₂)
      set B' := DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1) (𝒩.apply σ') (maxMixedState d₂)
      have hlog2_pos : 0 < ENNReal.ofReal (Real.log 2) := ENNReal.ofReal_pos.mpr (Real.log_pos (by norm_num))
      refine (ENNReal.mul_le_mul_iff_left (ne_of_gt hlog2_pos) ENNReal.ofReal_ne_top).mp ?_
      rw [relEntropy_frenkel_integral (mix_maxMixed_posDef (𝒩.apply ρ') hδ0 hδ1) (mix_maxMixed_posDef (𝒩.apply σ') hδ0 hδ1),
          relEntropy_frenkel_integral (mix_maxMixed_posDef ρ hε0 hε1) (mix_maxMixed_posDef σ hε0 hε1)]
      apply MeasureTheory.lintegral_mono; intro t
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ (mul_nonneg (abs_nonneg t) (sq_nonneg _))
      have hlin : ((1 - t : ℝ) : ℂ) • A'.mat + (t : ℂ) • B'.mat =
          ℰδ (((1 - t : ℝ) : ℂ) • ρ'.mat + (t : ℂ) • σ'.mat) := by
        rw [map_add, map_smul, map_smul]
        have hA' : ℰδ ρ'.mat = A'.mat := by
          ext i j; simp [ℰδ, A', DensityOp.mix, CPTPMap.apply, ρ'.trace_one, Complex.real_smul]
        have hB' : ℰδ σ'.mat = B'.mat := by
          ext i j; simp [ℰδ, B', DensityOp.mix, CPTPMap.apply, σ'.trace_one, Complex.real_smul]
        rw [hA', hB']
      have hA_herm : (((1 - t : ℝ) : ℂ) • ρ'.mat + (t : ℂ) • σ'.mat).IsHermitian := by
        have h1 : (((1 - t : ℝ) : ℂ) • ρ'.mat).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, ρ'.isHermitian.eq]
        have h2 : ((t : ℂ) • σ'.mat).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, σ'.isHermitian.eq]
        exact h1.add h2
      have hB_herm : (((1 - t : ℝ) : ℂ) • A'.mat + (t : ℂ) • B'.mat).IsHermitian := by
        have h1 : (((1 - t : ℝ) : ℂ) • A'.mat).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, A'.isHermitian.eq]
        have h2 : ((t : ℂ) • B'.mat).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, B'.isHermitian.eq]
        exact h1.add h2
      have hB'_herm : (ℰδ (((1 - t : ℝ) : ℂ) • ρ'.mat + (t : ℂ) • σ'.mat)).IsHermitian := hlin ▸ hB_herm
      rw [negPartTrace_eq_of_eq hB_herm hB'_herm hlin]
      exact negPartTrace_map_le ℰδ hℰδ_pos (fun X _ ↦ by rw [hℰδ_tr]) hA_herm hB'_herm
    let ε : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 2)
    have hε_pos : ∀ k : ℕ, 0 < ε k := fun k ↦ by positivity
    have hε_lt1 : ∀ k : ℕ, ε k < 1 := fun k ↦ by
      simp only [ε]; rw [div_lt_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hε_tendsto : Tendsto ε atTop (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall hε_pos⟩
      have h1 : Tendsto (fun k : ℕ ↦ (k : ℝ) + 2) atTop atTop :=
        Filter.tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
      simpa [ε, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp h1
    set A0 := DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1) (𝒩.apply ρ) (maxMixedState d₂)
    set B0 := DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1) (𝒩.apply σ) (maxMixedState d₂)
    let Ak : ℕ → DensityOp d₂ := fun k ↦
      DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1)
        (𝒩.apply (DensityOp.mix (ε k) (le_of_lt (hε_pos k)) (le_of_lt (hε_lt1 k)) ρ (maxMixedState d₁)))
        (maxMixedState d₂)
    let Bk : ℕ → DensityOp d₂ := fun k ↦
      DensityOp.mix δ (le_of_lt hδ0) (le_of_lt hδ1)
        (𝒩.apply (DensityOp.mix (ε k) (le_of_lt (hε_pos k)) (le_of_lt (hε_lt1 k)) σ (maxMixedState d₁)))
        (maxMixedState d₂)
    have hlog2_pos : 0 < ENNReal.ofReal (Real.log 2) := ENNReal.ofReal_pos.mpr (Real.log_pos (by norm_num))
    refine (ENNReal.mul_le_mul_iff_left (ne_of_gt hlog2_pos) ENNReal.ofReal_ne_top).mp ?_
    rw [relEntropy_frenkel_integral (mix_maxMixed_posDef (𝒩.apply ρ) hδ0 hδ1) (mix_maxMixed_posDef (𝒩.apply σ) hδ0 hδ1)]
    let fk : ℕ → ℝ → ℝ≥0∞ := fun k t ↦
      ENNReal.ofReal (negPartTrace (show (((1 - t : ℝ) : ℂ) • (Ak k).mat + (t : ℂ) • (Bk k).mat).IsHermitian by
        have h1 : (((1 - t : ℝ) : ℂ) • (Ak k).mat).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Ak k).isHermitian.eq]
        have h2 : ((t : ℂ) • (Bk k).mat).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Bk k).isHermitian.eq]
        exact h1.add h2) / (|t| * (t - 1) ^ 2))
    let f0 : ℝ → ℝ≥0∞ := fun t ↦
      ENNReal.ofReal (negPartTrace (show (((1 - t : ℝ) : ℂ) • A0.mat + (t : ℂ) • B0.mat).IsHermitian by
        have h1 : (((1 - t : ℝ) : ℂ) • A0.mat).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, A0.isHermitian.eq]
        have h2 : ((t : ℂ) • B0.mat).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, B0.isHermitian.eq]
        exact h1.add h2) / (|t| * (t - 1) ^ 2))
    have hfk_meas : ∀ k : ℕ, Measurable (fk k) := by
      intro k
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.div _ (show Continuous fun t : ℝ ↦ |t| * (t - 1) ^ 2 by fun_prop).measurable
      have hcont : Continuous (fun t : ℝ ↦
          negPartTrace (show (((1 - t : ℝ) : ℂ) • (Ak k).mat + (t : ℂ) • (Bk k).mat).IsHermitian by
            have h1 : (((1 - t : ℝ) : ℂ) • (Ak k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Ak k).isHermitian.eq]
            have h2 : ((t : ℂ) • (Bk k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Bk k).isHermitian.eq]
            exact h1.add h2)) := by
        rw [Metric.continuous_iff]
        intro t₀ η hη
        set C0 : ℝ := (Fintype.card d₂ : ℝ) * (∑ i : d₂, ∑ j : d₂, ‖(Bk k).mat i j - (Ak k).mat i j‖) + 1
        have hC0 : 0 < C0 := by
          have : 0 ≤ ∑ i : d₂, ∑ j : d₂, ‖(Bk k).mat i j - (Ak k).mat i j‖ :=
            Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg _
          positivity
        refine ⟨η / C0, div_pos hη hC0, fun t ht ↦ ?_⟩
        rw [Real.dist_eq] at ht ⊢
        have hdiff_sum : ∀ s₁ s₂ : ℝ,
            (∑ i : d₂, ∑ j : d₂, ‖(((1 - s₁ : ℝ) : ℂ) • (Ak k).mat + (s₁ : ℂ) • (Bk k).mat) i j -
              (((1 - s₂ : ℝ) : ℂ) • (Ak k).mat + (s₂ : ℂ) • (Bk k).mat) i j‖) =
            |s₁ - s₂| * (∑ i : d₂, ∑ j : d₂, ‖(Bk k).mat i j - (Ak k).mat i j‖) := by
          intro s₁ s₂
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
          have heq : (((1 - s₁ : ℝ) : ℂ) • (Ak k).mat + (s₁ : ℂ) • (Bk k).mat) i j -
              (((1 - s₂ : ℝ) : ℂ) • (Ak k).mat + (s₂ : ℂ) • (Bk k).mat) i j =
              ((s₁ - s₂ : ℝ) : ℂ) * ((Bk k).mat i j - (Ak k).mat i j) := by
            simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]; push_cast; ring
          rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h1 := negPartTrace_sub_le
          (show (((1 - t : ℝ) : ℂ) • (Ak k).mat + (t : ℂ) • (Bk k).mat).IsHermitian by
            have h1 : (((1 - t : ℝ) : ℂ) • (Ak k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Ak k).isHermitian.eq]
            have h2 : ((t : ℂ) • (Bk k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Bk k).isHermitian.eq]
            exact h1.add h2)
          (show (((1 - t₀ : ℝ) : ℂ) • (Ak k).mat + (t₀ : ℂ) • (Bk k).mat).IsHermitian by
            have h1 : (((1 - t₀ : ℝ) : ℂ) • (Ak k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Ak k).isHermitian.eq]
            have h2 : ((t₀ : ℂ) • (Bk k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Bk k).isHermitian.eq]
            exact h1.add h2)
        have h2 := negPartTrace_sub_le
          (show (((1 - t₀ : ℝ) : ℂ) • (Ak k).mat + (t₀ : ℂ) • (Bk k).mat).IsHermitian by
            have h1 : (((1 - t₀ : ℝ) : ℂ) • (Ak k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Ak k).isHermitian.eq]
            have h2 : ((t₀ : ℂ) • (Bk k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Bk k).isHermitian.eq]
            exact h1.add h2)
          (show (((1 - t : ℝ) : ℂ) • (Ak k).mat + (t : ℂ) • (Bk k).mat).IsHermitian by
            have h1 : (((1 - t : ℝ) : ℂ) • (Ak k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Ak k).isHermitian.eq]
            have h2 : ((t : ℂ) • (Bk k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Bk k).isHermitian.eq]
            exact h1.add h2)
        rw [hdiff_sum t t₀] at h1
        rw [hdiff_sum t₀ t, abs_sub_comm] at h2
        have hsum_nn : 0 ≤ ∑ i : d₂, ∑ j : d₂, ‖(Bk k).mat i j - (Ak k).mat i j‖ :=
          Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg _
        have hbd : (Fintype.card d₂ : ℝ) * (|t - t₀| * ∑ i : d₂, ∑ j : d₂, ‖(Bk k).mat i j - (Ak k).mat i j‖) < η := by
          have hle1 : (Fintype.card d₂ : ℝ) * (∑ i : d₂, ∑ j : d₂, ‖(Bk k).mat i j - (Ak k).mat i j‖) < C0 := by
            simp only [C0]; linarith
          calc (Fintype.card d₂ : ℝ) * (|t - t₀| * ∑ i : d₂, ∑ j : d₂, ‖(Bk k).mat i j - (Ak k).mat i j‖)
              = |t - t₀| * ((Fintype.card d₂ : ℝ) * ∑ i : d₂, ∑ j : d₂, ‖(Bk k).mat i j - (Ak k).mat i j‖) := by ring
            _ ≤ |t - t₀| * C0 := mul_le_mul_of_nonneg_left (le_of_lt hle1) (abs_nonneg _)
            _ < (η / C0) * C0 := mul_lt_mul_of_pos_right ht hC0
            _ = η := div_mul_cancel₀ η (ne_of_gt hC0)
        rw [abs_lt]; constructor <;> linarith
      exact hcont.measurable
    have hpt : ∀ t : ℝ, f0 t ≤ liminf (fun k ↦ fk k t) atTop := by
      intro t
      have htend : Tendsto (fun k ↦ fk k t) atTop (𝓝 (f0 t)) := by
        apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        apply Tendsto.div_const
        rw [Metric.tendsto_atTop]
        intro η hη
        set M1 : ℝ := ∑ i : d₂, ∑ j : d₂, ‖(𝒩.apply (maxMixedState d₁)).mat i j - (𝒩.apply ρ).mat i j‖
        set M2 : ℝ := ∑ i : d₂, ∑ j : d₂, ‖(𝒩.apply (maxMixedState d₁)).mat i j - (𝒩.apply σ).mat i j‖
        set C1 : ℝ := (Fintype.card d₂ : ℝ) * ((1 - δ) * (|1 - t| * M1 + |t| * M2)) + 1
        have hM1 : 0 ≤ M1 := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg _
        have hM2 : 0 ≤ M2 := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg _
        have hC1 : 0 < C1 := by positivity
        obtain ⟨N, hN⟩ := exists_nat_gt (C1 / η)
        refine ⟨N, fun k hk ↦ ?_⟩
        have hε_small : ε k * C1 < η := by
          have hk' : C1 / η < (k : ℝ) + 2 := by
            have : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
            linarith
          simp only [ε]
          rw [one_div, inv_mul_lt_iff₀ (by positivity)]
          exact (div_lt_iff₀ hη).mp hk' |> fun h ↦ by linarith
        have hmat_diff : ∀ i j : d₂,
            (((1 - t : ℝ) : ℂ) • (Ak k).mat + (t : ℂ) • (Bk k).mat) i j -
              (((1 - t : ℝ) : ℂ) • A0.mat + (t : ℂ) • B0.mat) i j =
            ((1 - δ : ℝ) : ℂ) * ((ε k : ℝ) : ℂ) *
              (((1 - t : ℝ) : ℂ) * ((𝒩.apply (maxMixedState d₁)).mat i j - (𝒩.apply ρ).mat i j) +
               (t : ℂ) * ((𝒩.apply (maxMixedState d₁)).mat i j - (𝒩.apply σ).mat i j)) := by
          intro i j
          have hlin_ρ : (𝒩.apply (DensityOp.mix (ε k) (le_of_lt (hε_pos k)) (le_of_lt (hε_lt1 k)) ρ (maxMixedState d₁))).mat =
              ((1 - ε k : ℝ) : ℂ) • (𝒩.apply ρ).mat + ((ε k : ℝ) : ℂ) • (𝒩.apply (maxMixedState d₁)).mat := by
            show 𝒩.toLinearMap (((1 - ε k : ℝ) : ℂ) • ρ.mat + ((ε k : ℝ) : ℂ) • (maxMixedState d₁).mat) = _
            rw [map_add, map_smul, map_smul]; rfl
          have hlin_σ : (𝒩.apply (DensityOp.mix (ε k) (le_of_lt (hε_pos k)) (le_of_lt (hε_lt1 k)) σ (maxMixedState d₁))).mat =
              ((1 - ε k : ℝ) : ℂ) • (𝒩.apply σ).mat + ((ε k : ℝ) : ℂ) • (𝒩.apply (maxMixedState d₁)).mat := by
            show 𝒩.toLinearMap (((1 - ε k : ℝ) : ℂ) • σ.mat + ((ε k : ℝ) : ℂ) • (maxMixedState d₁).mat) = _
            rw [map_add, map_smul, map_smul]; rfl
          have hAk : (Ak k).mat = ((1 - δ : ℝ) : ℂ) • (((1 - ε k : ℝ) : ℂ) • (𝒩.apply ρ).mat +
              ((ε k : ℝ) : ℂ) • (𝒩.apply (maxMixedState d₁)).mat) + ((δ : ℝ) : ℂ) • (maxMixedState d₂).mat := by
            change ((1 - δ : ℝ) : ℂ) • (𝒩.apply (DensityOp.mix (ε k) _ _ ρ (maxMixedState d₁))).mat + _ = _
            rw [hlin_ρ]; ext r s; simp [Complex.real_smul]
          have hBk : (Bk k).mat = ((1 - δ : ℝ) : ℂ) • (((1 - ε k : ℝ) : ℂ) • (𝒩.apply σ).mat +
              ((ε k : ℝ) : ℂ) • (𝒩.apply (maxMixedState d₁)).mat) + ((δ : ℝ) : ℂ) • (maxMixedState d₂).mat := by
            change ((1 - δ : ℝ) : ℂ) • (𝒩.apply (DensityOp.mix (ε k) _ _ σ (maxMixedState d₁))).mat + _ = _
            rw [hlin_σ]; ext r s; simp [Complex.real_smul]
          rw [hAk, hBk]
          simp only [A0, B0, DensityOp.mix, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
          push_cast; ring
        have hsum_le : (∑ i : d₂, ∑ j : d₂,
            ‖(((1 - t : ℝ) : ℂ) • (Ak k).mat + (t : ℂ) • (Bk k).mat) i j -
              (((1 - t : ℝ) : ℂ) • A0.mat + (t : ℂ) • B0.mat) i j‖) ≤
            ε k * ((1 - δ) * (|1 - t| * M1 + |t| * M2)) := by
          calc _ = ∑ i : d₂, ∑ j : d₂, (1 - δ) * ε k *
                ‖((1 - t : ℝ) : ℂ) * ((𝒩.apply (maxMixedState d₁)).mat i j - (𝒩.apply ρ).mat i j) +
                 (t : ℂ) * ((𝒩.apply (maxMixedState d₁)).mat i j - (𝒩.apply σ).mat i j)‖ := by
                apply Finset.sum_congr rfl; intro i _
                apply Finset.sum_congr rfl; intro j _
                rw [hmat_diff i j, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
                  Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_pos (hε_pos k)]
            _ ≤ ∑ i : d₂, ∑ j : d₂, (1 - δ) * ε k *
                (|1 - t| * ‖(𝒩.apply (maxMixedState d₁)).mat i j - (𝒩.apply ρ).mat i j‖ +
                 |t| * ‖(𝒩.apply (maxMixedState d₁)).mat i j - (𝒩.apply σ).mat i j‖) := by
                apply Finset.sum_le_sum; intro i _
                apply Finset.sum_le_sum; intro j _
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) (le_of_lt (hε_pos k)))
                refine le_trans (norm_add_le _ _) ?_
                rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
            _ = ε k * ((1 - δ) * (|1 - t| * M1 + |t| * M2)) := by
                simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
                ring
        have h1 := negPartTrace_sub_le
          (show (((1 - t : ℝ) : ℂ) • (Ak k).mat + (t : ℂ) • (Bk k).mat).IsHermitian by
            have h1 : (((1 - t : ℝ) : ℂ) • (Ak k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Ak k).isHermitian.eq]
            have h2 : ((t : ℂ) • (Bk k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Bk k).isHermitian.eq]
            exact h1.add h2)
          (show (((1 - t : ℝ) : ℂ) • A0.mat + (t : ℂ) • B0.mat).IsHermitian by
            have h1 : (((1 - t : ℝ) : ℂ) • A0.mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, A0.isHermitian.eq]
            have h2 : ((t : ℂ) • B0.mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, B0.isHermitian.eq]
            exact h1.add h2)
        have h2 := negPartTrace_sub_le
          (show (((1 - t : ℝ) : ℂ) • A0.mat + (t : ℂ) • B0.mat).IsHermitian by
            have h1 : (((1 - t : ℝ) : ℂ) • A0.mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, A0.isHermitian.eq]
            have h2 : ((t : ℂ) • B0.mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, B0.isHermitian.eq]
            exact h1.add h2)
          (show (((1 - t : ℝ) : ℂ) • (Ak k).mat + (t : ℂ) • (Bk k).mat).IsHermitian by
            have h1 : (((1 - t : ℝ) : ℂ) • (Ak k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Ak k).isHermitian.eq]
            have h2 : ((t : ℂ) • (Bk k).mat).IsHermitian := by
              rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, (Bk k).isHermitian.eq]
            exact h1.add h2)
        have hsum_symm : (∑ i : d₂, ∑ j : d₂,
            ‖(((1 - t : ℝ) : ℂ) • A0.mat + (t : ℂ) • B0.mat) i j -
              (((1 - t : ℝ) : ℂ) • (Ak k).mat + (t : ℂ) • (Bk k).mat) i j‖) =
            (∑ i : d₂, ∑ j : d₂,
            ‖(((1 - t : ℝ) : ℂ) • (Ak k).mat + (t : ℂ) • (Bk k).mat) i j -
              (((1 - t : ℝ) : ℂ) • A0.mat + (t : ℂ) • B0.mat) i j‖) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          exact norm_sub_rev _ _
        rw [hsum_symm] at h2
        have hbd : (Fintype.card d₂ : ℝ) * (ε k * ((1 - δ) * (|1 - t| * M1 + |t| * M2))) < η := by
          have hle1 : (Fintype.card d₂ : ℝ) * ((1 - δ) * (|1 - t| * M1 + |t| * M2)) < C1 := by
            simp only [C1]; linarith
          calc (Fintype.card d₂ : ℝ) * (ε k * ((1 - δ) * (|1 - t| * M1 + |t| * M2)))
              = ε k * ((Fintype.card d₂ : ℝ) * ((1 - δ) * (|1 - t| * M1 + |t| * M2))) := by ring
            _ ≤ ε k * C1 := mul_le_mul_of_nonneg_left (le_of_lt hle1) (le_of_lt (hε_pos k))
            _ < η := hε_small
        have hmul_le := mul_le_mul_of_nonneg_left hsum_le (Nat.cast_nonneg (α := ℝ) (Fintype.card d₂))
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith
      rw [htend.liminf_eq]
    calc ∫⁻ t, f0 t ∂volume
        ≤ ∫⁻ t, liminf (fun k ↦ fk k t) atTop ∂volume := MeasureTheory.lintegral_mono hpt
      _ ≤ liminf (fun k ↦ ∫⁻ t, fk k t ∂volume) atTop := MeasureTheory.lintegral_liminf_le hfk_meas
      _ = liminf (fun k ↦ relEntropy (Ak k) (Bk k) * ENNReal.ofReal (Real.log 2)) atTop := by
          congr 1; ext k
          exact (relEntropy_frenkel_integral
            (mix_maxMixed_posDef (𝒩.apply _) hδ0 hδ1) (mix_maxMixed_posDef (𝒩.apply _) hδ0 hδ1)).symm
      _ ≤ liminf (fun k ↦
            relEntropy (DensityOp.mix (ε k) (le_of_lt (hε_pos k)) (le_of_lt (hε_lt1 k)) ρ (maxMixedState d₁))
              (DensityOp.mix (ε k) (le_of_lt (hε_pos k)) (le_of_lt (hε_lt1 k)) σ (maxMixedState d₁)) *
            ENNReal.ofReal (Real.log 2)) atTop := by
          apply Filter.liminf_le_liminf
          · exact Eventually.of_forall fun k ↦
              mul_le_mul_of_nonneg_right (hdpi_ε (ε k) (hε_pos k) (hε_lt1 k)) zero_le
          · isBoundedDefault
          · isBoundedDefault
      _ = relEntropy ρ σ * ENNReal.ofReal (Real.log 2) := by
          have htend_rhs : Tendsto (fun k ↦
              relEntropy (DensityOp.mix (ε k) (le_of_lt (hε_pos k)) (le_of_lt (hε_lt1 k)) ρ (maxMixedState d₁))
                (DensityOp.mix (ε k) (le_of_lt (hε_pos k)) (le_of_lt (hε_lt1 k)) σ (maxMixedState d₁)) *
              ENNReal.ofReal (Real.log 2))
              atTop (𝓝 (relEntropy ρ σ * ENNReal.ofReal (Real.log 2))) := by
            have h1 := (tendsto_relEntropy_mix_maxMixed ρ σ).comp hε_tendsto
            have h2 : ∀ k : ℕ,
                (if h : 0 < ε k ∧ ε k < 1 then
                  relEntropy (DensityOp.mix (ε k) (le_of_lt h.1) (le_of_lt h.2) ρ (maxMixedState d₁))
                    (DensityOp.mix (ε k) (le_of_lt h.1) (le_of_lt h.2) σ (maxMixedState d₁))
                else relEntropy ρ σ) =
                relEntropy (DensityOp.mix (ε k) (le_of_lt (hε_pos k)) (le_of_lt (hε_lt1 k)) ρ (maxMixedState d₁))
                  (DensityOp.mix (ε k) (le_of_lt (hε_pos k)) (le_of_lt (hε_lt1 k)) σ (maxMixedState d₁)) :=
              fun k ↦ dif_pos ⟨hε_pos k, hε_lt1 k⟩
            have h1' : Tendsto (fun k ↦
                relEntropy (DensityOp.mix (ε k) (le_of_lt (hε_pos k)) (le_of_lt (hε_lt1 k)) ρ (maxMixedState d₁))
                  (DensityOp.mix (ε k) (le_of_lt (hε_pos k)) (le_of_lt (hε_lt1 k)) σ (maxMixedState d₁)))
                atTop (𝓝 (relEntropy ρ σ)) := by
              simpa [Function.comp_def, h2] using h1
            exact ENNReal.Tendsto.mul_const h1' (Or.inr ENNReal.ofReal_ne_top)
          exact htend_rhs.liminf_eq
  -- Step 2: Take `δ → 0+` via `tendsto_relEntropy_mix_maxMixed`
  refine le_of_tendsto (tendsto_relEntropy_mix_maxMixed (𝒩.apply ρ) (𝒩.apply σ)) ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
  rw [dif_pos ⟨hδ.1, hδ.2⟩]
  exact hstep_δ δ hδ.1 hδ.2

/-- **General CPTP Data Processing Inequality for Quantum Jensen–Shannon Divergence**:
`QJS(𝒩(ρ), 𝒩(σ)) ≤ QJS(ρ, σ)` for every CPTP map `𝒩` and all density operators `ρ, σ`. -/
theorem qjs_cptp_le (𝒩 : CPTPMap d₁ d₂) (ρ σ : DensityOp d₁) :
    qjs (𝒩.apply ρ) (𝒩.apply σ) ≤ qjs ρ σ := by
  haveI : Nonempty d₁ := by
    by_contra h0; haveI : IsEmpty d₁ := not_nonempty_iff.mp h0
    have htr := ρ.trace_one; simp [Matrix.trace] at htr
  haveI : Nonempty d₂ := by
    by_contra h0; haveI : IsEmpty d₂ := not_nonempty_iff.mp h0
    have htr := (𝒩.apply ρ).trace_one; simp [Matrix.trace] at htr
  have hdensity_ext : ∀ {α : Type u} [Fintype α] [DecidableEq α] (X Y : DensityOp α),
      X.mat = Y.mat → X = Y := by
    intro α _ _ ⟨_, _, _⟩ ⟨_, _, _⟩ h; cases h; rfl
  have hqjs_rel : ∀ {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α] (A B : DensityOp α),
      qjs A B = ((relEntropy A (DensityOp.midpoint A B)).toReal +
        (relEntropy B (DensityOp.midpoint A B)).toReal) / 2 ∧
      relEntropy A (DensityOp.midpoint A B) ≠ ⊤ ∧
      relEntropy B (DensityOp.midpoint A B) ≠ ⊤ := by
    intro α _ _ _ A B
    have hsuppA : suppSubset A (DensityOp.midpoint A B) := by
      intro i j hAi hMj
      set v : α → ℂ := fun r ↦ ((DensityOp.midpoint A B).eigUnitary : Matrix α α ℂ) r j
      have hker : (DensityOp.midpoint A B).mat.mulVec v = 0 := by
        set U := ((DensityOp.midpoint A B).eigUnitary : Matrix α α ℂ)
        have hspec : (DensityOp.midpoint A B).mat = U * Matrix.diagonal (Complex.ofReal ∘ (DensityOp.midpoint A B).eigvals) * star U := by
          simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
            Unitary.conjStarAlgAut_apply] using (DensityOp.midpoint A B).isHermitian.spectral_theorem
        have hcol : (star U).mulVec v = Pi.single j 1 := by
          ext k; have h := congr_fun (congr_fun (Unitary.coe_star_mul_self (DensityOp.midpoint A B).eigUnitary) k) j
          simpa [v, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
            Pi.single_apply, eq_comm] using h
        conv_lhs => rw [hspec]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol]
        have hz : Matrix.diagonal (Complex.ofReal ∘ (DensityOp.midpoint A B).eigvals) *ᵥ Pi.single j 1 = 0 := by
          ext k; rw [Matrix.mulVec_diagonal]; by_cases hk : k = j
          · subst hk; simp [hMj]
          · simp [Pi.single_eq_of_ne hk]
        rw [hz, Matrix.mulVec_zero]
      have hquad0 : (star v ⬝ᵥ (DensityOp.midpoint A B).mat.mulVec v).re = 0 := by rw [hker]; simp
      have hmid_quad : (star v ⬝ᵥ (DensityOp.midpoint A B).mat.mulVec v).re =
          ((star v ⬝ᵥ A.mat.mulVec v).re + (star v ⬝ᵥ B.mat.mulVec v).re) / 2 := by
        have h1 : (DensityOp.midpoint A B).mat.mulVec v =
            ((1 / 2 : ℝ) : ℂ) • A.mat.mulVec v + ((1 / 2 : ℝ) : ℂ) • B.mat.mulVec v := by
          show (((1 - 1 / 2 : ℝ) : ℂ) • A.mat + ((1 / 2 : ℝ) : ℂ) • B.mat).mulVec v = _
          rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]; norm_num
        rw [h1, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]; ring
      have hAnn : 0 ≤ (star v ⬝ᵥ A.mat.mulVec v).re :=
        (Complex.le_def.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp A.posSemidef).2 v)).1
      have hBnn : 0 ≤ (star v ⬝ᵥ B.mat.mulVec v).re :=
        (Complex.le_def.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp B.posSemidef).2 v)).1
      have hA0 : (star v ⬝ᵥ A.mat.mulVec v).re = 0 := by linarith
      rw [re_quadForm_spectral A.isHermitian v] at hA0
      have hterm0 : A.eigvals i * ‖((star (A.eigUnitary : Matrix α α ℂ)).mulVec v) i‖ ^ 2 = 0 := by
        have hle := Finset.single_le_sum (f := fun k : α ↦ A.eigvals k * ‖((star (A.eigUnitary : Matrix α α ℂ)).mulVec v) k‖ ^ 2)
          (fun k _ ↦ mul_nonneg (A.eigvals_nonneg k) (sq_nonneg _)) (Finset.mem_univ i)
        have hge : 0 ≤ A.eigvals i * ‖((star (A.eigUnitary : Matrix α α ℂ)).mulVec v) i‖ ^ 2 :=
          mul_nonneg (A.eigvals_nonneg i) (sq_nonneg _)
        unfold DensityOp.eigvals DensityOp.eigUnitary at hle hge ⊢
        linarith
      have hnorm0 : ((star (A.eigUnitary : Matrix α α ℂ)).mulVec v) i = 0 := by
        rcases mul_eq_zero.mp hterm0 with h | h
        · exact absurd h hAi
        · exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)
      have hconj : (star ((DensityOp.midpoint A B).eigUnitary : Matrix α α ℂ) * (A.eigUnitary : Matrix α α ℂ)) j i =
          star (((star (A.eigUnitary : Matrix α α ℂ)).mulVec v) i) := by
        simp only [v, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.star_apply, star_sum,
          star_mul', star_star]
        apply Finset.sum_congr rfl; intro k _; ring
      rw [hconj, hnorm0, star_zero]
    have hsuppB : suppSubset B (DensityOp.midpoint A B) := by
      intro i j hBi hMj
      set v : α → ℂ := fun r ↦ ((DensityOp.midpoint A B).eigUnitary : Matrix α α ℂ) r j
      have hker : (DensityOp.midpoint A B).mat.mulVec v = 0 := by
        set U := ((DensityOp.midpoint A B).eigUnitary : Matrix α α ℂ)
        have hspec : (DensityOp.midpoint A B).mat = U * Matrix.diagonal (Complex.ofReal ∘ (DensityOp.midpoint A B).eigvals) * star U := by
          simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
            Unitary.conjStarAlgAut_apply] using (DensityOp.midpoint A B).isHermitian.spectral_theorem
        have hcol : (star U).mulVec v = Pi.single j 1 := by
          ext k; have h := congr_fun (congr_fun (Unitary.coe_star_mul_self (DensityOp.midpoint A B).eigUnitary) k) j
          simpa [v, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
            Pi.single_apply, eq_comm] using h
        conv_lhs => rw [hspec]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol]
        have hz : Matrix.diagonal (Complex.ofReal ∘ (DensityOp.midpoint A B).eigvals) *ᵥ Pi.single j 1 = 0 := by
          ext k; rw [Matrix.mulVec_diagonal]; by_cases hk : k = j
          · subst hk; simp [hMj]
          · simp [Pi.single_eq_of_ne hk]
        rw [hz, Matrix.mulVec_zero]
      have hquad0 : (star v ⬝ᵥ (DensityOp.midpoint A B).mat.mulVec v).re = 0 := by rw [hker]; simp
      have hmid_quad : (star v ⬝ᵥ (DensityOp.midpoint A B).mat.mulVec v).re =
          ((star v ⬝ᵥ A.mat.mulVec v).re + (star v ⬝ᵥ B.mat.mulVec v).re) / 2 := by
        have h1 : (DensityOp.midpoint A B).mat.mulVec v =
            ((1 / 2 : ℝ) : ℂ) • A.mat.mulVec v + ((1 / 2 : ℝ) : ℂ) • B.mat.mulVec v := by
          show (((1 - 1 / 2 : ℝ) : ℂ) • A.mat + ((1 / 2 : ℝ) : ℂ) • B.mat).mulVec v = _
          rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]; norm_num
        rw [h1, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]; ring
      have hAnn : 0 ≤ (star v ⬝ᵥ A.mat.mulVec v).re :=
        (Complex.le_def.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp A.posSemidef).2 v)).1
      have hBnn : 0 ≤ (star v ⬝ᵥ B.mat.mulVec v).re :=
        (Complex.le_def.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp B.posSemidef).2 v)).1
      have hB0 : (star v ⬝ᵥ B.mat.mulVec v).re = 0 := by linarith
      rw [re_quadForm_spectral B.isHermitian v] at hB0
      have hterm0 : B.eigvals i * ‖((star (B.eigUnitary : Matrix α α ℂ)).mulVec v) i‖ ^ 2 = 0 := by
        have hle := Finset.single_le_sum (f := fun k : α ↦ B.eigvals k * ‖((star (B.eigUnitary : Matrix α α ℂ)).mulVec v) k‖ ^ 2)
          (fun k _ ↦ mul_nonneg (B.eigvals_nonneg k) (sq_nonneg _)) (Finset.mem_univ i)
        have hge : 0 ≤ B.eigvals i * ‖((star (B.eigUnitary : Matrix α α ℂ)).mulVec v) i‖ ^ 2 :=
          mul_nonneg (B.eigvals_nonneg i) (sq_nonneg _)
        unfold DensityOp.eigvals DensityOp.eigUnitary at hle hge ⊢
        linarith
      have hnorm0 : ((star (B.eigUnitary : Matrix α α ℂ)).mulVec v) i = 0 := by
        rcases mul_eq_zero.mp hterm0 with h | h
        · exact absurd h hBi
        · exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)
      have hconj : (star ((DensityOp.midpoint A B).eigUnitary : Matrix α α ℂ) * (B.eigUnitary : Matrix α α ℂ)) j i =
          star (((star (B.eigUnitary : Matrix α α ℂ)).mulVec v) i) := by
        simp only [v, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.star_apply, star_sum,
          star_mul', star_star]
        apply Finset.sum_congr rfl; intro k _; ring
      rw [hconj, hnorm0, star_zero]
    have hA_ne : relEntropy A (DensityOp.midpoint A B) ≠ ⊤ := by
      unfold relEntropy; rw [if_pos hsuppA]; exact ENNReal.ofReal_ne_top
    have hB_ne : relEntropy B (DensityOp.midpoint A B) ≠ ⊤ := by
      unfold relEntropy; rw [if_pos hsuppB]; exact ENNReal.ofReal_ne_top
    refine ⟨?_, hA_ne, hB_ne⟩
    have hL : Tendsto (fun δ : ℝ ↦
        if h : 0 < δ ∧ δ < 1 then
          qjs (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) A (maxMixedState α))
              (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) B (maxMixedState α))
        else qjs A B) (𝓝[>] 0) (𝓝 (qjs A B)) := by
      have hm := tendsto_vonNeumannEntropy_mix_maxMixed (DensityOp.midpoint A B)
      have hA' := tendsto_vonNeumannEntropy_mix_maxMixed A
      have hB' := tendsto_vonNeumannEntropy_mix_maxMixed B
      have hcomb := hm.sub ((hA'.add hB').div_const 2)
      refine hcomb.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
      have h01 : 0 ≤ δ ∧ δ ≤ 1 := ⟨le_of_lt hδ.1, le_of_lt hδ.2⟩
      rw [dif_pos h01, dif_pos h01, dif_pos h01, dif_pos ⟨hδ.1, hδ.2⟩]
      unfold qjs
      have hmid_eq : (DensityOp.midpoint
          (DensityOp.mix δ h01.1 h01.2 A (maxMixedState α))
          (DensityOp.mix δ h01.1 h01.2 B (maxMixedState α))).mat =
          (DensityOp.mix δ h01.1 h01.2 (DensityOp.midpoint A B) (maxMixedState α)).mat := by
        ext i j; simp [DensityOp.midpoint, DensityOp.mix, Complex.real_smul]; push_cast; ring
      rw [vonNeumannEntropy_eq_of_mat_eq hmid_eq]
    have hR : Tendsto (fun δ : ℝ ↦
        if h : 0 < δ ∧ δ < 1 then
          ((relEntropy (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) A (maxMixedState α))
              (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) (DensityOp.midpoint A B) (maxMixedState α))).toReal +
           (relEntropy (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) B (maxMixedState α))
              (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) (DensityOp.midpoint A B) (maxMixedState α))).toReal) / 2
        else ((relEntropy A (DensityOp.midpoint A B)).toReal +
              (relEntropy B (DensityOp.midpoint A B)).toReal) / 2)
        (𝓝[>] 0) (𝓝 (((relEntropy A (DensityOp.midpoint A B)).toReal +
          (relEntropy B (DensityOp.midpoint A B)).toReal) / 2)) := by
      have h1 := (ENNReal.continuousAt_toReal hA_ne).tendsto.comp
        (tendsto_relEntropy_mix_maxMixed A (DensityOp.midpoint A B))
      have h2 := (ENNReal.continuousAt_toReal hB_ne).tendsto.comp
        (tendsto_relEntropy_mix_maxMixed B (DensityOp.midpoint A B))
      have hcomb := (h1.add h2).div_const 2
      refine hcomb.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
      have hδ' : 0 < δ ∧ δ < 1 := ⟨hδ.1, hδ.2⟩
      simp only [Function.comp_def, dif_pos hδ']
    have hEq : ∀ᶠ δ : ℝ in 𝓝[>] 0,
        (if h : 0 < δ ∧ δ < 1 then
          qjs (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) A (maxMixedState α))
              (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) B (maxMixedState α))
        else qjs A B) =
        (if h : 0 < δ ∧ δ < 1 then
          ((relEntropy (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) A (maxMixedState α))
              (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) (DensityOp.midpoint A B) (maxMixedState α))).toReal +
           (relEntropy (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) B (maxMixedState α))
              (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) (DensityOp.midpoint A B) (maxMixedState α))).toReal) / 2
        else ((relEntropy A (DensityOp.midpoint A B)).toReal +
              (relEntropy B (DensityOp.midpoint A B)).toReal) / 2) := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
      have hδ' : 0 < δ ∧ δ < 1 := ⟨hδ.1, hδ.2⟩
      rw [dif_pos hδ', dif_pos hδ']
      have hq := (qjs_eq_half_relEntropy_midpoint (mix_maxMixed_posDef A hδ.1 hδ.2) (mix_maxMixed_posDef B hδ.1 hδ.2)).2
      have hmid_eq : DensityOp.midpoint
          (DensityOp.mix δ (le_of_lt hδ.1) (le_of_lt hδ.2) A (maxMixedState α))
          (DensityOp.mix δ (le_of_lt hδ.1) (le_of_lt hδ.2) B (maxMixedState α)) =
          DensityOp.mix δ (le_of_lt hδ.1) (le_of_lt hδ.2) (DensityOp.midpoint A B) (maxMixedState α) := by
        apply hdensity_ext
        ext i j; simp [DensityOp.midpoint, DensityOp.mix, Complex.real_smul]; push_cast; ring
      rw [hmid_eq] at hq
      have h1_ne : relEntropy (DensityOp.mix δ (le_of_lt hδ.1) (le_of_lt hδ.2) A (maxMixedState α))
          (DensityOp.mix δ (le_of_lt hδ.1) (le_of_lt hδ.2) (DensityOp.midpoint A B) (maxMixedState α)) ≠ ⊤ := by
        unfold relEntropy
        have hpd := mix_maxMixed_posDef (DensityOp.midpoint A B) hδ.1 hδ.2
        have hsp : suppSubset (DensityOp.mix δ (le_of_lt hδ.1) (le_of_lt hδ.2) A (maxMixedState α))
            (DensityOp.mix δ (le_of_lt hδ.1) (le_of_lt hδ.2) (DensityOp.midpoint A B) (maxMixedState α)) :=
          fun i j _ h0 ↦ absurd h0 (ne_of_gt (hpd.eigenvalues_pos j))
        rw [if_pos hsp]
        exact ENNReal.ofReal_ne_top
      have h2_ne : relEntropy (DensityOp.mix δ (le_of_lt hδ.1) (le_of_lt hδ.2) B (maxMixedState α))
          (DensityOp.mix δ (le_of_lt hδ.1) (le_of_lt hδ.2) (DensityOp.midpoint A B) (maxMixedState α)) ≠ ⊤ := by
        unfold relEntropy
        have hpd := mix_maxMixed_posDef (DensityOp.midpoint A B) hδ.1 hδ.2
        have hsp : suppSubset (DensityOp.mix δ (le_of_lt hδ.1) (le_of_lt hδ.2) B (maxMixedState α))
            (DensityOp.mix δ (le_of_lt hδ.1) (le_of_lt hδ.2) (DensityOp.midpoint A B) (maxMixedState α)) :=
          fun i j _ h0 ↦ absurd h0 (ne_of_gt (hpd.eigenvalues_pos j))
        rw [if_pos hsp]
        exact ENNReal.ofReal_ne_top
      have hq_real := congr_arg ENNReal.toReal hq
      rw [ENNReal.toReal_ofReal (qjs_eq_half_relEntropy_midpoint (mix_maxMixed_posDef A hδ.1 hδ.2) (mix_maxMixed_posDef B hδ.1 hδ.2)).1,
        ENNReal.toReal_div, ENNReal.toReal_add h1_ne h2_ne] at hq_real
      have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
      rw [htwo] at hq_real
      linarith
    exact tendsto_nhds_unique (hL.congr' hEq) hR
  obtain ⟨h1, _, _⟩ := hqjs_rel (𝒩.apply ρ) (𝒩.apply σ)
  obtain ⟨h2, h2A, h2B⟩ := hqjs_rel ρ σ
  have hmid_N : DensityOp.midpoint (𝒩.apply ρ) (𝒩.apply σ) = 𝒩.apply (DensityOp.midpoint ρ σ) := by
    apply hdensity_ext
    show ((1 - 1 / 2 : ℝ) : ℂ) • 𝒩.toLinearMap ρ.mat + ((1 / 2 : ℝ) : ℂ) • 𝒩.toLinearMap σ.mat =
      𝒩.toLinearMap (((1 - 1 / 2 : ℝ) : ℂ) • ρ.mat + ((1 / 2 : ℝ) : ℂ) • σ.mat)
    rw [map_add, map_smul, map_smul]
  rw [h1, h2, hmid_N]
  have hleA : (relEntropy (𝒩.apply ρ) (𝒩.apply (DensityOp.midpoint ρ σ))).toReal ≤
      (relEntropy ρ (DensityOp.midpoint ρ σ)).toReal :=
    ENNReal.toReal_mono h2A (relEntropy_cptp_le 𝒩 ρ (DensityOp.midpoint ρ σ))
  have hleB : (relEntropy (𝒩.apply σ) (𝒩.apply (DensityOp.midpoint ρ σ))).toReal ≤
      (relEntropy σ (DensityOp.midpoint ρ σ)).toReal :=
    ENNReal.toReal_mono h2B (relEntropy_cptp_le 𝒩 σ (DensityOp.midpoint ρ σ))
  linarith

/-- **General CPTP Data Processing Inequality for c-q Conditional Entropy**:
`H(𝒩 ∘ W) ≥ H(W)` for every CPTP map `𝒩` and every binary-input c-q channel `W`. -/
theorem condEntropy_cptp_ge (𝒩 : CPTPMap d₁ d₂) (W : CQChannel d₁) :
    W.condEntropy ≤ (𝒩.compCQ W).condEntropy := by
  unfold CQChannel.condEntropy CPTPMap.compCQ
  linarith [qjs_cptp_le 𝒩 (W.out false) (W.out true)]

end CPTPDPI

end PolarCodes
