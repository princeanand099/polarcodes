/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.QuantumProps

/-!
# Qubit Dephasing Channel and Gram-Matrix Dephasing Reduction (Lemma 4.1)

This module formalizes:
- The Pauli-`Z` unitary `pauliZTensorI` on `ℂ² ⊗ ℂ^d`
- The qubit dephasing channel `dephaseState p Ψ = (Z_p ⊗ id)(Ψ)` and its relative-entropy
  coherence `dephaseCoherence p Ψ = S(Ψ_∞) - S(Ψ_p) = QJS(Ψ_p, Ψ̃_p)`
- Pure-state density operators `pureState φ = |φ⟩⟨φ|`
- **Lemma 4.1 (Gram-Matrix Dephasing Reduction)**:
  `Ψ₁ := ½ [[ρ₀, √ρ₀√ρ₁], [√ρ₁√ρ₀, ρ₁]] ∈ D(ℂ² ⊗ H₁)` satisfies:
  1. `S(½ (ρ₀ ⊗ |φ₀⟩⟨φ₀| + ρ₁ ⊗ |φ₁⟩⟨φ₁|)) = S((Z_p ⊗ id)(Ψ₁))` for `p = (1 - |⟨φ₀|φ₁⟩|) / 2`,
  2. `S(Ψ₁) = S((ρ₀ + ρ₁) / 2)`,
  3. `S((Z_{1/2} ⊗ id)(Ψ₁)) = 1 + ½ (S(ρ₀) + S(ρ₁))`,
  4. `C(0) = H(W₁)`.
-/

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodes

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-! ### Pauli-`Z` Unitary and Qubit Dephasing Channel -/

/-- The unitary operator `Z ⊗ I` on `ℂ² ⊗ ℂ^d`, acting as `+1` on `false` and `-1` on `true`. -/
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
      · subst h1; simp [hpq]
      · simp [h1]⟩

/-- Qubit dephasing channel `(Z_p ⊗ id)(Ψ) = (1 - p) Ψ + p (Z ⊗ I) Ψ (Z ⊗ I)` for `p ∈ [0, 1]`. -/
noncomputable def dephaseState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) : DensityOp (Bool × d) :=
  DensityOp.mix p hp0 hp1 Ψ (DensityOp.conjUnitary (pauliZTensorI d) Ψ)

lemma dephaseState_apply (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) (b₁ b₂ : Bool) (i j : d) :
    (dephaseState p hp0 hp1 Ψ).mat (b₁, i) (b₂, j) =
      (if b₁ = b₂ then (1 : ℂ) else ((1 - 2 * p : ℝ) : ℂ)) * Ψ.mat (b₁, i) (b₂, j) := by
  simp only [dephaseState, DensityOp.mix, DensityOp.conjUnitary, pauliZTensorI,
    Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.star_apply, Complex.real_smul]
  have hconj :
      (∑ x : Bool × d, (∑ y : Bool × d,
          (if (b₁, i) = y then (if b₁ = false then (1 : ℂ) else -1) else 0) * Ψ.mat y x) *
        star (if x = (b₂, j) then (if x.1 = false then (1 : ℂ) else -1) else 0)) =
      (if b₁ = false then (1 : ℂ) else -1) * Ψ.mat (b₁, i) (b₂, j) *
        (if b₂ = false then (1 : ℂ) else -1) := by
    rw [Finset.sum_eq_single (b₂, j)]
    · rw [Finset.sum_eq_single (b₁, i)]
      · cases b₂ <;> simp
      · intro y _ hy; simp [Ne.symm hy]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro x _ hx; simp [hx]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hconj]
  cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring

lemma dephaseState_zero (Ψ : DensityOp (Bool × d)) :
    (dephaseState 0 le_rfl (by norm_num) Ψ).mat = Ψ.mat := by
  ext ⟨b₁, i⟩ ⟨b₂, j⟩
  rw [dephaseState_apply]
  cases b₁ <;> cases b₂ <;> simp

/-- Relative-entropy coherence of `Ψ` under qubit dephasing of strength `p`:
`C(p) := S((Z_{1/2} ⊗ id)(Ψ)) - S((Z_p ⊗ id)(Ψ))`. -/
noncomputable def dephaseCoherence (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) : ℝ :=
  vonNeumannEntropy (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) -
    vonNeumannEntropy (dephaseState p hp0 hp1 Ψ)

/-- `C(p) = QJS(Ψ_p, (Z ⊗ I) Ψ_p (Z ⊗ I))` for all `p ∈ [0, 1]`. -/
lemma dephaseCoherence_eq_qjs (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) :
    dephaseCoherence p hp0 hp1 Ψ =
      qjs (dephaseState p hp0 hp1 Ψ)
        (DensityOp.conjUnitary (pauliZTensorI d) (dephaseState p hp0 hp1 Ψ)) := by
  unfold dephaseCoherence qjs
  rw [vonNeumannEntropy_conjUnitary]
  have hmid : (DensityOp.midpoint (dephaseState p hp0 hp1 Ψ)
      (DensityOp.conjUnitary (pauliZTensorI d) (dephaseState p hp0 hp1 Ψ))).mat =
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ).mat := by
    ext ⟨b₁, i⟩ ⟨b₂, j⟩
    have h1 := dephaseState_apply (1 / 2) (by norm_num) (by norm_num)
      (dephaseState p hp0 hp1 Ψ) b₁ b₂ i j
    have h2 := dephaseState_apply (1 / 2) (by norm_num) (by norm_num) Ψ b₁ b₂ i j
    have h3 := dephaseState_apply p hp0 hp1 Ψ b₁ b₂ i j
    change (dephaseState (1 / 2) (by norm_num) (by norm_num) (dephaseState p hp0 hp1 Ψ)).mat (b₁, i) (b₂, j) = _
    rw [h1, h2, h3]
    cases b₁ <;> cases b₂ <;> norm_num
  rw [vonNeumannEntropy_eq_of_mat_eq hmid]
  ring

/-! ### Pure States and Gram-Matrix State `Ψ₁` -/

/-- Pure-state density operator `|φ⟩⟨φ|` for a unit vector `φ : d → ℂ`. -/
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

/-- Block column operator `A₀ : (Bool × d) × d` with blocks `√ρ₀ / √2` and `√ρ₁ / √2`. -/
noncomputable def gramFactor (ρ₀ ρ₁ : DensityOp d) : Matrix (Bool × d) d ℂ :=
  Matrix.of fun p k ↦
    ((Real.sqrt 2)⁻¹ : ℂ) * (if p.1 = false then ρ₀.sqrtMat p.2 k else ρ₁.sqrtMat p.2 k)

/-- The Gram state `Ψ₁ := ½ [[ρ₀, √ρ₀√ρ₁], [√ρ₁√ρ₀, ρ₁]] ∈ D(ℂ² ⊗ H₁)` from Eq. (4.1). -/
noncomputable def gramState (ρ₀ ρ₁ : DensityOp d) : DensityOp (Bool × d) where
  mat := gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ
  posSemidef := by simpa [Matrix.conjTranspose_conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self (gramFactor ρ₀ ρ₁)ᴴ
  trace_one := by
    have htr : (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ).trace =
        ((gramFactor ρ₀ ρ₁)ᴴ * gramFactor ρ₀ ρ₁).trace := Matrix.trace_mul_comm _ _
    rw [htr]
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
        simp only [Matrix.conjTranspose_apply] at hh
        rw [hh]
      have h1 : ∑ k : d, star (ρ₁.sqrtMat k i) * ρ₁.sqrtMat k j = ρ₁.mat i j := by
        have h := congr_fun (congr_fun ρ₁.sqrtMat_mul_self i) j
        rw [← h, Matrix.mul_apply]
        apply Finset.sum_congr rfl; intro k _
        have hh := congr_fun (congr_fun ρ₁.sqrtMat_isHermitian.eq i) k
        simp only [Matrix.conjTranspose_apply] at hh
        rw [hh]
      have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
        rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
          ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        push_cast; ring
      have hrew : ∀ (M : Matrix d d ℂ),
          (∑ k : d, star (((Real.sqrt 2 : ℂ)⁻¹) * M k i) * (((Real.sqrt 2 : ℂ)⁻¹) * M k j)) =
            (1 / 2 : ℂ) * ∑ k : d, star (M k i) * M k j := by
        intro M
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        rw [star_mul']
        calc star (M k i) * star ((Real.sqrt 2 : ℂ)⁻¹) * (((Real.sqrt 2 : ℂ)⁻¹) * M k j)
            = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (star (M k i) * M k j) := by ring
          _ = (1 / 2 : ℂ) * (star (M k i) * M k j) := by rw [hsq2]
      rw [hrew ρ₀.sqrtMat, hrew ρ₁.sqrtMat, h0, h1]
      push_cast; ring
    rw [hprod, (DensityOp.midpoint ρ₀ ρ₁).trace_one]

/-- **Lemma 4.1 (Gram-Matrix Dephasing Reduction)**:
Let `ρ₀, ρ₁ ∈ D(H₁)` and let `φ₀, φ₁ ∈ H₂` be unit vectors with overlap
`f₂ := ‖⟨φ₀|φ₁⟩‖ ∈ [0, 1]`. Setting `p := (1 - f₂) / 2 ∈ [0, 1/2]`:
1. `S(½ (ρ₀ ⊗ |φ₀⟩⟨φ₀| + ρ₁ ⊗ |φ₁⟩⟨φ₁|)) = S((Z_p ⊗ id)(Ψ₁))`,
2. `S(Ψ₁) = S((ρ₀ + ρ₁) / 2)`,
3. `S((Z_{1/2} ⊗ id)(Ψ₁)) = 1 + ½ (S(ρ₀) + S(ρ₁))`,
4. `C(0) = 1 - QJS(ρ₀, ρ₁)`. -/
theorem lemma_4_1_gram_dephasing
    (ρ₀ ρ₁ : DensityOp d₁) (φ₀ φ₁ : d₂ → ℂ)
    (hφ₀ : ∑ k : d₂, ‖φ₀ k‖ ^ 2 = 1) (hφ₁ : ∑ k : d₂, ‖φ₁ k‖ ^ 2 = 1) :
    let f₂ : ℝ := ‖∑ k : d₂, star (φ₀ k) * φ₁ k‖
    have hf₂_le : f₂ ≤ 1 := by
      have h1 : ‖∑ k : d₂, star (φ₀ k) * φ₁ k‖ ≤ ∑ k : d₂, ‖φ₀ k‖ * ‖φ₁ k‖ := by
        calc ‖∑ k : d₂, star (φ₀ k) * φ₁ k‖
            ≤ ∑ k : d₂, ‖star (φ₀ k) * φ₁ k‖ := norm_sum_le _ _
          _ = ∑ k : d₂, ‖φ₀ k‖ * ‖φ₁ k‖ := by simp [norm_mul]
      have h2 : ∑ k : d₂, ‖φ₀ k‖ * ‖φ₁ k‖ ≤
          Real.sqrt (∑ k : d₂, ‖φ₀ k‖ ^ 2) * Real.sqrt (∑ k : d₂, ‖φ₁ k‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k ↦ ‖φ₀ k‖) (fun k ↦ ‖φ₁ k‖)
      rw [hφ₀, hφ₁, Real.sqrt_one, mul_one] at h2
      exact le_trans h1 h2
    let p : ℝ := (1 - f₂) / 2
    have hp0 : 0 ≤ p := by simp only [p]; linarith
    have hp1 : p ≤ 1 / 2 := by simp only [p]; linarith [norm_nonneg (∑ k : d₂, star (φ₀ k) * φ₁ k)]
    vonNeumannEntropy (DensityOp.midpoint
        (DensityOp.tensor ρ₀ (pureState φ₀ hφ₀))
        (DensityOp.tensor ρ₁ (pureState φ₁ hφ₁))) =
      vonNeumannEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₀ ρ₁)) ∧
    vonNeumannEntropy (gramState ρ₀ ρ₁) = vonNeumannEntropy (DensityOp.midpoint ρ₀ ρ₁) ∧
    vonNeumannEntropy (dephaseState (1 / 2) (by norm_num) (by norm_num) (gramState ρ₀ ρ₁)) =
      1 + (vonNeumannEntropy ρ₀ + vonNeumannEntropy ρ₁) / 2 ∧
    dephaseCoherence 0 le_rfl (by norm_num) (gramState ρ₀ ρ₁) = 1 - qjs ρ₀ ρ₁ ∧
    (DensityOp.midpoint
        (DensityOp.tensor ρ₀ (pureState φ₀ hφ₀))
        (DensityOp.tensor ρ₁ (pureState φ₁ hφ₁))).mat.charpoly *
      Polynomial.X ^ Fintype.card (Bool × d₁) =
      (dephaseState p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₀ ρ₁)).mat.charpoly *
        Polynomial.X ^ Fintype.card (d₁ × d₂) := by
  intro f₂ hf₂_le p hp0 hp1
  have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  have hsq2' : ((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [mul_comm, hsq2]
  -- Part 2: `S(Ψ₁) = S(midpoint ρ₀ ρ₁)` via `spectral_sum_mul_conjTranspose (gramFactor ρ₀ ρ₁)`
  have hpart2 : vonNeumannEntropy (gramState ρ₀ ρ₁) =
      vonNeumannEntropy (DensityOp.midpoint ρ₀ ρ₁) := by
    unfold vonNeumannEntropy DensityOp.eigvals
    congr 1
    have hAA : (gramFactor ρ₀ ρ₁)ᴴ * gramFactor ρ₀ ρ₁ = (DensityOp.midpoint ρ₀ ρ₁).mat := by
      ext i j
      simp only [gramFactor, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
        DensityOp.midpoint, DensityOp.mix, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
      have h0 : ∑ k : d₁, star (ρ₀.sqrtMat k i) * ρ₀.sqrtMat k j = ρ₀.mat i j := by
        have h := congr_fun (congr_fun ρ₀.sqrtMat_mul_self i) j
        rw [← h, Matrix.mul_apply]
        apply Finset.sum_congr rfl; intro k _
        have hh := congr_fun (congr_fun ρ₀.sqrtMat_isHermitian.eq i) k
        simp only [Matrix.conjTranspose_apply] at hh; rw [hh]
      have h1 : ∑ k : d₁, star (ρ₁.sqrtMat k i) * ρ₁.sqrtMat k j = ρ₁.mat i j := by
        have h := congr_fun (congr_fun ρ₁.sqrtMat_mul_self i) j
        rw [← h, Matrix.mul_apply]
        apply Finset.sum_congr rfl; intro k _
        have hh := congr_fun (congr_fun ρ₁.sqrtMat_isHermitian.eq i) k
        simp only [Matrix.conjTranspose_apply] at hh; rw [hh]
      have hrew : ∀ (M : Matrix d₁ d₁ ℂ),
          (∑ k : d₁, star (((Real.sqrt 2 : ℂ)⁻¹) * M k i) * (((Real.sqrt 2 : ℂ)⁻¹) * M k j)) =
            (1 / 2 : ℂ) * ∑ k : d₁, star (M k i) * M k j := by
        intro M
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        rw [star_mul']
        calc star (M k i) * star ((Real.sqrt 2 : ℂ)⁻¹) * (((Real.sqrt 2 : ℂ)⁻¹) * M k j)
            = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (star (M k i) * M k j) := by ring
          _ = (1 / 2 : ℂ) * (star (M k i) * M k j) := by rw [hsq2]
      rw [hrew ρ₀.sqrtMat, hrew ρ₁.sqrtMat, h0, h1]; push_cast; ring
    have hcp := charpoly_mul_conjTranspose_eq (gramFactor ρ₀ ρ₁)
    rw [hAA] at hcp
    exact spectral_sum_eq_of_charpoly_mul_X_pow (gramState ρ₀ ρ₁).isHermitian
      (DensityOp.midpoint ρ₀ ρ₁).isHermitian hcp (by simp [Real.negMulLog])
  -- Part 3: `(Z_{1/2} ⊗ id)(Ψ₁) = ½ |0⟩⟨0| ⊗ ρ₀ + ½ |1⟩⟨1| ⊗ ρ₁`
  have hpart3 : vonNeumannEntropy (dephaseState (1 / 2) (by norm_num) (by norm_num) (gramState ρ₀ ρ₁)) =
      1 + (vonNeumannEntropy ρ₀ + vonNeumannEntropy ρ₁) / 2 := by
    have hmat : (dephaseState (1 / 2) (by norm_num) (by norm_num) (gramState ρ₀ ρ₁)).mat =
        (DensityOp.midpoint
          (DensityOp.tensor (CQChannel.ketBraBool false) ρ₀)
          (DensityOp.tensor (CQChannel.ketBraBool true) ρ₁)).mat := by
      ext ⟨b₁, i⟩ ⟨b₂, j⟩
      rw [dephaseState_apply]
      simp only [gramState, gramFactor, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, CQChannel.ketBraBool,
        Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul]
      cases b₁ <;> cases b₂
      · simp only [↓reduceIte, one_mul, and_self, Bool.false_eq_true, zero_mul, smul_zero, add_zero]
        have h0 : ∑ k : d₁, ρ₀.sqrtMat i k * star (ρ₀.sqrtMat j k) = ρ₀.mat i j := by
          have h := congr_fun (congr_fun ρ₀.sqrtMat_mul_self i) j
          rw [← h, Matrix.mul_apply]
          apply Finset.sum_congr rfl; intro k _
          have hh := congr_fun (congr_fun ρ₀.sqrtMat_isHermitian.eq k) j
          simp only [Matrix.conjTranspose_apply] at hh; rw [hh]
        have hrew : (∑ k : d₁, ((Real.sqrt 2 : ℂ)⁻¹) * ρ₀.sqrtMat i k *
            star (((Real.sqrt 2 : ℂ)⁻¹) * ρ₀.sqrtMat j k)) =
            (1 / 2 : ℂ) * ∑ k : d₁, ρ₀.sqrtMat i k * star (ρ₀.sqrtMat j k) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
          rw [star_mul']
          calc ((Real.sqrt 2 : ℂ)⁻¹) * ρ₀.sqrtMat i k * (star (ρ₀.sqrtMat j k) * star ((Real.sqrt 2 : ℂ)⁻¹))
              = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) *
                  (ρ₀.sqrtMat i k * star (ρ₀.sqrtMat j k)) := by ring
            _ = (1 / 2 : ℂ) * (ρ₀.sqrtMat i k * star (ρ₀.sqrtMat j k)) := by rw [hsq2']
        rw [hrew, h0]; push_cast; ring
      · norm_num
      · norm_num
      · simp only [Bool.true_eq_false, ↓reduceIte, one_mul, and_self, zero_mul, smul_zero, zero_add]
        have h1 : ∑ k : d₁, ρ₁.sqrtMat i k * star (ρ₁.sqrtMat j k) = ρ₁.mat i j := by
          have h := congr_fun (congr_fun ρ₁.sqrtMat_mul_self i) j
          rw [← h, Matrix.mul_apply]
          apply Finset.sum_congr rfl; intro k _
          have hh := congr_fun (congr_fun ρ₁.sqrtMat_isHermitian.eq k) j
          simp only [Matrix.conjTranspose_apply] at hh; rw [hh]
        have hrew : (∑ k : d₁, ((Real.sqrt 2 : ℂ)⁻¹) * ρ₁.sqrtMat i k *
            star (((Real.sqrt 2 : ℂ)⁻¹) * ρ₁.sqrtMat j k)) =
            (1 / 2 : ℂ) * ∑ k : d₁, ρ₁.sqrtMat i k * star (ρ₁.sqrtMat j k) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
          rw [star_mul']
          calc ((Real.sqrt 2 : ℂ)⁻¹) * ρ₁.sqrtMat i k * (star (ρ₁.sqrtMat j k) * star ((Real.sqrt 2 : ℂ)⁻¹))
              = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) *
                  (ρ₁.sqrtMat i k * star (ρ₁.sqrtMat j k)) := by ring
            _ = (1 / 2 : ℂ) * (ρ₁.sqrtMat i k * star (ρ₁.sqrtMat j k)) := by rw [hsq2']
        rw [hrew, h1]; push_cast; ring
    rw [vonNeumannEntropy_eq_of_mat_eq hmat, vonNeumannEntropy_block_midpoint]
  -- Part 4: `C(0) = 1 - QJS(ρ₀, ρ₁)`
  have hpart4 : dephaseCoherence 0 le_rfl (by norm_num) (gramState ρ₀ ρ₁) = 1 - qjs ρ₀ ρ₁ := by
    unfold dephaseCoherence qjs
    rw [vonNeumannEntropy_eq_of_mat_eq (dephaseState_zero (gramState ρ₀ ρ₁)), hpart2, hpart3]
    ring
  -- Part 1: Adjust global phase of `φ₁` so `⟨φ₀|ψ₁⟩ = f₂ ≥ 0`, build `A : (Bool × d₁) × (d₁ × d₂)`
  set z : ℂ := ∑ k : d₂, star (φ₀ k) * φ₁ k
  obtain ⟨u, hu_norm, hu_eq⟩ : ∃ u : ℂ, ‖u‖ = 1 ∧ u * z = (f₂ : ℂ) := by
    by_cases hz : z = 0
    · refine ⟨1, by simp, ?_⟩
      have hf0 : f₂ = 0 := by show ‖z‖ = 0; rw [hz, norm_zero]
      rw [hz, hf0]; simp
    · refine ⟨star z / (‖z‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z),
          div_self (norm_ne_zero_iff.mpr hz)]
      · have hne : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
        rw [div_mul_eq_mul_div, mul_comm (star z), Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          sq, Complex.ofReal_mul, mul_div_cancel_right₀ _ hne]
  let ψ₁ : d₂ → ℂ := fun k ↦ u * φ₁ k
  have hψ₁_norm : ∑ k : d₂, ‖ψ₁ k‖ ^ 2 = 1 := by
    simp only [ψ₁, norm_mul, hu_norm, one_mul, hφ₁]
  have hψ₁_ketbra : ∀ k₁ k₂ : d₂, ψ₁ k₁ * star (ψ₁ k₂) = φ₁ k₁ * star (φ₁ k₂) := by
    intro k₁ k₂
    have hu_sq : u * star u = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu_norm]; norm_num
    simp only [ψ₁, star_mul']
    calc _ = (u * star u) * (φ₁ k₁ * star (φ₁ k₂)) := by ring
      _ = φ₁ k₁ * star (φ₁ k₂) := by rw [hu_sq, one_mul]
  have hoverlap : ∑ k : d₂, star (φ₀ k) * ψ₁ k = (f₂ : ℂ) := by
    have h1 : ∑ k : d₂, star (φ₀ k) * ψ₁ k = u * z := by
      simp only [ψ₁, z, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [h1, hu_eq]
  have hoverlap_conj : ∑ k : d₂, star (ψ₁ k) * φ₀ k = (f₂ : ℂ) := by
    have h := congr_arg star hoverlap
    rw [star_sum, Complex.star_def, Complex.conj_ofReal] at h
    rw [← h]
    apply Finset.sum_congr rfl; intro k _
    rw [star_mul', star_star]
  have hφ₀_inner : ∑ k : d₂, star (φ₀ k) * φ₀ k = 1 := by
    have h : ∀ k : d₂, star (φ₀ k) * φ₀ k = ((‖φ₀ k‖ ^ 2 : ℝ) : ℂ) := by
      intro k; rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [h, ← Complex.ofReal_sum, hφ₀, Complex.ofReal_one]
  have hψ₁_inner : ∑ k : d₂, star (ψ₁ k) * ψ₁ k = 1 := by
    have h : ∀ k : d₂, star (ψ₁ k) * ψ₁ k = ((‖ψ₁ k‖ ^ 2 : ℝ) : ℂ) := by
      intro k; rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [h, ← Complex.ofReal_sum, hψ₁_norm, Complex.ofReal_one]
  -- Define `A : Matrix (Bool × d₁) (d₁ × d₂) ℂ`
  let A : Matrix (Bool × d₁) (d₁ × d₂) ℂ := Matrix.of fun p q ↦
    ((Real.sqrt 2)⁻¹ : ℂ) *
      if p.1 = false then ρ₀.sqrtMat p.2 q.1 * star (φ₀ q.2)
      else ρ₁.sqrtMat p.2 q.1 * star (ψ₁ q.2)
  have hAAH : A * Aᴴ = (dephaseState p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₀ ρ₁)).mat := by
    ext ⟨b₁, i⟩ ⟨b₂, j⟩
    rw [dephaseState_apply]
    simp only [A, gramState, gramFactor, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Fintype.sum_prod_type]
    have h1m2p : ((1 - 2 * p : ℝ) : ℂ) = (f₂ : ℂ) := by simp only [p]; push_cast; ring
    cases b₁ <;> cases b₂
    · simp only [↓reduceIte, one_mul]
      calc ∑ x : d₁, ∑ y : d₂,
              ((Real.sqrt 2 : ℂ)⁻¹) * (ρ₀.sqrtMat i x * star (φ₀ y)) *
                star (((Real.sqrt 2 : ℂ)⁻¹) * (ρ₀.sqrtMat j x * star (φ₀ y)))
          = ∑ x : d₁, (((Real.sqrt 2 : ℂ)⁻¹) * ρ₀.sqrtMat i x *
              star (((Real.sqrt 2 : ℂ)⁻¹) * ρ₀.sqrtMat j x)) * (∑ y : d₂, star (φ₀ y) * φ₀ y) := by
              apply Finset.sum_congr rfl; intro x _
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _
              simp only [star_mul', star_star]; ring
        _ = _ := by rw [hφ₀_inner]; simp
    · simp only [Bool.false_eq_true, ↓reduceIte, h1m2p]
      rw [Finset.mul_sum]
      calc ∑ x : d₁, ∑ y : d₂,
              ((Real.sqrt 2 : ℂ)⁻¹) * (ρ₀.sqrtMat i x * star (φ₀ y)) *
                star (((Real.sqrt 2 : ℂ)⁻¹) * (ρ₁.sqrtMat j x * star (ψ₁ y)))
          = ∑ x : d₁, (((Real.sqrt 2 : ℂ)⁻¹) * ρ₀.sqrtMat i x *
              star (((Real.sqrt 2 : ℂ)⁻¹) * ρ₁.sqrtMat j x)) * (∑ y : d₂, star (φ₀ y) * ψ₁ y) := by
              apply Finset.sum_congr rfl; intro x _
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _
              simp only [star_mul', star_star]; ring
        _ = _ := by rw [hoverlap]; apply Finset.sum_congr rfl; intro x _; simp only [Bool.true_eq_false, ↓reduceIte]; ring
    · simp only [Bool.true_eq_false, ↓reduceIte, h1m2p]
      rw [Finset.mul_sum]
      calc ∑ x : d₁, ∑ y : d₂,
              ((Real.sqrt 2 : ℂ)⁻¹) * (ρ₁.sqrtMat i x * star (ψ₁ y)) *
                star (((Real.sqrt 2 : ℂ)⁻¹) * (ρ₀.sqrtMat j x * star (φ₀ y)))
          = ∑ x : d₁, (((Real.sqrt 2 : ℂ)⁻¹) * ρ₁.sqrtMat i x *
              star (((Real.sqrt 2 : ℂ)⁻¹) * ρ₀.sqrtMat j x)) * (∑ y : d₂, star (ψ₁ y) * φ₀ y) := by
              apply Finset.sum_congr rfl; intro x _
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _
              simp only [star_mul', star_star]; ring
        _ = _ := by rw [hoverlap_conj]; apply Finset.sum_congr rfl; intro x _; ring
    · simp only [↓reduceIte, one_mul]
      calc ∑ x : d₁, ∑ y : d₂,
              ((Real.sqrt 2 : ℂ)⁻¹) * (ρ₁.sqrtMat i x * star (ψ₁ y)) *
                star (((Real.sqrt 2 : ℂ)⁻¹) * (ρ₁.sqrtMat j x * star (ψ₁ y)))
          = ∑ x : d₁, (((Real.sqrt 2 : ℂ)⁻¹) * ρ₁.sqrtMat i x *
              star (((Real.sqrt 2 : ℂ)⁻¹) * ρ₁.sqrtMat j x)) * (∑ y : d₂, star (ψ₁ y) * ψ₁ y) := by
              apply Finset.sum_congr rfl; intro x _
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _
              simp only [star_mul', star_star]; ring
        _ = _ := by rw [hψ₁_inner]; simp
  have hAHA : Aᴴ * A = (DensityOp.midpoint
      (DensityOp.tensor ρ₀ (pureState φ₀ hφ₀))
      (DensityOp.tensor ρ₁ (pureState φ₁ hφ₁))).mat := by
    ext ⟨i₁, k₁⟩ ⟨i₂, k₂⟩
    simp only [A, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
      DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, pureState,
      Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul]
    have h0 : ∑ x : d₁, star (ρ₀.sqrtMat x i₁) * ρ₀.sqrtMat x i₂ = ρ₀.mat i₁ i₂ := by
      have h := congr_fun (congr_fun ρ₀.sqrtMat_mul_self i₁) i₂
      rw [← h, Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro x _
      have hh := congr_fun (congr_fun ρ₀.sqrtMat_isHermitian.eq i₁) x
      simp only [Matrix.conjTranspose_apply] at hh; rw [hh]
    have h1 : ∑ x : d₁, star (ρ₁.sqrtMat x i₁) * ρ₁.sqrtMat x i₂ = ρ₁.mat i₁ i₂ := by
      have h := congr_fun (congr_fun ρ₁.sqrtMat_mul_self i₁) i₂
      rw [← h, Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro x _
      have hh := congr_fun (congr_fun ρ₁.sqrtMat_isHermitian.eq i₁) x
      simp only [Matrix.conjTranspose_apply] at hh; rw [hh]
    have hsum0 : (∑ x : d₁, star (((Real.sqrt 2 : ℂ)⁻¹) * (ρ₀.sqrtMat x i₁ * star (φ₀ k₁))) *
        (((Real.sqrt 2 : ℂ)⁻¹) * (ρ₀.sqrtMat x i₂ * star (φ₀ k₂)))) =
        (1 / 2 : ℂ) * (ρ₀.mat i₁ i₂ * (φ₀ k₁ * star (φ₀ k₂))) := by
      rw [← h0, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      simp only [star_mul', star_star]
      calc star ((Real.sqrt 2 : ℂ)⁻¹) * (star (ρ₀.sqrtMat x i₁) * φ₀ k₁) *
            (((Real.sqrt 2 : ℂ)⁻¹) * (ρ₀.sqrtMat x i₂ * star (φ₀ k₂)))
          = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
              (star (ρ₀.sqrtMat x i₁) * ρ₀.sqrtMat x i₂ * (φ₀ k₁ * star (φ₀ k₂))) := by ring
        _ = (1 / 2 : ℂ) * (star (ρ₀.sqrtMat x i₁) * ρ₀.sqrtMat x i₂ * (φ₀ k₁ * star (φ₀ k₂))) := by
              rw [hsq2]
    have hsum1 : (∑ x : d₁, star (((Real.sqrt 2 : ℂ)⁻¹) * (ρ₁.sqrtMat x i₁ * star (ψ₁ k₁))) *
        (((Real.sqrt 2 : ℂ)⁻¹) * (ρ₁.sqrtMat x i₂ * star (ψ₁ k₂)))) =
        (1 / 2 : ℂ) * (ρ₁.mat i₁ i₂ * (φ₁ k₁ * star (φ₁ k₂))) := by
      rw [← h1, ← hψ₁_ketbra k₁ k₂, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      simp only [star_mul', star_star]
      calc star ((Real.sqrt 2 : ℂ)⁻¹) * (star (ρ₁.sqrtMat x i₁) * ψ₁ k₁) *
            (((Real.sqrt 2 : ℂ)⁻¹) * (ρ₁.sqrtMat x i₂ * star (ψ₁ k₂)))
          = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
              (star (ρ₁.sqrtMat x i₁) * ρ₁.sqrtMat x i₂ * (ψ₁ k₁ * star (ψ₁ k₂))) := by ring
        _ = (1 / 2 : ℂ) * (star (ρ₁.sqrtMat x i₁) * ρ₁.sqrtMat x i₂ * (ψ₁ k₁ * star (ψ₁ k₂))) := by
              rw [hsq2]
    rw [hsum0, hsum1]; push_cast; ring
  have hcp : (DensityOp.midpoint
        (DensityOp.tensor ρ₀ (pureState φ₀ hφ₀))
        (DensityOp.tensor ρ₁ (pureState φ₁ hφ₁))).mat.charpoly *
      Polynomial.X ^ Fintype.card (Bool × d₁) =
      (dephaseState p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₀ ρ₁)).mat.charpoly *
        Polynomial.X ^ Fintype.card (d₁ × d₂) := by
    have h := (charpoly_mul_conjTranspose_eq A).symm
    rw [hAAH, hAHA] at h
    exact h
  have hpart1 : vonNeumannEntropy (DensityOp.midpoint
        (DensityOp.tensor ρ₀ (pureState φ₀ hφ₀))
        (DensityOp.tensor ρ₁ (pureState φ₁ hφ₁))) =
      vonNeumannEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₀ ρ₁)) := by
    unfold vonNeumannEntropy DensityOp.eigvals
    congr 1
    exact spectral_sum_eq_of_charpoly_mul_X_pow
      (DensityOp.midpoint (DensityOp.tensor ρ₀ (pureState φ₀ hφ₀))
        (DensityOp.tensor ρ₁ (pureState φ₁ hφ₁))).isHermitian
      (dephaseState p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₀ ρ₁)).isHermitian hcp (by simp [Real.negMulLog])
  exact ⟨hpart1, hpart2, hpart3, hpart4, hcp⟩

end PolarCodes
