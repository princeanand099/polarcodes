/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.Bhattacharyya

/-!
# Renes' Channel Duality and Canonical Channels (Proposition 2.2 & Eq. 2.9)

This module formalizes Renes' dual channel `W.dual` for any binary-input c-q channel `W`,
together with:
- **(D1)** `H(W) + H(W⊥) = 1` (`prop_2_2_D1`)
- **Eq. (2.9)** `H(W₁ ⊠ W₂) = H(W₁) + H(W₂) - 1 + H(W₁⊥ ⊠ W₂⊥)` (`checkCombine_duality`)
- **(D2)** `H((W₁ ⊠ W₂)⊥) = H(W₁⊥ ⊛ W₂⊥)` and `H((W₁ ⊛ W₂)⊥) = H(W₁⊥ ⊠ W₂⊥)` (`prop_2_2_D2`)
- Canonical channels `bscChannel`, `pureChannel`, `becChannel` and **(D3)** (`prop_2_2_D3`).
-/

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodes

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-! ### Renes' Dual Channel `W⊥` -/

/-- Renes' dual channel `W⊥ : {0, 1} → D(ℂ² ⊗ H)` associated to `W : {0, 1} → D(H)`:
`W⊥(0) = Ψ₁ = ½ [[ρ₀, √ρ₀√ρ₁], [√ρ₁√ρ₀, ρ₁]]`, `W⊥(1) = (Z ⊗ I) Ψ₁ (Z ⊗ I)`. -/
noncomputable def CQChannel.dual (W : CQChannel d) : CQChannel (Bool × d) where
  out
    | false => gramState (W.out false) (W.out true)
    | true => DensityOp.conjUnitary (pauliZTensorI d) (gramState (W.out false) (W.out true))

/-- **Proposition 2.2 (D1)**: `H(W) + H(W⊥) = 1` for every binary-input c-q channel `W`. -/
theorem prop_2_2_D1 (W : CQChannel d) :
    W.condEntropy + W.dual.condEntropy = 1 := by
  unfold CQChannel.condEntropy CQChannel.dual
  have hdeph := dephaseCoherence_eq_qjs 0 le_rfl (by norm_num) (gramState (W.out false) (W.out true))
  have h0 : dephaseState 0 le_rfl (by norm_num) (gramState (W.out false) (W.out true)) =
      gramState (W.out false) (W.out true) := by
    cases h : dephaseState 0 le_rfl (by norm_num) (gramState (W.out false) (W.out true))
    cases h' : gramState (W.out false) (W.out true)
    have hmat := dephaseState_zero (gramState (W.out false) (W.out true))
    rw [h, h'] at hmat
    congr
  rw [h0] at hdeph
  have h4 := (lemma_4_1_gram_dephasing (W.out false) (W.out true)
    (fun _ : Unit ↦ (1 : ℂ)) (fun _ : Unit ↦ (1 : ℂ)) (by simp) (by simp)).2.2.2
  rw [← hdeph, h4]
  ring

/-- **Proposition 2.2 (D1, capacity form)**: `I(W) + I(W⊥) = 1`. -/
theorem prop_2_2_D1_symCapacity (W : CQChannel d) :
    W.symCapacity + W.dual.symCapacity = 1 := by
  have h := prop_2_2_D1 W
  unfold CQChannel.symCapacity CQChannel.condEntropy at *
  linarith

/-! ### Eq. (2.9) and Proposition 2.2 (D2) -/

/-- Hadamard unitary `H ⊗ I` on `Bool × d`. -/
private noncomputable def hadamardTensorI (d : Type*) [Fintype d] [DecidableEq d] :
    Matrix.unitaryGroup (Bool × d) ℂ :=
  ⟨Matrix.of fun p q ↦
      if p.2 = q.2 then ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = true ∧ q.1 = true then -1 else 1) else 0, by
    have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast; ring
    rw [Matrix.mem_unitaryGroup_iff']
    ext ⟨b₁, i₁⟩ ⟨b₂, i₂⟩
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fintype.sum_bool]
    by_cases hi : i₁ = i₂
    · subst hi
      simp only [ite_mul, zero_mul, mul_ite, mul_zero, apply_ite star, star_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Prod.mk.injEq, and_true]
      have hsq2_mul : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
        have h : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
          rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
        calc ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)
            = star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) := by rw [h]
          _ = 1 / 2 := hsq2
      cases b₁ <;> cases b₂ <;> simp [star_mul'] <;> rw [hsq2_mul] <;> ring
    · simp only [Prod.mk.injEq, hi, and_false, ↓reduceIte]
      have h0 : ∀ b : Bool, ∑ x : d,
          star (if x = i₁ then ((Real.sqrt 2 : ℂ)⁻¹) * (if b = true ∧ b₁ = true then -1 else 1) else 0) *
            (if x = i₂ then ((Real.sqrt 2 : ℂ)⁻¹) * (if b = true ∧ b₂ = true then -1 else 1) else 0) = 0 := by
        intro b
        apply Finset.sum_eq_zero; intro x _
        by_cases hx : x = i₁
        · subst hx; simp [hi]
        · simp [hx]
      have ht := h0 true
      have hf := h0 false
      simp only [true_and, eq_self_iff_true] at ht ⊢
      rw [ht, hf, add_zero]⟩

private lemma conjUnitary_pauliZ_gram_apply {α : Type*} [Fintype α] [DecidableEq α]
    (τ₀ τ₁ : DensityOp α) (x y : Bool × α) :
    (DensityOp.conjUnitary (pauliZTensorI α) (gramState τ₀ τ₁)).mat x y =
      (if x.1 = false then (1 : ℂ) else -1) * (gramState τ₀ τ₁).mat x y *
        (if y.1 = false then (1 : ℂ) else -1) := by
  simp only [DensityOp.conjUnitary, pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.star_apply]
  rw [Finset.sum_eq_single y]
  · rw [Finset.sum_eq_single x]
    · cases y.1 <;> simp
    · intro z _ hz; simp [Ne.symm hz]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro z _ hz; simp [hz, Ne.symm hz]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma gramFactor_inner_same {α : Type*} [Fintype α] [DecidableEq α]
    (τ₀ τ₁ : DensityOp α) (i j : α) :
    (∑ p : Bool × α, star (gramFactor τ₀ τ₁ p i) * gramFactor τ₀ τ₁ p j) =
      (DensityOp.midpoint τ₀ τ₁).mat i j := by
  have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  simp only [gramFactor, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    ↓reduceIte, Bool.true_eq_false, DensityOp.midpoint, DensityOp.mix, Matrix.add_apply,
    Matrix.smul_apply, Complex.real_smul]
  have hterm : ∀ (τ : DensityOp α),
      (∑ k : α, star (((Real.sqrt 2 : ℂ)⁻¹) * τ.sqrtMat k i) * (((Real.sqrt 2 : ℂ)⁻¹) * τ.sqrtMat k j)) =
        (1 / 2 : ℂ) * τ.mat i j := by
    intro τ
    have hm := congr_fun (congr_fun τ.sqrtMat_mul_self i) j
    rw [← hm, Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    have hh := congr_fun (congr_fun τ.sqrtMat_isHermitian.eq i) k
    simp only [Matrix.conjTranspose_apply] at hh
    rw [star_mul', hh]
    calc _ = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (τ.sqrtMat i k * τ.sqrtMat k j) := by ring
      _ = (1 / 2 : ℂ) * (τ.sqrtMat i k * τ.sqrtMat k j) := by rw [hsq2]
  rw [hterm τ₀, hterm τ₁]; push_cast; ring

private lemma gramFactor_inner_diff {α : Type*} [Fintype α] [DecidableEq α]
    (τ₀ τ₁ : DensityOp α) (i j : α) :
    (∑ p : Bool × α, star (gramFactor τ₀ τ₁ p i) *
        ((if p.1 = false then (1 : ℂ) else -1) * gramFactor τ₀ τ₁ p j)) =
      (1 / 2 : ℂ) * (τ₀.mat i j - τ₁.mat i j) := by
  have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  simp only [gramFactor, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    ↓reduceIte, Bool.true_eq_false, one_mul, neg_mul, mul_neg, Finset.sum_neg_distrib]
  have hterm : ∀ (τ : DensityOp α),
      (∑ k : α, star (((Real.sqrt 2 : ℂ)⁻¹) * τ.sqrtMat k i) * (((Real.sqrt 2 : ℂ)⁻¹) * τ.sqrtMat k j)) =
        (1 / 2 : ℂ) * τ.mat i j := by
    intro τ
    have hm := congr_fun (congr_fun τ.sqrtMat_mul_self i) j
    rw [← hm, Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    have hh := congr_fun (congr_fun τ.sqrtMat_isHermitian.eq i) k
    simp only [Matrix.conjTranspose_apply] at hh
    rw [star_mul', hh]
    calc _ = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (τ.sqrtMat i k * τ.sqrtMat k j) := by ring
      _ = (1 / 2 : ℂ) * (τ.sqrtMat i k * τ.sqrtMat k j) := by rw [hsq2]
  rw [hterm τ₀, hterm τ₁]; ring

/-- **Eq. (2.9) (Check-Node Duality Identity)**:
`H(W₁ ⊠ W₂) = H(W₁) + H(W₂) - 1 + H(W₁⊥ ⊠ W₂⊥)` for all independent binary-input c-q channels. -/
theorem checkCombine_duality (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    (CQChannel.checkCombine W₁ W₂).condEntropy =
      W₁.condEntropy + W₂.condEntropy - 1 +
        (CQChannel.checkCombine W₁.dual W₂.dual).condEntropy := by
  set ρ₀ := W₁.out false
  set ρ₁ := W₁.out true
  set σ₀ := W₂.out false
  set σ₁ := W₂.out true
  set Ψ₁ := gramState ρ₀ ρ₁
  set Ψ₂ := gramState σ₀ σ₁
  set Ψ1_tilde := DensityOp.conjUnitary (pauliZTensorI d₁) Ψ₁
  set Ψ2_tilde := DensityOp.conjUnitary (pauliZTensorI d₂) Ψ₂
  -- Step 1: `(W₁⊥ ⊠ W₂⊥)(1)` is unitarily equivalent to `(W₁⊥ ⊠ W₂⊥)(0)` via `(Z ⊗ I) ⊗ I`
  let Z1I2 : Matrix.unitaryGroup ((Bool × d₁) × (Bool × d₂)) ℂ :=
    ⟨Matrix.diagonal (fun p ↦ if p.1.1 = false then (1 : ℂ) else -1), by
      rw [Matrix.mem_unitaryGroup_iff]
      ext p q
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply, Matrix.one_apply]
      by_cases hpq : p = q
      · subst hpq; simp only [↓reduceIte, Finset.sum_ite_eq', Finset.mem_univ]
        cases p.1.1 <;> simp
      · simp only [hpq, ↓reduceIte]
        apply Finset.sum_eq_zero; intro r _
        by_cases h1 : p = r
        · subst h1; simp [hpq, Ne.symm hpq]
        · simp [h1]⟩
  have hconj_out : (DensityOp.conjUnitary Z1I2 ((CQChannel.checkCombine W₁.dual W₂.dual).out false)).mat =
      ((CQChannel.checkCombine W₁.dual W₂.dual).out true).mat := by
    ext ⟨⟨a₁, i₁⟩, ⟨a₂, i₂⟩⟩ ⟨⟨b₁, j₁⟩, ⟨b₂, j₂⟩⟩
    have hZ1I2_apply : ∀ (M : Matrix ((Bool × d₁) × (Bool × d₂)) ((Bool × d₁) × (Bool × d₂)) ℂ)
        (p q : (Bool × d₁) × (Bool × d₂)),
        ((Z1I2 : Matrix ((Bool × d₁) × (Bool × d₂)) ((Bool × d₁) × (Bool × d₂)) ℂ) * M * star (Z1I2 : Matrix ((Bool × d₁) × (Bool × d₂)) ((Bool × d₁) × (Bool × d₂)) ℂ)) p q =
          (if p.1.1 = false then (1 : ℂ) else -1) * M p q * (if q.1.1 = false then (1 : ℂ) else -1) := by
      intro M p q
      simp only [Z1I2, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply]
      rw [Finset.sum_eq_single q]
      · rw [Finset.sum_eq_single p]
        · cases q.1.1 <;> simp
        · intro y _ hy; simp [Ne.symm hy]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro x _ hx; simp [hx, Ne.symm hx]
      · intro h; exact absurd (Finset.mem_univ _) h
    change ((Z1I2 : Matrix ((Bool × d₁) × (Bool × d₂)) ((Bool × d₁) × (Bool × d₂)) ℂ) * ((CQChannel.checkCombine W₁.dual W₂.dual).out false).mat *
        star (Z1I2 : Matrix ((Bool × d₁) × (Bool × d₂)) ((Bool × d₁) × (Bool × d₂)) ℂ)) _ _ = _
    rw [hZ1I2_apply]
    simp only [CQChannel.checkCombine, Bool.not_false, Bool.not_true, CQChannel.dual,
      DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, Complex.real_smul]
    rw [conjUnitary_pauliZ_gram_apply (W₁.out false) (W₁.out true) (a₁, i₁) (b₁, j₁),
      conjUnitary_pauliZ_gram_apply (W₂.out false) (W₂.out true) (a₂, i₂) (b₂, j₂)]
    cases a₁ <;> cases b₁ <;> cases a₂ <;> cases b₂ <;> simp <;> ring
  have hS_dual_eq : vonNeumannEntropy ((CQChannel.checkCombine W₁.dual W₂.dual).out true) =
      vonNeumannEntropy ((CQChannel.checkCombine W₁.dual W₂.dual).out false) := by
    rw [← vonNeumannEntropy_eq_of_mat_eq hconj_out, vonNeumannEntropy_conjUnitary]
  -- Step 2: Compute `S((W₁⊥ ⊠ W₂⊥)(0)) = 1 + ½ (S((W₁ ⊠ W₂)(0)) + S((W₁ ⊠ W₂)(1)))`
  -- Factor `(W₁⊥ ⊠ W₂⊥)(0) = M * Mᴴ` with `M : ((Bool × d₁) × (Bool × d₂)) × (Bool × (d₁ × d₂))`
  let A₁ := gramFactor ρ₀ ρ₁
  let A₂ := gramFactor σ₀ σ₁
  let Z1A1 : Matrix (Bool × d₁) d₁ ℂ := Matrix.of fun p k ↦
    (if p.1 = false then (1 : ℂ) else -1) * A₁ p k
  let Z2A2 : Matrix (Bool × d₂) d₂ ℂ := Matrix.of fun p k ↦
    (if p.1 = false then (1 : ℂ) else -1) * A₂ p k
  let M : Matrix ((Bool × d₁) × (Bool × d₂)) (Bool × (d₁ × d₂)) ℂ := Matrix.of fun p q ↦
    ((Real.sqrt 2 : ℂ)⁻¹) *
      if q.1 = false then A₁ p.1 q.2.1 * A₂ p.2 q.2.2
      else Z1A1 p.1 q.2.1 * Z2A2 p.2 q.2.2
  have hsq2' : ((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [mul_comm, hsq2']
  have hMMH : M * Mᴴ = ((CQChannel.checkCombine W₁.dual W₂.dual).out false).mat := by
    ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
    simp only [M, CQChannel.checkCombine, Bool.not_false, Bool.not_true, CQChannel.dual,
      DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul,
      Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false]
    rw [conjUnitary_pauliZ_gram_apply (W₁.out false) (W₁.out true) p₁ q₁,
      conjUnitary_pauliZ_gram_apply (W₂.out false) (W₂.out true) p₂ q₂]
    have hprod_f : (∑ k₁ : d₁, ∑ k₂ : d₂,
        ((Real.sqrt 2 : ℂ)⁻¹) * (A₁ p₁ k₁ * A₂ p₂ k₂) *
          star (((Real.sqrt 2 : ℂ)⁻¹) * (A₁ q₁ k₁ * A₂ q₂ k₂))) =
        (1 / 2 : ℂ) * ((gramState ρ₀ ρ₁).mat p₁ q₁ * (gramState σ₀ σ₁).mat p₂ q₂) := by
      simp only [gramState, A₁, A₂, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k₁ _
      apply Finset.sum_congr rfl; intro k₂ _
      simp only [star_mul']
      calc _ = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) *
              (gramFactor ρ₀ ρ₁ p₁ k₁ * star (gramFactor ρ₀ ρ₁ q₁ k₁) *
                (gramFactor σ₀ σ₁ p₂ k₂ * star (gramFactor σ₀ σ₁ q₂ k₂))) := by ring
        _ = (1 / 2 : ℂ) * (gramFactor ρ₀ ρ₁ p₁ k₁ * star (gramFactor ρ₀ ρ₁ q₁ k₁) *
              (gramFactor σ₀ σ₁ p₂ k₂ * star (gramFactor σ₀ σ₁ q₂ k₂))) := by rw [hsq2']
    have hprod_t : (∑ k₁ : d₁, ∑ k₂ : d₂,
        ((Real.sqrt 2 : ℂ)⁻¹) * (Z1A1 p₁ k₁ * Z2A2 p₂ k₂) *
          star (((Real.sqrt 2 : ℂ)⁻¹) * (Z1A1 q₁ k₁ * Z2A2 q₂ k₂))) =
        (1 / 2 : ℂ) * (((if p₁.1 = false then (1 : ℂ) else -1) * (gramState ρ₀ ρ₁).mat p₁ q₁ *
            (if q₁.1 = false then (1 : ℂ) else -1)) *
          ((if p₂.1 = false then (1 : ℂ) else -1) * (gramState σ₀ σ₁).mat p₂ q₂ *
            (if q₂.1 = false then (1 : ℂ) else -1))) := by
      simp only [Z1A1, Z2A2, Matrix.of_apply, gramState, A₁, A₂, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k₁ _
      apply Finset.sum_congr rfl; intro k₂ _
      have hs1 : star (if q₁.1 = false then (1 : ℂ) else -1) = if q₁.1 = false then (1 : ℂ) else -1 := by
        cases q₁.1 <;> simp
      have hs2 : star (if q₂.1 = false then (1 : ℂ) else -1) = if q₂.1 = false then (1 : ℂ) else -1 := by
        cases q₂.1 <;> simp
      simp only [star_mul', hs1, hs2]
      calc _ = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) *
              ((if p₁.1 = false then (1 : ℂ) else -1) * (gramFactor ρ₀ ρ₁ p₁ k₁ * star (gramFactor ρ₀ ρ₁ q₁ k₁)) *
                (if q₁.1 = false then (1 : ℂ) else -1) *
                ((if p₂.1 = false then (1 : ℂ) else -1) * (gramFactor σ₀ σ₁ p₂ k₂ * star (gramFactor σ₀ σ₁ q₂ k₂)) *
                  (if q₂.1 = false then (1 : ℂ) else -1))) := by ring
        _ = _ := by rw [hsq2']
    rw [hprod_f, hprod_t]; push_cast; ring
  -- Now show `(H ⊗ I) (Mᴴ M) (H ⊗ I) = ½ |0⟩⟨0| ⊗ (W₁⊠W₂)(0) + ½ |1⟩⟨1| ⊗ (W₁⊠W₂)(1)`
  let B_blk : DensityOp (Bool × (d₁ × d₂)) :=
    DensityOp.midpoint
      (DensityOp.tensor (CQChannel.ketBraBool false) ((CQChannel.checkCombine W₁ W₂).out false))
      (DensityOp.tensor (CQChannel.ketBraBool true) ((CQChannel.checkCombine W₁ W₂).out true))
  have hMHM_entries : ∀ (a b : Bool) (i₁ j₁ : d₁) (i₂ j₂ : d₂),
      (Mᴴ * M) (a, (i₁, i₂)) (b, (j₁, j₂)) =
        if a = b then
          (1 / 2 : ℂ) * ((DensityOp.midpoint ρ₀ ρ₁).mat i₁ j₁ * (DensityOp.midpoint σ₀ σ₁).mat i₂ j₂)
        else
          (1 / 2 : ℂ) * (((1 / 2 : ℂ) * (ρ₀.mat i₁ j₁ - ρ₁.mat i₁ j₁)) *
            ((1 / 2 : ℂ) * (σ₀.mat i₂ j₂ - σ₁.mat i₂ j₂))) := by
    intro a b i₁ j₁ i₂ j₂
    simp only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [Fintype.sum_prod_type]
    cases a <;> cases b
    · simp only [↓reduceIte]
      calc ∑ x₁ : Bool × d₁, ∑ x₂ : Bool × d₂,
              star (((Real.sqrt 2 : ℂ)⁻¹) * (A₁ x₁ i₁ * A₂ x₂ i₂)) *
                (((Real.sqrt 2 : ℂ)⁻¹) * (A₁ x₁ j₁ * A₂ x₂ j₂))
          = (1 / 2 : ℂ) * ((∑ x₁ : Bool × d₁, star (A₁ x₁ i₁) * A₁ x₁ j₁) *
              (∑ x₂ : Bool × d₂, star (A₂ x₂ i₂) * A₂ x₂ j₂)) := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              conv_rhs => rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro x₁ _
              apply Finset.sum_congr rfl; intro x₂ _
              simp only [star_mul']
              calc _ = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
                      (star (A₁ x₁ i₁) * A₁ x₁ j₁ * (star (A₂ x₂ i₂) * A₂ x₂ j₂)) := by ring
                _ = _ := by rw [hsq2]
        _ = _ := by rw [gramFactor_inner_same ρ₀ ρ₁, gramFactor_inner_same σ₀ σ₁]
    · simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Z1A1, Z2A2, Matrix.of_apply]
      calc ∑ x₁ : Bool × d₁, ∑ x₂ : Bool × d₂,
              star (((Real.sqrt 2 : ℂ)⁻¹) * (A₁ x₁ i₁ * A₂ x₂ i₂)) *
                (((Real.sqrt 2 : ℂ)⁻¹) * (((if x₁.1 = false then (1 : ℂ) else -1) * A₁ x₁ j₁) *
                  ((if x₂.1 = false then (1 : ℂ) else -1) * A₂ x₂ j₂)))
          = (1 / 2 : ℂ) * ((∑ x₁ : Bool × d₁, star (A₁ x₁ i₁) *
                ((if x₁.1 = false then (1 : ℂ) else -1) * A₁ x₁ j₁)) *
              (∑ x₂ : Bool × d₂, star (A₂ x₂ i₂) *
                ((if x₂.1 = false then (1 : ℂ) else -1) * A₂ x₂ j₂))) := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              conv_rhs => rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro x₁ _
              apply Finset.sum_congr rfl; intro x₂ _
              simp only [star_mul']
              calc _ = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
                      (star (A₁ x₁ i₁) * ((if x₁.1 = false then (1 : ℂ) else -1) * A₁ x₁ j₁) *
                        (star (A₂ x₂ i₂) * ((if x₂.1 = false then (1 : ℂ) else -1) * A₂ x₂ j₂))) := by ring
                _ = _ := by rw [hsq2]
        _ = _ := by rw [gramFactor_inner_diff ρ₀ ρ₁, gramFactor_inner_diff σ₀ σ₁]
    · simp only [Bool.true_eq_false, ↓reduceIte, Z1A1, Z2A2, Matrix.of_apply]
      calc ∑ x₁ : Bool × d₁, ∑ x₂ : Bool × d₂,
              star (((Real.sqrt 2 : ℂ)⁻¹) * (((if x₁.1 = false then (1 : ℂ) else -1) * A₁ x₁ i₁) *
                  ((if x₂.1 = false then (1 : ℂ) else -1) * A₂ x₂ i₂))) *
                (((Real.sqrt 2 : ℂ)⁻¹) * (A₁ x₁ j₁ * A₂ x₂ j₂))
          = (1 / 2 : ℂ) * ((∑ x₁ : Bool × d₁, star (A₁ x₁ i₁) *
                ((if x₁.1 = false then (1 : ℂ) else -1) * A₁ x₁ j₁)) *
              (∑ x₂ : Bool × d₂, star (A₂ x₂ i₂) *
                ((if x₂.1 = false then (1 : ℂ) else -1) * A₂ x₂ j₂))) := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              conv_rhs => rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro x₁ _
              apply Finset.sum_congr rfl; intro x₂ _
              have hs1 : star (if x₁.1 = false then (1 : ℂ) else -1) = if x₁.1 = false then (1 : ℂ) else -1 := by
                cases x₁.1 <;> simp
              have hs2 : star (if x₂.1 = false then (1 : ℂ) else -1) = if x₂.1 = false then (1 : ℂ) else -1 := by
                cases x₂.1 <;> simp
              simp only [star_mul', hs1, hs2]
              calc _ = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
                      (star (A₁ x₁ i₁) * ((if x₁.1 = false then (1 : ℂ) else -1) * A₁ x₁ j₁) *
                        (star (A₂ x₂ i₂) * ((if x₂.1 = false then (1 : ℂ) else -1) * A₂ x₂ j₂))) := by ring
                _ = _ := by rw [hsq2]
        _ = _ := by rw [gramFactor_inner_diff ρ₀ ρ₁, gramFactor_inner_diff σ₀ σ₁]
    · simp only [Bool.true_eq_false, ↓reduceIte, Z1A1, Z2A2, Matrix.of_apply]
      calc ∑ x₁ : Bool × d₁, ∑ x₂ : Bool × d₂,
              star (((Real.sqrt 2 : ℂ)⁻¹) * (((if x₁.1 = false then (1 : ℂ) else -1) * A₁ x₁ i₁) *
                  ((if x₂.1 = false then (1 : ℂ) else -1) * A₂ x₂ i₂))) *
                (((Real.sqrt 2 : ℂ)⁻¹) * (((if x₁.1 = false then (1 : ℂ) else -1) * A₁ x₁ j₁) *
                  ((if x₂.1 = false then (1 : ℂ) else -1) * A₂ x₂ j₂)))
          = (1 / 2 : ℂ) * ((∑ x₁ : Bool × d₁, star (A₁ x₁ i₁) * A₁ x₁ j₁) *
              (∑ x₂ : Bool × d₂, star (A₂ x₂ i₂) * A₂ x₂ j₂)) := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              conv_rhs => rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro x₁ _
              apply Finset.sum_congr rfl; intro x₂ _
              have hs1 : star (if x₁.1 = false then (1 : ℂ) else -1) * (if x₁.1 = false then (1 : ℂ) else -1) = 1 := by
                cases x₁.1 <;> simp
              have hs2 : star (if x₂.1 = false then (1 : ℂ) else -1) * (if x₂.1 = false then (1 : ℂ) else -1) = 1 := by
                cases x₂.1 <;> simp
              simp only [star_mul']
              calc _ = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
                      (star (if x₁.1 = false then (1 : ℂ) else -1) * (if x₁.1 = false then (1 : ℂ) else -1)) *
                      (star (if x₂.1 = false then (1 : ℂ) else -1) * (if x₂.1 = false then (1 : ℂ) else -1)) *
                      (star (A₁ x₁ i₁) * A₁ x₁ j₁ * (star (A₂ x₂ i₂) * A₂ x₂ j₂)) := by ring
                _ = _ := by rw [hsq2, hs1, hs2, mul_one, mul_one]
        _ = _ := by rw [gramFactor_inner_same ρ₀ ρ₁, gramFactor_inner_same σ₀ σ₁]
  set H_u := hadamardTensorI (d₁ × d₂)
  set K : Matrix (Bool × (d₁ × d₂)) (Bool × (d₁ × d₂)) ℂ := Mᴴ * M
  have hK_entries : ∀ (a b : Bool) (i₁ j₁ : d₁) (i₂ j₂ : d₂),
      K (a, (i₁, i₂)) (b, (j₁, j₂)) =
        if a = b then (1 / 2 : ℂ) * ((ρ₀.midpoint ρ₁).mat i₁ j₁ * (σ₀.midpoint σ₁).mat i₂ j₂)
        else (1 / 2 : ℂ) * (((1 / 2 : ℂ) * (ρ₀.mat i₁ j₁ - ρ₁.mat i₁ j₁)) *
          ((1 / 2 : ℂ) * (σ₀.mat i₂ j₂ - σ₁.mat i₂ j₂))) := hMHM_entries
  have hHMHMH : (H_u : Matrix (Bool × (d₁ × d₂)) (Bool × (d₁ × d₂)) ℂ) * (Mᴴ * M) *
      star (H_u : Matrix (Bool × (d₁ × d₂)) (Bool × (d₁ × d₂)) ℂ) = B_blk.mat := by
    change (H_u : Matrix (Bool × (d₁ × d₂)) (Bool × (d₁ × d₂)) ℂ) * K *
        star (H_u : Matrix (Bool × (d₁ × d₂)) (Bool × (d₁ × d₂)) ℂ) = B_blk.mat
    ext ⟨a, i₁, i₂⟩ ⟨b, j₁, j₂⟩
    simp only [H_u, hadamardTensorI, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Prod.mk.injEq, ite_and,
      ite_mul, zero_mul, mul_ite, mul_zero, apply_ite star, star_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    simp only [hK_entries, B_blk, CQChannel.checkCombine, CQChannel.ketBraBool,
      DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, Bool.not_false, Bool.not_true,
      Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.of_apply,
      Complex.real_smul]
    have hstar_s : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
    have hsq2_mul : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) :=
      calc ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)
          = star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) := by rw [hstar_s]
        _ = (1 / 2 : ℂ) := hsq2
    set r0 := ρ₀.mat i₁ j₁
    set r1 := ρ₁.mat i₁ j₁
    set s0 := σ₀.mat i₂ j₂
    set s1 := σ₁.mat i₂ j₂
    set u := ((Real.sqrt 2 : ℂ)⁻¹)
    have hu2 : u ^ 2 = (1 / 2 : ℂ) := by rw [sq]; exact hsq2_mul
    cases a <;> cases b <;>
      (simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, and_self, and_true, and_false,
        true_and, false_and, mul_one, mul_neg, neg_mul, star_mul', star_neg, star_one, hstar_s,
        one_mul, zero_mul, mul_zero, add_zero, zero_add];
       push_cast; ring_nf; try (rw [hu2]; ring))
  have hS_dual0 : vonNeumannEntropy ((CQChannel.checkCombine W₁.dual W₂.dual).out false) =
      1 + (vonNeumannEntropy ((CQChannel.checkCombine W₁ W₂).out false) +
        vonNeumannEntropy ((CQChannel.checkCombine W₁ W₂).out true)) / 2 := by
    rw [← vonNeumannEntropy_block_midpoint ((CQChannel.checkCombine W₁ W₂).out false)
      ((CQChannel.checkCombine W₁ W₂).out true)]
    unfold vonNeumannEntropy DensityOp.eigvals
    congr 1
    have hcp := charpoly_mul_conjTranspose_eq M
    rw [hMMH] at hcp
    have hcp_H : (Mᴴ * M).charpoly = B_blk.mat.charpoly := by
      rw [← hHMHMH, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
        Unitary.coe_star_mul_self H_u, Matrix.one_mul]
    rw [hcp_H] at hcp
    exact spectral_sum_eq_of_charpoly_mul_X_pow
      ((CQChannel.checkCombine W₁.dual W₂.dual).out false).isHermitian
      B_blk.isHermitian hcp (by simp [Real.negMulLog])
  -- Step 3: Compute `S(midpoint((W₁⊥⊠W₂⊥)(0), (W₁⊥⊠W₂⊥)(1))) = 2 + ½(S(ρ₀)+S(ρ₁)+S(σ₀)+S(σ₁))`
  have hmid_dual : (DensityOp.midpoint
      ((CQChannel.checkCombine W₁.dual W₂.dual).out false)
      ((CQChannel.checkCombine W₁.dual W₂.dual).out true)).mat =
      (DensityOp.tensor
        (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ₁)
        (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ₂)).mat := by
    ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
    simp only [CQChannel.checkCombine, CQChannel.dual, dephaseState, DensityOp.midpoint,
      DensityOp.mix, DensityOp.tensor, Bool.not_false, Bool.not_true, Matrix.add_apply,
      Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul, Ψ₁, Ψ₂]
    push_cast; ring
  have hS_mid_dual : vonNeumannEntropy (DensityOp.midpoint
      ((CQChannel.checkCombine W₁.dual W₂.dual).out false)
      ((CQChannel.checkCombine W₁.dual W₂.dual).out true)) =
      2 + (vonNeumannEntropy ρ₀ + vonNeumannEntropy ρ₁ +
        vonNeumannEntropy σ₀ + vonNeumannEntropy σ₁) / 2 := by
    rw [vonNeumannEntropy_eq_of_mat_eq hmid_dual, vonNeumannEntropy_tensor]
    have h3_1 := (lemma_4_1_gram_dephasing ρ₀ ρ₁ (fun _ : Unit ↦ (1 : ℂ)) (fun _ : Unit ↦ (1 : ℂ))
      (by simp) (by simp)).2.2.1
    have h3_2 := (lemma_4_1_gram_dephasing σ₀ σ₁ (fun _ : Unit ↦ (1 : ℂ)) (fun _ : Unit ↦ (1 : ℂ))
      (by simp) (by simp)).2.2.1
    linarith
  -- Step 4: Combine everything!
  have hmid_orig : (DensityOp.midpoint
      ((CQChannel.checkCombine W₁ W₂).out false)
      ((CQChannel.checkCombine W₁ W₂).out true)).mat =
      (DensityOp.tensor (DensityOp.midpoint ρ₀ ρ₁) (DensityOp.midpoint σ₀ σ₁)).mat := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Bool.not_false, Bool.not_true, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
      Complex.real_smul]
    push_cast; ring
  have hS_mid_orig : vonNeumannEntropy (DensityOp.midpoint
      ((CQChannel.checkCombine W₁ W₂).out false)
      ((CQChannel.checkCombine W₁ W₂).out true)) =
      vonNeumannEntropy (DensityOp.midpoint ρ₀ ρ₁) +
        vonNeumannEntropy (DensityOp.midpoint σ₀ σ₁) := by
    rw [vonNeumannEntropy_eq_of_mat_eq hmid_orig, vonNeumannEntropy_tensor]
  unfold CQChannel.condEntropy qjs
  rw [hS_dual_eq, hS_dual0, hS_mid_dual, hS_mid_orig]
  ring

/-- **Proposition 2.2 (D2)**: Entropic duality of Arıkan's check-node and variable-node transforms:
`H((W₁ ⊠ W₂)⊥) = H(W₁⊥ ⊛ W₂⊥)` and `H((W₁ ⊛ W₂)⊥) = H(W₁⊥ ⊠ W₂⊥)`. -/
theorem prop_2_2_D2 (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    (CQChannel.checkCombine W₁ W₂).dual.condEntropy =
      (CQChannel.varCombine W₁.dual W₂.dual).condEntropy ∧
    (CQChannel.varCombine W₁ W₂).dual.condEntropy =
      (CQChannel.checkCombine W₁.dual W₂.dual).condEntropy := by
  have hD1_1 := prop_2_2_D1 W₁
  have hD1_2 := prop_2_2_D1 W₂
  have hD1_c := prop_2_2_D1 (CQChannel.checkCombine W₁ W₂)
  have hD1_v := prop_2_2_D1 (CQChannel.varCombine W₁ W₂)
  have hcons := entropy_conservation W₁ W₂
  have hcons_d := entropy_conservation W₁.dual W₂.dual
  have hdual := checkCombine_duality W₁ W₂
  constructor <;> linarith

/-! ### Canonical Channels and Proposition 2.2 (D3) -/

/-- Binary symmetric channel `BSC(p)` with crossover probability `p ∈ [0, 1/2]`. -/
def bscChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : CQChannel Bool where
  out
    | false =>
      { mat := Matrix.diagonal (fun b ↦ if b = false then ((1 - p : ℝ) : ℂ) else (p : ℂ))
        posSemidef := by
          rw [Matrix.posSemidef_diagonal_iff]
          intro b; cases b <;> simp only [↓reduceIte, Bool.true_eq_false] <;> exact_mod_cast (by linarith : (0 : ℝ) ≤ _)
        trace_one := by
          simp only [Matrix.trace_diagonal, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false]
          push_cast; ring }
    | true =>
      { mat := Matrix.diagonal (fun b ↦ if b = false then (p : ℂ) else ((1 - p : ℝ) : ℂ))
        posSemidef := by
          rw [Matrix.posSemidef_diagonal_iff]
          intro b; cases b <;> simp only [↓reduceIte, Bool.true_eq_false] <;> exact_mod_cast (by linarith : (0 : ℝ) ≤ _)
        trace_one := by
          simp only [Matrix.trace_diagonal, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false]
          push_cast; ring }

/-- Binary erasure channel `BEC(ε)` with erasure probability `ε ∈ [0, 1]`, outputting on `Fin 3`
(`0 = bit 0`, `1 = bit 1`, `2 = erasure`). -/
def becChannel (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : CQChannel (Fin 3) where
  out
    | false =>
      { mat := Matrix.diagonal (fun i : Fin 3 ↦ match i with | 0 => ((1 - ε : ℝ) : ℂ) | 1 => 0 | 2 => (ε : ℂ))
        posSemidef := by
          rw [Matrix.posSemidef_diagonal_iff]
          intro i; fin_cases i
          · dsimp only; exact_mod_cast (by linarith : (0 : ℝ) ≤ 1 - ε)
          · exact le_rfl
          · dsimp only; exact_mod_cast hε0
        trace_one := by
          simp [Matrix.trace_diagonal, Fin.sum_univ_three] }
    | true =>
      { mat := Matrix.diagonal (fun i : Fin 3 ↦ match i with | 0 => 0 | 1 => ((1 - ε : ℝ) : ℂ) | 2 => (ε : ℂ))
        posSemidef := by
          rw [Matrix.posSemidef_diagonal_iff]
          intro i; fin_cases i
          · exact le_rfl
          · dsimp only; exact_mod_cast (by linarith : (0 : ℝ) ≤ 1 - ε)
          · dsimp only; exact_mod_cast hε0
        trace_one := by
          simp [Matrix.trace_diagonal, Fin.sum_univ_three] }

/-- Pure-state binary c-q channel `Pure(f)` with overlap `f ∈ [0, 1]`:
`|φ₀⟩ = (√((1+f)/2), √((1-f)/2))`, `|φ₁⟩ = (√((1+f)/2), -√((1-f)/2))`. -/
noncomputable def pureChannel (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) : CQChannel Bool where
  out
    | false =>
      pureState (fun b ↦ if b = false then (Real.sqrt ((1 + f) / 2) : ℂ) else (Real.sqrt ((1 - f) / 2) : ℂ))
        (by
          rw [Fintype.sum_bool]
          simp only [↓reduceIte, Bool.true_eq_false, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
            Real.sq_sqrt (by linarith : 0 ≤ (1 + f) / 2), Real.sq_sqrt (by linarith : 0 ≤ (1 - f) / 2)]
          ring)
    | true =>
      pureState (fun b ↦ if b = false then (Real.sqrt ((1 + f) / 2) : ℂ) else -(Real.sqrt ((1 - f) / 2) : ℂ))
        (by
          rw [Fintype.sum_bool]
          simp only [↓reduceIte, Bool.true_eq_false, norm_neg, Complex.norm_real,
            Real.norm_of_nonneg (Real.sqrt_nonneg _),
            Real.sq_sqrt (by linarith : 0 ≤ (1 + f) / 2), Real.sq_sqrt (by linarith : 0 ≤ (1 - f) / 2)]
          ring)

lemma condEntropy_bscChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bscChannel p hp0 hp1).condEntropy = h2 p := by
  have hdiag_S : ∀ (v : Bool → ℝ) (ρ : DensityOp Bool),
      ρ.mat = Matrix.diagonal (Complex.ofReal ∘ v) →
      vonNeumannEntropy ρ = (Real.negMulLog (v true) + Real.negMulLog (v false)) / Real.log 2 := by
    intro v ρ hmat
    have hD : (Matrix.diagonal (Complex.ofReal ∘ v)).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext b; simp
    unfold vonNeumannEntropy DensityOp.eigvals
    congr 1
    trans ∑ b : Bool, Real.negMulLog (hD.eigenvalues b)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow ρ.isHermitian hD (k := 0) (l := 0)
        (by rw [pow_zero, mul_one, mul_one, hmat]) (by simp [Real.negMulLog])
    · rw [spectral_sum_diagonal v hD (by simp [Real.negMulLog]), Fintype.sum_bool]
  have hS0 : vonNeumannEntropy ((bscChannel p hp0 hp1).out false) = h2 p := by
    rw [hdiag_S (fun b ↦ if b = false then 1 - p else p) _ (by
      ext i j; simp only [bscChannel, Matrix.diagonal_apply, Function.comp_apply]
      split_ifs with h1 h2 <;> simp_all), h2_eq_negMulLog]
    simp [add_comm]
  have hS1 : vonNeumannEntropy ((bscChannel p hp0 hp1).out true) = h2 p := by
    rw [hdiag_S (fun b ↦ if b = false then p else 1 - p) _ (by
      ext i j; simp only [bscChannel, Matrix.diagonal_apply, Function.comp_apply]
      split_ifs with h1 h2 <;> simp_all), h2_eq_negMulLog]
    simp; ring
  have hSmid : vonNeumannEntropy (DensityOp.midpoint ((bscChannel p hp0 hp1).out false)
      ((bscChannel p hp0 hp1).out true)) = 1 := by
    rw [hdiag_S (fun _ ↦ 1 / 2) _ (by
      ext i j
      simp only [DensityOp.midpoint, DensityOp.mix, bscChannel, Matrix.add_apply, Matrix.smul_apply,
        Matrix.diagonal_apply, Function.comp_apply, Complex.real_smul]
      cases i <;> cases j <;> simp <;> push_cast <;> ring)]
    unfold Real.negMulLog
    rw [one_div, Real.log_inv]
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp [hlog2]; ring
  unfold CQChannel.condEntropy qjs
  rw [hS0, hS1, hSmid]
  ring

lemma condEntropy_pureChannel (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    (pureChannel f hf0 hf1).condEntropy = 1 - h2 ((1 - f) / 2) := by
  have hS_pure : ∀ (φ : Bool → ℂ) (hφ : ∑ b : Bool, ‖φ b‖ ^ 2 = 1),
      vonNeumannEntropy (pureState φ hφ) = 0 := by
    intro φ hφ
    let M : Matrix Bool Unit ℂ := Matrix.of fun b _ ↦ φ b
    have hMMH : M * Mᴴ = (pureState φ hφ).mat := by
      ext i j; simp [M, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hMHM : Mᴴ * M = Matrix.diagonal (Complex.ofReal ∘ fun _ : Unit ↦ (1 : ℝ)) := by
      ext ⟨⟩ ⟨⟩
      simp only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.diagonal_apply, Function.comp_apply, ↓reduceIte, Complex.ofReal_one]
      have hterm : ∀ b : Bool, star (φ b) * φ b = ((‖φ b‖ ^ 2 : ℝ) : ℂ) := by
        intro b; rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp_rw [hterm, ← Complex.ofReal_sum, hφ, Complex.ofReal_one]
    have hD : (Matrix.diagonal (Complex.ofReal ∘ fun _ : Unit ↦ (1 : ℝ))).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext _; simp
    have hcp := charpoly_mul_conjTranspose_eq M
    rw [hMMH, hMHM] at hcp
    unfold vonNeumannEntropy DensityOp.eigvals
    have hsum : ∑ i : Bool, Real.negMulLog ((pureState φ hφ).isHermitian.eigenvalues i) =
        ∑ _ : Unit, Real.negMulLog (1 : ℝ) := by
      trans ∑ u : Unit, Real.negMulLog (hD.eigenvalues u)
      · exact spectral_sum_eq_of_charpoly_mul_X_pow (pureState φ hφ).isHermitian hD hcp
          (by simp [Real.negMulLog])
      · exact spectral_sum_diagonal (fun _ ↦ 1) hD (by simp [Real.negMulLog])
    rw [hsum]; simp [Real.negMulLog]
  have hS0 : vonNeumannEntropy ((pureChannel f hf0 hf1).out false) = 0 := by
    dsimp only [pureChannel]; exact hS_pure _ _
  have hS1 : vonNeumannEntropy ((pureChannel f hf0 hf1).out true) = 0 := by
    dsimp only [pureChannel]; exact hS_pure _ _
  have hmid : (DensityOp.midpoint ((pureChannel f hf0 hf1).out false)
      ((pureChannel f hf0 hf1).out true)).mat =
      Matrix.diagonal (Complex.ofReal ∘ fun b : Bool ↦ if b = false then (1 + f) / 2 else (1 - f) / 2) := by
    ext i j
    simp only [DensityOp.midpoint, DensityOp.mix, pureChannel, pureState, Matrix.add_apply,
      Matrix.smul_apply, Matrix.of_apply, Matrix.diagonal_apply, Function.comp_apply, Complex.real_smul]
    have h1 : (Real.sqrt ((1 + f) / 2) : ℂ) * star (Real.sqrt ((1 + f) / 2) : ℂ) = (((1 + f) / 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (by linarith)]
    have h2 : (Real.sqrt ((1 - f) / 2) : ℂ) * star (Real.sqrt ((1 - f) / 2) : ℂ) = (((1 - f) / 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (by linarith)]
    cases i <;> cases j <;>
      simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, mul_neg, neg_mul, neg_neg,
        star_neg, h1, h2] <;>
      push_cast <;> ring
  have hD : (Matrix.diagonal (Complex.ofReal ∘ fun b : Bool ↦
      if b = false then (1 + f) / 2 else (1 - f) / 2)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext b; simp
  have hSmid : vonNeumannEntropy (DensityOp.midpoint ((pureChannel f hf0 hf1).out false)
      ((pureChannel f hf0 hf1).out true)) = h2 ((1 - f) / 2) := by
    unfold vonNeumannEntropy DensityOp.eigvals
    rw [h2_eq_negMulLog]
    congr 1
    trans ∑ b : Bool, Real.negMulLog (hD.eigenvalues b)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow
        (DensityOp.midpoint _ _).isHermitian hD (k := 0) (l := 0)
        (by rw [pow_zero, mul_one, mul_one, hmid]) (by simp [Real.negMulLog])
    · rw [spectral_sum_diagonal _ hD (by simp [Real.negMulLog]), Fintype.sum_bool]
      simp only [Bool.true_eq_false, ↓reduceIte]
      have h1m : 1 - (1 - f) / 2 = (1 + f) / 2 := by ring
      rw [h1m]
  unfold CQChannel.condEntropy qjs
  rw [hS0, hS1, hSmid]
  ring

lemma condEntropy_becChannel (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (becChannel ε hε0 hε1).condEntropy = ε := by
  have hdiag_S : ∀ (v : Fin 3 → ℝ) (ρ : DensityOp (Fin 3)),
      ρ.mat = Matrix.diagonal (Complex.ofReal ∘ v) →
      vonNeumannEntropy ρ = (Real.negMulLog (v 0) + Real.negMulLog (v 1) + Real.negMulLog (v 2)) / Real.log 2 := by
    intro v ρ hmat
    have hD : (Matrix.diagonal (Complex.ofReal ∘ v)).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext i; simp
    unfold vonNeumannEntropy DensityOp.eigvals
    congr 1
    trans ∑ i : Fin 3, Real.negMulLog (hD.eigenvalues i)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow ρ.isHermitian hD (k := 0) (l := 0)
        (by rw [pow_zero, mul_one, mul_one, hmat]) (by simp [Real.negMulLog])
    · rw [spectral_sum_diagonal v hD (by simp [Real.negMulLog]), Fin.sum_univ_three]
  have hS0 : vonNeumannEntropy ((becChannel ε hε0 hε1).out false) =
      (Real.negMulLog (1 - ε) + Real.negMulLog ε) / Real.log 2 := by
    rw [hdiag_S ![1 - ε, 0, ε] _ (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [becChannel, Matrix.diagonal_apply])]
    simp [Real.negMulLog]
  have hS1 : vonNeumannEntropy ((becChannel ε hε0 hε1).out true) =
      (Real.negMulLog (1 - ε) + Real.negMulLog ε) / Real.log 2 := by
    rw [hdiag_S ![0, 1 - ε, ε] _ (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [becChannel, Matrix.diagonal_apply])]
    simp [Real.negMulLog]
  have hSmid : vonNeumannEntropy (DensityOp.midpoint ((becChannel ε hε0 hε1).out false)
      ((becChannel ε hε0 hε1).out true)) =
      (Real.negMulLog ((1 - ε) / 2) + Real.negMulLog ((1 - ε) / 2) + Real.negMulLog ε) / Real.log 2 := by
    rw [hdiag_S ![(1 - ε) / 2, (1 - ε) / 2, ε] _ (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [DensityOp.midpoint, DensityOp.mix, becChannel, Matrix.diagonal_apply, Complex.real_smul] <;>
        push_cast <;> ring)]
    rfl
  have hhalf : Real.negMulLog ((1 - ε) / 2) =
      Real.negMulLog (1 - ε) / 2 + (1 - ε) * Real.log 2 / 2 := by
    rw [div_eq_mul_inv, Real.negMulLog_mul]; unfold Real.negMulLog; rw [Real.log_inv]; ring
  unfold CQChannel.condEntropy qjs
  rw [hS0, hS1, hSmid, hhalf]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog2]; ring

/-- **Proposition 2.2 (D3)**: Canonical duality relations for `BSC(p)`, `Pure(1 - 2p)`, and `BEC(ε)`. -/
theorem prop_2_2_D3 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (bscChannel p hp0 (by linarith)).dual.condEntropy =
      (pureChannel (1 - 2 * p) (by linarith) (by linarith)).condEntropy ∧
    (pureChannel (1 - 2 * p) (by linarith) (by linarith)).dual.condEntropy =
      (bscChannel p hp0 (by linarith)).condEntropy ∧
    (becChannel ε hε0 hε1).dual.condEntropy =
      (becChannel (1 - ε) (by linarith) (by linarith)).condEntropy := by
  have h1 := prop_2_2_D1 (bscChannel p hp0 (by linarith))
  have h2 := prop_2_2_D1 (pureChannel (1 - 2 * p) (by linarith) (by linarith))
  have h3 := prop_2_2_D1 (becChannel ε hε0 hε1)
  rw [condEntropy_bscChannel] at h1
  rw [condEntropy_pureChannel] at h2
  rw [condEntropy_becChannel] at h3
  have harg : (1 - (1 - 2 * p)) / 2 = p := by ring
  rw [harg] at h2
  refine ⟨?_, ?_, ?_⟩
  · rw [condEntropy_pureChannel, harg]; linarith
  · rw [condEntropy_bscChannel]; linarith
  · rw [condEntropy_becChannel]; linarith

end PolarCodes
