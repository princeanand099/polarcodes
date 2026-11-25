/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.ChannelEquiv

/-!
# Channel-Level Polarization Duality (Proposition 2.2 D2)

Proves the two polarization-duality channel equivalences of Proposition 2.2 (D2):
- `(W₁ ⊠ W₂)⊥ ≃ W₁⊥ ⊛ W₂⊥` (`prop_2_2_D2_check_channelEquiv`)
- `(W₁ ⊛ W₂)⊥ ≃ W₁⊥ ⊠ W₂⊥` (`prop_2_2_D2_var_channelEquiv`)
at the level of reversible CPTP channel equivalence (`CQChannel.ChannelEquiv`),
from which the entropic equalities follow immediately via `CQChannel.ChannelEquiv.condEntropy_eq`.
-/

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodes

universe u

section ChannelDualityEquiv

private lemma pauliZTensorI_conj_entry {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix (Bool × d) (Bool × d) ℂ) (a₁ a₂ : Bool) (r₁ r₂ : d) :
    ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) * M *
      star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)) (a₁, r₁) (a₂, r₂) =
    (if a₁ = a₂ then (1 : ℂ) else -1) * M (a₁, r₁) (a₂, r₂) := by
  have hstar : star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) =
      (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) := by
    ext ⟨b₁, x₁⟩ ⟨b₂, x₂⟩
    by_cases h : (b₁, x₁) = (b₂, x₂)
    · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      cases b₁ <;> simp [pauliZTensorI, Matrix.star_apply, Matrix.diagonal_apply]
    · simp [pauliZTensorI, Matrix.star_apply, Matrix.diagonal_apply, h, Ne.symm h]
  rw [hstar]
  simp only [pauliZTensorI, Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases a₁ <;> cases a₂ <;> simp

/-- **Proposition 2.2 (D2, Check-Node Channel-Level Duality)**:
`(W₁ ⊠ W₂)⊥ ≃ W₁⊥ ⊛ W₂⊥` as reversible CPTP-equivalent c-q channels. -/
theorem prop_2_2_D2_check_channelEquiv {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    (W₁.checkCombine W₂).dual.ChannelEquiv (W₁.dual.varCombine W₂.dual) := by
  set ρ₀ := W₁.out false
  set ρ₁ := W₁.out true
  set σ₀ := W₂.out false
  set σ₁ := W₂.out true
  have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
  have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  let A₀ : Matrix (d₁ × d₂) (Bool × d₁ × d₂) ℂ :=
    Matrix.of fun (i₁, i₂) (v, j₁, j₂) ↦
      ((Real.sqrt 2 : ℂ)⁻¹) *
        (if v = false then ρ₀.sqrtMat i₁ j₁ * σ₀.sqrtMat i₂ j₂
         else ρ₁.sqrtMat i₁ j₁ * σ₁.sqrtMat i₂ j₂)
  let A₁ : Matrix (d₁ × d₂) (Bool × d₁ × d₂) ℂ :=
    Matrix.of fun (i₁, i₂) (v, j₁, j₂) ↦
      ((Real.sqrt 2 : ℂ)⁻¹) *
        (if v = false then ρ₁.sqrtMat i₁ j₁ * σ₀.sqrtMat i₂ j₂
         else ρ₀.sqrtMat i₁ j₁ * σ₁.sqrtMat i₂ j₂)
  have hsq_prod : ∀ (τ : DensityOp d₁) (η : DensityOp d₂) (i₁ j₁ : d₁) (i₂ j₂ : d₂),
      ∑ k₁ : d₁, ∑ k₂ : d₂,
        (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂)) =
        τ.mat i₁ j₁ * η.mat i₂ j₂ := by
    intro τ η i₁ j₁ i₂ j₂
    have h1 : ∑ k₁ : d₁, τ.sqrtMat i₁ k₁ * star (τ.sqrtMat j₁ k₁) = τ.mat i₁ j₁ := by
      have hsq := congr_fun (congr_fun τ.sqrtMat_mul_self i₁) j₁
      rw [← hsq]; simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro k _
      have hhk : star (τ.sqrtMat j₁ k) = τ.sqrtMat k j₁ := by
        have := congr_fun (congr_fun τ.sqrtMat_isHermitian.eq k) j₁
        simpa [Matrix.conjTranspose_apply] using this
      rw [hhk]
    have h2 : ∑ k₂ : d₂, η.sqrtMat i₂ k₂ * star (η.sqrtMat j₂ k₂) = η.mat i₂ j₂ := by
      have hsq := congr_fun (congr_fun η.sqrtMat_mul_self i₂) j₂
      rw [← hsq]; simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro k _
      have hhk : star (η.sqrtMat j₂ k) = η.sqrtMat k j₂ := by
        have := congr_fun (congr_fun η.sqrtMat_isHermitian.eq k) j₂
        simpa [Matrix.conjTranspose_apply] using this
      rw [hhk]
    calc ∑ k₁ : d₁, ∑ k₂ : d₂,
          (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂))
        = (∑ k₁ : d₁, τ.sqrtMat i₁ k₁ * star (τ.sqrtMat j₁ k₁)) *
          (∑ k₂ : d₂, η.sqrtMat i₂ k₂ * star (η.sqrtMat j₂ k₂)) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro k₁ _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k₂ _
            ring
      _ = τ.mat i₁ j₁ * η.mat i₂ j₂ := by rw [h1, h2]
  have hA₀ : A₀ * A₀ᴴ = ((W₁.checkCombine W₂).out false).mat := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [A₀, CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type,
      Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false, Matrix.add_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, Complex.real_smul, star_mul', hstar2]
    have hl : ∀ (τ : DensityOp d₁) (η : DensityOp d₂),
        ∑ k₁ : d₁, ∑ k₂ : d₂,
          ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
          ((Real.sqrt 2 : ℂ)⁻¹ * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂))) =
        (1 / 2 : ℂ) * (τ.mat i₁ j₁ * η.mat i₂ j₂) := by
      intro τ η
      rw [← hsq_prod τ η i₁ j₁ i₂ j₂, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k₁ _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k₂ _
      calc ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
            ((Real.sqrt 2 : ℂ)⁻¹ * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂)))
          = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
            ((τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂))) := by ring
        _ = _ := by rw [hmul2]
    rw [hl ρ₁ σ₁, hl ρ₀ σ₀]; push_cast; ring
  have hA₁ : A₁ * A₁ᴴ = ((W₁.checkCombine W₂).out true).mat := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [A₁, CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type,
      Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false, Matrix.add_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, Complex.real_smul, star_mul', hstar2]
    have hl : ∀ (τ : DensityOp d₁) (η : DensityOp d₂),
        ∑ k₁ : d₁, ∑ k₂ : d₂,
          ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
          ((Real.sqrt 2 : ℂ)⁻¹ * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂))) =
        (1 / 2 : ℂ) * (τ.mat i₁ j₁ * η.mat i₂ j₂) := by
      intro τ η
      rw [← hsq_prod τ η i₁ j₁ i₂ j₂, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k₁ _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k₂ _
      calc ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
            ((Real.sqrt 2 : ℂ)⁻¹ * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂)))
          = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
            ((τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂))) := by ring
        _ = _ := by rw [hmul2]
    rw [hl ρ₀ σ₁, hl ρ₁ σ₀]; push_cast; ring
  have hstep1 := (dual_isoEquiv_of_purification (W₁.checkCombine W₂) A₀ A₁ hA₀ hA₁).toChannelEquiv
  let W_prod : CQChannel ((Bool × d₁) × (Bool × d₂)) :=
    { out := fun b ↦ DensityOp.tensor (W₁.dual.out b) (W₂.dual.out b) }
  let P : Matrix ((Bool × d₁) × (Bool × d₂)) (Bool × (Bool × d₁ × d₂)) ℂ :=
    Matrix.of fun ((a, r), (c, s)) (u, v, r', s') ↦
      if a = xor u v ∧ c = v ∧ r = r' ∧ s = s' then 1 else 0
  have hP_iso : Pᴴ * P = 1 := by
    ext ⟨u₁, v₁, r₁, s₁⟩ ⟨u₂, v₂, r₂, s₂⟩
    simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
    by_cases h : (u₁, v₁, r₁, s₁) = (u₂, v₂, r₂, s₂)
    · rcases Prod.mk.inj h with ⟨rfl, h'⟩
      rcases Prod.mk.inj h' with ⟨rfl, h''⟩
      rcases Prod.mk.inj h'' with ⟨rfl, rfl⟩
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single (xor u₁ v₁)]
      · rw [Finset.sum_eq_single r₁]
        · rw [Finset.sum_eq_single v₁]
          · rw [Finset.sum_eq_single s₁]
            · simp
            · intro s _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ s₁) h
          · intro c _ hne; apply Finset.sum_eq_zero; intro s _; simp [hne]
          · intro h; exact absurd (Finset.mem_univ v₁) h
        · intro r _ hne; apply Finset.sum_eq_zero; intro c _; apply Finset.sum_eq_zero; intro s _; simp [hne]
        · intro h; exact absurd (Finset.mem_univ r₁) h
      · intro a _ hne; apply Finset.sum_eq_zero; intro r _; apply Finset.sum_eq_zero; intro c _
        apply Finset.sum_eq_zero; intro s _; simp [hne]
      · intro h; exact absurd (Finset.mem_univ (xor u₁ v₁)) h
    · simp only [h, ↓reduceIte]
      apply Finset.sum_eq_zero; intro a _
      apply Finset.sum_eq_zero; intro r _
      apply Finset.sum_eq_zero; intro c _
      apply Finset.sum_eq_zero; intro s _
      by_cases h1 : a = xor u₁ v₁ ∧ c = v₁ ∧ r = r₁ ∧ s = s₁
      · rcases h1 with ⟨rfl, rfl, rfl, rfl⟩
        have h2 : ¬ (xor u₁ c = xor u₂ v₂ ∧ c = v₂ ∧ r = r₂ ∧ s = s₂) := by
          rintro ⟨hxor, rfl, rfl, rfl⟩
          have hu : u₁ = u₂ := by cases u₁ <;> cases u₂ <;> cases c <;> simp_all
          exact h (by rw [hu])
        simp [h2]
      · simp [h1]
  have hstep2a : CQChannel.IsoEquiv
      ({ out := fun b ↦
          match b with
          | false =>
            { mat :=
                (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) *
                (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ
              posSemidef := posSemidef_mul_conjTranspose _
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hMM : (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ *
                    (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) =
                    (1 / 2 : ℂ) • ((W₁.checkCombine W₂).out false).mat +
                    (1 / 2 : ℂ) • ((W₁.checkCombine W₂).out true).mat := by
                  ext x y
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul', hstar2]
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
                    Fintype.sum_bool, Finset.mul_sum, mul_add]
                  rw [add_comm]
                  congr 1 <;>
                    (congr 1 <;>
                      (apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro s _;
                       simp only [star_star]; rw [← hmul2]; ring))
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    ((W₁.checkCombine W₂).out false).trace_one, ((W₁.checkCombine W₂).out true).trace_one]
                simp [smul_eq_mul]; ring }
          | true =>
            { mat :=
                (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) *
                (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ
              posSemidef := posSemidef_mul_conjTranspose _
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hMM : (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ *
                    (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) =
                    (1 / 2 : ℂ) • ((W₁.checkCombine W₂).out false).mat +
                    (1 / 2 : ℂ) • ((W₁.checkCombine W₂).out true).mat := by
                  ext x y
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, hstar2]
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
                    Fintype.sum_bool, Finset.mul_sum, mul_add]
                  rw [add_comm]
                  congr 1 <;>
                    (congr 1 <;>
                      (apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro s _;
                       simp only [star_star]; rw [← hmul2]; ring))
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    ((W₁.checkCombine W₂).out false).trace_one, ((W₁.checkCombine W₂).out true).trace_one]
                simp [smul_eq_mul]; ring } } : CQChannel (Bool × (Bool × d₁ × d₂)))
      W_prod := by
    refine ⟨(Bool × d₁) × (Bool × d₂), inferInstance, inferInstance, P, 1, hP_iso, by simp, ?_⟩
    have hPM : ∀ b : Bool,
        P * (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x)) =
        Matrix.of fun ((a, r), (c, s)) (i₁, i₂) ↦
          ((if b = false then gramFactor ρ₀ ρ₁ (a, r) i₁
            else ((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) * gramFactor ρ₀ ρ₁) (a, r) i₁) *
           (if b = false then gramFactor σ₀ σ₁ (c, s) i₂
            else ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁) (c, s) i₂)) := by
      intro b
      ext ⟨⟨a, r⟩, ⟨c, s⟩⟩ ⟨i₁, i₂⟩
      simp only [P, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (xor a c)]
      · rw [Finset.sum_eq_single c]
        · rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single s]
            · have hxor : xor (xor a c) c = a := by cases a <;> cases c <;> rfl
              simp only [hxor, and_self, ↓reduceIte, one_mul, A₀, A₁, Matrix.conjTranspose_apply,
                Matrix.of_apply, gramFactor, pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply,
                ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, star_mul', hstar2]
              have hρ₀ : star (ρ₀.sqrtMat i₁ r) = ρ₀.sqrtMat r i₁ := by
                have := congr_fun (congr_fun ρ₀.sqrtMat_isHermitian.eq r) i₁
                simpa [Matrix.conjTranspose_apply] using this
              have hρ₁ : star (ρ₁.sqrtMat i₁ r) = ρ₁.sqrtMat r i₁ := by
                have := congr_fun (congr_fun ρ₁.sqrtMat_isHermitian.eq r) i₁
                simpa [Matrix.conjTranspose_apply] using this
              have hσ₀ : star (σ₀.sqrtMat i₂ s) = σ₀.sqrtMat s i₂ := by
                have := congr_fun (congr_fun σ₀.sqrtMat_isHermitian.eq s) i₂
                simpa [Matrix.conjTranspose_apply] using this
              have hσ₁ : star (σ₁.sqrtMat i₂ s) = σ₁.sqrtMat s i₂ := by
                have := congr_fun (congr_fun σ₁.sqrtMat_isHermitian.eq s) i₂
                simpa [Matrix.conjTranspose_apply] using this
              cases b <;> cases a <;> cases c <;>
                simp [hρ₀, hρ₁, hσ₀, hσ₁] <;> ring
            · intro s' _ hne; simp [Ne.symm hne]
            · intro h; exact absurd (Finset.mem_univ s) h
          · intro r' _ hne; apply Finset.sum_eq_zero; intro s' _; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ r) h
        · intro v _ hne; apply Finset.sum_eq_zero; intro r' _; apply Finset.sum_eq_zero; intro s' _
          simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ c) h
      · intro u _ hne; apply Finset.sum_eq_zero; intro v _; apply Finset.sum_eq_zero; intro r' _
        apply Finset.sum_eq_zero; intro s' _
        by_cases hv : c = v
        · subst hv
          have hne' : ¬ (a = xor u c) := fun h ↦ hne (by rw [h]; cases u <;> cases c <;> rfl)
          simp [hne']
        · simp [hv]
      · intro h; exact absurd (Finset.mem_univ (xor a c)) h
    intro b
    have hMb : P * (match b with
        | false =>
          (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) *
          (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ
        | true =>
          (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) *
          (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ) * Pᴴ =
        1 * (W_prod.out b).mat * (1 : Matrix _ _ ℂ)ᴴ := by
      simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
      have hfactor_b : (P * Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x)) *
          (P * Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ =
          (W_prod.out b).mat := by
        rw [hPM b]
        ext ⟨⟨a₁, r₁⟩, ⟨c₁, s₁⟩⟩ ⟨⟨a₂, r₂⟩, ⟨c₂, s₂⟩⟩
        simp only [W_prod, DensityOp.tensor, CQChannel.dual, gramState, DensityOp.conjUnitary,
          Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.kroneckerMap_apply,
          Fintype.sum_prod_type]
        cases b
        · simp only [↓reduceIte, star_mul', Matrix.mul_apply, Matrix.conjTranspose_apply]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro i₁ _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i₂ _
          ring
        · simp only [Bool.true_eq_false, ↓reduceIte, star_mul']
          have h1 : (((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
              (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) *
              star (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ))) (a₁, r₁) (a₂, r₂) =
              (((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) * gramFactor ρ₀ ρ₁) *
              ((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) * gramFactor ρ₀ ρ₁)ᴴ) (a₁, r₁) (a₂, r₂) := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
          have h2 : (((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) *
              (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) *
              star (pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ))) (c₁, s₁) (c₂, s₂) =
              (((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁) *
              ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁)ᴴ) (c₁, s₁) (c₂, s₂) := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
          rw [h1, h2]
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro i₁ _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i₂ _
          ring
      cases b <;>
        simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using hfactor_b
    cases b <;> exact hMb
  let U_ctrl : Matrix (Bool × ((Bool × d₁) × (Bool × d₂)))
      (ULift.{u} Bool × ((Bool × d₁) × (Bool × d₂))) ℂ :=
    Matrix.of fun (w, x₁, x₂) (w', y₁, y₂) ↦
      if w = w'.down ∧ x₁ = y₁ ∧ x₂ = y₂ then
        (if w = true ∧ x₁.1 = true then -1 else 1)
      else 0
  have hU_iso : U_ctrlᴴ * U_ctrl = 1 := by
    ext ⟨⟨w₁⟩, ⟨a₁, r₁⟩, ⟨c₁, s₁⟩⟩ ⟨⟨w₂⟩, ⟨a₂, r₂⟩, ⟨c₂, s₂⟩⟩
    simp only [U_ctrl, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
    by_cases h : (ULift.up w₁, (a₁, r₁), (c₁, s₁)) = (ULift.up w₂, (a₂, r₂), (c₂, s₂))
    · rcases Prod.mk.inj h with ⟨hw, h'⟩
      rcases Prod.mk.inj h' with ⟨h1, h2⟩
      rcases Prod.mk.inj h1 with ⟨rfl, rfl⟩
      rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
      have hw' : w₁ = w₂ := congr_arg ULift.down hw
      subst hw'
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single w₁]
      · rw [Finset.sum_eq_single a₁]
        · rw [Finset.sum_eq_single r₁]
          · rw [Finset.sum_eq_single c₁]
            · rw [Finset.sum_eq_single s₁]
              · cases w₁ <;> cases a₁ <;> simp
              · intro s _ hne; simp [hne]
              · intro h; exact absurd (Finset.mem_univ s₁) h
            · intro c _ hne; apply Finset.sum_eq_zero; intro s _; simp [hne]
            · intro h; exact absurd (Finset.mem_univ c₁) h
          · intro r _ hne; apply Finset.sum_eq_zero; intro c _; apply Finset.sum_eq_zero; intro s _; simp [hne]
          · intro h; exact absurd (Finset.mem_univ r₁) h
        · intro a _ hne; apply Finset.sum_eq_zero; intro r _; apply Finset.sum_eq_zero; intro c _
          apply Finset.sum_eq_zero; intro s _; simp [hne]
        · intro h; exact absurd (Finset.mem_univ a₁) h
      · intro w _ hne; apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro r _
        apply Finset.sum_eq_zero; intro c _; apply Finset.sum_eq_zero; intro s _; simp [hne]
      · intro h; exact absurd (Finset.mem_univ w₁) h
    · simp only [h, ↓reduceIte]
      apply Finset.sum_eq_zero; intro w _
      apply Finset.sum_eq_zero; intro a _
      apply Finset.sum_eq_zero; intro r _
      apply Finset.sum_eq_zero; intro c _
      apply Finset.sum_eq_zero; intro s _
      by_cases h1 : w = w₁ ∧ (a, r) = (a₁, r₁) ∧ (c, s) = (c₁, s₁)
      · rcases h1 with ⟨rfl, h1a, h1c⟩
        rcases Prod.mk.inj h1a with ⟨rfl, rfl⟩
        rcases Prod.mk.inj h1c with ⟨rfl, rfl⟩
        have h2 : ¬ (w = w₂ ∧ (a, r) = (a₂, r₂) ∧ (c, s) = (c₂, s₂)) := by
          rintro ⟨hw, ha, hc⟩
          exact h (by rw [hw, ha, hc])
        simp [h2]
      · simp [h1]
  have hstep2b : (W_prod.tensorMaxMixed (ULift.{u} Bool)).IsoEquiv (W₁.dual.varCombine W₂.dual) := by
    refine ⟨Bool × ((Bool × d₁) × (Bool × d₂)), inferInstance, inferInstance, U_ctrl, 1, hU_iso, by simp, ?_⟩
    intro b
    rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
    ext ⟨w₁, ⟨a₁, r₁⟩, ⟨c₁, s₁⟩⟩ ⟨w₂, ⟨a₂, r₂⟩, ⟨c₂, s₂⟩⟩
    simp only [U_ctrl, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (ULift.up w₂)]
    · rw [Finset.sum_eq_single a₂]
      · rw [Finset.sum_eq_single r₂]
        · rw [Finset.sum_eq_single c₂]
          · rw [Finset.sum_eq_single s₂]
            · rw [Finset.sum_eq_single (ULift.up w₁)]
              · rw [Finset.sum_eq_single a₁]
                · rw [Finset.sum_eq_single r₁]
                  · rw [Finset.sum_eq_single c₁]
                    · rw [Finset.sum_eq_single s₁]
                      · simp only [↓reduceIte, and_self, CQChannel.tensorMaxMixed, W_prod,
                          CQChannel.varCombine, DensityOp.tensor, maxMixedState, CQChannel.dual,
                          DensityOp.conjUnitary, pauliZTensorI, Matrix.kroneckerMap_apply,
                          Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul,
                          Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
                          Fintype.card_ulift, Fintype.card_bool, Nat.cast_ofNat]
                        by_cases hw : w₁ = w₂
                        · subst hw
                          have hG1 := pauliZTensorI_conj_entry (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) a₁ a₂ r₁ r₂
                          cases w₁ <;> cases b <;> cases a₁ <;> cases a₂ <;>
                            simp [DensityOp.midpoint, DensityOp.mix, CQChannel.ketBraBool,
                              Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Complex.real_smul,
                              hG1] <;> ring
                        · cases w₁ <;> cases w₂ <;> simp_all [DensityOp.midpoint, DensityOp.mix,
                            CQChannel.ketBraBool, DensityOp.tensor, Matrix.kroneckerMap_apply,
                            Matrix.diagonal_apply]
                      · intro z _ hne; simp [Ne.symm hne]
                      · intro h; exact absurd (Finset.mem_univ s₁) h
                    · intro z _ hne; apply Finset.sum_eq_zero; intro _ _; simp [Ne.symm hne]
                    · intro h; exact absurd (Finset.mem_univ c₁) h
                  · intro z _ hne; apply Finset.sum_eq_zero; intro _ _; apply Finset.sum_eq_zero; intro _ _
                    simp [Ne.symm hne]
                  · intro h; exact absurd (Finset.mem_univ r₁) h
                · intro z _ hne; apply Finset.sum_eq_zero; intro _ _; apply Finset.sum_eq_zero; intro _ _
                  apply Finset.sum_eq_zero; intro _ _; simp [Ne.symm hne]
                · intro h; exact absurd (Finset.mem_univ a₁) h
              · intro w _ hne; apply Finset.sum_eq_zero; intro _ _; apply Finset.sum_eq_zero; intro _ _
                apply Finset.sum_eq_zero; intro _ _; apply Finset.sum_eq_zero; intro _ _
                have hne' : w₁ ≠ w.down := fun h ↦ hne (by cases w; simp_all)
                simp [hne']
              · intro h; exact absurd (Finset.mem_univ (ULift.up w₁)) h
            · intro z _ hne; simp [Ne.symm hne]
            · intro h; exact absurd (Finset.mem_univ s₂) h
          · intro z _ hne; apply Finset.sum_eq_zero; intro _ _; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ c₂) h
        · intro z _ hne; apply Finset.sum_eq_zero; intro _ _; apply Finset.sum_eq_zero; intro _ _
          simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ r₂) h
      · intro z _ hne; apply Finset.sum_eq_zero; intro _ _; apply Finset.sum_eq_zero; intro _ _
        apply Finset.sum_eq_zero; intro _ _; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ a₂) h
    · intro w _ hne; apply Finset.sum_eq_zero; intro _ _; apply Finset.sum_eq_zero; intro _ _
      apply Finset.sum_eq_zero; intro _ _; apply Finset.sum_eq_zero; intro _ _
      have hne' : w₂ ≠ w.down := fun h ↦ hne (by cases w; simp_all)
      simp [hne']
    · intro h; exact absurd (Finset.mem_univ (ULift.up w₂)) h
  exact ((hstep1.trans hstep2a.toChannelEquiv).trans
    (W_prod.channelEquiv_tensorMaxMixed (ULift.{u} Bool))).trans hstep2b.toChannelEquiv

set_option maxHeartbeats 600000 in
/-- **Proposition 2.2 (D2, Variable-Node Channel-Level Duality)**:
`(W₁ ⊛ W₂)⊥ ≃ W₁⊥ ⊠ W₂⊥` as reversible CPTP-equivalent c-q channels. -/
theorem prop_2_2_D2_var_channelEquiv {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    (W₁.varCombine W₂).dual.ChannelEquiv (W₁.dual.checkCombine W₂.dual) := by
  set ρ₀ := W₁.out false
  set ρ₁ := W₁.out true
  set σ₀ := W₂.out false
  set σ₁ := W₂.out true
  have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
  have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  let A₀ : Matrix (Bool × (d₁ × d₂)) (Bool × (d₁ × d₂)) ℂ :=
    Matrix.of fun (v, i₁, i₂) (v', j₁, j₂) ↦
      if v = v' then
        ((Real.sqrt 2 : ℂ)⁻¹) *
          (if v = false then ρ₀.sqrtMat i₁ j₁ * σ₀.sqrtMat i₂ j₂
           else ρ₁.sqrtMat i₁ j₁ * σ₀.sqrtMat i₂ j₂)
      else 0
  let A₁ : Matrix (Bool × (d₁ × d₂)) (Bool × (d₁ × d₂)) ℂ :=
    Matrix.of fun (v, i₁, i₂) (v', j₁, j₂) ↦
      if v = v' then
        ((Real.sqrt 2 : ℂ)⁻¹) *
          (if v = false then ρ₁.sqrtMat i₁ j₁ * σ₁.sqrtMat i₂ j₂
           else ρ₀.sqrtMat i₁ j₁ * σ₁.sqrtMat i₂ j₂)
      else 0
  have hsq_prod : ∀ (τ : DensityOp d₁) (η : DensityOp d₂) (i₁ j₁ : d₁) (i₂ j₂ : d₂),
      ∑ k₁ : d₁, ∑ k₂ : d₂,
        (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂)) =
        τ.mat i₁ j₁ * η.mat i₂ j₂ := by
    intro τ η i₁ j₁ i₂ j₂
    have h1 : ∑ k₁ : d₁, τ.sqrtMat i₁ k₁ * star (τ.sqrtMat j₁ k₁) = τ.mat i₁ j₁ := by
      have hsq := congr_fun (congr_fun τ.sqrtMat_mul_self i₁) j₁
      rw [← hsq]; simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro k _
      have hhk : star (τ.sqrtMat j₁ k) = τ.sqrtMat k j₁ := by
        have := congr_fun (congr_fun τ.sqrtMat_isHermitian.eq k) j₁
        simpa [Matrix.conjTranspose_apply] using this
      rw [hhk]
    have h2 : ∑ k₂ : d₂, η.sqrtMat i₂ k₂ * star (η.sqrtMat j₂ k₂) = η.mat i₂ j₂ := by
      have hsq := congr_fun (congr_fun η.sqrtMat_mul_self i₂) j₂
      rw [← hsq]; simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro k _
      have hhk : star (η.sqrtMat j₂ k) = η.sqrtMat k j₂ := by
        have := congr_fun (congr_fun η.sqrtMat_isHermitian.eq k) j₂
        simpa [Matrix.conjTranspose_apply] using this
      rw [hhk]
    calc ∑ k₁ : d₁, ∑ k₂ : d₂,
          (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂))
        = (∑ k₁ : d₁, τ.sqrtMat i₁ k₁ * star (τ.sqrtMat j₁ k₁)) *
          (∑ k₂ : d₂, η.sqrtMat i₂ k₂ * star (η.sqrtMat j₂ k₂)) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro k₁ _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k₂ _
            ring
      _ = τ.mat i₁ j₁ * η.mat i₂ j₂ := by rw [h1, h2]
  have hA₀ : A₀ * A₀ᴴ = ((W₁.varCombine W₂).out false).mat := by
    ext ⟨v₁, i₁, i₂⟩ ⟨v₂, j₁, j₂⟩
    simp only [A₀, CQChannel.varCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      CQChannel.ketBraBool, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_eq_single v₁]
    · by_cases hv : v₁ = v₂
      · subst hv
        have hl : ∀ (τ : DensityOp d₁) (η : DensityOp d₂),
            ∑ k₁ : d₁, ∑ k₂ : d₂,
              ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
              ((Real.sqrt 2 : ℂ)⁻¹ * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂))) =
            (1 / 2 : ℂ) * (τ.mat i₁ j₁ * η.mat i₂ j₂) := by
          intro τ η
          rw [← hsq_prod τ η i₁ j₁ i₂ j₂, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k₁ _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k₂ _
          calc ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
                ((Real.sqrt 2 : ℂ)⁻¹ * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂)))
              = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
                ((τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂))) := by ring
            _ = _ := by rw [hmul2]
        cases v₁ <;>
          simp only [↓reduceIte, Bool.true_eq_false, star_mul', hstar2, hl,
            Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
            Matrix.diagonal_apply, Complex.real_smul] <;> push_cast <;> ring
      · simp only [hv, Ne.symm hv, ↓reduceIte, star_zero, mul_zero, Finset.sum_const_zero,
          Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.diagonal_apply]
        cases v₁ <;> cases v₂ <;> simp_all
    · intro v _ hne; apply Finset.sum_eq_zero; intro k₁ _; apply Finset.sum_eq_zero; intro k₂ _
      simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ v₁) h
  have hA₁ : A₁ * A₁ᴴ = ((W₁.varCombine W₂).out true).mat := by
    ext ⟨v₁, i₁, i₂⟩ ⟨v₂, j₁, j₂⟩
    simp only [A₁, CQChannel.varCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      CQChannel.ketBraBool, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_eq_single v₁]
    · by_cases hv : v₁ = v₂
      · subst hv
        have hl : ∀ (τ : DensityOp d₁) (η : DensityOp d₂),
            ∑ k₁ : d₁, ∑ k₂ : d₂,
              ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
              ((Real.sqrt 2 : ℂ)⁻¹ * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂))) =
            (1 / 2 : ℂ) * (τ.mat i₁ j₁ * η.mat i₂ j₂) := by
          intro τ η
          rw [← hsq_prod τ η i₁ j₁ i₂ j₂, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k₁ _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k₂ _
          calc ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
                ((Real.sqrt 2 : ℂ)⁻¹ * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂)))
              = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
                ((τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂))) := by ring
            _ = _ := by rw [hmul2]
        cases v₁ <;>
          simp only [↓reduceIte, Bool.true_eq_false, star_mul', hstar2, hl,
            Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
            Matrix.diagonal_apply, Complex.real_smul] <;> push_cast <;> ring
      · simp only [hv, Ne.symm hv, ↓reduceIte, star_zero, mul_zero, Finset.sum_const_zero,
          Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.diagonal_apply]
        cases v₁ <;> cases v₂ <;> simp_all
    · intro v _ hne; apply Finset.sum_eq_zero; intro k₁ _; apply Finset.sum_eq_zero; intro k₂ _
      simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ v₁) h
  have hstep1 := (dual_isoEquiv_of_purification (W₁.varCombine W₂) A₀ A₁ hA₀ hA₁).toChannelEquiv
  let P : Matrix ((Bool × d₁) × (Bool × d₂)) (Bool × (Bool × (d₁ × d₂))) ℂ :=
    Matrix.of fun ((a, r), (c, s)) (u, v, r', s') ↦
      if a = xor u v ∧ c = u ∧ r = r' ∧ s = s' then 1 else 0
  have hP_iso : Pᴴ * P = 1 := by
    ext ⟨u₁, v₁, r₁, s₁⟩ ⟨u₂, v₂, r₂, s₂⟩
    simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
    by_cases h : (u₁, v₁, r₁, s₁) = (u₂, v₂, r₂, s₂)
    · rcases Prod.mk.inj h with ⟨rfl, h'⟩
      rcases Prod.mk.inj h' with ⟨rfl, h''⟩
      rcases Prod.mk.inj h'' with ⟨rfl, rfl⟩
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single (xor u₁ v₁)]
      · rw [Finset.sum_eq_single r₁]
        · rw [Finset.sum_eq_single u₁]
          · rw [Finset.sum_eq_single s₁]
            · simp
            · intro s _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ s₁) h
          · intro c _ hne; apply Finset.sum_eq_zero; intro s _; simp [hne]
          · intro h; exact absurd (Finset.mem_univ u₁) h
        · intro r _ hne; apply Finset.sum_eq_zero; intro c _; apply Finset.sum_eq_zero; intro s _; simp [hne]
        · intro h; exact absurd (Finset.mem_univ r₁) h
      · intro a _ hne; apply Finset.sum_eq_zero; intro r _; apply Finset.sum_eq_zero; intro c _
        apply Finset.sum_eq_zero; intro s _; simp [hne]
      · intro h; exact absurd (Finset.mem_univ (xor u₁ v₁)) h
    · simp only [h, ↓reduceIte]
      apply Finset.sum_eq_zero; intro a _
      apply Finset.sum_eq_zero; intro r _
      apply Finset.sum_eq_zero; intro c _
      apply Finset.sum_eq_zero; intro s _
      by_cases h1 : a = xor u₁ v₁ ∧ c = u₁ ∧ r = r₁ ∧ s = s₁
      · rcases h1 with ⟨rfl, rfl, rfl, rfl⟩
        have h2 : ¬ (xor c v₁ = xor u₂ v₂ ∧ c = u₂ ∧ r = r₂ ∧ s = s₂) := by
          rintro ⟨hxor, rfl, rfl, rfl⟩
          have hv : v₁ = v₂ := by cases c <;> cases v₁ <;> cases v₂ <;> simp_all
          exact h (by rw [hv])
        simp [h2]
      · simp [h1]
  have hstep2 : CQChannel.IsoEquiv
      ({ out := fun b ↦
          match b with
          | false =>
            { mat :=
                (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) *
                (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ
              posSemidef := posSemidef_mul_conjTranspose _
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hMM : (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ *
                    (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) =
                    (1 / 2 : ℂ) • ((W₁.varCombine W₂).out false).mat +
                    (1 / 2 : ℂ) • ((W₁.varCombine W₂).out true).mat := by
                  ext x y
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul', hstar2]
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
                    Fintype.sum_bool, Finset.mul_sum, mul_add]
                  rw [add_comm]
                  congr 1 <;>
                    (congr 1 <;>
                      (apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro s _;
                       simp only [star_star]; rw [← hmul2]; ring))
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    ((W₁.varCombine W₂).out false).trace_one, ((W₁.varCombine W₂).out true).trace_one]
                simp [smul_eq_mul]; ring }
          | true =>
            { mat :=
                (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) *
                (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ
              posSemidef := posSemidef_mul_conjTranspose _
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hMM : (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ *
                    (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) =
                    (1 / 2 : ℂ) • ((W₁.varCombine W₂).out false).mat +
                    (1 / 2 : ℂ) • ((W₁.varCombine W₂).out true).mat := by
                  ext x y
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, hstar2]
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
                    Fintype.sum_bool, Finset.mul_sum, mul_add]
                  rw [add_comm]
                  congr 1 <;>
                    (congr 1 <;>
                      (apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro s _;
                       simp only [star_star]; rw [← hmul2]; ring))
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    ((W₁.varCombine W₂).out false).trace_one, ((W₁.varCombine W₂).out true).trace_one]
                simp [smul_eq_mul]; ring } } : CQChannel (Bool × (Bool × (d₁ × d₂))))
      (W₁.dual.checkCombine W₂.dual) := by
    refine ⟨(Bool × d₁) × (Bool × d₂), inferInstance, inferInstance, P, 1, hP_iso, by simp, ?_⟩
    have hPM : ∀ b : Bool,
        P * (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x)) =
        Matrix.of fun ((a, r), (c, s)) (v', i₁, i₂) ↦
          if xor a c = v' then
            (if b = false then gramFactor ρ₀ ρ₁ (a, r) i₁ * gramFactor σ₀ σ₁ (c, s) i₂
             else gramFactor ρ₀ ρ₁ (a, r) i₁ *
               ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁) (c, s) i₂)
          else 0 := by
      intro b
      ext ⟨⟨a, r⟩, ⟨c, s⟩⟩ ⟨v', i₁, i₂⟩
      simp only [P, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single c]
      · rw [Finset.sum_eq_single (xor a c)]
        · rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single s]
            · have hxor : xor c (xor a c) = a := by cases a <;> cases c <;> rfl
              simp only [hxor, and_self, ↓reduceIte, one_mul, A₀, A₁, Matrix.conjTranspose_apply,
                Matrix.of_apply, gramFactor, pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply,
                ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
              by_cases hv : xor a c = v'
              · subst hv
                simp only [↓reduceIte, star_mul', hstar2]
                have hρ₀ : star (ρ₀.sqrtMat i₁ r) = ρ₀.sqrtMat r i₁ := by
                  have := congr_fun (congr_fun ρ₀.sqrtMat_isHermitian.eq r) i₁
                  simpa [Matrix.conjTranspose_apply] using this
                have hρ₁ : star (ρ₁.sqrtMat i₁ r) = ρ₁.sqrtMat r i₁ := by
                  have := congr_fun (congr_fun ρ₁.sqrtMat_isHermitian.eq r) i₁
                  simpa [Matrix.conjTranspose_apply] using this
                have hσ₀ : star (σ₀.sqrtMat i₂ s) = σ₀.sqrtMat s i₂ := by
                  have := congr_fun (congr_fun σ₀.sqrtMat_isHermitian.eq s) i₂
                  simpa [Matrix.conjTranspose_apply] using this
                have hσ₁ : star (σ₁.sqrtMat i₂ s) = σ₁.sqrtMat s i₂ := by
                  have := congr_fun (congr_fun σ₁.sqrtMat_isHermitian.eq s) i₂
                  simpa [Matrix.conjTranspose_apply] using this
                cases b <;> cases a <;> cases c <;>
                  simp [hρ₀, hρ₁, hσ₀, hσ₁] <;> ring
              · simp [hv, Ne.symm hv]
            · intro s' _ hne; simp [Ne.symm hne]
            · intro h; exact absurd (Finset.mem_univ s) h
          · intro r' _ hne; apply Finset.sum_eq_zero; intro s' _; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ r) h
        · intro v _ hne; apply Finset.sum_eq_zero; intro r' _; apply Finset.sum_eq_zero; intro s' _
          have hne' : ¬ (a = xor c v) := fun h ↦ hne (by rw [h]; cases c <;> cases v <;> rfl)
          simp [hne']
        · intro h; exact absurd (Finset.mem_univ (xor a c)) h
      · intro u _ hne; apply Finset.sum_eq_zero; intro v _; apply Finset.sum_eq_zero; intro r' _
        apply Finset.sum_eq_zero; intro s' _; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ c) h
    intro b
    have hfactor_b : (P * Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x)) *
        (P * Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ =
        ((W₁.dual.checkCombine W₂.dual).out b).mat := by
      rw [hPM b]
      ext ⟨⟨a₁, r₁⟩, ⟨c₁, s₁⟩⟩ ⟨⟨a₂, r₂⟩, ⟨c₂, s₂⟩⟩
      conv_lhs =>
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type]
      conv_rhs =>
        simp only [CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
          CQChannel.dual, gramState, DensityOp.conjUnitary, Matrix.add_apply, Matrix.smul_apply,
          Matrix.kroneckerMap_apply, Complex.real_smul]
      have hG1 := pauliZTensorI_conj_entry (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) a₁ a₂ r₁ r₂
      have hG2 := pauliZTensorI_conj_entry (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) c₁ c₂ s₁ s₂
      rw [Finset.sum_eq_single (xor a₁ c₁)]
      · by_cases hpar : xor a₁ c₁ = xor a₂ c₂
        · simp only [hpar, ↓reduceIte]
          have hprod : ∑ i₁ : d₁, ∑ i₂ : d₂,
              gramFactor ρ₀ ρ₁ (a₁, r₁) i₁ * gramFactor σ₀ σ₁ (c₁, s₁) i₂ *
              star (gramFactor ρ₀ ρ₁ (a₂, r₂) i₁ * gramFactor σ₀ σ₁ (c₂, s₂) i₂) =
              (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) (a₁, r₁) (a₂, r₂) *
              (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) (c₁, s₁) (c₂, s₂) := by
            simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_mul']
            rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i₁ _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i₂ _; ring
          cases b
          · simp only [↓reduceIte, Bool.not_false, hprod]
            change _ = ((1 - 1 / 2 : ℝ) : ℂ) *
                ((gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) (a₁, r₁) (a₂, r₂) *
                 (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) (c₁, s₁) (c₂, s₂)) +
              ((1 / 2 : ℝ) : ℂ) *
                (((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
                  (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) *
                  star (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ)) (a₁, r₁) (a₂, r₂) *
                 ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) *
                  (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) *
                  star (pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ)) (c₁, s₁) (c₂, s₂))
            rw [hG1, hG2]
            cases a₁ <;> cases a₂ <;> cases c₁ <;> cases c₂ <;> simp_all <;> push_cast <;> ring
          · simp only [Bool.true_eq_false, ↓reduceIte, Bool.not_true]
            have hprod' : ∑ i₁ : d₁, ∑ i₂ : d₂,
                gramFactor ρ₀ ρ₁ (a₁, r₁) i₁ *
                ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁) (c₁, s₁) i₂ *
                star (gramFactor ρ₀ ρ₁ (a₂, r₂) i₁ *
                  ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁) (c₂, s₂) i₂) =
                (if c₁ = c₂ then (1 : ℂ) else -1) *
                ((gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) (a₁, r₁) (a₂, r₂) *
                 (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) (c₁, s₁) (c₂, s₂)) := by
              have hZ2 : ∀ c s i₂, ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁) (c, s) i₂ =
                  (if c = false then (1 : ℂ) else -1) * gramFactor σ₀ σ₁ (c, s) i₂ := by
                intro c s i₂
                simp [pauliZTensorI, Matrix.diagonal_mul]
              simp_rw [hZ2]
              rw [← hprod, Finset.mul_sum]
              apply Finset.sum_congr rfl; intro i₁ _
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i₂ _
              cases c₁ <;> cases c₂ <;> simp [star_mul'] <;> ring
            rw [hprod']
            change _ = ((1 - 1 / 2 : ℝ) : ℂ) *
                (((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
                  (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) *
                  star (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ)) (a₁, r₁) (a₂, r₂) *
                 (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) (c₁, s₁) (c₂, s₂)) +
              ((1 / 2 : ℝ) : ℂ) *
                ((gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) (a₁, r₁) (a₂, r₂) *
                 ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) *
                  (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) *
                  star (pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ)) (c₁, s₁) (c₂, s₂))
            rw [hG1, hG2]
            cases a₁ <;> cases a₂ <;> cases c₁ <;> cases c₂ <;> simp_all <;> push_cast <;> ring
        · have hne' : ¬ (xor a₂ c₂ = xor a₁ c₁) := fun h ↦ hpar h.symm
          simp only [hne', ↓reduceIte, star_zero, mul_zero, Finset.sum_const_zero]
          cases b
          · simp only [Bool.not_false]
            change (0 : ℂ) = ((1 - 1 / 2 : ℝ) : ℂ) *
                ((gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) (a₁, r₁) (a₂, r₂) *
                 (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) (c₁, s₁) (c₂, s₂)) +
              ((1 / 2 : ℝ) : ℂ) *
                (((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
                  (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) *
                  star (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ)) (a₁, r₁) (a₂, r₂) *
                 ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) *
                  (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) *
                  star (pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ)) (c₁, s₁) (c₂, s₂))
            rw [hG1, hG2]
            cases a₁ <;> cases a₂ <;> cases c₁ <;> cases c₂ <;> simp_all <;> push_cast <;> ring
          · simp only [Bool.not_true]
            change (0 : ℂ) = ((1 - 1 / 2 : ℝ) : ℂ) *
                (((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
                  (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) *
                  star (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ)) (a₁, r₁) (a₂, r₂) *
                 (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) (c₁, s₁) (c₂, s₂)) +
              ((1 / 2 : ℝ) : ℂ) *
                ((gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) (a₁, r₁) (a₂, r₂) *
                 ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) *
                  (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) *
                  star (pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ)) (c₁, s₁) (c₂, s₂))
            rw [hG1, hG2]
            cases a₁ <;> cases a₂ <;> cases c₁ <;> cases c₂ <;> simp_all <;> push_cast <;> ring
      · intro v _ hne; apply Finset.sum_eq_zero; intro i₁ _; apply Finset.sum_eq_zero; intro i₂ _
        simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ (xor a₁ c₁)) h
    cases b <;>
      simpa [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one,
        Matrix.conjTranspose_mul, Matrix.mul_assoc] using hfactor_b
  exact hstep1.trans hstep2.toChannelEquiv

/-- **Proposition 2.2 (D2, Full Channel-Level Polarization Duality)**:
For all finite-dimensional binary-input c-q channels `W₁, W₂`:
`(W₁ ⊠ W₂)⊥ ≃ W₁⊥ ⊛ W₂⊥` and `(W₁ ⊛ W₂)⊥ ≃ W₁⊥ ⊠ W₂⊥`. -/
theorem prop_2_2_D2_channelEquiv {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    (W₁.checkCombine W₂).dual.ChannelEquiv (W₁.dual.varCombine W₂.dual) ∧
    (W₁.varCombine W₂).dual.ChannelEquiv (W₁.dual.checkCombine W₂.dual) :=
  ⟨prop_2_2_D2_check_channelEquiv W₁ W₂, prop_2_2_D2_var_channelEquiv W₁ W₂⟩

end ChannelDualityEquiv

end PolarCodes
