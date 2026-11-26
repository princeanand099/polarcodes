/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.ArikanTransform

/-!
# `G_N`-Coset Classical–Quantum Polar Codes, QSC Decoder, Wilde–Guha Bound, and Coding Theorem 1.1

This module completes the full coding-theoretic layer of Section 5 and Theorem 1.1:
- `condSynthState`: normalized conditional output state of `W_n^{(i)}` given prefix `p` and bit `b`
- `CosetPolarCode`: a deterministic `G_N`-coset classical–quantum polar code of blocklength `N = 2^n`,
  information set `𝒜`, rate `R = |𝒜| / N`, frozen vector `u_{𝒜^c}`, encoder `u_𝒜 ↦ (u_𝒜, u_{𝒜^c}) G_N`,
  decoding POVM `{Λ_{u_𝒜}}`, and average block-error probability `P_e(N, R)`
- `qscPolarCode`: the Quantum Successive-Cancellation (QSC) sequential projective/POVM decoder using
  binary Helstrom projectors for `i ∈ 𝒜` and frozen bits for `i ∉ 𝒜`
- `wilde_guha_qsc_bound`: existence of a deterministic frozen vector `u_{𝒜^c}` achieving
  `P_e(N, R) ≤ 2 √(∑_{i ∈ 𝒜} (1 / 2) Z(W_n^{(i)}))` (Wilde–Guha [12, Proposition 4])
- `theorem_1_1_coding_poly_blocklength`: full coding-theoretic Theorem 1.1 asserting existence of a
  deterministic `G_N`-coset c-q polar code of blocklength `N = 2^n ≥ C₀ (1/ε)^μ`, rate `R ≥ I(W) - ε`,
  and QSC block-error probability `P_e(N, R) ≤ 2^{-N^{0.49}}`.
-/

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodes

universe u

section PolarCoding

variable {d : Type u} [Fintype d] [DecidableEq d]

/-! ### Uniqueness of PSD Square Root and Block-Diagonal Fidelity Bound -/

/-- Uniqueness of the positive semidefinite square root of a `DensityOp`. -/
lemma DensityOp.sqrtMat_unique {α : Type*} [Fintype α] [DecidableEq α]
    (ρ : DensityOp α) {R : Matrix α α ℂ} (hR_psd : R.PosSemidef) (hR_sq : R * R = ρ.mat) :
    R = ρ.sqrtMat := by
  set U := (ρ.eigUnitary : Matrix α α ℂ)
  have hU_star : star U * U = 1 := Unitary.coe_star_mul_self ρ.eigUnitary
  have hU_mul : U * star U = 1 := Unitary.coe_mul_star_self ρ.eigUnitary
  have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by
    simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
  let M : Matrix α α ℂ := star U * R * U
  have hM_psd : M.PosSemidef := by
    change (star U * R * U).PosSemidef
    rw [Matrix.star_eq_conjTranspose]
    exact hR_psd.conjTranspose_mul_mul_same U
  have hM_sq : M * M = Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) := by
    calc M * M = star U * (R * (U * star U) * R) * U := by simp only [M, Matrix.mul_assoc]
      _ = star U * ρ.mat * U := by rw [hU_mul, Matrix.mul_one, hR_sq]
      _ = Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) := by
            conv_lhs => rw [hspec]
            calc star U * (U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U) * U
                = (star U * U) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * (star U * U) := by
                    simp only [Matrix.mul_assoc]
              _ = _ := by rw [hU_star, Matrix.one_mul, Matrix.mul_one]
  have hM_diag : M = Matrix.diagonal (fun i : α ↦ (Real.sqrt (ρ.eigvals i) : ℂ)) := by
    set V := (hM_psd.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
    have hV_star : star V * V = 1 := Unitary.coe_star_mul_self hM_psd.isHermitian.eigenvectorUnitary
    have hV_mul : V * star V = 1 := Unitary.coe_mul_star_self hM_psd.isHermitian.eigenvectorUnitary
    have hM_spec : M = V * Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues) * star V := by
      simpa [V, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using
        hM_psd.isHermitian.spectral_theorem
    have hM_sq_spec : V * Matrix.diagonal (fun k : α ↦ ((hM_psd.isHermitian.eigenvalues k ^ 2 : ℝ) : ℂ)) * star V =
        Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) := by
      rw [← hM_sq]
      conv_rhs => rw [hM_spec]
      calc V * Matrix.diagonal (fun k : α ↦ ((hM_psd.isHermitian.eigenvalues k ^ 2 : ℝ) : ℂ)) * star V
          = V * (Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues) *
              Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues)) * star V := by
                refine congr_arg (fun Z ↦ V * Z * star V) ?_
                rw [Matrix.diagonal_mul_diagonal]; congr 1; funext k; simp [sq]
        _ = V * (Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues) * (star V * V) *
              Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues)) * star V := by
                rw [hV_star, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hV_eig : ∀ i k : α,
        V i k * ((hM_psd.isHermitian.eigenvalues k : ℝ) : ℂ) =
        V i k * (Real.sqrt (ρ.eigvals i) : ℂ) := by
      intro i k
      have h1 : (V * Matrix.diagonal (fun k : α ↦ ((hM_psd.isHermitian.eigenvalues k ^ 2 : ℝ) : ℂ))) i k =
          (Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * V) i k := by
        have := congr_arg (fun X ↦ X * V) hM_sq_spec
        simp only [Matrix.mul_assoc, hV_star, Matrix.mul_one] at this
        exact congr_fun (congr_fun this i) k
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply] at h1
      by_cases hVik : V i k = 0
      · simp [hVik]
      · have hsq_eq : hM_psd.isHermitian.eigenvalues k ^ 2 = ρ.eigvals i := by
          have h2 : ((hM_psd.isHermitian.eigenvalues k ^ 2 : ℝ) : ℂ) = (ρ.eigvals i : ℂ) := by
            have : V i k * ((hM_psd.isHermitian.eigenvalues k ^ 2 : ℝ) : ℂ) =
                V i k * (ρ.eigvals i : ℂ) := by linear_combination h1
            exact mul_left_cancel₀ hVik this
          exact Complex.ofReal_injective h2
        have hval : hM_psd.isHermitian.eigenvalues k = Real.sqrt (ρ.eigvals i) := by
          rw [← hsq_eq, Real.sqrt_sq (hM_psd.eigenvalues_nonneg k)]
        rw [hval]
    ext i j
    conv_lhs => rw [hM_spec]
    rw [Matrix.mul_apply]
    have hterm : ∀ k : α,
        (V * Matrix.diagonal (Complex.ofReal ∘ hM_psd.isHermitian.eigenvalues)) i k * (star V) k j =
        V i k * (hM_psd.isHermitian.eigenvalues k : ℂ) * star (V j k) := by
      intro k; rw [Matrix.mul_diagonal, Matrix.star_apply, Function.comp_apply]
    simp_rw [hterm]
    simp only [Matrix.diagonal_apply]
    calc ∑ k : α, V i k * (hM_psd.isHermitian.eigenvalues k : ℂ) * star (V j k)
        = ∑ k : α, (Real.sqrt (ρ.eigvals i) : ℂ) * (V i k * star (V j k)) := by
            apply Finset.sum_congr rfl; intro k _
            rw [hV_eig i k]; ring
      _ = (Real.sqrt (ρ.eigvals i) : ℂ) * (V * star V) i j := by
            rw [← Finset.mul_sum]; simp [Matrix.mul_apply, Matrix.star_apply]
      _ = if i = j then (Real.sqrt (ρ.eigvals i) : ℂ) else 0 := by
            rw [hV_mul, Matrix.one_apply]
            split_ifs <;> simp
  calc R = (U * star U) * R * (U * star U) := by rw [hU_mul, Matrix.one_mul, Matrix.mul_one]
    _ = U * M * star U := by simp only [M, Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i : α ↦ (Real.sqrt (ρ.eigvals i) : ℂ)) * star U := by rw [hM_diag]
    _ = ρ.sqrtMat := rfl

/-- For uniform block-diagonal density operators `ρ₀ = ⊕_p (1/|κ|) σ₀(p)` and
`ρ₁ = ⊕_p (1/|κ|) σ₁(p)`, the average block root fidelity is bounded above by `rootFidelity ρ₀ ρ₁`. -/
lemma blockDiag_rootFidelity_ge {κ α : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    [Fintype α] [DecidableEq α]
    (σ₀ σ₁ : κ → DensityOp α) (ρ₀ ρ₁ : DensityOp (κ × α))
    (hρ₀ : ∀ p₁ p₂ r₁ r₂, ρ₀.mat (p₁, r₁) (p₂, r₂) =
      if p₁ = p₂ then ((Fintype.card κ : ℂ))⁻¹ * (σ₀ p₁).mat r₁ r₂ else 0)
    (hρ₁ : ∀ p₁ p₂ r₁ r₂, ρ₁.mat (p₁, r₁) (p₂, r₂) =
      if p₁ = p₂ then ((Fintype.card κ : ℂ))⁻¹ * (σ₁ p₁).mat r₁ r₂ else 0) :
    ((Fintype.card κ : ℝ))⁻¹ * ∑ p : κ, rootFidelity (σ₀ p) (σ₁ p) ≤ rootFidelity ρ₀ ρ₁ := by
  have hcard_pos : (0 : ℝ) < (Fintype.card κ : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hcard_pos
  have hsqrt_mul : ((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹ *
      ((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹ = ((Fintype.card κ : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (le_of_lt hcard_pos), Complex.ofReal_inv, Complex.ofReal_natCast]
  have hmk_sqrt : ∀ (σ : κ → DensityOp α) (ρ : DensityOp (κ × α)),
      (∀ p₁ p₂ r₁ r₂, ρ.mat (p₁, r₁) (p₂, r₂) =
        if p₁ = p₂ then ((Fintype.card κ : ℂ))⁻¹ * (σ p₁).mat r₁ r₂ else 0) →
      ρ.sqrtMat = Matrix.of fun (p₁, r₁) (p₂, r₂) ↦
        if p₁ = p₂ then ((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹ * (σ p₁).sqrtMat r₁ r₂ else 0 := by
    intro σ ρ hρ
    let R : Matrix (κ × α) (κ × α) ℂ :=
      Matrix.of fun (p₁, r₁) (p₂, r₂) ↦
        if p₁ = p₂ then ((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹ * (σ p₁).sqrtMat r₁ r₂ else 0
    have hR_psd : R.PosSemidef := by
      let c : ℝ := (Real.sqrt (Fintype.card κ : ℝ))⁻¹
      have hc : 0 ≤ c := by positivity
      let blk (p : κ) : Matrix (κ × α) (κ × α) ℂ :=
        let E : Matrix (κ × α) α ℂ := Matrix.of fun (q, r) s ↦ if q = p ∧ r = s then 1 else 0
        E * (σ p).sqrtMat * Eᴴ
      have hblk_psd : ∀ p : κ, (blk p).PosSemidef := fun p ↦
        (σ p).sqrtMat_posSemidef.mul_mul_conjTranspose_same _
      have hR_eq : R = (c : ℂ) • ∑ p : κ, blk p := by
        ext ⟨p₁, r₁⟩ ⟨p₂, r₂⟩
        simp only [R, blk, Matrix.of_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
          c, Complex.ofReal_inv]
        have hterm : ∀ p : κ,
            ((Matrix.of fun ((q, r) : κ × α) (s : α) ↦ if q = p ∧ r = s then (1 : ℂ) else 0) * (σ p).sqrtMat *
              (Matrix.of fun ((q, r) : κ × α) (s : α) ↦ if q = p ∧ r = s then (1 : ℂ) else 0)ᴴ) (p₁, r₁) (p₂, r₂) =
            if p₁ = p ∧ p₂ = p then (σ p).sqrtMat r₁ r₂ else 0 := by
          intro p
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
          rw [Finset.sum_eq_single r₂]
          · rw [Finset.sum_eq_single r₁]
            · by_cases h1 : p₁ = p <;> by_cases h2 : p₂ = p <;> simp [h1, h2]
            · intro s₁ _ hne; simp [Ne.symm hne]
            · intro h; exact absurd (Finset.mem_univ r₁) h
          · intro s₂ _ hne; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ r₂) h
        simp_rw [hterm]
        by_cases hp : p₁ = p₂
        · subst hp
          simp only [↓reduceIte, and_self]
          rw [Finset.sum_eq_single p₁]
          · simp
          · intro p _ hne; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ p₁) h
        · simp only [hp, ↓reduceIte]
          have h0 : ∑ p : κ, (if p₁ = p ∧ p₂ = p then (σ p).sqrtMat r₁ r₂ else 0) = 0 := by
            apply Finset.sum_eq_zero; intro p _
            have : ¬ (p₁ = p ∧ p₂ = p) := fun ⟨h1, h2⟩ ↦ hp (h1.trans h2.symm)
            simp [this]
          rw [h0, mul_zero]
      rw [hR_eq]
      have hsum_psd : (∑ p : κ, blk p).PosSemidef :=
        Finset.sum_induction _ (fun M : Matrix _ _ ℂ ↦ M.PosSemidef) (fun _ _ ha hb ↦ ha.add hb)
          Matrix.PosSemidef.zero (fun p _ ↦ hblk_psd p)
      simpa [Complex.real_smul] using hsum_psd.smul hc
    have hR_sq : R * R = ρ.mat := by
      ext ⟨p₁, r₁⟩ ⟨p₂, r₂⟩
      rw [hρ p₁ p₂ r₁ r₂]
      simp only [R, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single p₁]
      · by_cases hp : p₁ = p₂
        · subst hp
          simp only [↓reduceIte]
          have hsq := congr_fun (congr_fun (σ p₁).sqrtMat_mul_self r₁) r₂
          rw [← hsq, Matrix.mul_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro t _
          calc ((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹ * (σ p₁).sqrtMat r₁ t *
                (((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹ * (σ p₁).sqrtMat t r₂)
              = (((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹ *
                  ((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹) *
                ((σ p₁).sqrtMat r₁ t * (σ p₁).sqrtMat t r₂) := by ring
            _ = _ := by rw [hsqrt_mul]
        · simp [hp]
      · intro q _ hne; apply Finset.sum_eq_zero; intro t _; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ p₁) h
    exact (ρ.sqrtMat_unique hR_psd hR_sq).symm
  have hsq0 := hmk_sqrt σ₀ ρ₀ hρ₀
  have hsq1 := hmk_sqrt σ₁ ρ₁ hρ₁
  choose U_p hU_p using fun p : κ ↦ exists_unitary_trace_eq_traceNorm ((σ₀ p).sqrtMat * (σ₁ p).sqrtMat)
  let U : Matrix (κ × α) (κ × α) ℂ :=
    Matrix.of fun (p₁, r₁) (p₂, r₂) ↦ if p₁ = p₂ then (U_p p₁ : Matrix α α ℂ) r₁ r₂ else 0
  have hU_mem : U ∈ Matrix.unitaryGroup (κ × α) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext ⟨p₁, r₁⟩ ⟨p₂, r₂⟩
    simp only [U, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Fintype.sum_prod_type,
      Matrix.one_apply]
    rw [Finset.sum_eq_single p₁]
    · by_cases hp : p₁ = p₂
      · subst hp
        simp only [↓reduceIte, Prod.mk.injEq, true_and]
        have h := congr_fun (congr_fun (Unitary.coe_star_mul_self (U_p p₁)) r₁) r₂
        simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h
      · simp [hp]
    · intro q _ hne; apply Finset.sum_eq_zero; intro t _; simp [hne]
    · intro h; exact absurd (Finset.mem_univ p₁) h
  have htr : (Uᴴ * (ρ₀.sqrtMat * ρ₁.sqrtMat)).trace =
      ((Fintype.card κ : ℂ))⁻¹ * ∑ p : κ, ((rootFidelity (σ₀ p) (σ₁ p) : ℝ) : ℂ) := by
    rw [hsq0, hsq1]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, U,
      Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    have hblock : ∑ r : α, ∑ q₁ : κ, ∑ t₁ : α,
        star (if q₁ = p then (U_p q₁ : Matrix α α ℂ) t₁ r else 0) *
        ∑ q₂ : κ, ∑ t₂ : α,
          (if q₁ = q₂ then ((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹ * (σ₀ q₁).sqrtMat t₁ t₂ else 0) *
          (if q₂ = p then ((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹ * (σ₁ q₂).sqrtMat t₂ r else 0) =
        ((Fintype.card κ : ℂ))⁻¹ * (((U_p p : Matrix α α ℂ)ᴴ * ((σ₀ p).sqrtMat * (σ₁ p).sqrtMat)).trace) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _
      rw [Finset.sum_eq_single p]
      · simp only [↓reduceIte]
        apply Finset.sum_congr rfl; intro t₁ _
        rw [Finset.sum_eq_single p]
        · simp only [↓reduceIte, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro t₂ _
          calc star ((U_p p : Matrix α α ℂ) t₁ r) *
                (((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹ * (σ₀ p).sqrtMat t₁ t₂ *
                  (((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹ * (σ₁ p).sqrtMat t₂ r))
              = (((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹ *
                  ((Real.sqrt (Fintype.card κ : ℝ) : ℂ))⁻¹) *
                (star ((U_p p : Matrix α α ℂ) t₁ r) * ((σ₀ p).sqrtMat t₁ t₂ * (σ₁ p).sqrtMat t₂ r)) := by ring
            _ = _ := by rw [hsqrt_mul]
        · intro q₂ _ hne; apply Finset.sum_eq_zero; intro t₂ _; simp [hne]
        · intro h; exact absurd (Finset.mem_univ p) h
      · intro q₁ _ hne; apply Finset.sum_eq_zero; intro t₁ _; simp [hne]
      · intro h; exact absurd (Finset.mem_univ p) h
    rw [hblock, hU_p p, traceNorm_sqrt_mul_sqrt (σ₀ p) (σ₁ p)]
  have hle := re_trace_unitary_mul_le_traceNorm ⟨U, hU_mem⟩ (ρ₀.sqrtMat * ρ₁.sqrtMat)
  rw [traceNorm_sqrt_mul_sqrt ρ₀ ρ₁] at hle
  have hre : ((Uᴴ * (ρ₀.sqrtMat * ρ₁.sqrtMat)).trace).re =
      ((Fintype.card κ : ℝ))⁻¹ * ∑ p : κ, rootFidelity (σ₀ p) (σ₁ p) := by
    rw [htr]
    have hcast : ((Fintype.card κ : ℂ))⁻¹ * ∑ p : κ, ((rootFidelity (σ₀ p) (σ₁ p) : ℝ) : ℂ) =
        ((((Fintype.card κ : ℝ))⁻¹ * ∑ p : κ, rootFidelity (σ₀ p) (σ₁ p) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hcast, Complex.ofReal_re]
  linarith

/-! ### Conditional Synthesized States `condSynthState` -/

/-- Normalized conditional output state `ρ_{p, b}` of `W_n^{(i)}` given prefix `p : Fin i.val → Bool`
and bit `b : Bool`. -/
noncomputable def condSynthState (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n))
    (p : Fin i.val → Bool) (b : Bool) : DensityOp (Fin (2 ^ n) → d) where
  mat := ((2 : ℂ) ^ (2 ^ n - 1 - i.val))⁻¹ • synthBlockMat W n i p b
  posSemidef := by
    let c : ℝ := ((2 : ℝ) ^ (2 ^ n - 1 - i.val))⁻¹
    have hc : 0 ≤ c := by positivity
    have hsum_psd : (synthBlockMat W n i p b).PosSemidef := by
      unfold synthBlockMat
      exact Finset.sum_induction _ (fun M : Matrix _ _ ℂ ↦ M.PosSemidef) (fun _ _ ha hb ↦ ha.add hb)
        Matrix.PosSemidef.zero (fun u _ ↦ (productState W n (arikanTransform n u)).posSemidef)
    have hc_eq : ((2 : ℂ) ^ (2 ^ n - 1 - i.val))⁻¹ = (c : ℂ) := by
      simp [c]
    rw [hc_eq]
    simpa [Complex.real_smul] using hsum_psd.smul hc
  trace_one := by
    rw [Matrix.trace_smul, smul_eq_mul]
    have htr : (synthBlockMat W n i p b).trace = ((2 ^ (2 ^ n - 1 - i.val) : ℕ) : ℂ) := by
      unfold synthBlockMat
      rw [Matrix.trace_sum]
      have h1 : ∀ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ prefixOf i u = p ∧ u i = b),
          (productState W n (arikanTransform n u)).mat.trace = 1 :=
        fun u _ ↦ (productState W n (arikanTransform n u)).trace_one
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one,
        card_filter_prefix_at_eq]
    rw [htr]
    push_cast
    exact inv_mul_cancel₀ (by positivity)

/-- Average conditional root fidelity over prefixes `p` is bounded above by `(synthChannel W n i).fidelityParam`. -/
lemma avg_condSynth_rootFidelity_le (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n)) :
    ((2 : ℝ) ^ i.val)⁻¹ *
      ∑ p : Fin i.val → Bool,
        rootFidelity (condSynthState W n i p false) (condSynthState W n i p true) ≤
      (synthChannel W n i).fidelityParam := by
  have hcard : (Fintype.card (Fin i.val → Bool) : ℝ) = (2 : ℝ) ^ i.val := by
    simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hcardC : (Fintype.card (Fin i.val → Bool) : ℂ) = (2 : ℂ) ^ i.val := by
    simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [← hcard]
  have hblock : ∀ b : Bool, ∀ (p₁ p₂ : Fin i.val → Bool) (r₁ r₂ : Fin (2 ^ n) → d),
      ((synthChannel W n i).out b).mat (p₁, r₁) (p₂, r₂) =
        if p₁ = p₂ then
          ((Fintype.card (Fin i.val → Bool) : ℂ))⁻¹ * (condSynthState W n i p₁ b).mat r₁ r₂
        else 0 := by
    intro b p₁ p₂ r₁ r₂
    simp only [synthChannel, synthState, condSynthState, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, hcardC]
    by_cases hp : p₁ = p₂
    · subst hp; simp only [↓reduceIte]
      rw [← mul_assoc, ← mul_inv, ← pow_add]
      have hexp : i.val + (2 ^ n - 1 - i.val) = 2 ^ n - 1 := by omega
      rw [hexp]
    · simp [hp]
  exact blockDiag_rootFidelity_ge
    (fun p ↦ condSynthState W n i p false)
    (fun p ↦ condSynthState W n i p true)
    ((synthChannel W n i).out false)
    ((synthChannel W n i).out true)
    (hblock false) (hblock true)

/-! ### `G_N`-Coset Classical–Quantum Polar Code -/

/-- Embedding a message `m` on the information set `infoSet` and frozen bits `frozen` on `infoSetᶜ`
into a full input vector `u : Fin (2^n) → Bool`. -/
def embedMsg {N : ℕ} (infoSet : Finset (Fin N)) (frozen : Fin N → Bool)
    (m : {i : Fin N // i ∈ infoSet} → Bool) : Fin N → Bool :=
  fun i ↦ if hi : i ∈ infoSet then m ⟨i, hi⟩ else frozen i

/-- A deterministic `G_N`-coset classical–quantum polar code of blocklength `N = 2^n` for channel `W`. -/
structure CosetPolarCode (W : CQChannel d) (n : ℕ) where
  /-- Information set `𝒜 ⊆ Fin (2^n)`. -/
  infoSet : Finset (Fin (2 ^ n))
  /-- Deterministic frozen vector (values on `i ∉ infoSet` fix the coset). -/
  frozenBits : Fin (2 ^ n) → Bool
  /-- Decoding POVM `{Λ_{u_𝒜}}` on `ℂ^{d^N}`. -/
  povm : ({i : Fin (2 ^ n) // i ∈ infoSet} → Bool) →
    Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ
  /-- Each POVM element is positive semidefinite. -/
  povm_posSemidef : ∀ m, (povm m).PosSemidef
  /-- The POVM elements sum to the identity operator. -/
  povm_sum_one : ∑ m, povm m = 1

namespace CosetPolarCode

/-- Code rate `R = |𝒜| / 2^n`. -/
noncomputable def rate {W : CQChannel d} {n : ℕ} (C : CosetPolarCode W n) : ℝ :=
  (C.infoSet.card : ℝ) / ((2 : ℝ) ^ n)

/-- Arıkan `G_N`-coset encoding map `u_𝒜 ↦ (u_𝒜, u_{𝒜^c}) G_N`. -/
def encode {W : CQChannel d} {n : ℕ} (C : CosetPolarCode W n)
    (m : {i : Fin (2 ^ n) // i ∈ C.infoSet} → Bool) : Fin (2 ^ n) → Bool :=
  arikanTransform n (embedMsg C.infoSet C.frozenBits m)

/-- Average block-error probability `P_e(N, R)` under uniform messages `u_𝒜`. -/
noncomputable def avgBlockError {W : CQChannel d} {n : ℕ} (C : CosetPolarCode W n) : ℝ :=
  ((2 : ℝ) ^ C.infoSet.card)⁻¹ *
    ∑ m : {i : Fin (2 ^ n) // i ∈ C.infoSet} → Bool,
      (1 - ((C.povm m * (productState W n (C.encode m)).mat).trace).re)

end CosetPolarCode

/-! ### Quantum Successive-Cancellation (QSC) Sequential Projective/POVM Decoder -/

/-- Binary Helstrom projector for coordinate `i`, prefix `p`, and hypothesized bit `b`. -/
noncomputable def qscStepProj (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n))
    (p : Fin i.val → Bool) (b : Bool) :
    Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ :=
  if b = false then
    helstromProjector (condSynthState W n i p false) (condSynthState W n i p true)
  else
    1 - helstromProjector (condSynthState W n i p false) (condSynthState W n i p true)

lemma qscStepProj_isProjector (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n))
    (p : Fin i.val → Bool) (b : Bool) :
    IsProjector (qscStepProj W n i p b) := by
  unfold qscStepProj
  split_ifs
  · exact helstromProjector_isProjector _ _
  · exact (helstromProjector_isProjector _ _).sub_one

lemma qscStepProj_sum_bool (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n))
    (p : Fin i.val → Bool) :
    qscStepProj W n i p false + qscStepProj W n i p true = 1 := by
  simp [qscStepProj]

lemma seqProd_append {α : Type*} [Fintype α] [DecidableEq α]
    (Ps Qs : List (Matrix α α ℂ)) :
    seqProd (Ps ++ Qs) = seqProd Qs * seqProd Ps := by
  induction Ps with
  | nil => simp [seqProd]
  | cons P Ps ih =>
    simp only [List.cons_append, seqProd_cons, ih, Matrix.mul_assoc]

/-- List of the first `k` QSC step projectors (`0, ..., k - 1`) for vector `u`. -/
noncomputable def qscProjListPrefix (W : CQChannel d) (n : ℕ)
    (infoSet : Finset (Fin (2 ^ n))) :
    (k : ℕ) → k ≤ 2 ^ n → (Fin (2 ^ n) → Bool) →
      List (Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ)
  | 0, _, _ => []
  | k + 1, hk, u =>
      let i : Fin (2 ^ n) := ⟨k, by omega⟩
      qscProjListPrefix W n infoSet k (by omega) u ++
        [if i ∈ infoSet then qscStepProj W n i (prefixOf i u) (u i) else 1]

/-- Full list of all `2^n` QSC step projectors for vector `u`. -/
noncomputable def qscProjList (W : CQChannel d) (n : ℕ)
    (infoSet : Finset (Fin (2 ^ n))) (u : Fin (2 ^ n) → Bool) :
    List (Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ) :=
  qscProjListPrefix W n infoSet (2 ^ n) le_rfl u

lemma qscProjListPrefix_isProjector (W : CQChannel d) (n : ℕ)
    (infoSet : Finset (Fin (2 ^ n))) (k : ℕ) (hk : k ≤ 2 ^ n) (u : Fin (2 ^ n) → Bool) :
    ∀ P ∈ qscProjListPrefix W n infoSet k hk u, IsProjector P := by
  induction k with
  | zero => intro P hP; simp [qscProjListPrefix] at hP
  | succ k ih =>
    intro P hP
    simp only [qscProjListPrefix, List.mem_append, List.mem_singleton] at hP
    rcases hP with hP | rfl
    · exact ih (by omega) P hP
    · split_ifs
      · exact qscStepProj_isProjector W n ⟨k, by omega⟩ _ _
      · exact isProjector_one

/-- Sequential QSC Kraus operator `P_{k-1} ⋯ P_0` for the first `k` steps. -/
noncomputable def qscPrefixKraus (W : CQChannel d) (n : ℕ)
    (infoSet : Finset (Fin (2 ^ n))) (k : ℕ) (hk : k ≤ 2 ^ n) (u : Fin (2 ^ n) → Bool) :
    Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ :=
  seqProd (qscProjListPrefix W n infoSet k hk u)

lemma qscPrefixKraus_zero (W : CQChannel d) (n : ℕ) (infoSet : Finset (Fin (2 ^ n)))
    (u : Fin (2 ^ n) → Bool) :
    qscPrefixKraus W n infoSet 0 (Nat.zero_le _) u = 1 := rfl

lemma qscPrefixKraus_succ (W : CQChannel d) (n : ℕ) (infoSet : Finset (Fin (2 ^ n)))
    (k : ℕ) (hk : k + 1 ≤ 2 ^ n) (u : Fin (2 ^ n) → Bool) :
    qscPrefixKraus W n infoSet (k + 1) hk u =
      (if (⟨k, by omega⟩ : Fin (2 ^ n)) ∈ infoSet then
        qscStepProj W n ⟨k, by omega⟩ (prefixOf ⟨k, by omega⟩ u) (u ⟨k, by omega⟩)
       else 1) *
      qscPrefixKraus W n infoSet k (by omega) u := by
  simp only [qscPrefixKraus, qscProjListPrefix, seqProd_append, seqProd_cons, seqProd_nil,
    Matrix.one_mul]

/-- `qscPrefixKraus k` depends only on coordinates `< k` of `u`. -/
lemma qscPrefixKraus_congr (W : CQChannel d) (n : ℕ) (infoSet : Finset (Fin (2 ^ n)))
    (k : ℕ) (hk : k ≤ 2 ^ n) {u v : Fin (2 ^ n) → Bool}
    (h : ∀ j : Fin (2 ^ n), j.val < k → u j = v j) :
    qscPrefixKraus W n infoSet k hk u = qscPrefixKraus W n infoSet k hk v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [qscPrefixKraus_succ, qscPrefixKraus_succ]
    have hprev := ih (by omega) (fun j hj ↦ h j (by omega))
    have hpref : prefixOf ⟨k, by omega⟩ u = prefixOf ⟨k, by omega⟩ v := by
      funext j; exact h ⟨j.val, Nat.lt_trans j.isLt (by omega)⟩ (Nat.lt_succ_of_lt j.isLt)
    have huk : u ⟨k, by omega⟩ = v ⟨k, by omega⟩ := h ⟨k, by omega⟩ (Nat.lt_succ_self k)
    rw [hprev, hpref, huk]

/-- Inductive POVM completeness: summing `(qscPrefixKraus k)ᴴ * (qscPrefixKraus k)` over all
message assignments on `infoSet ∩ {0, ..., k - 1}` yields the identity matrix `1`. -/
lemma qscPrefixKraus_sum_one (W : CQChannel d) (n : ℕ)
    (infoSet : Finset (Fin (2 ^ n))) (frozen : Fin (2 ^ n) → Bool)
    (k : ℕ) (hk : k ≤ 2 ^ n) :
    (∑ m : {i : Fin (2 ^ n) // i ∈ infoSet ∧ i.val < k} → Bool,
      let u : Fin (2 ^ n) → Bool := fun i ↦ if hi : i ∈ infoSet ∧ i.val < k then m ⟨i, hi⟩ else frozen i
      (qscPrefixKraus W n infoSet k hk u)ᴴ * qscPrefixKraus W n infoSet k hk u) = 1 := by
  induction k with
  | zero =>
    have hsub : IsEmpty {i : Fin (2 ^ n) // i ∈ infoSet ∧ i.val < 0} := ⟨fun ⟨_, _, h⟩ ↦ by omega⟩
    have huniq : Unique ({i : Fin (2 ^ n) // i ∈ infoSet ∧ i.val < 0} → Bool) := Pi.uniqueOfIsEmpty _
    rw [Fintype.sum_unique]
    simp [qscPrefixKraus_zero]
  | succ k ih =>
    set ik : Fin (2 ^ n) := ⟨k, by omega⟩
    by_cases hik : ik ∈ infoSet
    · -- Split `{i ∈ infoSet | i < k + 1} → Bool` into `Bool × ({i ∈ infoSet | i < k} → Bool)`
      let e : ({i : Fin (2 ^ n) // i ∈ infoSet ∧ i.val < k + 1} → Bool) ≃
          Bool × ({i : Fin (2 ^ n) // i ∈ infoSet ∧ i.val < k} → Bool) :=
        { toFun := fun m ↦ (m ⟨ik, hik, Nat.lt_succ_self k⟩, fun ⟨i, hi, hlt⟩ ↦ m ⟨i, hi, by omega⟩)
          invFun := fun ⟨b, m'⟩ ⟨i, hi, hlt⟩ ↦
            if h : i.val < k then m' ⟨i, hi, h⟩ else b
          left_inv := fun m ↦ by
            funext ⟨i, hi, hlt⟩
            dsimp only
            split_ifs with h
            · rfl
            · have hi_eq : i = ik := Fin.ext (by dsimp [ik]; omega)
              subst hi_eq; rfl
          right_inv := fun ⟨b, m'⟩ ↦ by
            ext
            · simp [ik]
            · rename_i x; simp [x.2.2] }
      rw [← Equiv.sum_comp e.symm]
      rw [Fintype.sum_prod_type_right]
      have hinner : ∀ m' : {i : Fin (2 ^ n) // i ∈ infoSet ∧ i.val < k} → Bool,
          (∑ b : Bool,
            let u := fun i : Fin (2 ^ n) ↦
              if hi : i ∈ infoSet ∧ i.val < k + 1 then e.symm (b, m') ⟨i, hi⟩ else frozen i
            (qscPrefixKraus W n infoSet (k + 1) hk u)ᴴ * qscPrefixKraus W n infoSet (k + 1) hk u) =
          let u' := fun i : Fin (2 ^ n) ↦
            if hi : i ∈ infoSet ∧ i.val < k then m' ⟨i, hi⟩ else frozen i
          (qscPrefixKraus W n infoSet k (by omega) u')ᴴ * qscPrefixKraus W n infoSet k (by omega) u' := by
        intro m'
        set u' : Fin (2 ^ n) → Bool := fun i ↦ if hi : i ∈ infoSet ∧ i.val < k then m' ⟨i, hi⟩ else frozen i
        set K : Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ := qscPrefixKraus W n infoSet k (by omega) u'
        have hstep : ∀ b : Bool,
            let u := fun i : Fin (2 ^ n) ↦
              if hi : i ∈ infoSet ∧ i.val < k + 1 then e.symm (b, m') ⟨i, hi⟩ else frozen i
            (qscPrefixKraus W n infoSet (k + 1) hk u)ᴴ * qscPrefixKraus W n infoSet (k + 1) hk u =
              Kᴴ * qscStepProj W n ik (prefixOf ik u') b * K := by
          intro b
          set u : Fin (2 ^ n) → Bool := fun i ↦
            if hi : i ∈ infoSet ∧ i.val < k + 1 then e.symm (b, m') ⟨i, hi⟩ else frozen i
          have hagree : ∀ j : Fin (2 ^ n), j.val < k → u j = u' j := by
            intro j hj
            have hj' : j.val < k + 1 := by omega
            by_cases hmem : j ∈ infoSet
            · simp [u, u', e, hmem, hj, hj', Nat.le_of_lt hj]
            · simp [u, u', hmem]
          have hK : qscPrefixKraus W n infoSet k (by omega) u = K :=
            qscPrefixKraus_congr W n infoSet k (by omega) hagree
          have hpref : prefixOf ik u = prefixOf ik u' := by
            funext j; exact hagree ⟨j.val, Nat.lt_trans j.isLt ik.isLt⟩ j.isLt
          have huk : u ik = b := by
            simp [u, e, hik, ik]
          have hP := qscStepProj_isProjector W n ik (prefixOf ik u') b
          dsimp only
          rw [qscPrefixKraus_succ]
          simp only [ik, hik, ↓reduceIte, hK, hpref, huk]
          calc (qscStepProj W n ik (prefixOf ik u') b * K)ᴴ *
                (qscStepProj W n ik (prefixOf ik u') b * K)
              = Kᴴ * ((qscStepProj W n ik (prefixOf ik u') b)ᴴ *
                  qscStepProj W n ik (prefixOf ik u') b) * K := by
                    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
            _ = Kᴴ * qscStepProj W n ik (prefixOf ik u') b * K := by
                  rw [hP.1, hP.2]
        simp_rw [hstep]
        rw [Fintype.sum_bool, add_comm]
        calc Kᴴ * qscStepProj W n ik (prefixOf ik u') false * K +
              Kᴴ * qscStepProj W n ik (prefixOf ik u') true * K
            = Kᴴ * (qscStepProj W n ik (prefixOf ik u') false +
                qscStepProj W n ik (prefixOf ik u') true) * K := by
                  simp only [Matrix.mul_add, Matrix.add_mul]
          _ = Kᴴ * K := by rw [qscStepProj_sum_bool, Matrix.mul_one]
      simp_rw [hinner]
      exact ih (by omega)
    · -- `ik ∉ infoSet`: domains are equivalent and step `k` multiplies by `1`
      let e : ({i : Fin (2 ^ n) // i ∈ infoSet ∧ i.val < k + 1} → Bool) ≃
          ({i : Fin (2 ^ n) // i ∈ infoSet ∧ i.val < k} → Bool) :=
        { toFun := fun m ⟨i, hi, hlt⟩ ↦ m ⟨i, hi, by omega⟩
          invFun := fun m' ⟨i, hi, hlt⟩ ↦
            m' ⟨i, hi, by
              have hne : i.val ≠ k := fun h ↦ hik (by convert hi; exact Fin.ext h.symm)
              omega⟩
          left_inv := fun m ↦ by funext ⟨i, hi, hlt⟩; rfl
          right_inv := fun m' ↦ by funext ⟨i, hi, hlt⟩; rfl }
      rw [← Equiv.sum_comp e.symm]
      have hterm : ∀ m' : {i : Fin (2 ^ n) // i ∈ infoSet ∧ i.val < k} → Bool,
          let u := fun i : Fin (2 ^ n) ↦
            if hi : i ∈ infoSet ∧ i.val < k + 1 then e.symm m' ⟨i, hi⟩ else frozen i
          (qscPrefixKraus W n infoSet (k + 1) hk u)ᴴ * qscPrefixKraus W n infoSet (k + 1) hk u =
          let u' := fun i : Fin (2 ^ n) ↦
            if hi : i ∈ infoSet ∧ i.val < k then m' ⟨i, hi⟩ else frozen i
          (qscPrefixKraus W n infoSet k (by omega) u')ᴴ * qscPrefixKraus W n infoSet k (by omega) u' := by
        intro m'
        set u : Fin (2 ^ n) → Bool := fun i ↦
          if hi : i ∈ infoSet ∧ i.val < k + 1 then e.symm m' ⟨i, hi⟩ else frozen i
        set u' : Fin (2 ^ n) → Bool := fun i ↦
          if hi : i ∈ infoSet ∧ i.val < k then m' ⟨i, hi⟩ else frozen i
        have hagree : ∀ j : Fin (2 ^ n), j.val < k → u j = u' j := by
          intro j hj
          have hj' : j.val < k + 1 := by omega
          by_cases hmem : j ∈ infoSet
          · simp [u, u', e, hmem, hj, hj', Nat.le_of_lt hj]
          · simp [u, u', hmem]
        dsimp only
        rw [qscPrefixKraus_succ]
        simp only [ik, hik, ↓reduceIte, Matrix.one_mul,
          qscPrefixKraus_congr W n infoSet k (by omega) hagree]
      simp_rw [hterm]
      exact ih (by omega)

/-- The Quantum Successive-Cancellation (QSC) `G_N`-coset polar code for channel `W`, depth `n`,
information set `infoSet`, and deterministic frozen vector `frozen`. -/
noncomputable def qscPolarCode (W : CQChannel d) (n : ℕ)
    (infoSet : Finset (Fin (2 ^ n))) (frozen : Fin (2 ^ n) → Bool) :
    CosetPolarCode W n where
  infoSet := infoSet
  frozenBits := frozen
  povm m :=
    (qscPrefixKraus W n infoSet (2 ^ n) le_rfl (embedMsg infoSet frozen m))ᴴ *
      qscPrefixKraus W n infoSet (2 ^ n) le_rfl (embedMsg infoSet frozen m)
  povm_posSemidef m := Matrix.posSemidef_conjTranspose_mul_self _
  povm_sum_one := by
    let e : ({i : Fin (2 ^ n) // i ∈ infoSet ∧ i.val < 2 ^ n} → Bool) ≃
        ({i : Fin (2 ^ n) // i ∈ infoSet} → Bool) :=
      { toFun := fun m ⟨i, hi⟩ ↦ m ⟨i, hi, i.isLt⟩
        invFun := fun m ⟨i, hi, _⟩ ↦ m ⟨i, hi⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [← Equiv.sum_comp e]
    have hcongr : ∀ m : {i : Fin (2 ^ n) // i ∈ infoSet ∧ i.val < 2 ^ n} → Bool,
        embedMsg infoSet frozen (e m) =
          fun i ↦ if hi : i ∈ infoSet ∧ i.val < 2 ^ n then m ⟨i, hi⟩ else frozen i := by
      intro m; funext i
      by_cases hi : i ∈ infoSet
      · simp [embedMsg, e, hi, i.isLt]
      · simp [embedMsg, hi]
    simp_rw [hcongr]
    exact qscPrefixKraus_sum_one W n infoSet frozen (2 ^ n) le_rfl

/-! ### Wilde–Guha QSC Error Bound ([12, Proposition 4]) -/

/-- Sum of `List.map` over `qscProjListPrefix` equals the Finset sum over `i ∈ infoSet` with `i < k`. -/
private lemma qscProjListPrefix_map_sum (W : CQChannel d) (n : ℕ)
    (infoSet : Finset (Fin (2 ^ n))) (ρ : DensityOp (Fin (2 ^ n) → d))
    (u : Fin (2 ^ n) → Bool) (k : ℕ) (hk : k ≤ 2 ^ n) :
    ((qscProjListPrefix W n infoSet k hk u).map
      (fun P ↦ (((1 - P) * ρ.mat).trace).re)).sum =
    ∑ i ∈ infoSet.filter (fun i : Fin (2 ^ n) ↦ i.val < k),
      (((1 - qscStepProj W n i (prefixOf i u) (u i)) * ρ.mat).trace).re := by
  induction k with
  | zero =>
    have hempty : infoSet.filter (fun i : Fin (2 ^ n) ↦ i.val < 0) = ∅ := by
      ext i; simp
    simp [qscProjListPrefix, hempty]
  | succ k ih =>
    simp only [qscProjListPrefix, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, ih (by omega)]
    set ik : Fin (2 ^ n) := ⟨k, by omega⟩
    by_cases hik : ik ∈ infoSet
    · simp only [hik, ↓reduceIte]
      have hfilt : infoSet.filter (fun i : Fin (2 ^ n) ↦ i.val < k + 1) =
          insert ik (infoSet.filter (fun i : Fin (2 ^ n) ↦ i.val < k)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_insert, ik]
        constructor
        · intro ⟨hi, hlt⟩
          by_cases h : i.val = k
          · left; exact Fin.ext h
          · right; exact ⟨hi, by omega⟩
        · rintro (rfl | ⟨hi, hlt⟩)
          · exact ⟨hik, Nat.lt_succ_self k⟩
          · exact ⟨hi, by omega⟩
      have hnotmem : ik ∉ infoSet.filter (fun i : Fin (2 ^ n) ↦ i.val < k) := by
        simp [ik]
      rw [hfilt, Finset.sum_insert hnotmem, add_comm]
    · simp only [hik, ↓reduceIte, sub_self, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re,
        add_zero]
      have hfilt : infoSet.filter (fun i : Fin (2 ^ n) ↦ i.val < k + 1) =
          infoSet.filter (fun i : Fin (2 ^ n) ↦ i.val < k) := by
        ext i; simp only [Finset.mem_filter]
        constructor
        · intro ⟨hi, hlt⟩
          have hne : i.val ≠ k := fun h ↦ hik (by convert hi; exact Fin.ext h.symm)
          exact ⟨hi, by omega⟩
        · intro ⟨hi, hlt⟩; exact ⟨hi, by omega⟩
      rw [hfilt]

/-- Finite Jensen / Cauchy–Schwarz inequality for `Real.sqrt`:
`(|s|⁻¹ * ∑ x ∈ s, √(f x)) ≤ √(|s|⁻¹ * ∑ x ∈ s, f x)`. -/
private lemma avg_sqrt_le_sqrt_avg {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) :
    (s.card : ℝ)⁻¹ * ∑ x ∈ s, Real.sqrt (f x) ≤
      Real.sqrt ((s.card : ℝ)⁻¹ * ∑ x ∈ s, f x) := by
  have hcard_pos : (0 : ℝ) < (s.card : ℝ) := Nat.cast_pos.mpr hs.card_pos
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ ↦ (1 : ℝ)) (fun x ↦ Real.sqrt (f x))
  have h1 : ∑ x ∈ s, (1 : ℝ) * Real.sqrt (f x) = ∑ x ∈ s, Real.sqrt (f x) := by simp
  have h2 : ∑ _x ∈ s, (1 : ℝ) ^ 2 = (s.card : ℝ) := by simp
  have h3 : ∑ x ∈ s, Real.sqrt (f x) ^ 2 = ∑ x ∈ s, f x :=
    Finset.sum_congr rfl fun x hx ↦ Real.sq_sqrt (hf x hx)
  rw [h1, h2, h3] at hcs
  have hsq : ((s.card : ℝ)⁻¹ * ∑ x ∈ s, Real.sqrt (f x)) ^ 2 ≤
      (s.card : ℝ)⁻¹ * ∑ x ∈ s, f x := by
    rw [mul_pow, inv_pow]
    have hcard_ne : (s.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
    calc ((s.card : ℝ) ^ 2)⁻¹ * (∑ x ∈ s, Real.sqrt (f x)) ^ 2
        ≤ ((s.card : ℝ) ^ 2)⁻¹ * ((s.card : ℝ) * ∑ x ∈ s, f x) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (s.card : ℝ)⁻¹ * ∑ x ∈ s, f x := by field_simp
  exact Real.le_sqrt_of_sq_le hsq

/-- **Wilde–Guha QSC Average Block-Error Bound**: Averaging `(qscPolarCode W n infoSet frozen).avgBlockError`
uniformly over all frozen-bit vectors `frozen : Fin (2^n) → Bool` yields
`2 √(∑_{i ∈ infoSet} (1 / 2) * Z(W_n^{(i)}))`. -/
theorem wilde_guha_qsc_avg_bound (W : CQChannel d) (n : ℕ) (infoSet : Finset (Fin (2 ^ n))) :
    ((2 : ℝ) ^ (2 ^ n))⁻¹ *
      ∑ frozen : Fin (2 ^ n) → Bool,
        (qscPolarCode W n infoSet frozen).avgBlockError ≤
      2 * Real.sqrt (∑ i ∈ infoSet, (1 / 2 : ℝ) * (synthChannel W n i).fidelityParam) := by
  -- Step 1: Uniform average over all `u : Fin (2^n) → Bool`
  let errU (u : Fin (2 ^ n) → Bool) : ℝ :=
    1 - ((qscPrefixKraus W n infoSet (2 ^ n) le_rfl u *
          (productState W n (arikanTransform n u)).mat *
          (qscPrefixKraus W n infoSet (2 ^ n) le_rfl u)ᴴ).trace).re
  let stepErr (u : Fin (2 ^ n) → Bool) (i : Fin (2 ^ n)) : ℝ :=
    (((1 - qscStepProj W n i (prefixOf i u) (u i)) *
      (productState W n (arikanTransform n u)).mat).trace).re
  have hstepErr_nn : ∀ u i, 0 ≤ stepErr u i := by
    intro u i
    have hP := qscStepProj_isProjector W n i (prefixOf i u) (u i)
    have htr : ((1 - qscStepProj W n i (prefixOf i u) (u i)) *
        (productState W n (arikanTransform n u)).mat).trace =
        ((1 - qscStepProj W n i (prefixOf i u) (u i)) *
        (productState W n (arikanTransform n u)).mat *
        (1 - qscStepProj W n i (prefixOf i u) (u i))ᴴ).trace := by
      rw [Matrix.trace_mul_cycle, hP.sub_one.1, hP.sub_one.2]
    unfold stepErr; rw [htr]
    have hpsd := (productState W n (arikanTransform n u)).posSemidef.mul_mul_conjTranspose_same
      (1 - qscStepProj W n i (prefixOf i u) (u i))
    have hre : (((1 - qscStepProj W n i (prefixOf i u) (u i)) *
        (productState W n (arikanTransform n u)).mat *
        (1 - qscStepProj W n i (prefixOf i u) (u i))ᴴ).trace).re =
        ∑ a, hpsd.isHermitian.eigenvalues a := by
      rw [hpsd.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
      apply Finset.sum_congr rfl; intro a _; exact Complex.ofReal_re _
    rw [hre]
    exact Finset.sum_nonneg fun a _ ↦ hpsd.eigenvalues_nonneg a
  have hsen_u : ∀ u : Fin (2 ^ n) → Bool,
      errU u ≤ 2 * Real.sqrt (∑ i ∈ infoSet, stepErr u i) := by
    intro u
    have h := sen_noncommutative_union_bound (productState W n (arikanTransform n u))
      (qscProjListPrefix W n infoSet (2 ^ n) le_rfl u)
      (qscProjListPrefix_isProjector W n infoSet (2 ^ n) le_rfl u)
    have hsum := qscProjListPrefix_map_sum W n infoSet (productState W n (arikanTransform n u))
      u (2 ^ n) le_rfl
    have hfilt : infoSet.filter (fun i : Fin (2 ^ n) ↦ i.val < 2 ^ n) = infoSet := by
      ext i; simp [i.isLt]
    rw [hsum, hfilt] at h
    exact h
  -- Step 2: Average `errU u` over all `u : Fin (2^n) → Bool` and apply Jensen for `sqrt`
  have hcard_u : ((Finset.univ : Finset (Fin (2 ^ n) → Bool)).card : ℝ) = (2 : ℝ) ^ (2 ^ n) := by
    simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have havg_sen : ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ u : Fin (2 ^ n) → Bool, errU u ≤
      2 * Real.sqrt (((2 : ℝ) ^ (2 ^ n))⁻¹ *
        ∑ u : Fin (2 ^ n) → Bool, ∑ i ∈ infoSet, stepErr u i) := by
    calc ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ u : Fin (2 ^ n) → Bool, errU u
        ≤ ((2 : ℝ) ^ (2 ^ n))⁻¹ *
            ∑ u : Fin (2 ^ n) → Bool, (2 * Real.sqrt (∑ i ∈ infoSet, stepErr u i)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact Finset.sum_le_sum fun u _ ↦ hsen_u u
      _ = 2 * (((Finset.univ : Finset (Fin (2 ^ n) → Bool)).card : ℝ)⁻¹ *
            ∑ u : Fin (2 ^ n) → Bool, Real.sqrt (∑ i ∈ infoSet, stepErr u i)) := by
              rw [← Finset.mul_sum, hcard_u]; ring
      _ ≤ 2 * Real.sqrt (((Finset.univ : Finset (Fin (2 ^ n) → Bool)).card : ℝ)⁻¹ *
            ∑ u : Fin (2 ^ n) → Bool, ∑ i ∈ infoSet, stepErr u i) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact avg_sqrt_le_sqrt_avg Finset.univ Finset.univ_nonempty
                (fun u ↦ ∑ i ∈ infoSet, stepErr u i)
                (fun u _ ↦ Finset.sum_nonneg fun i _ ↦ hstepErr_nn u i)
      _ = _ := by rw [hcard_u]
  -- Step 3: For each `i`, average `stepErr u i` over `u` and bound by `(1 / 2) * Z(W_n^{(i)})`
  have havg_i : ∀ i : Fin (2 ^ n),
      ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ u : Fin (2 ^ n) → Bool, stepErr u i ≤
        (1 / 2 : ℝ) * (synthChannel W n i).fidelityParam := by
    intro i
    -- Partition `u` by `(prefixOf i u, u i)`
    have hpart : ∑ u : Fin (2 ^ n) → Bool, stepErr u i =
        ∑ p : Fin i.val → Bool, ∑ b : Bool,
          ∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ prefixOf i u = p ∧ u i = b),
            stepErr u i := by
      have h1 : ∀ u : Fin (2 ^ n) → Bool,
          stepErr u i = ∑ p : Fin i.val → Bool, ∑ b : Bool,
            if prefixOf i u = p ∧ u i = b then stepErr u i else 0 := by
        intro u
        rw [Finset.sum_eq_single (prefixOf i u)]
        · rw [Finset.sum_eq_single (u i)]
          · simp
          · intro b _ hne; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ (u i)) h
        · intro p _ hne; apply Finset.sum_eq_zero; intro b _; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ (prefixOf i u)) h
      conv_lhs => rw [Finset.sum_congr rfl fun u _ ↦ h1 u]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.sum_filter]
    have hblock_sum : ∀ (p : Fin i.val → Bool) (b : Bool),
        ∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ prefixOf i u = p ∧ u i = b),
          stepErr u i =
        (2 : ℝ) ^ (2 ^ n - 1 - i.val) *
          (((1 - qscStepProj W n i p b) * (condSynthState W n i p b).mat).trace).re := by
      intro p b
      have hcongr : ∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ prefixOf i u = p ∧ u i = b),
          stepErr u i =
          (((1 - qscStepProj W n i p b) * synthBlockMat W n i p b).trace).re := by
        unfold stepErr synthBlockMat
        rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
        apply Finset.sum_congr rfl; intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        rw [hu.1, hu.2]
      rw [hcongr]
      have hmat : synthBlockMat W n i p b =
          ((2 : ℂ) ^ (2 ^ n - 1 - i.val)) • (condSynthState W n i p b).mat := by
        simp only [condSynthState, smul_smul]
        rw [mul_inv_cancel₀ (by positivity), one_smul]
      rw [hmat, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      have hre : (((2 : ℂ) ^ (2 ^ n - 1 - i.val)) *
          ((1 - qscStepProj W n i p b) * (condSynthState W n i p b).mat).trace).re =
          (2 : ℝ) ^ (2 ^ n - 1 - i.val) *
            (((1 - qscStepProj W n i p b) * (condSynthState W n i p b).mat).trace).re := by
        have hcast : ((2 : ℂ) ^ (2 ^ n - 1 - i.val)) = (((2 : ℝ) ^ (2 ^ n - 1 - i.val) : ℝ) : ℂ) := by
          push_cast; rfl
        rw [hcast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact hre
    rw [hpart]
    have hpow : ((2 : ℝ) ^ (2 ^ n))⁻¹ * (2 : ℝ) ^ (2 ^ n - 1 - i.val) =
        ((2 : ℝ) ^ i.val)⁻¹ * (1 / 2 : ℝ) := by
      have hN : (2 : ℝ) ^ (2 ^ n) = (2 : ℝ) ^ i.val * 2 * (2 : ℝ) ^ (2 ^ n - 1 - i.val) := by
        rw [← pow_succ, ← pow_add, show i.val + 1 + (2 ^ n - 1 - i.val) = 2 ^ n by omega]
      rw [hN]
      have h1 : (2 : ℝ) ^ i.val ≠ 0 := by positivity
      have h2 : (2 : ℝ) ^ (2 ^ n - 1 - i.val) ≠ 0 := by positivity
      field_simp
    calc ((2 : ℝ) ^ (2 ^ n))⁻¹ *
          ∑ p : Fin i.val → Bool, ∑ b : Bool,
            ∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ prefixOf i u = p ∧ u i = b),
              stepErr u i
        = ((2 : ℝ) ^ i.val)⁻¹ *
            ∑ p : Fin i.val → Bool,
              (1 / 2 : ℝ) *
                ((((1 - helstromProjector (condSynthState W n i p false) (condSynthState W n i p true)) *
                    (condSynthState W n i p false).mat).trace).re +
                  ((helstromProjector (condSynthState W n i p false) (condSynthState W n i p true) *
                    (condSynthState W n i p true).mat).trace).re) := by
          simp_rw [hblock_sum]
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p _
          rw [Fintype.sum_bool, add_comm]
          simp only [qscStepProj, ↓reduceIte, Bool.true_eq_false, sub_sub_cancel]
          rw [← mul_add, ← mul_assoc, hpow, mul_assoc]
      _ ≤ ((2 : ℝ) ^ i.val)⁻¹ *
            ∑ p : Fin i.val → Bool,
              (1 / 2 : ℝ) * rootFidelity (condSynthState W n i p false) (condSynthState W n i p true) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum fun p _ ↦
            helstrom_error_le_fidelity (condSynthState W n i p false) (condSynthState W n i p true)
      _ = (1 / 2 : ℝ) *
            (((2 : ℝ) ^ i.val)⁻¹ *
              ∑ p : Fin i.val → Bool,
                rootFidelity (condSynthState W n i p false) (condSynthState W n i p true)) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ (1 / 2 : ℝ) * (synthChannel W n i).fidelityParam :=
          mul_le_mul_of_nonneg_left (avg_condSynth_rootFidelity_le W n i) (by norm_num)
  have havg_bound : ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ u : Fin (2 ^ n) → Bool, errU u ≤
      2 * Real.sqrt (∑ i ∈ infoSet, (1 / 2 : ℝ) * (synthChannel W n i).fidelityParam) := by
    refine le_trans havg_sen ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ havg_i i
  -- Step 4: Factor uniform average over `u` into average over frozen bits × `avgBlockError`
  let eSplit : ({i : Fin (2 ^ n) // i ∉ infoSet} → Bool) × ({i : Fin (2 ^ n) // i ∈ infoSet} → Bool) ≃
      (Fin (2 ^ n) → Bool) :=
    { toFun := fun ⟨f, m⟩ i ↦ if hi : i ∈ infoSet then m ⟨i, hi⟩ else f ⟨i, hi⟩
      invFun := fun u ↦ (fun ⟨i, _⟩ ↦ u i, fun ⟨i, _⟩ ↦ u i)
      left_inv := fun ⟨f, m⟩ ↦ by
        ext ⟨i, hi⟩ <;> simp [hi]
      right_inv := fun u ↦ by
        funext i; by_cases hi : i ∈ infoSet <;> simp [hi] }
  let extendF (f : {i : Fin (2 ^ n) // i ∉ infoSet} → Bool) : Fin (2 ^ n) → Bool :=
    fun i ↦ if hi : i ∉ infoSet then f ⟨i, hi⟩ else false
  have hsplit_sum :
      ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ u : Fin (2 ^ n) → Bool, errU u =
      ((2 : ℝ) ^ (2 ^ n - infoSet.card))⁻¹ *
        ∑ f : {i : Fin (2 ^ n) // i ∉ infoSet} → Bool,
          (qscPolarCode W n infoSet (extendF f)).avgBlockError := by
    rw [← Equiv.sum_comp eSplit errU, Fintype.sum_prod_type]
    have hpow : ((2 : ℝ) ^ (2 ^ n))⁻¹ =
        ((2 : ℝ) ^ (2 ^ n - infoSet.card))⁻¹ * ((2 : ℝ) ^ infoSet.card)⁻¹ := by
      have hle : infoSet.card ≤ 2 ^ n := by
        simpa [Fintype.card_fin] using Finset.card_le_univ infoSet
      have hN : (2 : ℝ) ^ (2 ^ n) = (2 : ℝ) ^ (2 ^ n - infoSet.card) * (2 : ℝ) ^ infoSet.card := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      rw [hN, mul_inv]
    rw [hpow, mul_assoc, Finset.mul_sum]
    apply congr_arg (((2 : ℝ) ^ (2 ^ n - infoSet.card))⁻¹ * ·)
    apply Finset.sum_congr rfl; intro f _
    unfold CosetPolarCode.avgBlockError qscPolarCode CosetPolarCode.encode
    dsimp only
    apply congr_arg (((2 : ℝ) ^ infoSet.card)⁻¹ * ·)
    apply Finset.sum_congr rfl; intro m _
    have hu_eq : eSplit (f, m) = embedMsg infoSet (extendF f) m := by
      funext i
      by_cases hi : i ∈ infoSet
      · simp [eSplit, embedMsg, hi]
      · simp [eSplit, embedMsg, extendF, hi]
    rw [hu_eq]
    unfold errU
    have htr : (qscPrefixKraus W n infoSet (2 ^ n) le_rfl (embedMsg infoSet (extendF f) m) *
          (productState W n (arikanTransform n (embedMsg infoSet (extendF f) m))).mat *
          (qscPrefixKraus W n infoSet (2 ^ n) le_rfl (embedMsg infoSet (extendF f) m))ᴴ).trace =
        ((qscPrefixKraus W n infoSet (2 ^ n) le_rfl (embedMsg infoSet (extendF f) m))ᴴ *
          qscPrefixKraus W n infoSet (2 ^ n) le_rfl (embedMsg infoSet (extendF f) m) *
          (productState W n (arikanTransform n (embedMsg infoSet (extendF f) m))).mat).trace := by
      rw [Matrix.trace_mul_cycle]
    rw [htr]
  rw [hsplit_sum] at havg_bound
  let G : (Fin (2 ^ n) → Bool) → ℝ := fun frozen ↦ (qscPolarCode W n infoSet frozen).avgBlockError
  have hconst : ∀ (f : {i : Fin (2 ^ n) // i ∉ infoSet} → Bool)
      (m : {i : Fin (2 ^ n) // i ∈ infoSet} → Bool),
      G (eSplit (f, m)) = G (extendF f) := by
    intro f m
    have hemb : ∀ m', embedMsg infoSet (eSplit (f, m)) m' = embedMsg infoSet (extendF f) m' := by
      intro m'; funext i; by_cases hi : i ∈ infoSet <;> simp [embedMsg, eSplit, extendF, hi]
    simp only [G, CosetPolarCode.avgBlockError, qscPolarCode, CosetPolarCode.encode, hemb]
    rfl
  have hfull : ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ frozen : Fin (2 ^ n) → Bool, G frozen =
      ((2 : ℝ) ^ (2 ^ n - infoSet.card))⁻¹ *
        ∑ f : {i : Fin (2 ^ n) // i ∉ infoSet} → Bool, G (extendF f) := by
    rw [← Equiv.sum_comp eSplit G, Fintype.sum_prod_type]
    simp_rw [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Finset.mul_sum, ← mul_assoc]
    have hle : infoSet.card ≤ 2 ^ n := by
      simpa [Fintype.card_fin] using Finset.card_le_univ infoSet
    have hN : (2 : ℝ) ^ (2 ^ n) = (2 : ℝ) ^ (2 ^ n - infoSet.card) * (2 : ℝ) ^ infoSet.card := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have h2pos : (2 : ℝ) ^ infoSet.card ≠ 0 := by positivity
    have h2pos' : (2 : ℝ) ^ (2 ^ n - infoSet.card) ≠ 0 := by positivity
    rw [hN]; field_simp
  change ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ frozen : Fin (2 ^ n) → Bool, G frozen ≤ _
  rw [hfull]
  exact havg_bound

/-- **Wilde–Guha Quantum Successive-Cancellation Coding Bound**:
There exists a deterministic frozen-bit assignment `frozen : Fin (2^n) → Bool` such that
`qscPolarCode W n infoSet frozen` achieves
`P_e(N, R) ≤ 2 √(∑_{i ∈ infoSet} (1 / 2) * Z(W_n^{(i)}))`. -/
theorem wilde_guha_qsc_bound (W : CQChannel d) (n : ℕ) (infoSet : Finset (Fin (2 ^ n))) :
    ∃ frozen : Fin (2 ^ n) → Bool,
      (qscPolarCode W n infoSet frozen).avgBlockError ≤
        2 * Real.sqrt (∑ i ∈ infoSet, (1 / 2 : ℝ) * (synthChannel W n i).fidelityParam) := by
  have havg := wilde_guha_qsc_avg_bound W n infoSet
  have hcard : ((Finset.univ : Finset (Fin (2 ^ n) → Bool)).card : ℝ) = (2 : ℝ) ^ (2 ^ n) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    norm_cast
  have hsum_le : ∑ frozen : Fin (2 ^ n) → Bool,
      (qscPolarCode W n infoSet frozen).avgBlockError ≤
      ∑ _frozen : Fin (2 ^ n) → Bool,
        (2 * Real.sqrt (∑ i ∈ infoSet, (1 / 2 : ℝ) * (synthChannel W n i).fidelityParam)) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ n) := by positivity
    calc ∑ frozen, (qscPolarCode W n infoSet frozen).avgBlockError
        = (2 : ℝ) ^ (2 ^ n) *
            (((2 : ℝ) ^ (2 ^ n))⁻¹ *
              ∑ frozen, (qscPolarCode W n infoSet frozen).avgBlockError) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left havg (le_of_lt hpos)
  obtain ⟨f, _, hf⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum_le
  exact ⟨f, hf⟩

/-! ### Full Coding-Theoretic Theorem 1.1 -/

/-- **Theorem 1.1 (Full Coding-Theoretic Polynomial-Blocklength Quantum Polar Codes)**:
There exist universal constants `μ > 0` and `C₀ > 0` such that for every finite-dimensional
binary-input c-q channel `W`, every gap `ε ∈ (0, 1)`, and every depth `n : ℕ` with blocklength
`N = 2^n ≥ C₀ (1 / ε)^μ`, there exists a deterministic `G_N`-coset classical–quantum polar code
of blocklength `N = 2^n`, rate `R ≥ I(W) - ε`, and QSC average block-error probability
`P_e(N, R) ≤ 2^{-N^{0.49}}`. -/
theorem theorem_1_1_coding_poly_blocklength :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ {d : Type u} [Fintype d] [DecidableEq d] (W : CQChannel d)
        {ε : ℝ}, 0 < ε → ε < 1 →
        ∀ (n : ℕ), C₀ * (1 / ε) ^ μ ≤ (2 : ℝ) ^ n →
          ∃ (infoSet : Finset (Fin (2 ^ n))) (frozen : Fin (2 ^ n) → Bool),
            let C := qscPolarCode W n infoSet frozen
            W.symCapacity - ε ≤ C.rate ∧
            C.avgBlockError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := by
  rcases theorem_1_1_quantum_polar_poly_blocklength with ⟨μ, C₀, hμ, hC₀, hpolar⟩
  refine ⟨μ, max C₀ 2, hμ, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right C₀ 2), ?_⟩
  intro d _ _ W ε hε0 hε1 n hn
  have h1eps : (1 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε0, one_mul]; exact le_of_lt hε1
  have hpow_ge1 : (1 : ℝ) ≤ (1 / ε) ^ μ := Real.one_le_rpow h1eps (le_of_lt hμ)
  have hn_base : C₀ * (1 / ε) ^ μ ≤ (2 : ℝ) ^ n :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left C₀ 2) (by linarith)) hn
  have hn_ge2 : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (2 : ℝ) = 2 * 1 := by ring
      _ ≤ max C₀ 2 * (1 / ε) ^ μ := mul_le_mul (le_max_right C₀ 2) hpow_ge1 (by norm_num) (by positivity)
      _ ≤ (2 : ℝ) ^ n := hn
  have hn1 : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    subst this; norm_num at hn_ge2
  -- Handle trivial case `W.symCapacity ≤ ε` with empty information set `𝒜 = ∅` (`P_e = 0`)
  by_cases htriv : W.symCapacity ≤ ε
  · refine ⟨∅, fun _ ↦ false, ?_, ?_⟩
    · simp only [CosetPolarCode.rate, qscPolarCode, Finset.card_empty, Nat.cast_zero, zero_div]
      linarith
    · have herr0 : (qscPolarCode W n ∅ (fun _ ↦ false)).avgBlockError = 0 := by
        unfold CosetPolarCode.avgBlockError qscPolarCode CosetPolarCode.encode
        have huniq : Unique ({i : Fin (2 ^ n) // i ∈ (∅ : Finset (Fin (2 ^ n)))} → Bool) :=
          Pi.uniqueOfIsEmpty _
        rw [Fintype.sum_unique]
        have hK : ∀ u, qscPrefixKraus W n ∅ (2 ^ n) le_rfl u = 1 := by
          intro u
          have hgen : ∀ k (hk : k ≤ 2 ^ n), qscPrefixKraus W n ∅ k hk u = 1 := by
            intro k hk
            induction k with
            | zero => rfl
            | succ k ih =>
              rw [qscPrefixKraus_succ]
              simp [ih (by omega)]
          exact hgen (2 ^ n) le_rfl
        simp only [hK, Matrix.conjTranspose_one, Matrix.one_mul,
          (productState W n _).trace_one, Complex.one_re, sub_self, mul_zero]
      rw [herr0]
      exact Real.rpow_nonneg (by norm_num) _
  · -- Non-trivial case: `ε < W.symCapacity`
    let thresh : ℝ := (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))
    let infoSet : Finset (Fin (2 ^ n)) :=
      Finset.univ.filter (fun i : Fin (2 ^ n) ↦ (synthChannel W n i).fidelityParam ≤ thresh)
    obtain ⟨frozen, hwg⟩ := wilde_guha_qsc_bound W n infoSet
    refine ⟨infoSet, frozen, ?_, ?_⟩
    · -- Rate bound: `infoSet.card / 2^n = treeProb n (...) ≥ W.symCapacity - ε`
      have hrate_eq : (qscPolarCode W n infoSet frozen).rate =
          treeProb n (fun b ↦ polarFidelity W n b ≤ thresh) := by
        unfold CosetPolarCode.rate qscPolarCode treeProb treeAvg ind
        dsimp only
        rw [Finset.sum_boole]
        congr 1
        norm_cast
        apply Finset.card_bij (fun i _ ↦ bitPath n i)
        · intro i hi
          simp only [infoSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          rwa [← synthChannel_fidelityParam_eq W n i]
        · intro i₁ _ i₂ _ h; exact (bitPath n).injective h
        · intro b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
          refine ⟨(bitPath n).symm b, ?_, (bitPath n).apply_symm_apply b⟩
          simp only [infoSet, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [synthChannel_fidelityParam_eq W n ((bitPath n).symm b), (bitPath n).apply_symm_apply b]
          exact hb
      rw [hrate_eq]
      exact hpolar W hε0 hε1 n hn_base
    · -- Block-error bound: `P_e ≤ 2 √(∑ (1/2) Z) ≤ 2 √(2^n * thresh) ≤ 2^{-(2^n)^0.49}`
      have hthresh_nn : 0 ≤ thresh := Real.rpow_nonneg (by norm_num) _
      have hsum_le : ∑ i ∈ infoSet, (1 / 2 : ℝ) * (synthChannel W n i).fidelityParam ≤
          (2 : ℝ) ^ n * thresh := by
        have h1 : ∑ i ∈ infoSet, (1 / 2 : ℝ) * (synthChannel W n i).fidelityParam ≤
            ∑ _i ∈ infoSet, thresh := by
          apply Finset.sum_le_sum; intro i hi
          simp only [infoSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have hnn : 0 ≤ (synthChannel W n i).fidelityParam :=
            Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _
          linarith
        have hcard_le : (infoSet.card : ℝ) ≤ (2 : ℝ) ^ n := by
          have := Finset.card_le_univ infoSet
          simp only [Fintype.card_fin] at this
          exact_mod_cast this
        calc ∑ i ∈ infoSet, (1 / 2 : ℝ) * (synthChannel W n i).fidelityParam
            ≤ (infoSet.card : ℝ) * thresh := by simpa [Finset.sum_const, nsmul_eq_mul] using h1
          _ ≤ (2 : ℝ) ^ n * thresh := mul_le_mul_of_nonneg_right hcard_le hthresh_nn
      calc (qscPolarCode W n infoSet frozen).avgBlockError
          ≤ 2 * Real.sqrt (∑ i ∈ infoSet, (1 / 2 : ℝ) * (synthChannel W n i).fidelityParam) := hwg
        _ ≤ 2 * Real.sqrt ((2 : ℝ) ^ n * thresh) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum_le) (by norm_num)
        _ ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := polar_error_exponent_bound hn1

end PolarCoding

end PolarCodes
