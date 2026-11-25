/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.QuantumChannels
import PolarCodes.ChannelDuality

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodes

universe u

lemma posSemidef_mul_conjTranspose {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) : (A * Aᴴ).PosSemidef := by
  simpa [Matrix.conjTranspose_conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self Aᴴ

private lemma density_spectral_eq {d : Type*} [Fintype d] [DecidableEq d] (ρ : DensityOp d) :
    ρ.mat = (ρ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *
      star (ρ.eigUnitary : Matrix d d ℂ) := by
  simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
    Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem

section ChannelEquivalence

/-- Output-isometry equivalence between two binary-input c-q channels:
there exists a common finite-dimensional ambient space `γ` and isometries
`V₁ : d₁ → γ`, `V₂ : d₂ → γ` (`V₁ᴴ V₁ = I`, `V₂ᴴ V₂ = I`) such that
`V₁ W₁(b) V₁ᴴ = V₂ W₂(b) V₂ᴴ` for both `b ∈ {false, true}`. -/
def CQChannel.IsoEquiv {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) : Prop :=
  ∃ (γ : Type u) (_ : Fintype γ) (_ : DecidableEq γ)
    (V₁ : Matrix γ d₁ ℂ) (V₂ : Matrix γ d₂ ℂ),
    V₁ᴴ * V₁ = 1 ∧ V₂ᴴ * V₂ = 1 ∧
    ∀ b : Bool, V₁ * (W₁.out b).mat * V₁ᴴ = V₂ * (W₂.out b).mat * V₂ᴴ

/-- Reversible CPTP channel equivalence between two binary-input c-q channels:
there exist CPTP maps `𝒩 : d₁ → d₂` and `ℳ : d₂ → d₁` such that
`𝒩(W₁(b)) = W₂(b)` and `ℳ(W₂(b)) = W₁(b)` for both `b ∈ {false, true}`. -/
def CQChannel.ChannelEquiv {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) : Prop :=
  ∃ (𝒩 : CPTPMap.{u} d₁ d₂) (ℳ : CPTPMap.{u} d₂ d₁),
    (∀ b : Bool, (𝒩.apply (W₁.out b)).mat = (W₂.out b).mat) ∧
    (∀ b : Bool, (ℳ.apply (W₂.out b)).mat = (W₁.out b).mat)

lemma CQChannel.ChannelEquiv.refl {d : Type u} [Fintype d] [DecidableEq d] (W : CQChannel d) :
    W.ChannelEquiv W := by
  refine ⟨CPTPMap.id d, CPTPMap.id d, fun b ↦ ?_, fun b ↦ ?_⟩ <;>
  · ext i j
    simp [CPTPMap.apply, CPTPMap.id, partialTrace₂Mat, Matrix.mul_apply,
      Matrix.conjTranspose_apply]

lemma CQChannel.ChannelEquiv.symm {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.ChannelEquiv W₂) : W₂.ChannelEquiv W₁ := by
  rcases h with ⟨𝒩, ℳ, h1, h2⟩
  exact ⟨ℳ, 𝒩, h2, h1⟩

lemma CQChannel.ChannelEquiv.trans {d₁ d₂ d₃ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃]
    {W₁ : CQChannel d₁} {W₂ : CQChannel d₂} {W₃ : CQChannel d₃}
    (h12 : W₁.ChannelEquiv W₂) (h23 : W₂.ChannelEquiv W₃) : W₁.ChannelEquiv W₃ := by
  rcases h12 with ⟨𝒩₁, ℳ₁, h1, h2⟩
  rcases h23 with ⟨𝒩₂, ℳ₂, h3, h4⟩
  refine ⟨𝒩₂.comp 𝒩₁, ℳ₁.comp ℳ₂, fun b ↦ ?_, fun b ↦ ?_⟩
  · rw [CPTPMap.comp_apply]
    have heq : 𝒩₁.apply (W₁.out b) = W₂.out b := by
      cases hA : 𝒩₁.apply (W₁.out b); cases hB : W₂.out b
      have hm := h1 b; rw [hA, hB] at hm; simp_all
    rw [heq]; exact h3 b
  · rw [CPTPMap.comp_apply]
    have heq : ℳ₂.apply (W₃.out b) = W₂.out b := by
      cases hA : ℳ₂.apply (W₃.out b); cases hB : W₂.out b
      have hm := h4 b; rw [hA, hB] at hm; simp_all
    rw [heq]; exact h2 b

/-- Reversible CPTP channel equivalence immediately implies equality of `condEntropy`,
`symCapacity`, and `qjs`. -/
theorem CQChannel.ChannelEquiv.condEntropy_eq {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.ChannelEquiv W₂) : W₁.condEntropy = W₂.condEntropy := by
  rcases h with ⟨𝒩, ℳ, h1, h2⟩
  have hle1 : W₁.condEntropy ≤ W₂.condEntropy := by
    have hge := condEntropy_cptp_ge 𝒩 W₁
    have heq : (𝒩.compCQ W₁).condEntropy = W₂.condEntropy := by
      have hch : 𝒩.compCQ W₁ = W₂ := by
        cases W₂ with | mk out₂ =>
        change CQChannel.mk (fun b ↦ 𝒩.apply (W₁.out b)) = CQChannel.mk out₂
        congr 1; funext b
        have hb := h1 b
        cases hA : 𝒩.apply (W₁.out b); cases hB : out₂ b
        rw [hA, hB] at hb; simp_all
      rw [hch]
    linarith
  have hle2 : W₂.condEntropy ≤ W₁.condEntropy := by
    have hge := condEntropy_cptp_ge ℳ W₂
    have heq : (ℳ.compCQ W₂).condEntropy = W₁.condEntropy := by
      have hch : ℳ.compCQ W₂ = W₁ := by
        cases W₁ with | mk out₁ =>
        change CQChannel.mk (fun b ↦ ℳ.apply (W₂.out b)) = CQChannel.mk out₁
        congr 1; funext b
        have hb := h2 b
        cases hA : ℳ.apply (W₂.out b); cases hB : out₁ b
        rw [hA, hB] at hb; simp_all
      rw [hch]
    linarith
  exact le_antisymm hle1 hle2

/-- Build a CPTP map from any contraction `K : Matrix β α ℂ` (`1 - Kᴴ K ≥ 0`), mapping
`ρ ↦ K ρ Kᴴ + Tr((1 - Kᴴ K) ρ) |b₀⟩⟨b₀|`. -/
noncomputable def CPTPMap.ofContraction {α β : Type u} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (K : Matrix β α ℂ) (hK : (1 - Kᴴ * K).PosSemidef) : CPTPMap.{u} α β := by
  let b₀ : β := Classical.arbitrary β
  let D : Matrix α α ℂ :=
    (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ) *
    Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
    star (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
  have hD_herm : Dᴴ = D := by
    simp only [D, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have hdiag : (Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)))ᴴ =
        Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) := by
      ext i j; by_cases h : i = j <;> simp [h, Matrix.conjTranspose_apply, Matrix.diagonal_apply, eq_comm]
    rw [hdiag]; simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hDD : D * D = 1 - Kᴴ * K := by
    set U := (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
    have hspec := (by simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hK.isHermitian.spectral_theorem)
    have hdiag_sq : Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
        Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) =
        Matrix.diagonal (Complex.ofReal ∘ hK.isHermitian.eigenvalues) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      simp only [Function.comp_apply, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hK.eigenvalues_nonneg i)]
    calc D * D = U * (Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
            (star U * U) * Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ))) *
            star U := by simp [D, U, Matrix.mul_assoc]
      _ = U * Matrix.diagonal (Complex.ofReal ∘ hK.isHermitian.eigenvalues) * star U := by
            rw [Unitary.coe_star_mul_self, Matrix.mul_one, hdiag_sq]
      _ = 1 - Kᴴ * K := hspec.symm
  refine ⟨PUnit.{u + 1} ⊕ α, inferInstance, inferInstance,
    Matrix.of fun (p : β × (PUnit.{u + 1} ⊕ α)) (a : α) ↦
      match p.2 with
      | Sum.inl _ => K p.1 a
      | Sum.inr c => if p.1 = b₀ then D c a else 0, ?_⟩
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_unique]
  have h1 : ∑ x : β, star (K x i) * K x j = (Kᴴ * K) i j := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h2 : ∑ x : β, ∑ c : α, star (if x = b₀ then D c i else 0) * (if x = b₀ then D c j else 0) =
      (Dᴴ * D) i j := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
    simp
  rw [Finset.sum_add_distrib, h1, h2, hD_herm, hDD]
  simp

lemma CPTPMap.ofContraction_apply_eq {α β : Type u} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (K : Matrix β α ℂ) (hK : (1 - Kᴴ * K).PosSemidef) (ρ : DensityOp α)
    (hker : (1 - Kᴴ * K) * ρ.mat = 0) :
    ((CPTPMap.ofContraction K hK).apply ρ).mat = K * ρ.mat * Kᴴ := by
  let D : Matrix α α ℂ :=
    (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ) *
    Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
    star (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
  have hD_herm : Dᴴ = D := by
    simp only [D, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have hdiag : (Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)))ᴴ =
        Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) := by
      ext i j; by_cases h : i = j <;> simp [h, Matrix.conjTranspose_apply, Matrix.diagonal_apply, eq_comm]
    rw [hdiag]; simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hDD : D * D = 1 - Kᴴ * K := by
    set U := (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
    have hspec := (by simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hK.isHermitian.spectral_theorem)
    have hdiag_sq : Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
        Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) =
        Matrix.diagonal (Complex.ofReal ∘ hK.isHermitian.eigenvalues) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      simp only [Function.comp_apply, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hK.eigenvalues_nonneg i)]
    calc D * D = U * (Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
            (star U * U) * Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ))) *
            star U := by simp [D, U, Matrix.mul_assoc]
      _ = U * Matrix.diagonal (Complex.ofReal ∘ hK.isHermitian.eigenvalues) * star U := by
            rw [Unitary.coe_star_mul_self, Matrix.mul_one, hdiag_sq]
      _ = 1 - Kᴴ * K := hspec.symm
  have hDρD_tr : (D * ρ.mat * Dᴴ).trace = 0 := by
    rw [Matrix.trace_mul_cycle, hD_herm, hDD, hker, Matrix.trace_zero]
  have hDρD : D * ρ.mat * Dᴴ = 0 := by
    have hpsd : (D * ρ.mat * Dᴴ).PosSemidef := ρ.posSemidef.mul_mul_conjTranspose_same D
    have hspec := (by simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hpsd.isHermitian.spectral_theorem)
    have heig_zero : ∀ i, hpsd.isHermitian.eigenvalues i = 0 := by
      have hsum : ∑ i : α, hpsd.isHermitian.eigenvalues i = 0 := by
        have htr := hpsd.isHermitian.trace_eq_sum_eigenvalues
        rw [hDρD_tr] at htr
        exact_mod_cast htr.symm
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ hpsd.eigenvalues_nonneg k)).mp hsum i
        (Finset.mem_univ i)
    rw [hspec]
    have hdiag0 : Matrix.diagonal (Complex.ofReal ∘ hpsd.isHermitian.eigenvalues) = 0 := by
      ext i j; simp [Matrix.diagonal_apply, heig_zero]
    rw [hdiag0, Matrix.mul_zero, Matrix.zero_mul]
  ext b₁ b₂
  change (partialTrace₂Mat ((CPTPMap.ofContraction K hK).isom * ρ.mat *
    (CPTPMap.ofContraction K hK).isomᴴ)) b₁ b₂ = (K * ρ.mat * Kᴴ) b₁ b₂
  dsimp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, CPTPMap.ofContraction]
  simp only [Matrix.of_apply, Fintype.sum_sum_type, Fintype.sum_unique, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  have hzero : ∑ c : α, ∑ a₂ : α, (∑ a₁ : α, (if b₁ = Classical.arbitrary β then D c a₁ else 0) *
      ρ.mat a₁ a₂) * star (if b₂ = Classical.arbitrary β then D c a₂ else 0) = 0 := by
    by_cases h1 : b₁ = Classical.arbitrary β
    · by_cases h2 : b₂ = Classical.arbitrary β
      · simp only [h1, h2, ↓reduceIte]
        have htr : ∑ c : α, (D * ρ.mat * Dᴴ) c c = 0 := by
          simp [hDρD]
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using htr
      · simp [h2]
    · simp [h1]
  rw [hzero, add_zero]

/-- Output-isometry equivalence implies reversible CPTP channel equivalence. -/
lemma CQChannel.IsoEquiv.toChannelEquiv {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.IsoEquiv W₂) : W₁.ChannelEquiv W₂ := by
  haveI : Nonempty d₁ := by
    by_contra h0; haveI : IsEmpty d₁ := not_nonempty_iff.mp h0
    have htr := (W₁.out false).trace_one; simp [Matrix.trace] at htr
  haveI : Nonempty d₂ := by
    by_contra h0; haveI : IsEmpty d₂ := not_nonempty_iff.mp h0
    have htr := (W₂.out false).trace_one; simp [Matrix.trace] at htr
  rcases h with ⟨γ, _, _, V₁, V₂, hV₁, hV₂, heq⟩
  let K₁ : Matrix d₂ d₁ ℂ := V₂ᴴ * V₁
  let K₂ : Matrix d₁ d₂ ℂ := V₁ᴴ * V₂
  have hK₁_contr : (1 - K₁ᴴ * K₁).PosSemidef := by
    have h1 : 1 - K₁ᴴ * K₁ = V₁ᴴ * (1 - V₂ * V₂ᴴ) * V₁ := by
      simp only [K₁, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV₁, Matrix.mul_assoc]
    have hproj : (1 - V₂ * V₂ᴴ).PosSemidef := by
      have hp : (1 - V₂ * V₂ᴴ) = (1 - V₂ * V₂ᴴ)ᴴ * (1 - V₂ * V₂ᴴ) := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_one, Matrix.one_mul]
        have hsq : V₂ * V₂ᴴ * (V₂ * V₂ᴴ) = V₂ * V₂ᴴ := by
          calc V₂ * V₂ᴴ * (V₂ * V₂ᴴ) = V₂ * (V₂ᴴ * V₂) * V₂ᴴ := by simp [Matrix.mul_assoc]
            _ = V₂ * V₂ᴴ := by rw [hV₂, Matrix.mul_one]
        rw [hsq]; abel
      rw [hp]; exact Matrix.posSemidef_conjTranspose_mul_self _
    rw [h1]; exact hproj.conjTranspose_mul_mul_same V₁
  have hK₂_contr : (1 - K₂ᴴ * K₂).PosSemidef := by
    have h1 : 1 - K₂ᴴ * K₂ = V₂ᴴ * (1 - V₁ * V₁ᴴ) * V₂ := by
      simp only [K₂, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV₂, Matrix.mul_assoc]
    have hproj : (1 - V₁ * V₁ᴴ).PosSemidef := by
      have hp : (1 - V₁ * V₁ᴴ) = (1 - V₁ * V₁ᴴ)ᴴ * (1 - V₁ * V₁ᴴ) := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_one, Matrix.one_mul]
        have hsq : V₁ * V₁ᴴ * (V₁ * V₁ᴴ) = V₁ * V₁ᴴ := by
          calc V₁ * V₁ᴴ * (V₁ * V₁ᴴ) = V₁ * (V₁ᴴ * V₁) * V₁ᴴ := by simp [Matrix.mul_assoc]
            _ = V₁ * V₁ᴴ := by rw [hV₁, Matrix.mul_one]
        rw [hsq]; abel
      rw [hp]; exact Matrix.posSemidef_conjTranspose_mul_self _
    rw [h1]; exact hproj.conjTranspose_mul_mul_same V₂
  refine ⟨CPTPMap.ofContraction K₁ hK₁_contr, CPTPMap.ofContraction K₂ hK₂_contr, ?_, ?_⟩
  · intro b
    have hker : (1 - K₁ᴴ * K₁) * (W₁.out b).mat = 0 := by
      have h1 : K₁ᴴ * K₁ * (W₁.out b).mat = (W₁.out b).mat := by
        calc K₁ᴴ * K₁ * (W₁.out b).mat
            = V₁ᴴ * V₂ * V₂ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₁ := by
                simp only [K₁, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
                  Matrix.mul_assoc]
                have : (W₁.out b).mat * (V₁ᴴ * V₁) = (W₁.out b).mat := by rw [hV₁, Matrix.mul_one]
                simpa [Matrix.mul_assoc] using congr_arg (fun X ↦ V₁ᴴ * V₂ * V₂ᴴ * V₁ * X) this.symm
          _ = V₁ᴴ * V₂ * V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₁ := by rw [heq b]
          _ = V₁ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₁ := by
                calc V₁ᴴ * V₂ * V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₁
                    = V₁ᴴ * (V₂ * (V₂ᴴ * V₂) * (W₂.out b).mat * V₂ᴴ) * V₁ := by simp [Matrix.mul_assoc]
                  _ = _ := by rw [hV₂, Matrix.mul_one]
          _ = V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₁ := by rw [← heq b]
          _ = (W₁.out b).mat := by
                calc V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₁
                    = (V₁ᴴ * V₁) * (W₁.out b).mat * (V₁ᴴ * V₁) := by simp [Matrix.mul_assoc]
                  _ = (W₁.out b).mat := by rw [hV₁, Matrix.one_mul, Matrix.mul_one]
      rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self]
    rw [CPTPMap.ofContraction_apply_eq K₁ hK₁_contr (W₁.out b) hker]
    calc K₁ * (W₁.out b).mat * K₁ᴴ
        = V₂ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₂ := by
            simp [K₁, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₂ := by rw [heq b]
      _ = (W₂.out b).mat := by
            calc V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₂
                = (V₂ᴴ * V₂) * (W₂.out b).mat * (V₂ᴴ * V₂) := by simp [Matrix.mul_assoc]
              _ = (W₂.out b).mat := by rw [hV₂, Matrix.one_mul, Matrix.mul_one]
  · intro b
    have hker : (1 - K₂ᴴ * K₂) * (W₂.out b).mat = 0 := by
      have h1 : K₂ᴴ * K₂ * (W₂.out b).mat = (W₂.out b).mat := by
        calc K₂ᴴ * K₂ * (W₂.out b).mat
            = V₂ᴴ * V₁ * V₁ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₂ := by
                simp only [K₂, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
                  Matrix.mul_assoc]
                have : (W₂.out b).mat * (V₂ᴴ * V₂) = (W₂.out b).mat := by rw [hV₂, Matrix.mul_one]
                simpa [Matrix.mul_assoc] using congr_arg (fun X ↦ V₂ᴴ * V₁ * V₁ᴴ * V₂ * X) this.symm
          _ = V₂ᴴ * V₁ * V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₂ := by rw [← heq b]
          _ = V₂ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₂ := by
                calc V₂ᴴ * V₁ * V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₂
                    = V₂ᴴ * (V₁ * (V₁ᴴ * V₁) * (W₁.out b).mat * V₁ᴴ) * V₂ := by simp [Matrix.mul_assoc]
                  _ = _ := by rw [hV₁, Matrix.mul_one]
          _ = V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₂ := by rw [heq b]
          _ = (W₂.out b).mat := by
                calc V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₂
                    = (V₂ᴴ * V₂) * (W₂.out b).mat * (V₂ᴴ * V₂) := by simp [Matrix.mul_assoc]
                  _ = (W₂.out b).mat := by rw [hV₂, Matrix.one_mul, Matrix.mul_one]
      rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self]
    rw [CPTPMap.ofContraction_apply_eq K₂ hK₂_contr (W₂.out b) hker]
    calc K₂ * (W₂.out b).mat * K₂ᴴ
        = V₁ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₁ := by
            simp [K₂, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₁ := by rw [← heq b]
      _ = (W₁.out b).mat := by
            calc V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₁
                = (V₁ᴴ * V₁) * (W₁.out b).mat * (V₁ᴴ * V₁) := by simp [Matrix.mul_assoc]
              _ = (W₁.out b).mat := by rw [hV₁, Matrix.one_mul, Matrix.mul_one]

lemma CQChannel.IsoEquiv.condEntropy_eq {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.IsoEquiv W₂) : W₁.condEntropy = W₂.condEntropy :=
  h.toChannelEquiv.condEntropy_eq

/-- Appending an independent maximally mixed register `I/|α|` yields a `ChannelEquiv` channel. -/
noncomputable def CQChannel.tensorMaxMixed {d : Type u} [Fintype d] [DecidableEq d]
    (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α] (W : CQChannel d) :
    CQChannel (α × d) where
  out b := DensityOp.tensor (maxMixedState α) (W.out b)

lemma CQChannel.channelEquiv_tensorMaxMixed {d : Type u} [Fintype d] [DecidableEq d]
    (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α] (W : CQChannel d) :
    W.ChannelEquiv (W.tensorMaxMixed α) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let c : ℂ := ((Real.sqrt (Fintype.card α : ℝ) : ℂ)⁻¹)
  have hc_sq : star c * c = ((Fintype.card α : ℂ)⁻¹) := by
    simp only [c, ← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt (le_of_lt hcard_pos)]
    push_cast; rfl
  let 𝒩 : CPTPMap.{u} d (α × d) :=
    ⟨α, inferInstance, inferInstance,
      Matrix.of fun (p : (α × d) × α) (x : d) ↦ if p.1.1 = p.2 ∧ p.1.2 = x then c else 0, by
        ext x y
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Fintype.sum_prod_type, Matrix.one_apply]
        by_cases hxy : x = y
        · subst hxy
          simp only [↓reduceIte]
          calc ∑ a : α, ∑ r : d, ∑ e : α,
                star (if a = e ∧ r = x then c else 0) * (if a = e ∧ r = x then c else 0)
              = ∑ a : α, (star c * c) := by
                  apply Finset.sum_congr rfl; intro a _
                  rw [Finset.sum_eq_single x]
                  · rw [Finset.sum_eq_single a]
                    · simp
                    · intro e _ hne; simp [Ne.symm hne]
                    · intro h; exact absurd (Finset.mem_univ a) h
                  · intro r _ hne; apply Finset.sum_eq_zero; intro e _; simp [hne]
                  · intro h; exact absurd (Finset.mem_univ x) h
            _ = (Fintype.card α : ℂ) * ((Fintype.card α : ℂ)⁻¹) := by
                  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc_sq]
            _ = 1 := mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        · simp only [hxy, ↓reduceIte]
          apply Finset.sum_eq_zero; intro a _
          apply Finset.sum_eq_zero; intro r _
          apply Finset.sum_eq_zero; intro e _
          by_cases hr : r = x
          · subst hr; simp [hxy]
          · simp [hr]⟩
  let ℳ : CPTPMap.{u} (α × d) d :=
    ⟨α, inferInstance, inferInstance,
      Matrix.of fun (p : d × α) (q : α × d) ↦ if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0, by
        ext ⟨a₁, x₁⟩ ⟨a₂, x₂⟩
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Fintype.sum_prod_type, Matrix.one_apply]
        by_cases h : (a₁, x₁) = (a₂, x₂)
        · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
          simp only [↓reduceIte]
          rw [Finset.sum_eq_single x₁]
          · rw [Finset.sum_eq_single a₁]
            · simp
            · intro e _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ a₁) h
          · intro r _ hne; apply Finset.sum_eq_zero; intro e _; simp [hne]
          · intro h; exact absurd (Finset.mem_univ x₁) h
        · simp only [h, ↓reduceIte]
          apply Finset.sum_eq_zero; intro r _
          apply Finset.sum_eq_zero; intro e _
          by_cases h1 : r = x₁ ∧ e = a₁
          · rcases h1 with ⟨rfl, rfl⟩
            have h2 : ¬ (r = x₂ ∧ e = a₂) := fun ⟨hx, ha⟩ ↦ h (by rw [ha, hx])
            simp [h2]
          · simp [h1]⟩
  refine ⟨𝒩, ℳ, ?_, ?_⟩
  · intro b
    ext ⟨a₁, x₁⟩ ⟨a₂, x₂⟩
    change (partialTrace₂Mat (𝒩.isom * (W.out b).mat * 𝒩.isomᴴ)) (a₁, x₁) (a₂, x₂) =
      (DensityOp.tensor (maxMixedState α) (W.out b)).mat (a₁, x₁) (a₂, x₂)
    dsimp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, 𝒩]
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      DensityOp.tensor, maxMixedState, Matrix.kroneckerMap_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    rw [Finset.sum_eq_single a₁]
    · rw [Finset.sum_eq_single x₂]
      · rw [Finset.sum_eq_single x₁]
        · by_cases ha : a₁ = a₂
          · subst ha
            simp only [↓reduceIte, mul_one]
            calc c * (W.out b).mat x₁ x₂ * star c
                = (star c * c) * (W.out b).mat x₁ x₂ := by ring
              _ = _ := by rw [hc_sq]
          · simp [ha, Ne.symm ha]
        · intro y₁ _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ x₁) h
      · intro y₂ _ hne; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ x₂) h
    · intro e _ hne
      apply Finset.sum_eq_zero; intro y₂ _
      apply Finset.sum_eq_zero; intro y₁ _
      simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ a₁) h
  · intro b
    ext x₁ x₂
    change (partialTrace₂Mat (ℳ.isom * (DensityOp.tensor (maxMixedState α) (W.out b)).mat *
      ℳ.isomᴴ)) x₁ x₂ = (W.out b).mat x₁ x₂
    dsimp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, ℳ]
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      DensityOp.tensor, maxMixedState, Matrix.kroneckerMap_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, Fintype.sum_prod_type]
    have hsum : ∑ e : α,
        (∑ a₂ : α, ∑ y₂ : d,
          (∑ a₁ : α, ∑ y₁ : d,
            (if x₁ = y₁ ∧ e = a₁ then (1 : ℂ) else 0) *
            (((Fintype.card α : ℂ)⁻¹ * (if a₁ = a₂ then 1 else 0)) * (W.out b).mat y₁ y₂)) *
          star (if x₂ = y₂ ∧ e = a₂ then (1 : ℂ) else 0)) =
        ∑ _ : α, ((Fintype.card α : ℂ)⁻¹ * (W.out b).mat x₁ x₂) := by
      apply Finset.sum_congr rfl; intro e _
      rw [Finset.sum_eq_single e]
      · rw [Finset.sum_eq_single x₂]
        · rw [Finset.sum_eq_single e]
          · rw [Finset.sum_eq_single x₁]
            · simp
            · intro y₁ _ hne; simp [Ne.symm hne]
            · intro h; exact absurd (Finset.mem_univ x₁) h
          · intro a₁ _ hne; apply Finset.sum_eq_zero; intro y₁ _; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ e) h
        · intro y₂ _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ x₂) h
      · intro a₂ _ hne; apply Finset.sum_eq_zero; intro y₂ _; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ e) h
    rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

/-- Any factorization `A₀ * A₀ᴴ = W(0)`, `A₁ * A₁ᴴ = W(1)` yields a dual channel `W_E` on
`Bool × E` that is `IsoEquiv` to `W.dual`. -/
lemma dual_isoEquiv_of_purification {d E : Type u} [Fintype d] [DecidableEq d]
    [Fintype E] [DecidableEq E] (W : CQChannel d)
    (A₀ A₁ : Matrix d E ℂ)
    (hA₀ : A₀ * A₀ᴴ = (W.out false).mat)
    (hA₁ : A₁ * A₁ᴴ = (W.out true).mat) :
    let M₀ : Matrix (Bool × E) d ℂ :=
      Matrix.of fun p x ↦ ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)
    let M₁ : Matrix (Bool × E) d ℂ :=
      Matrix.of fun p x ↦ ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)
    let W_E : CQChannel (Bool × E) :=
      { out := fun b ↦
          match b with
          | false =>
            { mat := M₀ * M₀ᴴ
              posSemidef := posSemidef_mul_conjTranspose M₀
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hsq2 : ((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
                  rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal,
                    ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
                  push_cast; ring
                have hMM : M₀ᴴ * M₀ = (1 / 2 : ℂ) • (W.out false).mat + (1 / 2 : ℂ) • (W.out true).mat := by
                  ext x y
                  simp only [M₀, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul']
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
                  rw [Finset.sum_add_distrib]
                  congr 1 <;>
                    (apply Finset.sum_congr rfl; intro e _;
                     calc star (star (A₀ x e)) * star ((Real.sqrt 2 : ℂ)⁻¹) * (((Real.sqrt 2 : ℂ)⁻¹) * star (A₀ y e))
                         = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) * (A₀ x e * star (A₀ y e)) := by simp; ring
                       _ = (1 / 2 : ℂ) * (A₀ x e * star (A₀ y e)) := by rw [hsq2]
                     <|>
                     calc star (star (A₁ x e)) * star ((Real.sqrt 2 : ℂ)⁻¹) * (((Real.sqrt 2 : ℂ)⁻¹) * star (A₁ y e))
                         = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) * (A₁ x e * star (A₁ y e)) := by simp; ring
                       _ = (1 / 2 : ℂ) * (A₁ x e * star (A₁ y e)) := by rw [hsq2])
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    (W.out false).trace_one, (W.out true).trace_one]
                simp [smul_eq_mul]; ring }
          | true =>
            { mat := M₁ * M₁ᴴ
              posSemidef := posSemidef_mul_conjTranspose M₁
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hsq2 : ((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
                  rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal,
                    ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
                  push_cast; ring
                have hMM : M₁ᴴ * M₁ = (1 / 2 : ℂ) • (W.out false).mat + (1 / 2 : ℂ) • (W.out true).mat := by
                  ext x y
                  simp only [M₁, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul', star_neg]
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
                  rw [Finset.sum_add_distrib]
                  congr 1 <;>
                    (apply Finset.sum_congr rfl; intro e _;
                     calc star (star (A₀ x e)) * star ((Real.sqrt 2 : ℂ)⁻¹) * (((Real.sqrt 2 : ℂ)⁻¹) * star (A₀ y e))
                         = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) * (A₀ x e * star (A₀ y e)) := by simp; ring
                       _ = (1 / 2 : ℂ) * (A₀ x e * star (A₀ y e)) := by rw [hsq2]
                     <|>
                     calc -(star (star (A₁ x e))) * star ((Real.sqrt 2 : ℂ)⁻¹) * (((Real.sqrt 2 : ℂ)⁻¹) * -(star (A₁ y e)))
                         = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) * (A₁ x e * star (A₁ y e)) := by simp; ring
                       _ = (1 / 2 : ℂ) * (A₁ x e * star (A₁ y e)) := by rw [hsq2])
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    (W.out false).trace_one, (W.out true).trace_one]
                simp [smul_eq_mul]; ring } }
    W.dual.IsoEquiv W_E := by
  intro M₀ M₁ W_E
  have hfactor : ∀ (τ : DensityOp d) (A : Matrix d E ℂ), A * Aᴴ = τ.mat →
      ∃ V : Matrix (E ⊕ d) d ℂ, Vᴴ * V = 1 ∧
        ∀ (y : E ⊕ d) (x : d), (V * τ.sqrtMat) y x =
          match y with
          | Sum.inl e => Aᴴ e x
          | Sum.inr _ => 0 := by
    intro τ A hA
    set U := (τ.eigUnitary : Matrix d d ℂ)
    have hU_mul : U * star U = 1 := Unitary.coe_mul_star_self τ.eigUnitary
    have hU_star : star U * U = 1 := Unitary.coe_star_mul_self τ.eigUnitary
    have hspec : τ.mat = U * Matrix.diagonal (Complex.ofReal ∘ τ.eigvals) * star U :=
      density_spectral_eq τ
    let pinv : Matrix d d ℂ :=
      U * Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) * star U
    let P : Matrix d d ℂ :=
      U * Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) * star U
    let Q : Matrix d d ℂ := 1 - P
    have hP_herm : Pᴴ = P := by
      simp only [P, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      have hd : (Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0))ᴴ =
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) := by
        ext i j; by_cases h : i = j
        · subst h; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply, ↓reduceIte]
          split_ifs <;> simp
        · simp [h, Ne.symm h, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
      rw [hd]; simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    have hP_idem : P * P = P := by
      have hd : Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) *
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) =
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) := by
        rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> simp
      calc P * P = U * (Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) *
              (star U * U) * Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0)) * star U := by
                simp [P, Matrix.mul_assoc]
        _ = P := by rw [hU_star, Matrix.mul_one, hd]
    have hpinv_herm : pinvᴴ = pinv := by
      simp only [pinv, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      have hd : (Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0))ᴴ =
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) := by
        ext i j; by_cases h : i = j
        · subst h; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply, ↓reduceIte]
          split_ifs <;> simp [← Complex.ofReal_inv]
        · simp [h, Ne.symm h, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
      rw [hd]; simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    have hpinv_mul_mat : pinv * τ.mat * pinv = P := by
      have hd : Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) *
          Matrix.diagonal (Complex.ofReal ∘ τ.eigvals) *
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) =
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) := by
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        congr 1; funext i; simp only [Function.comp_apply]
        split_ifs with hi
        · have hne : (Real.sqrt (τ.eigvals i) : ℂ) ≠ 0 :=
            Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hi))
          have hsq : (Real.sqrt (τ.eigvals i) : ℂ) * (Real.sqrt (τ.eigvals i) : ℂ) = (τ.eigvals i : ℂ) := by
            rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hi)]
          rw [← hsq]; field_simp [hne]
        · simp
      calc pinv * τ.mat * pinv
          = U * (Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) *
            (star U * U) * Matrix.diagonal (Complex.ofReal ∘ τ.eigvals) * (star U * U) *
            Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0)) * star U := by
              rw [hspec]; simp [pinv, Matrix.mul_assoc]
        _ = P := by rw [hU_star, Matrix.mul_one, Matrix.mul_one, hd]
    have hsq_spec : τ.sqrtMat = U * Matrix.diagonal (fun i : d ↦ (Real.sqrt (τ.eigvals i) : ℂ)) * star U := rfl
    have hpinv_sqrt : pinv * τ.sqrtMat = P := by
      have hd : Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) *
          Matrix.diagonal (fun i : d ↦ (Real.sqrt (τ.eigvals i) : ℂ)) =
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) := by
        rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i
        split_ifs with hi
        · exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hi)))
        · simp
      calc pinv * τ.sqrtMat
          = U * (Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) *
            (star U * U) * Matrix.diagonal (fun i : d ↦ (Real.sqrt (τ.eigvals i) : ℂ))) * star U := by
              rw [hsq_spec]; simp [pinv, Matrix.mul_assoc]
        _ = P := by rw [hU_star, Matrix.mul_one, hd]
    have hQ_sqrt : Q * τ.sqrtMat = 0 := by
      have hP_sqrt : P * τ.sqrtMat = τ.sqrtMat := by
        have hd : Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) *
            Matrix.diagonal (fun i : d ↦ (Real.sqrt (τ.eigvals i) : ℂ)) =
            Matrix.diagonal (fun i : d ↦ (Real.sqrt (τ.eigvals i) : ℂ)) := by
          rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i
          split_ifs with hi
          · simp
          · have h0 : τ.eigvals i = 0 := le_antisymm (not_lt.mp hi) (τ.eigvals_nonneg i)
            simp [h0]
        calc P * τ.sqrtMat
            = U * (Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) *
              (star U * U) * Matrix.diagonal (fun i : d ↦ (Real.sqrt (τ.eigvals i) : ℂ))) * star U := by
                rw [hsq_spec]; simp [P, Matrix.mul_assoc]
          _ = τ.sqrtMat := by rw [hU_star, Matrix.mul_one, hd, ← hsq_spec]
      simp [Q, Matrix.sub_mul, Matrix.one_mul, hP_sqrt]
    have hQ_herm : Qᴴ = Q := by simp [Q, hP_herm]
    have hQ_idem : Q * Q = Q := by
      simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP_idem]; abel
    have hAH_Q : Aᴴ * Q = 0 := by
      have hQ_mat : Q * τ.mat * Qᴴ = 0 := by
        have hsq2 : τ.sqrtMat * τ.sqrtMat = τ.mat := τ.sqrtMat_mul_self
        rw [← hsq2]; calc Q * (τ.sqrtMat * τ.sqrtMat) * Qᴴ = (Q * τ.sqrtMat) * (τ.sqrtMat * Qᴴ) := by simp [Matrix.mul_assoc]
          _ = 0 := by rw [hQ_sqrt, Matrix.zero_mul]
      have hAQ : (Aᴴ * Q)ᴴ * (Aᴴ * Q) = 0 := by
        calc (Aᴴ * Q)ᴴ * (Aᴴ * Q) = Qᴴ * (A * Aᴴ) * Q := by
                simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = Q * τ.mat * Qᴴ := by rw [hA, hQ_herm]
          _ = 0 := hQ_mat
      ext e x
      have hdiag := congr_fun (congr_fun hAQ x) x
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply] at hdiag
      have hre := congr_arg Complex.re hdiag
      simp only [Complex.zero_re, Complex.re_sum] at hre
      have hsum : ∑ e' : E, ‖(Aᴴ * Q) e' x‖ ^ 2 = 0 := by
        rw [← hre]
        apply Finset.sum_congr rfl; intro e' _
        have hsq : star ((Aᴴ * Q) e' x) * (Aᴴ * Q) e' x = ((‖(Aᴴ * Q) e' x‖ ^ 2 : ℝ) : ℂ) := by
          rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [hsq, Complex.ofReal_re]
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun e' _ ↦ sq_nonneg ‖(Aᴴ * Q) e' x‖)).mp
        hsum e (Finset.mem_univ e)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hterm)
    have hAH_P : Aᴴ * P = Aᴴ := by
      have : Aᴴ * (1 - P) = 0 := hAH_Q
      rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
      exact this.symm
    let W_mat : Matrix E d ℂ := Aᴴ * pinv
    let V : Matrix (E ⊕ d) d ℂ := Matrix.of fun y x ↦
      match y with
      | Sum.inl e => W_mat e x
      | Sum.inr r => Q r x
    refine ⟨V, ?_, ?_⟩
    · ext i j
      simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_sum_type, Matrix.one_apply]
      have h1 : ∑ e : E, star (W_mat e i) * W_mat e j = P i j := by
        have hWW : W_matᴴ * W_mat = P := by
          calc W_matᴴ * W_mat = pinvᴴ * (A * Aᴴ) * pinv := by
                  simp [W_mat, Matrix.conjTranspose_mul, Matrix.mul_assoc]
            _ = pinv * τ.mat * pinv := by rw [hpinv_herm, hA]
            _ = P := hpinv_mul_mat
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using congr_fun (congr_fun hWW i) j
      have h2 : ∑ r : d, star (Q r i) * Q r j = Q i j := by
        have hQQ : Qᴴ * Q = Q := by rw [hQ_herm, hQ_idem]
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using congr_fun (congr_fun hQQ i) j
      rw [h1, h2]
      have hPQ : P + Q = 1 := by simp [Q]
      have := congr_fun (congr_fun hPQ i) j
      simpa [Matrix.add_apply, Matrix.one_apply] using this
    · intro y x
      cases y with
      | inl e =>
        have h1 : (V * τ.sqrtMat) (Sum.inl e) x = (W_mat * τ.sqrtMat) e x := by
          simp [V, Matrix.mul_apply]
        rw [h1]
        have hWsq : W_mat * τ.sqrtMat = Aᴴ := by
          calc W_mat * τ.sqrtMat = Aᴴ * (pinv * τ.sqrtMat) := by simp [W_mat, Matrix.mul_assoc]
            _ = Aᴴ * P := by rw [hpinv_sqrt]
            _ = Aᴴ := hAH_P
        rw [hWsq]
      | inr r =>
        have h1 : (V * τ.sqrtMat) (Sum.inr r) x = (Q * τ.sqrtMat) r x := by
          simp [V, Matrix.mul_apply]
        rw [h1, hQ_sqrt]; rfl
  obtain ⟨V₀, hV₀, hV₀_sq⟩ := hfactor (W.out false) A₀ hA₀
  obtain ⟨V₁, hV₁, hV₁_sq⟩ := hfactor (W.out true) A₁ hA₁
  let V : Matrix (Bool × (E ⊕ d)) (Bool × d) ℂ :=
    Matrix.of fun p q ↦ if p.1 = q.1 then (if p.1 = false then V₀ p.2 q.2 else V₁ p.2 q.2) else 0
  let ι : Matrix (Bool × (E ⊕ d)) (Bool × E) ℂ :=
    Matrix.of fun p q ↦ if p.1 = q.1 ∧ p.2 = Sum.inl q.2 then 1 else 0
  have hV_iso : Vᴴ * V = 1 := by
    ext ⟨b₁, x₁⟩ ⟨b₂, x₂⟩
    simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
    by_cases hb : b₁ = b₂
    · subst hb
      rw [Finset.sum_eq_single b₁]
      · cases b₁
        · have h := congr_fun (congr_fun hV₀ x₁) x₂
          simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
        · have h := congr_fun (congr_fun hV₁ x₁) x₂
          simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
      · intro c _ hne; apply Finset.sum_eq_zero; intro y _; simp [hne]
      · intro h; exact absurd (Finset.mem_univ b₁) h
    · simp only [Prod.mk.injEq, hb, false_and, ↓reduceIte]
      apply Finset.sum_eq_zero; intro c _
      apply Finset.sum_eq_zero; intro y _
      by_cases hc : c = b₁
      · subst hc; simp [hb]
      · simp [hc]
  have hι_iso : ιᴴ * ι = 1 := by
    ext ⟨b₁, e₁⟩ ⟨b₂, e₂⟩
    simp only [ι, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply]
    by_cases h : (b₁, e₁) = (b₂, e₂)
    · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single b₁]
      · have h2 : ∑ a₂ : d, star (if b₁ = b₁ ∧ (Sum.inr a₂ : E ⊕ d) = Sum.inl e₁ then (1 : ℂ) else 0) *
            (if b₁ = b₁ ∧ (Sum.inr a₂ : E ⊕ d) = Sum.inl e₁ then 1 else 0) = 0 := by simp
        rw [h2, add_zero, Finset.sum_eq_single e₁]
        · simp
        · intro a₁ _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ e₁) h
      · intro c _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ b₁) h
    · simp only [h, ↓reduceIte]
      apply Finset.sum_eq_zero; intro c _
      have h2 : ∑ a₂ : d, star (if c = b₁ ∧ (Sum.inr a₂ : E ⊕ d) = Sum.inl e₁ then (1 : ℂ) else 0) *
          (if c = b₂ ∧ (Sum.inr a₂ : E ⊕ d) = Sum.inl e₂ then 1 else 0) = 0 := by simp
      rw [h2, add_zero]
      apply Finset.sum_eq_zero; intro a₁ _
      by_cases h1 : c = b₁ ∧ a₁ = e₁
      · rcases h1 with ⟨rfl, rfl⟩
        have h2' : ¬ (c = b₂ ∧ a₁ = e₂) := fun ⟨hb, he⟩ ↦ h (by rw [hb, he])
        simp [h2']
      · simp [h1]
  have hVM₀ : V * gramFactor (W.out false) (W.out true) = ι * M₀ := by
    ext ⟨b, y⟩ x
    simp only [V, ι, gramFactor, M₀, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single b, Finset.sum_eq_single b]
    · cases b
      · simp only [↓reduceIte]
        have hL : ∑ r : d, V₀ y r * (((Real.sqrt 2 : ℂ)⁻¹) * (W.out false).sqrtMat r x) =
            ((Real.sqrt 2 : ℂ)⁻¹) * (V₀ * (W.out false).sqrtMat) y x := by
          simp only [Matrix.mul_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro r _; ring
        rw [hL, hV₀_sq y x]
        cases y with
        | inl e =>
          rw [Finset.sum_eq_single e]
          · simp
          · intro e' _ hne; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ e) h
        | inr r => simp
      · simp only [↓reduceIte, Bool.true_eq_false]
        have hL : ∑ r : d, V₁ y r * (((Real.sqrt 2 : ℂ)⁻¹) * (W.out true).sqrtMat r x) =
            ((Real.sqrt 2 : ℂ)⁻¹) * (V₁ * (W.out true).sqrtMat) y x := by
          simp only [Matrix.mul_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro r _; ring
        rw [hL, hV₁_sq y x]
        cases y with
        | inl e =>
          rw [Finset.sum_eq_single e]
          · simp
          · intro e' _ hne; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ e) h
        | inr r => simp
    · intro c _ hne; apply Finset.sum_eq_zero; intro e _; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ b) h
    · intro c _ hne; apply Finset.sum_eq_zero; intro r _; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ b) h
  have hVM₁ : V * ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) *
      gramFactor (W.out false) (W.out true)) = ι * M₁ := by
    have hZ_comm : V * (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) =
        (pauliZTensorI (E ⊕ d) : Matrix (Bool × (E ⊕ d)) (Bool × (E ⊕ d)) ℂ) * V := by
      ext ⟨b₁, y⟩ ⟨b₂, x⟩
      simp only [V, pauliZTensorI, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
      cases b₁ <;> cases b₂ <;> simp
    have hZ_ι : (pauliZTensorI (E ⊕ d) : Matrix (Bool × (E ⊕ d)) (Bool × (E ⊕ d)) ℂ) * ι =
        ι * (pauliZTensorI E : Matrix (Bool × E) (Bool × E) ℂ) := by
      ext ⟨b₁, y⟩ ⟨b₂, e⟩
      simp only [ι, pauliZTensorI, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
      cases b₁ <;> cases b₂ <;> simp
    have hZ_M₀ : (pauliZTensorI E : Matrix (Bool × E) (Bool × E) ℂ) * M₀ = M₁ := by
      ext ⟨b, e⟩ x
      simp only [pauliZTensorI, M₀, M₁, Matrix.diagonal_mul, Matrix.of_apply]
      cases b <;> simp
    calc V * ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) * gramFactor (W.out false) (W.out true))
        = (V * (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)) * gramFactor (W.out false) (W.out true) := by
            rw [Matrix.mul_assoc]
      _ = (pauliZTensorI (E ⊕ d) : Matrix (Bool × (E ⊕ d)) (Bool × (E ⊕ d)) ℂ) * (V * gramFactor (W.out false) (W.out true)) := by
            rw [hZ_comm, Matrix.mul_assoc]
      _ = (pauliZTensorI (E ⊕ d) : Matrix (Bool × (E ⊕ d)) (Bool × (E ⊕ d)) ℂ) * (ι * M₀) := by rw [hVM₀]
      _ = ι * ((pauliZTensorI E : Matrix (Bool × E) (Bool × E) ℂ) * M₀) := by
            rw [← Matrix.mul_assoc, hZ_ι, Matrix.mul_assoc]
      _ = ι * M₁ := by rw [hZ_M₀]
  refine ⟨Bool × (E ⊕ d), inferInstance, inferInstance, V, ι, hV_iso, hι_iso, ?_⟩
  intro b; cases b
  · change V * (gramFactor (W.out false) (W.out true) * (gramFactor (W.out false) (W.out true))ᴴ) * Vᴴ =
      ι * (M₀ * M₀ᴴ) * ιᴴ
    calc V * (gramFactor (W.out false) (W.out true) * (gramFactor (W.out false) (W.out true))ᴴ) * Vᴴ
        = (V * gramFactor (W.out false) (W.out true)) * (V * gramFactor (W.out false) (W.out true))ᴴ := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (ι * M₀) * (ι * M₀)ᴴ := by rw [hVM₀]
      _ = ι * (M₀ * M₀ᴴ) * ιᴴ := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · change V * ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) *
        (gramFactor (W.out false) (W.out true) * (gramFactor (W.out false) (W.out true))ᴴ) *
        star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)) * Vᴴ =
      ι * (M₁ * M₁ᴴ) * ιᴴ
    set G := gramFactor (W.out false) (W.out true)
    set Zd := (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)
    calc V * (Zd * (G * Gᴴ) * star Zd) * Vᴴ
        = (V * (Zd * G)) * (V * (Zd * G))ᴴ := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
      _ = (ι * M₁) * (ι * M₁)ᴴ := by rw [hVM₁]
      _ = ι * (M₁ * M₁ᴴ) * ιᴴ := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Proposition 2.2 (D3, Exact Output-Isometry Duality for Pure-State Channels)**:
`Pure(1 - 2p)⊥` is literally output-isometry equivalent (`IsoEquiv`) to `BSC(p)` for all `p ∈ [0, 1/2]`. -/
theorem prop_2_2_D3_isoEquiv_pure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (pureChannel (1 - 2 * p) (by linarith) (by linarith)).dual.IsoEquiv
      (bscChannel p hp0 (by linarith)) := by
  set f : ℝ := 1 - 2 * p
  have hf0 : 0 ≤ f := by linarith
  have hf1 : f ≤ 1 := by linarith
  have h1pf : (1 + f) / 2 = 1 - p := by simp only [f]; ring
  have h1mf : (1 - f) / 2 = p := by simp only [f]; ring
  let A₀ : Matrix Bool PUnit.{1} ℂ :=
    Matrix.of fun b _ ↦ if b = false then (Real.sqrt (1 - p) : ℂ) else (Real.sqrt p : ℂ)
  let A₁ : Matrix Bool PUnit.{1} ℂ :=
    Matrix.of fun b _ ↦ if b = false then (Real.sqrt (1 - p) : ℂ) else -(Real.sqrt p : ℂ)
  have hA₀ : A₀ * A₀ᴴ = ((pureChannel f hf0 hf1).out false).mat := by
    ext i j
    cases i <;> cases j <;>
      simp [A₀, pureChannel, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply, Fintype.sum_unique, h1pf, h1mf]
  have hA₁ : A₁ * A₁ᴴ = ((pureChannel f hf0 hf1).out true).mat := by
    ext i j
    cases i <;> cases j <;>
      simp [A₁, pureChannel, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply, Fintype.sum_unique, h1pf, h1mf]
  obtain ⟨γ, _, _, V₁, V₂, h1, h2, heq⟩ :=
    dual_isoEquiv_of_purification (pureChannel f hf0 hf1) A₀ A₁ hA₀ hA₁
  let H : Matrix (Bool × PUnit.{1}) Bool ℂ :=
    Matrix.of fun r c ↦ ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = true ∧ c = true then -1 else 1)
  have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
  have hH_iso : Hᴴ * H = 1 := by
    ext i j
    simp only [H, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool, Matrix.one_apply, star_mul']
    cases i <;> cases j <;> (simp [hstar2, hmul2]; try norm_num)
  have hsp1 : (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) = ((1 - p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hsp2 : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
  have hH_bsc : ∀ b : Bool,
      H * ((bscChannel p hp0 (by linarith)).out b).mat * Hᴴ =
        (match b with
         | false =>
           (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
             ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x)) *
           (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
             ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x))ᴴ
         | true =>
           (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
             ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x)) *
           (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
             ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x))ᴴ) := by
    intro b
    ext ⟨r₁, ⟨⟩⟩ ⟨r₂, ⟨⟩⟩
    cases b <;> cases r₁ <;> cases r₂ <;>
      (simp [H, A₀, A₁, bscChannel, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply, Matrix.diagonal_apply, Fintype.sum_bool, hstar2, hmul2, hsp1, hsp2];
       try (ring_nf; simp only [sq, hmul2, hsp1, hsp2]; push_cast; ring))
  refine ⟨γ, inferInstance, inferInstance, V₁, V₂ * H, h1, ?_, ?_⟩
  · calc (V₂ * H)ᴴ * (V₂ * H) = Hᴴ * (V₂ᴴ * V₂) * H := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hH_iso]
  · intro b
    calc V₁ * ((pureChannel f hf0 hf1).dual.out b).mat * V₁ᴴ
        = V₂ * (match b with
            | false =>
              (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
                ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x)) *
              (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
                ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x))ᴴ
            | true =>
              (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
                ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x)) *
              (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
                ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x))ᴴ) * V₂ᴴ := by
            cases b <;> exact heq _
      _ = V₂ * (H * ((bscChannel p hp0 (by linarith)).out b).mat * Hᴴ) * V₂ᴴ := by rw [hH_bsc b]
      _ = (V₂ * H) * ((bscChannel p hp0 (by linarith)).out b).mat * (V₂ * H)ᴴ := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Proposition 2.2 (D3, Channel-Level Dualities for BSC, Pure-State, and BEC Channels)**:
For every `p ∈ [0, 1/2]` and `ε ∈ [0, 1]`:
1. `BSC(p)⊥ ≃ Pure(1 - 2p)`
2. `Pure(1 - 2p)⊥ ≃ BSC(p)`
3. `BEC(ε)⊥ ≃ BEC(1 - ε)`. -/
theorem prop_2_2_D3_channelEquiv {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (bscChannel p hp0 (by linarith)).dual.ChannelEquiv
      (pureChannel (1 - 2 * p) (by linarith) (by linarith)) ∧
    (pureChannel (1 - 2 * p) (by linarith) (by linarith)).dual.ChannelEquiv
      (bscChannel p hp0 (by linarith)) ∧
    (becChannel ε hε0 hε1).dual.ChannelEquiv
      (becChannel (1 - ε) (by linarith) (by linarith)) := by
  refine ⟨?_, (prop_2_2_D3_isoEquiv_pure hp0 hp1).toChannelEquiv, ?_⟩
  · -- 1. `BSC(p)⊥ ≃ Pure(1 - 2p)`:
    set f : ℝ := 1 - 2 * p
    have hf0 : 0 ≤ f := by linarith
    have hf1 : f ≤ 1 := by linarith
    have h1pf : (1 + f) / 2 = 1 - p := by simp only [f]; ring
    have h1mf : (1 - f) / 2 = p := by simp only [f]; ring
    let A₀ : Matrix Bool Bool ℂ :=
      Matrix.diagonal fun k : Bool ↦ if k = false then (Real.sqrt (1 - p) : ℂ) else (Real.sqrt p : ℂ)
    let A₁ : Matrix Bool Bool ℂ :=
      Matrix.diagonal fun k : Bool ↦ if k = false then (Real.sqrt p : ℂ) else (Real.sqrt (1 - p) : ℂ)
    have hsp1 : (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) = ((1 - p : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
    have hsp2 : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
    have hA₀ : A₀ * A₀ᴴ = ((bscChannel p hp0 (by linarith)).out false).mat := by
      ext i j; cases i <;> cases j <;>
        simp [A₀, bscChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, hsp1, hsp2]
    have hA₁ : A₁ * A₁ᴴ = ((bscChannel p hp0 (by linarith)).out true).mat := by
      ext i j; cases i <;> cases j <;>
        simp [A₁, bscChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, hsp1, hsp2]
    have hstep1 := (dual_isoEquiv_of_purification (bscChannel p hp0 (by linarith)) A₀ A₁ hA₀ hA₁).toChannelEquiv
    let U : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
      Matrix.of fun r c ↦ if r.2 = c.1 ∧ xor r.1 r.2 = c.2 then 1 else 0
    have hU_iso : Uᴴ * U = 1 := by
      ext ⟨c₁, s₁⟩ ⟨c₂, s₂⟩
      simp only [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_prod_type, Fintype.sum_bool, Matrix.one_apply]
      cases c₁ <;> cases s₁ <;> cases c₂ <;> cases s₂ <;> simp
    have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast; ring
    have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
    let M : Bool → Matrix (Bool × Bool) Bool ℂ := fun b ↦
      match b with
      | false => Matrix.of fun (r : Bool × Bool) (x : Bool) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x)
      | true => Matrix.of fun (r : Bool × Bool) (x : Bool) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x)
    let N : Bool → Matrix (Bool × Bool) Bool ℂ := fun b ↦
      match b with
      | false => Matrix.of fun (q : Bool × Bool) (x : Bool) ↦
          if q.1 = x then
            ((Real.sqrt 2 : ℂ)⁻¹) * (if q.2 = false then (Real.sqrt (1 - p) : ℂ) else (Real.sqrt p : ℂ))
          else 0
      | true => Matrix.of fun (q : Bool × Bool) (x : Bool) ↦
          if q.1 = x then
            (if q.1 = false then (1 : ℂ) else (-1 : ℂ)) * ((Real.sqrt 2 : ℂ)⁻¹) *
              (if q.2 = false then (Real.sqrt (1 - p) : ℂ) else -(Real.sqrt p : ℂ))
          else 0
    have hMN : ∀ b, M b = U * N b := by
      intro b; ext ⟨r₁, r₂⟩ x
      simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, U, M, N, A₀, A₁,
        Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
      cases b <;> cases r₁ <;> cases r₂ <;> cases x <;> simp <;> ring
    have hNN : ∀ b, N b * (N b)ᴴ = (((pureChannel f hf0 hf1).tensorMaxMixed Bool).out b).mat := by
      intro b; ext ⟨c₁, s₁⟩ ⟨c₂, s₂⟩
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool, N,
        CQChannel.tensorMaxMixed, DensityOp.tensor, maxMixedState, pureChannel, pureState,
        Matrix.of_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, h1pf, h1mf, Fintype.card_bool, Nat.cast_ofNat]
      cases b <;> cases c₁ <;> cases s₁ <;> cases c₂ <;> cases s₂ <;>
        (simp [hstar2, hmul2, hsp1, hsp2]; try (ring_nf; simp only [sq, hmul2, hsp1, hsp2]; push_cast; ring))
    have hstep2 : CQChannel.IsoEquiv
        ({ out := fun b ↦
            match b with
            | false =>
              { mat := M false * (M false)ᴴ
                posSemidef := posSemidef_mul_conjTranspose (M false)
                trace_one := by
                  have h := (((pureChannel f hf0 hf1).tensorMaxMixed Bool).out false).trace_one
                  rw [hMN false, Matrix.conjTranspose_mul, Matrix.mul_assoc,
                    ← Matrix.mul_assoc (N false), hNN false, ← Matrix.mul_assoc,
                    Matrix.trace_mul_cycle, hU_iso, Matrix.one_mul]
                  exact h }
            | true =>
              { mat := M true * (M true)ᴴ
                posSemidef := posSemidef_mul_conjTranspose (M true)
                trace_one := by
                  have h := (((pureChannel f hf0 hf1).tensorMaxMixed Bool).out true).trace_one
                  rw [hMN true, Matrix.conjTranspose_mul, Matrix.mul_assoc,
                    ← Matrix.mul_assoc (N true), hNN true, ← Matrix.mul_assoc,
                    Matrix.trace_mul_cycle, hU_iso, Matrix.one_mul]
                  exact h } } : CQChannel (Bool × Bool))
        ((pureChannel f hf0 hf1).tensorMaxMixed Bool) := by
      refine ⟨Bool × Bool, inferInstance, inferInstance, 1, U, by simp, hU_iso, ?_⟩
      intro b
      cases b
      · simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
        rw [hMN false, Matrix.conjTranspose_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc (N false), hNN false, ← Matrix.mul_assoc]
      · simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
        rw [hMN true, Matrix.conjTranspose_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc (N true), hNN true, ← Matrix.mul_assoc]
    exact (hstep1.trans hstep2.toChannelEquiv).trans
      ((pureChannel f hf0 hf1).channelEquiv_tensorMaxMixed Bool).symm
  · -- 3. `BEC(ε)⊥ ≃ BEC(1 - ε)`:
    let A₀ : Matrix (Fin 3) (Fin 3) ℂ :=
      Matrix.diagonal ![((Real.sqrt (1 - ε) : ℂ)), 0, ((Real.sqrt ε : ℂ))]
    let A₁ : Matrix (Fin 3) (Fin 3) ℂ :=
      Matrix.diagonal ![0, ((Real.sqrt (1 - ε) : ℂ)), ((Real.sqrt ε : ℂ))]
    have hs1 : (Real.sqrt (1 - ε) : ℂ) * (Real.sqrt (1 - ε) : ℂ) = ((1 - ε : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
    have hs2 : (Real.sqrt ε : ℂ) * (Real.sqrt ε : ℂ) = (ε : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hε0]
    have hA₀ : A₀ * A₀ᴴ = ((becChannel ε hε0 hε1).out false).mat := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [A₀, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three, hs1, hs2]
    have hA₁ : A₁ * A₁ᴴ = ((becChannel ε hε0 hε1).out true).mat := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [A₁, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three, hs1, hs2]
    have hstep1 := (dual_isoEquiv_of_purification (becChannel ε hε0 hε1) A₀ A₁ hA₀ hA₁).toChannelEquiv
    have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast; ring
    have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
    let M : Bool → Matrix (Bool × Fin 3) (Fin 3) ℂ := fun b ↦
      match b with
      | false => Matrix.of fun (r : Bool × Fin 3) (x : Fin 3) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x)
      | true => Matrix.of fun (r : Bool × Fin 3) (x : Fin 3) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x)
    let D : Bool → Matrix (Bool × Fin 3) (Bool × Fin 3) ℂ := fun b ↦
      Matrix.of fun r₁ r₂ ↦
        if r₁ = (false, 0) ∧ r₂ = (false, 0) then ((1 - ε : ℝ) : ℂ) / 2
        else if r₁ = (true, 1) ∧ r₂ = (true, 1) then ((1 - ε : ℝ) : ℂ) / 2
        else if r₁.2 = 2 ∧ r₂.2 = 2 then
          if b = false ∨ r₁.1 = r₂.1 then (ε : ℂ) / 2 else -((ε : ℂ) / 2)
        else 0
    have hMD : ∀ b, M b * (M b)ᴴ = D b := by
      intro b; ext ⟨r₁, k₁⟩ ⟨r₂, k₂⟩
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
        M, D, A₀, A₁, Matrix.of_apply, Matrix.diagonal_apply]
      cases b <;> cases r₁ <;> cases r₂ <;> fin_cases k₁ <;> fin_cases k₂ <;>
        (simp [hstar2, hmul2, hs1, hs2]; try (ring_nf; simp only [sq, hmul2, hs1, hs2]; push_cast; ring))
    let V𝒩 : Matrix (Fin 3 × (Bool × Fin 3)) (Bool × Fin 3) ℂ :=
      Matrix.of fun p q ↦
        if q.2 = 0 then (if p.1 = 2 ∧ p.2 = (q.1, 0) then 1 else 0)
        else if q.2 = 1 then (if p.1 = 2 ∧ p.2 = (q.1, 1) then 1 else 0)
        else
          if p.2 = (false, 2) then
            if p.1 = 0 then ((Real.sqrt 2 : ℂ)⁻¹)
            else if p.1 = 1 then (if q.1 = false then ((Real.sqrt 2 : ℂ)⁻¹) else -((Real.sqrt 2 : ℂ)⁻¹))
            else 0
          else 0
    have hV𝒩 : V𝒩ᴴ * V𝒩 = 1 := by
      ext ⟨b₁, k₁⟩ ⟨b₂, k₂⟩
      simp only [V𝒩, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, Matrix.one_apply]
      fin_cases k₁ <;> fin_cases k₂ <;> cases b₁ <;> cases b₂ <;>
        (simp [hstar2, hmul2]; try norm_num; try (ring_nf; simp only [sq, hmul2]; norm_num))
    let 𝒩 : CPTPMap.{0} (Bool × Fin 3) (Fin 3) :=
      ⟨Bool × Fin 3, inferInstance, inferInstance, V𝒩, hV𝒩⟩
    let Q : Bool → Matrix (Fin 3 × (Bool × Fin 3)) (Fin 3) ℂ := fun b ↦
      Matrix.of fun p x ↦
        if p = (2, (false, 0)) ∧ x = 0 then ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt (1 - ε) : ℂ)
        else if p = (2, (true, 1)) ∧ x = 1 then (if b = false then 1 else -1) * ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt (1 - ε) : ℂ)
        else if p = (0, (false, 2)) ∧ x = 2 ∧ b = false then (Real.sqrt ε : ℂ)
        else if p = (1, (false, 2)) ∧ x = 2 ∧ b = true then (Real.sqrt ε : ℂ)
        else 0
    have hNQ : ∀ b, V𝒩 * M b = Q b := by
      intro b; ext ⟨i, e⟩ x
      simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three,
        V𝒩, M, Q, A₀, A₁, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
      fin_cases x
      · cases b <;> fin_cases i <;> by_cases he : e = (false, 0) <;> simp [he]
      · cases b <;> fin_cases i <;> by_cases he : e = (true, 1) <;> simp [he]
      · cases b <;> fin_cases i <;> by_cases he : e = (false, 2) <;>
          (simp [he]; try (ring_nf; simp only [sq, hmul2]; ring))
    let Vℳ : Matrix ((Bool × Fin 3) × Bool) (Fin 3) ℂ :=
      Matrix.of fun p k ↦
        if k = 0 then (if p.2 = false ∧ p.1.2 = 2 then ((Real.sqrt 2 : ℂ)⁻¹) else 0)
        else if k = 1 then (if p.2 = false ∧ p.1.2 = 2 then (if p.1.1 = false then ((Real.sqrt 2 : ℂ)⁻¹) else -((Real.sqrt 2 : ℂ)⁻¹)) else 0)
        else
          if p = ((false, 0), false) ∨ p = ((true, 1), true) then ((Real.sqrt 2 : ℂ)⁻¹) else 0
    have hVℳ : Vℳᴴ * Vℳ = 1 := by
      ext k₁ k₂
      simp only [Vℳ, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, Matrix.one_apply]
      fin_cases k₁ <;> fin_cases k₂ <;>
        (simp [hstar2, hmul2]; try norm_num; try (ring_nf; simp only [sq, hmul2]; norm_num))
    let ℳ : CPTPMap.{0} (Fin 3) (Bool × Fin 3) :=
      ⟨Bool, inferInstance, inferInstance, Vℳ, hVℳ⟩
    have hstep2 : CQChannel.ChannelEquiv
        ({ out := fun b ↦
            match b with
            | false =>
              { mat := M false * (M false)ᴴ
                posSemidef := posSemidef_mul_conjTranspose (M false)
                trace_one := by
                  rw [hMD false]
                  simp only [Matrix.trace, Matrix.diag, D, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three]
                  simp; push_cast; ring }
            | true =>
              { mat := M true * (M true)ᴴ
                posSemidef := posSemidef_mul_conjTranspose (M true)
                trace_one := by
                  rw [hMD true]
                  simp only [Matrix.trace, Matrix.diag, D, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three]
                  simp; push_cast; ring } } : CQChannel (Bool × Fin 3))
        (becChannel (1 - ε) (by linarith) (by linarith)) := by
      refine ⟨𝒩, ℳ, ?_, ?_⟩
      · intro b
        have hmat : V𝒩 * ((match b with
            | false => ({ mat := M false * (M false)ᴴ, posSemidef := posSemidef_mul_conjTranspose (M false), trace_one := _ } : DensityOp (Bool × Fin 3))
            | true => ({ mat := M true * (M true)ᴴ, posSemidef := posSemidef_mul_conjTranspose (M true), trace_one := _ } : DensityOp (Bool × Fin 3))).mat) * V𝒩ᴴ =
            Q b * (Q b)ᴴ := by
          cases b <;>
            calc V𝒩 * (M _ * (M _)ᴴ) * V𝒩ᴴ
                = (V𝒩 * M _) * (V𝒩 * M _)ᴴ := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
              _ = Q _ * (Q _)ᴴ := by rw [hNQ]
        ext i j
        change (partialTrace₂Mat (V𝒩 * _ * V𝒩ᴴ)) i j = ((becChannel (1 - ε) _ _).out b).mat i j
        rw [hmat]
        dsimp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk]
        cases b <;> fin_cases i <;> fin_cases j <;>
          (simp [Q, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three,
            hstar2, hmul2, hs1, hs2];
           try (ring_nf; simp only [sq, hmul2, hs1, hs2]; push_cast; ring))
      · intro b
        ext ⟨r₁, k₁⟩ ⟨r₂, k₂⟩
        have hmat : ((match b with
            | false => ({ mat := M false * (M false)ᴴ, posSemidef := posSemidef_mul_conjTranspose (M false), trace_one := _ } : DensityOp (Bool × Fin 3))
            | true => ({ mat := M true * (M true)ᴴ, posSemidef := posSemidef_mul_conjTranspose (M true), trace_one := _ } : DensityOp (Bool × Fin 3))).mat) = D b := by
          cases b <;> exact hMD _
        change (partialTrace₂Mat (Vℳ * ((becChannel (1 - ε) _ _).out b).mat * Vℳᴴ))
          (r₁, k₁) (r₂, k₂) = _
        rw [hmat]
        dsimp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, Vℳ]
        fin_cases k₁ <;> fin_cases k₂
        · cases b <;> cases r₁ <;> cases r₂ <;>
            (simp [D, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
              Fintype.sum_bool, Fin.sum_univ_three, hstar2, hmul2];
             try (ring_nf; simp only [sq, hmul2]; push_cast; ring))
        · simp [D, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
            Fintype.sum_bool, Fin.sum_univ_three]
        · simp [D, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
            Fintype.sum_bool, Fin.sum_univ_three]
        · simp [D, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
            Fintype.sum_bool, Fin.sum_univ_three]
        · cases b <;> cases r₁ <;> cases r₂ <;>
            (simp [D, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
              Fintype.sum_bool, Fin.sum_univ_three, hstar2, hmul2];
             try (ring_nf; simp only [sq, hmul2]; push_cast; ring))
        · simp [D, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
            Fintype.sum_bool, Fin.sum_univ_three]
        · simp [D, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
            Fintype.sum_bool, Fin.sum_univ_three]
        · simp [D, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
            Fintype.sum_bool, Fin.sum_univ_three]
        · cases b <;> cases r₁ <;> cases r₂ <;>
            (simp [D, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
              Fintype.sum_bool, Fin.sum_univ_three, hstar2, hmul2];
             try (ring_nf; simp only [sq, hmul2]; push_cast; ring))
    exact hstep1.trans hstep2

end ChannelEquivalence

end PolarCodes
