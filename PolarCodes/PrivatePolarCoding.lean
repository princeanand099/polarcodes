/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.QuantumPolarCoding
import PolarCodes.PhiAndFuchs

/-!
# Operational Private Classical Polar Coding over Quantum Wiretap Channels (Renes–Wilde [10])

This module formalizes the operational wiretap private classical polar coding layer of
Corollary 5.5 (Renes–Wilde [10]) unconditionally on top of Mathlib:
1. Elementary properties of trace distance (`traceDist_nonneg`, `traceDist_symm`,
   `traceDist_triangle`, `traceDist_cptp_le`, `traceDist_blockDiag_eq_avg`, `traceDist_avg_le`).
2. **Exact Channel-Duality Identity** (`traceDist_dual_eq_fidelityParam`):
   `T(W⊥(0), W⊥(1)) = Z(W)` for every binary c-q channel `W`, yielding
   `T((W_E)_N^{(i)}(0), (W_E)_N^{(i)}(1)) = Z((W_P)_N^{(i⊥)})` for every complementary channel
   `W_E = ampChannel 𝒩.complementary` and phase channel `W_P = phaseChannel 𝒩`.
3. **Operational Wiretap Scheme & Telescoping Decoupling**:
   Randomized privacy-amplification encoder, pre-shared secret-key register `ℰ`, wiretap Eve
   joint state `ρ_{ME}` via `(𝒩.complementary)^⊗N`, Bob's QSC decoding error, and Eve's
   secrecy trace-distance bound `T(ρ_{ME}, π_M ⊗ ρ_E) ≤ 2^{-N^{0.49}}`.
-/

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodes

section TraceDistProps

variable {d : Type*} [Fintype d] [DecidableEq d]

private lemma posPartTrace_add_le_aux {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Matrix α α ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    posPartTrace (hA.add hB) ≤ posPartTrace hA + posPartTrace hB := by
  have hP_psd : (posPartMat hA + posPartMat hB).PosSemidef :=
    (posPartMat_posSemidef hA).add (posPartMat_posSemidef hB)
  have hdiff_psd : ((posPartMat hA + posPartMat hB) - (A + B)).PosSemidef := by
    have hsub : (posPartMat hA + posPartMat hB) - (A + B) = negPartMat hA + negPartMat hB := by
      have h1 := posPartMat_sub_negPartMat hA
      have h2 := posPartMat_sub_negPartMat hB
      have e1 : posPartMat hA - A = negPartMat hA := sub_eq_of_eq_add' (eq_add_of_sub_eq h1)
      have e2 : posPartMat hB - B = negPartMat hB := sub_eq_of_eq_add' (eq_add_of_sub_eq h2)
      rw [← e1, ← e2]; abel
    rw [hsub]; exact (negPartMat_posSemidef hA).add (negPartMat_posSemidef hB)
  have hle := posPartTrace_le_trace_of_le (hA.add hB) hP_psd hdiff_psd
  rw [Matrix.trace_add, trace_posPartMat hA, trace_posPartMat hB, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_re] at hle
  exact hle

private lemma posPartTrace_smul_nonneg_aux {α : Type*} [Fintype α] [DecidableEq α]
    {c : ℝ} (hc : 0 ≤ c) {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    posPartTrace (show ((c : ℂ) • A).IsHermitian by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hA.eq]) =
    c * posPartTrace hA := by
  have hnegA : (-A).IsHermitian := by rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, hA.eq]
  have hcA : ((c : ℂ) • A).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hA.eq]
  have hnegcA : (-((c : ℂ) • A)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, hcA.eq]
  have h1 : posPartTrace hcA = negPartTrace hnegcA := by
    rw [negPartTrace_eq_posPartTrace_neg hnegcA (by rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, hnegcA.eq])]
    exact posPartTrace_eq_of_eq _ _ (by simp)
  have h2 : posPartTrace hA = negPartTrace hnegA := by
    rw [negPartTrace_eq_posPartTrace_neg hnegA (by rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, hnegA.eq])]
    exact posPartTrace_eq_of_eq _ _ (by simp)
  have h3 : negPartTrace hnegcA = negPartTrace (show ((c : ℂ) • (-A)).IsHermitian by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hnegA.eq]) :=
    negPartTrace_eq_of_eq _ _ (by simp)
  rw [h1, h3, negPartTrace_smul_nonneg hc hnegA, ← h2]

lemma traceDist_nonneg (ρ σ : DensityOp d) : 0 ≤ traceDist ρ σ := by
  rw [traceDist_eq_hockeyStick_one, hockeyStick_eq_posPartTrace]
  exact Finset.sum_nonneg fun _ _ ↦ le_max_right _ _

lemma traceDist_self (ρ : DensityOp d) : traceDist ρ ρ = 0 := by
  rw [traceDist_eq_hockeyStick_one, hockeyStick_eq_posPartTrace]
  have h0 : (0 : Matrix d d ℂ).IsHermitian := by simp [Matrix.IsHermitian]
  rw [posPartTrace_eq_of_eq _ h0 (by simp)]
  have hD : (0 : Matrix d d ℂ) = Matrix.diagonal (Complex.ofReal ∘ fun _ : d ↦ (0 : ℝ)) := by
    ext i j; simp [Matrix.diagonal_apply]
  have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ fun _ : d ↦ (0 : ℝ))).IsHermitian := by
    rw [← hD]; exact h0
  rw [posPartTrace_eq_of_eq h0 hD_herm hD]
  unfold posPartTrace
  rw [spectral_sum_diagonal (f := fun x : ℝ ↦ max x 0) (fun _ : d ↦ (0 : ℝ)) hD_herm (by simp)]
  simp

lemma traceDist_symm (ρ σ : DensityOp d) : traceDist ρ σ = traceDist σ ρ := by
  rw [traceDist_eq_half_traceNorm, traceDist_eq_half_traceNorm]
  congr 1
  unfold traceNorm
  have hmat : (ρ.mat - σ.mat)ᴴ * (ρ.mat - σ.mat) = (σ.mat - ρ.mat)ᴴ * (σ.mat - ρ.mat) := by
    have hneg : ρ.mat - σ.mat = -(σ.mat - ρ.mat) := (neg_sub _ _).symm
    rw [hneg, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  exact spectral_sum_eq_of_charpoly_mul_X_pow (f := Real.sqrt) (k := 0) (l := 0)
    (Matrix.posSemidef_conjTranspose_mul_self _).isHermitian
    (Matrix.posSemidef_conjTranspose_mul_self _).isHermitian
    (by rw [hmat]) Real.sqrt_zero

lemma traceDist_triangle (ρ τ σ : DensityOp d) :
    traceDist ρ σ ≤ traceDist ρ τ + traceDist τ σ := by
  rw [traceDist_eq_hockeyStick_one, traceDist_eq_hockeyStick_one, traceDist_eq_hockeyStick_one,
    hockeyStick_eq_posPartTrace, hockeyStick_eq_posPartTrace, hockeyStick_eq_posPartTrace]
  have hA := hockeyStick_isHermitian 1 ρ τ
  have hB := hockeyStick_isHermitian 1 τ σ
  have hsum : ρ.mat - (1 : ℂ) • σ.mat = (ρ.mat - (1 : ℂ) • τ.mat) + (τ.mat - (1 : ℂ) • σ.mat) := by
    simp only [one_smul]; abel
  rw [posPartTrace_eq_of_eq (hockeyStick_isHermitian 1 ρ σ) (hA.add hB) hsum]
  exact posPartTrace_add_le_aux hA hB

lemma traceDist_cptp_le {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ℰ : CPTPMap α β) (ρ σ : DensityOp α) :
    traceDist (ℰ.apply ρ) (ℰ.apply σ) ≤ traceDist ρ σ := by
  rw [traceDist_eq_hockeyStick_one, traceDist_eq_hockeyStick_one,
    hockeyStick_eq_posPartTrace, hockeyStick_eq_posPartTrace]
  have hneg1 : posPartTrace (hockeyStick_isHermitian 1 (ℰ.apply ρ) (ℰ.apply σ)) =
      negPartTrace ((ℰ.apply σ).isHermitian.sub (ℰ.apply ρ).isHermitian) := by
    have hBA := (ℰ.apply σ).isHermitian.sub (ℰ.apply ρ).isHermitian
    rw [negPartTrace_eq_posPartTrace_neg hBA (by rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, hBA.eq])]
    exact posPartTrace_eq_of_eq _ _ (by simp [neg_sub])
  have hneg2 : posPartTrace (hockeyStick_isHermitian 1 ρ σ) =
      negPartTrace (σ.isHermitian.sub ρ.isHermitian) := by
    have hBA := σ.isHermitian.sub ρ.isHermitian
    rw [negPartTrace_eq_posPartTrace_neg hBA (by rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, hBA.eq])]
    exact posPartTrace_eq_of_eq _ _ (by simp [neg_sub])
  rw [hneg1, hneg2]
  have hlin : ℰ.toLinearMap (σ.mat - ρ.mat) = (ℰ.apply σ).mat - (ℰ.apply ρ).mat := by
    rw [map_sub]; rfl
  have hB' : (ℰ.toLinearMap (σ.mat - ρ.mat)).IsHermitian :=
    hlin ▸ ((ℰ.apply σ).isHermitian.sub (ℰ.apply ρ).isHermitian)
  rw [negPartTrace_eq_of_eq ((ℰ.apply σ).isHermitian.sub (ℰ.apply ρ).isHermitian) hB' hlin.symm]
  exact negPartTrace_map_le ℰ.toLinearMap
    (fun X hX ↦ partialTrace₂Mat_posSemidef (by
      simpa [Matrix.star_eq_conjTranspose] using hX.mul_mul_conjTranspose_same ℰ.isom))
    (fun X _ ↦ by
      simp only [CPTPMap.toLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
      rw [partialTrace₂Mat_trace, Matrix.trace_mul_cycle, ℰ.isometry, Matrix.one_mul])
    (σ.isHermitian.sub ρ.isHermitian) hB'

lemma CQChannel.ChannelEquiv.traceDist_eq {d₁ d₂ : Type*}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    {W₁ : CQChannel d₁} {W₂ : CQChannel d₂} (h : W₁.ChannelEquiv W₂) :
    traceDist (W₁.out false) (W₁.out true) = traceDist (W₂.out false) (W₂.out true) := by
  rcases h with ⟨⟨ℰ₁, h₁⟩, ⟨ℰ₂, h₂⟩⟩
  refine le_antisymm ?_ ?_
  · have hle := traceDist_cptp_le ℰ₂ (W₂.out false) (W₂.out true)
    have hf : ℰ₂.apply (W₂.out false) = W₁.out false := DensityOp.ext (h₂ false)
    have ht : ℰ₂.apply (W₂.out true) = W₁.out true := DensityOp.ext (h₂ true)
    rwa [hf, ht] at hle
  · have hle := traceDist_cptp_le ℰ₁ (W₁.out false) (W₁.out true)
    have hf : ℰ₁.apply (W₁.out false) = W₂.out false := DensityOp.ext (h₁ false)
    have ht : ℰ₁.apply (W₁.out true) = W₂.out true := DensityOp.ext (h₁ true)
    rwa [hf, ht] at hle

lemma traceDist_transpose (ρ σ : DensityOp d) :
    traceDist ρ.transpose σ.transpose = traceDist ρ σ := by
  rw [traceDist_eq_hockeyStick_one, traceDist_eq_hockeyStick_one,
    hockeyStick_eq_posPartTrace, hockeyStick_eq_posPartTrace]
  have hcp : (ρ.transpose.mat - (1 : ℂ) • σ.transpose.mat).charpoly =
      (ρ.mat - (1 : ℂ) • σ.mat).charpoly := by
    have ht : ρ.transpose.mat - (1 : ℂ) • σ.transpose.mat = (ρ.mat - (1 : ℂ) • σ.mat)ᵀ := by
      simp [DensityOp.transpose, Matrix.transpose_sub]
    rw [ht, Matrix.charpoly_transpose]
  exact spectral_sum_eq_of_charpoly_mul_X_pow (f := fun x : ℝ ↦ max x 0) (k := 0) (l := 0)
    (hockeyStick_isHermitian 1 ρ.transpose σ.transpose)
    (hockeyStick_isHermitian 1 ρ σ)
    (by rw [hcp]) (by simp)

/-- Uniform block-diagonal state on `κ × α`: `|κ|⁻¹ ∑_k |k⟩⟨k| ⊗ ρ(k)`. -/
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
        · simp only [↓reduceIte, ← Finset.mul_sum]; ring
        · intro k' _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ k) h
      rw [hsum]
      refine Finset.sum_nonneg fun k _ ↦ ?_
      have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (ρ k).posSemidef).2 (fun i ↦ v (k, i))
      have hc : (0 : ℂ) ≤ ((Fintype.card κ : ℝ)⁻¹ : ℂ) :=
        Complex.zero_le_real.mpr (by positivity)
      simpa using mul_nonneg hc hq
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

/-- Trace distance between two uniform block-diagonal states equals the average of block trace distances. -/
lemma traceDist_uniformBlockDiag {κ α : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    [Fintype α] [DecidableEq α] (ρ σ : κ → DensityOp α) :
    traceDist (uniformBlockDiag ρ) (uniformBlockDiag σ) =
      (Fintype.card κ : ℝ)⁻¹ * ∑ k : κ, traceDist (ρ k) (σ k) := by
  have hΔ : ∀ k : κ, ((ρ k).mat - (σ k).mat).IsHermitian := fun k ↦ (ρ k).isHermitian.sub (σ k).isHermitian
  let U : Matrix (κ × α) (κ × α) ℂ :=
    Matrix.of fun (k₁, i₁) (k₂, i₂) ↦
      if k₁ = k₂ then ((hΔ k₁).eigenvectorUnitary : Matrix α α ℂ) i₁ i₂ else 0
  have hU_l : star U * U = 1 := by
    ext ⟨k₁, i₁⟩ ⟨k₂, i₂⟩
    simp only [U, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Fintype.sum_prod_type,
      Matrix.one_apply]
    by_cases hk : k₁ = k₂
    · subst hk
      rw [Finset.sum_eq_single k₁]
      · simp only [↓reduceIte, Prod.mk.injEq, true_and]
        have h := congr_fun (congr_fun (Unitary.coe_star_mul_self (hΔ k₁).eigenvectorUnitary) i₁) i₂
        simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h
      · intro k _ hne; apply Finset.sum_eq_zero; intro j _; simp [hne]
      · intro h; exact absurd (Finset.mem_univ k₁) h
    · have hne : (k₁, i₁) ≠ (k₂, i₂) := fun h ↦ hk (Prod.mk.inj h).1
      rw [if_neg hne]
      apply Finset.sum_eq_zero; intro k _; apply Finset.sum_eq_zero; intro j _
      by_cases h1 : k = k₁
      · subst h1; simp [hk]
      · simp [h1]
  let lam : (κ × α) → ℝ := fun p ↦ (Fintype.card κ : ℝ)⁻¹ * (hΔ p.1).eigenvalues p.2
  have hspec : (uniformBlockDiag ρ).mat - (1 : ℂ) • (uniformBlockDiag σ).mat =
      U * Matrix.diagonal (Complex.ofReal ∘ lam) * star U := by
    ext ⟨k₁, i₁⟩ ⟨k₂, i₂⟩
    simp only [uniformBlockDiag, one_smul, Matrix.sub_apply, Matrix.of_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, U, Matrix.star_apply, Matrix.of_apply, Fintype.sum_prod_type,
      Function.comp_apply, lam]
    by_cases hk : k₁ = k₂
    · subst hk
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single k₁]
      · simp only [↓reduceIte]
        have hsk := congr_fun (congr_fun (hΔ k₁).spectral_theorem i₁) i₂
        simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.mul_diagonal,
          Matrix.star_apply, Function.comp_apply] at hsk
        rw [← mul_sub, hsk, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        push_cast; ring
      · intro k _ hne; apply Finset.sum_eq_zero; intro j _; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ k₁) h
    · simp only [hk, ↓reduceIte, sub_self]
      symm
      apply Finset.sum_eq_zero; intro k _; apply Finset.sum_eq_zero; intro j _
      by_cases h1 : k₁ = k
      · subst h1; simp [Ne.symm hk]
      · simp [h1]
  have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext p; simp
  have hcp : ((uniformBlockDiag ρ).mat - (1 : ℂ) • (uniformBlockDiag σ).mat).charpoly =
      (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
    rw [hspec]
    have hsim := Matrix.charpoly_mul_comm (U * Matrix.diagonal (Complex.ofReal ∘ lam)) (star U)
    rw [hsim, ← Matrix.mul_assoc, hU_l, Matrix.one_mul]
  rw [traceDist_eq_hockeyStick_one, hockeyStick_eq_posPartTrace]
  unfold posPartTrace
  have hsum := spectral_sum_eq_of_charpoly_mul_X_pow (f := fun x : ℝ ↦ max x 0) (k := 0) (l := 0)
    (hockeyStick_isHermitian 1 (uniformBlockDiag ρ) (uniformBlockDiag σ)) hD_herm
    (by rw [hcp]) (by simp)
  rw [hsum, spectral_sum_diagonal (f := fun x : ℝ ↦ max x 0) lam hD_herm (by simp),
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _
  have hpos : (0 : ℝ) ≤ (Fintype.card κ : ℝ)⁻¹ := by positivity
  simp_rw [lam, ← mul_max_of_nonneg _ _ hpos, mul_zero, ← Finset.mul_sum]
  congr 1
  rw [traceDist_eq_hockeyStick_one, hockeyStick_eq_posPartTrace]
  exact (posPartTrace_eq_of_eq (hockeyStick_isHermitian 1 (ρ k) (σ k)) (hΔ k) (by simp)).symm

/-- Convexity of trace distance over finite uniform averages. -/
lemma traceDist_uniformAvg_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype α] [DecidableEq α]
    (ρ σ : ι → DensityOp α) (ρAvg σAvg : DensityOp α)
    (hρ : ρAvg.mat = ((Fintype.card ι : ℂ)⁻¹) • ∑ i : ι, (ρ i).mat)
    (hσ : σAvg.mat = ((Fintype.card ι : ℂ)⁻¹) • ∑ i : ι, (σ i).mat) :
    traceDist ρAvg σAvg ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, traceDist (ρ i) (σ i) := by
  let ℰ : CPTPMap (ι × α) α :=
    { env := ι
      fintypeEnv := inferInstance
      decEqEnv := inferInstance
      isom := Matrix.of fun (a, k) (k', a') ↦ if k = k' ∧ a = a' then 1 else 0
      isometry := by
        ext ⟨k₁, a₁⟩ ⟨k₂, a₂⟩
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Fintype.sum_prod_type, Matrix.one_apply]
        rw [Finset.sum_eq_single a₁]
        · rw [Finset.sum_eq_single k₁]
          · by_cases h : (k₁, a₁) = (k₂, a₂)
            · rcases Prod.mk.inj h with ⟨rfl, rfl⟩; simp
            · simp only [h, ↓reduceIte, and_self, one_mul]
              have hne : ¬ (k₁ = k₂ ∧ a₁ = a₂) := fun ⟨hk, ha⟩ ↦ h (by rw [hk, ha])
              simp [hne]
          · intro k _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ k₁) h
        · intro a _ hne; apply Finset.sum_eq_zero; intro k _; simp [hne]
        · intro h; exact absurd (Finset.mem_univ a₁) h }
  have happly : ∀ τ : ι → DensityOp α,
      (ℰ.apply (uniformBlockDiag τ)).mat = ((Fintype.card ι : ℂ)⁻¹) • ∑ i : ι, (τ i).mat := by
    intro τ
    ext a₁ a₂
    simp only [ℰ, CPTPMap.apply, CPTPMap.toLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      partialTrace₂Mat, uniformBlockDiag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single a₂]
      · rw [Finset.sum_eq_single k]
        · rw [Finset.sum_eq_single a₁]
          · simp
          · intro a _ hne; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ a₁) h
        · intro k' _ hne; apply Finset.sum_eq_zero; intro a _; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ k) h
      · intro a _ hne; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ a₂) h
    · intro k' _ hne; apply Finset.sum_eq_zero; intro a _; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ k) h
  have h1 : ℰ.apply (uniformBlockDiag ρ) = ρAvg := DensityOp.ext ((happly ρ).trans hρ.symm)
  have h2 : ℰ.apply (uniformBlockDiag σ) = σAvg := DensityOp.ext ((happly σ).trans hσ.symm)
  rw [← h1, ← h2, ← traceDist_uniformBlockDiag ρ σ]
  exact traceDist_cptp_le ℰ (uniformBlockDiag ρ) (uniformBlockDiag σ)

lemma traceDist_symmetrize (W : CQChannel d) :
    traceDist (W.symmetrize.out false) (W.symmetrize.out true) =
      traceDist (W.out false) (W.out true) := by
  have h0 : W.symmetrize.out false = uniformBlockDiag (fun b : Bool ↦ W.out b) := by
    apply DensityOp.ext
    ext ⟨b₁, i₁⟩ ⟨b₂, i₂⟩
    simp only [CQChannel.symmetrize, uniformBlockDiag, DensityOp.midpoint, DensityOp.mix,
      DensityOp.tensor, CQChannel.ketBraBool, Matrix.add_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, Matrix.of_apply, Complex.real_smul, Fintype.card_bool,
      Nat.cast_ofNat]
    cases b₁ <;> cases b₂ <;> simp <;> ring
  have h1 : W.symmetrize.out true = uniformBlockDiag (fun b : Bool ↦ W.out (!b)) := by
    apply DensityOp.ext
    ext ⟨b₁, i₁⟩ ⟨b₂, i₂⟩
    simp only [CQChannel.symmetrize, uniformBlockDiag, DensityOp.midpoint, DensityOp.mix,
      DensityOp.tensor, CQChannel.ketBraBool, Matrix.add_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, Matrix.of_apply, Complex.real_smul, Fintype.card_bool,
      Nat.cast_ofNat]
    cases b₁ <;> cases b₂ <;> simp <;> ring
  rw [h0, h1, traceDist_uniformBlockDiag, Fintype.sum_bool, Fintype.card_bool]
  simp only [Nat.cast_ofNat, Bool.not_false, Bool.not_true]
  rw [traceDist_symm (W.out true) (W.out false)]
  ring

end TraceDistProps

section ExactDuality

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **Exact Channel-Duality Identity**: For every binary c-q channel `V`,
the trace distance between the outputs of its dual channel `V⊥` equals the Bhattacharyya /
fidelity parameter of `V`: `T(V⊥(0), V⊥(1)) = Z(V)`. -/
theorem traceDist_dual_eq_fidelityParam (V : CQChannel d) :
    traceDist (V.dual.out false) (V.dual.out true) = V.fidelityParam := by
  set ρ₀ := V.out false
  set ρ₁ := V.out true
  have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
  have hΔ_entry : ∀ a₁ a₂ : Bool, ∀ i₁ i₂ : d,
      ((V.dual.out false).mat - (V.dual.out true).mat) (a₁, i₁) (a₂, i₂) =
        if a₁ = a₂ then 0
        else if a₁ = false then (ρ₀.sqrtMat * ρ₁.sqrtMat) i₁ i₂
        else (ρ₁.sqrtMat * ρ₀.sqrtMat) i₁ i₂ := by
    intro a₁ a₂ i₁ i₂
    have hZstar : star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) =
        (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) := by
      ext ⟨b₁, x₁⟩ ⟨b₂, x₂⟩
      by_cases h : (b₁, x₁) = (b₂, x₂)
      · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
        cases b₁ <;> simp [pauliZTensorI, Matrix.star_apply, Matrix.diagonal_apply]
      · simp [pauliZTensorI, Matrix.star_apply, Matrix.diagonal_apply, h, Ne.symm h]
    have hG_entry : ∀ b₁ b₂ : Bool, ∀ x₁ x₂ : d,
        (gramState ρ₀ ρ₁).mat (b₁, x₁) (b₂, x₂) =
          (1 / 2 : ℂ) * ((if b₁ = false then ρ₀.sqrtMat else ρ₁.sqrtMat) *
            (if b₂ = false then ρ₀.sqrtMat else ρ₁.sqrtMat)) x₁ x₂ := by
      intro b₁ b₂ x₁ x₂
      simp only [gramState, gramFactor, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply, star_mul', hstar2, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      have hρ₀ : star (ρ₀.sqrtMat x₂ k) = ρ₀.sqrtMat k x₂ := by
        have := congr_fun (congr_fun ρ₀.sqrtMat_isHermitian.eq k) x₂
        simpa [Matrix.conjTranspose_apply] using this
      have hρ₁ : star (ρ₁.sqrtMat x₂ k) = ρ₁.sqrtMat k x₂ := by
        have := congr_fun (congr_fun ρ₁.sqrtMat_isHermitian.eq k) x₂
        simpa [Matrix.conjTranspose_apply] using this
      cases b₁ <;> cases b₂ <;> simp only [↓reduceIte, Bool.true_eq_false, hρ₀, hρ₁] <;>
        (calc ((Real.sqrt 2 : ℂ)⁻¹ * _) * ((Real.sqrt 2 : ℂ)⁻¹ * _)
            = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (_ * _) := by ring
          _ = (1 / 2 : ℂ) * (_ * _) := by rw [hmul2])
    simp only [CQChannel.dual, DensityOp.conjUnitary, Matrix.sub_apply, hZstar]
    simp only [pauliZTensorI, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hG_entry a₁ a₂ i₁ i₂]
    cases a₁ <;> cases a₂ <;> simp <;> ring
  set Δ := (V.dual.out false).mat - (V.dual.out true).mat
  have hΔ_sq : Δᴴ * Δ = Matrix.of fun (a₁, i₁) (a₂, i₂) ↦
      if a₁ = a₂ then
        if a₁ = false then (ρ₀.sqrtMat * ρ₁.mat * ρ₀.sqrtMat) i₁ i₂
        else (ρ₁.sqrtMat * ρ₀.mat * ρ₁.sqrtMat) i₁ i₂
      else 0 := by
    have hΔ_herm : Δ.IsHermitian := (V.dual.out false).isHermitian.sub (V.dual.out true).isHermitian
    rw [hΔ_herm.eq]
    ext ⟨a₁, i₁⟩ ⟨a₂, i₂⟩
    simp only [Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_bool]
    simp_rw [hΔ_entry]
    cases a₁ <;> cases a₂ <;> simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true,
      mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
    · have h1 : (ρ₀.sqrtMat * ρ₁.sqrtMat) * (ρ₁.sqrtMat * ρ₀.sqrtMat) =
          ρ₀.sqrtMat * ρ₁.mat * ρ₀.sqrtMat := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc ρ₁.sqrtMat ρ₁.sqrtMat, ρ₁.sqrtMat_mul_self]
      rw [← h1, Matrix.mul_apply]
    · have h1 : (ρ₁.sqrtMat * ρ₀.sqrtMat) * (ρ₀.sqrtMat * ρ₁.sqrtMat) =
          ρ₁.sqrtMat * ρ₀.mat * ρ₁.sqrtMat := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc ρ₀.sqrtMat ρ₀.sqrtMat, ρ₀.sqrtMat_mul_self]
      rw [← h1, Matrix.mul_apply]
  have hM₀ := posSemidef_sqrt_mul_sqrt ρ₀ ρ₁
  have hM₁ := posSemidef_sqrt_mul_sqrt ρ₁ ρ₀
  let e : Bool × d ≃ d ⊕ d :=
    { toFun := fun p ↦ if p.1 = false then Sum.inl p.2 else Sum.inr p.2
      invFun := fun s ↦ match s with | Sum.inl x => (false, x) | Sum.inr x => (true, x)
      left_inv := fun ⟨b, x⟩ ↦ by cases b <;> rfl
      right_inv := fun s ↦ by cases s <;> rfl }
  have hreidx : (Δᴴ * Δ).submatrix e.symm e.symm =
      Matrix.fromBlocks (ρ₀.sqrtMat * ρ₁.mat * ρ₀.sqrtMat) 0 0 (ρ₁.sqrtMat * ρ₀.mat * ρ₁.sqrtMat) := by
    rw [hΔ_sq]
    ext s₁ s₂
    cases s₁ <;> cases s₂ <;> simp [e, Matrix.fromBlocks]
  have hcp_block : (Δᴴ * Δ).charpoly =
      (ρ₀.sqrtMat * ρ₁.mat * ρ₀.sqrtMat).charpoly * (ρ₁.sqrtMat * ρ₀.mat * ρ₁.sqrtMat).charpoly := by
    have h1 := Matrix.charpoly_reindex e (Δᴴ * Δ)
    rw [← h1]
    change ((Δᴴ * Δ).submatrix e.symm e.symm).charpoly = _
    rw [hreidx, Matrix.charpoly_fromBlocks_zero₁₂]
  have hcp_eq : (ρ₁.sqrtMat * ρ₀.mat * ρ₁.sqrtMat).charpoly =
      (ρ₀.sqrtMat * ρ₁.mat * ρ₀.sqrtMat).charpoly := by
    have h1 := Matrix.charpoly_mul_comm (ρ₁.sqrtMat * ρ₀.sqrtMat) (ρ₀.sqrtMat * ρ₁.sqrtMat)
    have hL : (ρ₁.sqrtMat * ρ₀.sqrtMat) * (ρ₀.sqrtMat * ρ₁.sqrtMat) = ρ₁.sqrtMat * ρ₀.mat * ρ₁.sqrtMat := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc ρ₀.sqrtMat ρ₀.sqrtMat, ρ₀.sqrtMat_mul_self]
    have hR : (ρ₀.sqrtMat * ρ₁.sqrtMat) * (ρ₁.sqrtMat * ρ₀.sqrtMat) = ρ₀.sqrtMat * ρ₁.mat * ρ₀.sqrtMat := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc ρ₁.sqrtMat ρ₁.sqrtMat, ρ₁.sqrtMat_mul_self]
    rw [← hL, ← hR]; exact h1
  let D : Matrix (Bool × d) (Bool × d) ℂ :=
    Matrix.diagonal (Complex.ofReal ∘ fun p : Bool × d ↦ hM₀.isHermitian.eigenvalues p.2)
  have hD_herm : D.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext p; simp
  have hcp_D : (Δᴴ * Δ).charpoly = D.charpoly := by
    rw [hcp_block, hcp_eq]
    have hcp_M₀ : (ρ₀.sqrtMat * ρ₁.mat * ρ₀.sqrtMat).charpoly =
        ∏ i : d, (Polynomial.X - Polynomial.C (hM₀.isHermitian.eigenvalues i : ℂ)) := by
      set U : Matrix d d ℂ := (hM₀.isHermitian.eigenvectorUnitary : Matrix d d ℂ)
      have hspec : ρ₀.sqrtMat * ρ₁.mat * ρ₀.sqrtMat =
          U * Matrix.diagonal (Complex.ofReal ∘ hM₀.isHermitian.eigenvalues) * star U := by
        simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM₀.isHermitian.spectral_theorem
      rw [hspec]
      have hsim := Matrix.charpoly_mul_comm (U * Matrix.diagonal (Complex.ofReal ∘ hM₀.isHermitian.eigenvalues)) (star U)
      rw [hsim, ← Matrix.mul_assoc, Unitary.coe_star_mul_self hM₀.isHermitian.eigenvectorUnitary,
        Matrix.one_mul, charpoly_diagonal_complex]
    rw [hcp_M₀, charpoly_diagonal_complex, Fintype.prod_prod_type, Fintype.prod_bool]
  rw [traceDist_eq_half_traceNorm]
  unfold traceNorm CQChannel.fidelityParam rootFidelity
  have hsum := spectral_sum_eq_of_charpoly_mul_X_pow (f := Real.sqrt) (k := 0) (l := 0)
    (Matrix.posSemidef_conjTranspose_mul_self Δ).isHermitian hD_herm
    (by rw [hcp_D]) Real.sqrt_zero
  rw [hsum, spectral_sum_diagonal (f := Real.sqrt) (fun p : Bool × d ↦ hM₀.isHermitian.eigenvalues p.2)
    hD_herm Real.sqrt_zero, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

private lemma checkCombine_transpose {α₁ α₂ : Type*} [Fintype α₁] [DecidableEq α₁]
    [Fintype α₂] [DecidableEq α₂] (W₁ : CQChannel α₁) (W₂ : CQChannel α₂) :
    (W₁.transpose.checkCombine W₂.transpose) = (W₁.checkCombine W₂).transpose := by
  cases W₁; cases W₂
  congr 1; funext b; apply DensityOp.ext
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [CQChannel.checkCombine, CQChannel.transpose, DensityOp.transpose,
    DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, Matrix.kroneckerMap_apply]

private lemma varCombine_transpose {α₁ α₂ : Type*} [Fintype α₁] [DecidableEq α₁]
    [Fintype α₂] [DecidableEq α₂] (W₁ : CQChannel α₁) (W₂ : CQChannel α₂) :
    (W₁.transpose.varCombine W₂.transpose) = (W₁.varCombine W₂).transpose := by
  cases W₁; cases W₂
  congr 1; funext b; apply DensityOp.ext
  ext ⟨v₁, i₁, i₂⟩ ⟨v₂, j₁, j₂⟩
  simp [CQChannel.varCombine, CQChannel.transpose, DensityOp.transpose,
    DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, CQChannel.ketBraBool,
    Matrix.kroneckerMap_apply]
  cases v₁ <;> cases v₂ <;> simp

private lemma polarChannelTree_transpose_traceDist {α : Type} [Fintype α] [DecidableEq α]
    (W : CQChannel α) : ∀ (n : ℕ) (b : Fin n → Bool),
    traceDist ((polarChannelTree W.transpose n b).out false)
      ((polarChannelTree W.transpose n b).out true) =
    traceDist ((polarChannelTree W n b).out false)
      ((polarChannelTree W n b).out true) := by
  have heq : ∀ (n : ℕ) (b : Fin n → Bool),
      polarChannelTree W.transpose n b = (polarChannelTree W n b).transpose := by
    intro n
    induction n with
    | zero => intro b; rfl
    | succ k ih =>
      intro b
      simp only [polarChannelTree]
      cases b ⟨k, Nat.lt_succ_self k⟩
      · simp only [ih, checkCombine_transpose]; rfl
      · simp only [ih, varCombine_transpose]; rfl
  intro n b
  rw [heq n b]
  exact traceDist_transpose _ _

private lemma polarChannelTree_symmetrize_traceDist {α : Type} [Fintype α] [DecidableEq α]
    (W : CQChannel α) (n : ℕ) (b : Fin n → Bool) :
    traceDist ((polarChannelTree W.symmetrize n b).out false)
      ((polarChannelTree W.symmetrize n b).out true) =
    traceDist ((polarChannelTree W n b).out false)
      ((polarChannelTree W n b).out true) := by
  have heq : ∀ (m : ℕ) (p : Fin m → Bool),
      (polarChannelTree W.symmetrize m p).ChannelEquiv (polarChannelTree W m p).symmetrize := by
    intro m
    induction m with
    | zero => intro p; exact CQChannel.ChannelEquiv.refl _
    | succ k ih =>
      intro p
      simp only [polarChannelTree]
      have hih := ih (fun i ↦ p i.castSucc)
      cases p ⟨k, Nat.lt_succ_self k⟩
      · exact (hih.checkCombine hih).trans (symmetrize_minusChannel_channelEquiv _)
      · exact (hih.varCombine hih).trans (symmetrize_plusChannel_channelEquiv _)
  rw [(heq n b).traceDist_eq, traceDist_symmetrize]

/-- **Complementary–Phase Polarization Duality for Synthetic Channels**:
For every qubit-input CPTP map `𝒩`, depth `n`, and index `i : Fin (2^n)`,
the trace distance of Eve's `i`-th synthetic channel `(W_E)_N^{(i)}` equals the
Bhattacharyya/fidelity parameter of the dual-indexed phase synthetic channel `(W_P)_N^{(i⊥)}`. -/
theorem synthChannel_complementary_traceDist_eq_phase_fidelityParam
    {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap.{0} Bool d) (n : ℕ) (i : Fin (2 ^ n)) :
    traceDist ((synthChannel (ampChannel 𝒩.complementary) n i).out false)
      ((synthChannel (ampChannel 𝒩.complementary) n i).out true) =
    (synthChannel (phaseChannel 𝒩) n (dualIndex n i)).fidelityParam := by
  set b := bitPath n i
  have h1 : traceDist ((synthChannel (ampChannel 𝒩.complementary) n i).out false)
      ((synthChannel (ampChannel 𝒩.complementary) n i).out true) =
      traceDist ((polarChannelTree (ampChannel 𝒩.complementary) n b).out false)
        ((polarChannelTree (ampChannel 𝒩.complementary) n b).out true) :=
    (synthChannel_reindex_polarChannelTree (ampChannel 𝒩.complementary) n i).toChannelEquiv.traceDist_eq
  have h2 : traceDist ((polarChannelTree (ampChannel 𝒩.complementary) n b).out false)
      ((polarChannelTree (ampChannel 𝒩.complementary) n b).out true) =
      traceDist ((polarChannelTree (phaseChannel 𝒩).dual n b).out false)
        ((polarChannelTree (phaseChannel 𝒩).dual n b).out true) := by
    rw [← polarChannelTree_transpose_traceDist (ampChannel 𝒩.complementary) n b,
      ← polarChannelTree_symmetrize_traceDist (ampChannel 𝒩.complementary).transpose n b]
    exact ((phaseChannel_dual_channelEquiv 𝒩).polarChannelTree n b).traceDist_eq.symm
  have h3 : traceDist ((polarChannelTree (phaseChannel 𝒩).dual n b).out false)
      ((polarChannelTree (phaseChannel 𝒩).dual n b).out true) =
      traceDist (((polarChannelTree (phaseChannel 𝒩) n (fun k ↦ !(b k))).dual).out false)
        (((polarChannelTree (phaseChannel 𝒩) n (fun k ↦ !(b k))).dual).out true) := by
    have hnot : (fun k ↦ !(!(b k))) = b := funext fun k ↦ Bool.not_not _
    have heq := polarChannelTree_dual_complement_channelEquiv (phaseChannel 𝒩) n (fun k ↦ !(b k))
    rw [hnot] at heq
    exact heq.traceDist_eq.symm
  have h4 : traceDist (((polarChannelTree (phaseChannel 𝒩) n (fun k ↦ !(b k))).dual).out false)
      (((polarChannelTree (phaseChannel 𝒩) n (fun k ↦ !(b k))).dual).out true) =
      (polarChannelTree (phaseChannel 𝒩) n (fun k ↦ !(b k))).fidelityParam :=
    traceDist_dual_eq_fidelityParam _
  have h5 : (synthChannel (phaseChannel 𝒩) n (dualIndex n i)).fidelityParam =
      (polarChannelTree (phaseChannel 𝒩) n (fun k ↦ !(b k))).fidelityParam := by
    rw [synthChannel_fidelityParam_eq]
    simp only [dualIndex, Equiv.apply_symm_apply, b]
  rw [h1, h2, h3, h4, h5]

end ExactDuality

section OperationalWiretap

variable {d : Type} [Fintype d] [DecidableEq d]

/-- Assemble an `N`-bit Arikan input word from four disjoint index registers:
message `m` on `infoSet`, local randomness `r` on `randSet`, pre-shared secret key `k` on
`assistSet`, and public deterministic frozen bits `uF` on the remaining indices. -/
def wiretapWord {N : ℕ} (infoSet randSet assistSet : Finset (Fin N))
    (uF : Fin N → Bool) (m : infoSet → Bool) (r : randSet → Bool) (k : assistSet → Bool) :
    Fin N → Bool :=
  fun i ↦
    if h1 : i ∈ infoSet then m ⟨i, h1⟩
    else if h2 : i ∈ randSet then r ⟨i, h2⟩
    else if h3 : i ∈ assistSet then k ⟨i, h3⟩
    else uF i

/-- Bob's effective frozen-bit vector given the public frozen assignment `uF` and pre-shared
secret key `k` on `assistSet`. -/
def bobEffectiveFrozen {N : ℕ} (assistSet : Finset (Fin N))
    (uF : Fin N → Bool) (k : assistSet → Bool) : Fin N → Bool :=
  fun i ↦ if h : i ∈ assistSet then k ⟨i, h⟩ else uF i

/-- For any fixed subset `S ⊆ Fin (2^n)` and assignment `u : Fin (2^n) → Bool`, the state
obtained by fixing the coordinates of `v` on `S` to match `u` and averaging uniformly over
all remaining coordinates `Sᶜ`, sent through `W^⊗N ∘ arikanTransform n`. -/
noncomputable def fixedSubsetAvgState {α : Type*} [Fintype α] [DecidableEq α]
    (W : CQChannel α) (n : ℕ) (S : Finset (Fin (2 ^ n))) (u : Fin (2 ^ n) → Bool) :
    DensityOp (Fin (2 ^ n) → α) where
  mat := ((2 : ℂ) ^ (2 ^ n - S.card))⁻¹ •
    ∑ v ∈ Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ S, v j = u j),
      (productState W n (arikanTransform n v)).mat
  posSemidef := by
    have hc : (0 : ℝ) ≤ ((2 : ℝ) ^ (2 ^ n - S.card))⁻¹ := by positivity
    have hsum : (∑ v ∈ Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ S, v j = u j),
        (productState W n (arikanTransform n v)).mat).PosSemidef :=
      Finset.sum_induction _ (fun M : Matrix _ _ ℂ ↦ M.PosSemidef)
        (fun _ _ ha hb ↦ ha.add hb) Matrix.PosSemidef.zero
        (fun v _ ↦ (productState W n (arikanTransform n v)).posSemidef)
    have hsm : ((2 : ℂ) ^ (2 ^ n - S.card))⁻¹ •
        ∑ v ∈ Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ S, v j = u j),
          (productState W n (arikanTransform n v)).mat =
        (((2 : ℝ) ^ (2 ^ n - S.card))⁻¹) •
        ∑ v ∈ Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ S, v j = u j),
          (productState W n (arikanTransform n v)).mat := by
      ext i j; simp [Complex.real_smul]
    rw [hsm]; exact hsum.smul hc
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_sum]
    have htr : ∀ v : Fin (2 ^ n) → Bool, (productState W n (arikanTransform n v)).mat.trace = 1 :=
      fun v ↦ (productState W n (arikanTransform n v)).trace_one
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
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
    rw [hcard]
    push_cast
    exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))

/-- Eve's conditional output state given message `m` and public frozen bits `uF`, averaged
uniformly over Alice's local randomness `r` and pre-shared secret key `k`. -/
noncomputable def wiretapEveCondState (𝒩 : CPTPMap.{0} Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (uF : Fin (2 ^ n) → Bool) (m : infoSet → Bool) :
    DensityOp (Fin (2 ^ n) → 𝒩.env) :=
  fixedSubsetAvgState (ampChannel 𝒩.complementary) n (randSet ∪ assistSet)ᶜ
    (fun i ↦ if h : i ∈ infoSet then m ⟨i, h⟩ else uF i)

/-- Eve's joint classical-quantum message-eavesdropper state `ρ_{ME}` under a uniform message
`M` and fixed public frozen assignment `uF`. -/
noncomputable def wiretapEveJointState (𝒩 : CPTPMap.{0} Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (uF : Fin (2 ^ n) → Bool) :
    DensityOp ((infoSet → Bool) × (Fin (2 ^ n) → 𝒩.env)) :=
  uniformBlockDiag (fun m ↦ wiretapEveCondState 𝒩 n infoSet randSet assistSet uF m)

/-- Eve's ideal decoupled state `π_M ⊗ ρ_E`, where `ρ_E` is the uniform average channel output
independent of both the message `M` and the public frozen bits `uF`. -/
noncomputable def wiretapIdealEveState (𝒩 : CPTPMap.{0} Bool d) (n : ℕ)
    (infoSet : Finset (Fin (2 ^ n))) :
    DensityOp ((infoSet → Bool) × (Fin (2 ^ n) → 𝒩.env)) :=
  uniformBlockDiag (fun _ : infoSet → Bool ↦
    fixedSubsetAvgState (ampChannel 𝒩.complementary) n ∅ (fun _ ↦ false))

/-- Operational secrecy error `T(ρ_{ME}, π_M ⊗ ρ_E)` for a wiretap polar code with public
frozen assignment `uF`. -/
noncomputable def wiretapSecrecyError (𝒩 : CPTPMap.{0} Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (uF : Fin (2 ^ n) → Bool) : ℝ :=
  traceDist (wiretapEveJointState 𝒩 n infoSet randSet assistSet uF)
    (wiretapIdealEveState 𝒩 n infoSet)

/-- Bob's operational average decoding error (averaged over uniform pre-shared key `k`, message
`m`, and randomness `r`) when using the Wilde–Guha QSC decoder on `infoSet ∪ randSet`. -/
noncomputable def wiretapBobError (𝒩 : CPTPMap.{0} Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (uF : Fin (2 ^ n) → Bool) : ℝ :=
  ((2 : ℝ) ^ assistSet.card)⁻¹ *
    ∑ k : assistSet → Bool,
      (qscPolarCode (ampChannel 𝒩) n (infoSet ∪ randSet)
        (bobEffectiveFrozen assistSet uF k)).avgBlockError

/-- Prefix restriction `S ∩ {0, ..., k - 1}`. -/
private def prefixSubset {N : ℕ} (S : Finset (Fin N)) (k : ℕ) : Finset (Fin N) :=
  S.filter (fun j ↦ j.val < k)

private lemma prefixSubset_zero {N : ℕ} (S : Finset (Fin N)) : prefixSubset S 0 = ∅ := by
  ext j; simp [prefixSubset]

private lemma prefixSubset_full {N : ℕ} (S : Finset (Fin N)) : prefixSubset S N = S := by
  ext j; simp [prefixSubset, j.isLt]

private lemma prefixSubset_succ_of_notMem {N : ℕ} (S : Finset (Fin N)) {k : ℕ} (hk : k < N)
    (hnot : (⟨k, hk⟩ : Fin N) ∉ S) :
    prefixSubset S (k + 1) = prefixSubset S k := by
  ext j
  simp only [prefixSubset, Finset.mem_filter, Nat.lt_succ_iff]
  constructor
  · rintro ⟨hjS, hle⟩
    refine ⟨hjS, lt_of_le_of_ne hle fun heq ↦ hnot ?_⟩
    convert hjS; exact Fin.ext heq.symm
  · rintro ⟨hjS, hlt⟩; exact ⟨hjS, le_of_lt hlt⟩

private lemma prefixSubset_succ_of_mem {N : ℕ} (S : Finset (Fin N)) {k : ℕ} (hk : k < N)
    (hmem : (⟨k, hk⟩ : Fin N) ∈ S) :
    prefixSubset S (k + 1) = insert ⟨k, hk⟩ (prefixSubset S k) := by
  ext j
  simp only [prefixSubset, Finset.mem_filter, Finset.mem_insert, Nat.lt_succ_iff]
  constructor
  · rintro ⟨hjS, hle⟩
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact Or.inl (Fin.ext heq)
    · exact Or.inr ⟨hjS, hlt⟩
  · rintro (rfl | ⟨hjS, hlt⟩)
    · exact ⟨hmem, le_rfl⟩
    · exact ⟨hjS, le_of_lt hlt⟩

/-- **Telescoping Decoupling Lemma**: For any subset `T ⊆ Fin (2^n)`, the uniform average over
`u : Fin (2^n) → Bool` of `T(fixedSubsetAvgState W n T u, fixedSubsetAvgState W n ∅ u)` is
bounded by `∑ i ∈ T, (1/2) * T((synthChannel W n i).out false, (synthChannel W n i).out true)`. -/
theorem avg_fixedSubset_decoupling_le {α : Type*} [Fintype α] [DecidableEq α]
    (W : CQChannel α) (n : ℕ) (T : Finset (Fin (2 ^ n))) :
    ((2 : ℝ) ^ (2 ^ n))⁻¹ *
      ∑ u : Fin (2 ^ n) → Bool,
        traceDist (fixedSubsetAvgState W n T u) (fixedSubsetAvgState W n ∅ u) ≤
      ∑ i ∈ T, (1 / 2) * traceDist ((synthChannel W n i).out false) ((synthChannel W n i).out true) := by
  have htele : ∀ u : Fin (2 ^ n) → Bool,
      traceDist (fixedSubsetAvgState W n T u) (fixedSubsetAvgState W n ∅ u) ≤
        ∑ k ∈ Finset.range (2 ^ n),
          traceDist (fixedSubsetAvgState W n (prefixSubset T (k + 1)) u)
            (fixedSubsetAvgState W n (prefixSubset T k) u) := by
    intro u
    suffices h : ∀ m : ℕ, m ≤ 2 ^ n →
        traceDist (fixedSubsetAvgState W n (prefixSubset T m) u)
          (fixedSubsetAvgState W n (prefixSubset T 0) u) ≤
          ∑ k ∈ Finset.range m,
            traceDist (fixedSubsetAvgState W n (prefixSubset T (k + 1)) u)
              (fixedSubsetAvgState W n (prefixSubset T k) u) by
      simpa [prefixSubset_zero, prefixSubset_full] using h (2 ^ n) le_rfl
    intro m
    induction m with
    | zero => intro _; simp [traceDist_self]
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ]
      have h1 := traceDist_triangle
        (fixedSubsetAvgState W n (prefixSubset T (k + 1)) u)
        (fixedSubsetAvgState W n (prefixSubset T k) u)
        (fixedSubsetAvgState W n (prefixSubset T 0) u)
      linarith [ih (Nat.le_of_succ_le hk)]
  have havg_tele : ((2 : ℝ) ^ (2 ^ n))⁻¹ *
      ∑ u : Fin (2 ^ n) → Bool,
        traceDist (fixedSubsetAvgState W n T u) (fixedSubsetAvgState W n ∅ u) ≤
      ∑ k ∈ Finset.range (2 ^ n),
        ((2 : ℝ) ^ (2 ^ n))⁻¹ *
          ∑ u : Fin (2 ^ n) → Bool,
            traceDist (fixedSubsetAvgState W n (prefixSubset T (k + 1)) u)
              (fixedSubsetAvgState W n (prefixSubset T k) u) := by
    calc _ ≤ ((2 : ℝ) ^ (2 ^ n))⁻¹ *
            ∑ u : Fin (2 ^ n) → Bool, ∑ k ∈ Finset.range (2 ^ n),
              traceDist (fixedSubsetAvgState W n (prefixSubset T (k + 1)) u)
                (fixedSubsetAvgState W n (prefixSubset T k) u) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ ↦ htele u) (by positivity)
      _ = _ := by rw [Finset.sum_comm, Finset.mul_sum]
  have hstep : ∀ k (hk : k < 2 ^ n),
      ((2 : ℝ) ^ (2 ^ n))⁻¹ *
        ∑ u : Fin (2 ^ n) → Bool,
          traceDist (fixedSubsetAvgState W n (prefixSubset T (k + 1)) u)
            (fixedSubsetAvgState W n (prefixSubset T k) u) ≤
      if (⟨k, hk⟩ : Fin (2 ^ n)) ∈ T then
        (1 / 2) * traceDist ((synthChannel W n ⟨k, hk⟩).out false)
          ((synthChannel W n ⟨k, hk⟩).out true)
      else 0 := by
    intro k hk
    set i : Fin (2 ^ n) := ⟨k, hk⟩
    by_cases hiT : i ∈ T
    · rw [if_pos hiT]
      set S := prefixSubset T k
      have hiS : i ∉ S := by simp [S, prefixSubset, i]
      have hS_succ : prefixSubset T (k + 1) = insert i S := prefixSubset_succ_of_mem T hk hiT
      have hhalf_step : ∀ u : Fin (2 ^ n) → Bool,
          traceDist (fixedSubsetAvgState W n (insert i S) u) (fixedSubsetAvgState W n S u) =
            (1 / 2) * traceDist
              (fixedSubsetAvgState W n (insert i S) (Function.update u i false))
              (fixedSubsetAvgState W n (insert i S) (Function.update u i true)) := by
        intro u
        have hmid : (fixedSubsetAvgState W n S u).mat =
            ((1 / 2 : ℝ) : ℂ) • (fixedSubsetAvgState W n (insert i S) (Function.update u i false)).mat +
            ((1 / 2 : ℝ) : ℂ) • (fixedSubsetAvgState W n (insert i S) (Function.update u i true)).mat := by
          simp only [fixedSubsetAvgState]
          have hcard : (insert i S).card = S.card + 1 := Finset.card_insert_of_notMem hiS
          have hle : S.card + 1 ≤ 2 ^ n := by
            have := Finset.card_le_univ (insert i S); rwa [Fintype.card_fin, hcard] at this
          have hsub_eq : 2 ^ n - S.card = (2 ^ n - (insert i S).card) + 1 := by omega
          have hfilt : Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ S, v j = u j) =
              Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ insert i S, v j = Function.update u i false j) ∪
              Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ insert i S, v j = Function.update u i true j) := by
            ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
              Finset.mem_insert, forall_eq_or_imp, Function.update_self]
            constructor
            · intro hv
              cases hvi : v i
              · exact Or.inl ⟨rfl, fun j hj ↦ by
                  have hne : j ≠ i := fun h ↦ hiS (h ▸ hj)
                  simp [Function.update_of_ne hne, hv j hj]⟩
              · exact Or.inr ⟨rfl, fun j hj ↦ by
                  have hne : j ≠ i := fun h ↦ hiS (h ▸ hj)
                  simp [Function.update_of_ne hne, hv j hj]⟩
            · rintro (⟨_, hv⟩ | ⟨_, hv⟩) <;> intro j hj
              · have hne : j ≠ i := fun h ↦ hiS (h ▸ hj)
                simpa [Function.update_of_ne hne] using hv j hj
              · have hne : j ≠ i := fun h ↦ hiS (h ▸ hj)
                simpa [Function.update_of_ne hne] using hv j hj
          have hdisj : Disjoint
              (Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ insert i S, v j = Function.update u i false j))
              (Finset.univ.filter (fun v : Fin (2 ^ n) → Bool ↦ ∀ j ∈ insert i S, v j = Function.update u i true j)) := by
            rw [Finset.disjoint_left]
            intro v h1 h2
            have hf := (Finset.mem_filter.mp h1).2 i (Finset.mem_insert_self i S)
            have ht := (Finset.mem_filter.mp h2).2 i (Finset.mem_insert_self i S)
            simp at hf ht; rw [hf] at ht; cases ht
          rw [hfilt, Finset.sum_union hdisj, hsub_eq, pow_succ, mul_inv, smul_add]
          simp only [smul_smul]; push_cast; ring_nf
        have hdiff_eq : ∀ b : Bool,
            (fixedSubsetAvgState W n (insert i S) (Function.update u i b)).mat -
              (1 : ℂ) • (fixedSubsetAvgState W n S u).mat =
            ((1 / 2 : ℝ) : ℂ) •
              ((fixedSubsetAvgState W n (insert i S) (Function.update u i b)).mat -
               (fixedSubsetAvgState W n (insert i S) (Function.update u i (!b))).mat) := by
          intro b
          rw [one_smul, hmid]
          cases b <;> (ext x y; simp; ring)
        have hupd : Function.update u i (u i) = u := Function.update_eq_self i u
        rw [← hupd]
        set b := u i
        rw [traceDist_eq_hockeyStick_one, hockeyStick_eq_posPartTrace]
        have hH := ((fixedSubsetAvgState W n (insert i S) (Function.update u i b)).isHermitian.sub
          (fixedSubsetAvgState W n (insert i S) (Function.update u i (!b))).isHermitian)
        have hHc : (((1 / 2 : ℝ) : ℂ) • ((fixedSubsetAvgState W n (insert i S) (Function.update u i b)).mat -
            (fixedSubsetAvgState W n (insert i S) (Function.update u i (!b))).mat)).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hH.eq]
        rw [posPartTrace_eq_of_eq _ hHc (hdiff_eq b), posPartTrace_smul_nonneg_aux (by norm_num) hH]
        congr 1
        have htd : posPartTrace hH = traceDist
            (fixedSubsetAvgState W n (insert i S) (Function.update u i b))
            (fixedSubsetAvgState W n (insert i S) (Function.update u i (!b))) := by
          rw [traceDist_eq_hockeyStick_one, hockeyStick_eq_posPartTrace]
          exact posPartTrace_eq_of_eq _ _ (by simp)
        rw [htd]
        cases b
        · rfl
        · exact traceDist_symm _ _
      simp_rw [hS_succ, hhalf_step]
      rw [← Finset.mul_sum, ← mul_assoc, mul_comm (((2 : ℝ) ^ (2 ^ n))⁻¹), mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      let R : Finset (Fin i.val) := Finset.univ.filter (fun j : Fin i.val ↦ ⟨j.val, lt_trans j.isLt i.isLt⟩ ∉ S)
      have hconv_u : ∀ u : Fin (2 ^ n) → Bool,
          traceDist
            (fixedSubsetAvgState W n (insert i S) (Function.update u i false))
            (fixedSubsetAvgState W n (insert i S) (Function.update u i true)) ≤
          ((2 : ℝ) ^ R.card)⁻¹ *
            ∑ q : R → Bool,
              traceDist
                (condSynthState W n i (fun j : Fin i.val ↦
                  if h : j ∈ R then q ⟨j, h⟩ else u ⟨j.val, lt_trans j.isLt i.isLt⟩) false)
                (condSynthState W n i (fun j : Fin i.val ↦
                  if h : j ∈ R then q ⟨j, h⟩ else u ⟨j.val, lt_trans j.isLt i.isLt⟩) true) := by
        intro u
        have hcard_R : R.card + S.card = i.val := by
          have hS_sub : S.card = (Finset.univ.filter (fun j : Fin i.val ↦ ⟨j.val, lt_trans j.isLt i.isLt⟩ ∈ S)).card := by
            apply Finset.card_bij (fun x hx ↦ (⟨x.val, (Finset.mem_filter.mp hx).2⟩ : Fin i.val))
            · intro x hx; simp [Finset.mem_filter, hx]
            · intro x₁ _ x₂ _ h; exact Fin.ext (congr_arg Fin.val h)
            · intro j hj
              refine ⟨⟨j.val, lt_trans j.isLt i.isLt⟩, (Finset.mem_filter.mp hj).2, rfl⟩
          rw [hS_sub, Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ, Fintype.card_fin]
        have havg_mat : ∀ b : Bool,
            (fixedSubsetAvgState W n (insert i S) (Function.update u i b)).mat =
              ((Fintype.card (R → Bool) : ℂ)⁻¹) •
                ∑ q : R → Bool,
                  (condSynthState W n i (fun j : Fin i.val ↦
                    if h : j ∈ R then q ⟨j, h⟩ else u ⟨j.val, lt_trans j.isLt i.isLt⟩) b).mat := by
          intro b
          simp only [fixedSubsetAvgState, condSynthState, synthBlockMat, Fintype.card_fun,
            Fintype.card_bool, Fintype.card_coe]
          rw [← Finset.smul_sum, smul_smul]
          have hcard_ins : (insert i S).card = S.card + 1 := Finset.card_insert_of_notMem hiS
          have hexp : 2 ^ n - (insert i S).card = R.card + (2 ^ n - 1 - i.val) := by
            have := i.isLt; omega
          have hpow : ((2 : ℂ) ^ (2 ^ n - (insert i S).card))⁻¹ =
              ((2 : ℂ) ^ R.card)⁻¹ * ((2 : ℂ) ^ (2 ^ n - 1 - i.val))⁻¹ := by
            rw [hexp, pow_add, mul_inv, mul_comm]
          rw [← hpow]
          congr 1
          rw [← Finset.sum_biUnion]
          · congr 1; ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
              Finset.mem_insert, forall_eq_or_imp, Function.update_self]
            constructor
            · rintro ⟨hvi, hvS⟩
              refine ⟨fun j ↦ v ⟨j.1.val, lt_trans j.1.isLt i.isLt⟩, ?_, hvi⟩
              funext j
              simp only [prefixOf]
              by_cases hj : j ∈ R
              · simp [hj]
              · simp only [hj, ↓reduceIte]
                have hjS : (⟨j.val, lt_trans j.isLt i.isLt⟩ : Fin (2 ^ n)) ∈ S := by
                  simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
                  exact hj
                have hne : (⟨j.val, lt_trans j.isLt i.isLt⟩ : Fin (2 ^ n)) ≠ i :=
                  fun h ↦ hiS (h ▸ hjS)
                simpa [Function.update_of_ne hne] using hvS _ hjS
            · rintro ⟨q, hp, hvi⟩
              refine ⟨hvi, fun j hjS ↦ ?_⟩
              have hjk : j.val < i.val := (Finset.mem_filter.mp hjS).2
              have hjnotR : (⟨j.val, hjk⟩ : Fin i.val) ∉ R := by
                simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; exact hjS
              have hne : j ≠ i := fun h ↦ hiS (h ▸ hjS)
              have hval := congr_fun hp ⟨j.val, hjk⟩
              simp only [prefixOf, hjnotR, ↓reduceIte] at hval
              simpa [Function.update_of_ne hne] using hval
          · intro q₁ _ q₂ _ hne
            rw [Finset.disjoint_left]
            intro v h1 h2
            have hp1 := (Finset.mem_filter.mp h1).2.1
            have hp2 := (Finset.mem_filter.mp h2).2.1
            apply hne; funext ⟨j, hj⟩
            have h1j := congr_fun hp1 j
            have h2j := congr_fun hp2 j
            simp only [prefixOf, hj, ↓reduceIte] at h1j h2j
            exact h1j.symm.trans h2j
        simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using
          traceDist_uniformAvg_le _ _ _ _ (havg_mat false) (havg_mat true)
      have havg_p : ((2 : ℝ) ^ (2 ^ n))⁻¹ *
          ∑ u : Fin (2 ^ n) → Bool,
            ((2 : ℝ) ^ R.card)⁻¹ *
              ∑ q : R → Bool,
                traceDist
                  (condSynthState W n i (fun j : Fin i.val ↦
                    if h : j ∈ R then q ⟨j, h⟩ else u ⟨j.val, lt_trans j.isLt i.isLt⟩) false)
                  (condSynthState W n i (fun j : Fin i.val ↦
                    if h : j ∈ R then q ⟨j, h⟩ else u ⟨j.val, lt_trans j.isLt i.isLt⟩) true) =
          ((2 : ℝ) ^ i.val)⁻¹ *
            ∑ p : Fin i.val → Bool,
              traceDist (condSynthState W n i p false) (condSynthState W n i p true) := by
        let F : (Fin i.val → Bool) → ℝ := fun p ↦
          traceDist (condSynthState W n i p false) (condSynthState W n i p true)
        have hfiber : ∀ p : Fin i.val → Bool,
            (Finset.univ.filter (fun uq : (Fin (2 ^ n) → Bool) × (R → Bool) ↦
              (fun j : Fin i.val ↦
                if h : j ∈ R then uq.2 ⟨j, h⟩ else uq.1 ⟨j.val, lt_trans j.isLt i.isLt⟩) = p)).card =
            2 ^ (2 ^ n + R.card - i.val) := by
          intro p
          let A : Finset (Fin (2 ^ n)) := S
          have hA_card : A.card = i.val - R.card := by
            have hcard_R : R.card + S.card = i.val := by
              have hS_sub : S.card = (Finset.univ.filter (fun j : Fin i.val ↦ ⟨j.val, lt_trans j.isLt i.isLt⟩ ∈ S)).card := by
                apply Finset.card_bij (fun x hx ↦ (⟨x.val, (Finset.mem_filter.mp hx).2⟩ : Fin i.val))
                · intro x hx; simp [Finset.mem_filter, hx]
                · intro x₁ _ x₂ _ h; exact Fin.ext (congr_arg Fin.val h)
                · intro j hj; refine ⟨⟨j.val, lt_trans j.isLt i.isLt⟩, (Finset.mem_filter.mp hj).2, rfl⟩
              rw [hS_sub, Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ, Fintype.card_fin]
            omega
          let e : {uq : (Fin (2 ^ n) → Bool) × (R → Bool) //
              (fun j : Fin i.val ↦
                if h : j ∈ R then uq.2 ⟨j, h⟩ else uq.1 ⟨j.val, lt_trans j.isLt i.isLt⟩) = p} ≃
              ({j : Fin (2 ^ n) // j ∉ S} → Bool) :=
            { toFun := fun uq j ↦ uq.1.1 j.1
              invFun := fun w ↦
                ⟨(fun x ↦ if hx : x ∈ S then p ⟨x.val, (Finset.mem_filter.mp hx).2⟩ else w ⟨x, hx⟩,
                  fun j ↦ p j.1),
                 funext fun j ↦ by
                   by_cases hj : j ∈ R
                   · simp [hj]
                   · have hjS : (⟨j.val, lt_trans j.isLt i.isLt⟩ : Fin (2 ^ n)) ∈ S := by
                       simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
                       exact hj
                     simp [hj, hjS]⟩
              left_inv := fun ⟨⟨u, q⟩, huq⟩ ↦ by
                apply Subtype.ext; apply Prod.ext
                · funext x
                  by_cases hx : x ∈ S
                  · simp only [hx, ↓reduceIte]
                    have hnotR : (⟨x.val, (Finset.mem_filter.mp hx).2⟩ : Fin i.val) ∉ R := by
                      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, not_not]; exact hx
                    have hv := congr_fun huq ⟨x.val, (Finset.mem_filter.mp hx).2⟩
                    simp only [hnotR, ↓reduceIte] at hv
                    exact hv.symm
                  · simp [hx]
                · funext ⟨j, hj⟩
                  have hv := congr_fun huq j
                  simp only [hj, ↓reduceIte] at hv
                  exact hv.symm
              right_inv := fun w ↦ funext fun ⟨x, hx⟩ ↦ by simp [hx] }
          rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_subtype_compl, Fintype.card_fin]
          congr 1
          have := i.isLt; have := Finset.card_le_univ R; rw [Fintype.card_fin] at this
          omega
        have hsum_eq : ∑ u : Fin (2 ^ n) → Bool, ∑ q : R → Bool,
            F (fun j : Fin i.val ↦ if h : j ∈ R then q ⟨j, h⟩ else u ⟨j.val, lt_trans j.isLt i.isLt⟩) =
            (2 : ℝ) ^ (2 ^ n + R.card - i.val) * ∑ p : Fin i.val → Bool, F p := by
          rw [← Fintype.sum_prod_type', Finset.mul_sum]
          rw [Finset.sum_fiberwise_of_maps_to (g := fun uq : (Fin (2 ^ n) → Bool) × (R → Bool) ↦
            fun j : Fin i.val ↦ if h : j ∈ R then uq.2 ⟨j, h⟩ else uq.1 ⟨j.val, lt_trans j.isLt i.isLt⟩)
            (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)]
          apply Finset.sum_congr rfl; intro p _
          have hcongr : ∑ x ∈ Finset.univ.filter (fun uq : (Fin (2 ^ n) → Bool) × (R → Bool) ↦
              (fun j : Fin i.val ↦ if h : j ∈ R then uq.2 ⟨j, h⟩ else uq.1 ⟨j.val, lt_trans j.isLt i.isLt⟩) = p),
              F (fun j : Fin i.val ↦ if h : j ∈ R then x.2 ⟨j, h⟩ else x.1 ⟨j.val, lt_trans j.isLt i.isLt⟩) =
              ∑ _x ∈ Finset.univ.filter (fun uq : (Fin (2 ^ n) → Bool) × (R → Bool) ↦
                (fun j : Fin i.val ↦ if h : j ∈ R then uq.2 ⟨j, h⟩ else uq.1 ⟨j.val, lt_trans j.isLt i.isLt⟩) = p),
              F p :=
            Finset.sum_congr rfl fun x hx ↦ by rw [(Finset.mem_filter.mp hx).2]
          rw [hcongr, Finset.sum_const, hfiber p, nsmul_eq_mul]; push_cast; rfl
        have hLHS : ((2 : ℝ) ^ (2 ^ n))⁻¹ *
            ∑ u : Fin (2 ^ n) → Bool, ((2 : ℝ) ^ R.card)⁻¹ *
              ∑ q : R → Bool, F (fun j : Fin i.val ↦ if h : j ∈ R then q ⟨j, h⟩ else u ⟨j.val, lt_trans j.isLt i.isLt⟩) =
            ((2 : ℝ) ^ (2 ^ n))⁻¹ * ((2 : ℝ) ^ R.card)⁻¹ *
              ((2 : ℝ) ^ (2 ^ n + R.card - i.val) * ∑ p : Fin i.val → Bool, F p) := by
          rw [← Finset.mul_sum, ← mul_assoc, hsum_eq]
        rw [hLHS, ← mul_assoc]
        congr 1
        have hle : i.val ≤ 2 ^ n + R.card := Nat.le_trans (le_of_lt i.isLt) (Nat.le_add_right _ _)
        have hpow_eq : (2 : ℝ) ^ (2 ^ n + R.card - i.val) * (2 : ℝ) ^ i.val =
            (2 : ℝ) ^ (2 ^ n) * (2 : ℝ) ^ R.card := by
          rw [← pow_add, ← pow_add, Nat.sub_add_cancel hle]
        have h2ne1 : (2 : ℝ) ^ (2 ^ n) ≠ 0 := by positivity
        have h2ne2 : (2 : ℝ) ^ R.card ≠ 0 := by positivity
        have h2ne3 : (2 : ℝ) ^ i.val ≠ 0 := by positivity
        field_simp [h2ne1, h2ne2, h2ne3]
        linarith
      have hsynth_eq : traceDist ((synthChannel W n i).out false) ((synthChannel W n i).out true) =
          ((2 : ℝ) ^ i.val)⁻¹ *
            ∑ p : Fin i.val → Bool,
              traceDist (condSynthState W n i p false) (condSynthState W n i p true) := by
        have hout : ∀ b : Bool, (synthChannel W n i).out b =
            uniformBlockDiag (fun p : Fin i.val → Bool ↦ condSynthState W n i p b) := by
          intro b
          apply DensityOp.ext
          ext ⟨p₁, x₁⟩ ⟨p₂, x₂⟩
          simp only [synthChannel, synthState, uniformBlockDiag, condSynthState, Matrix.of_apply,
            Matrix.smul_apply, smul_eq_mul, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
          split_ifs with hp
          · subst hp
            have hexp : 2 ^ n - 1 = i.val + (2 ^ n - 1 - i.val) := by have := i.isLt; omega
            have hpow : ((2 : ℂ) ^ (2 ^ n - 1))⁻¹ =
                ((2 : ℂ) ^ i.val)⁻¹ * ((2 : ℂ) ^ (2 ^ n - 1 - i.val))⁻¹ := by
              rw [hexp, pow_add, mul_inv, mul_comm]
            rw [hpow]; push_cast; ring
          · rfl
        rw [hout false, hout true, traceDist_uniformBlockDiag]
        simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      rw [hsynth_eq, ← havg_p]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ ↦ hconv_u u) (by positivity)
    · rw [if_neg hiT]
      have hsame := prefixSubset_succ_of_notMem T hk hiT
      simp [hsame, traceDist_self]
  calc ((2 : ℝ) ^ (2 ^ n))⁻¹ *
        ∑ u : Fin (2 ^ n) → Bool,
          traceDist (fixedSubsetAvgState W n T u) (fixedSubsetAvgState W n ∅ u)
      ≤ ∑ k ∈ Finset.range (2 ^ n),
          ((2 : ℝ) ^ (2 ^ n))⁻¹ *
            ∑ u : Fin (2 ^ n) → Bool,
              traceDist (fixedSubsetAvgState W n (prefixSubset T (k + 1)) u)
                (fixedSubsetAvgState W n (prefixSubset T k) u) := havg_tele
    _ ≤ ∑ i : Fin (2 ^ n),
          if i ∈ T then
            (1 / 2) * traceDist ((synthChannel W n i).out false) ((synthChannel W n i).out true)
          else 0 := by
        rw [← Fin.sum_univ_eq_sum_range (fun k ↦ if h : k < 2 ^ n then
          ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ u : Fin (2 ^ n) → Bool,
            traceDist (fixedSubsetAvgState W n (prefixSubset T (k + 1)) u)
              (fixedSubsetAvgState W n (prefixSubset T k) u) else 0)]
        · apply Finset.sum_le_sum; intro i _
          simp only [i.isLt, ↓reduceDIte]
          exact hstep i.val i.isLt
        · exact Finset.sum_congr rfl fun k hk ↦ by simp [Finset.mem_range.mp hk]
    _ = ∑ i ∈ T, (1 / 2) * traceDist ((synthChannel W n i).out false) ((synthChannel W n i).out true) := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **Average Operational Secrecy Bound**: Averaging `wiretapSecrecyError` over all public
frozen assignments `uF : Fin (2^n) → Bool` yields the Renes–Wilde phase-polarization upper bound. -/
theorem avg_wiretapSecrecyError_le (𝒩 : CPTPMap.{0} Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (hdisj_ir : Disjoint infoSet randSet)
    (hdisj_ia : Disjoint infoSet assistSet) :
    ((2 : ℝ) ^ (2 ^ n))⁻¹ *
      ∑ uF : Fin (2 ^ n) → Bool,
        wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF ≤
      ∑ i ∈ (randSet ∪ assistSet)ᶜ,
        (1 / 2) * (synthChannel (phaseChannel 𝒩) n (dualIndex n i)).fidelityParam := by
  set T := (randSet ∪ assistSet)ᶜ
  have hinfo_sub : infoSet ⊆ T := by
    intro i hi
    simp only [T, Finset.mem_compl, Finset.mem_union, not_or]
    exact ⟨Finset.disjoint_left.mp hdisj_ir hi, Finset.disjoint_left.mp hdisj_ia hi⟩
  have hsec_eq : ∀ uF : Fin (2 ^ n) → Bool,
      wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF =
        ((2 : ℝ) ^ infoSet.card)⁻¹ *
          ∑ m : infoSet → Bool,
            traceDist
              (fixedSubsetAvgState (ampChannel 𝒩.complementary) n T
                (fun i ↦ if h : i ∈ infoSet then m ⟨i, h⟩ else uF i))
              (fixedSubsetAvgState (ampChannel 𝒩.complementary) n ∅
                (fun i ↦ if h : i ∈ infoSet then m ⟨i, h⟩ else uF i)) := by
    intro uF
    unfold wiretapSecrecyError wiretapEveJointState wiretapIdealEveState wiretapEveCondState
    rw [traceDist_uniformBlockDiag]
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    congr 1; apply Finset.sum_congr rfl; intro m _
    congr 1
    apply DensityOp.ext; simp [fixedSubsetAvgState]
  simp_rw [hsec_eq]
  have hreidx : ((2 : ℝ) ^ (2 ^ n))⁻¹ *
      ∑ uF : Fin (2 ^ n) → Bool,
        ((2 : ℝ) ^ infoSet.card)⁻¹ *
          ∑ m : infoSet → Bool,
            traceDist
              (fixedSubsetAvgState (ampChannel 𝒩.complementary) n T
                (fun i ↦ if h : i ∈ infoSet then m ⟨i, h⟩ else uF i))
              (fixedSubsetAvgState (ampChannel 𝒩.complementary) n ∅
                (fun i ↦ if h : i ∈ infoSet then m ⟨i, h⟩ else uF i)) =
      ((2 : ℝ) ^ (2 ^ n))⁻¹ *
        ∑ u : Fin (2 ^ n) → Bool,
          traceDist
            (fixedSubsetAvgState (ampChannel 𝒩.complementary) n T u)
            (fixedSubsetAvgState (ampChannel 𝒩.complementary) n ∅ u) := by
    let F : (Fin (2 ^ n) → Bool) → ℝ := fun u ↦
      traceDist (fixedSubsetAvgState (ampChannel 𝒩.complementary) n T u)
        (fixedSubsetAvgState (ampChannel 𝒩.complementary) n ∅ u)
    let g : (Fin (2 ^ n) → Bool) × (infoSet → Bool) → (Fin (2 ^ n) → Bool) :=
      fun p i ↦ if h : i ∈ infoSet then p.2 ⟨i, h⟩ else p.1 i
    have hfib : ∀ u : Fin (2 ^ n) → Bool,
        (Finset.univ.filter (fun p : (Fin (2 ^ n) → Bool) × (infoSet → Bool) ↦ g p = u)).card =
        2 ^ infoSet.card := by
      intro u
      let e : {p : (Fin (2 ^ n) → Bool) × (infoSet → Bool) // g p = u} ≃ (infoSet → Bool) :=
        { toFun := fun p i ↦ p.1.1 i.1
          invFun := fun w ↦
            ⟨(fun i ↦ if h : i ∈ infoSet then w ⟨i, h⟩ else u i, fun i ↦ u i.1),
             funext fun i ↦ by by_cases h : i ∈ infoSet <;> simp [g, h]⟩
          left_inv := fun ⟨⟨uF, m'⟩, h⟩ ↦ by
            apply Subtype.ext; apply Prod.ext
            · funext i; by_cases hi : i ∈ infoSet
              · simp [hi]
              · have := congr_fun h i; simp [g, hi] at this ⊢; exact this.symm
            · funext ⟨i, hi⟩; have := congr_fun h i; simp [g, hi] at this; exact this.symm
          right_inv := fun w ↦ funext fun ⟨i, hi⟩ ↦ by simp [hi] }
      rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_coe]
    have hsum : ∑ uF : Fin (2 ^ n) → Bool, ∑ m : infoSet → Bool, F (g (uF, m)) =
        (2 : ℝ) ^ infoSet.card * ∑ u : Fin (2 ^ n) → Bool, F u := by
      rw [← Fintype.sum_prod_type']
      rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := g)
        (fun _ _ ↦ Finset.mem_univ _)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro u _
      have hconst : ∑ p ∈ Finset.univ.filter (fun p ↦ g p = u), F (g p) =
          ∑ _p ∈ Finset.univ.filter (fun p ↦ g p = u), F u :=
        Finset.sum_congr rfl fun p hp ↦ by rw [(Finset.mem_filter.mp hp).2]
      rw [hconst, Finset.sum_const, hfib u, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    have h2pos : ((2 : ℝ) ^ infoSet.card) ≠ 0 := by positivity
    calc ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ uF : Fin (2 ^ n) → Bool,
            ((2 : ℝ) ^ infoSet.card)⁻¹ * ∑ m : infoSet → Bool, F (g (uF, m))
        = ((2 : ℝ) ^ (2 ^ n))⁻¹ * (((2 : ℝ) ^ infoSet.card)⁻¹ *
            ∑ uF : Fin (2 ^ n) → Bool, ∑ m : infoSet → Bool, F (g (uF, m))) := by
            rw [← Finset.mul_sum]
      _ = ((2 : ℝ) ^ (2 ^ n))⁻¹ * (((2 : ℝ) ^ infoSet.card)⁻¹ *
            ((2 : ℝ) ^ infoSet.card * ∑ u : Fin (2 ^ n) → Bool, F u)) := by rw [hsum]
      _ = ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ u : Fin (2 ^ n) → Bool, F u := by
            rw [← mul_assoc (((2 : ℝ) ^ infoSet.card)⁻¹), inv_mul_cancel₀ h2pos, one_mul]
  rw [hreidx]
  calc ((2 : ℝ) ^ (2 ^ n))⁻¹ *
        ∑ u : Fin (2 ^ n) → Bool,
          traceDist (fixedSubsetAvgState (ampChannel 𝒩.complementary) n T u)
            (fixedSubsetAvgState (ampChannel 𝒩.complementary) n ∅ u)
      ≤ ∑ i ∈ T, (1 / 2) * traceDist ((synthChannel (ampChannel 𝒩.complementary) n i).out false)
          ((synthChannel (ampChannel 𝒩.complementary) n i).out true) :=
        avg_fixedSubset_decoupling_le (ampChannel 𝒩.complementary) n T
    _ = ∑ i ∈ T, (1 / 2) * (synthChannel (phaseChannel 𝒩) n (dualIndex n i)).fidelityParam := by
        apply Finset.sum_congr rfl; intro i _
        rw [synthChannel_complementary_traceDist_eq_phase_fidelityParam]

/-- **Average Operational Decoding Error Bound for Bob**: Averaging `wiretapBobError` over all
public frozen assignments `uF : Fin (2^n) → Bool` yields the Wilde–Guha QSC decoding error bound
on `infoSet ∪ randSet`. -/
theorem avg_wiretapBobError_le (𝒩 : CPTPMap.{0} Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n))) :
    ((2 : ℝ) ^ (2 ^ n))⁻¹ *
      ∑ uF : Fin (2 ^ n) → Bool,
        wiretapBobError 𝒩 n infoSet randSet assistSet uF ≤
      2 * Real.sqrt (∑ i ∈ infoSet ∪ randSet,
        (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam) := by
  let F : (Fin (2 ^ n) → Bool) → ℝ := fun f ↦
    (qscPolarCode (ampChannel 𝒩) n (infoSet ∪ randSet) f).avgBlockError
  let g : (Fin (2 ^ n) → Bool) × (assistSet → Bool) → (Fin (2 ^ n) → Bool) :=
    fun p ↦ bobEffectiveFrozen assistSet p.1 p.2
  have hfib : ∀ u : Fin (2 ^ n) → Bool,
      (Finset.univ.filter (fun p : (Fin (2 ^ n) → Bool) × (assistSet → Bool) ↦ g p = u)).card =
      2 ^ assistSet.card := by
    intro u
    let e : {p : (Fin (2 ^ n) → Bool) × (assistSet → Bool) // g p = u} ≃ (assistSet → Bool) :=
      { toFun := fun p i ↦ p.1.1 i.1
        invFun := fun w ↦
          ⟨(fun i ↦ if h : i ∈ assistSet then w ⟨i, h⟩ else u i, fun i ↦ u i.1),
           funext fun i ↦ by by_cases h : i ∈ assistSet <;> simp [g, bobEffectiveFrozen, h]⟩
        left_inv := fun ⟨⟨uF, k'⟩, h⟩ ↦ by
          apply Subtype.ext; apply Prod.ext
          · funext i; by_cases hi : i ∈ assistSet
            · simp [hi]
            · have := congr_fun h i; simp [g, bobEffectiveFrozen, hi] at this ⊢; exact this.symm
          · funext ⟨i, hi⟩; have := congr_fun h i; simp [g, bobEffectiveFrozen, hi] at this; exact this.symm
        right_inv := fun w ↦ funext fun ⟨i, hi⟩ ↦ by simp [hi] }
    rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe]
  have hsum : ∑ uF : Fin (2 ^ n) → Bool, ∑ k : assistSet → Bool, F (g (uF, k)) =
      (2 : ℝ) ^ assistSet.card * ∑ u : Fin (2 ^ n) → Bool, F u := by
    rw [← Fintype.sum_prod_type']
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := g)
      (fun _ _ ↦ Finset.mem_univ _)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _
    have hconst : ∑ p ∈ Finset.univ.filter (fun p ↦ g p = u), F (g p) =
        ∑ _p ∈ Finset.univ.filter (fun p ↦ g p = u), F u :=
      Finset.sum_congr rfl fun p hp ↦ by rw [(Finset.mem_filter.mp hp).2]
    rw [hconst, Finset.sum_const, hfib u, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  have h2pos : ((2 : ℝ) ^ assistSet.card) ≠ 0 := by positivity
  have hreidx : ((2 : ℝ) ^ (2 ^ n))⁻¹ *
      ∑ uF : Fin (2 ^ n) → Bool, wiretapBobError 𝒩 n infoSet randSet assistSet uF =
      ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ f : Fin (2 ^ n) → Bool, F f := by
    unfold wiretapBobError
    calc ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ uF : Fin (2 ^ n) → Bool,
            ((2 : ℝ) ^ assistSet.card)⁻¹ * ∑ k : assistSet → Bool, F (g (uF, k))
        = ((2 : ℝ) ^ (2 ^ n))⁻¹ * (((2 : ℝ) ^ assistSet.card)⁻¹ *
            ∑ uF : Fin (2 ^ n) → Bool, ∑ k : assistSet → Bool, F (g (uF, k))) := by
            rw [← Finset.mul_sum]
      _ = ((2 : ℝ) ^ (2 ^ n))⁻¹ * (((2 : ℝ) ^ assistSet.card)⁻¹ *
            ((2 : ℝ) ^ assistSet.card * ∑ u : Fin (2 ^ n) → Bool, F u)) := by rw [hsum]
      _ = ((2 : ℝ) ^ (2 ^ n))⁻¹ * ∑ f : Fin (2 ^ n) → Bool, F f := by
            rw [← mul_assoc (((2 : ℝ) ^ assistSet.card)⁻¹), inv_mul_cancel₀ h2pos, one_mul]
  rw [hreidx]
  exact wilde_guha_qsc_avg_bound (ampChannel 𝒩) n (infoSet ∪ randSet)

/-- **Simultaneous Existence of a Good Public Frozen Assignment `uF`**: There exists a deterministic
public frozen vector `uF : Fin (2^n) → Bool` achieving the combined Bob decoding error and Eve
trace-distance secrecy error bound. -/
theorem exists_wiretap_frozen_good (𝒩 : CPTPMap.{0} Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (hdisj_ir : Disjoint infoSet randSet)
    (hdisj_ia : Disjoint infoSet assistSet) :
    ∃ uF : Fin (2 ^ n) → Bool,
      wiretapBobError 𝒩 n infoSet randSet assistSet uF +
        wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF ≤
      2 * Real.sqrt (∑ i ∈ infoSet ∪ randSet,
          (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam) +
        ∑ i ∈ (randSet ∪ assistSet)ᶜ,
          (1 / 2) * (synthChannel (phaseChannel 𝒩) n (dualIndex n i)).fidelityParam := by
  set B := 2 * Real.sqrt (∑ i ∈ infoSet ∪ randSet,
        (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam) +
      ∑ i ∈ (randSet ∪ assistSet)ᶜ,
        (1 / 2) * (synthChannel (phaseChannel 𝒩) n (dualIndex n i)).fidelityParam
  have havg : ((2 : ℝ) ^ (2 ^ n))⁻¹ *
      ∑ uF : Fin (2 ^ n) → Bool,
        (wiretapBobError 𝒩 n infoSet randSet assistSet uF +
         wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF) ≤ B := by
    rw [Finset.sum_add_distrib, mul_add]
    exact add_le_add (avg_wiretapBobError_le 𝒩 n infoSet randSet assistSet)
      (avg_wiretapSecrecyError_le 𝒩 n infoSet randSet assistSet hdisj_ir hdisj_ia)
  by_contra h
  push Not at h
  have hsum_gt : (2 : ℝ) ^ (2 ^ n) * B <
      ∑ uF : Fin (2 ^ n) → Bool,
        (wiretapBobError 𝒩 n infoSet randSet assistSet uF +
         wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF) := by
    have h1 : ∑ _uF : Fin (2 ^ n) → Bool, B <
        ∑ uF : Fin (2 ^ n) → Bool,
          (wiretapBobError 𝒩 n infoSet randSet assistSet uF +
           wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun uF _ ↦ h uF)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h1
    exact h1
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ n) := by positivity
  have hlt : B < ((2 : ℝ) ^ (2 ^ n))⁻¹ *
      ∑ uF : Fin (2 ^ n) → Bool,
        (wiretapBobError 𝒩 n infoSet randSet assistSet uF +
         wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF) := by
    rw [lt_inv_mul_iff₀ h2pos]; exact hsum_gt
  linarith

/-- An operational Renes–Wilde private classical wiretap polar code over `𝒩^⊗(2^n)` with
randomized privacy-amplification encoder, pre-shared secret key register `assistSet`, Bob's
Wilde–Guha QSC decoder, and Eve's complementary-channel wiretap state. -/
structure OperationalPrivatePolarCode (𝒩 : CPTPMap.{0} Bool d) (n : ℕ) where
  infoSet : Finset (Fin (2 ^ n))
  randSet : Finset (Fin (2 ^ n))
  assistSet : Finset (Fin (2 ^ n))
  disjoint_info_rand : Disjoint infoSet randSet
  disjoint_info_assist : Disjoint infoSet assistSet
  disjoint_rand_assist : Disjoint randSet assistSet
  publicFrozen : Fin (2 ^ n) → Bool

/-- Private message transmission rate `|infoSet| / 2^n`. -/
noncomputable def OperationalPrivatePolarCode.rate {𝒩 : CPTPMap.{0} Bool d} {n : ℕ}
    (C : OperationalPrivatePolarCode 𝒩 n) : ℝ :=
  (C.infoSet.card : ℝ) / (2 : ℝ) ^ n

/-- Pre-shared secret key assistance rate `|assistSet| / 2^n`. -/
noncomputable def OperationalPrivatePolarCode.secretKeyRate {𝒩 : CPTPMap.{0} Bool d} {n : ℕ}
    (C : OperationalPrivatePolarCode 𝒩 n) : ℝ :=
  (C.assistSet.card : ℝ) / (2 : ℝ) ^ n

/-- Bob's operational QSC decoding error for `C`. -/
noncomputable def OperationalPrivatePolarCode.bobDecodingError {𝒩 : CPTPMap.{0} Bool d} {n : ℕ}
    (C : OperationalPrivatePolarCode 𝒩 n) : ℝ :=
  wiretapBobError 𝒩 n C.infoSet C.randSet C.assistSet C.publicFrozen

/-- Eve's operational trace-distance secrecy error `T(ρ_{ME}, π_M ⊗ ρ_E)` for `C`. -/
noncomputable def OperationalPrivatePolarCode.eveSecrecyError {𝒩 : CPTPMap.{0} Bool d} {n : ℕ}
    (C : OperationalPrivatePolarCode 𝒩 n) : ℝ :=
  wiretapSecrecyError 𝒩 n C.infoSet C.randSet C.assistSet C.publicFrozen

lemma OperationalPrivatePolarCode.bobDecodingError_nonneg {𝒩 : CPTPMap.{0} Bool d} {n : ℕ}
    (C : OperationalPrivatePolarCode 𝒩 n) : 0 ≤ C.bobDecodingError := by
  unfold OperationalPrivatePolarCode.bobDecodingError wiretapBobError
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg; intro k _
  exact (qscPolarCode (ampChannel 𝒩) n (C.infoSet ∪ C.randSet)
    (bobEffectiveFrozen C.assistSet C.publicFrozen k)).avgBlockError_nonneg

lemma OperationalPrivatePolarCode.eveSecrecyError_nonneg {𝒩 : CPTPMap.{0} Bool d} {n : ℕ}
    (C : OperationalPrivatePolarCode 𝒩 n) : 0 ≤ C.eveSecrecyError :=
  traceDist_nonneg _ _

end OperationalWiretap

end PolarCodes
