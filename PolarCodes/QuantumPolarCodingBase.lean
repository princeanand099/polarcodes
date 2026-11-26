/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.PolarCoding
import PolarCodes.QuantumChannels
import PolarCodes.ChannelDualityEquiv

/-!
# Quantum and Private Polar Coding via the Renes–Wilde Reduction (Corollary 5.5)

Part 1: CPTP tensor/idBoolTensor, `CQChannel.DegradedTo`, polar tree preservation & duality,
`symCoherentInfo`, Renes–Wilde `ampChannel`/`phaseChannel`, `amp_phase_symCapacity_sum`,
`goodSet`/`veryNoisySet`/`unpolarizedSet`, and `dual_unpolarized_fraction_le`.
-/

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodes

private lemma rootFidelity_nonneg {α : Type*} [Fintype α] [DecidableEq α] (ρ σ : DensityOp α) :
    0 ≤ rootFidelity ρ σ :=
  Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _

private lemma densityOp_ext {α : Type*} [Fintype α] [DecidableEq α] {ρ σ : DensityOp α}
    (h : ρ.mat = σ.mat) : ρ = σ := by
  cases ρ; cases σ; congr

universe u

section QuantumPolarCoding

variable {d : Type u} [Fintype d] [DecidableEq d]

/-! ### 1. Tensor Product of CPTP Maps and Preservation of Degradation / Channel Equivalence -/

/-- Tensor product `𝒟₁ ⊗ 𝒟₂` of two CPTP maps. -/
noncomputable def CPTPMap.tensor {α₁ β₁ α₂ β₂ : Type u}
    [Fintype α₁] [DecidableEq α₁] [Fintype β₁] [DecidableEq β₁]
    [Fintype α₂] [DecidableEq α₂] [Fintype β₂] [DecidableEq β₂]
    (𝒟₁ : CPTPMap.{u} α₁ β₁) (𝒟₂ : CPTPMap.{u} α₂ β₂) :
    CPTPMap.{u} (α₁ × α₂) (β₁ × β₂) :=
  ⟨𝒟₁.env × 𝒟₂.env, inferInstance, inferInstance,
    Matrix.of fun ((b₁, b₂), (e₁, e₂)) (a₁, a₂) ↦
      𝒟₁.isom (b₁, e₁) a₁ * 𝒟₂.isom (b₂, e₂) a₂, by
    ext ⟨a₁, a₂⟩ ⟨a₁', a₂'⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply, star_mul']
    have h1 := congr_fun (congr_fun 𝒟₁.5 a₁) a₁'
    have h2 := congr_fun (congr_fun 𝒟₂.5 a₂) a₂'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.one_apply] at h1 h2
    calc ∑ b₁ : β₁, ∑ b₂ : β₂, ∑ e₁ : 𝒟₁.env, ∑ e₂ : 𝒟₂.env,
          (star (𝒟₁.isom (b₁, e₁) a₁) * star (𝒟₂.isom (b₂, e₂) a₂)) *
          (𝒟₁.isom (b₁, e₁) a₁' * 𝒟₂.isom (b₂, e₂) a₂')
        = (∑ b₁ : β₁, ∑ e₁ : 𝒟₁.env, star (𝒟₁.isom (b₁, e₁) a₁) * 𝒟₁.isom (b₁, e₁) a₁') *
          (∑ b₂ : β₂, ∑ e₂ : 𝒟₂.env, star (𝒟₂.isom (b₂, e₂) a₂) * 𝒟₂.isom (b₂, e₂) a₂') := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro b₁ _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro e₁ _
            apply Finset.sum_congr rfl; intro b₂ _
            apply Finset.sum_congr rfl; intro e₂ _
            ring
      _ = (if a₁ = a₁' then (1 : ℂ) else 0) * (if a₂ = a₂' then (1 : ℂ) else 0) := by
            rw [h1, h2]
      _ = if (a₁, a₂) = (a₁', a₂') then 1 else 0 := by
            by_cases ha1 : a₁ = a₁' <;> by_cases ha2 : a₂ = a₂' <;> simp [ha1, ha2]⟩

/-- `(𝒟₁ ⊗ 𝒟₂)(ρ₁ ⊗ ρ₂) = 𝒟₁(ρ₁) ⊗ 𝒟₂(ρ₂)`. -/
lemma CPTPMap.tensor_apply_tensor {α₁ β₁ α₂ β₂ : Type u}
    [Fintype α₁] [DecidableEq α₁] [Fintype β₁] [DecidableEq β₁]
    [Fintype α₂] [DecidableEq α₂] [Fintype β₂] [DecidableEq β₂]
    (𝒟₁ : CPTPMap.{u} α₁ β₁) (𝒟₂ : CPTPMap.{u} α₂ β₂)
    (ρ₁ : DensityOp α₁) (ρ₂ : DensityOp α₂) :
    ((𝒟₁.tensor 𝒟₂).apply (DensityOp.tensor ρ₁ ρ₂)).mat =
      (DensityOp.tensor (𝒟₁.apply ρ₁) (𝒟₂.apply ρ₂)).mat := by
  ext ⟨b₁, b₂⟩ ⟨b₁', b₂'⟩
  unfold CPTPMap.apply CPTPMap.toLinearMap CPTPMap.tensor partialTrace₂Mat DensityOp.tensor
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, star_mul']
  have hterm : ∀ (e₁ : 𝒟₁.env) (e₂ : 𝒟₂.env),
      ∑ a₁' : α₁, ∑ a₂' : α₂,
        (∑ a₁ : α₁, ∑ a₂ : α₂,
          𝒟₁.isom (b₁, e₁) a₁ * 𝒟₂.isom (b₂, e₂) a₂ * (ρ₁.mat a₁ a₁' * ρ₂.mat a₂ a₂')) *
        (star (𝒟₁.isom (b₁', e₁) a₁') * star (𝒟₂.isom (b₂', e₂) a₂')) =
      (∑ a₁' : α₁, (∑ a₁ : α₁, 𝒟₁.isom (b₁, e₁) a₁ * ρ₁.mat a₁ a₁') * star (𝒟₁.isom (b₁', e₁) a₁')) *
      (∑ a₂' : α₂, (∑ a₂ : α₂, 𝒟₂.isom (b₂, e₂) a₂ * ρ₂.mat a₂ a₂') * star (𝒟₂.isom (b₂', e₂) a₂')) := by
    intro e₁ e₂
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a₁' _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a₁ _
    apply Finset.sum_congr rfl; intro a₂' _
    apply Finset.sum_congr rfl; intro a₂ _
    ring
  simp_rw [hterm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro e₁ _
  rw [Finset.mul_sum]

/-- Identity-on-`Bool` tensored with a CPTP map `𝒟`: `id_Bool ⊗ 𝒟 : CPTPMap (Bool × α) (Bool × β)`. -/
noncomputable def CPTPMap.idBoolTensor {α β : Type u} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (𝒟 : CPTPMap.{u} α β) :
    CPTPMap.{u} (Bool × α) (Bool × β) :=
  ⟨𝒟.env, inferInstance, inferInstance,
    Matrix.of fun ((w, b), e) (w', a) ↦ if w = w' then 𝒟.isom (b, e) a else 0, by
    ext ⟨w₁, a₁⟩ ⟨w₂, a₂⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
    by_cases hw : w₁ = w₂
    · subst hw
      rw [Finset.sum_eq_single w₁]
      · simp only [↓reduceIte, Prod.mk.injEq, true_and]
        have h := congr_fun (congr_fun 𝒟.5 a₁) a₂
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
          Matrix.one_apply] using h
      · intro w _ hne; apply Finset.sum_eq_zero; intro b _; apply Finset.sum_eq_zero; intro e _
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ w₁) h
    · have hne : (w₁, a₁) ≠ (w₂, a₂) := fun h ↦ hw (Prod.mk.inj h).1
      rw [if_neg hne]
      apply Finset.sum_eq_zero; intro w _
      apply Finset.sum_eq_zero; intro b _
      apply Finset.sum_eq_zero; intro e _
      by_cases h1 : w = w₁
      · subst h1; simp [hw]
      · simp [h1]⟩

/-- `(id_Bool ⊗ 𝒟)(|w⟩⟨w| ⊗ ρ) = |w⟩⟨w| ⊗ 𝒟(ρ)`. -/
lemma CPTPMap.idBoolTensor_apply_ketBra {α β : Type u} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (𝒟 : CPTPMap.{u} α β) (w : Bool) (ρ : DensityOp α) :
    (𝒟.idBoolTensor.apply (DensityOp.tensor (CQChannel.ketBraBool w) ρ)).mat =
      (DensityOp.tensor (CQChannel.ketBraBool w) (𝒟.apply ρ)).mat := by
  ext ⟨w₁, b₁⟩ ⟨w₂, b₂⟩
  unfold CPTPMap.apply CPTPMap.toLinearMap CPTPMap.idBoolTensor partialTrace₂Mat
    DensityOp.tensor CQChannel.ketBraBool
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  by_cases h1 : w₁ = w
  · subst h1
    by_cases h2 : w₂ = w₁
    · subst h2
      simp only [↓reduceIte, and_self, one_mul]
      apply Finset.sum_congr rfl; intro e _
      rw [Finset.sum_eq_single w₂]
      · apply Finset.sum_congr rfl; intro a' _
        rw [Finset.sum_eq_single w₂]
        · simp
        · intro w' _ hne; apply Finset.sum_eq_zero; intro a _; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ w₂) h
      · intro w' _ hne; apply Finset.sum_eq_zero; intro a' _; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ w₂) h
    · simp only [h2, and_false, ↓reduceIte, zero_mul]
      apply Finset.sum_eq_zero; intro e _
      apply Finset.sum_eq_zero; intro w' _
      apply Finset.sum_eq_zero; intro a' _
      by_cases hw' : w₂ = w'
      · subst hw'
        simp [h2]
      · simp [hw']
  · simp only [h1, false_and, ↓reduceIte, zero_mul]
    apply Finset.sum_eq_zero; intro e _
    apply Finset.sum_eq_zero; intro w' _
    apply Finset.sum_eq_zero; intro a' _
    have hzero : ∑ x : Bool, ∑ a : α,
        (if w₁ = x then 𝒟.isom (b₁, e) a else 0) *
        ((if x = w ∧ w' = w then (1 : ℂ) else 0) * ρ.mat a a') = 0 := by
      apply Finset.sum_eq_zero; intro x _
      apply Finset.sum_eq_zero; intro a _
      by_cases hx : w₁ = x
      · subst hx; simp [h1]
      · simp [hx]
    rw [hzero, zero_mul]

/-- Linearity of `CPTPMap.apply` on midpoints. -/
lemma CPTPMap.apply_midpoint {α β : Type u} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (𝒟 : CPTPMap.{u} α β) (ρ σ : DensityOp α) :
    (𝒟.apply (DensityOp.midpoint ρ σ)).mat =
      (DensityOp.midpoint (𝒟.apply ρ) (𝒟.apply σ)).mat := by
  ext i j
  unfold CPTPMap.apply CPTPMap.toLinearMap partialTrace₂Mat DensityOp.midpoint DensityOp.mix
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.real_smul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro e _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro l _
  ring

/-- `W₁.DegradedTo W₂` means `W₂` is obtained by post-processing `W₁` with a CPTP map `𝒟`. -/
def CQChannel.DegradedTo {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) : Prop :=
  ∃ 𝒟 : CPTPMap.{u} d₁ d₂, ∀ b : Bool, (𝒟.apply (W₁.out b)).mat = (W₂.out b).mat

lemma CQChannel.DegradedTo.condEntropy_le {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.DegradedTo W₂) : W₁.condEntropy ≤ W₂.condEntropy := by
  rcases h with ⟨𝒟, h𝒟⟩
  have heq : (𝒟.compCQ W₁).condEntropy = W₂.condEntropy := by
    have hch : 𝒟.compCQ W₁ = W₂ := by
      cases W₂
      unfold CPTPMap.compCQ
      congr
      funext b
      exact densityOp_ext (h𝒟 b)
    rw [hch]
  rw [← heq]
  exact condEntropy_cptp_ge 𝒟 W₁

lemma CQChannel.DegradedTo.trans {d₁ d₂ d₃ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃]
    {W₁ : CQChannel d₁} {W₂ : CQChannel d₂} {W₃ : CQChannel d₃}
    (h12 : W₁.DegradedTo W₂) (h23 : W₂.DegradedTo W₃) : W₁.DegradedTo W₃ := by
  rcases h12 with ⟨𝒟₁, h₁⟩
  rcases h23 with ⟨𝒟₂, h₂⟩
  refine ⟨𝒟₂.comp 𝒟₁, fun b ↦ ?_⟩
  rw [CPTPMap.comp_apply]
  have h1' : 𝒟₁.apply (W₁.out b) = W₂.out b := densityOp_ext (h₁ b)
  rw [h1', h₂ b]

lemma CQChannel.DegradedTo.checkCombine {d₁ d₂ d₁' d₂' : Type u}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    [Fintype d₁'] [DecidableEq d₁'] [Fintype d₂'] [DecidableEq d₂']
    {W₁ : CQChannel d₁} {W₂ : CQChannel d₂} {W₁' : CQChannel d₁'} {W₂' : CQChannel d₂'}
    (h1 : W₁.DegradedTo W₁') (h2 : W₂.DegradedTo W₂') :
    (W₁.checkCombine W₂).DegradedTo (W₁'.checkCombine W₂') := by
  rcases h1 with ⟨𝒟₁, h𝒟₁⟩
  rcases h2 with ⟨𝒟₂, h𝒟₂⟩
  refine ⟨𝒟₁.tensor 𝒟₂, fun b ↦ ?_⟩
  simp only [CQChannel.checkCombine]
  rw [CPTPMap.apply_midpoint]
  have hd1 : (𝒟₁.tensor 𝒟₂).apply (DensityOp.tensor (W₁.out b) (W₂.out false)) =
      DensityOp.tensor (W₁'.out b) (W₂'.out false) := by
    apply densityOp_ext
    rw [CPTPMap.tensor_apply_tensor]
    rw [densityOp_ext (h𝒟₁ b), densityOp_ext (h𝒟₂ false)]
  have hd2 : (𝒟₁.tensor 𝒟₂).apply (DensityOp.tensor (W₁.out (!b)) (W₂.out true)) =
      DensityOp.tensor (W₁'.out (!b)) (W₂'.out true) := by
    apply densityOp_ext
    rw [CPTPMap.tensor_apply_tensor]
    rw [densityOp_ext (h𝒟₁ (!b)), densityOp_ext (h𝒟₂ true)]
  rw [hd1, hd2]

lemma CQChannel.DegradedTo.varCombine {d₁ d₂ d₁' d₂' : Type u}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    [Fintype d₁'] [DecidableEq d₁'] [Fintype d₂'] [DecidableEq d₂']
    {W₁ : CQChannel d₁} {W₂ : CQChannel d₂} {W₁' : CQChannel d₁'} {W₂' : CQChannel d₂'}
    (h1 : W₁.DegradedTo W₁') (h2 : W₂.DegradedTo W₂') :
    (W₁.varCombine W₂).DegradedTo (W₁'.varCombine W₂') := by
  rcases h1 with ⟨𝒟₁, h𝒟₁⟩
  rcases h2 with ⟨𝒟₂, h𝒟₂⟩
  refine ⟨(𝒟₁.tensor 𝒟₂).idBoolTensor, fun b ↦ ?_⟩
  simp only [CQChannel.varCombine]
  rw [CPTPMap.apply_midpoint]
  have hd1 : (𝒟₁.tensor 𝒟₂).idBoolTensor.apply
      (DensityOp.tensor (CQChannel.ketBraBool false) (DensityOp.tensor (W₁.out b) (W₂.out b))) =
      DensityOp.tensor (CQChannel.ketBraBool false) (DensityOp.tensor (W₁'.out b) (W₂'.out b)) := by
    apply densityOp_ext
    rw [CPTPMap.idBoolTensor_apply_ketBra]
    have hinner : (𝒟₁.tensor 𝒟₂).apply (DensityOp.tensor (W₁.out b) (W₂.out b)) =
        DensityOp.tensor (W₁'.out b) (W₂'.out b) := by
      apply densityOp_ext; rw [CPTPMap.tensor_apply_tensor, densityOp_ext (h𝒟₁ b), densityOp_ext (h𝒟₂ b)]
    rw [hinner]
  have hd2 : (𝒟₁.tensor 𝒟₂).idBoolTensor.apply
      (DensityOp.tensor (CQChannel.ketBraBool true) (DensityOp.tensor (W₁.out (!b)) (W₂.out b))) =
      DensityOp.tensor (CQChannel.ketBraBool true) (DensityOp.tensor (W₁'.out (!b)) (W₂'.out b)) := by
    apply densityOp_ext
    rw [CPTPMap.idBoolTensor_apply_ketBra]
    have hinner : (𝒟₁.tensor 𝒟₂).apply (DensityOp.tensor (W₁.out (!b)) (W₂.out b)) =
        DensityOp.tensor (W₁'.out (!b)) (W₂'.out b) := by
      apply densityOp_ext; rw [CPTPMap.tensor_apply_tensor, densityOp_ext (h𝒟₁ (!b)), densityOp_ext (h𝒟₂ b)]
    rw [hinner]
  rw [hd1, hd2]

lemma CQChannel.ChannelEquiv.checkCombine {d₁ d₂ d₁' d₂' : Type u}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    [Fintype d₁'] [DecidableEq d₁'] [Fintype d₂'] [DecidableEq d₂']
    {W₁ : CQChannel d₁} {W₂ : CQChannel d₂} {W₁' : CQChannel d₁'} {W₂' : CQChannel d₂'}
    (h1 : W₁.ChannelEquiv W₁') (h2 : W₂.ChannelEquiv W₂') :
    (W₁.checkCombine W₂).ChannelEquiv (W₁'.checkCombine W₂') := by
  rcases h1 with ⟨𝒩₁, ℳ₁, hN₁, hM₁⟩
  rcases h2 with ⟨𝒩₂, ℳ₂, hN₂, hM₂⟩
  obtain ⟨𝒩, hN⟩ := CQChannel.DegradedTo.checkCombine ⟨𝒩₁, hN₁⟩ ⟨𝒩₂, hN₂⟩
  obtain ⟨ℳ, hM⟩ := CQChannel.DegradedTo.checkCombine ⟨ℳ₁, hM₁⟩ ⟨ℳ₂, hM₂⟩
  exact ⟨𝒩, ℳ, hN, hM⟩

lemma CQChannel.ChannelEquiv.varCombine {d₁ d₂ d₁' d₂' : Type u}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    [Fintype d₁'] [DecidableEq d₁'] [Fintype d₂'] [DecidableEq d₂']
    {W₁ : CQChannel d₁} {W₂ : CQChannel d₂} {W₁' : CQChannel d₁'} {W₂' : CQChannel d₂'}
    (h1 : W₁.ChannelEquiv W₁') (h2 : W₂.ChannelEquiv W₂') :
    (W₁.varCombine W₂).ChannelEquiv (W₁'.varCombine W₂') := by
  rcases h1 with ⟨𝒩₁, ℳ₁, hN₁, hM₁⟩
  rcases h2 with ⟨𝒩₂, ℳ₂, hN₂, hM₂⟩
  obtain ⟨𝒩, hN⟩ := CQChannel.DegradedTo.varCombine ⟨𝒩₁, hN₁⟩ ⟨𝒩₂, hN₂⟩
  obtain ⟨ℳ, hM⟩ := CQChannel.DegradedTo.varCombine ⟨ℳ₁, hM₁⟩ ⟨ℳ₂, hM₂⟩
  exact ⟨𝒩, ℳ, hN, hM⟩

/-- Degradation is preserved along every branch of the polarization tree. -/
theorem CQChannel.DegradedTo.polarChannelTree {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.DegradedTo W₂) :
    ∀ (n : ℕ) (b : Fin n → Bool),
      (polarChannelTree W₁ n b).ch.DegradedTo (polarChannelTree W₂ n b).ch
  | 0, _ => h
  | n + 1, b => by
    have hsnoc : b = Fin.snoc (α := fun _ ↦ Bool) (Fin.init b) (b (Fin.last n)) :=
      (Fin.snoc_init_self b).symm
    rw [hsnoc]
    have ih := h.polarChannelTree n (Fin.init b)
    cases b (Fin.last n)
    · rw [polarChannelTree_snoc_false, polarChannelTree_snoc_false]
      exact ih.checkCombine ih
    · rw [polarChannelTree_snoc_true, polarChannelTree_snoc_true]
      exact ih.varCombine ih

/-- Channel equivalence is preserved along every branch of the polarization tree. -/
theorem CQChannel.ChannelEquiv.polarChannelTree {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.ChannelEquiv W₂) (n : ℕ) (b : Fin n → Bool) :
    (polarChannelTree W₁ n b).ch.ChannelEquiv (polarChannelTree W₂ n b).ch := by
  rcases h with ⟨𝒩, ℳ, hN, hM⟩
  obtain ⟨𝒩', hN'⟩ := CQChannel.DegradedTo.polarChannelTree ⟨𝒩, hN⟩ n b
  obtain ⟨ℳ', hM'⟩ := CQChannel.DegradedTo.polarChannelTree ⟨ℳ, hM⟩ n b
  exact ⟨𝒩', ℳ', hN', hM'⟩

/-- Channel-level duality along the polarization tree: `(W⊥)_n^{(!b)} ≃ (W_n^{(b)})⊥`. -/
theorem polarChannelTree_dual_complement_channelEquiv (W : CQChannel d) :
    ∀ (n : ℕ) (b : Fin n → Bool),
      (polarChannelTree W.dual n (fun k ↦ !(b k))).ch.ChannelEquiv
        (polarChannelTree W n b).ch.dual
  | 0, _ => CQChannel.ChannelEquiv.refl W.dual
  | n + 1, b => by
    have haux : ∀ (b₀ : Fin n → Bool) (bn : Bool),
        (polarChannelTree W.dual (n + 1) (fun k ↦ !(Fin.snoc (α := fun _ ↦ Bool) b₀ bn k))).ch.ChannelEquiv
          (polarChannelTree W (n + 1) (Fin.snoc (α := fun _ ↦ Bool) b₀ bn)).ch.dual := by
      intro b₀ bn
      have h1 : (fun k : Fin (n + 1) ↦ !(Fin.snoc (α := fun _ ↦ Bool) b₀ bn k)) =
          Fin.snoc (α := fun _ ↦ Bool) (fun k : Fin n ↦ !(b₀ k)) (!bn) := by
        funext k
        refine Fin.lastCases ?_ ?_ k
        · simp
        · intro j; simp
      rw [h1]
      have ih := polarChannelTree_dual_complement_channelEquiv W n b₀
      cases bn
      · rw [Bool.not_false, polarChannelTree_snoc_true, polarChannelTree_snoc_false]
        exact (ih.varCombine ih).trans (prop_2_2_D2_check_channelEquiv _ _).symm
      · rw [Bool.not_true, polarChannelTree_snoc_false, polarChannelTree_snoc_true]
        exact (ih.checkCombine ih).trans (prop_2_2_D2_var_channelEquiv _ _).symm
    have hres := haux (Fin.init b) (b (Fin.last n))
    rwa [Fin.snoc_init_self] at hres

/-- Exact entropy duality along the polarization tree: `H((W⊥)_n^{(!b)}) = 1 - H(W_n^{(b)})`. -/
theorem polarCondEntropy_dual_complement (W : CQChannel d) (n : ℕ) (b : Fin n → Bool) :
    polarCondEntropy W.dual n (fun k ↦ !(b k)) = 1 - polarCondEntropy W n b := by
  unfold polarCondEntropy
  rw [(polarChannelTree_dual_complement_channelEquiv W n b).condEntropy_eq]
  linarith [prop_2_2_D1 (polarChannelTree W n b).ch]

/-! ### 2. Symmetric Coherent / Private Information and Renes–Wilde Amplitude & Phase Channels -/

/-- Symmetric coherent (and, for degradable channels, symmetric private) information
`I_sym(𝒩) = S(𝒩(π₂)) - S(𝒩^c(π₂))` of a qubit-input CPTP map `𝒩 : CPTPMap Bool d`. -/
noncomputable def symCoherentInfo {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d) : ℝ :=
  vonNeumannEntropy (𝒩.apply (maxMixedState Bool)) -
    vonNeumannEntropy (𝒩.complementary.apply (maxMixedState Bool))

/-- Renes–Wilde amplitude classical–quantum channel `W_A(z) = 𝒩(|z⟩⟨z|)`. -/
noncomputable def ampChannel {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d) : CQChannel d where
  out z := 𝒩.apply (CQChannel.ketBraBool z)

/-- Square-root / Stinespring factor `A : Matrix (Bool × d) 𝒩.env ℂ` of the Choi state
`Φ_𝒩 = (id ⊗ 𝒩)(|Φ⁺⟩⟨Φ⁺|)`: `A (a, b) e = (√2)⁻¹ 𝒩.isom (b, e) a`. -/
noncomputable def choiFactor {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d) : Matrix (Bool × d) 𝒩.env ℂ :=
  Matrix.of fun (a, b) e ↦ ((Real.sqrt 2 : ℂ)⁻¹) * 𝒩.isom (b, e) a

/-- Choi state `Φ_𝒩 = (id ⊗ 𝒩)(|Φ⁺⟩⟨Φ⁺|) = A * Aᴴ` of a qubit-input CPTP map `𝒩`. -/
noncomputable def choiState {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d) : DensityOp (Bool × d) where
  mat := choiFactor 𝒩 * (choiFactor 𝒩)ᴴ
  posSemidef := posSemidef_mul_conjTranspose (choiFactor 𝒩)
  trace_one := by
    have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
    have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast; ring
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      choiFactor, Matrix.of_apply, Fintype.sum_prod_type, star_mul', hstar2]
    have hstep : ∀ a : Bool,
        ∑ b : d, ∑ e : 𝒩.env,
          ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b, e) a) *
          ((Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b, e) a)) = (1 / 2 : ℂ) := by
      intro a
      have hiso := congr_fun (congr_fun 𝒩.5 a) a
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, ↓reduceIte,
        Fintype.sum_prod_type] at hiso
      have hfactor : ∑ b : d, ∑ e : 𝒩.env,
          ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b, e) a) *
          ((Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b, e) a)) =
          (1 / 2 : ℂ) * ∑ b : d, ∑ e : 𝒩.env, star (𝒩.isom (b, e) a) * 𝒩.isom (b, e) a := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _
        calc ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b, e) a) * ((Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b, e) a))
            = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (star (𝒩.isom (b, e) a) * 𝒩.isom (b, e) a) := by ring
          _ = _ := by rw [hmul2]
      rw [hfactor, hiso, mul_one]
    simp_rw [hstep]
    simp [Fintype.sum_bool]

/-- Renes–Wilde phase classical–quantum channel `W_P`:
`W_P(0) = Φ_𝒩 = (id ⊗ 𝒩)(|Φ⁺⟩⟨Φ⁺|)` and `W_P(1) = (Z ⊗ I) Φ_𝒩 (Z ⊗ I)`. -/
noncomputable def phaseChannel {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d) : CQChannel (Bool × d) where
  out b := match b with
    | false => choiState 𝒩
    | true => (choiState 𝒩).conjUnitary (pauliZTensorI d)

/-- `((choiFactor 𝒩)ᴴ * choiFactor 𝒩)` equals the transpose of `(𝒩.complementary.apply (maxMixedState Bool)).mat`. -/
lemma choiFactor_conjTranspose_mul_eq {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d) :
    (choiFactor 𝒩)ᴴ * choiFactor 𝒩 = (𝒩.complementary.apply (maxMixedState Bool)).matᵀ := by
  have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
  have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  ext e₁ e₂
  have hL : ((choiFactor 𝒩)ᴴ * choiFactor 𝒩) e₁ e₂ =
      ∑ b : d, ∑ a : Bool, ((Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b, e₁) a)) *
        ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b, e₂) a) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, choiFactor, Matrix.of_apply,
      Fintype.sum_prod_type, star_mul', hstar2]
    rw [Finset.sum_comm]
  have hR : (𝒩.complementary.apply (maxMixedState Bool)).matᵀ e₁ e₂ =
      ∑ b : d, (1 / 2 : ℂ) * (𝒩.isom (b, e₂) true * star (𝒩.isom (b, e₁) true) +
        𝒩.isom (b, e₂) false * star (𝒩.isom (b, e₁) false)) := by
    rw [Matrix.transpose_apply]
    change ∑ b : d, (𝒩.complementary.isom * (maxMixedState Bool).mat *
      𝒩.complementary.isomᴴ) (e₂, b) (e₁, b) = _
    have hM : (maxMixedState Bool).mat = ((2 : ℂ)⁻¹) • (1 : Matrix Bool Bool ℂ) := by
      simp [maxMixedState]
    apply Finset.sum_congr rfl; intro b _
    rw [hM, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply]
    simp only [CPTPMap.complementary, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_bool, smul_eq_mul]
    ring
  rw [hL, hR]
  apply Finset.sum_congr rfl; intro b _
  rw [Fintype.sum_bool]
  calc (Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b, e₁) true) * ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b, e₂) true) +
        (Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b, e₁) false) * ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b, e₂) false)
      = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) *
        (𝒩.isom (b, e₂) true * star (𝒩.isom (b, e₁) true) +
         𝒩.isom (b, e₂) false * star (𝒩.isom (b, e₁) false)) := by ring
    _ = _ := by rw [hmul2]

/-- `S(choiState 𝒩) = S(𝒩.complementary (π₂))`. -/
theorem vonNeumannEntropy_choiState_eq_complementary {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d) :
    vonNeumannEntropy (choiState 𝒩) =
      vonNeumannEntropy (𝒩.complementary.apply (maxMixedState Bool)) := by
  unfold vonNeumannEntropy
  congr 1
  have h1 : ((choiFactor 𝒩 * (choiFactor 𝒩)ᴴ)).IsHermitian := (choiState 𝒩).isHermitian
  have h2 : (((choiFactor 𝒩)ᴴ * choiFactor 𝒩)).IsHermitian := by
    rw [choiFactor_conjTranspose_mul_eq]
    exact (𝒩.complementary.apply (maxMixedState Bool)).isHermitian.transpose
  have h3 := (𝒩.complementary.apply (maxMixedState Bool)).isHermitian
  have hspec1 : ∑ i : Bool × d, Real.negMulLog (h1.eigenvalues i) =
      ∑ j : 𝒩.env, Real.negMulLog (h2.eigenvalues j) :=
    spectral_sum_mul_conjTranspose (choiFactor 𝒩) h1 h2 (by simp [Real.negMulLog])
  have hchar_tr : ((choiFactor 𝒩)ᴴ * choiFactor 𝒩).charpoly * Polynomial.X ^ Fintype.card 𝒩.env =
      (𝒩.complementary.apply (maxMixedState Bool)).mat.charpoly * Polynomial.X ^ Fintype.card 𝒩.env := by
    rw [choiFactor_conjTranspose_mul_eq, Matrix.charpoly_transpose]
  have hspec2 : ∑ j : 𝒩.env, Real.negMulLog (h2.eigenvalues j) =
      ∑ j : 𝒩.env, Real.negMulLog (h3.eigenvalues j) :=
    spectral_sum_eq_of_charpoly_mul_X_pow h2 h3 hchar_tr (by simp [Real.negMulLog])
  exact hspec1.trans hspec2

/-- The midpoint of `ampChannel 𝒩` is `𝒩(maxMixedState Bool)`. -/
lemma ampChannel_midpoint_mat {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d) :
    (DensityOp.midpoint ((ampChannel 𝒩).out false) ((ampChannel 𝒩).out true)).mat =
      (𝒩.apply (maxMixedState Bool)).mat := by
  ext i j
  simp only [DensityOp.midpoint, DensityOp.mix, ampChannel, CPTPMap.apply, CPTPMap.toLinearMap,
    partialTrace₂Mat, CQChannel.ketBraBool, maxMixedState, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Complex.real_smul, Fintype.sum_bool, Fintype.card_bool,
    Nat.cast_ofNat, ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, and_self, and_false,
    false_and, mul_zero, zero_mul, add_zero, zero_add, mul_one,
    Complex.ofReal_inv, Complex.ofReal_ofNat]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro e _
  push_cast; ring

/-- The midpoint of `phaseChannel 𝒩` is the block-diagonal state
`½ |0⟩⟨0| ⊗ 𝒩(|0⟩⟨0|) + ½ |1⟩⟨1| ⊗ 𝒩(|1⟩⟨1|)`. -/
lemma phaseChannel_midpoint_mat {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d) :
    (DensityOp.midpoint ((phaseChannel 𝒩).out false) ((phaseChannel 𝒩).out true)).mat =
      (DensityOp.midpoint
        (DensityOp.tensor (CQChannel.ketBraBool false) ((ampChannel 𝒩).out false))
        (DensityOp.tensor (CQChannel.ketBraBool true) ((ampChannel 𝒩).out true))).mat := by
  have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
  have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  have hZstar : star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) =
      (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) := by
    ext ⟨b₁, x₁⟩ ⟨b₂, x₂⟩
    by_cases h : (b₁, x₁) = (b₂, x₂)
    · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      cases b₁ <;> simp [pauliZTensorI, Matrix.star_apply, Matrix.diagonal_apply]
    · simp [pauliZTensorI, Matrix.star_apply, Matrix.diagonal_apply, h, Ne.symm h]
  have hZ_conj : ∀ (M : Matrix (Bool × d) (Bool × d) ℂ) (a₁ a₂ : Bool) (b₁ b₂ : d),
      ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) * M *
        star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)) (a₁, b₁) (a₂, b₂) =
      (if a₁ = false then (1 : ℂ) else -1) * M (a₁, b₁) (a₂, b₂) *
        (if a₂ = false then (1 : ℂ) else -1) := by
    intro M a₁ a₂ b₁ b₂
    rw [hZstar]
    simp [pauliZTensorI, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  simp only [DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, phaseChannel, ampChannel,
    choiState, DensityOp.conjUnitary, Matrix.add_apply, Matrix.smul_apply, hZ_conj,
    Matrix.kroneckerMap_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, choiFactor,
    CQChannel.ketBraBool, CPTPMap.apply, CPTPMap.toLinearMap, partialTrace₂Mat, Matrix.of_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Complex.real_smul, Fintype.sum_bool, star_mul', hstar2]
  cases a₁ <;> cases a₂
  · simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro e _
    calc ((1 - 1 / 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b₁, e) false *
            ((Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b₂, e) false))) +
          ((1 / 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b₁, e) false *
            ((Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b₂, e) false)))
        = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
          (𝒩.isom (b₁, e) false * star (𝒩.isom (b₂, e) false)) := by push_cast; ring
      _ = _ := by rw [hmul2]; push_cast; ring
  · simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      one_mul, mul_one, mul_neg, neg_mul, mul_zero, zero_mul, add_zero, zero_add]
    push_cast; ring
  · simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      one_mul, mul_one, mul_neg, neg_mul, mul_zero, zero_mul, add_zero, zero_add]
    push_cast; ring
  · simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      one_mul, mul_one, mul_neg, neg_mul, neg_neg, mul_zero, zero_mul, add_zero, zero_add]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro e _
    calc ((1 - 1 / 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b₁, e) true *
            ((Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b₂, e) true))) +
          ((1 / 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b₁, e) true *
            ((Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b₂, e) true)))
        = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
          (𝒩.isom (b₁, e) true * star (𝒩.isom (b₂, e) true)) := by push_cast; ring
      _ = _ := by rw [hmul2]; push_cast; ring

/-- **Renes–Wilde Capacity Identity**:
`I(W_A) + I(W_P) - 1 = I_sym(𝒩)` for every finite-dimensional qubit-input CPTP map `𝒩`. -/
theorem amp_phase_symCapacity_sum {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d) :
    (ampChannel 𝒩).symCapacity + (phaseChannel 𝒩).symCapacity - 1 = symCoherentInfo 𝒩 := by
  unfold CQChannel.symCapacity qjs symCoherentInfo
  have hAm := vonNeumannEntropy_eq_of_mat_eq (ampChannel_midpoint_mat 𝒩)
  have hPm := vonNeumannEntropy_eq_of_mat_eq (phaseChannel_midpoint_mat 𝒩)
  rw [vonNeumannEntropy_block_midpoint] at hPm
  have hP0 : vonNeumannEntropy ((phaseChannel 𝒩).out false) =
      vonNeumannEntropy (𝒩.complementary.apply (maxMixedState Bool)) :=
    vonNeumannEntropy_choiState_eq_complementary 𝒩
  have hP1 : vonNeumannEntropy ((phaseChannel 𝒩).out true) =
      vonNeumannEntropy (𝒩.complementary.apply (maxMixedState Bool)) := by
    change vonNeumannEntropy ((choiState 𝒩).conjUnitary (pauliZTensorI d)) = _
    rw [vonNeumannEntropy_conjUnitary, vonNeumannEntropy_choiState_eq_complementary]
  linarith

/-! ### 3. Polarized Good Sets, Very Noisy Sets, and Dual Unpolarized Fraction -/

/-- Good index set `𝒢_N(W, δ) = {i ∈ Fin (2^n) : Z(W_n^{(i)}) ≤ δ}`. -/
noncomputable def goodSet (W : CQChannel d) (n : ℕ) (δ : ℝ) : Finset (Fin (2 ^ n)) :=
  Finset.univ.filter (fun i ↦ (synthChannel W n i).fidelityParam ≤ δ)

/-- Dual-complement bit-flip on `Fin (2^n)`: maps index `i` with path `b` to path `!b`. -/
def dualIndex (n : ℕ) (i : Fin (2 ^ n)) : Fin (2 ^ n) :=
  (bitPath n).symm (fun k ↦ !(bitPath n i k))

lemma dualIndex_involutive (n : ℕ) (i : Fin (2 ^ n)) :
    dualIndex n (dualIndex n i) = i := by
  simp only [dualIndex, Equiv.apply_symm_apply]
  have h : (fun k ↦ !!(bitPath n i k)) = bitPath n i := by
    funext k; exact Bool.not_not _
  rw [h, Equiv.symm_apply_apply]

lemma dualIndex_bijective (n : ℕ) : Function.Bijective (dualIndex n) :=
  Function.Involutive.bijective (dualIndex_involutive n)

/-- Very noisy index set `ℬ_N(W, δ) = {i ∈ Fin (2^n) : Z((W⊥)_n^{(dualIndex n i)}) ≤ δ}`. -/
noncomputable def veryNoisySet (W : CQChannel d) (n : ℕ) (δ : ℝ) : Finset (Fin (2 ^ n)) :=
  Finset.univ.filter (fun i ↦ (synthChannel W.dual n (dualIndex n i)).fidelityParam ≤ δ)

/-- Unpolarized index set `𝒰_N(W, δ) = (𝒢_N(W, δ) ∪ ℬ_N(W, δ))ᶜ`. -/
noncomputable def unpolarizedSet (W : CQChannel d) (n : ℕ) (δ : ℝ) : Finset (Fin (2 ^ n)) :=
  Finset.univ \ (goodSet W n δ ∪ veryNoisySet W n δ)

lemma goodSet_card_eq_treeProb (W : CQChannel d) (n : ℕ) (δ : ℝ) :
    ((goodSet W n δ).card : ℝ) / (2 : ℝ) ^ n = treeProb n (fun b ↦ polarFidelity W n b ≤ δ) := by
  unfold treeProb treeAvg ind
  dsimp only
  rw [Finset.sum_boole]
  congr 1
  norm_cast
  apply Finset.card_bij (fun i _ ↦ bitPath n i)
  · intro i hi
    simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rwa [← synthChannel_fidelityParam_eq W n i]
  · intro i₁ _ i₂ _ h; exact (bitPath n).injective h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨(bitPath n).symm b, ?_, (bitPath n).apply_symm_apply b⟩
    simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [synthChannel_fidelityParam_eq W n ((bitPath n).symm b), (bitPath n).apply_symm_apply b]
    exact hb

lemma veryNoisySet_card_eq (W : CQChannel d) (n : ℕ) (δ : ℝ) :
    (veryNoisySet W n δ).card = (goodSet W.dual n δ).card := by
  apply Finset.card_bij (fun i _ ↦ dualIndex n i)
  · intro i hi
    simp only [veryNoisySet, goodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi
  · intro i₁ _ i₂ _ h; exact (dualIndex_bijective n).1 h
  · intro j hj
    simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨dualIndex n j, ?_, dualIndex_involutive n j⟩
    simp only [veryNoisySet, Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [dualIndex_involutive]

lemma logb_two_five_fourths_lt_half : Real.logb 2 (5 / 4 : ℝ) < 1 / 2 := by
  rw [Real.logb, div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have h1 : (2 : ℝ) * Real.log (5 / 4 : ℝ) < Real.log 2 := by
    have hpow : Real.log ((5 / 4 : ℝ) ^ (2 : ℕ)) = (2 : ℝ) * Real.log (5 / 4 : ℝ) := by
      rw [Real.log_pow]; norm_num
    rw [← hpow]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- For any threshold `δ ≤ 1/4`, `goodSet W n δ` and `veryNoisySet W n δ` are disjoint. -/
theorem goodSet_disjoint_veryNoisySet (W : CQChannel d) (n : ℕ) {δ : ℝ} (hδ : δ ≤ 1 / 4) :
    Disjoint (goodSet W n δ) (veryNoisySet W n δ) := by
  rw [Finset.disjoint_left]
  intro i hiG hiB
  simp only [goodSet, veryNoisySet, Finset.mem_filter, Finset.mem_univ, true_and] at hiG hiB
  have hH1 : (synthChannel W n i).condEntropy ≤ Real.logb 2 (5 / 4 : ℝ) := by
    have h1 := condEntropy_le_logb_one_add_fidelityParam (synthChannel W n i)
    have h2 : Real.logb 2 (1 + (synthChannel W n i).fidelityParam) ≤ Real.logb 2 (5 / 4 : ℝ) := by
      apply Real.logb_le_logb_of_le (by norm_num)
      · have hnn : 0 ≤ (synthChannel W n i).fidelityParam := rootFidelity_nonneg _ _
        linarith
      · linarith
    exact h1.trans h2
  have hH2 : (synthChannel W.dual n (dualIndex n i)).condEntropy ≤ Real.logb 2 (5 / 4 : ℝ) := by
    have h1 := condEntropy_le_logb_one_add_fidelityParam (synthChannel W.dual n (dualIndex n i))
    have h2 : Real.logb 2 (1 + (synthChannel W.dual n (dualIndex n i)).fidelityParam) ≤
        Real.logb 2 (5 / 4 : ℝ) := by
      apply Real.logb_le_logb_of_le (by norm_num)
      · have hnn : 0 ≤ (synthChannel W.dual n (dualIndex n i)).fidelityParam := rootFidelity_nonneg _ _
        linarith
      · linarith
    exact h1.trans h2
  rw [synthChannel_condEntropy_eq] at hH1 hH2
  have hbp : bitPath n (dualIndex n i) = fun k ↦ !(bitPath n i k) := by
    simp [dualIndex]
  rw [hbp, polarCondEntropy_dual_complement] at hH2
  have hlt := logb_two_five_fourths_lt_half
  linarith

/-- **Dual Unpolarized Fraction Bound**:
When both `W` and `W⊥` polarize to within additive gap `η`, the unpolarized fraction
`|𝒰_N(W, δ)| / N` is at most `2 η`. -/
theorem dual_unpolarized_fraction_le (W : CQChannel d) (n : ℕ) {δ η : ℝ} (hδ : δ ≤ 1 / 4)
    (hW : W.symCapacity - η ≤ ((goodSet W n δ).card : ℝ) / (2 : ℝ) ^ n)
    (hWd : W.dual.symCapacity - η ≤ ((goodSet W.dual n δ).card : ℝ) / (2 : ℝ) ^ n) :
    ((unpolarizedSet W n δ).card : ℝ) / (2 : ℝ) ^ n ≤ 2 * η := by
  have hdisj := goodSet_disjoint_veryNoisySet W n hδ
  have hunion_card : (goodSet W n δ ∪ veryNoisySet W n δ).card =
      (goodSet W n δ).card + (goodSet W.dual n δ).card := by
    rw [Finset.card_union_of_disjoint hdisj, veryNoisySet_card_eq]
  have hsub : (unpolarizedSet W n δ).card + (goodSet W n δ ∪ veryNoisySet W n δ).card = 2 ^ n := by
    unfold unpolarizedSet
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    have hle : (goodSet W n δ ∪ veryNoisySet W n δ).card ≤ 2 ^ n := by
      simpa [Fintype.card_fin] using Finset.card_le_univ (goodSet W n δ ∪ veryNoisySet W n δ)
    omega
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hreal : ((unpolarizedSet W n δ).card : ℝ) / (2 : ℝ) ^ n =
      1 - ((goodSet W n δ).card : ℝ) / (2 : ℝ) ^ n - ((goodSet W.dual n δ).card : ℝ) / (2 : ℝ) ^ n := by
    have hcast : ((unpolarizedSet W n δ).card : ℝ) + ((goodSet W n δ).card : ℝ) +
        ((goodSet W.dual n δ).card : ℝ) = (2 : ℝ) ^ n := by
      have : (unpolarizedSet W n δ).card + ((goodSet W n δ).card + (goodSet W.dual n δ).card) = 2 ^ n := by
        rw [← hunion_card]; exact hsub
      exact_mod_cast (by omega : (unpolarizedSet W n δ).card + (goodSet W n δ).card + (goodSet W.dual n δ).card = 2 ^ n)
    field_simp [ne_of_gt hpow_pos]
    linarith
  have hcap_dual : W.symCapacity + W.dual.symCapacity = 1 := prop_2_2_D1_symCapacity W
  linarith

end QuantumPolarCoding

end PolarCodes
