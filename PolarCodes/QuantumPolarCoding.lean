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

Formalizes Section 5.3 / Corollary 5.5 of *Polynomial-Blocklength Quantum Polar Codes
via Nonlinear Dephasing Contraction* (Renes–Wilde [10] reduction):

1. **Qubit-input quantum channels**: `symCoherentInfo 𝒩` for any finite-dimensional
   CPTP map `𝒩 : CPTPMap Bool d`, complementary channel `𝒩.complementary`, and
   degradability `𝒩.IsDegradable`.
2. **Amplitude and phase c-q channels (`W_A, W_P`)**:
   - `ampChannel 𝒩` (`z ↦ 𝒩(|z⟩⟨z|)`)
   - `choiState 𝒩` (`(id ⊗ 𝒩)(|Φ⁺⟩⟨Φ⁺|)`) and `phaseChannel 𝒩` (`0 ↦ choiState 𝒩`, `1 ↦ (Z ⊗ I) choiState 𝒩 (Z ⊗ I)`)
   - `amp_phase_symCapacity_sum`: exact identity `I(W_A) + I(W_P) - 1 = I_sym(𝒩)`.
3. **Dual unpolarized fraction & degradable vanishing assistance**:
   - `CPTPMap.tensor`, `CPTPMap.idBoolTensor`, `CQChannel.DegradedTo`, and preservation of
     degradation and channel equivalence under `checkCombine`, `varCombine`, and `polarChannelTree`
   - `polarCondEntropy_dual_complement`: `H((W⊥)_n^{(!b)}) = 1 - H(W_n^{(b)})`
   - `dual_unpolarized_fraction_le`: unpolarized fraction `≤ ε / 2` when applying Theorem 1.1 with
     `ε' = ε / 4` to `W` and `W⊥`
   - `degradable_amp_phase_sum_le_one` and `degradable_vanishing_assistance`: for degradable `𝒩`,
     `H((W_A)_n^{(b)}) + H((W_P)_n^{(!b)}) ≤ 1`, forcing the entanglement / secret-key assistance
     set to lie inside the unpolarized set of fraction `≤ ε / 2`.
4. **CSS / private polar coding scheme & Corollary 5.5**:
   - `CSSPrivatePolarCode 𝒩 n` combining amplitude and phase QSC polar codes on the shared
     information set `𝒜 = 𝒢_N(W_A) ∩ dualIndex(𝒢_N(W_P))`
   - `corollary_5_5_quantum_private_polar_coding`: polynomial blocklength `N = 2^n ≥ C₀ (1/ε)^μ`,
     rate `R ≥ I_sym(𝒩) - ε / 2`, combined decoding + secrecy error `≤ 2 · 2^{-N^{0.49}}`,
     unpolarized fraction `≤ ε / 2`, and vanishing assistance rate `≤ ε / 2` for degradable channels.
-/

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodes

universe u

section QuantumPolarCoding

variable {d : Type u} [Fintype d] [DecidableEq d]

/-! ### 1. Tensor Product of CPTP Maps and Preservation of Degradation / Channel Equivalence -/

/-- Tensor product `𝒟₁ ⊗ 𝒟₂` of two CPTP maps. -/
noncomputable def CPTPMap.tensor {α₁ β₁ α₂ β₂ : Type u}
    [Fintype α₁] [DecidableEq α₁] [Fintype β₁] [DecidableEq β₁]
    [Fintype α₂] [DecidableEq α₂] [Fintype β₂] [DecidableEq β₂]
    (𝒟₁ : CPTPMap.{u} α₁ β₁) (𝒟₂ : CPTPMap.{u} α₂ β₂) :
    CPTPMap.{u} (α₁ × α₂) (β₁ × β₂) where
  env := 𝒟₁.env × 𝒟₂.env
  fintypeEnv := inferInstance
  decEqEnv := inferInstance
  isom := Matrix.of fun ((b₁, b₂), (e₁, e₂)) (a₁, a₂) ↦
    𝒟₁.isom (b₁, e₁) a₁ * 𝒟₂.isom (b₂, e₂) a₂
  isometry := by
    ext ⟨a₁, a₂⟩ ⟨a₁', a₂'⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply, star_mul']
    have h1 := congr_fun (congr_fun 𝒟₁.isometry a₁) a₁'
    have h2 := congr_fun (congr_fun 𝒟₂.isometry a₂) a₂'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.one_apply] at h1 h2
    calc ∑ b₁ : β₁, ∑ b₂ : β₂, ∑ e₁ : 𝒟₁.env, ∑ e₂ : 𝒟₂.env,
          (star (𝒟₂.isom (b₂, e₂) a₂) * star (𝒟₁.isom (b₁, e₁) a₁)) *
          (𝒟₁.isom (b₁, e₁) a₁' * 𝒟₂.isom (b₂, e₂) a₂')
        = (∑ b₁ : β₁, ∑ e₁ : 𝒟₁.env, star (𝒟₁.isom (b₁, e₁) a₁) * 𝒟₁.isom (b₁, e₁) a₁') *
          (∑ b₂ : β₂, ∑ e₂ : 𝒟₂.env, star (𝒟₂.isom (b₂, e₂) a₂) * 𝒟₂.isom (b₂, e₂) a₂') := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro b₁ _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro b₂ _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro e₁ _
            apply Finset.sum_congr rfl; intro e₂ _
            ring
      _ = (if a₁ = a₁' then (1 : ℂ) else 0) * (if a₂ = a₂' then (1 : ℂ) else 0) := by
            rw [h1, h2]
      _ = if (a₁, a₂) = (a₁', a₂') then 1 else 0 := by
            by_cases ha1 : a₁ = a₁' <;> by_cases ha2 : a₂ = a₂' <;> simp [ha1, ha2]

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
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, star_mul']
  have hterm : ∀ (e₁ : 𝒟₁.env) (e₂ : 𝒟₂.env),
      ∑ a₁' : α₁, ∑ a₂' : α₂,
        (∑ a₁ : α₁, ∑ a₂ : α₂,
          𝒟₁.isom (b₁, e₁) a₁ * 𝒟₂.isom (b₂, e₂) a₂ * (ρ₁.mat a₁ a₁' * ρ₂.mat a₂ a₂')) *
        (star (𝒟₂.isom (b₂', e₂) a₂') * star (𝒟₁.isom (b₁', e₁) a₁')) =
      (∑ a₁' : α₁, (∑ a₁ : α₁, 𝒟₁.isom (b₁, e₁) a₁ * ρ₁.mat a₁ a₁') * star (𝒟₁.isom (b₁', e₁) a₁')) *
      (∑ a₂' : α₂, (∑ a₂ : α₂, 𝒟₂.isom (b₂, e₂) a₂ * ρ₂.mat a₂ a₂') * star (𝒟₂.isom (b₂', e₂) a₂')) := by
    intro e₁ e₂
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a₁' _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a₂' _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a₁ _
    apply Finset.sum_congr rfl; intro a₂ _
    ring
  simp_rw [hterm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro e₁ _
  rw [Finset.mul_sum]

/-- Identity-on-`Bool` tensored with a CPTP map `𝒟`: `id_Bool ⊗ 𝒟 : CPTPMap (Bool × α) (Bool × β)`. -/
noncomputable def CPTPMap.idBoolTensor {α β : Type u} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (𝒟 : CPTPMap.{u} α β) :
    CPTPMap.{u} (Bool × α) (Bool × β) where
  env := 𝒟.env
  fintypeEnv := inferInstance
  decEqEnv := inferInstance
  isom := Matrix.of fun ((w, b), e) (w', a) ↦ if w = w' then 𝒟.isom (b, e) a else 0
  isometry := by
    ext ⟨w₁, a₁⟩ ⟨w₂, a₂⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
    by_cases hw : w₁ = w₂
    · subst hw
      rw [Finset.sum_eq_single w₁]
      · simp only [↓reduceIte, Prod.mk.injEq, true_and]
        have h := congr_fun (congr_fun 𝒟.isometry a₁) a₂
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
      · simp [h1]

/-- `(id_Bool ⊗ 𝒟)(|w⟩⟨w| ⊗ ρ) = |w⟩⟨w| ⊗ 𝒟(ρ)`. -/
lemma CPTPMap.idBoolTensor_apply_ketBra {α β : Type u} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (𝒟 : CPTPMap.{u} α β) (w : Bool) (ρ : DensityOp α) :
    (𝒟.idBoolTensor.apply (DensityOp.tensor (CQChannel.ketBraBool w) ρ)).mat =
      (DensityOp.tensor (CQChannel.ketBraBool w) (𝒟.apply ρ)).mat := by
  ext ⟨w₁, b₁⟩ ⟨w₂, b₂⟩
  unfold CPTPMap.apply CPTPMap.toLinearMap CPTPMap.idBoolTensor partialTrace₂Mat
    DensityOp.tensor CQChannel.ketBraBool
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  by_cases h1 : w₁ = w
  · subst h1
    by_cases h2 : w₂ = w₁
    · subst h2
      simp only [↓reduceIte, and_self, one_mul]
      apply Finset.sum_congr rfl; intro e _
      rw [Finset.sum_eq_single w₁]
      · apply Finset.sum_congr rfl; intro a' _
        rw [Finset.sum_eq_single w₁]
        · simp
        · intro w' _ hne; apply Finset.sum_eq_zero; intro a _; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ w₁) h
      · intro w' _ hne; apply Finset.sum_eq_zero; intro a' _; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ w₁) h
    · simp only [h2, and_false, ↓reduceIte, zero_mul]
      apply Finset.sum_eq_zero; intro e _
      apply Finset.sum_eq_zero; intro w' _
      apply Finset.sum_eq_zero; intro a' _
      by_cases hw' : w₂ = w'
      · subst hw'
        have hne : ¬ (w₂ = w₁) := h2
        simp [hne]
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
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.real_smul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro e _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
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
      cases W₂; congr; funext b; apply DensityOp.ext; exact h𝒟 b
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
  have h1' : 𝒟₁.apply (W₁.out b) = W₂.out b := DensityOp.ext (h₁ b)
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
    apply DensityOp.ext
    rw [CPTPMap.tensor_apply_tensor]
    rw [DensityOp.ext (h𝒟₁ b), DensityOp.ext (h𝒟₂ false)]
  have hd2 : (𝒟₁.tensor 𝒟₂).apply (DensityOp.tensor (W₁.out (!b)) (W₂.out true)) =
      DensityOp.tensor (W₁'.out (!b)) (W₂'.out true) := by
    apply DensityOp.ext
    rw [CPTPMap.tensor_apply_tensor]
    rw [DensityOp.ext (h𝒟₁ (!b)), DensityOp.ext (h𝒟₂ true)]
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
    apply DensityOp.ext
    rw [CPTPMap.idBoolTensor_apply_ketBra]
    have hinner : (𝒟₁.tensor 𝒟₂).apply (DensityOp.tensor (W₁.out b) (W₂.out b)) =
        DensityOp.tensor (W₁'.out b) (W₂'.out b) := by
      apply DensityOp.ext; rw [CPTPMap.tensor_apply_tensor, DensityOp.ext (h𝒟₁ b), DensityOp.ext (h𝒟₂ b)]
    rw [hinner]
  have hd2 : (𝒟₁.tensor 𝒟₂).idBoolTensor.apply
      (DensityOp.tensor (CQChannel.ketBraBool true) (DensityOp.tensor (W₁.out (!b)) (W₂.out b))) =
      DensityOp.tensor (CQChannel.ketBraBool true) (DensityOp.tensor (W₁'.out (!b)) (W₂'.out b)) := by
    apply DensityOp.ext
    rw [CPTPMap.idBoolTensor_apply_ketBra]
    have hinner : (𝒟₁.tensor 𝒟₂).apply (DensityOp.tensor (W₁.out (!b)) (W₂.out b)) =
        DensityOp.tensor (W₁'.out (!b)) (W₂'.out b) := by
      apply DensityOp.ext; rw [CPTPMap.tensor_apply_tensor, DensityOp.ext (h𝒟₁ (!b)), DensityOp.ext (h𝒟₂ b)]
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
    have h1 : (fun k : Fin (n + 1) ↦ !(b k)) =
        Fin.snoc (α := fun _ ↦ Bool) (fun k : Fin n ↦ !(Fin.init b k)) (!(b (Fin.last n))) := by
      funext k
      refine Fin.lastCases ?_ ?_ k
      · simp
      · intro j; simp [Fin.init]
    have h2 : b = Fin.snoc (α := fun _ ↦ Bool) (Fin.init b) (b (Fin.last n)) :=
      (Fin.snoc_init_self b).symm
    rw [h1]
    conv_rhs => rw [h2]
    have ih := polarChannelTree_dual_complement_channelEquiv W n (Fin.init b)
    cases b (Fin.last n)
    · simp only [Bool.not_false, polarChannelTree_snoc_true, polarChannelTree_snoc_false,
        BundledCQChannel.plus, BundledCQChannel.minus, CQChannel.plusChannel, CQChannel.minusChannel]
      exact (ih.varCombine ih).trans (prop_2_2_D2_check_channelEquiv _ _).symm
    · simp only [Bool.not_true, polarChannelTree_snoc_false, polarChannelTree_snoc_true,
        BundledCQChannel.plus, BundledCQChannel.minus, CQChannel.plusChannel, CQChannel.minusChannel]
      exact (ih.checkCombine ih).trans (prop_2_2_D2_var_channelEquiv _ _).symm

/-- Exact entropy duality along the polarization tree: `H((W⊥)_n^{(!b)}) = 1 - H(W_n^{(b)})`. -/
theorem polarCondEntropy_dual_complement (W : CQChannel d) (n : ℕ) (b : Fin n → Bool) :
    polarCondEntropy W.dual n (fun k ↦ !(b k)) = 1 - polarCondEntropy W n b := by
  unfold polarCondEntropy
  rw [(polarChannelTree_dual_complement_channelEquiv W n b).condEntropy_eq]
  linarith [prop_2_2_D1 (polarChannelTree W n b).ch]

/-! ### 2. Symmetric Coherent / Private Information and Renes–Wilde Amplitude & Phase Channels -/

/-- Symmetric coherent (and, for degradable channels, symmetric private) information
`I_sym(𝒩) = S(𝒩(π₂)) - S(𝒩^c(π₂))` of a qubit-input CPTP map `𝒩 : CPTPMap Bool d`. -/
noncomputable def symCoherentInfo (𝒩 : CPTPMap.{0} Bool d) : ℝ :=
  vonNeumannEntropy (𝒩.apply (maxMixedState Bool)) -
    vonNeumannEntropy (𝒩.complementary.apply (maxMixedState Bool))

/-- Renes–Wilde amplitude classical–quantum channel `W_A(z) = 𝒩(|z⟩⟨z|)`. -/
noncomputable def ampChannel (𝒩 : CPTPMap.{0} Bool d) : CQChannel d where
  out z := 𝒩.apply (CQChannel.ketBraBool z)

/-- Square-root / Stinespring factor `A : Matrix (Bool × d) 𝒩.env ℂ` of the Choi state
`Φ_𝒩 = (id ⊗ 𝒩)(|Φ⁺⟩⟨Φ⁺|)`: `A (a, b) e = (√2)⁻¹ 𝒩.isom (b, e) a`. -/
noncomputable def choiFactor (𝒩 : CPTPMap.{0} Bool d) : Matrix (Bool × d) 𝒩.env ℂ :=
  Matrix.of fun (a, b) e ↦ ((Real.sqrt 2 : ℂ)⁻¹) * 𝒩.isom (b, e) a

/-- Choi state `Φ_𝒩 = (id ⊗ 𝒩)(|Φ⁺⟩⟨Φ⁺|) = A * Aᴴ` of a qubit-input CPTP map `𝒩`. -/
noncomputable def choiState (𝒩 : CPTPMap.{0} Bool d) : DensityOp (Bool × d) where
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
      have hiso := congr_fun (congr_fun 𝒩.isometry a) a
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
    ring

/-- Renes–Wilde phase classical–quantum channel `W_P`:
`W_P(0) = Φ_𝒩 = (id ⊗ 𝒩)(|Φ⁺⟩⟨Φ⁺|)` and `W_P(1) = (Z ⊗ I) Φ_𝒩 (Z ⊗ I)`. -/
noncomputable def phaseChannel (𝒩 : CPTPMap.{0} Bool d) : CQChannel (Bool × d) where
  out b := match b with
    | false => choiState 𝒩
    | true => (choiState 𝒩).conjUnitary (pauliZTensorI d)

/-- `((choiFactor 𝒩)ᴴ * choiFactor 𝒩)` equals the transpose of `(𝒩.complementary.apply (maxMixedState Bool)).mat`. -/
lemma choiFactor_conjTranspose_mul_eq (𝒩 : CPTPMap.{0} Bool d) :
    (choiFactor 𝒩)ᴴ * choiFactor 𝒩 = (𝒩.complementary.apply (maxMixedState Bool)).matᵀ := by
  have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
  have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  ext e₁ e₂
  simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    choiFactor, Matrix.of_apply, Fintype.sum_prod_type, star_mul', hstar2,
    CPTPMap.apply, CPTPMap.complementary, CPTPMap.toLinearMap, partialTrace₂Mat,
    maxMixedState, Matrix.smul_apply, Matrix.one_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Complex.real_smul, Fintype.card_bool, Nat.cast_ofNat]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true,
    smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add, mul_one,
    Complex.ofReal_inv, Complex.ofReal_ofNat]
  calc (Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b, e₁) true) * ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b, e₂) true) +
        (Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b, e₁) false) * ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b, e₂) false)
      = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) *
        (𝒩.isom (b, e₂) true * star (𝒩.isom (b, e₁) true) +
         𝒩.isom (b, e₂) false * star (𝒩.isom (b, e₁) false)) := by ring
    _ = _ := by rw [hmul2]; ring

/-- `S(choiState 𝒩) = S(𝒩.complementary (π₂))`. -/
theorem vonNeumannEntropy_choiState_eq_complementary (𝒩 : CPTPMap.{0} Bool d) :
    vonNeumannEntropy (choiState 𝒩) =
      vonNeumannEntropy (𝒩.complementary.apply (maxMixedState Bool)) := by
  unfold vonNeumannEntropy
  have h1 : ((choiFactor 𝒩 * (choiFactor 𝒩)ᴴ)).IsHermitian := (choiState 𝒩).isHermitian
  have h2 : (((choiFactor 𝒩)ᴴ * choiFactor 𝒩)).IsHermitian := by
    rw [choiFactor_conjTranspose_mul_eq]
    exact (𝒩.complementary.apply (maxMixedState Bool)).isHermitian.transpose
  have h3 := (𝒩.complementary.apply (maxMixedState Bool)).isHermitian
  have hspec1 : ∑ i : Bool × d, negMulLog2 (h1.eigenvalues i) =
      ∑ j : 𝒩.env, negMulLog2 (h2.eigenvalues j) :=
    spectral_sum_mul_conjTranspose (choiFactor 𝒩) h1 h2 (by simp [negMulLog2])
  have hchar_tr : ((choiFactor 𝒩)ᴴ * choiFactor 𝒩).charpoly * Polynomial.X ^ Fintype.card 𝒩.env =
      (𝒩.complementary.apply (maxMixedState Bool)).mat.charpoly * Polynomial.X ^ Fintype.card 𝒩.env := by
    rw [choiFactor_conjTranspose_mul_eq, Matrix.charpoly_transpose]
  have hspec2 : ∑ j : 𝒩.env, negMulLog2 (h2.eigenvalues j) =
      ∑ j : 𝒩.env, negMulLog2 (h3.eigenvalues j) :=
    spectral_sum_eq_of_charpoly_mul_X_pow h2 h3 hchar_tr (by simp [negMulLog2])
  exact hspec1.trans hspec2

/-- The midpoint of `ampChannel 𝒩` is `𝒩(maxMixedState Bool)`. -/
lemma ampChannel_midpoint_mat (𝒩 : CPTPMap.{0} Bool d) :
    (DensityOp.midpoint ((ampChannel 𝒩).out false) ((ampChannel 𝒩).out true)).mat =
      (𝒩.apply (maxMixedState Bool)).mat := by
  ext i j
  simp only [DensityOp.midpoint, DensityOp.mix, ampChannel, CPTPMap.apply, CPTPMap.toLinearMap,
    partialTrace₂Mat, CQChannel.ketBraBool, maxMixedState, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Complex.real_smul, Fintype.sum_bool, Fintype.card_bool,
    Nat.cast_ofNat, ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, mul_zero, zero_mul,
    add_zero, zero_add, mul_one, Complex.ofReal_inv, Complex.ofReal_ofNat]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [← mul_add, ← add_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro e _
  push_cast; ring

/-- The midpoint of `phaseChannel 𝒩` is the block-diagonal state
`½ |0⟩⟨0| ⊗ 𝒩(|0⟩⟨0|) + ½ |1⟩⟨1| ⊗ 𝒩(|1⟩⟨1|)`. -/
lemma phaseChannel_midpoint_mat (𝒩 : CPTPMap.{0} Bool d) :
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
  ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  simp only [DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, phaseChannel, ampChannel,
    choiState, DensityOp.conjUnitary, hZstar, pauliZTensorI, Matrix.add_apply, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, choiFactor, CQChannel.ketBraBool, CPTPMap.apply,
    CPTPMap.toLinearMap, partialTrace₂Mat, Matrix.of_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Complex.real_smul, Fintype.sum_bool, star_mul', hstar2]
  cases a₁ <;> cases a₂
  · simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, one_mul, mul_one, mul_zero,
      zero_mul, add_zero, zero_add]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro e _
    calc (1 - 1 / 2 : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b₁, e) false *
            ((Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b₂, e) false))) +
          (1 / 2 : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b₁, e) false *
            ((Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b₂, e) false)))
        = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
          (𝒩.isom (b₁, e) false * star (𝒩.isom (b₂, e) false)) := by ring
      _ = _ := by rw [hmul2]; push_cast; ring
  · simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, one_mul, mul_one, mul_neg,
      neg_mul, mul_zero, zero_mul, add_zero, zero_add]
    push_cast; ring
  · simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, one_mul, mul_one, mul_neg,
      neg_mul, mul_zero, zero_mul, add_zero, zero_add]
    push_cast; ring
  · simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, one_mul, mul_one, mul_neg,
      neg_mul, neg_neg, mul_zero, zero_mul, add_zero, zero_add]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro e _
    calc (1 - 1 / 2 : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b₁, e) true *
            ((Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b₂, e) true))) +
          (1 / 2 : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (b₁, e) true *
            ((Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (b₂, e) true)))
        = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
          (𝒩.isom (b₁, e) true * star (𝒩.isom (b₂, e) true)) := by ring
      _ = _ := by rw [hmul2]; push_cast; ring

/-- **Renes–Wilde Capacity Identity**:
`I(W_A) + I(W_P) - 1 = I_sym(𝒩)` for every finite-dimensional qubit-input CPTP map `𝒩`. -/
theorem amp_phase_symCapacity_sum (𝒩 : CPTPMap.{0} Bool d) :
    (ampChannel 𝒩).symCapacity + (phaseChannel 𝒩).symCapacity - 1 = symCoherentInfo 𝒩 := by
  unfold CQChannel.symCapacity CQChannel.condEntropy qjs symCoherentInfo
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
  unfold treeProb
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
    rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
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

/-! ### 4. Degradable Vanishing Assistance (Renes–Wilde [10]) -/

/-- For a degradable qubit-input CPTP map `𝒩`, `ampChannel 𝒩` degrades to `ampChannel 𝒩.complementary`. -/
lemma degradable_ampChannel_degradedTo {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap.{0} Bool d) (hdeg : 𝒩.IsDegradable) :
    (ampChannel 𝒩).DegradedTo (ampChannel 𝒩.complementary) := by
  rcases hdeg with ⟨𝒟, h𝒟⟩
  exact ⟨𝒟, fun b ↦ h𝒟 (CQChannel.ketBraBool b)⟩

/-- Transpose of a density operator `ρᵀ`. -/
def DensityOp.transpose {α : Type*} [Fintype α] [DecidableEq α] (ρ : DensityOp α) : DensityOp α where
  mat := ρ.matᵀ
  posSemidef := ρ.posSemidef.transpose
  trace_one := by simp [Matrix.trace_transpose, ρ.trace_one]

/-- Transpose of a c-q channel: `Wᵀ(b) = (W(b))ᵀ`. -/
def CQChannel.transpose {α : Type*} [Fintype α] [DecidableEq α] (W : CQChannel α) : CQChannel α where
  out b := (W.out b).transpose

/-- Symmetrized version of a c-q channel: `W_sym(b) = ½ |0⟩⟨0| ⊗ W(b) + ½ |1⟩⟨1| ⊗ W(!b)`. -/
noncomputable def CQChannel.symmetrize {α : Type*} [Fintype α] [DecidableEq α] (W : CQChannel α) :
    CQChannel (Bool × α) where
  out b := DensityOp.midpoint
    (DensityOp.tensor (CQChannel.ketBraBool false) (W.out b))
    (DensityOp.tensor (CQChannel.ketBraBool true) (W.out (!b)))

lemma vonNeumannEntropy_transpose {α : Type*} [Fintype α] [DecidableEq α] (ρ : DensityOp α) :
    vonNeumannEntropy ρ.transpose = vonNeumannEntropy ρ := by
  unfold vonNeumannEntropy
  have hchar : ρ.transpose.mat.charpoly * Polynomial.X ^ Fintype.card α =
      ρ.mat.charpoly * Polynomial.X ^ Fintype.card α := by
    simp [DensityOp.transpose, Matrix.charpoly_transpose]
  exact spectral_sum_eq_of_charpoly_mul_X_pow ρ.transpose.isHermitian ρ.isHermitian hchar
    (by simp [negMulLog2])

/-- Transpose commutes with `polarChannelTree` (up to exact matrix transpose on outputs). -/
lemma polarChannelTree_transpose_condEntropy {α : Type u} [Fintype α] [DecidableEq α]
    (W : CQChannel α) :
    ∀ (n : ℕ) (b : Fin n → Bool),
      polarCondEntropy W.transpose n b = polarCondEntropy W n b := by
  have hmat : ∀ (n : ℕ) (b : Fin n → Bool),
      ∃ e : (polarChannelTree W.transpose n b).dim ≃ (polarChannelTree W n b).dim,
        ∀ (z : Bool) (x y : (polarChannelTree W.transpose n b).dim),
          ((polarChannelTree W.transpose n b).ch.out z).mat x y =
            ((polarChannelTree W n b).ch.out z).mat (e y) (e x) := by
    intro n
    induction n with
    | zero =>
      intro b
      refine ⟨Equiv.refl α, fun z x y ↦ rfl⟩
    | succ n ih =>
      intro b
      have hsnoc : b = Fin.snoc (α := fun _ ↦ Bool) (Fin.init b) (b (Fin.last n)) :=
        (Fin.snoc_init_self b).symm
      rw [hsnoc]
      obtain ⟨e, he⟩ := ih (Fin.init b)
      cases b (Fin.last n)
      · rw [polarChannelTree_snoc_false, polarChannelTree_snoc_false]
        refine ⟨e.prodCongr e, fun z ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ↦ ?_⟩
        simp only [BundledCQChannel.minus, CQChannel.minusChannel, CQChannel.checkCombine,
          DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply,
          Matrix.kroneckerMap_apply, Equiv.prodCongr_apply, Prod.map_apply, he]
      · rw [polarChannelTree_snoc_true, polarChannelTree_snoc_true]
        refine ⟨(Equiv.refl Bool).prodCongr (e.prodCongr e), fun z ⟨w₁, x₁, x₂⟩ ⟨w₂, y₁, y₂⟩ ↦ ?_⟩
        simp only [BundledCQChannel.plus, CQChannel.plusChannel, CQChannel.varCombine,
          DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, CQChannel.ketBraBool,
          Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.of_apply,
          Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map_apply, he]
        cases w₁ <;> cases w₂ <;> simp
  intro n b
  obtain ⟨e, he⟩ := hmat n b
  unfold polarCondEntropy CQChannel.condEntropy qjs
  have hS : ∀ (ρ : DensityOp (polarChannelTree W.transpose n b).dim)
      (σ : DensityOp (polarChannelTree W n b).dim),
      (∀ x y, ρ.mat x y = σ.mat (e y) (e x)) →
      vonNeumannEntropy ρ = vonNeumannEntropy σ := by
    intro ρ σ h
    rw [← vonNeumannEntropy_transpose σ]
    exact (vonNeumannEntropy_of_reindex e ρ σ.transpose (fun x y ↦ (h x y).symm)).symm
  have hS0 := hS _ _ (he false)
  have hS1 := hS _ _ (he true)
  have hSm := hS
    (DensityOp.midpoint ((polarChannelTree W.transpose n b).ch.out false)
      ((polarChannelTree W.transpose n b).ch.out true))
    (DensityOp.midpoint ((polarChannelTree W n b).ch.out false)
      ((polarChannelTree W n b).ch.out true))
    (fun x y ↦ by simp only [DensityOp.midpoint, DensityOp.mix, Matrix.add_apply, Matrix.smul_apply, he])
  linarith

/-- `W.symmetrize` has the same conditional entropy as `W`. -/
lemma condEntropy_symmetrize {α : Type*} [Fintype α] [DecidableEq α] (W : CQChannel α) :
    W.symmetrize.condEntropy = W.condEntropy := by
  unfold CQChannel.condEntropy CQChannel.symmetrize qjs
  have h0 : vonNeumannEntropy (DensityOp.midpoint
      (DensityOp.tensor (CQChannel.ketBraBool false) (W.out false))
      (DensityOp.tensor (CQChannel.ketBraBool true) (W.out true))) =
      1 + (vonNeumannEntropy (W.out false) + vonNeumannEntropy (W.out true)) / 2 :=
    vonNeumannEntropy_block_midpoint (W.out false) (W.out true)
  have h1 : vonNeumannEntropy (DensityOp.midpoint
      (DensityOp.tensor (CQChannel.ketBraBool false) (W.out true))
      (DensityOp.tensor (CQChannel.ketBraBool true) (W.out false))) =
      1 + (vonNeumannEntropy (W.out true) + vonNeumannEntropy (W.out false)) / 2 :=
    vonNeumannEntropy_block_midpoint (W.out true) (W.out false)
  have hmid : (DensityOp.midpoint
      (DensityOp.midpoint (DensityOp.tensor (CQChannel.ketBraBool false) (W.out false))
        (DensityOp.tensor (CQChannel.ketBraBool true) (W.out true)))
      (DensityOp.midpoint (DensityOp.tensor (CQChannel.ketBraBool false) (W.out true))
        (DensityOp.tensor (CQChannel.ketBraBool true) (W.out false)))).mat =
      (DensityOp.midpoint
        (DensityOp.tensor (CQChannel.ketBraBool false) (DensityOp.midpoint (W.out false) (W.out true)))
        (DensityOp.tensor (CQChannel.ketBraBool true) (DensityOp.midpoint (W.out false) (W.out true)))).mat := by
    ext ⟨a₁, i₁⟩ ⟨a₂, i₂⟩
    simp only [DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, CQChannel.ketBraBool,
      Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.of_apply, Complex.real_smul]
    cases a₁ <;> cases a₂ <;> simp <;> push_cast <;> ring
  have hSm := vonNeumannEntropy_eq_of_mat_eq hmid
  rw [vonNeumannEntropy_block_midpoint] at hSm
  linarith

/-- `W.symmetrize` commutes with `minusChannel` up to `ChannelEquiv`. -/
lemma symmetrize_minusChannel_channelEquiv {α : Type u} [Fintype α] [DecidableEq α]
    (W : CQChannel α) :
    W.symmetrize.minusChannel.ChannelEquiv W.minusChannel.symmetrize := by
  let e : (ULift.{u} Bool × (Bool × (α × α))) ≃ ((Bool × α) × (Bool × α)) :=
    { toFun := fun ⟨⟨w₂⟩, w, x₁, x₂⟩ ↦ ((xor w w₂, x₁), (w₂, x₂))
      invFun := fun ⟨(w₁, x₁), (w₂, x₂)⟩ ↦ (ULift.up w₂, xor w₁ w₂, x₁, x₂)
      left_inv := fun ⟨⟨w₂⟩, w, x₁, x₂⟩ ↦ by
        simp only [Prod.mk.injEq, true_and, and_true]
        cases w <;> cases w₂ <;> rfl
      right_inv := fun ⟨(w₁, x₁), (w₂, x₂)⟩ ↦ by
        simp only [Prod.mk.injEq, true_and, and_true]
        cases w₁ <;> cases w₂ <;> rfl }
  let P : Matrix ((Bool × α) × (Bool × α)) (ULift.{u} Bool × (Bool × (α × α))) ℂ :=
    Matrix.of fun r c ↦ if r = e c then 1 else 0
  have hP_iso : Pᴴ * P = 1 := by
    ext c₁ c₂
    simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (e c₁)]
    · by_cases h : c₁ = c₂
      · subst h; simp
      · have he : e c₁ ≠ e c₂ := fun h' ↦ h (e.injective h')
        simp [h, he]
    · intro r _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ (e c₁)) h
  have hiso : (W.minusChannel.symmetrize.tensorMaxMixed (ULift.{u} Bool)).IsoEquiv
      W.symmetrize.minusChannel := by
    refine ⟨(Bool × α) × (Bool × α), inferInstance, inferInstance, P, 1, hP_iso, by simp, ?_⟩
    intro b
    rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
    ext ⟨⟨w₁, i₁⟩, ⟨w₂, i₂⟩⟩ ⟨⟨w₁', j₁⟩, ⟨w₂', j₂⟩⟩
    conv_lhs =>
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, P, Matrix.of_apply]
    rw [Finset.sum_eq_single (e.symm ((w₁', j₁), (w₂', j₂)))]
    · rw [Finset.sum_eq_single (e.symm ((w₁, i₁), (w₂, i₂)))]
      · simp only [Equiv.apply_symm_apply, ↓reduceIte, one_mul, star_one, mul_one, e,
          Equiv.coe_fn_symm_mk, CQChannel.tensorMaxMixed, CQChannel.minusChannel,
          CQChannel.checkCombine, CQChannel.symmetrize, DensityOp.midpoint, DensityOp.mix,
          DensityOp.tensor, CQChannel.ketBraBool, maxMixedState, Matrix.add_apply,
          Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply,
          Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, Fintype.card_ulift,
          Fintype.card_bool, Nat.cast_ofNat]
        cases b <;> cases w₁ <;> cases w₂ <;> cases w₁' <;> cases w₂' <;>
          simp <;> push_cast <;> ring
      · intro c _ hne
        have : ((w₁, i₁), (w₂, i₂)) ≠ e c := fun h ↦ hne (by rw [h, e.symm_apply_apply]).symm
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro c _ hne
      have : ((w₁', j₁), (w₂', j₂)) ≠ e c := fun h ↦ hne (by rw [h, e.symm_apply_apply]).symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact ((W.minusChannel.symmetrize.channelEquiv_tensorMaxMixed (ULift.{u} Bool)).trans
    hiso.toChannelEquiv).symm

/-- `W.symmetrize` commutes with `plusChannel` up to `ChannelEquiv`. -/
lemma symmetrize_plusChannel_channelEquiv {α : Type u} [Fintype α] [DecidableEq α]
    (W : CQChannel α) :
    W.symmetrize.plusChannel.ChannelEquiv W.plusChannel.symmetrize := by
  let e : (ULift.{u} Bool × (Bool × (Bool × (α × α)))) ≃ (Bool × ((Bool × α) × (Bool × α))) :=
    { toFun := fun ⟨⟨w₁⟩, w, u', x₁, x₂⟩ ↦ (xor u' (xor w₁ w), ((w₁, x₁), (w, x₂)))
      invFun := fun ⟨u, (w₁, x₁), (w₂, x₂)⟩ ↦ (ULift.up w₁, w₂, xor u (xor w₁ w₂), x₁, x₂)
      left_inv := fun ⟨⟨w₁⟩, w, u', x₁, x₂⟩ ↦ by
        simp only [Prod.mk.injEq, true_and, and_true]
        cases w₁ <;> cases w <;> cases u' <;> rfl
      right_inv := fun ⟨u, (w₁, x₁), (w₂, x₂)⟩ ↦ by
        simp only [Prod.mk.injEq, true_and, and_true]
        cases u <;> cases w₁ <;> cases w₂ <;> rfl }
  let P : Matrix (Bool × ((Bool × α) × (Bool × α)))
      (ULift.{u} Bool × (Bool × (Bool × (α × α)))) ℂ :=
    Matrix.of fun r c ↦ if r = e c then 1 else 0
  have hP_iso : Pᴴ * P = 1 := by
    ext c₁ c₂
    simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (e c₁)]
    · by_cases h : c₁ = c₂
      · subst h; simp
      · have he : e c₁ ≠ e c₂ := fun h' ↦ h (e.injective h')
        simp [h, he]
    · intro r _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ (e c₁)) h
  have hiso : (W.plusChannel.symmetrize.tensorMaxMixed (ULift.{u} Bool)).IsoEquiv
      W.symmetrize.plusChannel := by
    refine ⟨Bool × ((Bool × α) × (Bool × α)), inferInstance, inferInstance, P, 1, hP_iso, by simp, ?_⟩
    intro b
    rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
    ext ⟨u₁, ⟨w₁, i₁⟩, ⟨w₂, i₂⟩⟩ ⟨u₂, ⟨w₁', j₁⟩, ⟨w₂', j₂⟩⟩
    conv_lhs =>
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, P, Matrix.of_apply]
    rw [Finset.sum_eq_single (e.symm (u₂, (w₁', j₁), (w₂', j₂)))]
    · rw [Finset.sum_eq_single (e.symm (u₁, (w₁, i₁), (w₂, i₂)))]
      · simp only [Equiv.apply_symm_apply, ↓reduceIte, one_mul, star_one, mul_one, e,
          Equiv.coe_fn_symm_mk, CQChannel.tensorMaxMixed, CQChannel.plusChannel,
          CQChannel.varCombine, CQChannel.symmetrize, DensityOp.midpoint, DensityOp.mix,
          DensityOp.tensor, CQChannel.ketBraBool, maxMixedState, Matrix.add_apply,
          Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply,
          Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, Fintype.card_ulift,
          Fintype.card_bool, Nat.cast_ofNat]
        cases b <;> cases u₁ <;> cases u₂ <;> cases w₁ <;> cases w₂ <;> cases w₁' <;> cases w₂' <;>
          simp <;> push_cast <;> ring
      · intro c _ hne
        have : (u₁, (w₁, i₁), (w₂, i₂)) ≠ e c := fun h ↦ hne (by rw [h, e.symm_apply_apply]).symm
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro c _ hne
      have : (u₂, (w₁', j₁), (w₂', j₂)) ≠ e c := fun h ↦ hne (by rw [h, e.symm_apply_apply]).symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact ((W.plusChannel.symmetrize.channelEquiv_tensorMaxMixed (ULift.{u} Bool)).trans
    hiso.toChannelEquiv).symm

/-- Symmetrization preserves `polarCondEntropy` at every depth `n` and path `b`. -/
theorem polarCondEntropy_symmetrize {α : Type u} [Fintype α] [DecidableEq α]
    (W : CQChannel α) (n : ℕ) (b : Fin n → Bool) :
    polarCondEntropy W.symmetrize n b = polarCondEntropy W n b := by
  have heq : ∀ (m : ℕ) (c : Fin m → Bool),
      (polarChannelTree W.symmetrize m c).ch.ChannelEquiv (polarChannelTree W m c).ch.symmetrize := by
    intro m
    induction m with
    | zero => intro c; exact CQChannel.ChannelEquiv.refl W.symmetrize
    | succ m ih =>
      intro c
      have hsnoc : c = Fin.snoc (α := fun _ ↦ Bool) (Fin.init c) (c (Fin.last m)) :=
        (Fin.snoc_init_self c).symm
      rw [hsnoc]
      have hih := ih (Fin.init c)
      cases c (Fin.last m)
      · rw [polarChannelTree_snoc_false, polarChannelTree_snoc_false]
        exact (hih.checkCombine hih).trans (symmetrize_minusChannel_channelEquiv _)
      · rw [polarChannelTree_snoc_true, polarChannelTree_snoc_true]
        exact (hih.varCombine hih).trans (symmetrize_plusChannel_channelEquiv _)
  unfold polarCondEntropy
  rw [(heq n b).condEntropy_eq, condEntropy_symmetrize]

/-- **Phase–Complementary Channel Duality**:
`(phaseChannel 𝒩).dual ≃ (ampChannel 𝒩.complementary).transpose.symmetrize`. -/
theorem phaseChannel_dual_channelEquiv {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap.{0} Bool d) :
    (phaseChannel 𝒩).dual.ChannelEquiv (ampChannel 𝒩.complementary).transpose.symmetrize := by
  have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
  have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  let A₀ : Matrix (Bool × d) 𝒩.env ℂ := choiFactor 𝒩
  let A₁ : Matrix (Bool × d) 𝒩.env ℂ :=
    (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) * choiFactor 𝒩
  have hA₀ : A₀ * A₀ᴴ = ((phaseChannel 𝒩).out false).mat := rfl
  have hA₁ : A₁ * A₁ᴴ = ((phaseChannel 𝒩).out true).mat := by
    change ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) * choiFactor 𝒩) *
        ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) * choiFactor 𝒩)ᴴ =
      (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) * (choiFactor 𝒩 * (choiFactor 𝒩)ᴴ) *
        star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
  have hstep1 := (dual_isoEquiv_of_purification (phaseChannel 𝒩) A₀ A₁ hA₀ hA₁).toChannelEquiv
  let H : Matrix (Bool × 𝒩.env) (Bool × 𝒩.env) ℂ :=
    Matrix.of fun (u₁, e₁) (u₂, e₂) ↦
      if e₁ = e₂ then ((Real.sqrt 2 : ℂ)⁻¹) * (if u₁ = true ∧ u₂ = true then -1 else 1) else 0
  have hH_iso : Hᴴ * H = 1 := by
    ext ⟨u₁, e₁⟩ ⟨u₂, e₂⟩
    simp only [H, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single e₁]
    · by_cases he : e₁ = e₂
      · subst he
        simp only [↓reduceIte, Prod.mk.injEq, and_true, Fintype.sum_bool, star_mul', hstar2]
        cases u₁ <;> cases u₂ <;> simp <;>
          (have : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := hmul2;
           linear_combination this + this)
      · have hne : (u₁, e₁) ≠ (u₂, e₂) := fun h ↦ he (Prod.mk.inj h).2
        simp [he, hne]
    · intro e _ hne; apply Finset.sum_eq_zero; intro u _; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ e₁) h
  have hstep2 : CQChannel.IsoEquiv
      ({ out := fun b ↦
          match b with
          | false =>
            { mat :=
                (Matrix.of fun (p : Bool × 𝒩.env) (x : Bool × d) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) *
                (Matrix.of fun (p : Bool × 𝒩.env) (x : Bool × d) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ
              posSemidef := posSemidef_mul_conjTranspose _
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hMM : (Matrix.of fun (p : Bool × 𝒩.env) (x : Bool × d) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ *
                    (Matrix.of fun (p : Bool × 𝒩.env) (x : Bool × d) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) =
                    (1 / 2 : ℂ) • ((phaseChannel 𝒩).out false).mat +
                    (1 / 2 : ℂ) • ((phaseChannel 𝒩).out true).mat := by
                  ext x y
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul', hstar2]
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, mul_add]
                  rw [add_comm]
                  congr 1 <;> (apply Finset.sum_congr rfl; intro e _; simp only [star_star]; rw [← hmul2]; ring)
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    ((phaseChannel 𝒩).out false).trace_one, ((phaseChannel 𝒩).out true).trace_one]
                simp [smul_eq_mul]; ring }
          | true =>
            { mat :=
                (Matrix.of fun (p : Bool × 𝒩.env) (x : Bool × d) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) *
                (Matrix.of fun (p : Bool × 𝒩.env) (x : Bool × d) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ
              posSemidef := posSemidef_mul_conjTranspose _
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hMM : (Matrix.of fun (p : Bool × 𝒩.env) (x : Bool × d) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ *
                    (Matrix.of fun (p : Bool × 𝒩.env) (x : Bool × d) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) =
                    (1 / 2 : ℂ) • ((phaseChannel 𝒩).out false).mat +
                    (1 / 2 : ℂ) • ((phaseChannel 𝒩).out true).mat := by
                  ext x y
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, hstar2]
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, mul_add]
                  rw [add_comm]
                  congr 1 <;> (apply Finset.sum_congr rfl; intro e _; simp only [star_star]; rw [← hmul2]; ring)
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    ((phaseChannel 𝒩).out false).trace_one, ((phaseChannel 𝒩).out true).trace_one]
                simp [smul_eq_mul]; ring } } : CQChannel (Bool × 𝒩.env))
      (ampChannel 𝒩.complementary).transpose.symmetrize := by
    refine ⟨Bool × 𝒩.env, inferInstance, inferInstance, H, 1, hH_iso, by simp, ?_⟩
    have hHM : ∀ b : Bool,
        H * (Matrix.of fun (p : Bool × 𝒩.env) (x : Bool × d) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x)) =
        Matrix.of fun (u, e) (a, x) ↦
          if a = xor u b then ((Real.sqrt 2 : ℂ)⁻¹) * star (𝒩.isom (x, e) a) else 0 := by
      intro b
      ext ⟨u, e⟩ ⟨a, x⟩
      simp only [H, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single e]
      · simp only [↓reduceIte, Fintype.sum_bool, A₀, A₁, Matrix.conjTranspose_apply,
          choiFactor, pauliZTensorI, Matrix.diagonal_mul, Matrix.of_apply, star_mul', hstar2]
        have h3 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) +
            ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) =
            ((Real.sqrt 2 : ℂ)⁻¹) := by
          calc ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) +
                ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)
              = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) +
                 ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * ((Real.sqrt 2 : ℂ)⁻¹) := by ring
            _ = (1 / 2 + 1 / 2) * ((Real.sqrt 2 : ℂ)⁻¹) := by rw [hmul2]
            _ = ((Real.sqrt 2 : ℂ)⁻¹) := by ring
        cases b <;> cases u <;> cases a <;> simp <;>
          first | ring | (linear_combination star (𝒩.isom (x, e) _) * h3)
      · intro e' _ hne; apply Finset.sum_eq_zero; intro v _; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ e) h
    intro b
    have hfactor : (H * Matrix.of fun (p : Bool × 𝒩.env) (x : Bool × d) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x)) *
        (H * Matrix.of fun (p : Bool × 𝒩.env) (x : Bool × d) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ =
        ((ampChannel 𝒩.complementary).transpose.symmetrize.out b).mat := by
      rw [hHM b]
      ext ⟨u₁, e₁⟩ ⟨u₂, e₂⟩
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_prod_type, CQChannel.symmetrize, CQChannel.transpose, DensityOp.transpose,
        ampChannel, CPTPMap.apply, CPTPMap.complementary, CPTPMap.toLinearMap, partialTrace₂Mat,
        DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, CQChannel.ketBraBool,
        Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
        LinearMap.coe_mk, AddHom.coe_mk, Complex.real_smul, Fintype.sum_bool, star_mul',
        star_star, hstar2]
      cases b <;> cases u₁ <;> cases u₂ <;>
        simp only [↓reduceIte, Bool.xor_false, Bool.xor_true, Bool.true_eq_false, Bool.false_eq_true,
          Bool.not_false, Bool.not_true, and_self, and_false, false_and, one_mul, mul_one,
          mul_zero, zero_mul, add_zero, zero_add, star_zero, Finset.sum_const_zero] <;>
        first
        | rfl
        | (rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _;
           calc ((Real.sqrt 2 : ℂ)⁻¹ * star (𝒩.isom (x, e₁) _)) *
                  ((Real.sqrt 2 : ℂ)⁻¹ * 𝒩.isom (x, e₂) _)
               = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
                 (𝒩.isom (x, e₂) _ * star (𝒩.isom (x, e₁) _)) := by ring
             _ = _ := by rw [hmul2]; push_cast; ring)
    cases b <;>
      simpa [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one,
        Matrix.conjTranspose_mul, Matrix.mul_assoc] using hfactor
  exact hstep1.trans hstep2.toChannelEquiv

/-- **Degradable Entropy Sum Inequality**:
For any degradable qubit-input CPTP map `𝒩`, every depth `n`, and every branch path `b : Fin n → Bool`,
`H((W_A)_n^{(b)}) + H((W_P)_n^{(!b)}) ≤ 1`. -/
theorem degradable_amp_phase_sum_le_one {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap.{0} Bool d) (hdeg : 𝒩.IsDegradable) (n : ℕ) (b : Fin n → Bool) :
    polarCondEntropy (ampChannel 𝒩) n b +
      polarCondEntropy (phaseChannel 𝒩) n (fun k ↦ !(b k)) ≤ 1 := by
  have h1 : polarCondEntropy (ampChannel 𝒩) n b ≤
      polarCondEntropy (ampChannel 𝒩.complementary) n b :=
    ((degradable_ampChannel_degradedTo 𝒩 hdeg).polarChannelTree n b).condEntropy_le
  have h2 : polarCondEntropy (ampChannel 𝒩.complementary) n b =
      polarCondEntropy (phaseChannel 𝒩).dual n b := by
    rw [← polarChannelTree_transpose_condEntropy (ampChannel 𝒩.complementary) n b,
      ← polarCondEntropy_symmetrize (ampChannel 𝒩.complementary).transpose n b]
    exact ((phaseChannel_dual_channelEquiv 𝒩).polarChannelTree n b).condEntropy_eq.symm
  have h3 : polarCondEntropy (phaseChannel 𝒩).dual n b =
      1 - polarCondEntropy (phaseChannel 𝒩) n (fun k ↦ !(b k)) := by
    have hnot : (fun k ↦ !(!(b k))) = b := funext fun k ↦ Bool.not_not _
    have h := polarCondEntropy_dual_complement (phaseChannel 𝒩) n (fun k ↦ !(b k))
    rwa [hnot] at h
  linarith

/-- **Degradable Vanishing Assistance**:
For a degradable qubit-input CPTP map `𝒩` and any `δ ≤ 1/4`, the pre-shared entanglement /
secret-key assistance set `ℰ = 𝒢_N(W_A)ᶜ ∩ {i : dualIndex n i ∉ 𝒢_N(W_P)}` is contained in the
combined unpolarized set `𝒰_N(W_A) ∪ {i : dualIndex n i ∈ 𝒰_N(W_P)}`. -/
theorem degradable_assistance_subset_unpolarized {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap.{0} Bool d) (hdeg : 𝒩.IsDegradable) (n : ℕ) {δ : ℝ} (hδ : δ ≤ 1 / 4) :
    Finset.univ.filter (fun i : Fin (2 ^ n) ↦
        i ∉ goodSet (ampChannel 𝒩) n δ ∧ dualIndex n i ∉ goodSet (phaseChannel 𝒩) n δ) ⊆
      unpolarizedSet (ampChannel 𝒩) n δ ∪
        (unpolarizedSet (phaseChannel 𝒩) n δ).image (dualIndex n) := by
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with ⟨hnotGA, hnotGP⟩
  by_cases hBA : i ∈ veryNoisySet (ampChannel 𝒩) n δ
  · apply Finset.mem_union_right
    rw [Finset.mem_image]
    refine ⟨dualIndex n i, ?_, dualIndex_involutive n i⟩
    simp only [unpolarizedSet, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
      not_or]
    refine ⟨hnotGP, fun hBP ↦ ?_⟩
    simp only [veryNoisySet, Finset.mem_filter, Finset.mem_univ, true_and] at hBA hBP
    have hH1 : (synthChannel (ampChannel 𝒩).dual n (dualIndex n i)).condEntropy ≤
        Real.logb 2 (5 / 4 : ℝ) := by
      have := condEntropy_le_logb_one_add_fidelityParam
        (synthChannel (ampChannel 𝒩).dual n (dualIndex n i))
      have h2 : Real.logb 2 (1 + (synthChannel (ampChannel 𝒩).dual n (dualIndex n i)).fidelityParam) ≤
          Real.logb 2 (5 / 4 : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) (by linarith [rootFidelity_nonneg ((synthChannel (ampChannel 𝒩).dual n (dualIndex n i)).out false) ((synthChannel (ampChannel 𝒩).dual n (dualIndex n i)).out true)]) (by linarith)
      exact this.trans h2
    have hH2 : (synthChannel (phaseChannel 𝒩).dual n (dualIndex n (dualIndex n i))).condEntropy ≤
        Real.logb 2 (5 / 4 : ℝ) := by
      have := condEntropy_le_logb_one_add_fidelityParam
        (synthChannel (phaseChannel 𝒩).dual n (dualIndex n (dualIndex n i)))
      have h2 : Real.logb 2 (1 + (synthChannel (phaseChannel 𝒩).dual n (dualIndex n (dualIndex n i))).fidelityParam) ≤
          Real.logb 2 (5 / 4 : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) (by linarith [rootFidelity_nonneg ((synthChannel (phaseChannel 𝒩).dual n (dualIndex n (dualIndex n i))).out false) ((synthChannel (phaseChannel 𝒩).dual n (dualIndex n (dualIndex n i))).out true)]) (by linarith)
      exact this.trans h2
    rw [synthChannel_condEntropy_eq] at hH1 hH2
    rw [dualIndex_involutive] at hH2
    have hbp1 : bitPath n (dualIndex n i) = fun k ↦ !(bitPath n i k) := by simp [dualIndex]
    rw [hbp1, polarCondEntropy_dual_complement] at hH1
    have hnot : (fun k ↦ !(!(bitPath n i k))) = bitPath n i := funext fun k ↦ Bool.not_not _
    have hdualP : polarCondEntropy (phaseChannel 𝒩).dual n (bitPath n i) =
        1 - polarCondEntropy (phaseChannel 𝒩) n (fun k ↦ !(bitPath n i k)) := by
      have h := polarCondEntropy_dual_complement (phaseChannel 𝒩) n (fun k ↦ !(bitPath n i k))
      rwa [hnot] at h
    rw [hdualP] at hH2
    have hsum := degradable_amp_phase_sum_le_one 𝒩 hdeg n (bitPath n i)
    have hlt := logb_two_five_fourths_lt_half
    linarith
  · apply Finset.mem_union_left
    simp only [unpolarizedSet, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
      not_or]
    exact ⟨hnotGA, hBA⟩

/-! ### 5. Single-Block CSS / Private Polar Code and Full Corollary 5.5 -/

/-- A single-block Renes–Wilde CSS / private polar code of blocklength `N = 2^n` for a
qubit-input quantum channel `𝒩 : CPTPMap Bool d`, bundling the amplitude QSC polar code,
the dual-indexed phase QSC polar code on the shared information set, and the entanglement /
secret-key assistance set `ℰ`. -/
structure CSSPrivatePolarCode {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap.{0} Bool d) (n : ℕ) where
  ampCode : CosetPolarCode (ampChannel 𝒩) n
  phaseCode : CosetPolarCode (phaseChannel 𝒩) n
  infoSet_align : phaseCode.infoSet = ampCode.infoSet.image (dualIndex n)
  assistanceSet : Finset (Fin (2 ^ n))

/-- Information rate `|𝒜| / 2^n` of a CSS / private polar code. -/
noncomputable def CSSPrivatePolarCode.rate {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap.{0} Bool d} {n : ℕ} (C : CSSPrivatePolarCode 𝒩 n) : ℝ :=
  C.ampCode.rate

/-- Entanglement / secret-key assistance rate `|ℰ| / 2^n`. -/
noncomputable def CSSPrivatePolarCode.assistanceRate {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap.{0} Bool d} {n : ℕ} (C : CSSPrivatePolarCode 𝒩 n) : ℝ :=
  (C.assistanceSet.card : ℝ) / (2 : ℝ) ^ n

/-- Combined trace-distance decoding + secrecy error bound `P_e(amp) + P_e(phase)`. -/
noncomputable def CSSPrivatePolarCode.combinedError {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap.{0} Bool d} {n : ℕ} (C : CSSPrivatePolarCode 𝒩 n) : ℝ :=
  C.ampCode.avgBlockError + C.phaseCode.avgBlockError

/-- **Corollary 5.5 (Full Quantum & Private Polar Coding — Renes–Wilde [10] Reduction)**:
There exist universal constants `μ > 0` and `C₀ > 0` such that for every finite-dimensional
qubit-input quantum channel `𝒩 : CPTPMap Bool d`, every gap `ε ∈ (0, 1)`, and every depth `n`
with blocklength `N = 2^n ≥ C₀ (1 / ε)^μ`:
1. There exists a single-block CSS / private polar code `C : CSSPrivatePolarCode 𝒩 n` of
   blocklength `N = 2^n` achieving rate `C.rate ≥ I_sym(𝒩) - ε / 2`.
2. Its amplitude decoding error, phase / secrecy error, and combined error satisfy
   `C.ampCode.avgBlockError ≤ 2^{-N^{0.49}}`, `C.phaseCode.avgBlockError ≤ 2^{-N^{0.49}}`,
   and `C.combinedError ≤ 2 · 2^{-N^{0.49}}`.
3. The combined unpolarized fraction of `(W_A, W_P)` is at most `ε / 2`.
4. If `𝒩` is degradable (`𝒩.IsDegradable`), the pre-shared entanglement / secret-key assistance
   rate vanishes: `C.assistanceRate ≤ ε / 2`. -/
theorem corollary_5_5_quantum_private_polar_coding :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap.{0} Bool d)
        {ε : ℝ}, 0 < ε → ε < 1 →
        ∀ (n : ℕ), C₀ * (1 / ε) ^ μ ≤ (2 : ℝ) ^ n →
          let thresh : ℝ := (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))
          ∃ C : CSSPrivatePolarCode 𝒩 n,
            symCoherentInfo 𝒩 - ε / 2 ≤ C.rate ∧
            C.ampCode.avgBlockError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
            C.phaseCode.avgBlockError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
            C.combinedError ≤ 2 * (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
            ((unpolarizedSet (ampChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n ≤ ε / 4 ∧
            ((unpolarizedSet (phaseChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n ≤ ε / 4 ∧
            (𝒩.IsDegradable → C.assistanceRate ≤ ε / 2) := by
  rcases theorem_1_1_quantum_polar_poly_blocklength.{0} with ⟨μ, C₀, hμ, hC₀, hpolar⟩
  refine ⟨μ, max (C₀ * (8 : ℝ) ^ μ) 2, hμ,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro d _ _ 𝒩 ε hε0 hε1 n hn
  dsimp only
  set thresh : ℝ := (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))
  have h1eps : (1 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε0, one_mul]; exact le_of_lt hε1
  have hpow_ge1 : (1 : ℝ) ≤ (1 / ε) ^ μ := Real.one_le_rpow h1eps (le_of_lt hμ)
  have hn_ge2 : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (2 : ℝ) = 2 * 1 := by ring
      _ ≤ max (C₀ * (8 : ℝ) ^ μ) 2 * (1 / ε) ^ μ :=
          mul_le_mul (le_max_right _ _) hpow_ge1 (by norm_num) (by positivity)
      _ ≤ (2 : ℝ) ^ n := hn
  have hn1 : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    subst this; norm_num at hn_ge2
  have hε8_pos : (0 : ℝ) < ε / 8 := by linarith
  have hε8_lt1 : ε / 8 < 1 := by linarith
  have hn_eps8 : C₀ * (1 / (ε / 8)) ^ μ ≤ (2 : ℝ) ^ n := by
    have h8 : (1 / (ε / 8)) ^ μ = (8 : ℝ) ^ μ * (1 / ε) ^ μ := by
      have heq : (1 : ℝ) / (ε / 8) = 8 * (1 / ε) := by field_simp
      rw [heq, Real.mul_rpow (by norm_num) (by positivity)]
    rw [h8, ← mul_assoc]
    exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hn
  have hWA := hpolar (ampChannel 𝒩) hε8_pos hε8_lt1 n hn_eps8
  have hWAd := hpolar (ampChannel 𝒩).dual hε8_pos hε8_lt1 n hn_eps8
  have hWP := hpolar (phaseChannel 𝒩) hε8_pos hε8_lt1 n hn_eps8
  have hWPd := hpolar (phaseChannel 𝒩).dual hε8_pos hε8_lt1 n hn_eps8
  rw [← goodSet_card_eq_treeProb] at hWA hWAd hWP hWPd
  have hthresh_le : thresh ≤ 1 / 4 := by
    have hpow2 : (1 : ℝ) ≤ ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    have hexp : -(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ) ≤ (-2 : ℝ) := by linarith
    calc thresh = (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ)) := rfl
      _ ≤ (2 : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 1 / 4 := by norm_num
  have hU_A : ((unpolarizedSet (ampChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n ≤ ε / 4 := by
    have := dual_unpolarized_fraction_le (ampChannel 𝒩) n hthresh_le hWA hWAd
    linarith
  have hU_P : ((unpolarizedSet (phaseChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n ≤ ε / 4 := by
    have := dual_unpolarized_fraction_le (phaseChannel 𝒩) n hthresh_le hWP hWPd
    linarith
  let infoA : Finset (Fin (2 ^ n)) :=
    (goodSet (ampChannel 𝒩) n thresh).filter (fun i ↦ dualIndex n i ∈ goodSet (phaseChannel 𝒩) n thresh)
  let infoP : Finset (Fin (2 ^ n)) := infoA.image (dualIndex n)
  let assistSet : Finset (Fin (2 ^ n)) :=
    Finset.univ.filter (fun i : Fin (2 ^ n) ↦
      i ∉ goodSet (ampChannel 𝒩) n thresh ∧ dualIndex n i ∉ goodSet (phaseChannel 𝒩) n thresh)
  obtain ⟨frozenA, hwgA⟩ := wilde_guha_qsc_bound (ampChannel 𝒩) n infoA
  obtain ⟨frozenP, hwgP⟩ := wilde_guha_qsc_bound (phaseChannel 𝒩) n infoP
  refine ⟨⟨qscPolarCode (ampChannel 𝒩) n infoA frozenA,
           qscPolarCode (phaseChannel 𝒩) n infoP frozenP, rfl, assistSet⟩,
          ?_, ?_, ?_, ?_, hU_A, hU_P, ?_⟩
  · let gP_dual : Finset (Fin (2 ^ n)) :=
      (goodSet (phaseChannel 𝒩) n thresh).image (dualIndex n)
    have hinfoA_eq : infoA = goodSet (ampChannel 𝒩) n thresh ∩ gP_dual := by
      ext i
      simp only [infoA, gP_dual, Finset.mem_filter, Finset.mem_inter, Finset.mem_image]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, dualIndex n i, h2, dualIndex_involutive n i⟩
      · rintro ⟨h1, j, hj, rfl⟩
        exact ⟨h1, by rwa [dualIndex_involutive]⟩
    have hgP_card : gP_dual.card = (goodSet (phaseChannel 𝒩) n thresh).card :=
      Finset.card_image_of_injective _ (dualIndex_bijective n).1
    have hcard_inter : (goodSet (ampChannel 𝒩) n thresh).card +
        (goodSet (phaseChannel 𝒩) n thresh).card ≤ infoA.card + 2 ^ n := by
      rw [hinfoA_eq, ← hgP_card]
      have hu := Finset.card_union_add_card_inter (goodSet (ampChannel 𝒩) n thresh) gP_dual
      have hle : (goodSet (ampChannel 𝒩) n thresh ∪ gP_dual).card ≤ 2 ^ n := by
        simpa [Fintype.card_fin] using Finset.card_le_univ (goodSet (ampChannel 𝒩) n thresh ∪ gP_dual)
      omega
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hrate_ge : ((goodSet (ampChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n +
        ((goodSet (phaseChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n - 1 ≤
        (infoA.card : ℝ) / (2 : ℝ) ^ n := by
      have hcast : ((goodSet (ampChannel 𝒩) n thresh).card : ℝ) +
          ((goodSet (phaseChannel 𝒩) n thresh).card : ℝ) ≤ (infoA.card : ℝ) + (2 : ℝ) ^ n := by
        exact_mod_cast hcard_inter
      rw [div_add_div_same, sub_le_iff_le_add]
      rw [div_le_iff₀ hpow_pos]
      have hmul : ((infoA.card : ℝ) / (2 : ℝ) ^ n + 1) * (2 : ℝ) ^ n = (infoA.card : ℝ) + (2 : ℝ) ^ n := by
        field_simp [ne_of_gt hpow_pos]
      linarith
    have hcap := amp_phase_symCapacity_sum 𝒩
    change symCoherentInfo 𝒩 - ε / 2 ≤ (infoA.card : ℝ) / (2 : ℝ) ^ n
    linarith
  · have hthresh_nn : 0 ≤ thresh := Real.rpow_nonneg (by norm_num) _
    have hsum_le : ∑ i ∈ infoA, (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam ≤
        (2 : ℝ) ^ n * thresh := by
      have h1 : ∑ i ∈ infoA, (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam ≤
          ∑ _i ∈ infoA, thresh := by
        apply Finset.sum_le_sum; intro i hi
        have hiG : i ∈ goodSet (ampChannel 𝒩) n thresh := (Finset.mem_filter.mp hi).1
        simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiG
        have hnn : 0 ≤ (synthChannel (ampChannel 𝒩) n i).fidelityParam := rootFidelity_nonneg _ _
        linarith
      have hcard_le : (infoA.card : ℝ) ≤ (2 : ℝ) ^ n := by
        simpa [Fintype.card_fin] using (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_univ infoA)
      calc ∑ i ∈ infoA, (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam
          ≤ (infoA.card : ℝ) * thresh := by simpa [Finset.sum_const, nsmul_eq_mul] using h1
        _ ≤ (2 : ℝ) ^ n * thresh := mul_le_mul_of_nonneg_right hcard_le hthresh_nn
    calc (qscPolarCode (ampChannel 𝒩) n infoA frozenA).avgBlockError
        ≤ 2 * Real.sqrt (∑ i ∈ infoA, (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam) := hwgA
      _ ≤ 2 * Real.sqrt ((2 : ℝ) ^ n * thresh) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum_le) (by norm_num)
      _ ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := polar_error_exponent_bound hn1
  · have hthresh_nn : 0 ≤ thresh := Real.rpow_nonneg (by norm_num) _
    have hsum_le : ∑ j ∈ infoP, (1 / 2 : ℝ) * (synthChannel (phaseChannel 𝒩) n j).fidelityParam ≤
        (2 : ℝ) ^ n * thresh := by
      have h1 : ∑ j ∈ infoP, (1 / 2 : ℝ) * (synthChannel (phaseChannel 𝒩) n j).fidelityParam ≤
          ∑ _j ∈ infoP, thresh := by
        apply Finset.sum_le_sum; intro j hj
        rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
        have hiP : dualIndex n i ∈ goodSet (phaseChannel 𝒩) n thresh := (Finset.mem_filter.mp hi).2
        simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiP
        have hnn : 0 ≤ (synthChannel (phaseChannel 𝒩) n (dualIndex n i)).fidelityParam :=
          rootFidelity_nonneg _ _
        linarith
      have hcard_le : (infoP.card : ℝ) ≤ (2 : ℝ) ^ n := by
        simpa [Fintype.card_fin] using (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_univ infoP)
      calc ∑ j ∈ infoP, (1 / 2 : ℝ) * (synthChannel (phaseChannel 𝒩) n j).fidelityParam
          ≤ (infoP.card : ℝ) * thresh := by simpa [Finset.sum_const, nsmul_eq_mul] using h1
        _ ≤ (2 : ℝ) ^ n * thresh := mul_le_mul_of_nonneg_right hcard_le hthresh_nn
    calc (qscPolarCode (phaseChannel 𝒩) n infoP frozenP).avgBlockError
        ≤ 2 * Real.sqrt (∑ j ∈ infoP, (1 / 2 : ℝ) * (synthChannel (phaseChannel 𝒩) n j).fidelityParam) := hwgP
      _ ≤ 2 * Real.sqrt ((2 : ℝ) ^ n * thresh) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum_le) (by norm_num)
      _ ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := polar_error_exponent_bound hn1
  · unfold CSSPrivatePolarCode.combinedError
    dsimp only
    have hthresh_nn : 0 ≤ thresh := Real.rpow_nonneg (by norm_num) _
    have hA_err : (qscPolarCode (ampChannel 𝒩) n infoA frozenA).avgBlockError ≤
        (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := by
      have hsum_le : ∑ i ∈ infoA, (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam ≤
          (2 : ℝ) ^ n * thresh := by
        have h1 : ∑ i ∈ infoA, (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam ≤
            ∑ _i ∈ infoA, thresh := by
          apply Finset.sum_le_sum; intro i hi
          have hiG : i ∈ goodSet (ampChannel 𝒩) n thresh := (Finset.mem_filter.mp hi).1
          simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiG
          linarith [rootFidelity_nonneg ((synthChannel (ampChannel 𝒩) n i).out false) ((synthChannel (ampChannel 𝒩) n i).out true)]
        have hcard_le : (infoA.card : ℝ) ≤ (2 : ℝ) ^ n := by
          simpa [Fintype.card_fin] using (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_univ infoA)
        calc ∑ i ∈ infoA, (1 / 2 : ℝ) * (synthChannel (ampChannel 𝒩) n i).fidelityParam
            ≤ (infoA.card : ℝ) * thresh := by simpa [Finset.sum_const, nsmul_eq_mul] using h1
          _ ≤ (2 : ℝ) ^ n * thresh := mul_le_mul_of_nonneg_right hcard_le hthresh_nn
      exact (hwgA.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum_le) (by norm_num))).trans
        (polar_error_exponent_bound hn1)
    have hP_err : (qscPolarCode (phaseChannel 𝒩) n infoP frozenP).avgBlockError ≤
        (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := by
      have hsum_le : ∑ j ∈ infoP, (1 / 2 : ℝ) * (synthChannel (phaseChannel 𝒩) n j).fidelityParam ≤
          (2 : ℝ) ^ n * thresh := by
        have h1 : ∑ j ∈ infoP, (1 / 2 : ℝ) * (synthChannel (phaseChannel 𝒩) n j).fidelityParam ≤
            ∑ _j ∈ infoP, thresh := by
          apply Finset.sum_le_sum; intro j hj
          rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
          have hiP : dualIndex n i ∈ goodSet (phaseChannel 𝒩) n thresh := (Finset.mem_filter.mp hi).2
          simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiP
          linarith [rootFidelity_nonneg ((synthChannel (phaseChannel 𝒩) n (dualIndex n i)).out false) ((synthChannel (phaseChannel 𝒩) n (dualIndex n i)).out true)]
        have hcard_le : (infoP.card : ℝ) ≤ (2 : ℝ) ^ n := by
          simpa [Fintype.card_fin] using (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_univ infoP)
        calc ∑ j ∈ infoP, (1 / 2 : ℝ) * (synthChannel (phaseChannel 𝒩) n j).fidelityParam
            ≤ (infoP.card : ℝ) * thresh := by simpa [Finset.sum_const, nsmul_eq_mul] using h1
          _ ≤ (2 : ℝ) ^ n * thresh := mul_le_mul_of_nonneg_right hcard_le hthresh_nn
      exact (hwgP.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum_le) (by norm_num))).trans
        (polar_error_exponent_bound hn1)
    linarith
  · intro hdeg
    unfold CSSPrivatePolarCode.assistanceRate
    dsimp only
    have hsub := degradable_assistance_subset_unpolarized 𝒩 hdeg n hthresh_le
    have hcard : assistSet.card ≤
        (unpolarizedSet (ampChannel 𝒩) n thresh).card +
        (unpolarizedSet (phaseChannel 𝒩) n thresh).card := by
      calc assistSet.card
          ≤ (unpolarizedSet (ampChannel 𝒩) n thresh ∪
              (unpolarizedSet (phaseChannel 𝒩) n thresh).image (dualIndex n)).card :=
            Finset.card_le_card hsub
        _ ≤ (unpolarizedSet (ampChannel 𝒩) n thresh).card +
            ((unpolarizedSet (phaseChannel 𝒩) n thresh).image (dualIndex n)).card :=
            Finset.card_union_le _ _
        _ = (unpolarizedSet (ampChannel 𝒩) n thresh).card +
            (unpolarizedSet (phaseChannel 𝒩) n thresh).card := by
            rw [Finset.card_image_of_injective _ (dualIndex_bijective n).1]
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hdiv : (assistSet.card : ℝ) / (2 : ℝ) ^ n ≤
        ((unpolarizedSet (ampChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n +
        ((unpolarizedSet (phaseChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hpow_pos)
    linarith

end QuantumPolarCoding

end PolarCodes
