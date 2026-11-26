/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.QuantumPolarCodingBase

/-!
# Quantum and Private Polar Coding via the Renes–Wilde Reduction (Corollary 5.5)

Part 2: Degradable vanishing assistance (`degradable_amp_phase_sum_le_one`,
`degradable_assistance_subset_unpolarized`), `CSSPrivatePolarCode`, and the
headline `corollary_5_5_quantum_private_polar_coding`.
-/

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodes

private lemma rootFidelity_nonneg {α : Type*} [Fintype α] [DecidableEq α] (ρ σ : DensityOp α) :
    0 ≤ rootFidelity ρ σ := by
  unfold rootFidelity
  exact Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _

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
  congr 1
  have hchar : ρ.transpose.mat.charpoly * Polynomial.X ^ Fintype.card α =
      ρ.mat.charpoly * Polynomial.X ^ Fintype.card α := by
    simp [DensityOp.transpose, Matrix.charpoly_transpose]
  exact spectral_sum_eq_of_charpoly_mul_X_pow ρ.transpose.isHermitian ρ.isHermitian hchar
    (by simp [Real.negMulLog])

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
        change ((polarChannelTree W.transpose n (Fin.init b)).ch.minusChannel.out z).mat (x₁, x₂) (y₁, y₂) =
          ((polarChannelTree W n (Fin.init b)).ch.minusChannel.out z).mat (e y₁, e y₂) (e x₁, e x₂)
        simp only [CQChannel.minusChannel, CQChannel.checkCombine,
          DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply,
          Matrix.kroneckerMap_apply]
        rw [he, he, he, he]
      · rw [polarChannelTree_snoc_true, polarChannelTree_snoc_true]
        refine ⟨(Equiv.refl Bool).prodCongr (e.prodCongr e), fun z ⟨w₁, x₁, x₂⟩ ⟨w₂, y₁, y₂⟩ ↦ ?_⟩
        change ((polarChannelTree W.transpose n (Fin.init b)).ch.plusChannel.out z).mat (w₁, x₁, x₂) (w₂, y₁, y₂) =
          ((polarChannelTree W n (Fin.init b)).ch.plusChannel.out z).mat (w₂, e y₁, e y₂) (w₁, e x₁, e x₂)
        simp only [CQChannel.plusChannel, CQChannel.varCombine,
          DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, CQChannel.ketBraBool,
          Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.of_apply]
        cases w₁ <;> cases w₂ <;> simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true,
          and_self, and_false, false_and, one_mul, zero_mul, add_zero, zero_add, smul_zero] <;>
          try rw [he, he]
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
  simp only [Bool.not_false, Bool.not_true]
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
  -- Basis permutation on `(Bool × α) × (Bool × α) ≃ ULift Bool × (Bool × (α × α))`
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
    · intro r _ hne; simp [hne]
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
        have : ((w₁, i₁), (w₂, i₂)) ≠ e c := fun h ↦ hne ((e.symm_apply_apply c).symm.trans (congr_arg e.symm h.symm))
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro c _ hne
      have : ((w₁', j₁), (w₂', j₂)) ≠ e c := fun h ↦ hne ((e.symm_apply_apply c).symm.trans (congr_arg e.symm h.symm))
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
    · intro r _ hne; simp [hne]
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
        have : (u₁, (w₁, i₁), (w₂, i₂)) ≠ e c := fun h ↦ hne ((e.symm_apply_apply c).symm.trans (congr_arg e.symm h.symm))
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro c _ hne
      have : (u₂, (w₁', j₁), (w₂', j₂)) ≠ e c := fun h ↦ hne ((e.symm_apply_apply c).symm.trans (congr_arg e.symm h.symm))
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
    · intro e _ hne; apply Finset.sum_eq_zero; intro u _; simp [hne]
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
        cases b <;> cases u <;> cases a <;>
          simp only [↓reduceIte, Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
            Bool.true_eq_false, Bool.false_eq_true, and_self, and_false, false_and,
            one_mul, mul_one, neg_mul, mul_neg, neg_neg, mul_zero, zero_mul,
            add_zero, zero_add, star_one, star_neg, ← mul_assoc, hmul2] <;>
          ring
      · intro e' _ hne; apply Finset.sum_eq_zero; intro v _; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ e) h
    have hamp_comp : ∀ (a : Bool) (e₁ e₂ : 𝒩.env),
        ((ampChannel 𝒩.complementary).out a).mat e₂ e₁ =
          ∑ x : d, 𝒩.isom (x, e₂) a * star (𝒩.isom (x, e₁) a) := by
      intro a e₁ e₂
      change ∑ x : d, (𝒩.complementary.isom * (CQChannel.ketBraBool a).mat *
        𝒩.complementary.isomᴴ) (e₂, x) (e₁, x) = _
      apply Finset.sum_congr rfl; intro x _
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool]
      simp only [CPTPMap.complementary, CQChannel.ketBraBool, Matrix.of_apply]
      cases a <;> simp
    intro b
    have hfactor : (H * Matrix.of fun (p : Bool × 𝒩.env) (x : Bool × d) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x)) *
        (H * Matrix.of fun (p : Bool × 𝒩.env) (x : Bool × d) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ =
        ((ampChannel 𝒩.complementary).transpose.symmetrize.out b).mat := by
      rw [hHM b]
      ext ⟨u₁, e₁⟩ ⟨u₂, e₂⟩
      simp only [CQChannel.symmetrize, CQChannel.transpose, DensityOp.transpose,
        DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, CQChannel.ketBraBool,
        Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
        Complex.real_smul, hamp_comp, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_bool]
      cases b <;> cases u₁ <;> cases u₂ <;>
        simp only [↓reduceIte, Bool.xor_false, Bool.xor_true, Bool.true_eq_false, Bool.false_eq_true,
          Bool.not_false, Bool.not_true, and_self, and_false, false_and, one_mul, mul_one,
          mul_zero, zero_mul, add_zero, zero_add, star_zero, star_mul', star_star, hstar2,
          Finset.sum_const_zero] <;>
        (first
        | rfl
        | (rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _;
           have hcalc : ∀ z₁ z₂ : ℂ,
               ((Real.sqrt 2 : ℂ)⁻¹ * star z₁) * ((Real.sqrt 2 : ℂ)⁻¹ * z₂) =
                 ((1 / 2 : ℝ) : ℂ) * (z₂ * star z₁) := fun z₁ z₂ ↦ by
             calc ((Real.sqrt 2 : ℂ)⁻¹ * star z₁) * ((Real.sqrt 2 : ℂ)⁻¹ * z₂)
                 = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (z₂ * star z₁) := by ring
               _ = ((1 / 2 : ℝ) : ℂ) * (z₂ * star z₁) := by rw [hmul2]; push_cast; ring
           have hcalc' : ∀ z₁ z₂ : ℂ,
               ((Real.sqrt 2 : ℂ)⁻¹ * star z₁) * ((Real.sqrt 2 : ℂ)⁻¹ * z₂) =
                 ((1 - 1 / 2 : ℝ) : ℂ) * (z₂ * star z₁) := fun z₁ z₂ ↦ by
             rw [hcalc]; norm_num
           first | exact hcalc _ _ | exact hcalc' _ _))
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
  · -- If `i ∈ ℬ_N(W_A)`, then `dualIndex n i` cannot be in `ℬ_N(W_P)`, so it is in `𝒰_N(W_P)`
    apply Finset.mem_union_right
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
        Real.logb_le_logb_of_le (by norm_num) (by have hnn : 0 ≤ (synthChannel (ampChannel 𝒩).dual n (dualIndex n i)).fidelityParam := rootFidelity_nonneg _ _; linarith) (by linarith)
      exact this.trans h2
    have hH2 : (synthChannel (phaseChannel 𝒩).dual n (dualIndex n (dualIndex n i))).condEntropy ≤
        Real.logb 2 (5 / 4 : ℝ) := by
      have := condEntropy_le_logb_one_add_fidelityParam
        (synthChannel (phaseChannel 𝒩).dual n (dualIndex n (dualIndex n i)))
      have h2 : Real.logb 2 (1 + (synthChannel (phaseChannel 𝒩).dual n (dualIndex n (dualIndex n i))).fidelityParam) ≤
          Real.logb 2 (5 / 4 : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) (by have hnn : 0 ≤ (synthChannel (phaseChannel 𝒩).dual n (dualIndex n (dualIndex n i))).fidelityParam := rootFidelity_nonneg _ _; linarith) (by linarith)
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
  -- Apply Theorem 1.1 with `ε' = ε / 8` to `W_A`, `W_A⊥`, `W_P`, `W_P⊥`
  have hWA := hpolar (ampChannel 𝒩) hε8_pos hε8_lt1 n hn_eps8
  have hWAd := hpolar (ampChannel 𝒩).dual hε8_pos hε8_lt1 n hn_eps8
  have hWP := hpolar (phaseChannel 𝒩) hε8_pos hε8_lt1 n hn_eps8
  have hWPd := hpolar (phaseChannel 𝒩).dual hε8_pos hε8_lt1 n hn_eps8
  rw [← goodSet_card_eq_treeProb] at hWA hWAd hWP hWPd
  -- Show `thresh ≤ 1 / 4` (since `2^n ≥ 2` implies `200 * (2^n)^0.49047 ≥ 200 ≥ 2`)
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
  -- Shared information set `𝒜 = 𝒢_N(W_A) ∩ {i : dualIndex n i ∈ 𝒢_N(W_P)}`
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
  · -- Rate bound: `|infoA| / 2^n ≥ I(W_A) + I(W_P) - 1 - ε/4 ≥ I_sym(𝒩) - ε/2`
    let gP_dual : Finset (Fin (2 ^ n)) :=
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
      rw [← add_div, sub_le_iff_le_add]
      rw [div_le_iff₀ hpow_pos]
      have hmul : ((infoA.card : ℝ) / (2 : ℝ) ^ n + 1) * (2 : ℝ) ^ n = (infoA.card : ℝ) + (2 : ℝ) ^ n := by
        field_simp [ne_of_gt hpow_pos]
      linarith
    have hcap := amp_phase_symCapacity_sum 𝒩
    change symCoherentInfo 𝒩 - ε / 2 ≤ (infoA.card : ℝ) / (2 : ℝ) ^ n
    linarith
  · -- Amplitude QSC error bound
    have hthresh_nn : 0 ≤ thresh := Real.rpow_nonneg (by norm_num) _
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
  · -- Phase / secrecy QSC error bound
    have hthresh_nn : 0 ≤ thresh := Real.rpow_nonneg (by norm_num) _
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
  · -- Combined error bound
    unfold CSSPrivatePolarCode.combinedError
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
          have hnn : 0 ≤ (synthChannel (ampChannel 𝒩) n i).fidelityParam := rootFidelity_nonneg _ _; linarith
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
          have hnn : 0 ≤ (synthChannel (phaseChannel 𝒩) n (dualIndex n i)).fidelityParam := rootFidelity_nonneg _ _; linarith
        have hcard_le : (infoP.card : ℝ) ≤ (2 : ℝ) ^ n := by
          simpa [Fintype.card_fin] using (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_univ infoP)
        calc ∑ j ∈ infoP, (1 / 2 : ℝ) * (synthChannel (phaseChannel 𝒩) n j).fidelityParam
            ≤ (infoP.card : ℝ) * thresh := by simpa [Finset.sum_const, nsmul_eq_mul] using h1
          _ ≤ (2 : ℝ) ^ n * thresh := mul_le_mul_of_nonneg_right hcard_le hthresh_nn
      exact (hwgP.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum_le) (by norm_num))).trans
        (polar_error_exponent_bound hn1)
    linarith
  · -- Vanishing assistance rate for degradable channels
    intro hdeg
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

end PolarCodes
