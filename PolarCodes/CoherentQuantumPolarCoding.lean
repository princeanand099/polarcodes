/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.PrivatePolarCoding

/-!
# Operational Entanglement-Assisted Coherent CSS Quantum Polar Coding (Renes–Wilde [10])

This module proves the operational entanglement-assisted coherent quantum communication layer of
Corollary 5.5 (Renes–Wilde [10]) unconditionally on top of Mathlib:
1. N-fold tensor power quantum channel `CPTPMap.tensorPow 𝒩 n : CPTPMap (Fin (2^n) → Bool) (Fin (2^n) → d)`,
   left identity tensor `CPTPMap.tensorIdLeft`, and sequential composition `CPTPMap.seqComp`.
2. Maximally entangled Bell state `maxEntangledState α : DensityOp (α × α)`.
3. Coherent CSS polar encoder isometry `cssPolarEncoder` (preparing `|+⟩` on `randSet` and `|uF⟩`
   on public frozen indices, encoding logical qubits `infoSet` and Alice's entanglement register
   `assistSet` via the coherent polar transform `arikanTransform n`).
4. Uhlmann unitary decoupling (`exists_uhlmann_unitary`) and coherent QSC amplitude-decoding
   Stinespring isometry (`W_Z`), combined into a single operational CPTP decoder `𝒟_N` achieving
   `T((id_R ⊗ 𝒟_N ∘ 𝒩^⊗N ∘ ℰ_N)(Φ^+_{RM} ⊗ Φ^+_{E_A E_B}), Φ^+_{RM}) ≤ √(2 ε_Bob) + √(2 ε_sec)`.
-/

open Matrix BigOperators Real Finset
open scoped ComplexOrder

namespace PolarCodes

lemma rootFidelity_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (ρ σ : DensityOp α) : 0 ≤ rootFidelity ρ σ :=
  Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _

section CPTPCombinators

/-- N-fold tensor power of a qubit-input quantum channel `𝒩 : CPTPMap Bool d`. -/
noncomputable def CPTPMap.tensorPow {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap.{0} Bool d) (n : ℕ) :
    CPTPMap.{0} (Fin (2 ^ n) → Bool) (Fin (2 ^ n) → d) where
  env := Fin (2 ^ n) → 𝒩.env
  fintypeEnv := inferInstance
  decEqEnv := inferInstance
  isom := Matrix.of fun p x ↦ ∏ i : Fin (2 ^ n), 𝒩.isom (p.1 i, p.2 i) (x i)
  isom_eq := by
    ext x₁ x₂
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    let e : ((Fin (2 ^ n) → d) × (Fin (2 ^ n) → 𝒩.env)) ≃ (Fin (2 ^ n) → d × 𝒩.env) :=
      { toFun := fun p i ↦ (p.1 i, p.2 i)
        invFun := fun q ↦ (fun i ↦ (q i).1, fun i ↦ (q i).2)
        left_inv := fun ⟨_, _⟩ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hsum : ∑ p : (Fin (2 ^ n) → d) × (Fin (2 ^ n) → 𝒩.env),
        star (∏ i : Fin (2 ^ n), 𝒩.isom (p.1 i, p.2 i) (x₁ i)) *
          ∏ i : Fin (2 ^ n), 𝒩.isom (p.1 i, p.2 i) (x₂ i) =
        ∑ q : Fin (2 ^ n) → d × 𝒩.env,
          ∏ i : Fin (2 ^ n), star (𝒩.isom (q i) (x₁ i)) * 𝒩.isom (q i) (x₂ i) := by
      rw [← Equiv.sum_comp e.symm]
      apply Finset.sum_congr rfl; intro q _
      rw [star_prod, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      rfl
    rw [hsum, ← Fintype.prod_sum (fun i (p : d × 𝒩.env) ↦ star (𝒩.isom p (x₁ i)) * 𝒩.isom p (x₂ i))]
    have hfac : ∀ i : Fin (2 ^ n),
        ∑ p : d × 𝒩.env, star (𝒩.isom p (x₁ i)) * 𝒩.isom p (x₂ i) =
          if x₁ i = x₂ i then (1 : ℂ) else 0 := by
      intro i
      have h := congr_fun (congr_fun 𝒩.isom_eq (x₁ i)) (x₂ i)
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
    simp_rw [hfac]
    by_cases hx : x₁ = x₂
    · subst hx; simp
    · rw [if_neg hx]
      have hne : ∃ i : Fin (2 ^ n), x₁ i ≠ x₂ i := by
        by_contra hall; push Not at hall; exact hx (funext hall)
      obtain ⟨i₀, hi₀⟩ := hne
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀)

/-- Tensor a quantum channel `𝒩` on the right with the identity channel on `α`. -/
noncomputable def CPTPMap.tensorIdLeft (α : Type) [Fintype α] [DecidableEq α]
    {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (𝒩 : CPTPMap.{0} β γ) : CPTPMap.{0} (α × β) (α × γ) where
  env := 𝒩.env
  fintypeEnv := 𝒩.fintypeEnv
  decEqEnv := 𝒩.decEqEnv
  isom := Matrix.of fun p q ↦ if p.1.1 = q.1 then 𝒩.isom (p.1.2, p.2) q.2 else 0
  isom_eq := by
    ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type]
    have h1 : ∀ a : α, (∑ c : γ, ∑ e : 𝒩.env,
        star (if a = a₁ then 𝒩.isom (c, e) b₁ else 0) *
          (if a = a₂ then 𝒩.isom (c, e) b₂ else 0)) =
        if a = a₁ ∧ a = a₂ then (if b₁ = b₂ then (1 : ℂ) else 0) else 0 := by
      intro a
      by_cases h12 : a = a₁ ∧ a = a₂
      · rcases h12 with ⟨rfl, rfl⟩
        simp only [↓reduceIte, and_self]
        have h := congr_fun (congr_fun 𝒩.isom_eq b₁) b₂
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
          Matrix.one_apply] using h
      · rw [if_neg h12]
        apply Finset.sum_eq_zero; intro c _
        apply Finset.sum_eq_zero; intro e _
        by_cases ha1 : a = a₁
        · have ha2 : a ≠ a₂ := fun h ↦ h12 ⟨ha1, h⟩
          rw [if_pos ha1, if_neg ha2, mul_zero]
        · rw [if_neg ha1, star_zero, zero_mul]
    simp_rw [h1]
    by_cases ha : a₁ = a₂
    · subst ha
      rw [Finset.sum_eq_single a₁]
      · simp
      · intro a _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ a₁) h
    · rw [if_neg (fun h ↦ ha (congr_arg Prod.fst h))]
      apply Finset.sum_eq_zero; intro a _
      have hne : ¬ (a = a₁ ∧ a = a₂) := fun ⟨h1, h2⟩ ↦ ha (h1.symm.trans h2)
      simp [hne]

/-- Sequential composition `ℳ ∘ 𝒩` of two CPTP maps. -/
noncomputable def CPTPMap.seqComp {α β γ : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (ℳ : CPTPMap.{0} β γ) (𝒩 : CPTPMap.{0} α β) : CPTPMap.{0} α γ where
  env := ℳ.env × 𝒩.env
  fintypeEnv := @instFintypeProd _ _ ℳ.fintypeEnv 𝒩.fintypeEnv
  decEqEnv := @instDecidableEqProd _ _ ℳ.decEqEnv 𝒩.decEqEnv
  isom := Matrix.of fun p x ↦ ∑ y : β, ℳ.isom (p.1, p.2.1) y * 𝒩.isom (y, p.2.2) x
  isom_eq := by
    letI := ℳ.fintypeEnv; letI := ℳ.decEqEnv
    letI := 𝒩.fintypeEnv; letI := 𝒩.decEqEnv
    ext x₁ x₂
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type]
    have hswap : ∑ z : γ, ∑ e₂ : ℳ.env, ∑ e₁ : 𝒩.env,
        star (∑ y₁ : β, ℳ.isom (z, e₂) y₁ * 𝒩.isom (y₁, e₁) x₁) *
          (∑ y₂ : β, ℳ.isom (z, e₂) y₂ * 𝒩.isom (y₂, e₁) x₂) =
        ∑ y₁ : β, ∑ y₂ : β,
          (∑ z : γ, ∑ e₂ : ℳ.env, star (ℳ.isom (z, e₂) y₁) * ℳ.isom (z, e₂) y₂) *
          (∑ e₁ : 𝒩.env, star (𝒩.isom (y₁, e₁) x₁) * 𝒩.isom (y₂, e₁) x₂) := by
      simp_rw [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
      calc ∑ z : γ, ∑ e₂ : ℳ.env, ∑ e₁ : 𝒩.env, ∑ y₁ : β, ∑ y₂ : β,
            star (𝒩.isom (y₁, e₁) x₁) * star (ℳ.isom (z, e₂) y₁) * (ℳ.isom (z, e₂) y₂ * 𝒩.isom (y₂, e₁) x₂)
          = ∑ z : γ, ∑ e₂ : ℳ.env, ∑ y₁ : β, ∑ y₂ : β, ∑ e₁ : 𝒩.env,
              (star (ℳ.isom (z, e₂) y₁) * ℳ.isom (z, e₂) y₂) *
              (star (𝒩.isom (y₁, e₁) x₁) * 𝒩.isom (y₂, e₁) x₂) := by
            apply Finset.sum_congr rfl; intro z _
            apply Finset.sum_congr rfl; intro e₂ _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y₁ _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y₂ _
            apply Finset.sum_congr rfl; intro e₁ _; ring
        _ = ∑ y₁ : β, ∑ y₂ : β, ∑ z : γ, ∑ e₂ : ℳ.env, ∑ e₁ : 𝒩.env,
              (star (ℳ.isom (z, e₂) y₁) * ℳ.isom (z, e₂) y₂) *
              (star (𝒩.isom (y₁, e₁) x₁) * 𝒩.isom (y₂, e₁) x₂) := by
            rw [Finset.sum_comm]
            conv_lhs =>
              arg 2; ext e₂
              rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y₁ _
            rw [Finset.sum_comm]
            conv_lhs =>
              arg 2; ext z
              rw [Finset.sum_comm]
            rw [Finset.sum_comm]
    rw [hswap]
    have hM : ∀ y₁ y₂ : β,
        ∑ z : γ, ∑ e₂ : ℳ.env, star (ℳ.isom (z, e₂) y₁) * ℳ.isom (z, e₂) y₂ =
          if y₁ = y₂ then (1 : ℂ) else 0 := by
      intro y₁ y₂
      have h := congr_fun (congr_fun ℳ.isom_eq y₁) y₂
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Matrix.one_apply] using h
    simp_rw [hM]
    have hdiag : ∑ y₁ : β, ∑ y₂ : β,
        (if y₁ = y₂ then (1 : ℂ) else 0) *
          ∑ e₁ : 𝒩.env, star (𝒩.isom (y₁, e₁) x₁) * 𝒩.isom (y₂, e₁) x₂ =
        ∑ y : β, ∑ e₁ : 𝒩.env, star (𝒩.isom (y, e₁) x₁) * 𝒩.isom (y, e₁) x₂ := by
      apply Finset.sum_congr rfl; intro y₁ _
      rw [Finset.sum_eq_single y₁]
      · simp
      · intro y₂ _ hne; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ y₁) h
    rw [hdiag]
    have hN := congr_fun (congr_fun 𝒩.isom_eq x₁) x₂
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.one_apply] using hN

/-- Apply a CPTP map `𝒩` by acting directly on a pure state vector `ψ : α → ℂ`, producing a
density operator on `β` (equal to `𝒩.apply (pureState ψ hψ)`). -/
lemma CPTPMap.apply_pureState {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (𝒩 : CPTPMap.{0} α β) (ψ : α → ℂ)
    (hψ : ∑ a : α, ‖ψ a‖ ^ 2 = 1) :
    (𝒩.apply (pureState ψ hψ)).mat =
      let φ : β × 𝒩.env → ℂ := fun p ↦ ∑ a : α, 𝒩.isom p a * ψ a
      Matrix.of fun b₁ b₂ ↦ ∑ e : 𝒩.env, φ (b₁, e) * star (φ (b₂, e)) := by
  letI := 𝒩.fintypeEnv; letI := 𝒩.decEqEnv
  ext b₁ b₂
  simp only [CPTPMap.apply, CPTPMap.toLinearMap, partialTrace₂Mat, pureState, Matrix.of_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl; intro e _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  simp only [star_sum, star_mul']
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a₁ _
  apply Finset.sum_congr rfl; intro a₂ _
  ring

/-- Maximally entangled state `|Φ^+_α⟩⟨Φ^+_α|` on `α × α`. -/
noncomputable def maxEntangledVec (α : Type) [Fintype α] [DecidableEq α] : α × α → ℂ :=
  fun p ↦ if p.1 = p.2 then ((Real.sqrt (Fintype.card α) : ℝ) : ℂ)⁻¹ else 0

lemma maxEntangledVec_norm (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] :
    ∑ p : α × α, ‖maxEntangledVec α p‖ ^ 2 = 1 := by
  rw [Fintype.sum_prod_type]
  have hrow : ∀ a : α, ∑ b : α, ‖maxEntangledVec α (a, b)‖ ^ 2 = (Fintype.card α : ℝ)⁻¹ := by
    intro a
    rw [Finset.sum_eq_single a]
    · simp only [maxEntangledVec, ↓reduceIte, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    · intro b _ hne; simp [maxEntangledVec, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ a) h
  simp_rw [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

noncomputable def maxEntangledState (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] :
    DensityOp (α × α) :=
  pureState (maxEntangledVec α) (maxEntangledVec_norm α)

end CPTPCombinators

section UhlmannAndGentle

/-- Pure-state trace distance formula in terms of inner product:
`T(|u⟩⟨u|, |v⟩⟨v|) = √(1 - |⟨u|v⟩|²)`. -/
lemma traceDist_pureState_eq {α : Type*} [Fintype α] [DecidableEq α]
    (u v : α → ℂ) (hu : ∑ a, ‖u a‖ ^ 2 = 1) (hv : ∑ a, ‖v a‖ ^ 2 = 1) :
    traceDist (pureState u hu) (pureState v hv) ≤
      Real.sqrt (1 - ‖∑ a : α, star (u a) * v a‖ ^ 2) := by
  have hfv := traceDist_le_sqrt_one_sub_rootFidelity_sq (pureState u hu) (pureState v hv)
  have hfid : ‖∑ a : α, star (u a) * v a‖ ≤ rootFidelity (pureState u hu) (pureState v hv) := by
    -- Direct computation: `F(|u⟩⟨u|, |v⟩⟨v|) = |⟨u|v⟩|`
    set P₀ := pureState u hu
    set P₁ := pureState v hv
    have hP₀_sq : P₀.mat * P₀.mat = P₀.mat := by
      ext i j
      simp only [P₀, pureState, Matrix.mul_apply, Matrix.of_apply]
      have hnorm : ∑ k : α, star (u k) * u k = 1 := by
        have h1 : ∀ k, star (u k) * u k = ((‖u k‖ ^ 2 : ℝ) : ℂ) := fun k ↦ by
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        simp_rw [h1, ← Complex.ofReal_sum, hu, Complex.ofReal_one]
      calc ∑ k : α, u i * star (u k) * (u k * star (u j))
          = u i * (∑ k : α, star (u k) * u k) * star (u j) := by
              rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; ring
        _ = u i * star (u j) := by rw [hnorm, mul_one]
    have hP₁_sq : P₁.mat * P₁.mat = P₁.mat := by
      ext i j
      simp only [P₁, pureState, Matrix.mul_apply, Matrix.of_apply]
      have hnorm : ∑ k : α, star (v k) * v k = 1 := by
        have h1 : ∀ k, star (v k) * v k = ((‖v k‖ ^ 2 : ℝ) : ℂ) := fun k ↦ by
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        simp_rw [h1, ← Complex.ofReal_sum, hv, Complex.ofReal_one]
      calc ∑ k : α, v i * star (v k) * (v k * star (v j))
          = v i * (∑ k : α, star (v k) * v k) * star (v j) := by
              rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; ring
        _ = v i * star (v j) := by rw [hnorm, mul_one]
    have hsq0 : P₀.sqrtMat = P₀.mat :=
      (P₀.sqrtMat_unique P₀.posSemidef hP₀_sq).symm
    have hsq1 : P₁.sqrtMat = P₁.mat :=
      (P₁.sqrtMat_unique P₁.posSemidef hP₁_sq).symm
    have htr : (P₀.sqrtMat * P₁.sqrtMat).trace =
        (∑ a : α, star (u a) * v a) * star (∑ a : α, star (u a) * v a) := by
      rw [hsq0, hsq1]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, P₀, P₁, pureState, Matrix.of_apply]
      rw [star_sum, Finset.sum_mul]
      simp_rw [Finset.mul_sum, star_mul', star_star]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      ring
    -- Use `re_trace_unitary_mul_le_traceNorm` with phase unitary `e^{iθ} I`
    set c : ℂ := ∑ a : α, star (u a) * v a
    by_cases hc : c = 0
    · rw [hc, norm_zero]; exact rootFidelity_nonneg _ _
    · -- Compute `rootFidelity P₀ P₁` directly via `P₀.mat * P₁.mat * P₀.mat = ‖c‖² • P₀.mat`
      have hprod : P₀.sqrtMat * P₁.mat * P₀.sqrtMat = ((‖c‖ ^ 2 : ℝ) : ℂ) • P₀.mat := by
        rw [hsq0]
        ext i j
        simp only [P₀, P₁, pureState, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
          smul_eq_mul]
        have hc2 : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * star c := by
          rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [hc2]
        simp only [c, star_sum, star_mul', star_star]
        calc ∑ k : α, (∑ l : α, u i * star (u l) * (v l * star (v k))) * (u k * star (u j))
            = ∑ k : α, ∑ l : α, u i * star (u l) * (v l * star (v k)) * (u k * star (u j)) := by
                apply Finset.sum_congr rfl; intro k _; rw [Finset.sum_mul]
          _ = ((∑ l : α, star (u l) * v l) * ∑ k : α, u k * star (v k)) * (u i * star (u j)) := by
                conv_rhs => simp_rw [Finset.sum_mul, Finset.mul_sum]
                conv_rhs => rw [Finset.sum_comm]
                apply Finset.sum_congr rfl; intro k _
                apply Finset.sum_congr rfl; intro l _; ring
      -- Eigenvalues of `‖c‖² • P₀.mat`: trace of `√(‖c‖² • P₀)` = `‖c‖ * Tr(√P₀) = ‖c‖ * Tr(P₀) = ‖c‖`
      unfold rootFidelity
      have hH := posSemidef_sqrt_mul_sqrt P₀ P₁ |>.isHermitian
      have hP0_eigs : ∑ i : α, Real.sqrt (P₀.isHermitian.eigenvalues i) = 1 := by
        have htr0 : P₀.sqrtMat.trace = ∑ i : α, (Real.sqrt (P₀.isHermitian.eigenvalues i) : ℂ) := by
          unfold DensityOp.sqrtMat
          rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
          rfl
        rw [hsq0, P₀.trace_one] at htr0
        have := congr_arg Complex.re htr0.symm
        simpa [Complex.re_sum] using this
      have hcp : (P₀.sqrtMat * P₁.mat * P₀.sqrtMat).charpoly =
          (((‖c‖ ^ 2 : ℝ) : ℂ) • P₀.mat).charpoly := congr_arg Matrix.charpoly hprod
      have hsm_herm : (((‖c‖ ^ 2 : ℝ) : ℂ) • P₀.mat).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
          P₀.isHermitian.eq]
      have hsum1 := spectral_sum_eq_of_charpoly_mul_X_pow (f := Real.sqrt) (k := 0) (l := 0)
        hH hsm_herm (by rw [hcp]) Real.sqrt_zero
      rw [hsum1]
      -- Now relate `spectral_sum` of `r • P₀.mat` to `√r * spectral_sum P₀.mat`
      set U0 : Matrix α α ℂ := (P₀.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
      have hD_eq : (((‖c‖ ^ 2 : ℝ) : ℂ) • P₀.mat) =
          U0 * Matrix.diagonal (fun i : α ↦ ((‖c‖ ^ 2 * P₀.isHermitian.eigenvalues i : ℝ) : ℂ)) * star U0 := by
        have hspec : P₀.mat = U0 * Matrix.diagonal (Complex.ofReal ∘ P₀.isHermitian.eigenvalues) * star U0 := by
          simpa [U0, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using P₀.isHermitian.spectral_theorem
        conv_lhs => rw [hspec]
        rw [← Matrix.smul_mul, ← Matrix.mul_smul]
        congr 2; ext i j; simp only [Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply,
          smul_eq_mul]
        split_ifs <;> simp [Complex.ofReal_mul]
      have hD_herm : (Matrix.diagonal (fun i : α ↦ ((‖c‖ ^ 2 * P₀.isHermitian.eigenvalues i : ℝ) : ℂ))).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext i; simp
      have hcp2 : ((((‖c‖ ^ 2 : ℝ) : ℂ) • P₀.mat)).charpoly =
          (Matrix.diagonal (fun i : α ↦ ((‖c‖ ^ 2 * P₀.isHermitian.eigenvalues i : ℝ) : ℂ))).charpoly := by
        rw [hD_eq]
        have hsim := Matrix.charpoly_mul_comm
          (U0 * Matrix.diagonal (fun i : α ↦ ((‖c‖ ^ 2 * P₀.isHermitian.eigenvalues i : ℝ) : ℂ))) (star U0)
        rw [hsim, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]
      have hsum2 := spectral_sum_eq_of_charpoly_mul_X_pow (f := Real.sqrt) (k := 0) (l := 0)
        hsm_herm hD_herm (by rw [hcp2]) Real.sqrt_zero
      rw [hsum2, spectral_sum_diagonal (fun i ↦ ‖c‖ ^ 2 * P₀.isHermitian.eigenvalues i) hD_herm (by simp)]
      have hsqrt_mul : ∑ i : α, Real.sqrt (‖c‖ ^ 2 * P₀.isHermitian.eigenvalues i) =
          ‖c‖ * ∑ i : α, Real.sqrt (P₀.isHermitian.eigenvalues i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]
      rw [hsqrt_mul, hP0_eigs, mul_one]
  exact hfv.trans (Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (∑ a : α, star (u a) * v a)]))

/-- **Uhlmann Unitary Theorem on a Fixed Purification Register**:
Given two purifications `u, v : A × B → ℂ` of density operators `ρ_A, σ_A : DensityOp A`,
there exists a unitary `U : Matrix.unitaryGroup B ℂ` acting on `B` alone such that
`T((I_A ⊗ U)|u⟩⟨u|(I_A ⊗ U)ᴴ, |v⟩⟨v|) ≤ √(1 - F(ρ_A, σ_A)²)`. -/
theorem exists_uhlmann_unitary {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (ρ σ : DensityOp A)
    (u v : A × B → ℂ) (hu : ∑ p, ‖u p‖ ^ 2 = 1) (hv : ∑ p, ‖v p‖ ^ 2 = 1)
    (hpt_u : partialTrace₂Mat A B (pureState u hu).mat = ρ.mat)
    (hpt_v : partialTrace₂Mat A B (pureState v hv).mat = σ.mat) :
    ∃ U : Matrix B B ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      rootFidelity ρ σ =
        ‖∑ p : A × B, star (v p) * ∑ b' : B, U p.2 b' * u (p.1, b')‖ := by
  let Mu : Matrix A B ℂ := Matrix.of fun a b ↦ u (a, b)
  let Mv : Matrix A B ℂ := Matrix.of fun a b ↦ v (a, b)
  have hMu : Mu * Muᴴ = ρ.mat := by
    rw [← hpt_u]
    ext a₁ a₂
    simp [Mu, partialTrace₂Mat, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hMv : Mv * Mvᴴ = σ.mat := by
    rw [← hpt_v]
    ext a₁ a₂
    simp [Mv, partialTrace₂Mat, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply]
  let X : Matrix B B ℂ := Mvᴴ * Mu
  obtain ⟨W, hW⟩ := exists_unitary_trace_eq_traceNorm X
  let Umat : Matrix B B ℂ := Matrix.of fun b₁ b₂ ↦ star ((W : Matrix B B ℂ) b₁ b₂)
  have hU_mem : Umat ∈ Matrix.unitaryGroup B ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext b₁ b₂
    have h := congr_fun (congr_fun (Unitary.coe_star_mul_self W) b₁) b₂
    have h' := congr_arg star h
    simp only [Umat, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply,
      star_sum, star_mul', star_star] at h' ⊢
    rw [show (∑ x : B, (W : Matrix B B ℂ) x b₁ * star ((W : Matrix B B ℂ) x b₂)) =
        (∑ x : B, star ((W : Matrix B B ℂ) x b₂) * (W : Matrix B B ℂ) x b₁) from
        Finset.sum_congr rfl (fun x _ ↦ mul_comm _ _)] at h'
    rw [show (∑ x : B, (W : Matrix B B ℂ) x b₁ * star ((W : Matrix B B ℂ) x b₂)) =
        (∑ x : B, star ((W : Matrix B B ℂ) x b₂) * (W : Matrix B B ℂ) x b₁) from
        Finset.sum_congr rfl (fun x _ ↦ mul_comm _ _)]
    rw [h']
    by_cases hb : b₁ = b₂ <;> simp [hb]
  let U : Matrix.unitaryGroup B ℂ := ⟨Umat, hU_mem⟩
  let u' : A × B → ℂ := fun p ↦ ∑ b' : B, (U : Matrix B B ℂ) p.2 b' * u (p.1, b')
  have hu' : ∑ p : A × B, ‖u' p‖ ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    have hrow : ∀ a : A, ∑ b : B, ‖u' (a, b)‖ ^ 2 = ∑ b : B, ‖u (a, b)‖ ^ 2 := by
      intro a
      have hC : ((∑ b : B, ‖u' (a, b)‖ ^ 2 : ℝ) : ℂ) = ((∑ b : B, ‖u (a, b)‖ ^ 2 : ℝ) : ℂ) := by
        simp only [Complex.ofReal_sum]
        have h1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := fun z ↦ by
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        simp_rw [h1]
        simp only [u', star_sum, star_mul]
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        calc ∑ b : B, ∑ b₁ : B, ∑ b₂ : B,
              star (u (a, b₁)) * star ((U : Matrix B B ℂ) b b₁) * ((U : Matrix B B ℂ) b b₂ * u (a, b₂))
            = ∑ b₁ : B, ∑ b₂ : B,
                (∑ b : B, star ((U : Matrix B B ℂ) b b₁) * (U : Matrix B B ℂ) b b₂) *
                (star (u (a, b₁)) * u (a, b₂)) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro b₁ _
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro b₂ _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl; intro b _; ring
          _ = ∑ b₁ : B, ∑ b₂ : B, (if b₁ = b₂ then (1 : ℂ) else 0) * (star (u (a, b₁)) * u (a, b₂)) := by
              apply Finset.sum_congr rfl; intro b₁ _
              apply Finset.sum_congr rfl; intro b₂ _
              congr 1
              have h := congr_fun (congr_fun (Unitary.coe_star_mul_self U) b₁) b₂
              simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h
          _ = ∑ b : B, star (u (a, b)) * u (a, b) := by
              apply Finset.sum_congr rfl; intro b₁ _
              rw [Finset.sum_eq_single b₁]
              · simp
              · intro b₂ _ hne; simp [Ne.symm hne]
              · intro h; exact absurd (Finset.mem_univ b₁) h
      exact Complex.ofReal_injective hC
    simp_rw [hrow]
    rw [← Fintype.sum_prod_type (f := fun p : A × B ↦ ‖u p‖ ^ 2)]
    exact hu
  have hov : ∑ p : A × B, star (v p) * u' p = (traceNorm X : ℂ) := by
    rw [← hW]
    rw [Fintype.sum_prod_type]
    simp only [u', U, Umat, X, Mv, Mu, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    calc ∑ a : A, ∑ b : B, ∑ b' : B, star (v (a, b)) * (star ((W : Matrix B B ℂ) b b') * u (a, b'))
        = ∑ b' : B, ∑ b : B, ∑ a : A, star ((W : Matrix B B ℂ) b b') * (star (v (a, b)) * u (a, b')) := by
          rw [Finset.sum_comm]
          conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro b' _
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro a _; ring
      _ = _ := by
          apply Finset.sum_congr rfl; intro b' _
          apply Finset.sum_congr rfl; intro b _
          rfl
  -- Now show `traceNorm X = rootFidelity ρ σ`
  have htn_eq : traceNorm X = rootFidelity ρ σ := by
    unfold traceNorm rootFidelity
    have hXHX : Xᴴ * X = Muᴴ * σ.mat * Mu := by
      simp only [X, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
        ← Matrix.mul_assoc Mv Mvᴴ, hMv]
    have hcp1 : (Muᴴ * (σ.mat * Mu)).charpoly * Polynomial.X ^ Fintype.card A =
        ((σ.mat * Mu) * Muᴴ).charpoly * Polynomial.X ^ Fintype.card B := by
      -- Sylvester's identity for rectangular matrices
      let P : Matrix (B ⊕ A) (B ⊕ A) ℂ := Matrix.fromBlocks 0 Muᴴ 0 0
      let Q : Matrix (B ⊕ A) (B ⊕ A) ℂ := Matrix.fromBlocks 0 0 (σ.mat * Mu) 0
      have hPQ : P * Q = Matrix.fromBlocks (Muᴴ * (σ.mat * Mu)) 0 0 0 := by
        simp [P, Q, Matrix.fromBlocks_multiply]
      have hQP : Q * P = Matrix.fromBlocks 0 0 0 ((σ.mat * Mu) * Muᴴ) := by
        simp [P, Q, Matrix.fromBlocks_multiply]
      have hzA : (0 : Matrix A A ℂ).charpoly = Polynomial.X ^ Fintype.card A := by
        rw [show (0 : Matrix A A ℂ) = Matrix.diagonal (fun _ : A ↦ (0 : ℂ)) by ext; simp]
        rw [charpoly_diagonal_complex]; simp [Finset.prod_const]
      have hzB : (0 : Matrix B B ℂ).charpoly = Polynomial.X ^ Fintype.card B := by
        rw [show (0 : Matrix B B ℂ) = Matrix.diagonal (fun _ : B ↦ (0 : ℂ)) by ext; simp]
        rw [charpoly_diagonal_complex]; simp [Finset.prod_const]
      have hc := Matrix.charpoly_mul_comm P Q
      rw [hPQ, hQP, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_fromBlocks_zero₁₂,
        hzA, hzB, mul_comm (Polynomial.X ^ Fintype.card B)] at hc
      exact hc
    have hcp2 : (σ.mat * ρ.mat).charpoly = (ρ.sqrtMat * σ.mat * ρ.sqrtMat).charpoly := by
      have h1 := Matrix.charpoly_mul_comm (σ.mat * ρ.sqrtMat) ρ.sqrtMat
      have hL : (σ.mat * ρ.sqrtMat) * ρ.sqrtMat = σ.mat * ρ.mat := by
        rw [Matrix.mul_assoc, ρ.sqrtMat_mul_self]
      have hR : ρ.sqrtMat * (σ.mat * ρ.sqrtMat) = ρ.sqrtMat * σ.mat * ρ.sqrtMat := by
        rw [Matrix.mul_assoc]
      rw [← hL, ← hR]; exact h1
    have hcp_final : (Xᴴ * X).charpoly * Polynomial.X ^ Fintype.card A =
        (ρ.sqrtMat * σ.mat * ρ.sqrtMat).charpoly * Polynomial.X ^ Fintype.card B := by
      rw [hXHX, Matrix.mul_assoc Muᴴ σ.mat Mu, hcp1, Matrix.mul_assoc σ.mat Mu Muᴴ, hMu, hcp2]
    exact spectral_sum_eq_of_charpoly_mul_X_pow (f := Real.sqrt)
      (Matrix.posSemidef_conjTranspose_mul_self X).isHermitian
      (posSemidef_sqrt_mul_sqrt ρ σ).isHermitian hcp_final Real.sqrt_zero
  refine ⟨(U : Matrix B B ℂ), ?_, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  · simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  · rw [hov, Complex.norm_real, Real.norm_eq_abs, htn_eq,
      abs_of_nonneg (rootFidelity_nonneg ρ σ)]

/-- Operator square root of any positive semidefinite matrix `M ≽ 0`. -/
noncomputable def psdSqrt {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matrix α α ℂ} (hM : M.PosSemidef) : Matrix α α ℂ :=
  (hM.isHermitian.eigenvectorUnitary : Matrix α α ℂ) *
    Matrix.diagonal (fun i ↦ (Real.sqrt (hM.isHermitian.eigenvalues i) : ℂ)) *
    star (hM.isHermitian.eigenvectorUnitary : Matrix α α ℂ)

lemma psdSqrt_isHermitian {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matrix α α ℂ} (hM : M.PosSemidef) : (psdSqrt hM).IsHermitian := by
  unfold psdSqrt
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.diagonal_conjTranspose, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]
  congr 2; ext i j; simp [Matrix.diagonal_apply]

lemma psdSqrt_mul_self {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matrix α α ℂ} (hM : M.PosSemidef) : psdSqrt hM * psdSqrt hM = M := by
  unfold psdSqrt
  set U : Matrix α α ℂ := (hM.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hM.isHermitian.eigenvectorUnitary
  have hspec : M = U * Matrix.diagonal (Complex.ofReal ∘ hM.isHermitian.eigenvalues) * star U := by
    simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM.isHermitian.spectral_theorem
  calc (U * Matrix.diagonal (fun i ↦ (Real.sqrt (hM.isHermitian.eigenvalues i) : ℂ)) * star U) *
        (U * Matrix.diagonal (fun i ↦ (Real.sqrt (hM.isHermitian.eigenvalues i) : ℂ)) * star U)
      = U * (Matrix.diagonal (fun i ↦ (Real.sqrt (hM.isHermitian.eigenvalues i) : ℂ)) *
          (star U * U) *
          Matrix.diagonal (fun i ↦ (Real.sqrt (hM.isHermitian.eigenvalues i) : ℂ))) * star U := by
          simp only [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (Complex.ofReal ∘ hM.isHermitian.eigenvalues) * star U := by
          rw [hU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          congr 3; ext i; simp only [Function.comp_apply]
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hM.eigenvalues_nonneg i)]
    _ = M := hspec.symm

lemma psdSqrt_ge_self_of_le_one {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matrix α α ℂ} (hM : M.PosSemidef) (hM1 : (1 - M).PosSemidef) :
    (psdSqrt hM - M).PosSemidef := by
  set U : Matrix α α ℂ := (hM.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
  have hspec : M = U * Matrix.diagonal (Complex.ofReal ∘ hM.isHermitian.eigenvalues) * star U := by
    simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM.isHermitian.spectral_theorem
  have hle1 : ∀ i : α, hM.isHermitian.eigenvalues i ≤ 1 := by
    intro i
    set v : α → ℂ := fun k ↦ U k i
    have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM1).2 v
    have hU_l : star U * U = 1 := Unitary.coe_star_mul_self hM.isHermitian.eigenvectorUnitary
    have h1 : star U *ᵥ v = Pi.single i 1 := by
      ext k
      have h := congr_fun (congr_fun hU_l k) i
      simpa [v, U, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
        Pi.single_apply, eq_comm] using h
    have hv1 : star v ⬝ᵥ v = 1 := by
      have h := congr_fun (congr_fun hU_l i) i
      simpa [v, Matrix.mul_apply, dotProduct, Pi.star_apply, Matrix.star_apply, Matrix.one_apply] using h
    have hvM : star v ⬝ᵥ (M *ᵥ v) = (hM.isHermitian.eigenvalues i : ℂ) := by
      conv_lhs => rw [hspec]
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1]
      have h2 : Matrix.diagonal (Complex.ofReal ∘ hM.isHermitian.eigenvalues) *ᵥ Pi.single i (1 : ℂ) =
          Pi.single i (hM.isHermitian.eigenvalues i : ℂ) := by
        ext k; simp only [Matrix.mulVec_diagonal, Pi.single_apply, Function.comp_apply]
        split_ifs with hk
        · subst hk; simp
        · simp
      rw [h2]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.single_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have : ∑ k : α, star (v k) * (U k i * (hM.isHermitian.eigenvalues i : ℂ)) =
          (star v ⬝ᵥ v) * (hM.isHermitian.eigenvalues i : ℂ) := by
        rw [dotProduct, Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; simp [v]; ring
      rw [this, hv1, one_mul]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hv1, hvM] at hq
    rw [Complex.le_def] at hq
    simpa using hq.1
  have hdiff : psdSqrt hM - M =
      U * Matrix.diagonal (fun i ↦ ((Real.sqrt (hM.isHermitian.eigenvalues i) - hM.isHermitian.eigenvalues i : ℝ) : ℂ)) * star U := by
    unfold psdSqrt
    conv_lhs => arg 2; rw [hspec]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2; ext i j; simp only [Matrix.sub_apply, Matrix.diagonal_apply, Function.comp_apply]
    split_ifs <;> simp
  rw [hdiff]
  have hD : (Matrix.diagonal (fun i ↦ ((Real.sqrt (hM.isHermitian.eigenvalues i) - hM.isHermitian.eigenvalues i : ℝ) : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; intro i
    rw [Complex.zero_le_real]
    have hnn := hM.eigenvalues_nonneg i
    have h1 := hle1 i
    have hsq : hM.isHermitian.eigenvalues i ^ 2 ≤ hM.isHermitian.eigenvalues i := by nlinarith
    have hle := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hnn] at hle
    linarith
  simpa [Matrix.star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same U

end UhlmannAndGentle


section CoherentCSSPolarCoding

variable {d : Type} [Fintype d] [DecidableEq d]

/-- Walsh–Hadamard phase sign `(-1)^{v · r}` on `α → Bool`. -/
def phaseSign {α : Type*} [Fintype α] (v r : α → Bool) : ℂ :=
  ∏ i : α, if v i && r i then (-1 : ℂ) else (1 : ℂ)

lemma phaseSign_star {α : Type*} [Fintype α] (v r : α → Bool) :
    star (phaseSign v r) = phaseSign v r := by
  simp only [phaseSign, star_prod]
  apply Finset.prod_congr rfl; intro i _
  cases v i <;> cases r i <;> simp

lemma phaseSign_mul_self {α : Type*} [Fintype α] (v r : α → Bool) :
    phaseSign v r * phaseSign v r = 1 := by
  simp only [phaseSign, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one; intro i _
  cases v i <;> cases r i <;> simp

lemma phaseSign_mul_right {α : Type*} [Fintype α] (v r₁ r₂ : α → Bool) :
    phaseSign v r₁ * phaseSign v r₂ = phaseSign v (fun i ↦ xor (r₁ i) (r₂ i)) := by
  simp only [phaseSign, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro i _
  rcases Bool.eq_false_or_eq_true (v i) with hv | hv <;>
    rcases Bool.eq_false_or_eq_true (r₁ i) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (r₂ i) with h2 | h2 <;>
    simp [hv, h1, h2]

lemma sum_phaseSign_mul {α : Type*} [Fintype α] [DecidableEq α] (r₁ r₂ : α → Bool) :
    ∑ v : α → Bool, phaseSign v r₁ * phaseSign v r₂ =
      if r₁ = r₂ then ((2 : ℝ) ^ Fintype.card α : ℂ) else 0 := by
  simp_rw [phaseSign_mul_right, phaseSign]
  rw [← Fintype.prod_sum (fun i b ↦ if (b && xor (r₁ i) (r₂ i)) = true then (-1 : ℂ) else (1 : ℂ))]
  by_cases h : r₁ = r₂
  · subst h; rw [if_pos rfl]
    have h1 : ∀ i : α, ∑ b : Bool, (if b && xor (r₁ i) (r₁ i) then (-1 : ℂ) else (1 : ℂ)) = 2 := by
      intro i; cases r₁ i <;> simp [Fintype.sum_bool] <;> norm_num
    simp_rw [h1, Finset.prod_const, Finset.card_univ]; push_cast; rfl
  · rw [if_neg h]
    have hex : ∃ i : α, r₁ i ≠ r₂ i := by
      by_contra hall; push Not at hall; exact h (funext hall)
    obtain ⟨i₀, hi₀⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i₀)
    cases h1 : r₁ i₀ <;> cases h2 : r₂ i₀
    · exact absurd (h1.trans h2.symm) hi₀
    · simp [Fintype.sum_bool]
    · simp [Fintype.sum_bool]
    · exact absurd (h1.trans h2.symm) hi₀

/-- Phase-randomized coherent CSS quantum polar encoder isometry: maps logical qubits
`m : infoSet → Bool` and Alice's entanglement-assistance qubits `a : assistSet → Bool` to
`Fin (2^n) → Bool` by preparing `2^{-|R|/2} ∑_r (-1)^{v · r} |arikanTransform n (wiretapWord ... m r a)⟩`. -/
noncomputable def cssPolarEncoderIsom (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (uF : Fin (2 ^ n) → Bool) (v : randSet → Bool) :
    Matrix (Fin (2 ^ n) → Bool) ((infoSet → Bool) × (assistSet → Bool)) ℂ :=
  Matrix.of fun x p ↦
    ((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹ *
      ∑ r : randSet → Bool,
        if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF p.1 r p.2) then
          phaseSign v r
        else 0

lemma cssPolarEncoderIsom_isometry (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (hdisj_ir : Disjoint infoSet randSet)
    (hdisj_ia : Disjoint infoSet assistSet)
    (hdisj_ra : Disjoint randSet assistSet)
    (uF : Fin (2 ^ n) → Bool) (v : randSet → Bool) :
    (cssPolarEncoderIsom n infoSet randSet assistSet uF v)ᴴ *
      cssPolarEncoderIsom n infoSet randSet assistSet uF v = 1 := by
  have hinj : ∀ m₁ m₂ r₁ r₂ a₁ a₂,
      arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) =
      arikanTransform n (wiretapWord infoSet randSet assistSet uF m₂ r₂ a₂) →
      m₁ = m₂ ∧ r₁ = r₂ ∧ a₁ = a₂ := by
    intro m₁ m₂ r₁ r₂ a₁ a₂ heq
    have hw := arikanTransform_bijective n |>.injective heq
    refine ⟨?_, ?_, ?_⟩
    · funext ⟨i, hi⟩
      have h := congr_fun hw i
      simpa [wiretapWord, hi] using h
    · funext ⟨i, hi⟩
      have h := congr_fun hw i
      have hni : i ∉ infoSet := Finset.disjoint_right.mp hdisj_ir hi
      simpa [wiretapWord, hni, hi] using h
    · funext ⟨i, hi⟩
      have h := congr_fun hw i
      have hni : i ∉ infoSet := Finset.disjoint_right.mp hdisj_ia hi
      have hnr : i ∉ randSet := Finset.disjoint_right.mp hdisj_ra hi
      simpa [wiretapWord, hni, hnr, hi] using h
  ext ⟨m₁, a₁⟩ ⟨m₂, a₂⟩
  simp only [cssPolarEncoderIsom, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply, star_mul, star_sum, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hnorm : (((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹) *
      (((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹) =
      (((2 : ℝ) ^ randSet.card : ℝ) : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  calc ∑ x : Fin (2 ^ n) → Bool,
        (∑ r₁ : randSet → Bool, star (if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) then phaseSign v r₁ else 0)) *
          ((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹ *
        (((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹ *
          ∑ r₂ : randSet → Bool, if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m₂ r₂ a₂) then phaseSign v r₂ else 0)
      = (((2 : ℝ) ^ randSet.card : ℝ) : ℂ)⁻¹ *
          ∑ r₁ : randSet → Bool, ∑ r₂ : randSet → Bool,
            ∑ x : Fin (2 ^ n) → Bool,
              (if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) then phaseSign v r₁ else 0) *
              (if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m₂ r₂ a₂) then phaseSign v r₂ else 0) := by
        rw [Finset.mul_sum]
        conv_rhs => arg 2; ext r₁; rw [Finset.mul_sum]
        conv_rhs => arg 2; ext r₁; arg 2; ext r₂; rw [Finset.mul_sum]
        conv_rhs => arg 2; ext r₁; rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro x _
        have hst : ∀ r₁ : randSet → Bool,
            star (if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) then phaseSign v r₁ else 0) =
            if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) then phaseSign v r₁ else 0 := by
          intro r₁; split_ifs <;> simp [phaseSign_star]
        simp_rw [hst, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro r₁ _
        apply Finset.sum_congr rfl; intro r₂ _
        rw [← hnorm]; ring
    _ = (((2 : ℝ) ^ randSet.card : ℝ) : ℂ)⁻¹ *
          ∑ r₁ : randSet → Bool, ∑ r₂ : randSet → Bool,
            if arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) =
               arikanTransform n (wiretapWord infoSet randSet assistSet uF m₂ r₂ a₂) then
              phaseSign v r₁ * phaseSign v r₂
            else 0 := by
        congr 1; apply Finset.sum_congr rfl; intro r₁ _
        apply Finset.sum_congr rfl; intro r₂ _
        rw [Finset.sum_eq_single (arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁))]
        · simp [mul_ite]
        · intro x _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
    _ = if (m₁, a₁) = (m₂, a₂) then 1 else 0 := by
        by_cases hma : (m₁, a₁) = (m₂, a₂)
        · rw [if_pos hma]
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hma
          have hdiag : ∀ r₁ : randSet → Bool,
              ∑ r₂ : randSet → Bool,
                (if arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) =
                    arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₂ a₁) then
                  phaseSign v r₁ * phaseSign v r₂
                else 0) = 1 := by
            intro r₁
            rw [Finset.sum_eq_single r₁]
            · simp [phaseSign_mul_self]
            · intro r₂ _ hne; rw [if_neg]; intro heq; exact hne (hinj m₁ m₁ r₁ r₂ a₁ a₁ heq).2.1.symm
            · intro h; exact absurd (Finset.mem_univ r₁) h
          simp_rw [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_coe, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
          push_cast
          exact inv_mul_cancel₀ (by positivity)
        · rw [if_neg hma]
          have h0 : ∑ r₁ : randSet → Bool, ∑ r₂ : randSet → Bool,
              (if arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r₁ a₁) =
                  arikanTransform n (wiretapWord infoSet randSet assistSet uF m₂ r₂ a₂) then
                phaseSign v r₁ * phaseSign v r₂
              else 0) = 0 := by
            apply Finset.sum_eq_zero; intro r₁ _
            apply Finset.sum_eq_zero; intro r₂ _
            rw [if_neg]; intro heq
            obtain ⟨hm, _, ha⟩ := hinj m₁ m₂ r₁ r₂ a₁ a₂ heq
            exact hma (Prod.ext hm ha)
          rw [h0, mul_zero]

/-- Phase-randomized coherent CSS polar encoder as a pure isometric CPTP map. -/
noncomputable def cssPolarEncoder (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (hdisj_ir : Disjoint infoSet randSet)
    (hdisj_ia : Disjoint infoSet assistSet)
    (hdisj_ra : Disjoint randSet assistSet)
    (uF : Fin (2 ^ n) → Bool) (v : randSet → Bool) :
    CPTPMap.{0} ((infoSet → Bool) × (assistSet → Bool)) (Fin (2 ^ n) → Bool) where
  env := Unit
  fintypeEnv := inferInstance
  decEqEnv := inferInstance
  isom := Matrix.of fun p q ↦ cssPolarEncoderIsom n infoSet randSet assistSet uF v p.1 q
  isom_eq := by
    have h := cssPolarEncoderIsom_isometry n infoSet randSet assistSet hdisj_ir hdisj_ia hdisj_ra uF v
    ext q₁ q₂
    have hq := congr_fun (congr_fun h q₁) q₂
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type] using hq

/-- Operational entanglement-transmission output state on `R × M̂` (`(infoSet → Bool) × (infoSet → Bool)`):
Starting from `|Φ^+⟩_{RM} ⊗ |Φ^+⟩_{E_A E_B}`, Alice applies `ℰ` to `(M, E_A)`, sends `A^N` through
`𝒩^{⊗N}` to Bob, and Bob applies `𝒟` to `(B^N, E_B)` to output `M̂`. -/
noncomputable def entanglementChannelOutput (𝒩 : CPTPMap.{0} Bool d) (n : ℕ)
    (infoSet assistSet : Finset (Fin (2 ^ n)))
    (ℰ : CPTPMap.{0} ((infoSet → Bool) × (assistSet → Bool)) (Fin (2 ^ n) → Bool))
    (𝒟 : CPTPMap.{0} ((Fin (2 ^ n) → d) × (assistSet → Bool)) (infoSet → Bool)) :
    DensityOp ((infoSet → Bool) × (infoSet → Bool)) :=
  let initVec : (infoSet → Bool) × (((infoSet → Bool) × (assistSet → Bool)) × (assistSet → Bool)) → ℂ :=
    fun p ↦ maxEntangledVec (infoSet → Bool) (p.1, p.2.1.1) *
            maxEntangledVec (assistSet → Bool) (p.2.1.2, p.2.2)
  have hinit : ∑ p, ‖initVec p‖ ^ 2 = 1 := by
    simp only [initVec, norm_mul, mul_pow, Fintype.sum_prod_type]
    have h1 : ∀ m₁ m₂ : infoSet → Bool,
        ∑ a₁ : assistSet → Bool, ∑ a₂ : assistSet → Bool,
          ‖maxEntangledVec (infoSet → Bool) (m₁, m₂)‖ ^ 2 *
          ‖maxEntangledVec (assistSet → Bool) (a₁, a₂)‖ ^ 2 =
        ‖maxEntangledVec (infoSet → Bool) (m₁, m₂)‖ ^ 2 := by
      intro m₁ m₂
      simp_rw [← Finset.mul_sum]
      rw [← Fintype.sum_prod_type (f := fun p ↦ ‖maxEntangledVec (assistSet → Bool) p‖ ^ 2),
        maxEntangledVec_norm (assistSet → Bool), mul_one]
    simp_rw [h1]
    rw [← Fintype.sum_prod_type (f := fun p ↦ ‖maxEntangledVec (infoSet → Bool) p‖ ^ 2)]
    exact maxEntangledVec_norm (infoSet → Bool)
  let initState := pureState initVec hinit
  let aliceToBob : CPTPMap.{0} (((infoSet → Bool) × (assistSet → Bool)) × (assistSet → Bool))
      ((Fin (2 ^ n) → d) × (assistSet → Bool)) :=
    ((𝒩.tensorPow n).seqComp ℰ).tensor (CPTPMap.id (assistSet → Bool))
  let fullBob : CPTPMap.{0} (((infoSet → Bool) × (assistSet → Bool)) × (assistSet → Bool))
      (infoSet → Bool) :=
    𝒟.seqComp aliceToBob
  (CPTPMap.tensorIdLeft (infoSet → Bool) fullBob).apply initState

/-- Operational entanglement-transmission trace-distance error:
`T((id_R ⊗ 𝒟 ∘ 𝒩^{⊗N} ∘ ℰ)(Φ^+_{RM} ⊗ Φ^+_{E_A E_B}), Φ^+_{RM})`. -/
noncomputable def quantumEntanglementError (𝒩 : CPTPMap.{0} Bool d) (n : ℕ)
    (infoSet assistSet : Finset (Fin (2 ^ n)))
    (ℰ : CPTPMap.{0} ((infoSet → Bool) × (assistSet → Bool)) (Fin (2 ^ n) → Bool))
    (𝒟 : CPTPMap.{0} ((Fin (2 ^ n) → d) × (assistSet → Bool)) (infoSet → Bool)) : ℝ :=
  traceDist (entanglementChannelOutput 𝒩 n infoSet assistSet ℰ 𝒟)
    (maxEntangledState (infoSet → Bool))

end CoherentCSSPolarCoding

section CoherentDecoderTheorem

variable {d : Type} [Fintype d] [DecidableEq d]

private lemma nonempty_of_cptpMap (𝒩 : CPTPMap.{0} Bool d) : Nonempty d ∧ Nonempty 𝒩.env := by
  letI := 𝒩.fintypeEnv
  have h := congr_fun (congr_fun 𝒩.isom_eq false) false
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    Fintype.sum_prod_type] at h
  have hne_d : Nonempty d := by
    by_contra hd; rw [not_nonempty_iff] at hd; simp at h
  have hne_e : Nonempty 𝒩.env := by
    by_contra he; rw [not_nonempty_iff] at he; simp at h
  exact ⟨hne_d, hne_e⟩

private lemma sqrt_one_sub_norm_sq_le_sqrt_two_mul {c : ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (hre : 1 - ε ≤ c.re) :
    Real.sqrt (1 - ‖c‖ ^ 2) ≤ Real.sqrt (2 * ε) := by
  apply Real.sqrt_le_sqrt
  by_cases h1 : 1 ≤ ε
  · nlinarith [norm_nonneg c]
  · push Not at h1
    have hle : 1 - ε ≤ ‖c‖ := le_trans hre (Complex.re_le_norm c)
    nlinarith [sq_nonneg ε]

private lemma trace_mul_psd_re_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {A : Matrix α α ℂ} (hA : A.PosSemidef) (ρ : DensityOp α) :
    0 ≤ ((A * ρ.mat).trace).re := by
  have heq : (A * ρ.mat).trace = (ρ.sqrtMat * A * ρ.sqrtMatᴴ).trace := by
    symm
    rw [ρ.sqrtMat_isHermitian.eq, Matrix.trace_mul_cycle, ρ.sqrtMat_mul_self, Matrix.trace_mul_comm]
  rw [heq]
  have hpsd : (ρ.sqrtMat * A * ρ.sqrtMatᴴ).PosSemidef := hA.mul_mul_conjTranspose_same ρ.sqrtMat
  have htr := hpsd.isHermitian.trace_eq_sum_eigenvalues
  rw [htr, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ ↦ by simpa using hpsd.eigenvalues_nonneg i

private lemma productState_amp_eq_tensorPow_partialTrace (𝒩 : CPTPMap.{0} Bool d) (n : ℕ)
    (x : Fin (2 ^ n) → Bool) (y₁ y₂ : Fin (2 ^ n) → d) :
    (productState (ampChannel 𝒩) n x).mat y₁ y₂ =
      ∑ e : Fin (2 ^ n) → 𝒩.env,
        (𝒩.tensorPow n).isom (y₁, e) x * star ((𝒩.tensorPow n).isom (y₂, e) x) := by
  letI := 𝒩.fintypeEnv; letI := 𝒩.decEqEnv
  simp only [productState, productStateMat, Matrix.of_apply, CPTPMap.tensorPow, star_prod,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i e ↦ 𝒩.isom (y₁ i, e) (x i) * star (𝒩.isom (y₂ i, e) (x i)))]
  apply Finset.prod_congr rfl; intro i _
  have hamp : ((ampChannel 𝒩).out (x i)).mat (y₁ i) (y₂ i) =
      ∑ e : 𝒩.env, 𝒩.isom (y₁ i, e) (x i) * star (𝒩.isom (y₂ i, e) (x i)) := by
    simp only [ampChannel, CPTPMap.apply, CPTPMap.toLinearMap, partialTrace₂Mat,
      CQChannel.ketBraBool, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
    apply Finset.sum_congr rfl; intro e _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    cases x i <;> simp [Fintype.sum_bool]
  exact hamp

private lemma productState_comp_eq_tensorPow_partialTrace (𝒩 : CPTPMap.{0} Bool d) (n : ℕ)
    (x : Fin (2 ^ n) → Bool) (e₁ e₂ : Fin (2 ^ n) → 𝒩.env) :
    (productState (ampChannel 𝒩.complementary) n x).mat e₁ e₂ =
      ∑ y : Fin (2 ^ n) → d,
        (𝒩.tensorPow n).isom (y, e₁) x * star ((𝒩.tensorPow n).isom (y, e₂) x) := by
  letI := 𝒩.fintypeEnv; letI := 𝒩.decEqEnv
  simp only [productState, productStateMat, Matrix.of_apply, CPTPMap.tensorPow, star_prod,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i y ↦ 𝒩.isom (y, e₁ i) (x i) * star (𝒩.isom (y, e₂ i) (x i)))]
  apply Finset.prod_congr rfl; intro i _
  have hcomp : ((ampChannel 𝒩.complementary).out (x i)).mat (e₁ i) (e₂ i) =
      ∑ y : d, 𝒩.isom (y, e₁ i) (x i) * star (𝒩.isom (y, e₂ i) (x i)) := by
    simp only [ampChannel, CPTPMap.complementary, CPTPMap.apply, CPTPMap.toLinearMap,
      partialTrace₂Mat, CQChannel.ketBraBool, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
    apply Finset.sum_congr rfl; intro y _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    cases x i <;> simp [Fintype.sum_bool]
  exact hcomp

set_option maxHeartbeats 2400000 in
/-- **Operational Entanglement-Assisted Coherent CSS Quantum Polar Decoding Theorem (Renes–Wilde [10])**:
For any qubit-input quantum channel `𝒩`, blocklength `N = 2^n`, pairwise disjoint register sets
`(infoSet, randSet, assistSet)`, and public frozen vector `uF`, there exists a deterministic
phase choice `v : randSet → Bool` and a genuine coherent CPTP decoder
`𝒟 : CPTPMap ((Fin (2^n) → d) × (assistSet → Bool)) (infoSet → Bool)` such that
`T((id_R ⊗ 𝒟 ∘ 𝒩^⊗N ∘ ℰ_v)(Φ^+_{RM} ⊗ Φ^+_{E_A E_B}), Φ^+_{RM}) ≤ √(2 ε_Bob) + √(2 ε_sec)`. -/
theorem exists_coherent_css_decoder (𝒩 : CPTPMap.{0} Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (hdisj_ir : Disjoint infoSet randSet)
    (hdisj_ia : Disjoint infoSet assistSet)
    (hdisj_ra : Disjoint randSet assistSet)
    (uF : Fin (2 ^ n) → Bool) :
    ∃ (v : randSet → Bool)
      (𝒟 : CPTPMap.{0} ((Fin (2 ^ n) → d) × (assistSet → Bool)) (infoSet → Bool)),
      quantumEntanglementError 𝒩 n infoSet assistSet
        (cssPolarEncoder n infoSet randSet assistSet hdisj_ir hdisj_ia hdisj_ra uF v) 𝒟 ≤
      Real.sqrt (2 * wiretapBobError 𝒩 n infoSet randSet assistSet uF) +
        Real.sqrt (2 * wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF) := by
  letI := 𝒩.fintypeEnv; letI := 𝒩.decEqEnv
  obtain ⟨⟨d₀⟩, ⟨e₀_single⟩⟩ := nonempty_of_cptpMap 𝒩
  let M := infoSet → Bool
  let R := randSet → Bool
  let A := assistSet → Bool
  let Y := Fin (2 ^ n) → d
  let E := Fin (2 ^ n) → 𝒩.env
  let Anc := Y × A × R × E
  let B_tot := M × Anc
  letI : DecidableEq Anc := inferInstanceAs (DecidableEq (Y × A × R × E))
  letI : DecidableEq B_tot := inferInstanceAs (DecidableEq (M × Anc))
  let y₀ : Y := fun _ ↦ d₀
  let a₀ : A := fun _ ↦ false
  let r₀ : R := fun _ ↦ false
  let e₀ : E := fun _ ↦ e₀_single
  obtain ⟨V_isom, hV_def⟩ : ∃ V : Matrix (Y × E) (Fin (2 ^ n) → Bool) ℂ, V = (𝒩.tensorPow n).isom :=
    ⟨(𝒩.tensorPow n).isom, rfl⟩
  have hV_orth : ∀ (x₁ x₂ : Fin (2 ^ n) → Bool),
      ∑ e : E, ∑ y : Y, star (V_isom (y, e) x₁) * V_isom (y, e) x₂ =
        if x₁ = x₂ then (1 : ℂ) else 0 := by
    intro x₁ x₂
    rw [hV_def]
    have h := congr_fun (congr_fun (𝒩.tensorPow n).isom_eq x₁) x₂
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fintype.sum_prod_type] at h
    rw [Finset.sum_comm]
    exact h
  let eMR : (M × R) ≃ ({i : Fin (2 ^ n) // i ∈ infoSet ∪ randSet} → Bool) :=
    { toFun := fun mr ⟨i, hi⟩ ↦
        if h : i ∈ infoSet then mr.1 ⟨i, h⟩
        else mr.2 ⟨i, (Finset.mem_union.mp hi).resolve_left h⟩
      invFun := fun w ↦
        (fun ⟨i, hi⟩ ↦ w ⟨i, Finset.mem_union_left _ hi⟩,
         fun ⟨i, hi⟩ ↦ w ⟨i, Finset.mem_union_right _ hi⟩)
      left_inv := fun ⟨m, r⟩ ↦ by
        apply Prod.ext
        · funext ⟨i, hi⟩; simp [hi]
        · funext ⟨i, hi⟩
          have hni : i ∉ infoSet := Finset.disjoint_right.mp hdisj_ir hi
          simp [hni]
      right_inv := fun w ↦ by
        funext ⟨i, hi⟩; by_cases h : i ∈ infoSet <;> simp [h] }
  have hemb_eq : ∀ (a : A) (m : M) (r : R),
      embedMsg (infoSet ∪ randSet) (bobEffectiveFrozen assistSet uF a) (eMR (m, r)) =
        wiretapWord infoSet randSet assistSet uF m r a := by
    intro a m r; funext i
    by_cases hi : i ∈ infoSet
    · simp [embedMsg, eMR, wiretapWord, Finset.mem_union_left _ hi, hi]
    · by_cases hr : i ∈ randSet
      · simp [embedMsg, eMR, wiretapWord, Finset.mem_union_right _ hr, hi, hr]
      · have hnot : i ∉ infoSet ∪ randSet := by simp [hi, hr]
        by_cases ha : i ∈ assistSet
        · simp [embedMsg, bobEffectiveFrozen, wiretapWord, hnot, hi, hr, ha]
        · simp [embedMsg, bobEffectiveFrozen, wiretapWord, hnot, hi, hr, ha]
  let C_qsc (a : A) := qscPolarCode (ampChannel 𝒩) n (infoSet ∪ randSet) (bobEffectiveFrozen assistSet uF a)
  let K (a : A) (m : M) (r : R) : Matrix Y Y ℂ :=
    psdSqrt ((C_qsc a).povm_posSemidef (eMR (m, r)))
  let W_Z : Matrix B_tot (Y × A) ℂ :=
    Matrix.of fun b ya ↦
      if b.2.2.1 = ya.2 ∧ b.2.2.2.2 = e₀ then K ya.2 b.1 b.2.2.2.1 b.2.1 ya.1 else 0
  have hWZ_isom : W_Zᴴ * W_Z = 1 := by
    ext ⟨y₁, a₁⟩ ⟨y₂, a₂⟩
    simp only [W_Z, B_tot, Anc, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.one_apply, Fintype.sum_prod_type]
    by_cases ha : a₁ = a₂
    · subst ha
      have hsum : ∑ m : M, ∑ y : Y, ∑ a' : A, ∑ r : R, ∑ e' : E,
          star (if a' = a₁ ∧ e' = e₀ then K a₁ m r y y₁ else 0) *
            (if a' = a₁ ∧ e' = e₀ then K a₁ m r y y₂ else 0) =
          ∑ m : M, ∑ r : R, ((K a₁ m r)ᴴ * K a₁ m r) y₁ y₂ := by
        apply Finset.sum_congr rfl; intro m _
        rw [Finset.sum_comm]
        have h1 : ∀ a' : A, ∑ y : Y, ∑ r : R, ∑ e' : E,
            star (if a' = a₁ ∧ e' = e₀ then K a₁ m r y y₁ else 0) *
              (if a' = a₁ ∧ e' = e₀ then K a₁ m r y y₂ else 0) =
            if a' = a₁ then ∑ r : R, ((K a₁ m r)ᴴ * K a₁ m r) y₁ y₂ else 0 := by
          intro a'
          by_cases ha' : a' = a₁
          · subst ha'; rw [if_pos rfl]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro r _
            rw [Matrix.mul_apply]
            apply Finset.sum_congr rfl; intro y _
            rw [Finset.sum_eq_single e₀]
            · simp [Matrix.conjTranspose_apply]
            · intro e' _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ e₀) h
          · rw [if_neg ha']
            apply Finset.sum_eq_zero; intro y _
            apply Finset.sum_eq_zero; intro r _
            apply Finset.sum_eq_zero; intro e' _
            simp [ha']
        simp_rw [h1]
        rw [Finset.sum_eq_single a₁]
        · simp
        · intro a' _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ a₁) h
      rw [hsum]
      have hK_sq : ∀ m r, (K a₁ m r)ᴴ * K a₁ m r = (C_qsc a₁).povm (eMR (m, r)) := fun m r ↦ by
        rw [(psdSqrt_isHermitian _).eq, psdSqrt_mul_self]
      simp_rw [hK_sq]
      rw [← Fintype.sum_prod_type (f := fun mr : M × R ↦ (C_qsc a₁).povm (eMR mr) y₁ y₂)]
      rw [Equiv.sum_comp eMR (fun w ↦ (C_qsc a₁).povm w y₁ y₂)]
      have h1 := congr_fun (congr_fun (C_qsc a₁).povm_sum_one y₁) y₂
      simp only [Matrix.sum_apply, Matrix.one_apply] at h1
      simp only [Prod.mk.injEq, and_true]
      convert h1
    · rw [if_neg (fun h ↦ ha (congr_arg Prod.snd h))]
      apply Finset.sum_eq_zero; intro m _
      apply Finset.sum_eq_zero; intro y _
      apply Finset.sum_eq_zero; intro a' _
      apply Finset.sum_eq_zero; intro r _
      apply Finset.sum_eq_zero; intro e' _
      by_cases h1 : a' = a₁ ∧ e' = e₀
      · have h2 : ¬ (a' = a₂ ∧ e' = e₀) := fun h ↦ ha (h1.1.symm.trans h.1)
        rw [if_pos h1, if_neg h2, mul_zero]
      · rw [if_neg h1, star_zero, zero_mul]
  let ν : ℂ := ((Real.sqrt ((2 : ℝ) ^ infoSet.card) : ℝ) : ℂ)⁻¹ *
    ((Real.sqrt ((2 : ℝ) ^ assistSet.card) : ℝ) : ℂ)⁻¹ *
    ((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹
  have hν_sq : star ν * ν = (((2 : ℝ) ^ infoSet.card * (2 : ℝ) ^ assistSet.card * (2 : ℝ) ^ randSet.card : ℝ) : ℂ)⁻¹ := by
    simp only [ν, star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    have h1 : ∀ k : ℕ, (((Real.sqrt ((2 : ℝ) ^ k) : ℝ) : ℂ)⁻¹) * (((Real.sqrt ((2 : ℝ) ^ k) : ℝ) : ℂ)⁻¹) =
        (((2 : ℝ) ^ k : ℝ) : ℂ)⁻¹ := fun k ↦ by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    calc (((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹ *
          (((Real.sqrt ((2 : ℝ) ^ assistSet.card) : ℝ) : ℂ)⁻¹ *
           ((Real.sqrt ((2 : ℝ) ^ infoSet.card) : ℝ) : ℂ)⁻¹)) *
         (((Real.sqrt ((2 : ℝ) ^ infoSet.card) : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt ((2 : ℝ) ^ assistSet.card) : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹)
        = ((((Real.sqrt ((2 : ℝ) ^ infoSet.card) : ℝ) : ℂ)⁻¹) * (((Real.sqrt ((2 : ℝ) ^ infoSet.card) : ℝ) : ℂ)⁻¹)) *
          ((((Real.sqrt ((2 : ℝ) ^ assistSet.card) : ℝ) : ℂ)⁻¹) * (((Real.sqrt ((2 : ℝ) ^ assistSet.card) : ℝ) : ℂ)⁻¹)) *
          ((((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹) * (((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹)) := by ring
      _ = (((2 : ℝ) ^ infoSet.card : ℝ) : ℂ)⁻¹ * (((2 : ℝ) ^ assistSet.card : ℝ) : ℂ)⁻¹ *
          (((2 : ℝ) ^ randSet.card : ℝ) : ℂ)⁻¹ := by rw [h1, h1, h1]
      _ = _ := by push_cast; rw [mul_inv, mul_inv]
  let ψ_ch (v : R) : (M × E) × (Y × A) → ℂ := fun p ↦
    ν * ∑ r : R, phaseSign v r * V_isom (p.2.1, p.1.2)
      (arikanTransform n (wiretapWord infoSet randSet assistSet uF p.1.1 r p.2.2))
  let ψ_Z (v : R) : (M × E) × B_tot → ℂ := fun p ↦
    ∑ ya : Y × A, W_Z p.2 ya * ψ_ch v (p.1, ya)
  let ψ_ideal (v : R) : (M × E) × B_tot → ℂ := fun p ↦
    if p.2.1 = p.1.1 ∧ p.2.2.2.2.2 = e₀ then
      ν * phaseSign v p.2.2.2.2.1 * V_isom (p.2.2.1, p.1.2)
        (arikanTransform n (wiretapWord infoSet randSet assistSet uF p.1.1 p.2.2.2.2.1 p.2.2.2.1))
    else 0
  have hψ_ideal_norm : ∀ v : R, ∑ p : (M × E) × B_tot, ‖ψ_ideal v p‖ ^ 2 = 1 := by
    intro v
    have hC : ((∑ p : (M × E) × B_tot, ‖ψ_ideal v p‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      have h1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := fun z ↦ by
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp_rw [h1]
      simp only [ψ_ideal, B_tot, Anc, Fintype.sum_prod_type]
      have hinner : ∀ m : M, ∀ e : E,
          ∑ m' : M, ∑ y : Y, ∑ a : A, ∑ r : R, ∑ e' : E,
            star (if m' = m ∧ e' = e₀ then ν * phaseSign v r * V_isom (y, e)
              (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a)) else 0) *
            (if m' = m ∧ e' = e₀ then ν * phaseSign v r * V_isom (y, e)
              (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a)) else 0) =
          (star ν * ν) * ∑ a : A, ∑ r : R, ∑ y : Y,
            star (V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))) *
            V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a)) := by
        intro m e
        rw [Finset.sum_eq_single m]
        · simp only [true_and, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro r _
          apply Finset.sum_congr rfl; intro y _
          rw [Finset.sum_eq_single e₀]
          · simp only [↓reduceIte, star_mul', phaseSign_star]
            have hps := phaseSign_mul_self v r
            linear_combination (star ν * ν *
              (star (V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))) *
               V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a)))) * hps
          · intro e' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ e₀) h
        · intro m' _ hne
          apply Finset.sum_eq_zero; intro y _
          apply Finset.sum_eq_zero; intro a _
          apply Finset.sum_eq_zero; intro r _
          apply Finset.sum_eq_zero; intro e' _
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ m) h
      simp_rw [hinner]
      rw [Finset.sum_comm]
      have hV_unit : ∀ (x : Fin (2 ^ n) → Bool),
          ∑ e : E, ∑ y : Y, star (V_isom (y, e) x) * V_isom (y, e) x = 1 :=
        fun x ↦ by simpa using hV_orth x x
      calc ∑ e : E, ∑ m : M, (star ν * ν) * ∑ a : A, ∑ r : R, ∑ y : Y,
              star (V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))) *
              V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))
          = (star ν * ν) * ∑ m : M, ∑ a : A, ∑ r : R, ∑ e : E, ∑ y : Y,
              star (V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))) *
              V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a)) := by
            rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]
            congr 1; apply Finset.sum_congr rfl; intro m _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a _
            rw [Finset.sum_comm]
        _ = (star ν * ν) * ∑ _m : M, ∑ _a : A, ∑ _r : R, (1 : ℂ) := by
            congr 1; apply Finset.sum_congr rfl; intro m _
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro r _
            exact hV_unit _
        _ = 1 := by
            simp only [M, A, R, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
              Fintype.card_coe, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat, hν_sq]
            have hne : ((2 : ℂ) ^ infoSet.card * (2 : ℂ) ^ assistSet.card * (2 : ℂ) ^ randSet.card) ≠ 0 := by
              positivity
            push_cast
            field_simp [hne]
    exact Complex.ofReal_injective (by simpa using hC)
  have hψ_ch_norm : ∀ v : R, ∑ p : (M × E) × (Y × A), ‖ψ_ch v p‖ ^ 2 = 1 := by
    intro v
    have hC : ((∑ p : (M × E) × (Y × A), ‖ψ_ch v p‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      have h1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := fun z ↦ by
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp_rw [h1]
      simp only [Fintype.sum_prod_type]
      have hinner : ∀ (m : M) (e : E) (y : Y) (a : A),
          star (ψ_ch v ((m, e), (y, a))) * ψ_ch v ((m, e), (y, a)) =
            (star ν * ν) * ∑ r₁ : R, ∑ r₂ : R,
              (phaseSign v r₁ * phaseSign v r₂) *
              (star (V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₁ a))) *
               V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₂ a))) := by
        intro m e y a
        simp only [ψ_ch, star_mul, star_sum, phaseSign_star]
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro r₁ _
        apply Finset.sum_congr rfl; intro r₂ _; ring
      simp_rw [hinner, ← Finset.mul_sum]
      have hV := hV_orth
      have hinj_r : ∀ (m : M) (a : A) (r₁ r₂ : R),
          arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₁ a) =
          arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₂ a) → r₁ = r₂ := by
        intro m a r₁ r₂ heq
        have hw := (arikanTransform_bijective n).injective heq
        funext ⟨i, hi⟩
        have hni : i ∉ infoSet := Finset.disjoint_right.mp hdisj_ir hi
        have h := congr_fun hw i
        simpa [wiretapWord, hni, hi] using h
      calc (star ν * ν) * ∑ m : M, ∑ e : E, ∑ y : Y, ∑ a : A, ∑ r₁ : R, ∑ r₂ : R,
            (phaseSign v r₁ * phaseSign v r₂) *
            (star (V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₁ a))) *
             V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₂ a)))
          = (star ν * ν) * ∑ m : M, ∑ a : A, ∑ r₁ : R, ∑ r₂ : R,
              (phaseSign v r₁ * phaseSign v r₂) *
              ∑ e : E, ∑ y : Y,
                star (V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₁ a))) *
                V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₂ a)) := by
            congr 1; apply Finset.sum_congr rfl; intro m _
            have hsw : ∀ (f : E → Y → A → R → R → ℂ),
                (∑ e, ∑ y, ∑ a, ∑ r₁, ∑ r₂, f e y a r₁ r₂) =
                (∑ a, ∑ r₁, ∑ r₂, ∑ e, ∑ y, f e y a r₁ r₂) := by
              intro f
              rw [Finset.sum_comm]
              conv_lhs => arg 2; ext y; rw [Finset.sum_comm]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro a _
              rw [Finset.sum_comm]
              conv_lhs => arg 2; ext e; rw [Finset.sum_comm]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro r₁ _
              rw [Finset.sum_comm]
              conv_lhs => arg 2; ext y; rw [Finset.sum_comm]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro r₂ _
              rw [Finset.sum_comm]
            rw [hsw]
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro r₁ _
            apply Finset.sum_congr rfl; intro r₂ _
            simp_rw [← Finset.mul_sum]
        _ = (star ν * ν) * ∑ m : M, ∑ a : A, ∑ r₁ : R, ∑ r₂ : R,
              (phaseSign v r₁ * phaseSign v r₂) *
              (if arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₁ a) =
                  arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₂ a) then (1 : ℂ) else 0) := by
            congr 1; apply Finset.sum_congr rfl; intro m _
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro r₁ _
            apply Finset.sum_congr rfl; intro r₂ _
            rw [hV]
        _ = (star ν * ν) * ∑ _m : M, ∑ _a : A, ∑ _r₁ : R, (1 : ℂ) := by
            congr 1; apply Finset.sum_congr rfl; intro m _
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro r₁ _
            rw [Finset.sum_eq_single r₁]
            · simp [phaseSign_mul_self]
            · intro r₂ _ hne; rw [if_neg, mul_zero]; intro heq; exact hne (hinj_r m a r₁ r₂ heq).symm
            · intro h; exact absurd (Finset.mem_univ r₁) h
        _ = 1 := by
            simp only [M, A, R, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
              Fintype.card_coe, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat, hν_sq]
            have hne : ((2 : ℂ) ^ infoSet.card * (2 : ℂ) ^ assistSet.card * (2 : ℂ) ^ randSet.card) ≠ 0 := by
              positivity
            push_cast
            field_simp [hne]
    exact Complex.ofReal_injective (by simpa using hC)
  have hψ_Z_norm : ∀ v : R, ∑ p : (M × E) × B_tot, ‖ψ_Z v p‖ ^ 2 = 1 := by
    intro v
    have hC : ((∑ p : (M × E) × B_tot, ‖ψ_Z v p‖ ^ 2 : ℝ) : ℂ) =
        ((∑ p : (M × E) × (Y × A), ‖ψ_ch v p‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sum]
      have h1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := fun z ↦ by
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp_rw [h1]
      conv_lhs => rw [Fintype.sum_prod_type]
      conv_rhs => rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro me _
      have hinner : ∀ b : B_tot,
          star (ψ_Z v (me, b)) * ψ_Z v (me, b) =
            ∑ ya₁ : Y × A, ∑ ya₂ : Y × A,
              (star (W_Z b ya₁) * W_Z b ya₂) * (star (ψ_ch v (me, ya₁)) * ψ_ch v (me, ya₂)) := by
        intro b
        simp only [ψ_Z, star_sum, star_mul]
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro ya₁ _
        apply Finset.sum_congr rfl; intro ya₂ _; ring
      simp_rw [hinner]
      rw [Finset.sum_comm]
      have hsw : ∑ ya₁ : Y × A, ∑ b : B_tot, ∑ ya₂ : Y × A,
            (star (W_Z b ya₁) * W_Z b ya₂) * (star (ψ_ch v (me, ya₁)) * ψ_ch v (me, ya₂)) =
          ∑ ya₁ : Y × A, ∑ ya₂ : Y × A,
            (W_Zᴴ * W_Z) ya₁ ya₂ * (star (ψ_ch v (me, ya₁)) * ψ_ch v (me, ya₂)) := by
        apply Finset.sum_congr rfl; intro ya₁ _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro ya₂ _
        rw [Matrix.mul_apply, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro b _; simp [Matrix.conjTranspose_apply]
      rw [hsw, hWZ_isom]
      apply Finset.sum_congr rfl; intro ya₁ _
      rw [Finset.sum_eq_single ya₁]
      · simp
      · intro ya₂ _ hne; simp [Matrix.one_apply, Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ ya₁) h
    rw [← hψ_ch_norm v]; exact Complex.ofReal_injective hC
  have hov_exists : ∃ v : R,
      1 - wiretapBobError 𝒩 n infoSet randSet assistSet uF ≤
        (∑ p : (M × E) × B_tot, star (ψ_ideal v p) * ψ_Z v p).re := by
    have hov_sum : ∑ v : R, ∑ p : (M × E) × B_tot, star (ψ_ideal v p) * ψ_Z v p =
        ((2 : ℝ) ^ randSet.card : ℂ) * (star ν * ν) *
          ∑ a : A, ∑ m : M, ∑ r : R,
            (K a m r * (productState (ampChannel 𝒩) n
              (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))).mat).trace := by
      have hterm : ∀ v : R, ∀ m : M, ∀ e : E,
          ∑ m' : M, ∑ y : Y, ∑ a' : A, ∑ r' : R, ∑ e' : E,
            star (if m' = m ∧ e' = e₀ then ν * phaseSign v r' * V_isom (y, e)
              (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r' a')) else 0) *
            (∑ y₁ : Y, ∑ a₁ : A,
              (if a' = a₁ ∧ e' = e₀ then K a₁ m' r' y y₁ else 0) *
              (ν * ∑ r₂ : R, phaseSign v r₂ * V_isom (y₁, e)
                (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₂ a₁)))) =
          (star ν * ν) * ∑ a : A, ∑ r' : R, ∑ r₂ : R,
            (phaseSign v r' * phaseSign v r₂) *
            ∑ y : Y, ∑ y₁ : Y,
              K a m r' y y₁ *
              V_isom (y₁, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₂ a)) *
              star (V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r' a))) := by
        intro v m e
        rw [Finset.sum_eq_single m]
        · simp only [true_and, Finset.mul_sum]
          have h1 : ∀ y : Y, ∀ a' : A, ∀ r' : R,
              ∑ e' : E,
                star (if e' = e₀ then ν * phaseSign v r' * V_isom (y, e)
                  (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r' a')) else 0) *
                (∑ y₁ : Y, ∑ a₁ : A,
                  (if a' = a₁ ∧ e' = e₀ then K a₁ m r' y y₁ else 0) *
                  (ν * ∑ r₂ : R, phaseSign v r₂ * V_isom (y₁, e)
                    (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₂ a₁)))) =
              (star ν * ν) * ∑ r₂ : R, (phaseSign v r' * phaseSign v r₂) * ∑ y₁ : Y,
                K a' m r' y y₁ *
                V_isom (y₁, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₂ a')) *
                star (V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r' a'))) := by
            intro y a' r'
            rw [Finset.sum_eq_single e₀]
            · simp only [↓reduceIte, and_true, star_mul', phaseSign_star]
              have ha' : ∀ y₁ : Y, ∑ a₁ : A,
                  (if a' = a₁ then K a₁ m r' y y₁ else 0) *
                  (ν * ∑ r₂ : R, phaseSign v r₂ * V_isom (y₁, e)
                    (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₂ a₁))) =
                  K a' m r' y y₁ * (ν * ∑ r₂ : R, phaseSign v r₂ * V_isom (y₁, e)
                    (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₂ a'))) := fun y₁ ↦ by
                rw [Finset.sum_eq_single a']
                · simp
                · intro a₁ _ hne; simp [Ne.symm hne]
                · intro h; exact absurd (Finset.mem_univ a') h
              simp_rw [ha', Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro r₂ _
              apply Finset.sum_congr rfl; intro y₁ _; ring
            · intro e' _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ e₀) h
          simp_rw [h1]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro r' _
          simp_rw [← Finset.mul_sum]
          rw [Finset.mul_sum, Finset.sum_comm]
          apply Finset.sum_congr rfl; intro r₂ _
          simp_rw [← Finset.mul_sum]
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro y _
          rw [Finset.mul_sum, Finset.mul_sum]
        · intro m' _ hne
          apply Finset.sum_eq_zero; intro y _
          apply Finset.sum_eq_zero; intro a' _
          apply Finset.sum_eq_zero; intro r' _
          apply Finset.sum_eq_zero; intro e' _
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ m) h
      have hsingle : ∀ v : R, ∑ p : (M × E) × B_tot, star (ψ_ideal v p) * ψ_Z v p =
          (star ν * ν) * ∑ m : M, ∑ e : E, ∑ a : A, ∑ r' : R, ∑ r₂ : R,
            (phaseSign v r' * phaseSign v r₂) *
            ∑ y : Y, ∑ y₁ : Y,
              K a m r' y y₁ *
              V_isom (y₁, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₂ a)) *
              star (V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r' a))) := by
        intro v
        simp only [ψ_ideal, ψ_Z, ψ_ch, W_Z, B_tot, Anc, Fintype.sum_prod_type]
        simp_rw [hterm v, ← Finset.mul_sum]
      simp_rw [hsingle, ← Finset.mul_sum]
      let g : M → E → A → R → R → ℂ := fun m e a r' r₂ ↦
        ∑ y : Y, ∑ y₁ : Y,
          K a m r' y y₁ *
          V_isom (y₁, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r₂ a)) *
          star (V_isom (y, e) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r' a)))
      have hswap : ∑ v : R, ∑ m : M, ∑ e : E, ∑ a : A, ∑ r' : R, ∑ r₂ : R,
            (phaseSign v r' * phaseSign v r₂) * g m e a r' r₂ =
          ∑ m : M, ∑ e : E, ∑ a : A, ∑ r' : R, ∑ r₂ : R,
            (∑ v : R, phaseSign v r' * phaseSign v r₂) * g m e a r' r₂ := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro m _
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro e _
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro r' _
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro r₂ _
        rw [Finset.sum_mul]
      change (star ν * ν) * (∑ v : R, ∑ m : M, ∑ e : E, ∑ a : A, ∑ r' : R, ∑ r₂ : R,
        (phaseSign v r' * phaseSign v r₂) * g m e a r' r₂) = _
      rw [hswap]
      have hkill : ∀ m e a r', ∑ r₂ : R, (∑ v : R, phaseSign v r' * phaseSign v r₂) * g m e a r' r₂ =
          ((2 : ℝ) ^ randSet.card : ℂ) * g m e a r' r' := by
        intro m e a r'
        simp_rw [sum_phaseSign_mul]
        rw [Finset.sum_eq_single r']
        · simp
        · intro r₂ _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ r') h
      simp_rw [hkill, ← Finset.mul_sum]
      rw [← mul_assoc, mul_comm (star ν * ν) ((2 : ℝ) ^ randSet.card : ℂ), mul_assoc]
      congr 1
      calc ∑ m : M, ∑ e : E, ∑ a : A, ∑ r : R, g m e a r r
          = ∑ a : A, ∑ m : M, ∑ r : R, ∑ e : E, g m e a r r := by
            rw [Finset.sum_comm]
            conv_lhs => arg 2; ext e; rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro m _
            rw [Finset.sum_comm]
        _ = ∑ a : A, ∑ m : M, ∑ r : R,
              (K a m r * (productState (ampChannel 𝒩) n
                (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))).mat).trace := by
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro m _
            apply Finset.sum_congr rfl; intro r _
            simp only [g, hV_def, Matrix.trace, Matrix.diag, Matrix.mul_apply,
              productState_amp_eq_tensorPow_partialTrace, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y₁ _
            apply Finset.sum_congr rfl; intro e _; ring
    have hK_ge : ∀ (a : A) (m : M) (r : R),
        (((C_qsc a).povm (eMR (m, r)) * (productState (ampChannel 𝒩) n
            (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))).mat).trace).re ≤
        ((K a m r * (productState (ampChannel 𝒩) n
            (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))).mat).trace).re := by
      intro a m r
      let w₀ : {i : Fin (2 ^ n) // i ∈ (C_qsc a).infoSet} → Bool := eMR (m, r)
      let Λ := (C_qsc a).povm w₀
      have hle1 : (1 - Λ).PosSemidef := by
        have h1 : 1 - Λ = ∑ w ∈ Finset.univ.erase w₀, (C_qsc a).povm w := by
          have hsum := (C_qsc a).povm_sum_one
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀)] at hsum
          exact eq_sub_of_add_eq' hsum
        rw [h1]
        have hsum_psd : ∀ s : Finset ({i : Fin (2 ^ n) // i ∈ (C_qsc a).infoSet} → Bool),
            (∑ w ∈ s, (C_qsc a).povm w).PosSemidef := by
          intro s
          induction s using Finset.cons_induction with
          | empty => simp [Matrix.PosSemidef.zero]
          | cons w s hw ih =>
            rw [Finset.sum_cons]
            exact ((C_qsc a).povm_posSemidef w).add ih
        exact hsum_psd _
      have hdiff_psd : (K a m r - Λ).PosSemidef :=
        psdSqrt_ge_self_of_le_one ((C_qsc a).povm_posSemidef (eMR (m, r))) hle1
      have hnn := trace_mul_psd_re_nonneg hdiff_psd
        (productState (ampChannel 𝒩) n (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a)))
      rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at hnn
      linarith
    have hsum_ge : ((2 : ℝ) ^ randSet.card) * (1 - wiretapBobError 𝒩 n infoSet randSet assistSet uF) ≤
        ∑ v : R, (∑ p : (M × E) × B_tot, star (ψ_ideal v p) * ψ_Z v p).re := by
      have hre := congr_arg Complex.re hov_sum
      rw [Complex.re_sum] at hre
      rw [hre]
      have hpref : (((2 : ℝ) ^ randSet.card : ℂ) * (star ν * ν)) =
          ((((2 : ℝ) ^ infoSet.card * (2 : ℝ) ^ assistSet.card : ℝ)⁻¹ : ℝ) : ℂ) := by
        rw [hν_sq]
        have hpos : ((2 : ℂ) ^ randSet.card) ≠ 0 := by positivity
        have hpos2 : ((2 : ℂ) ^ infoSet.card * (2 : ℂ) ^ assistSet.card) ≠ 0 := by positivity
        push_cast
        field_simp [hpos, hpos2]
      rw [hpref, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.re_sum]
      have htr_ge : ∑ a : A, ∑ m : M, ∑ r : R,
            (((C_qsc a).povm (eMR (m, r)) * (productState (ampChannel 𝒩) n
              (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))).mat).trace).re ≤
          ∑ a : A, (∑ m : M, ∑ r : R,
            (K a m r * (productState (ampChannel 𝒩) n
              (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))).mat).trace).re := by
        apply Finset.sum_le_sum; intro a _
        rw [Complex.re_sum]
        apply Finset.sum_le_sum; intro m _
        rw [Complex.re_sum]
        apply Finset.sum_le_sum; intro r _
        exact hK_ge a m r
      have hcard_union : (infoSet ∪ randSet).card = infoSet.card + randSet.card :=
        Finset.card_union_of_disjoint hdisj_ir
      have hbob_id : ((2 : ℝ) ^ randSet.card) * (1 - wiretapBobError 𝒩 n infoSet randSet assistSet uF) =
          ((2 : ℝ) ^ infoSet.card * (2 : ℝ) ^ assistSet.card)⁻¹ *
            ∑ a : A, ∑ m : M, ∑ r : R,
              (((C_qsc a).povm (eMR (m, r)) * (productState (ampChannel 𝒩) n
                (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))).mat).trace).re := by
        unfold wiretapBobError
        have havg_a : ∀ a : A,
            1 - (C_qsc a).avgBlockError =
              ((2 : ℝ) ^ infoSet.card * (2 : ℝ) ^ randSet.card)⁻¹ *
                ∑ m : M, ∑ r : R,
                  (((C_qsc a).povm (eMR (m, r)) * (productState (ampChannel 𝒩) n
                    (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))).mat).trace).re := by
          intro a
          unfold CosetPolarCode.avgBlockError
          change 1 - ((2 : ℝ) ^ (infoSet ∪ randSet).card)⁻¹ *
            ∑ w : {i : Fin (2 ^ n) // i ∈ infoSet ∪ randSet} → Bool,
              (1 - (((C_qsc a).povm w * (productState (ampChannel 𝒩) n
                (arikanTransform n (embedMsg (infoSet ∪ randSet) (bobEffectiveFrozen assistSet uF a) w))).mat).trace).re) = _
          have hcard : ((2 : ℝ) ^ (infoSet ∪ randSet).card) = (2 : ℝ) ^ infoSet.card * (2 : ℝ) ^ randSet.card := by
            rw [hcard_union, pow_add]
          have hsum_one : ∑ _w : {i : Fin (2 ^ n) // i ∈ infoSet ∪ randSet} → Bool, (1 : ℝ) =
              (2 : ℝ) ^ (infoSet ∪ randSet).card := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
              Fintype.card_coe, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
          have hrew : ∑ w : {i : Fin (2 ^ n) // i ∈ infoSet ∪ randSet} → Bool,
              (1 - (((C_qsc a).povm w * (productState (ampChannel 𝒩) n
                (arikanTransform n (embedMsg (infoSet ∪ randSet) (bobEffectiveFrozen assistSet uF a) w))).mat).trace).re) =
              (2 : ℝ) ^ (infoSet ∪ randSet).card -
              ∑ m : M, ∑ r : R,
                (((C_qsc a).povm (eMR (m, r)) * (productState (ampChannel 𝒩) n
                  (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a))).mat).trace).re := by
            rw [Finset.sum_sub_distrib, hsum_one]
            congr 1
            rw [← Equiv.sum_comp eMR, Fintype.sum_prod_type]
            apply Finset.sum_congr rfl; intro m _
            apply Finset.sum_congr rfl; intro r _
            rw [hemb_eq]
          rw [hrew, mul_sub, inv_mul_cancel₀ (by positivity), hcard]
          ring
        have hsum_A : ∑ _a : A, (1 : ℝ) = (2 : ℝ) ^ assistSet.card := by
          simp [A, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
        have h1sub : 1 - ((2 : ℝ) ^ assistSet.card)⁻¹ * ∑ a : A, (C_qsc a).avgBlockError =
            ((2 : ℝ) ^ assistSet.card)⁻¹ * ∑ a : A, (1 - (C_qsc a).avgBlockError) := by
          rw [Finset.sum_sub_distrib, hsum_A, mul_sub, inv_mul_cancel₀ (by positivity)]
        rw [h1sub]
        simp_rw [havg_a, ← Finset.mul_sum]
        have hposR : (2 : ℝ) ^ randSet.card ≠ 0 := by positivity
        have hposM : (2 : ℝ) ^ infoSet.card ≠ 0 := by positivity
        have hposA : (2 : ℝ) ^ assistSet.card ≠ 0 := by positivity
        field_simp [hposR, hposM, hposA]
      rw [hbob_id]
      exact mul_le_mul_of_nonneg_left htr_ge (by positivity)
    by_contra hall; push Not at hall
    have hlt : ∑ v : R, (∑ p : (M × E) × B_tot, star (ψ_ideal v p) * ψ_Z v p).re <
        ∑ _v : R, (1 - wiretapBobError 𝒩 n infoSet randSet assistSet uF) := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro v _; exact hall v
    simp only [R, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hlt
    linarith
  obtain ⟨v, hv_ov⟩ := hov_exists
  have hbob_nn : 0 ≤ wiretapBobError 𝒩 n infoSet randSet assistSet uF := by
    unfold wiretapBobError
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg; intro a _
    unfold CosetPolarCode.avgBlockError
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg; intro m _
    have hle : (((C_qsc a).povm m * (productState (ampChannel 𝒩) n ((C_qsc a).encode m)).mat).trace).re ≤ 1 := by
      have hsum1 : ∑ m', (((C_qsc a).povm m' * (productState (ampChannel 𝒩) n ((C_qsc a).encode m)).mat).trace).re = 1 := by
        rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, (C_qsc a).povm_sum_one, Matrix.one_mul,
          (productState (ampChannel 𝒩) n ((C_qsc a).encode m)).trace_one, Complex.one_re]
      have hnn : ∀ m', 0 ≤ (((C_qsc a).povm m' * (productState (ampChannel 𝒩) n ((C_qsc a).encode m)).mat).trace).re := by
        intro m'
        have hsq : (productState (ampChannel 𝒩) n ((C_qsc a).encode m)).mat =
            (productState (ampChannel 𝒩) n ((C_qsc a).encode m)).sqrtMat *
              (productState (ampChannel 𝒩) n ((C_qsc a).encode m)).sqrtMat :=
          (productState (ampChannel 𝒩) n ((C_qsc a).encode m)).sqrtMat_mul_self.symm
        have htr : ((C_qsc a).povm m' * (productState (ampChannel 𝒩) n ((C_qsc a).encode m)).mat).trace =
            ((productState (ampChannel 𝒩) n ((C_qsc a).encode m)).sqrtMat * (C_qsc a).povm m' *
              ((productState (ampChannel 𝒩) n ((C_qsc a).encode m)).sqrtMat)ᴴ).trace := by
          rw [hsq, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
            (productState (ampChannel 𝒩) n ((C_qsc a).encode m)).sqrtMat_isHermitian.eq]
        rw [htr]
        have hHerm : ((productState (ampChannel 𝒩) n ((C_qsc a).encode m)).sqrtMat * (C_qsc a).povm m' *
            ((productState (ampChannel 𝒩) n ((C_qsc a).encode m)).sqrtMat)ᴴ).PosSemidef :=
          ((C_qsc a).povm_posSemidef m').mul_mul_conjTranspose_same
            (productState (ampChannel 𝒩) n ((C_qsc a).encode m)).sqrtMat
        rw [hHerm.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
        exact Finset.sum_nonneg fun idx _ ↦ by simpa using hHerm.eigenvalues_nonneg idx
      have hm_le := Finset.single_le_sum (fun m' _ ↦ hnn m') (Finset.mem_univ m)
      linarith
    linarith
  let ρ_E : DensityOp E := fixedSubsetAvgState (ampChannel 𝒩.complementary) n ∅ (fun _ ↦ false)
  let ψ_target : (M × E) × B_tot → ℂ := fun p ↦
    if p.2.2.1 = y₀ ∧ p.2.2.2.1 = a₀ ∧ p.2.2.2.2.1 = r₀ then
      maxEntangledVec M (p.1.1, p.2.1) * ρ_E.sqrtMat p.1.2 p.2.2.2.2.2
    else 0
  have hψ_target_norm : ∑ p : (M × E) × B_tot, ‖ψ_target p‖ ^ 2 = 1 := by
    have hC : ((∑ p : (M × E) × B_tot, ‖ψ_target p‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      have h1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := fun z ↦ by
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp_rw [h1]
      simp only [ψ_target, B_tot, Anc, Fintype.sum_prod_type]
      have hinner : ∀ m : M, ∀ e : E, ∀ m' : M,
          ∑ y : Y, ∑ a : A, ∑ r : R, ∑ e' : E,
            star (if y = y₀ ∧ a = a₀ ∧ r = r₀ then maxEntangledVec M (m, m') * ρ_E.sqrtMat e e' else 0) *
            (if y = y₀ ∧ a = a₀ ∧ r = r₀ then maxEntangledVec M (m, m') * ρ_E.sqrtMat e e' else 0) =
          (star (maxEntangledVec M (m, m')) * maxEntangledVec M (m, m')) * ρ_E.mat e e := by
        intro m e m'
        rw [Finset.sum_eq_single y₀]
        · rw [Finset.sum_eq_single a₀]
          · rw [Finset.sum_eq_single r₀]
            · simp only [true_and, ↓reduceIte, star_mul']
              have hsq := congr_fun (congr_fun ρ_E.sqrtMat_mul_self e) e
              rw [Matrix.mul_apply] at hsq
              rw [← hsq, Finset.mul_sum]
              apply Finset.sum_congr rfl; intro e' _
              have hh := congr_fun (congr_fun ρ_E.sqrtMat_isHermitian.eq e') e
              simp only [Matrix.conjTranspose_apply] at hh
              rw [← hh]; ring
            · intro r _ hne; apply Finset.sum_eq_zero; intro e' _; simp [hne]
            · intro h; exact absurd (Finset.mem_univ r₀) h
          · intro a _ hne; apply Finset.sum_eq_zero; intro r _; apply Finset.sum_eq_zero; intro e' _; simp [hne]
          · intro h; exact absurd (Finset.mem_univ a₀) h
        · intro y _ hne; apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro r _
          apply Finset.sum_eq_zero; intro e' _; simp [hne]
        · intro h; exact absurd (Finset.mem_univ y₀) h
      simp_rw [hinner]
      have htrE : ∑ e : E, ρ_E.mat e e = 1 := ρ_E.trace_one
      have hM : ∑ m : M, ∑ m' : M, star (maxEntangledVec M (m, m')) * maxEntangledVec M (m, m') = 1 := by
        have h := congr_arg Complex.ofReal (maxEntangledVec_norm M)
        simp only [Complex.ofReal_sum, Complex.ofReal_one, Fintype.sum_prod_type] at h
        rw [← h]
        apply Finset.sum_congr rfl; intro m _
        apply Finset.sum_congr rfl; intro m' _
        exact (h1 _).symm
      calc ∑ m : M, ∑ e : E, ∑ m' : M,
            (star (maxEntangledVec M (m, m')) * maxEntangledVec M (m, m')) * ρ_E.mat e e
          = (∑ m : M, ∑ m' : M, star (maxEntangledVec M (m, m')) * maxEntangledVec M (m, m')) *
            (∑ e : E, ρ_E.mat e e) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro m _
            rw [Finset.sum_comm, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro m' _
            rw [Finset.mul_sum]
        _ = 1 := by rw [hM, htrE, mul_one]
    exact Complex.ofReal_injective (by simpa using hC)
  have hpt_ideal : partialTrace₂Mat (M × E) B_tot (pureState (ψ_ideal v) (hψ_ideal_norm v)).mat =
      (wiretapEveJointState 𝒩 n infoSet randSet assistSet uF).mat := by
    ext ⟨m₁, e₁⟩ ⟨m₂, e₂⟩
    simp only [partialTrace₂Mat, pureState, ψ_ideal, Matrix.of_apply, B_tot, Anc, Fintype.sum_prod_type]
    by_cases hm : m₁ = m₂
    · subst hm
      have hL : ∑ m' : M, ∑ y : Y, ∑ a : A, ∑ r : R, ∑ e' : E,
          (if m' = m₁ ∧ e' = e₀ then ν * phaseSign v r * V_isom (y, e₁)
            (arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r a)) else 0) *
          star (if m' = m₁ ∧ e' = e₀ then ν * phaseSign v r * V_isom (y, e₂)
            (arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r a)) else 0) =
          (star ν * ν) * ∑ r : R, ∑ a : A,
            (productState (ampChannel 𝒩.complementary) n
              (arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r a))).mat e₁ e₂ := by
        rw [Finset.sum_eq_single m₁]
        · simp only [true_and]
          have he' : ∀ y a r,
              ∑ e' : E,
                (if e' = e₀ then ν * phaseSign v r * V_isom (y, e₁)
                  (arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r a)) else 0) *
                star (if e' = e₀ then ν * phaseSign v r * V_isom (y, e₂)
                  (arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r a)) else 0) =
              (star ν * ν) *
                (V_isom (y, e₁) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r a)) *
                 star (V_isom (y, e₂) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r a)))) := by
            intro y a r
            rw [Finset.sum_eq_single e₀]
            · simp only [↓reduceIte, star_mul', phaseSign_star]
              have hps := phaseSign_mul_self v r
              linear_combination (star ν * ν *
                (V_isom (y, e₁) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r a)) *
                 star (V_isom (y, e₂) (arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r a))))) * hps
            · intro e' _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ e₀) h
          simp_rw [he', ← Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro r _
          apply Finset.sum_congr rfl; intro a _
          simpa only [hV_def] using (productState_comp_eq_tensorPow_partialTrace 𝒩 n _ e₁ e₂).symm
        · intro m' _ hne
          apply Finset.sum_eq_zero; intro y _
          apply Finset.sum_eq_zero; intro a _
          apply Finset.sum_eq_zero; intro r _
          apply Finset.sum_eq_zero; intro e' _
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ m₁) h
      rw [hL]
      simp only [wiretapEveJointState, uniformBlockDiag, wiretapEveCondState, Matrix.of_apply,
        ↓reduceIte, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Nat.cast_pow, Nat.cast_ofNat,
        hν_sq]
      push_cast
      rw [mul_inv, mul_inv, mul_assoc]
      ring
    · have hL : ∑ m' : M, ∑ y : Y, ∑ a : A, ∑ r : R, ∑ e' : E,
          (if m' = m₁ ∧ e' = e₀ then ν * phaseSign v r * V_isom (y, e₁)
            (arikanTransform n (wiretapWord infoSet randSet assistSet uF m₁ r a)) else 0) *
          star (if m' = m₂ ∧ e' = e₀ then ν * phaseSign v r * V_isom (y, e₂)
            (arikanTransform n (wiretapWord infoSet randSet assistSet uF m₂ r a)) else 0) = 0 := by
        apply Finset.sum_eq_zero; intro m' _
        apply Finset.sum_eq_zero; intro y _
        apply Finset.sum_eq_zero; intro a _
        apply Finset.sum_eq_zero; intro r _
        apply Finset.sum_eq_zero; intro e' _
        by_cases h1 : m' = m₁ ∧ e' = e₀
        · have h2 : ¬ (m' = m₂ ∧ e' = e₀) := fun h ↦ hm (h1.1.symm.trans h.1)
          rw [if_pos h1, if_neg h2, star_zero, mul_zero]
        · rw [if_neg h1, zero_mul]
      rw [hL]
      simp [wiretapEveJointState, uniformBlockDiag, hm]
  have hpt_target : partialTrace₂Mat (M × E) B_tot (pureState ψ_target hψ_target_norm).mat =
      (wiretapIdealEveState 𝒩 n infoSet).mat := by
    ext ⟨m₁, e₁⟩ ⟨m₂, e₂⟩
    simp only [partialTrace₂Mat, pureState, ψ_target, Matrix.of_apply, B_tot, Anc, Fintype.sum_prod_type]
    have hL : ∑ m' : M, ∑ y : Y, ∑ a : A, ∑ r : R, ∑ e' : E,
        (if y = y₀ ∧ a = a₀ ∧ r = r₀ then maxEntangledVec M (m₁, m') * ρ_E.sqrtMat e₁ e' else 0) *
        star (if y = y₀ ∧ a = a₀ ∧ r = r₀ then maxEntangledVec M (m₂, m') * ρ_E.sqrtMat e₂ e' else 0) =
        (∑ m' : M, maxEntangledVec M (m₁, m') * star (maxEntangledVec M (m₂, m'))) * ρ_E.mat e₁ e₂ := by
      have h1 : ∀ m' : M,
          ∑ y : Y, ∑ a : A, ∑ r : R, ∑ e' : E,
            (if y = y₀ ∧ a = a₀ ∧ r = r₀ then maxEntangledVec M (m₁, m') * ρ_E.sqrtMat e₁ e' else 0) *
            star (if y = y₀ ∧ a = a₀ ∧ r = r₀ then maxEntangledVec M (m₂, m') * ρ_E.sqrtMat e₂ e' else 0) =
          (maxEntangledVec M (m₁, m') * star (maxEntangledVec M (m₂, m'))) * ρ_E.mat e₁ e₂ := by
        intro m'
        rw [Finset.sum_eq_single y₀]
        · rw [Finset.sum_eq_single a₀]
          · rw [Finset.sum_eq_single r₀]
            · simp only [true_and, ↓reduceIte, star_mul']
              have hsq := congr_fun (congr_fun ρ_E.sqrtMat_mul_self e₁) e₂
              rw [Matrix.mul_apply] at hsq
              rw [← hsq, Finset.mul_sum]
              apply Finset.sum_congr rfl; intro e' _
              have hh := congr_fun (congr_fun ρ_E.sqrtMat_isHermitian.eq e') e₂
              simp only [Matrix.conjTranspose_apply] at hh
              rw [← hh]; ring
            · intro r _ hne; apply Finset.sum_eq_zero; intro e' _; simp [hne]
            · intro h; exact absurd (Finset.mem_univ r₀) h
          · intro a _ hne; apply Finset.sum_eq_zero; intro r _; apply Finset.sum_eq_zero; intro e' _; simp [hne]
          · intro h; exact absurd (Finset.mem_univ a₀) h
        · intro y _ hne; apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro r _
          apply Finset.sum_eq_zero; intro e' _; simp [hne]
        · intro h; exact absurd (Finset.mem_univ y₀) h
      simp_rw [h1, ← Finset.sum_mul]
    rw [hL]
    have hM_sum : ∑ m' : M, maxEntangledVec M (m₁, m') * star (maxEntangledVec M (m₂, m')) =
        if m₁ = m₂ then ((Fintype.card M : ℝ) : ℂ)⁻¹ else 0 := by
      simp only [maxEntangledVec]
      by_cases hm : m₁ = m₂
      · subst hm; rw [if_pos rfl]
        rw [Finset.sum_eq_single m₁]
        · simp only [↓reduceIte, star_inv₀, Complex.star_def, Complex.conj_ofReal]
          rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
        · intro m' _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ m₁) h
      · rw [if_neg hm]
        apply Finset.sum_eq_zero; intro m' _
        by_cases h1 : m₁ = m'
        · subst h1; simp [Ne.symm hm]
        · simp [h1]
    rw [hM_sum]
    simp only [wiretapIdealEveState, uniformBlockDiag, ρ_E, Matrix.of_apply]
    split_ifs <;> simp
  obtain ⟨U_dec, hU_l, hU_r, hU_fid⟩ :=
    exists_uhlmann_unitary (wiretapEveJointState 𝒩 n infoSet randSet assistSet uF)
      (wiretapIdealEveState 𝒩 n infoSet)
      (ψ_ideal v) ψ_target (hψ_ideal_norm v) hψ_target_norm hpt_ideal hpt_target
  let ψ_Z_dec : (M × E) × B_tot → ℂ := fun p ↦ ∑ b : B_tot, U_dec p.2 b * ψ_Z v (p.1, b)
  let ψ_ideal_dec : (M × E) × B_tot → ℂ := fun p ↦ ∑ b : B_tot, U_dec p.2 b * ψ_ideal v (p.1, b)
  have hunitary_inner : ∀ (u w : (M × E) × B_tot → ℂ),
      ∑ p : (M × E) × B_tot,
        star (∑ b : B_tot, U_dec p.2 b * u (p.1, b)) * (∑ b : B_tot, U_dec p.2 b * w (p.1, b)) =
      ∑ p : (M × E) × B_tot, star (u p) * w p := by
    intro u w
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro m _
    apply Finset.sum_congr rfl; intro e _
    simp only [star_sum, star_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    calc ∑ b : B_tot, ∑ b₁ : B_tot, ∑ b₂ : B_tot,
          star (u ((m, e), b₁)) * star (U_dec b b₁) * (U_dec b b₂ * w ((m, e), b₂))
        = ∑ b₁ : B_tot, ∑ b₂ : B_tot,
            (U_decᴴ * U_dec) b₁ b₂ * (star (u ((m, e), b₁)) * w ((m, e), b₂)) := by
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
          rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b₁ _
          rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b₂ _
          apply Finset.sum_congr rfl; intro b _; ring
      _ = ∑ b₁ : B_tot, star (u ((m, e), b₁)) * w ((m, e), b₁) := by
          rw [hU_l]
          apply Finset.sum_congr rfl; intro b₁ _
          rw [Finset.sum_eq_single b₁]
          · simp
          · intro b₂ _ hne; simp [Matrix.one_apply, Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ b₁) h
  have hψ_Z_dec_norm : ∑ p : (M × E) × B_tot, ‖ψ_Z_dec p‖ ^ 2 = 1 := by
    have hC : ((∑ p : (M × E) × B_tot, ‖ψ_Z_dec p‖ ^ 2 : ℝ) : ℂ) =
        ((∑ p : (M × E) × B_tot, ‖ψ_Z v p‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sum]
      have h1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := fun z ↦ by
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp_rw [h1]
      exact hunitary_inner (ψ_Z v) (ψ_Z v)
    rw [← hψ_Z_norm v]; exact Complex.ofReal_injective hC
  have hψ_ideal_dec_norm : ∑ p : (M × E) × B_tot, ‖ψ_ideal_dec p‖ ^ 2 = 1 := by
    have hC : ((∑ p : (M × E) × B_tot, ‖ψ_ideal_dec p‖ ^ 2 : ℝ) : ℂ) =
        ((∑ p : (M × E) × B_tot, ‖ψ_ideal v p‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sum]
      have h1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := fun z ↦ by
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp_rw [h1]
      exact hunitary_inner (ψ_ideal v) (ψ_ideal v)
    rw [← hψ_ideal_norm v]; exact Complex.ofReal_injective hC
  have htd_dec1 : traceDist (pureState ψ_Z_dec hψ_Z_dec_norm)
      (pureState ψ_ideal_dec hψ_ideal_dec_norm) ≤
      Real.sqrt (2 * wiretapBobError 𝒩 n infoSet randSet assistSet uF) := by
    rw [traceDist_symm, traceDist_pureState_eq ψ_ideal_dec ψ_Z_dec hψ_ideal_dec_norm hψ_Z_dec_norm,
      hunitary_inner (ψ_ideal v) (ψ_Z v)]
    exact sqrt_one_sub_norm_sq_le_sqrt_two_mul hbob_nn hv_ov
  have htd_dec2 : traceDist (pureState ψ_ideal_dec hψ_ideal_dec_norm)
      (pureState ψ_target hψ_target_norm) ≤
      Real.sqrt (2 * wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF) := by
    rw [traceDist_symm, traceDist_pureState_eq ψ_target ψ_ideal_dec hψ_target_norm hψ_ideal_dec_norm]
    have hfvg := one_sub_rootFidelity_le_traceDist
      (wiretapEveJointState 𝒩 n infoSet randSet assistSet uF)
      (wiretapIdealEveState 𝒩 n infoSet)
    have hsec_nn : 0 ≤ wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF :=
      traceDist_nonneg _ _
    have hnorm_ge : 1 - wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF ≤
        ‖∑ p : (M × E) × B_tot, star (ψ_target p) * ψ_ideal_dec p‖ := by
      have heq : ∑ p : (M × E) × B_tot, star (ψ_target p) * ψ_ideal_dec p =
          ∑ p : (M × E) × B_tot, star (ψ_target p) * ∑ b : B_tot, U_dec p.2 b * ψ_ideal v (p.1, b) := rfl
      rw [heq, ← hU_fid]
      unfold wiretapSecrecyError; linarith
    apply Real.sqrt_le_sqrt
    by_cases h1 : 1 ≤ wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF
    · nlinarith [norm_nonneg (∑ p : (M × E) × B_tot, star (ψ_target p) * ψ_ideal_dec p)]
    · push Not at h1
      nlinarith [sq_nonneg (wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF)]
  have htd_tot : traceDist (pureState ψ_Z_dec hψ_Z_dec_norm)
      (pureState ψ_target hψ_target_norm) ≤
      Real.sqrt (2 * wiretapBobError 𝒩 n infoSet randSet assistSet uF) +
        Real.sqrt (2 * wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF) :=
    le_trans (traceDist_triangle _ _ _) (add_le_add htd_dec1 htd_dec2)
  let 𝒟 : CPTPMap.{0} (Y × A) M :=
    { env := Anc
      fintypeEnv := inferInstance
      decEqEnv := inferInstance
      isom := U_dec * W_Z
      isom_eq := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U_decᴴ,
          hU_l, Matrix.one_mul, hWZ_isom] }
  let ptraceEA : CPTPMap.{0} ((M × E) × B_tot) (M × M) :=
    { env := E × Anc
      fintypeEnv := inferInstance
      decEqEnv := inferInstance
      isom := Matrix.of fun p q ↦
        if p.1.1 = q.1.1 ∧ p.1.2 = q.2.1 ∧ p.2.1 = q.1.2 ∧ p.2.2 = q.2.2 then 1 else 0
      isom_eq := by
        ext ⟨⟨m₁, e₁⟩, ⟨m₁', anc₁⟩⟩ ⟨⟨m₂, e₂⟩, ⟨m₂', anc₂⟩⟩
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
          Fintype.sum_prod_type]
        rw [Finset.sum_eq_single m₁]
        · rw [Finset.sum_eq_single m₁']
          · rw [Finset.sum_eq_single e₁]
            · rw [Finset.sum_eq_single anc₁]
              · simp [Prod.mk.injEq, eq_comm]
              · intro anc _ hne; simp [hne]
              · intro h; exact absurd (Finset.mem_univ anc₁) h
            · intro e _ hne; apply Finset.sum_eq_zero; intro anc _; simp [hne]
            · intro h; exact absurd (Finset.mem_univ e₁) h
          · intro m' _ hne; apply Finset.sum_eq_zero; intro e _; apply Finset.sum_eq_zero; intro anc _; simp [hne]
          · intro h; exact absurd (Finset.mem_univ m₁') h
        · intro m _ hne; apply Finset.sum_eq_zero; intro m' _; apply Finset.sum_eq_zero; intro e _
          apply Finset.sum_eq_zero; intro anc _; simp [hne]
        · intro h; exact absurd (Finset.mem_univ m₁) h }
  have hptr_target : ptraceEA.apply (pureState ψ_target hψ_target_norm) = maxEntangledState M := by
    apply densityOp_eq_of_mat
    ext ⟨m₁, m₁'⟩ ⟨m₂, m₂'⟩
    rw [CPTPMap.apply_pureState]
    simp only [ptraceEA, maxEntangledState, pureState, Matrix.of_apply, B_tot, Anc, Fintype.sum_prod_type]
    have hs : ∀ (m m' : M) (e : E) (anc : Anc),
        ∑ p₁ : M, ∑ p₂ : E, ∑ q₁ : M, ∑ q₂ : Y, ∑ q₃ : A, ∑ q₄ : R, ∑ q₅ : E,
          (if m = p₁ ∧ m' = q₁ ∧ e = p₂ ∧ anc = (q₂, q₃, q₄, q₅) then (1 : ℂ) else 0) *
          ψ_target ((p₁, p₂), (q₁, (q₂, q₃, q₄, q₅))) =
        ψ_target ((m, e), (m', anc)) := by
      intro m m' e anc
      have heq : (∑ p : (M × E) × B_tot,
          (if m = p.1.1 ∧ m' = p.2.1 ∧ e = p.1.2 ∧ anc = p.2.2 then (1 : ℂ) else 0) *
          ψ_target p) = ψ_target ((m, e), (m', anc)) := by
        rw [Finset.sum_eq_single ((m, e), (m', anc))]
        · simp
        · intro p _ hne
          rw [if_neg, zero_mul]
          rintro ⟨h1, h2, h3, h4⟩
          exact hne (Prod.ext (Prod.ext h1.symm h3.symm) (Prod.ext h2.symm h4.symm))
        · intro h; exact absurd (Finset.mem_univ _) h
      simpa [B_tot, Anc, Fintype.sum_prod_type] using heq
    have hL1 : ∑ e : E, ∑ y : Y, ∑ a : A, ∑ r : R, ∑ e' : E,
        (∑ p₁ : M, ∑ p₂ : E, ∑ q₁ : M, ∑ q₂ : Y, ∑ q₃ : A, ∑ q₄ : R, ∑ q₅ : E,
          (if m₁ = p₁ ∧ m₁' = q₁ ∧ e = p₂ ∧ (y, a, r, e') = (q₂, q₃, q₄, q₅) then (1 : ℂ) else 0) *
          ψ_target ((p₁, p₂), (q₁, (q₂, q₃, q₄, q₅)))) *
        star (∑ p₁ : M, ∑ p₂ : E, ∑ q₁ : M, ∑ q₂ : Y, ∑ q₃ : A, ∑ q₄ : R, ∑ q₅ : E,
          (if m₂ = p₁ ∧ m₂' = q₁ ∧ e = p₂ ∧ (y, a, r, e') = (q₂, q₃, q₄, q₅) then (1 : ℂ) else 0) *
          ψ_target ((p₁, p₂), (q₁, (q₂, q₃, q₄, q₅)))) =
        ∑ e : E, ∑ y : Y, ∑ a : A, ∑ r : R, ∑ e' : E,
          ψ_target ((m₁, e), (m₁', (y, a, r, e'))) * star (ψ_target ((m₂, e), (m₂', (y, a, r, e')))) := by
      apply Finset.sum_congr rfl; intro e _
      apply Finset.sum_congr rfl; intro y _
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro e' _
      rw [hs m₁ m₁' e (y, a, r, e'), hs m₂ m₂' e (y, a, r, e')]
    rw [hL1]
    have h1 : ∀ e : E,
        ∑ y : Y, ∑ a : A, ∑ r : R, ∑ e' : E,
          ψ_target ((m₁, e), (m₁', (y, a, r, e'))) * star (ψ_target ((m₂, e), (m₂', (y, a, r, e')))) =
        maxEntangledVec M (m₁, m₁') * star (maxEntangledVec M (m₂, m₂')) * ρ_E.mat e e := by
      intro e
      simp only [ψ_target]
      rw [Finset.sum_eq_single y₀]
      · rw [Finset.sum_eq_single a₀]
        · rw [Finset.sum_eq_single r₀]
          · simp only [true_and, ↓reduceIte, star_mul']
            have hsq := congr_fun (congr_fun ρ_E.sqrtMat_mul_self e) e
            rw [Matrix.mul_apply] at hsq
            rw [← hsq, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro e' _
            have hh := congr_fun (congr_fun ρ_E.sqrtMat_isHermitian.eq e') e
            simp only [Matrix.conjTranspose_apply] at hh
            rw [← hh]; ring
          · intro r _ hne; apply Finset.sum_eq_zero; intro e' _; simp [hne]
          · intro h; exact absurd (Finset.mem_univ r₀) h
        · intro a _ hne; apply Finset.sum_eq_zero; intro r _; apply Finset.sum_eq_zero; intro e' _; simp [hne]
        · intro h; exact absurd (Finset.mem_univ a₀) h
      · intro y _ hne; apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro r _
        apply Finset.sum_eq_zero; intro e' _; simp [hne]
      · intro h; exact absurd (Finset.mem_univ y₀) h
    simp_rw [h1, ← Finset.mul_sum]
    have htr : ∑ e : E, ρ_E.mat e e = 1 := ρ_E.trace_one
    rw [htr, mul_one]
  have hptr_Z : ptraceEA.apply (pureState ψ_Z_dec hψ_Z_dec_norm) =
      entanglementChannelOutput 𝒩 n infoSet assistSet
        (cssPolarEncoder n infoSet randSet assistSet hdisj_ir hdisj_ia hdisj_ra uF v) 𝒟 := by
    let ℰ := cssPolarEncoder n infoSet randSet assistSet hdisj_ir hdisj_ia hdisj_ra uF v
    let aliceToBob := ((𝒩.tensorPow n).seqComp ℰ).tensor (CPTPMap.id A)
    let fullBob := 𝒟.seqComp aliceToBob
    let initVec : M × ((M × A) × A) → ℂ := fun p ↦
      maxEntangledVec M (p.1, p.2.1.1) * maxEntangledVec A (p.2.1.2, p.2.2)
    have hamp_eq : ∀ (m m' : M) (anc : Anc) (e : E),
        ∑ p : M × ((M × A) × A),
          (CPTPMap.tensorIdLeft M fullBob).isom ((m, m'), (anc, ((e, ()), ()))) p * initVec p =
        ψ_Z_dec ((m, e), (m', anc)) := by
      intro m m' anc e
      simp only [CPTPMap.tensorIdLeft, CPTPMap.seqComp, CPTPMap.tensor, CPTPMap.id,
        fullBob, aliceToBob, ℰ, cssPolarEncoder, cssPolarEncoderIsom, 𝒟,
        Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type, initVec, ← hV_def]
      rw [Finset.sum_eq_single m]
      · simp only [↓reduceIte, one_mul]
        rw [Finset.sum_eq_single m]
        · have ha_coll : ∀ a₁ : A,
              ∑ a₂ : A,
                (∑ y : Y, ∑ a' : A,
                  (∑ b : B_tot, U_dec (m', anc) b * W_Z b (y, a')) *
                  ((∑ x : Fin (2 ^ n) → Bool,
                    V_isom (y, e) x *
                    (((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹ *
                      ∑ r : R, if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a₁) then phaseSign v r else 0)) *
                   if a' = a₂ then (1 : ℂ) else 0)) *
                (maxEntangledVec M (m, m) * maxEntangledVec A (a₁, a₂)) =
              ∑ y : Y,
                (∑ b : B_tot, U_dec (m', anc) b * W_Z b (y, a₁)) *
                (ν * ∑ r : R, phaseSign v r * V_isom (y, e)
                  (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a₁))) := by
            intro a₁
            rw [Finset.sum_eq_single a₁]
            · simp only [maxEntangledVec, ↓reduceIte]
              have hν_eq : ((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹ *
                  (((Real.sqrt (Fintype.card M : ℝ) : ℝ) : ℂ)⁻¹ *
                   ((Real.sqrt (Fintype.card A : ℝ) : ℝ) : ℂ)⁻¹) = ν := by
                simp only [ν, M, A, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
                  Nat.cast_pow, Nat.cast_ofNat]; ring
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl; intro y _
              rw [Finset.sum_eq_single a₁]
              · simp only [↓reduceIte, mul_one]
                have hx_sum : ∑ x : Fin (2 ^ n) → Bool,
                    V_isom (y, e) x *
                    (((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹ *
                      ∑ r : R, if x = arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a₁) then phaseSign v r else 0) =
                    ((Real.sqrt ((2 : ℝ) ^ randSet.card) : ℝ) : ℂ)⁻¹ *
                      ∑ r : R, phaseSign v r * V_isom (y, e)
                        (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a₁)) := by
                  simp_rw [Finset.mul_sum]
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl; intro r _
                  rw [Finset.sum_eq_single (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a₁))]
                  · simp only [↓reduceIte]; ring
                  · intro x _ hne; simp [hne]
                  · intro h; exact absurd (Finset.mem_univ _) h
                rw [hx_sum, ← hν_eq]; ring
              · intro a' _ hne; simp [hne]
              · intro h; exact absurd (Finset.mem_univ a₁) h
            · intro a₂ _ hne; simp [maxEntangledVec, hne]
            · intro h; exact absurd (Finset.mem_univ a₁) h
          simp_rw [ha_coll]
          simp only [ψ_Z_dec, ψ_Z, ψ_ch, Fintype.sum_prod_type]
          rw [Finset.sum_comm]
          have hreorder : ∑ y : Y, ∑ a₁ : A,
              (∑ b : B_tot, U_dec (m', anc) b * W_Z b (y, a₁)) *
              (ν * ∑ r : R, phaseSign v r * V_isom (y, e)
                (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a₁))) =
              ∑ b : B_tot, U_dec (m', anc) b *
                ∑ y : Y, ∑ a₁ : A, W_Z b (y, a₁) *
                  (ν * ∑ r : R, phaseSign v r * V_isom (y, e)
                    (arikanTransform n (wiretapWord infoSet randSet assistSet uF m r a₁))) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            conv_lhs => arg 2; ext a₁; rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro b _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y _
            apply Finset.sum_congr rfl; intro a₁ _; ring
          simpa [Fintype.sum_prod_type] using hreorder
        · intro m₁ _ hne; apply Finset.sum_eq_zero; intro a₁ _; apply Finset.sum_eq_zero; intro a₂ _
          simp [maxEntangledVec, hne]
        · intro h; exact absurd (Finset.mem_univ m) h
      · intro m₁ _ hne; apply Finset.sum_eq_zero; intro m₂ _; apply Finset.sum_eq_zero; intro a₁ _
        apply Finset.sum_eq_zero; intro a₂ _; simp [hne]
      · intro h; exact absurd (Finset.mem_univ m) h
    apply densityOp_eq_of_mat
    ext ⟨m₁, m₁'⟩ ⟨m₂, m₂'⟩
    have hL : (ptraceEA.apply (pureState ψ_Z_dec hψ_Z_dec_norm)).mat (m₁, m₁') (m₂, m₂') =
        ∑ e : E, ∑ anc : Anc, ψ_Z_dec ((m₁, e), (m₁', anc)) * star (ψ_Z_dec ((m₂, e), (m₂', anc))) := by
      rw [CPTPMap.apply_pureState]
      simp only [ptraceEA, Matrix.of_apply, B_tot, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro e _
      apply Finset.sum_congr rfl; intro anc _
      have hs : ∀ (m m' : M),
          ∑ p₁ : M, ∑ p₂ : E, ∑ q₁ : M, ∑ q₂ : Anc,
            (if m = p₁ ∧ m' = q₁ ∧ e = p₂ ∧ anc = q₂ then (1 : ℂ) else 0) *
            ψ_Z_dec ((p₁, p₂), (q₁, q₂)) =
          ψ_Z_dec ((m, e), (m', anc)) := by
        intro m m'
        have heq : (∑ p : (M × E) × B_tot,
            (if m = p.1.1 ∧ m' = p.2.1 ∧ e = p.1.2 ∧ anc = p.2.2 then (1 : ℂ) else 0) *
            ψ_Z_dec p) = ψ_Z_dec ((m, e), (m', anc)) := by
          rw [Finset.sum_eq_single ((m, e), (m', anc))]
          · simp
          · intro p _ hne
            rw [if_neg, zero_mul]
            rintro ⟨h1, h2, h3, h4⟩
            exact hne (Prod.ext (Prod.ext h1.symm h3.symm) (Prod.ext h2.symm h4.symm))
          · intro h; exact absurd (Finset.mem_univ _) h
        simpa [B_tot, Fintype.sum_prod_type] using heq
      rw [hs m₁ m₁', hs m₂ m₂']
    have hR : (entanglementChannelOutput 𝒩 n infoSet assistSet ℰ 𝒟).mat (m₁, m₁') (m₂, m₂') =
        ∑ e : E, ∑ anc : Anc, ψ_Z_dec ((m₁, e), (m₁', anc)) * star (ψ_Z_dec ((m₂, e), (m₂', anc))) := by
      unfold entanglementChannelOutput
      rw [CPTPMap.apply_pureState]
      simp only [Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_unique]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro e _
      apply Finset.sum_congr rfl; intro anc _
      change (∑ p : M × ((M × A) × A),
        (CPTPMap.tensorIdLeft M fullBob).isom ((m₁, m₁'), (anc, ((e, ()), ()))) p * initVec p) *
        star (∑ p : M × ((M × A) × A),
        (CPTPMap.tensorIdLeft M fullBob).isom ((m₂, m₂'), (anc, ((e, ()), ()))) p * initVec p) = _
      rw [hamp_eq m₁ m₁' anc e, hamp_eq m₂ m₂' anc e]
    rw [hL, hR]
  refine ⟨v, 𝒟, ?_⟩
  unfold quantumEntanglementError
  rw [← hptr_Z, ← hptr_target]
  exact le_trans (traceDist_cptp_le ptraceEA _ _) htd_tot

end CoherentDecoderTheorem

/-- Bundled operational entanglement-assisted coherent CSS quantum polar code for a qubit-input
quantum channel `𝒩` at blocklength `N = 2^n`, with a genuine isometric CSS encoder `ℰ`, a
genuine coherent CPTP decoder `𝒟`, and the operational entanglement-transmission trace-distance
error `T((id_R ⊗ 𝒟 ∘ 𝒩^⊗N ∘ ℰ)(Φ^+_{RM} ⊗ Φ^+_{E_A E_B}), Φ^+_{RM})`. -/
structure OperationalQuantumPolarCode {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap.{0} Bool d) (n : ℕ) where
  infoSet : Finset (Fin (2 ^ n))
  randSet : Finset (Fin (2 ^ n))
  assistSet : Finset (Fin (2 ^ n))
  disj_ir : Disjoint infoSet randSet
  disj_ia : Disjoint infoSet assistSet
  disj_ra : Disjoint randSet assistSet
  publicFrozen : Fin (2 ^ n) → Bool
  phaseChoice : randSet → Bool
  decoder : CPTPMap.{0} ((Fin (2 ^ n) → d) × (assistSet → Bool)) (infoSet → Bool)

noncomputable def OperationalQuantumPolarCode.encoder {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap.{0} Bool d} {n : ℕ} (C : OperationalQuantumPolarCode 𝒩 n) :
    CPTPMap.{0} ((C.infoSet → Bool) × (C.assistSet → Bool)) (Fin (2 ^ n) → Bool) :=
  cssPolarEncoder n C.infoSet C.randSet C.assistSet C.disj_ir C.disj_ia C.disj_ra
    C.publicFrozen C.phaseChoice

noncomputable def OperationalQuantumPolarCode.entanglementError {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap.{0} Bool d} {n : ℕ} (C : OperationalQuantumPolarCode 𝒩 n) : ℝ :=
  quantumEntanglementError 𝒩 n C.infoSet C.assistSet C.encoder C.decoder

noncomputable def OperationalQuantumPolarCode.rate {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap.{0} Bool d} {n : ℕ} (C : OperationalQuantumPolarCode 𝒩 n) : ℝ :=
  (C.infoSet.card : ℝ) / ((2 : ℝ) ^ n)

noncomputable def OperationalQuantumPolarCode.assistanceRate {d : Type} [Fintype d] [DecidableEq d]
    {𝒩 : CPTPMap.{0} Bool d} {n : ℕ} (C : OperationalQuantumPolarCode 𝒩 n) : ℝ :=
  (C.assistSet.card : ℝ) / ((2 : ℝ) ^ n)

end PolarCodes
