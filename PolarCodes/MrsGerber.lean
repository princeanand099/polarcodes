/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.ChannelDuality
import PolarCodes.DephasingSDPI
import PolarCodes.SplittingBounds

/-!
# Quantum Mrs. Gerber Bounds (Theorem 1.2 & Propositions 4.2–4.4)

This module formalizes Section 4 of the manuscript:
1. **Theorem 1.2(a) — Hybrid Quantum Mrs. Gerber's Lemma**:
   - Pure-state branch (`theorem_1_2a_pure`): for arbitrary `W₁` and pure-state `W₂`,
     `H(W₁ ⊛ W₂) ≤ 1 - gc(1 - H₁, 1 - H₂)` and
     `H(W₁ ⊠ W₂) ≥ H₁ + H₂ - 1 + gc(1 - H₁, 1 - H₂) ≥ gq(H₁, H₂)`.
   - Classical branch (`theorem_1_2a_classical`): for arbitrary `W₁` and classical `W₂`,
     `H(W₁ ⊠ W₂) ≥ gc(H₁, H₂) ≥ gq(H₁, H₂)` (proved via BSC duality + simultaneous
     unitary diagonalization + posterior conditioning + Wyner–Ziv convexity `convexOn_gc`).
2. **Proposition 4.2 — Four-Branch Purification Bound** (`prop_4_2_four_branch`):
   for ALL independent binary-input c-q channels `W₁, W₂`,
   `H(W₁ ⊠ W₂) ≥ max { H₁ + Δ(1 - H₁, 1 - 2^{H₂ - 1}), H₂ + Δ(1 - H₂, 1 - 2^{H₁ - 1}),
                        H₂ + Δ(H₁, 1 - 2^{-H₂}), H₁ + Δ(H₂, 1 - 2^{-H₁}) }`.
3. **Theorem 1.2(b) — Linear-Scaling Splitting & Uniform Potential Contraction**
   (`theorem_1_2b_linear_splitting`, `theorem_1_2b_potential_contraction`):
   for every binary-input c-q channel `W`,
   `H(W⁻) - H(W) = H(W) - H(W⁺) ≥ θ₀ H(W)(1 - H(W))` and
   `½ (T(W⁻) + T(W⁺)) ≤ Λ₀ T(W)` with `Λ₀ = √(1 - θ₀²/4) < 1`.
-/

open Matrix BigOperators Real Filter Topology Set
open scoped ComplexOrder

namespace PolarCodes

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-! ### Helper: Unitary Equivalence and Block-Diagonal Entropy Identities -/

/-- Unitary invariance of `CQChannel.condEntropy` when output states are conjugated by `U`. -/
lemma condEntropy_eq_of_conjUnitary {W₁ W₂ : CQChannel d} (U : Matrix.unitaryGroup d ℂ)
    (h0 : (W₂.out false).mat = (DensityOp.conjUnitary U (W₁.out false)).mat)
    (h1 : (W₂.out true).mat = (DensityOp.conjUnitary U (W₁.out true)).mat) :
    W₂.condEntropy = W₁.condEntropy := by
  unfold CQChannel.condEntropy qjs
  have hm : (DensityOp.midpoint (W₂.out false) (W₂.out true)).mat =
      (DensityOp.conjUnitary U (DensityOp.midpoint (W₁.out false) (W₁.out true))).mat := by
    simp only [DensityOp.midpoint, DensityOp.mix, DensityOp.conjUnitary, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, h0, h1]
  rw [vonNeumannEntropy_eq_of_mat_eq h0, vonNeumannEntropy_eq_of_mat_eq h1,
    vonNeumannEntropy_eq_of_mat_eq hm,
    vonNeumannEntropy_conjUnitary, vonNeumannEntropy_conjUnitary, vonNeumannEntropy_conjUnitary]

/-- Swapping the order of `W₁, W₂` in `checkCombine` preserves `condEntropy`. -/
lemma condEntropy_checkCombine_comm (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    (CQChannel.checkCombine W₁ W₂).condEntropy = (CQChannel.checkCombine W₂ W₁).condEntropy := by
  -- Reindex `d₁ × d₂ ≃ d₂ × d₁` via swap matrix
  let e : d₁ × d₂ ≃ d₂ × d₁ := Equiv.prodComm d₁ d₂
  have hS_swap : ∀ (A : DensityOp (d₁ × d₂)) (B : DensityOp (d₂ × d₁)),
      (∀ i₁ i₂ j₁ j₂, A.mat (i₁, i₂) (j₁, j₂) = B.mat (i₂, i₁) (j₂, j₁)) →
      vonNeumannEntropy A = vonNeumannEntropy B := by
    intro A B hAB
    let P : Matrix (d₁ × d₂) (d₂ × d₁) ℂ := Matrix.of fun p q ↦ if e p = q then 1 else 0
    have hPPH : P * Pᴴ = 1 := by
      ext p q
      simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
      rw [Finset.sum_eq_single (e p)]
      · simp [e.injective.eq_iff, eq_comm]
      · intro r _ hr; simp [Ne.symm hr]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hPHP : Pᴴ * P = 1 := by
      ext p q
      simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
      rw [Finset.sum_eq_single (e.symm p)]
      · simp [e.symm_apply_eq, eq_comm]
      · intro r _ hr; simp [show e r ≠ p from fun h ↦ hr (e.symm_apply_eq.mpr h.symm).symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hmat : A.mat = P * B.mat * Pᴴ := by
      ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
      simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
      rw [Finset.sum_eq_single (j₂, j₁)]
      · rw [Finset.sum_eq_single (i₂, i₁)]
        · simp [e, hAB]
        · intro r _ hr; simp [e, Ne.symm hr]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro r _ hr; simp [e, Ne.symm hr]
      · intro h; exact absurd (Finset.mem_univ _) h
    unfold vonNeumannEntropy DensityOp.eigvals
    congr 1
    let M : Matrix (d₁ × d₂) (d₂ × d₁) ℂ := P * B.sqrtMat
    have hMMH : M * Mᴴ = A.mat := by
      calc M * Mᴴ = P * (B.sqrtMat * B.sqrtMat) * Pᴴ := by
            simp only [M, Matrix.conjTranspose_mul, B.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
        _ = P * B.mat * Pᴴ := by rw [B.sqrtMat_mul_self]
        _ = A.mat := hmat.symm
    have hMHM : Mᴴ * M = B.mat := by
      calc Mᴴ * M = B.sqrtMat * ((Pᴴ * P) * B.sqrtMat) := by
            simp only [M, Matrix.conjTranspose_mul, B.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
        _ = B.mat := by rw [hPHP, Matrix.one_mul, B.sqrtMat_mul_self]
    have hcp := charpoly_mul_conjTranspose_eq M
    rw [hMMH, hMHM] at hcp
    exact spectral_sum_eq_of_charpoly_mul_X_pow A.isHermitian B.isHermitian hcp (by simp [Real.negMulLog])
  unfold CQChannel.condEntropy qjs
  have h0 := hS_swap ((CQChannel.checkCombine W₁ W₂).out false) ((CQChannel.checkCombine W₂ W₁).out false) (by
    intro i₁ i₂ j₁ j₂
    simp only [CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Bool.not_false, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul]
    ring)
  have h1 := hS_swap ((CQChannel.checkCombine W₁ W₂).out true) ((CQChannel.checkCombine W₂ W₁).out true) (by
    intro i₁ i₂ j₁ j₂
    simp only [CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Bool.not_true, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul]
    ring)
  have hm := hS_swap (DensityOp.midpoint ((CQChannel.checkCombine W₁ W₂).out false) ((CQChannel.checkCombine W₁ W₂).out true))
    (DensityOp.midpoint ((CQChannel.checkCombine W₂ W₁).out false) ((CQChannel.checkCombine W₂ W₁).out true)) (by
    intro i₁ i₂ j₁ j₂
    simp only [CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Bool.not_false, Bool.not_true, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul]
    ring)
  rw [h0, h1, hm]

/-- Swapping `false` and `true` inputs of `W₁` preserves `H(W₁ ⊠ W₂)` and `H(W₁)`. -/
private lemma condEntropy_checkCombine_flip (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    (CQChannel.checkCombine ⟨fun b ↦ W₁.out (!b)⟩ W₂).condEntropy =
      (CQChannel.checkCombine W₁ W₂).condEntropy := by
  unfold CQChannel.condEntropy
  have h0 : ((CQChannel.checkCombine ⟨fun b ↦ W₁.out (!b)⟩ W₂).out false).mat =
      ((CQChannel.checkCombine W₁ W₂).out true).mat := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Bool.not_false, Bool.not_true, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
      Complex.real_smul]
    ring
  have h1 : ((CQChannel.checkCombine ⟨fun b ↦ W₁.out (!b)⟩ W₂).out true).mat =
      ((CQChannel.checkCombine W₁ W₂).out false).mat := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Bool.not_false, Bool.not_true, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
      Complex.real_smul]
    ring
  have hq : qjs ((CQChannel.checkCombine ⟨fun b ↦ W₁.out (!b)⟩ W₂).out false)
      ((CQChannel.checkCombine ⟨fun b ↦ W₁.out (!b)⟩ W₂).out true) =
      qjs ((CQChannel.checkCombine W₁ W₂).out false) ((CQChannel.checkCombine W₁ W₂).out true) := by
    rw [qjs_symm ((CQChannel.checkCombine W₁ W₂).out false)]
    unfold qjs
    have hm : (DensityOp.midpoint ((CQChannel.checkCombine ⟨fun b ↦ W₁.out (!b)⟩ W₂).out false)
        ((CQChannel.checkCombine ⟨fun b ↦ W₁.out (!b)⟩ W₂).out true)).mat =
        (DensityOp.midpoint ((CQChannel.checkCombine W₁ W₂).out true)
          ((CQChannel.checkCombine W₁ W₂).out false)).mat := by
      simp only [DensityOp.midpoint, DensityOp.mix, h0, h1]
    rw [vonNeumannEntropy_eq_of_mat_eq h0, vonNeumannEntropy_eq_of_mat_eq h1,
      vonNeumannEntropy_eq_of_mat_eq hm]
  rw [hq]

/-- Conditional entropy of a general channel `W` lies in `[0, 1]`. -/
lemma condEntropy_mem_Icc (W : CQChannel d) : W.condEntropy ∈ Set.Icc (0 : ℝ) 1 := by
  haveI : Nonempty d := by
    by_contra h0
    haveI : IsEmpty d := not_nonempty_iff.mp h0
    have htr := (W.out false).trace_one
    simp [Matrix.trace] at htr
  have hmax_pd : (maxMixedState d).mat.PosDef := by
    have hpos : (0 : ℝ) < ((Fintype.card d : ℝ)⁻¹) := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    simpa [maxMixedState, Complex.real_smul] using (Matrix.PosDef.one (n := d) (R := ℂ)).smul hpos
  have hq_mem : qjs (W.out false) (W.out true) ∈ Set.Icc (0 : ℝ) 1 := by
    let ρ := W.out false
    let σ := W.out true
    let f : ℝ → ℝ := fun ε ↦
      if h : 0 ≤ ε ∧ ε ≤ 1 then
        qjs (DensityOp.mix ε h.1 h.2 ρ (maxMixedState d))
          (DensityOp.mix ε h.1 h.2 σ (maxMixedState d))
      else 0
    have hf : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (qjs ρ σ)) := by
      have h1' := tendsto_vonNeumannEntropy_mix_maxMixed (DensityOp.midpoint ρ σ)
      have h2' := tendsto_vonNeumannEntropy_mix_maxMixed ρ
      have h3' := tendsto_vonNeumannEntropy_mix_maxMixed σ
      have hcomb := h1'.sub ((h2'.add h3').div_const 2)
      refine hcomb.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      have hc : 0 ≤ ε ∧ ε ≤ 1 := ⟨le_of_lt hε.1, le_of_lt hε.2⟩
      dsimp only [f]; rw [dif_pos hc, dif_pos hc, dif_pos hc, dif_pos hc]; unfold qjs
      have hmid : (DensityOp.midpoint (DensityOp.mix ε hc.1 hc.2 ρ (maxMixedState d))
          (DensityOp.mix ε hc.1 hc.2 σ (maxMixedState d))).mat =
          (DensityOp.mix ε hc.1 hc.2 (DensityOp.midpoint ρ σ) (maxMixedState d)).mat := by
        ext i j
        simp only [DensityOp.midpoint, DensityOp.mix, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
        push_cast; ring
      rw [vonNeumannEntropy_eq_of_mat_eq hmid]
    have hpd_all : ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (τ : DensityOp d),
        (DensityOp.mix ε (le_of_lt hε.1) (le_of_lt hε.2) τ (maxMixedState d)).mat.PosDef := by
      intro ε hε τ
      have ha : ((1 - ε : ℝ) • τ.mat).PosSemidef := τ.posSemidef.smul (by linarith [hε.2])
      have hb : (ε • (maxMixedState d).mat).PosDef := hmax_pd.smul hε.1
      simpa [DensityOp.mix, add_comm] using hb.add_posSemidef ha
    constructor
    · refine ge_of_tendsto hf ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      have hc : 0 ≤ ε ∧ ε ≤ 1 := ⟨le_of_lt hε.1, le_of_lt hε.2⟩
      dsimp only [f]; rw [dif_pos hc]
      exact (qjs_eq_half_relEntropy_midpoint (hpd_all ε hε ρ) (hpd_all ε hε σ)).1
    · refine le_of_tendsto hf ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      have hc : 0 ≤ ε ∧ ε ≤ 1 := ⟨le_of_lt hε.1, le_of_lt hε.2⟩
      dsimp only [f]; rw [dif_pos hc]
      have hmid_le : qjs (DensityOp.mix ε hc.1 hc.2 ρ (maxMixedState d))
          (DensityOp.mix ε hc.1 hc.2 σ (maxMixedState d)) ≤ 1 := by
        have hW' : (CQChannel.mk fun b ↦ if b = false then DensityOp.mix ε hc.1 hc.2 ρ (maxMixedState d)
            else DensityOp.mix ε hc.1 hc.2 σ (maxMixedState d)).condEntropy ≥ 0 := by
          have h5 := condEntropy_ge_one_sub_h2 (CQChannel.mk fun b ↦ if b = false then DensityOp.mix ε hc.1 hc.2 ρ (maxMixedState d)
            else DensityOp.mix ε hc.1 hc.2 σ (maxMixedState d))
          have hh2 : h2 ((1 - (CQChannel.mk fun b ↦ if b = false then DensityOp.mix ε hc.1 hc.2 ρ (maxMixedState d)
            else DensityOp.mix ε hc.1 hc.2 σ (maxMixedState d)).fidelityParam) / 2) ≤ 1 := h2_le_one _
          linarith
        simpa [CQChannel.condEntropy] using hW'
      exact hmid_le
  unfold CQChannel.condEntropy
  exact ⟨by linarith [hq_mem.2], by linarith [hq_mem.1]⟩

/-! ### Part 1: Theorem 1.2(a) — Pure-State Hybrid Bound -/

/-- **Theorem 1.2(a) (Pure-State Hybrid Q-MGL)**:
For any binary-input c-q channel `W₁` and any pure-state channel `W₂`,
`H(W₁ ⊛ W₂) ≤ 1 - gc(1 - H₁, 1 - H₂)` and
`H(W₁ ⊠ W₂) ≥ H₁ + H₂ - 1 + gc(1 - H₁, 1 - H₂) ≥ gq(H₁, H₂)`. -/
theorem theorem_1_2a_pure (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) (hW₂ : W₂.IsPureState) :
    (CQChannel.varCombine W₁ W₂).condEntropy ≤
      1 - gc (1 - W₁.condEntropy) (1 - W₂.condEntropy) ∧
    W₁.condEntropy + W₂.condEntropy - 1 + gc (1 - W₁.condEntropy) (1 - W₂.condEntropy) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy ∧
    gq W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy := by
  obtain ⟨φ₀, φ₁, hφ₀, hφ₁, hmat₀, hmat₁⟩ := hW₂
  set ρ₀ := W₁.out false
  set ρ₁ := W₁.out true
  set σ₀ := pureState φ₀ hφ₀
  set σ₁ := pureState φ₁ hφ₁
  set f₂ := ‖∑ i : d₂, star (φ₀ i) * φ₁ i‖
  have hf₂_nn : 0 ≤ f₂ := norm_nonneg _
  have hf₂_le1 : f₂ ≤ 1 := by
    have h := (lemma_4_1_gram_dephasing ρ₀ ρ₁ φ₀ φ₁ hφ₀ hφ₁).1
    linarith
  set p := (1 - f₂) / 2
  have hp0 : 0 ≤ p := by linarith
  have hp1 : p ≤ 1 / 2 := by linarith
  -- Step 1: `W₂.condEntropy = 1 - h2 p` and `h2Inv (1 - W₂.condEntropy) = p`
  have hH₂ : W₂.condEntropy = 1 - h2 p := by
    unfold CQChannel.condEntropy
    have hq_eq : qjs (W₂.out false) (W₂.out true) = qjs σ₀ σ₁ := by
      unfold qjs
      have hm : (DensityOp.midpoint (W₂.out false) (W₂.out true)).mat = (DensityOp.midpoint σ₀ σ₁).mat := by
        simp only [DensityOp.midpoint, DensityOp.mix, σ₀, σ₁, pureState, hmat₀, hmat₁]
      rw [vonNeumannEntropy_eq_of_mat_eq hmat₀, vonNeumannEntropy_eq_of_mat_eq hmat₁,
        vonNeumannEntropy_eq_of_mat_eq hm]
    rw [hq_eq, qjs_pureState φ₀ φ₁ hφ₀ hφ₁]
  have hinv₂ : h2Inv (1 - W₂.condEntropy) = p := by
    rw [hH₂, sub_sub_cancel, h2Inv_h2 ⟨hp0, hp1⟩]
  -- Step 2: Both `U₁`-branches in Eq. (2.7) equal `dephaseCoherence p (gramState ρ₀ ρ₁)`
  have hbranch0 : 1 - qjs (DensityOp.tensor ρ₀ (W₂.out false)) (DensityOp.tensor ρ₁ (W₂.out true)) =
      dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₀ ρ₁) := by
    have hL := lemma_4_1_gram_dephasing ρ₀ ρ₁ φ₀ φ₁ hφ₀ hφ₁
    have hq_eq : qjs (DensityOp.tensor ρ₀ (W₂.out false)) (DensityOp.tensor ρ₁ (W₂.out true)) =
        qjs (DensityOp.tensor ρ₀ σ₀) (DensityOp.tensor ρ₁ σ₁) := by
      unfold qjs
      have h0 : (DensityOp.tensor ρ₀ (W₂.out false)).mat = (DensityOp.tensor ρ₀ σ₀).mat := by
        simp [DensityOp.tensor, σ₀, pureState, hmat₀]
      have h1 : (DensityOp.tensor ρ₁ (W₂.out true)).mat = (DensityOp.tensor ρ₁ σ₁).mat := by
        simp [DensityOp.tensor, σ₁, pureState, hmat₁]
      have hm : (DensityOp.midpoint (DensityOp.tensor ρ₀ (W₂.out false)) (DensityOp.tensor ρ₁ (W₂.out true))).mat =
          (DensityOp.midpoint (DensityOp.tensor ρ₀ σ₀) (DensityOp.tensor ρ₁ σ₁)).mat := by
        simp [DensityOp.midpoint, DensityOp.mix, h0, h1]
      rw [vonNeumannEntropy_eq_of_mat_eq h0, vonNeumannEntropy_eq_of_mat_eq h1,
        vonNeumannEntropy_eq_of_mat_eq hm]
    rw [hq_eq]
    unfold qjs dephaseCoherence
    have hSσ₀ : vonNeumannEntropy σ₀ = 0 := by
      have := (lemma_4_1_gram_dephasing ρ₀ ρ₁ φ₀ φ₁ hφ₀ hφ₁).2.2.1
      -- Pure state has entropy 0 via Sylvester charpoly on rank-1 matrix `M : d₂ × Unit`
      let M : Matrix d₂ Unit ℂ := Matrix.of fun i _ ↦ φ₀ i
      have hMMH : M * Mᴴ = σ₀.mat := by ext i j; simp [M, σ₀, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply]
      have hMHM : Mᴴ * M = Matrix.diagonal (Complex.ofReal ∘ fun _ : Unit ↦ (1 : ℝ)) := by
        ext ⟨⟩ ⟨⟩
        simp only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Matrix.diagonal_apply, Function.comp_apply, ↓reduceIte, Complex.ofReal_one]
        have hterm : ∀ i : d₂, star (φ₀ i) * φ₀ i = ((‖φ₀ i‖ ^ 2 : ℝ) : ℂ) := by
          intro i; rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        simp_rw [hterm, ← Complex.ofReal_sum, hφ₀, Complex.ofReal_one]
      have hD : (Matrix.diagonal (Complex.ofReal ∘ fun _ : Unit ↦ (1 : ℝ))).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext _; simp
      have hcp := charpoly_mul_conjTranspose_eq M
      rw [hMMH, hMHM] at hcp
      unfold vonNeumannEntropy DensityOp.eigvals
      have hsum : ∑ i : d₂, Real.negMulLog (σ₀.isHermitian.eigenvalues i) = ∑ _ : Unit, Real.negMulLog (1 : ℝ) := by
        trans ∑ u : Unit, Real.negMulLog (hD.eigenvalues u)
        · exact spectral_sum_eq_of_charpoly_mul_X_pow σ₀.isHermitian hD hcp (by simp [Real.negMulLog])
        · exact spectral_sum_diagonal (fun _ ↦ 1) hD (by simp [Real.negMulLog])
      rw [hsum]; simp [Real.negMulLog]
    have hSσ₁ : vonNeumannEntropy σ₁ = 0 := by
      let M : Matrix d₂ Unit ℂ := Matrix.of fun i _ ↦ φ₁ i
      have hMMH : M * Mᴴ = σ₁.mat := by ext i j; simp [M, σ₁, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply]
      have hMHM : Mᴴ * M = Matrix.diagonal (Complex.ofReal ∘ fun _ : Unit ↦ (1 : ℝ)) := by
        ext ⟨⟩ ⟨⟩
        simp only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Matrix.diagonal_apply, Function.comp_apply, ↓reduceIte, Complex.ofReal_one]
        have hterm : ∀ i : d₂, star (φ₁ i) * φ₁ i = ((‖φ₁ i‖ ^ 2 : ℝ) : ℂ) := by
          intro i; rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        simp_rw [hterm, ← Complex.ofReal_sum, hφ₁, Complex.ofReal_one]
      have hD : (Matrix.diagonal (Complex.ofReal ∘ fun _ : Unit ↦ (1 : ℝ))).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext _; simp
      have hcp := charpoly_mul_conjTranspose_eq M
      rw [hMMH, hMHM] at hcp
      unfold vonNeumannEntropy DensityOp.eigvals
      have hsum : ∑ i : d₂, Real.negMulLog (σ₁.isHermitian.eigenvalues i) = ∑ _ : Unit, Real.negMulLog (1 : ℝ) := by
        trans ∑ u : Unit, Real.negMulLog (hD.eigenvalues u)
        · exact spectral_sum_eq_of_charpoly_mul_X_pow σ₁.isHermitian hD hcp (by simp [Real.negMulLog])
        · exact spectral_sum_diagonal (fun _ ↦ 1) hD (by simp [Real.negMulLog])
      rw [hsum]; simp [Real.negMulLog]
    rw [vonNeumannEntropy_tensor, vonNeumannEntropy_tensor, hSσ₀, hSσ₁, add_zero, add_zero,
      hL.2.1, hL.2.2.1]
    ring
  have hbranch1 : 1 - qjs (DensityOp.tensor ρ₁ (W₂.out false)) (DensityOp.tensor ρ₀ (W₂.out true)) =
      dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₀ ρ₁) := by
    -- Same via `lemma_4_1_gram_dephasing ρ₁ ρ₀ φ₀ φ₁` + `X ⊗ I` unitary equivalence of `gramState ρ₁ ρ₀` and `gramState ρ₀ ρ₁`
    have hL := lemma_4_1_gram_dephasing ρ₁ ρ₀ φ₀ φ₁ hφ₀ hφ₁
    let XI : Matrix.unitaryGroup (Bool × d₁) ℂ :=
      ⟨Matrix.of fun a b ↦ if a.1 = !b.1 ∧ a.2 = b.2 then 1 else 0, by
        rw [Matrix.mem_unitaryGroup_iff']
        ext ⟨a₁, i₁⟩ ⟨a₂, i₂⟩
        simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply,
          Fintype.sum_prod_type, Fintype.sum_bool]
        cases a₁ <;> cases a₂ <;> simp [eq_comm]⟩
    have hX_gram : (DensityOp.conjUnitary XI (gramState ρ₀ ρ₁)).mat = (gramState ρ₁ ρ₀).mat := by
      ext ⟨a, i⟩ ⟨b, j⟩
      simp only [DensityOp.conjUnitary, XI, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply]
      rw [Finset.sum_eq_single (!b, j)]
      · rw [Finset.sum_eq_single (!a, i)]
        · simp only [Bool.not_not, and_self, ↓reduceIte, one_mul, star_one, mul_one]
          simp only [gramState, gramFactor, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
          cases a <;> cases b <;> simp
        · intro ⟨c, k⟩ _ hne
          have : ¬(a = !c ∧ i = k) := by
            intro ⟨h1, h2⟩; apply hne; ext
            · simp [h1]
            · exact h2.symm
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro ⟨c, k⟩ _ hne
        have : ¬(b = !c ∧ j = k) := by
          intro ⟨h1, h2⟩; apply hne; ext
          · simp [h1]
          · exact h2.symm
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hX_deph : (DensityOp.conjUnitary XI (dephaseState p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₀ ρ₁))).mat =
        (dephaseState p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₁ ρ₀)).mat := by
      have hXZ : (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ) * (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) =
          -((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) * (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ)) := by
        ext ⟨a, i⟩ ⟨b, j⟩
        simp only [XI, pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply, Matrix.neg_apply]
        rw [Finset.sum_eq_single (b, j)]
        · rw [Finset.sum_eq_single (a, i)]
          · cases a <;> cases b <;> simp
          · intro r _ hr; simp [Ne.symm hr]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro r _ hr; simp [hr]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hXZ_conj : (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
          (DensityOp.conjUnitary (pauliZTensorI d₁) (gramState ρ₀ ρ₁)).mat *
          star (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ) =
          (DensityOp.conjUnitary (pauliZTensorI d₁) (gramState ρ₁ ρ₀)).mat := by
        rw [← hX_gram]
        simp only [DensityOp.conjUnitary, Matrix.mul_assoc]
        have h1 : (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ) * (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
            ((gramState ρ₀ ρ₁).mat * (star (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
              star (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ))) =
            ((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) * (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ)) *
            ((gramState ρ₀ ρ₁).mat * (star (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
              star (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ))) := by
          have hst : star (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
              star (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ) =
              -(star (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
                star (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ)) := by
            have := congr_arg star hXZ
            simpa [Matrix.star_mul] using this
          rw [hXZ, hst, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
        simpa only [Matrix.mul_assoc] using h1
      simp only [DensityOp.conjUnitary, dephaseState, DensityOp.mix, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul]
      rw [show (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ) * (gramState ρ₀ ρ₁).mat *
          star (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ) = (gramState ρ₁ ρ₀).mat from hX_gram,
        hXZ_conj]
    have hS_deph : vonNeumannEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₁ ρ₀)) =
        vonNeumannEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₀ ρ₁)) := by
      rw [← vonNeumannEntropy_eq_of_mat_eq hX_deph, vonNeumannEntropy_conjUnitary]
    have hq_eq : qjs (DensityOp.tensor ρ₁ (W₂.out false)) (DensityOp.tensor ρ₀ (W₂.out true)) =
        qjs (DensityOp.tensor ρ₁ σ₀) (DensityOp.tensor ρ₀ σ₁) := by
      unfold qjs
      have h0 : (DensityOp.tensor ρ₁ (W₂.out false)).mat = (DensityOp.tensor ρ₁ σ₀).mat := by
        simp [DensityOp.tensor, σ₀, pureState, hmat₀]
      have h1 : (DensityOp.tensor ρ₀ (W₂.out true)).mat = (DensityOp.tensor ρ₀ σ₁).mat := by
        simp [DensityOp.tensor, σ₁, pureState, hmat₁]
      have hm : (DensityOp.midpoint (DensityOp.tensor ρ₁ (W₂.out false)) (DensityOp.tensor ρ₀ (W₂.out true))).mat =
          (DensityOp.midpoint (DensityOp.tensor ρ₁ σ₀) (DensityOp.tensor ρ₀ σ₁)).mat := by
        simp [DensityOp.midpoint, DensityOp.mix, h0, h1]
      rw [vonNeumannEntropy_eq_of_mat_eq h0, vonNeumannEntropy_eq_of_mat_eq h1,
        vonNeumannEntropy_eq_of_mat_eq hm]
    rw [hq_eq]
    unfold qjs dephaseCoherence
    have hSσ₀ : vonNeumannEntropy σ₀ = 0 := by
      let M : Matrix d₂ Unit ℂ := Matrix.of fun i _ ↦ φ₀ i
      have hMMH : M * Mᴴ = σ₀.mat := by ext i j; simp [M, σ₀, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply]
      have hMHM : Mᴴ * M = Matrix.diagonal (Complex.ofReal ∘ fun _ : Unit ↦ (1 : ℝ)) := by
        ext ⟨⟩ ⟨⟩
        simp only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Matrix.diagonal_apply, Function.comp_apply, ↓reduceIte, Complex.ofReal_one]
        have hterm : ∀ i : d₂, star (φ₀ i) * φ₀ i = ((‖φ₀ i‖ ^ 2 : ℝ) : ℂ) := by
          intro i; rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        simp_rw [hterm, ← Complex.ofReal_sum, hφ₀, Complex.ofReal_one]
      have hD : (Matrix.diagonal (Complex.ofReal ∘ fun _ : Unit ↦ (1 : ℝ))).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext _; simp
      have hcp := charpoly_mul_conjTranspose_eq M
      rw [hMMH, hMHM] at hcp
      unfold vonNeumannEntropy DensityOp.eigvals
      have hsum : ∑ i : d₂, Real.negMulLog (σ₀.isHermitian.eigenvalues i) = ∑ _ : Unit, Real.negMulLog (1 : ℝ) := by
        trans ∑ u : Unit, Real.negMulLog (hD.eigenvalues u)
        · exact spectral_sum_eq_of_charpoly_mul_X_pow σ₀.isHermitian hD hcp (by simp [Real.negMulLog])
        · exact spectral_sum_diagonal (fun _ ↦ 1) hD (by simp [Real.negMulLog])
      rw [hsum]; simp [Real.negMulLog]
    have hSσ₁ : vonNeumannEntropy σ₁ = 0 := by
      let M : Matrix d₂ Unit ℂ := Matrix.of fun i _ ↦ φ₁ i
      have hMMH : M * Mᴴ = σ₁.mat := by ext i j; simp [M, σ₁, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply]
      have hMHM : Mᴴ * M = Matrix.diagonal (Complex.ofReal ∘ fun _ : Unit ↦ (1 : ℝ)) := by
        ext ⟨⟩ ⟨⟩
        simp only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Matrix.diagonal_apply, Function.comp_apply, ↓reduceIte, Complex.ofReal_one]
        have hterm : ∀ i : d₂, star (φ₁ i) * φ₁ i = ((‖φ₁ i‖ ^ 2 : ℝ) : ℂ) := by
          intro i; rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        simp_rw [hterm, ← Complex.ofReal_sum, hφ₁, Complex.ofReal_one]
      have hD : (Matrix.diagonal (Complex.ofReal ∘ fun _ : Unit ↦ (1 : ℝ))).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext _; simp
      have hcp := charpoly_mul_conjTranspose_eq M
      rw [hMMH, hMHM] at hcp
      unfold vonNeumannEntropy DensityOp.eigvals
      have hsum : ∑ i : d₂, Real.negMulLog (σ₁.isHermitian.eigenvalues i) = ∑ _ : Unit, Real.negMulLog (1 : ℝ) := by
        trans ∑ u : Unit, Real.negMulLog (hD.eigenvalues u)
        · exact spectral_sum_eq_of_charpoly_mul_X_pow σ₁.isHermitian hD hcp (by simp [Real.negMulLog])
        · exact spectral_sum_diagonal (fun _ ↦ 1) hD (by simp [Real.negMulLog])
      rw [hsum]; simp [Real.negMulLog]
    have hL0 := (lemma_4_1_gram_dephasing ρ₀ ρ₁ φ₀ φ₁ hφ₀ hφ₁).2.2.1
    rw [vonNeumannEntropy_tensor, vonNeumannEntropy_tensor, hSσ₀, hSσ₁, add_zero, add_zero,
      hL.2.1, hS_deph, hL0]
    ring
  -- Step 3: Apply Eq. (2.7) and Theorem 1.3
  have hvar_eq : (CQChannel.varCombine W₁ W₂).condEntropy = dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₀ ρ₁) := by
    have h27 := varCombine_condEntropy W₁ W₂
    linarith
  have hC0 : dephaseCoherence 0 le_rfl (by norm_num) (gramState ρ₀ ρ₁) = W₁.condEntropy := by
    have h4 := (lemma_4_1_gram_dephasing ρ₀ ρ₁ φ₀ φ₁ hφ₀ hφ₁).2.2.2
    have h0 : (dephaseState 0 le_rfl (by norm_num) (gramState ρ₀ ρ₁)).mat = (gramState ρ₀ ρ₁).mat :=
      dephaseState_zero (gramState ρ₀ ρ₁)
    unfold dephaseCoherence CQChannel.condEntropy at *
    rw [vonNeumannEntropy_eq_of_mat_eq h0]
    exact h4
  have hsdpi := theorem_1_3_dephasing_sdpi (gramState ρ₀ ρ₁) hp0 hp1
  rw [hC0] at hsdpi
  have hvar_le : (CQChannel.varCombine W₁ W₂).condEntropy ≤
      1 - gc (1 - W₁.condEntropy) (1 - W₂.condEntropy) := by
    rw [hvar_eq]
    unfold gc
    rw [hinv₂]
    exact hsdpi
  have hcons := entropy_conservation W₁ W₂
  have hchk_ge : W₁.condEntropy + W₂.condEntropy - 1 + gc (1 - W₁.condEntropy) (1 - W₂.condEntropy) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy := by linarith
  have hgq_le : gq W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy := by
    unfold gq
    exact le_trans (le_max_right _ _) hchk_ge
  exact ⟨hvar_le, hchk_ge, hgq_le⟩

/-! ### Part 2: Theorem 1.2(a) — Classical Hybrid Bound -/

/-- `H(W₁ ⊠ BSC(q)) ≥ gc(H(W₁), h₂(q))` for every `W₁` and `q ∈ [0, 1/2]`. -/
theorem theorem_1_2a_bsc (W₁ : CQChannel d₁) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    gc W₁.condEntropy (h2 q) ≤ (CQChannel.checkCombine W₁ (bscChannel q hq0 (by linarith))).condEntropy := by
  set W₂ := bscChannel q hq0 (by linarith)
  set Wp := pureChannel (1 - 2 * q) (by linarith) (by linarith)
  -- Show `H(W₁.dual ⊠ W₂.dual) = H(W₁.dual ⊠ Wp)` because `W₂.dual` is a 50-50 direct sum of
  -- `Wp` and `Wp` with flipped inputs (unitarily equivalent to `Wp`)!
  -- Even simpler: compute `W₂.dual` explicitly on `Bool × Bool`:
  -- On `d = false` block: `|v₀⟩ = (√(1-q), √q)`, `|v₀'⟩ = (√(1-q), -√q)` (overlap `1 - 2q`)
  -- On `d = true` block: `|v₁⟩ = (√q, √(1-q))`, `|v₁'⟩ = (√q, -√(1-q))` (overlap `-(1-2q)`)
  have hWp_pure : Wp.IsPureState := by
    refine ⟨fun b ↦ if b = false then (Real.sqrt ((1 + (1 - 2 * q)) / 2) : ℂ) else (Real.sqrt ((1 - (1 - 2 * q)) / 2) : ℂ),
            fun b ↦ if b = false then (Real.sqrt ((1 + (1 - 2 * q)) / 2) : ℂ) else -(Real.sqrt ((1 - (1 - 2 * q)) / 2) : ℂ),
            ?_, ?_, rfl, rfl⟩
    · rw [Fintype.sum_bool]
      simp only [↓reduceIte, Bool.true_eq_false, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (by linarith : 0 ≤ (1 + (1 - 2 * q)) / 2),
        Real.sq_sqrt (by linarith : 0 ≤ (1 - (1 - 2 * q)) / 2)]
      ring
    · rw [Fintype.sum_bool]
      simp only [↓reduceIte, Bool.true_eq_false, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (by linarith : 0 ≤ (1 + (1 - 2 * q)) / 2),
        Real.sq_sqrt (by linarith : 0 ≤ (1 - (1 - 2 * q)) / 2)]
      ring
  have hdual_eq : (CQChannel.checkCombine W₁.dual W₂.dual).condEntropy =
      (CQChannel.checkCombine W₁.dual Wp).condEntropy := by
    -- Reorder `(Bool × d₁) × (Bool × Bool)` to `Bool × ((Bool × d₁) × Bool)` via the classical flag `c : Bool`
    -- (the second coordinate of `W₂.dual`'s `Bool × Bool`), where `c = false` gives `W₁.dual ⊠ Wp`
    -- and `c = true` gives `W₁.dual ⊠ Wp` conjugated by `I ⊗ X` (swapping `Bool` of `Wp`)!
    have hsqrt_bsc : ∀ (b : Bool) (i j : Bool),
        (W₂.out b).sqrtMat i j =
          if i = j then
            ((Real.sqrt (if i = b then 1 - q else q) : ℝ) : ℂ)
          else 0 := by
      intro b i j
      -- `(W₂.out b).mat = diagonal (if i = b then 1-q else q)`, so its unique PSD square root is diagonal!
      set D : Matrix Bool Bool ℂ := Matrix.diagonal (fun k ↦ ((Real.sqrt (if k = b then 1 - q else q) : ℝ) : ℂ))
      have hDD : D * D = (W₂.out b).mat := by
        ext x y
        simp only [D, W₂, bscChannel, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
        split_ifs with hxy
        · subst hxy
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by split_ifs <;> linarith)]
          cases b <;> cases x <;> simp
        · rfl
      have hD_psd : D.PosSemidef := by
        rw [Matrix.posSemidef_diagonal_iff]; intro k; exact_mod_cast Real.sqrt_nonneg _
      have huniq : (W₂.out b).sqrtMat = D := by
        -- Both `S = (W₂.out b).sqrtMat` and `D` are PSD with `S^2 = D^2 = (W₂.out b).mat`
        -- Since `D` is diagonal with entries `≥ 0`, check on basis vectors `e_k`:
        -- `S^2 e_k = d_k^2 e_k`, so `S e_k = d_k e_k`!
        have hcol : ∀ k : Bool, (W₂.out b).sqrtMat.mulVec (Pi.single k 1) = D.mulVec (Pi.single k 1) := by
          intro k
          set S := (W₂.out b).sqrtMat
          set U := ((W₂.out b).eigUnitary : Matrix Bool Bool ℂ)
          set lam := (W₂.out b).eigvals
          have hS_def : S = U * Matrix.diagonal (fun r ↦ (Real.sqrt (lam r) : ℂ)) * star U := rfl
          set dk := Real.sqrt (if k = b then 1 - q else q)
          have hmat_k : (W₂.out b).mat.mulVec (Pi.single k 1) = ((dk ^ 2 : ℝ) : ℂ) • Pi.single k 1 := by
            ext r
            rw [← hDD, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
            simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, dk]
            by_cases hr : r = k
            · subst hr; simp [sq, ← Complex.ofReal_mul]
            · simp [hr]
          set y : Bool → ℂ := (star U).mulVec (Pi.single k 1)
          have hU_mul : U * star U = 1 := Unitary.coe_mul_star_self (W₂.out b).eigUnitary
          have hU_smul : star U * U = 1 := Unitary.coe_star_mul_self (W₂.out b).eigUnitary
          have hy_coord : ∀ r : Bool, lam r ≠ dk ^ 2 → y r = 0 := by
            intro r hr
            have hspec : (W₂.out b).mat = U * Matrix.diagonal (Complex.ofReal ∘ lam) * star U := by
              simpa [U, lam, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
                Unitary.conjStarAlgAut_apply] using (W₂.out b).isHermitian.spectral_theorem
            have h1 := congr_arg (fun v ↦ ((star U).mulVec v) r) hmat_k
            have hL : ((star U).mulVec ((W₂.out b).mat.mulVec (Pi.single k 1))) r = (lam r : ℂ) * y r := by
              conv_lhs => rw [hspec]
              rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc (star U), ← Matrix.mul_assoc (star U),
                hU_smul, Matrix.one_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]; rfl
            rw [hL, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h1
            have hsub : ((lam r : ℂ) - ((dk ^ 2 : ℝ) : ℂ)) * y r = 0 := by linear_combination h1
            have hne : (lam r : ℂ) - ((dk ^ 2 : ℝ) : ℂ) ≠ 0 := by
              rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.mpr hr
            exact (mul_eq_zero.mp hsub).resolve_left hne
          have hS_k : S.mulVec (Pi.single k 1) = (dk : ℂ) • Pi.single k 1 := by
            rw [hS_def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
            have hdiag : Matrix.diagonal (fun r ↦ (Real.sqrt (lam r) : ℂ)) *ᵥ y = (dk : ℂ) • y := by
              ext r; rw [Matrix.mulVec_diagonal]; simp only [Pi.smul_apply, smul_eq_mul]
              by_cases hr : lam r = dk ^ 2
              · rw [hr, Real.sqrt_sq (Real.sqrt_nonneg _)]
              · rw [hy_coord r hr, mul_zero, mul_zero]
            rw [hdiag, Matrix.mulVec_smul, show U.mulVec y = Pi.single k 1 by
              simp only [y, Matrix.mulVec_mulVec, hU_mul, Matrix.one_mulVec]]
          ext r
          rw [hS_k, Matrix.mulVec_diagonal]
          simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, dk]
          by_cases hr : r = k
          · subst hr; simp
          · simp [hr]
        ext i j
        have h := congr_fun (hcol j) i
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
      rw [huniq]; simp [D, Matrix.diagonal_apply]
    -- Show `W₂.dual` has block-diagonal outputs in `Bool` (the 2nd coordinate of `Bool × Bool`):
    -- block `c = false` is `½ Wp.out b`, block `c = true` is `½ (X * Wp.out b * X)`!
    let X : Matrix.unitaryGroup Bool ℂ :=
      ⟨Matrix.of fun a b ↦ if a = !b then 1 else 0, by
        rw [Matrix.mem_unitaryGroup_iff']; ext a b
        simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply, Fintype.sum_bool]
        cases a <;> cases b <;> simp⟩
    let U_swap : Matrix.unitaryGroup ((Bool × d₁) × (Bool × Bool)) ℂ :=
      ⟨Matrix.of fun p q ↦
          if p.1 = q.1 ∧ p.2.2 = q.2.2 ∧ (if p.2.2 = false then p.2.1 = q.2.1 else p.2.1 = !q.2.1) then 1 else 0, by
        rw [Matrix.mem_unitaryGroup_iff']
        ext ⟨p₁, a₁, c₁⟩ ⟨p₂, a₂, c₂⟩
        simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type]
        by_cases h1 : p₁ = p₂
        · subst h1
          simp only [Prod.mk.injEq, true_and]
          rw [Finset.sum_eq_single p₁]
          · simp only [true_and, Fintype.sum_bool]
            cases c₁ <;> cases c₂ <;> cases a₁ <;> cases a₂ <;> simp
          · intro x _ hx; simp [hx, Ne.symm hx]
          · intro h; exact absurd (Finset.mem_univ _) h
        · simp only [Prod.mk.injEq, h1, false_and, ↓reduceIte]
          apply Finset.sum_eq_zero; intro x _
          by_cases hx : x = p₁
          · subst hx; simp [h1, Ne.symm h1]
          · simp [hx]⟩
    -- Conjugate `W₁.dual ⊠ W₂.dual` by `U_swap` and reindex to `Bool × ((Bool × d₁) × Bool)` to get
    -- `DensityOp.midpoint (ketBraBool false ⊗ (W₁.dual ⊠ Wp).out u) (ketBraBool true ⊗ (W₁.dual ⊠ Wp).out u)`!
    have hS_iso : ∀ (u : Bool),
        vonNeumannEntropy ((CQChannel.checkCombine W₁.dual W₂.dual).out u) =
          1 + vonNeumannEntropy ((CQChannel.checkCombine W₁.dual Wp).out u) := by
      intro u
      have hblk := vonNeumannEntropy_block_midpoint
        ((CQChannel.checkCombine W₁.dual Wp).out u) ((CQChannel.checkCombine W₁.dual Wp).out u)
      have hmid_same : vonNeumannEntropy (DensityOp.midpoint
          (DensityOp.tensor (CQChannel.ketBraBool false) ((CQChannel.checkCombine W₁.dual Wp).out u))
          (DensityOp.tensor (CQChannel.ketBraBool true) ((CQChannel.checkCombine W₁.dual Wp).out u))) =
          1 + vonNeumannEntropy ((CQChannel.checkCombine W₁.dual Wp).out u) := by linarith
      rw [← hmid_same]
      -- Permute `((Bool × d₁) × (Bool × Bool)) ≃ (Bool × ((Bool × d₁) × Bool))` with `c = true` flipping `a`
      let e : ((Bool × d₁) × (Bool × Bool)) ≃ (Bool × ((Bool × d₁) × Bool)) :=
        { toFun := fun ⟨p₁, a, c⟩ ↦ (c, (p₁, if c = false then a else !a))
          invFun := fun ⟨c, p₁, a⟩ ↦ (p₁, if c = false then a else !a, c)
          left_inv := fun ⟨p₁, a, c⟩ ↦ by cases c <;> simp
          right_inv := fun ⟨c, p₁, a⟩ ↦ by cases c <;> simp }
      let P : Matrix ((Bool × d₁) × (Bool × Bool)) (Bool × ((Bool × d₁) × Bool)) ℂ :=
        Matrix.of fun p q ↦ if e p = q then 1 else 0
      have hPHP : Pᴴ * P = 1 := by
        ext p q
        simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
        rw [Finset.sum_eq_single (e.symm p)]
        · simp [e.symm_apply_eq, eq_comm]
        · intro r _ hr; simp [show e r ≠ p from fun h ↦ hr (e.symm_apply_eq.mpr h.symm).symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      set B_tgt := DensityOp.midpoint
        (DensityOp.tensor (CQChannel.ketBraBool false) ((CQChannel.checkCombine W₁.dual Wp).out u))
        (DensityOp.tensor (CQChannel.ketBraBool true) ((CQChannel.checkCombine W₁.dual Wp).out u))
      have hmat : ((CQChannel.checkCombine W₁.dual W₂.dual).out u).mat = P * B_tgt.mat * Pᴴ := by
        ext ⟨p₁, a₁, c₁⟩ ⟨q₁, a₂, c₂⟩
        simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
        rw [Finset.sum_eq_single (e (q₁, a₂, c₂))]
        · rw [Finset.sum_eq_single (e (p₁, a₁, c₁))]
          · simp only [↓reduceIte, one_mul, star_one, mul_one, e, Equiv.coe_fn_mk]
            have hsq2 : ((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
              rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
                ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
              push_cast; ring
            have h1q : (1 + (1 - 2 * q)) / 2 = 1 - q := by ring
            have hq' : (1 - (1 - 2 * q)) / 2 = q := by ring
            simp only [B_tgt, CQChannel.checkCombine, CQChannel.dual, CQChannel.ketBraBool, Wp, pureChannel,
              pureState, gramState, gramFactor, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
              DensityOp.conjUnitary, pauliZTensorI, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
              Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.star_apply, Matrix.kroneckerMap_apply,
              Matrix.of_apply, Complex.real_smul, Fintype.sum_prod_type, Fintype.sum_bool, h1q, hq']
            simp_rw [hsqrt_bsc]
            cases u <;> cases c₁ <;> cases c₂ <;> cases a₁ <;> cases a₂ <;>
              (simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, Bool.not_false, Bool.not_true,
                and_self, and_true, and_false, true_and, false_and, mul_one, one_mul, mul_zero, zero_mul,
                add_zero, zero_add, mul_neg, neg_mul, neg_neg, star_mul', star_neg, star_one, star_zero,
                Complex.star_def, Complex.conj_ofReal];
               try ring;
               have hs : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
                 rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
                   Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; push_cast; ring
               ring_nf; try simp only [show ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) by rw [sq, hs]];
               push_cast; ring)
          · intro r _ hr; simp [Ne.symm hr]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro r _ hr; simp [Ne.symm hr]
        · intro h; exact absurd (Finset.mem_univ _) h
      unfold vonNeumannEntropy DensityOp.eigvals
      congr 1
      let M : Matrix ((Bool × d₁) × (Bool × Bool)) (Bool × ((Bool × d₁) × Bool)) ℂ := P * B_tgt.sqrtMat
      have hMMH : M * Mᴴ = ((CQChannel.checkCombine W₁.dual W₂.dual).out u).mat := by
        calc M * Mᴴ = P * (B_tgt.sqrtMat * B_tgt.sqrtMat) * Pᴴ := by
              simp only [M, Matrix.conjTranspose_mul, B_tgt.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
          _ = P * B_tgt.mat * Pᴴ := by rw [B_tgt.sqrtMat_mul_self]
          _ = _ := hmat.symm
      have hMHM : Mᴴ * M = B_tgt.mat := by
        calc Mᴴ * M = B_tgt.sqrtMat * ((Pᴴ * P) * B_tgt.sqrtMat) := by
              simp only [M, Matrix.conjTranspose_mul, B_tgt.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
          _ = B_tgt.mat := by rw [hPHP, Matrix.one_mul, B_tgt.sqrtMat_mul_self]
      have hcp := charpoly_mul_conjTranspose_eq M
      rw [hMMH, hMHM] at hcp
      exact spectral_sum_eq_of_charpoly_mul_X_pow
        ((CQChannel.checkCombine W₁.dual W₂.dual).out u).isHermitian B_tgt.isHermitian hcp
        (by simp [Real.negMulLog])
    have hS_mid : vonNeumannEntropy (DensityOp.midpoint
        ((CQChannel.checkCombine W₁.dual W₂.dual).out false)
        ((CQChannel.checkCombine W₁.dual W₂.dual).out true)) =
        1 + vonNeumannEntropy (DensityOp.midpoint
          ((CQChannel.checkCombine W₁.dual Wp).out false)
          ((CQChannel.checkCombine W₁.dual Wp).out true)) := by
      -- Same permutation `e` maps the midpoint to `½ |0⟩⟨0| ⊗ mid_Wp + ½ |1⟩⟨1| ⊗ mid_Wp`!
      have hblk := vonNeumannEntropy_block_midpoint
        (DensityOp.midpoint ((CQChannel.checkCombine W₁.dual Wp).out false) ((CQChannel.checkCombine W₁.dual Wp).out true))
        (DensityOp.midpoint ((CQChannel.checkCombine W₁.dual Wp).out false) ((CQChannel.checkCombine W₁.dual Wp).out true))
      have hmid_same : vonNeumannEntropy (DensityOp.midpoint
          (DensityOp.tensor (CQChannel.ketBraBool false)
            (DensityOp.midpoint ((CQChannel.checkCombine W₁.dual Wp).out false) ((CQChannel.checkCombine W₁.dual Wp).out true)))
          (DensityOp.tensor (CQChannel.ketBraBool true)
            (DensityOp.midpoint ((CQChannel.checkCombine W₁.dual Wp).out false) ((CQChannel.checkCombine W₁.dual Wp).out true)))) =
          1 + vonNeumannEntropy (DensityOp.midpoint
            ((CQChannel.checkCombine W₁.dual Wp).out false) ((CQChannel.checkCombine W₁.dual Wp).out true)) := by linarith
      rw [← hmid_same]
      let e : ((Bool × d₁) × (Bool × Bool)) ≃ (Bool × ((Bool × d₁) × Bool)) :=
        { toFun := fun ⟨p₁, a, c⟩ ↦ (c, (p₁, if c = false then a else !a))
          invFun := fun ⟨c, p₁, a⟩ ↦ (p₁, if c = false then a else !a, c)
          left_inv := fun ⟨p₁, a, c⟩ ↦ by cases c <;> simp
          right_inv := fun ⟨c, p₁, a⟩ ↦ by cases c <;> simp }
      let P : Matrix ((Bool × d₁) × (Bool × Bool)) (Bool × ((Bool × d₁) × Bool)) ℂ :=
        Matrix.of fun p q ↦ if e p = q then 1 else 0
      have hPHP : Pᴴ * P = 1 := by
        ext p q
        simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
        rw [Finset.sum_eq_single (e.symm p)]
        · simp [e.symm_apply_eq, eq_comm]
        · intro r _ hr; simp [show e r ≠ p from fun h ↦ hr (e.symm_apply_eq.mpr h.symm).symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      set B_tgt := DensityOp.midpoint
        (DensityOp.tensor (CQChannel.ketBraBool false)
          (DensityOp.midpoint ((CQChannel.checkCombine W₁.dual Wp).out false) ((CQChannel.checkCombine W₁.dual Wp).out true)))
        (DensityOp.tensor (CQChannel.ketBraBool true)
          (DensityOp.midpoint ((CQChannel.checkCombine W₁.dual Wp).out false) ((CQChannel.checkCombine W₁.dual Wp).out true)))
      -- Since `P * B_u * Pᴴ = out u` for `u ∈ {false, true}`, taking midpoint preserves `P * · * Pᴴ`!
      have hmat : (DensityOp.midpoint ((CQChannel.checkCombine W₁.dual W₂.dual).out false)
          ((CQChannel.checkCombine W₁.dual W₂.dual).out true)).mat = P * B_tgt.mat * Pᴴ := by
        ext ⟨p₁, a₁, c₁⟩ ⟨q₁, a₂, c₂⟩
        simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
        rw [Finset.sum_eq_single (e (q₁, a₂, c₂))]
        · rw [Finset.sum_eq_single (e (p₁, a₁, c₁))]
          · simp only [↓reduceIte, one_mul, star_one, mul_one, e, Equiv.coe_fn_mk]
            have h1q : (1 + (1 - 2 * q)) / 2 = 1 - q := by ring
            have hq' : (1 - (1 - 2 * q)) / 2 = q := by ring
            simp only [B_tgt, CQChannel.checkCombine, CQChannel.dual, CQChannel.ketBraBool, Wp, pureChannel,
              pureState, gramState, gramFactor, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
              DensityOp.conjUnitary, pauliZTensorI, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
              Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.star_apply, Matrix.kroneckerMap_apply,
              Matrix.of_apply, Complex.real_smul, Fintype.sum_prod_type, Fintype.sum_bool, h1q, hq']
            simp_rw [hsqrt_bsc]
            cases c₁ <;> cases c₂ <;> cases a₁ <;> cases a₂ <;>
              (simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, Bool.not_false, Bool.not_true,
                and_self, and_true, and_false, true_and, false_and, mul_one, one_mul, mul_zero, zero_mul,
                add_zero, zero_add, mul_neg, neg_mul, neg_neg, star_mul', star_neg, star_one, star_zero,
                Complex.star_def, Complex.conj_ofReal];
               try ring;
               have hs : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
                 rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
                   Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; push_cast; ring
               ring_nf; try simp only [show ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) by rw [sq, hs]];
               push_cast; ring)
          · intro r _ hr; simp [Ne.symm hr]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro r _ hr; simp [Ne.symm hr]
        · intro h; exact absurd (Finset.mem_univ _) h
      unfold vonNeumannEntropy DensityOp.eigvals
      congr 1
      let M : Matrix ((Bool × d₁) × (Bool × Bool)) (Bool × ((Bool × d₁) × Bool)) ℂ := P * B_tgt.sqrtMat
      have hMMH : M * Mᴴ = (DensityOp.midpoint ((CQChannel.checkCombine W₁.dual W₂.dual).out false)
          ((CQChannel.checkCombine W₁.dual W₂.dual).out true)).mat := by
        calc M * Mᴴ = P * (B_tgt.sqrtMat * B_tgt.sqrtMat) * Pᴴ := by
              simp only [M, Matrix.conjTranspose_mul, B_tgt.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
          _ = P * B_tgt.mat * Pᴴ := by rw [B_tgt.sqrtMat_mul_self]
          _ = _ := hmat.symm
      have hMHM : Mᴴ * M = B_tgt.mat := by
        calc Mᴴ * M = B_tgt.sqrtMat * ((Pᴴ * P) * B_tgt.sqrtMat) := by
              simp only [M, Matrix.conjTranspose_mul, B_tgt.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
          _ = B_tgt.mat := by rw [hPHP, Matrix.one_mul, B_tgt.sqrtMat_mul_self]
      have hcp := charpoly_mul_conjTranspose_eq M
      rw [hMMH, hMHM] at hcp
      exact spectral_sum_eq_of_charpoly_mul_X_pow
        (DensityOp.midpoint _ _).isHermitian B_tgt.isHermitian hcp (by simp [Real.negMulLog])
    unfold CQChannel.condEntropy qjs
    rw [hS_iso false, hS_iso true, hS_mid]
    ring
  have h29 := checkCombine_duality W₁ W₂
  have hpure := (theorem_1_2a_pure W₁.dual Wp hWp_pure).2.1
  have hD1 := prop_2_2_D1 W₁
  have hH₂ : W₂.condEntropy = h2 q := condEntropy_bscChannel q hq0 (by linarith)
  have hHp : Wp.condEntropy = 1 - h2 q := by
    rw [condEntropy_pureChannel]
    have harg : (1 - (1 - 2 * q)) / 2 = q := by ring
    rw [harg]
  have h1m1 : 1 - W₁.dual.condEntropy = W₁.condEntropy := by linarith
  have h1m2 : 1 - Wp.condEntropy = h2 q := by linarith
  rw [h1m1, h1m2] at hpure
  linarith

/-- Simultaneous unitary diagonalization of two commuting Hermitian matrices `A, B`. -/
lemma simultaneous_diagonalization {A B : Matrix d d ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hcomm : A * B = B * A) :
    ∃ (U : Matrix.unitaryGroup d ℂ) (α β : d → ℝ),
      star (U : Matrix d d ℂ) * A * (U : Matrix d d ℂ) = Matrix.diagonal (Complex.ofReal ∘ α) ∧
      star (U : Matrix d d ℂ) * B * (U : Matrix d d ℂ) = Matrix.diagonal (Complex.ofReal ∘ β) := by
  set U₀ := hA.eigenvectorUnitary
  set α := hA.eigenvalues
  set B' : Matrix d d ℂ := star (U₀ : Matrix d d ℂ) * B * (U₀ : Matrix d d ℂ)
  have hU₀_mul : (U₀ : Matrix d d ℂ) * star (U₀ : Matrix d d ℂ) = 1 := Unitary.coe_mul_star_self U₀
  have hU₀_star : star (U₀ : Matrix d d ℂ) * (U₀ : Matrix d d ℂ) = 1 := Unitary.coe_star_mul_self U₀
  have hA_diag : star (U₀ : Matrix d d ℂ) * A * (U₀ : Matrix d d ℂ) = Matrix.diagonal (Complex.ofReal ∘ α) := by
    have hspec : A = (U₀ : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ α) * star (U₀ : Matrix d d ℂ) := by
      simpa [U₀, α, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
    conv_lhs => rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (U₀ : Matrix d d ℂ)) (U₀ : Matrix d d ℂ), hU₀_star,
      Matrix.one_mul, hU₀_star, Matrix.mul_one]
  have hB'_herm : B'.IsHermitian := by
    simp only [B', Matrix.IsHermitian, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
      star_star, hB.eq, Matrix.mul_assoc]
  have hB'_block : ∀ i j : d, α i ≠ α j → B' i j = 0 := by
    intro i j hij
    have hcomm' : Matrix.diagonal (Complex.ofReal ∘ α) * B' = B' * Matrix.diagonal (Complex.ofReal ∘ α) := by
      rw [← hA_diag]
      simp only [B', Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U₀ : Matrix d d ℂ) (star (U₀ : Matrix d d ℂ)), hU₀_mul,
        Matrix.one_mul, ← Matrix.mul_assoc A B, hcomm, Matrix.mul_assoc B A]
      conv_rhs =>
        rw [← Matrix.mul_assoc (U₀ : Matrix d d ℂ) (star (U₀ : Matrix d d ℂ)), hU₀_mul,
          Matrix.one_mul]
    have hij_eq := congr_fun (congr_fun hcomm' i) j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Function.comp_apply] at hij_eq
    have hsub : ((α i : ℂ) - (α j : ℂ)) * B' i j = 0 := by linear_combination hij_eq
    have hne : (α i : ℂ) - (α j : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.mpr hij
    exact (mul_eq_zero.mp hsub).resolve_left hne
  -- Diagonalize each eigenspace block `S c = {i : d // α i = c}` independently
  let Bblk : ∀ c : ℝ, Matrix {i : d // α i = c} {i : d // α i = c} ℂ :=
    fun c ↦ Matrix.of fun i j ↦ B' i.1 j.1
  have hBblk_herm : ∀ c : ℝ, (Bblk c).IsHermitian := by
    intro c; ext i j
    have hh := congr_fun (congr_fun hB'_herm.eq i.1) j.1
    simpa [Bblk, Matrix.conjTranspose_apply] using hh
  let V : Matrix d d ℂ := Matrix.of fun i j ↦
    if h : α i = α j then
      ((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) ⟨i, rfl⟩ ⟨j, h.symm⟩
    else 0
  have hV_unit : V ∈ Matrix.unitaryGroup d ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply]
    by_cases hij : α i = α j
    · have hsum : (∑ k : d, star (V k i) * V k j) =
          ∑ k : {k : d // α k = α i},
            star (((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) k ⟨i, rfl⟩) *
              (((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) k ⟨j, hij.symm⟩) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : d ↦ α k = α i)]
        have hzero : ∑ k ∈ Finset.univ.filter (fun k : d ↦ ¬ α k = α i), star (V k i) * V k j = 0 := by
          apply Finset.sum_eq_zero; intro k hk
          have hne : α k ≠ α i := (Finset.mem_filter.mp hk).2
          simp [V, hne]
        rw [hzero, add_zero]
        refine Finset.sum_bij (fun k hk ↦ (⟨k, (Finset.mem_filter.mp hk).2⟩ : {k : d // α k = α i}))
          (fun _ _ ↦ Finset.mem_univ _)
          (fun _ _ _ _ h ↦ congr_arg Subtype.val h)
          (fun b _ ↦ ⟨b.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, Subtype.ext rfl⟩)
          (fun k hk ↦ ?_)
        have hki : α k = α i := (Finset.mem_filter.mp hk).2
        have hkj : α k = α j := hki.trans hij
        simp only [V, Matrix.of_apply, hki, hkj, ↓reduceDIte]
        cases hki; rfl
      rw [hsum]
      have hu := congr_fun (congr_fun (Unitary.coe_star_mul_self (hBblk_herm (α i)).eigenvectorUnitary)
        ⟨i, rfl⟩) ⟨j, hij.symm⟩
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at hu
      rw [hu]
      by_cases h : i = j
      · subst h; simp
      · have hne : (⟨i, rfl⟩ : {k : d // α k = α i}) ≠ ⟨j, hij.symm⟩ := fun heq ↦ h (congr_arg Subtype.val heq)
        simp [h, hne]
    · have hne_ij : i ≠ j := fun h ↦ hij (by rw [h])
      simp only [hne_ij, ↓reduceIte]
      apply Finset.sum_eq_zero; intro k _
      by_cases hk : α k = α i
      · have hk' : α k ≠ α j := by rw [hk]; exact hij
        simp [V, hk, hk']
      · simp [V, hk]
  let V_u : Matrix.unitaryGroup d ℂ := ⟨V, hV_unit⟩
  let U : Matrix.unitaryGroup d ℂ := U₀ * V_u
  let β : d → ℝ := fun i ↦ (hBblk_herm (α i)).eigenvalues ⟨i, rfl⟩
  refine ⟨U, α, β, ?_, ?_⟩
  · -- `Uᴴ A U = Vᴴ (U₀ᴴ A U₀) V = Vᴴ diag(α) V = diag(α)`
    have hcomm_V : Matrix.diagonal (Complex.ofReal ∘ α) * V = V * Matrix.diagonal (Complex.ofReal ∘ α) := by
      ext i j
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Function.comp_apply, V, Matrix.of_apply]
      split_ifs with h
      · rw [h]
      · simp
    calc star (U : Matrix d d ℂ) * A * (U : Matrix d d ℂ)
        = star V * (star (U₀ : Matrix d d ℂ) * A * (U₀ : Matrix d d ℂ)) * V := by
            simp only [U, V_u, Unitary.coe_mul, star_mul, Matrix.mul_assoc]
      _ = star V * (Matrix.diagonal (Complex.ofReal ∘ α) * V) := by rw [hA_diag, Matrix.mul_assoc]
      _ = (star V * V) * Matrix.diagonal (Complex.ofReal ∘ α) := by rw [hcomm_V, Matrix.mul_assoc]
      _ = Matrix.diagonal (Complex.ofReal ∘ α) := by
            have hVs : star V * V = 1 := Unitary.coe_star_mul_self V_u
            rw [hVs, Matrix.one_mul]
  · -- `Uᴴ B U = Vᴴ B' V = diag(β)`
    have hVB'V : star V * B' * V = Matrix.diagonal (Complex.ofReal ∘ β) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply, Function.comp_apply]
      by_cases hij : α i = α j
      · -- Restrict both sums `k, l` to `{x : d // α x = α i}`
        have hsum : (∑ l : d, (∑ k : d, star (V k i) * B' k l) * V l j) =
            ∑ l : {x : d // α x = α i},
              (∑ k : {x : d // α x = α i},
                star (((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) k ⟨i, rfl⟩) *
                  Bblk (α i) k l) *
                (((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) l ⟨j, hij.symm⟩) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : d ↦ α l = α i)]
          have hzero_l : ∑ l ∈ Finset.univ.filter (fun l : d ↦ ¬ α l = α i),
              (∑ k : d, star (V k i) * B' k l) * V l j = 0 := by
            apply Finset.sum_eq_zero; intro l hl
            have hne : α l ≠ α j := by
              intro h; exact (Finset.mem_filter.mp hl).2 (h.trans hij.symm)
            simp [V, hne]
          rw [hzero_l, add_zero]
          refine Finset.sum_bij (fun l hl ↦ (⟨l, (Finset.mem_filter.mp hl).2⟩ : {x : d // α x = α i}))
            (fun _ _ ↦ Finset.mem_univ _)
            (fun _ _ _ _ h ↦ congr_arg Subtype.val h)
            (fun b _ ↦ ⟨b.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, Subtype.ext rfl⟩)
            (fun l hl ↦ ?_)
          have hli : α l = α i := (Finset.mem_filter.mp hl).2
          have hlj : α l = α j := hli.trans hij
          have hVl : V l j = ((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) ⟨l, hli⟩ ⟨j, hij.symm⟩ := by
            simp only [V, Matrix.of_apply, hlj, ↓reduceDIte]
            cases hli; rfl
          rw [hVl]
          congr 1
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : d ↦ α k = α i)]
          have hzero_k : ∑ k ∈ Finset.univ.filter (fun k : d ↦ ¬ α k = α i),
              star (V k i) * B' k l = 0 := by
            apply Finset.sum_eq_zero; intro k hk
            have hne : α k ≠ α i := (Finset.mem_filter.mp hk).2
            simp [V, hne]
          rw [hzero_k, add_zero]
          refine Finset.sum_bij (fun k hk ↦ (⟨k, (Finset.mem_filter.mp hk).2⟩ : {x : d // α x = α i}))
            (fun _ _ ↦ Finset.mem_univ _)
            (fun _ _ _ _ h ↦ congr_arg Subtype.val h)
            (fun b _ ↦ ⟨b.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, Subtype.ext rfl⟩)
            (fun k hk ↦ ?_)
          have hki : α k = α i := (Finset.mem_filter.mp hk).2
          simp only [V, Bblk, Matrix.of_apply, hki, ↓reduceDIte]
          cases hki; rfl
        rw [hsum]
        have hdiag_blk : star ((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) * Bblk (α i) *
            ((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) =
            Matrix.diagonal (Complex.ofReal ∘ (hBblk_herm (α i)).eigenvalues) := by
          have hspec : Bblk (α i) = ((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) *
              Matrix.diagonal (Complex.ofReal ∘ (hBblk_herm (α i)).eigenvalues) *
              star ((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) := by
            simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using (hBblk_herm (α i)).spectral_theorem
          conv_lhs => rw [hspec]
          simp only [Matrix.mul_assoc]
          have hVstar : star ((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) *
              ((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) = 1 :=
            Unitary.coe_star_mul_self (hBblk_herm (α i)).eigenvectorUnitary
          rw [← Matrix.mul_assoc (star ((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ)),
            hVstar, Matrix.one_mul, hVstar, Matrix.mul_one]
        have hentry := congr_fun (congr_fun hdiag_blk ⟨i, rfl⟩) ⟨j, hij.symm⟩
        simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply, Function.comp_apply] at hentry
        rw [hentry]
        by_cases h : i = j
        · subst h; simp [β]
        · have hne : (⟨i, rfl⟩ : {x : d // α x = α i}) ≠ ⟨j, hij.symm⟩ := fun heq ↦ h (congr_arg Subtype.val heq)
          simp [h, hne]
      · have hne_ij : i ≠ j := fun h ↦ hij (by rw [h])
        simp only [hne_ij, ↓reduceIte]
        apply Finset.sum_eq_zero; intro l _
        by_cases hlj : α l = α j
        · have hsum_k : ∑ k : d, star (V k i) * B' k l = 0 := by
            apply Finset.sum_eq_zero; intro k _
            by_cases hki : α k = α i
            · have hkl : α k ≠ α l := by rw [hki, hlj]; exact hij
              rw [hB'_block k l hkl, mul_zero]
            · simp [V, hki]
          rw [hsum_k, zero_mul]
        · simp [V, hlj]
    calc star (U : Matrix d d ℂ) * B * (U : Matrix d d ℂ)
        = star V * B' * V := by simp only [U, V_u, B', Unitary.coe_mul, star_mul, Matrix.mul_assoc]
      _ = Matrix.diagonal (Complex.ofReal ∘ β) := hVB'V

/-- Block-diagonal von Neumann entropy: if `ρ : DensityOp (d₁ × d₂)` is block-diagonal in the
second register with `ρ.mat (i₁, y₁) (j₁, y₂) = if y₁ = y₂ then w y₁ • (τ y₁).mat i₁ j₁ else 0`,
then `S(ρ) = (∑ y, Real.negMulLog (w y)) / log 2 + ∑ y, w y * S(τ y)`. -/
private lemma vonNeumannEntropy_block_diag {w : d₂ → ℝ} (hw_nn : ∀ y, 0 ≤ w y)
    (τ : d₂ → DensityOp d₁) (ρ : DensityOp (d₁ × d₂))
    (hρ : ∀ i₁ j₁ y₁ y₂, ρ.mat (i₁, y₁) (j₁, y₂) =
      if y₁ = y₂ then ((w y₁ : ℝ) : ℂ) * (τ y₁).mat i₁ j₁ else 0) :
    vonNeumannEntropy ρ =
      (∑ y : d₂, Real.negMulLog (w y)) / Real.log 2 + ∑ y : d₂, w y * vonNeumannEntropy (τ y) := by
  -- Block-diagonal unitary `U = ⨁_y U_y` diagonalizes `ρ` with eigenvalues `w y * λ_{y, i}`
  let U : Matrix (d₁ × d₂) (d₁ × d₂) ℂ := Matrix.of fun p q ↦
    if p.2 = q.2 then ((τ p.2).eigUnitary : Matrix d₁ d₁ ℂ) p.1 q.1 else 0
  let lam : d₁ × d₂ → ℝ := fun p ↦ w p.2 * (τ p.2).eigvals p.1
  have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext p; simp
  have hU_star : star U * U = 1 := by
    ext ⟨i₁, y₁⟩ ⟨j₁, y₂⟩
    simp only [U, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type]
    by_cases hy : y₁ = y₂
    · subst hy
      rw [Finset.sum_eq_single y₁]
      · simp only [↓reduceIte, Prod.mk.injEq, and_true]
        have hu := congr_fun (congr_fun (Unitary.coe_star_mul_self (τ y₁).eigUnitary) i₁) j₁
        simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using hu
      · intro y _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [Prod.mk.injEq, hy, and_false, ↓reduceIte]
      apply Finset.sum_eq_zero; intro i _
      apply Finset.sum_eq_zero; intro y _
      by_cases h1 : y = y₁
      · subst h1; simp [hy]
      · simp [h1]
  have hρ_eq : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ lam) * star U := by
    ext ⟨i₁, y₁⟩ ⟨j₁, y₂⟩
    rw [hρ i₁ j₁ y₁ y₂]
    simp only [U, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.diagonal_apply,
      Function.comp_apply, Fintype.sum_prod_type, lam]
    by_cases hy : y₁ = y₂
    · subst hy
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single y₁]
      · simp only [↓reduceIte]
        have hspec := congr_fun (congr_fun (τ y₁).isHermitian.spectral_theorem i₁) j₁
        simp only [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply, Matrix.mul_apply,
          Matrix.diagonal_apply, Matrix.conjTranspose_apply, Function.comp_apply,
          ← Matrix.star_apply] at hspec
        rw [hspec]
        simp only [DensityOp.eigUnitary, DensityOp.eigvals, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.sum_eq_single k]
        · rw [Finset.sum_eq_single y₁]
          · rw [Finset.sum_eq_single k]
            · simp only [↓reduceIte, Complex.ofReal_mul]; ring
            · intro l _ hl; simp [Ne.symm hl]
            · intro h; exact absurd (Finset.mem_univ _) h
          · intro y _ hy; simp [Ne.symm hy]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro l _ hl; simp [Ne.symm hl]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro y _ hne
        apply Finset.sum_eq_zero; intro k _
        simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [hy, ↓reduceIte]
      apply Finset.sum_eq_zero; intro k _
      apply Finset.sum_eq_zero; intro y _
      by_cases h2 : y₂ = y
      · subst h2
        have hsum0 : ∑ l : d₁, ∑ z : d₂,
            (if y₁ = z then ((τ y₁).eigUnitary : Matrix d₁ d₁ ℂ) i₁ l else 0) *
              (if (l, z) = (k, y₂) then ((w y₂ * (τ y₂).eigvals k : ℝ) : ℂ) else 0) = 0 := by
          apply Finset.sum_eq_zero; intro l _
          apply Finset.sum_eq_zero; intro z _
          by_cases hz : y₁ = z
          · subst hz; simp [hy]
          · simp [hz]
        rw [hsum0, zero_mul]
      · simp [h2]
  have hcp : ρ.mat.charpoly = (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
    rw [hρ_eq, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU_star, Matrix.one_mul]
  unfold vonNeumannEntropy DensityOp.eigvals
  have hspec_sum : ∑ p : d₁ × d₂, Real.negMulLog (ρ.isHermitian.eigenvalues p) =
      ∑ p : d₁ × d₂, Real.negMulLog (lam p) := by
    trans ∑ p : d₁ × d₂, Real.negMulLog (hD_herm.eigenvalues p)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow ρ.isHermitian hD_herm (k := 0) (l := 0)
        (by rw [pow_zero, mul_one, mul_one, hcp]) (by simp [Real.negMulLog])
    · exact spectral_sum_diagonal lam hD_herm (by simp [Real.negMulLog])
  rw [hspec_sum, Fintype.sum_prod_type_right]
  have hinner : ∀ y : d₂, ∑ i : d₁, Real.negMulLog (w y * (τ y).eigvals i) =
      Real.negMulLog (w y) + w y * ∑ i : d₁, Real.negMulLog ((τ y).eigvals i) := by
    intro y
    simp_rw [Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      (τ y).sum_eigvals, one_mul]
    ring
  simp_rw [lam, hinner, Finset.sum_add_distrib, add_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl; intro y _
  ring

/-- **Theorem 1.2(a) (Classical Hybrid Q-MGL)**:
For any binary-input c-q channel `W₁` and any classical channel `W₂` (commuting outputs),
`H(W₁ ⊠ W₂) ≥ gc(H(W₁), H(W₂)) ≥ gq(H(W₁), H(W₂))`. -/
theorem theorem_1_2a_classical (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) (hW₂ : W₂.IsClassical) :
    gc W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy ∧
    gq W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy := by
  obtain ⟨U, p₀, p₁, hdiag₀, hdiag₁⟩ :=
    simultaneous_diagonalization (W₂.out false).isHermitian (W₂.out true).isHermitian hW₂
  have hU_mul : (U : Matrix d₂ d₂ ℂ) * star (U : Matrix d₂ d₂ ℂ) = 1 := Unitary.coe_mul_star_self U
  have hU_star : star (U : Matrix d₂ d₂ ℂ) * (U : Matrix d₂ d₂ ℂ) = 1 := Unitary.coe_star_mul_self U
  have hp₀_nn : ∀ y : d₂, 0 ≤ p₀ y := by
    intro y
    have hpsd : (Matrix.diagonal (Complex.ofReal ∘ p₀)).PosSemidef := by
      rw [← hdiag₀]
      simpa [Matrix.star_eq_conjTranspose] using (W₂.out false).posSemidef.conjTranspose_mul_mul_same (U : Matrix d₂ d₂ ℂ)
    exact_mod_cast (Matrix.posSemidef_diagonal_iff.mp hpsd) y
  have hp₁_nn : ∀ y : d₂, 0 ≤ p₁ y := by
    intro y
    have hpsd : (Matrix.diagonal (Complex.ofReal ∘ p₁)).PosSemidef := by
      rw [← hdiag₁]
      simpa [Matrix.star_eq_conjTranspose] using (W₂.out true).posSemidef.conjTranspose_mul_mul_same (U : Matrix d₂ d₂ ℂ)
    exact_mod_cast (Matrix.posSemidef_diagonal_iff.mp hpsd) y
  have hp₀_sum : ∑ y : d₂, p₀ y = 1 := by
    have htr : (Matrix.diagonal (Complex.ofReal ∘ p₀)).trace = 1 := by
      rw [← hdiag₀, Matrix.trace_mul_cycle, hU_mul, Matrix.one_mul, (W₂.out false).trace_one]
    have hre := congr_arg Complex.re htr
    simpa [Matrix.trace_diagonal, Function.comp_apply] using hre
  have hp₁_sum : ∑ y : d₂, p₁ y = 1 := by
    have htr : (Matrix.diagonal (Complex.ofReal ∘ p₁)).trace = 1 := by
      rw [← hdiag₁, Matrix.trace_mul_cycle, hU_mul, Matrix.one_mul, (W₂.out true).trace_one]
    have hre := congr_arg Complex.re htr
    simpa [Matrix.trace_diagonal, Function.comp_apply] using hre
  -- Replace `W₂` by the unitarily equivalent diagonal channel `W₂d`
  let W₂d : CQChannel d₂ :=
    { out := fun b ↦ DensityOp.conjUnitary (star U) (W₂.out b) }
  have hW₂d_0 : (W₂d.out false).mat = Matrix.diagonal (Complex.ofReal ∘ p₀) := by
    simpa [W₂d, DensityOp.conjUnitary, star_star] using hdiag₀
  have hW₂d_1 : (W₂d.out true).mat = Matrix.diagonal (Complex.ofReal ∘ p₁) := by
    simpa [W₂d, DensityOp.conjUnitary, star_star] using hdiag₁
  have hH₂_eq : W₂d.condEntropy = W₂.condEntropy :=
    condEntropy_eq_of_conjUnitary (star U) rfl rfl
  -- Tensor unitary `I ⊗ Uᴴ` shows `H(W₁ ⊠ W₂d) = H(W₁ ⊠ W₂)`
  let IU : Matrix.unitaryGroup (d₁ × d₂) ℂ :=
    ⟨Matrix.kroneckerMap (· * ·) (1 : Matrix d₁ d₁ ℂ) (star (U : Matrix d₂ d₂ ℂ)), by
      rw [Matrix.mem_unitaryGroup_iff']
      ext ⟨i₁, y₁⟩ ⟨j₁, y₂⟩
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
        Fintype.sum_prod_type, star_mul', star_ite, star_one, star_zero, ite_mul, zero_mul,
        mul_ite, mul_zero, one_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      by_cases hi : i₁ = j₁
      · subst hi
        simp only [↓reduceIte, Prod.mk.injEq, true_and]
        have hu := congr_fun (congr_fun hU_mul y₁) y₂
        simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using hu
      · simp [hi]⟩
  have hchk_eq : (CQChannel.checkCombine W₁ W₂d).condEntropy = (CQChannel.checkCombine W₁ W₂).condEntropy := by
    apply condEntropy_eq_of_conjUnitary IU
    · ext ⟨i₁, y₁⟩ ⟨j₁, y₂⟩
      simp only [CQChannel.checkCombine, W₂d, DensityOp.conjUnitary, DensityOp.midpoint, DensityOp.mix,
        DensityOp.tensor, IU, Bool.not_false, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.star_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Complex.real_smul,
        Fintype.sum_prod_type, star_mul', star_ite, star_one, star_zero, ite_mul, zero_mul,
        mul_ite, mul_zero, one_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        star_star, Finset.mul_sum, Finset.sum_mul]
      simp_rw [Finset.sum_add_distrib]
      congr 1 <;> (apply Finset.sum_congr rfl; intro z _; apply Finset.sum_congr rfl; intro w _; ring)
    · ext ⟨i₁, y₁⟩ ⟨j₁, y₂⟩
      simp only [CQChannel.checkCombine, W₂d, DensityOp.conjUnitary, DensityOp.midpoint, DensityOp.mix,
        DensityOp.tensor, IU, Bool.not_true, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.star_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Complex.real_smul,
        Fintype.sum_prod_type, star_mul', star_ite, star_one, star_zero, ite_mul, zero_mul,
        mul_ite, mul_zero, one_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        star_star, Finset.mul_sum, Finset.sum_mul]
      simp_rw [Finset.sum_add_distrib]
      congr 1 <;> (apply Finset.sum_congr rfl; intro z _; apply Finset.sum_congr rfl; intro w _; ring)
  -- Posterior weights `w y = (p₀ y + p₁ y) / 2` and crossover probabilities `q y ∈ [0, 1/2]`
  let w : d₂ → ℝ := fun y ↦ (p₀ y + p₁ y) / 2
  have hw_nn : ∀ y : d₂, 0 ≤ w y := fun y ↦ by dsimp [w]; linarith [hp₀_nn y, hp₁_nn y]
  have hw_sum : ∑ y : d₂, w y = 1 := by
    simp only [w, ← Finset.sum_div, Finset.sum_add_distrib, hp₀_sum, hp₁_sum]; norm_num
  let q_raw : d₂ → ℝ := fun y ↦ if w y = 0 then 0 else p₁ y / (2 * w y)
  have hq_raw0 : ∀ y : d₂, 0 ≤ q_raw y := by
    intro y; dsimp [q_raw]; split_ifs with h
    · exact le_rfl
    · exact div_nonneg (hp₁_nn y) (by linarith [hw_nn y])
  have hq_raw1 : ∀ y : d₂, q_raw y ≤ 1 := by
    intro y; dsimp [q_raw]; split_ifs with h
    · norm_num
    · have hw_pos : 0 < w y := lt_of_le_of_ne (hw_nn y) (Ne.symm h)
      rw [div_le_one (by linarith)]
      dsimp [w]; linarith [hp₀_nn y]
  -- Define `q y = min (q_raw y) (1 - q_raw y) ∈ [0, 1/2]` so `h2 (q y) = h2 (q_raw y)`
  let q : d₂ → ℝ := fun y ↦ min (q_raw y) (1 - q_raw y)
  have hq0 : ∀ y : d₂, 0 ≤ q y := fun y ↦ le_min (hq_raw0 y) (by linarith [hq_raw1 y])
  have hq1 : ∀ y : d₂, q y ≤ 1 / 2 := fun y ↦ by
    rcases le_or_gt (q_raw y) (1 / 2) with h | h
    · exact le_trans (min_le_left _ _) h
    · exact le_trans (min_le_right _ _) (by linarith)
  -- Express `W₂d.condEntropy = ∑ y, w y * h2 (q y)`
  have hH₂_decomp : W₂d.condEntropy = ∑ y : d₂, w y * h2 (q y) := by
    have hS_diag : ∀ (v : d₂ → ℝ) (ρ : DensityOp d₂), ρ.mat = Matrix.diagonal (Complex.ofReal ∘ v) →
        vonNeumannEntropy ρ = (∑ y : d₂, Real.negMulLog (v y)) / Real.log 2 := by
      intro v ρ hmat
      have hD : (Matrix.diagonal (Complex.ofReal ∘ v)).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext y; simp
      unfold vonNeumannEntropy DensityOp.eigvals
      congr 1
      trans ∑ y : d₂, Real.negMulLog (hD.eigenvalues y)
      · exact spectral_sum_eq_of_charpoly_mul_X_pow ρ.isHermitian hD (k := 0) (l := 0)
          (by rw [pow_zero, mul_one, mul_one, hmat]) (by simp [Real.negMulLog])
      · exact spectral_sum_diagonal v hD (by simp [Real.negMulLog])
    have hS0 := hS_diag p₀ (W₂d.out false) hW₂d_0
    have hS1 := hS_diag p₁ (W₂d.out true) hW₂d_1
    have hSm := hS_diag w (DensityOp.midpoint (W₂d.out false) (W₂d.out true)) (by
      ext i j
      simp only [DensityOp.midpoint, DensityOp.mix, hW₂d_0, hW₂d_1, Matrix.add_apply, Matrix.smul_apply,
        Matrix.diagonal_apply, Function.comp_apply, Complex.real_smul, w]
      split_ifs <;> simp <;> push_cast <;> ring)
    unfold CQChannel.condEntropy qjs
    rw [hS0, hS1, hSm]
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hterm : ∀ y : d₂,
        w y * h2 (q y) =
          w y - (Real.negMulLog (w y) - (Real.negMulLog (p₀ y) + Real.negMulLog (p₁ y)) / 2) / Real.log 2 := by
      intro y
      by_cases hw0 : w y = 0
      · have hp0 : p₀ y = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y, hp₁_nn y]
        have hp1 : p₁ y = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y, hp₁_nn y]
        simp [hw0, hp0, hp1, Real.negMulLog]
      · have hw_pos : 0 < w y := lt_of_le_of_ne (hw_nn y) (Ne.symm hw0)
        have hq_h2 : h2 (q y) = h2 (q_raw y) := by
          dsimp [q]; rcases le_total (q_raw y) (1 - q_raw y) with h | h
          · rw [min_eq_left h]
          · rw [min_eq_right h, h2_symm]
        rw [hq_h2, h2_eq_negMulLog]
        have hp1_eq : p₁ y = (2 * w y) * q_raw y := by
          dsimp [q_raw]; rw [if_neg hw0]; field_simp [ne_of_gt hw_pos]
        have hp0_eq : p₀ y = (2 * w y) * (1 - q_raw y) := by
          have : p₀ y + p₁ y = 2 * w y := by dsimp [w]; ring
          linarith
        rw [hp0_eq, hp1_eq, Real.negMulLog_mul, Real.negMulLog_mul, Real.negMulLog_mul]
        have h2w : Real.negMulLog (2 * w y) = -2 * w y * Real.log 2 + 2 * Real.negMulLog (w y) := by
          rw [Real.negMulLog_mul]; unfold Real.negMulLog; ring
        have hsum_q : (1 - q_raw y) + q_raw y = 1 := by ring
        field_simp [hlog2]
        nlinarith [h2w]
    calc 1 - ((∑ y : d₂, Real.negMulLog (w y)) / Real.log 2 -
            ((∑ y : d₂, Real.negMulLog (p₀ y)) / Real.log 2 + (∑ y : d₂, Real.negMulLog (p₁ y)) / Real.log 2) / 2)
        = ∑ y : d₂, (w y - (Real.negMulLog (w y) - (Real.negMulLog (p₀ y) + Real.negMulLog (p₁ y)) / 2) / Real.log 2) := by
            rw [Finset.sum_sub_distrib, hw_sum]
            congr 1
            simp_rw [sub_div, Finset.sum_sub_distrib, ← Finset.sum_div, div_div, ← add_div,
              Finset.sum_add_distrib]
            field_simp [hlog2]; ring
      _ = ∑ y : d₂, w y * h2 (q y) := by
            apply Finset.sum_congr rfl; intro y _; exact (hterm y).symm
  -- Express `(W₁ ⊠ W₂d).condEntropy = ∑ y, w y * (W₁ ⊠ BSC(q y)).condEntropy`
  have hchk_decomp : (CQChannel.checkCombine W₁ W₂d).condEntropy =
      ∑ y : d₂, w y * (CQChannel.checkCombine W₁ (bscChannel (q y) (hq0 y) (by linarith [hq1 y]))).condEntropy := by
    let τ₀ : d₂ → DensityOp d₁ := fun y ↦ DensityOp.mix (q_raw y) (hq_raw0 y) (hq_raw1 y) (W₁.out false) (W₁.out true)
    let τ₁ : d₂ → DensityOp d₁ := fun y ↦ DensityOp.mix (q_raw y) (hq_raw0 y) (hq_raw1 y) (W₁.out true) (W₁.out false)
    let τm : d₂ → DensityOp d₁ := fun y ↦ DensityOp.midpoint (τ₀ y) (τ₁ y)
    have hS0 := vonNeumannEntropy_block_diag hw_nn τ₀ ((CQChannel.checkCombine W₁ W₂d).out false) (by
      intro i₁ j₁ y₁ y₂
      simp only [CQChannel.checkCombine, Bool.not_false, DensityOp.midpoint, DensityOp.mix,
        DensityOp.tensor, hW₂d_0, hW₂d_1, Matrix.add_apply, Matrix.smul_apply,
        Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Function.comp_apply, Complex.real_smul, τ₀]
      split_ifs with hy
      · subst hy
        by_cases hw0 : w y₁ = 0
        · have hp0 : p₀ y₁ = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y₁, hp₁_nn y₁]
          have hp1 : p₁ y₁ = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y₁, hp₁_nn y₁]
          simp [hw0, hp0, hp1]
        · have hp1_eq : p₁ y₁ = 2 * w y₁ * q_raw y₁ := by
            dsimp [q_raw]; rw [if_neg hw0]; field_simp [hw0]
          have hp0_eq : p₀ y₁ = 2 * w y₁ * (1 - q_raw y₁) := by
            have : p₀ y₁ + p₁ y₁ = 2 * w y₁ := by dsimp [w]; ring
            linarith
          rw [hp0_eq, hp1_eq]; push_cast; ring
      · simp)
    have hS1 := vonNeumannEntropy_block_diag hw_nn τ₁ ((CQChannel.checkCombine W₁ W₂d).out true) (by
      intro i₁ j₁ y₁ y₂
      simp only [CQChannel.checkCombine, Bool.not_true, DensityOp.midpoint, DensityOp.mix,
        DensityOp.tensor, hW₂d_0, hW₂d_1, Matrix.add_apply, Matrix.smul_apply,
        Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Function.comp_apply, Complex.real_smul, τ₁]
      split_ifs with hy
      · subst hy
        by_cases hw0 : w y₁ = 0
        · have hp0 : p₀ y₁ = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y₁, hp₁_nn y₁]
          have hp1 : p₁ y₁ = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y₁, hp₁_nn y₁]
          simp [hw0, hp0, hp1]
        · have hp1_eq : p₁ y₁ = 2 * w y₁ * q_raw y₁ := by
            dsimp [q_raw]; rw [if_neg hw0]; field_simp [hw0]
          have hp0_eq : p₀ y₁ = 2 * w y₁ * (1 - q_raw y₁) := by
            have : p₀ y₁ + p₁ y₁ = 2 * w y₁ := by dsimp [w]; ring
            linarith
          rw [hp0_eq, hp1_eq]; push_cast; ring
      · simp)
    have hSm := vonNeumannEntropy_block_diag hw_nn τm
      (DensityOp.midpoint ((CQChannel.checkCombine W₁ W₂d).out false) ((CQChannel.checkCombine W₁ W₂d).out true)) (by
      intro i₁ j₁ y₁ y₂
      simp only [CQChannel.checkCombine, Bool.not_false, Bool.not_true, DensityOp.midpoint, DensityOp.mix,
        DensityOp.tensor, hW₂d_0, hW₂d_1, Matrix.add_apply, Matrix.smul_apply,
        Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Function.comp_apply, Complex.real_smul, τm, τ₀, τ₁]
      split_ifs with hy
      · subst hy
        by_cases hw0 : w y₁ = 0
        · have hp0 : p₀ y₁ = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y₁, hp₁_nn y₁]
          have hp1 : p₁ y₁ = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y₁, hp₁_nn y₁]
          simp [hw0, hp0, hp1]
        · have hp1_eq : p₁ y₁ = 2 * w y₁ * q_raw y₁ := by
            dsimp [q_raw]; rw [if_neg hw0]; field_simp [hw0]
          have hp0_eq : p₀ y₁ = 2 * w y₁ * (1 - q_raw y₁) := by
            have : p₀ y₁ + p₁ y₁ = 2 * w y₁ := by dsimp [w]; ring
            linarith
          rw [hp0_eq, hp1_eq]; push_cast; ring
      · simp)
    -- Show `1 - qjs (τ₀ y) (τ₁ y) = (W₁ ⊠ BSC(q y)).condEntropy`
    have hblk_bsc : ∀ y : d₂,
        1 - (vonNeumannEntropy (τm y) - (vonNeumannEntropy (τ₀ y) + vonNeumannEntropy (τ₁ y)) / 2) =
          (CQChannel.checkCombine W₁ (bscChannel (q y) (hq0 y) (by linarith [hq1 y]))).condEntropy := by
      intro y
      -- `(W₁ ⊠ BSC(q y))` is block-diagonal over `Bool` with weights `1/2, 1/2` and blocks `(τ₀', τ₁')`
      let qy := q y
      let σ₀' := DensityOp.mix qy (hq0 y) (by linarith [hq1 y]) (W₁.out false) (W₁.out true)
      let σ₁' := DensityOp.mix qy (hq0 y) (by linarith [hq1 y]) (W₁.out true) (W₁.out false)
      have hb0 := vonNeumannEntropy_block_diag (w := fun _ : Bool ↦ (1 / 2 : ℝ)) (fun _ ↦ by norm_num)
        (fun b ↦ if b = false then σ₀' else σ₁')
        ((CQChannel.checkCombine W₁ (bscChannel qy (hq0 y) (by linarith [hq1 y]))).out false) (by
        intro i₁ j₁ b₁ b₂
        simp only [CQChannel.checkCombine, bscChannel, Bool.not_false, DensityOp.midpoint, DensityOp.mix,
          DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
          Matrix.diagonal_apply, Complex.real_smul, σ₀', σ₁']
        cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring)
      have hb1 := vonNeumannEntropy_block_diag (w := fun _ : Bool ↦ (1 / 2 : ℝ)) (fun _ ↦ by norm_num)
        (fun b ↦ if b = false then σ₁' else σ₀')
        ((CQChannel.checkCombine W₁ (bscChannel qy (hq0 y) (by linarith [hq1 y]))).out true) (by
        intro i₁ j₁ b₁ b₂
        simp only [CQChannel.checkCombine, bscChannel, Bool.not_true, DensityOp.midpoint, DensityOp.mix,
          DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
          Matrix.diagonal_apply, Complex.real_smul, σ₀', σ₁']
        cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring)
      have hbm := vonNeumannEntropy_block_diag (w := fun _ : Bool ↦ (1 / 2 : ℝ)) (fun _ ↦ by norm_num)
        (fun _ ↦ DensityOp.midpoint σ₀' σ₁')
        (DensityOp.midpoint ((CQChannel.checkCombine W₁ (bscChannel qy (hq0 y) (by linarith [hq1 y]))).out false)
          ((CQChannel.checkCombine W₁ (bscChannel qy (hq0 y) (by linarith [hq1 y]))).out true)) (by
        intro i₁ j₁ b₁ b₂
        simp only [CQChannel.checkCombine, bscChannel, Bool.not_false, Bool.not_true, DensityOp.midpoint,
          DensityOp.mix, DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
          Matrix.diagonal_apply, Complex.real_smul, σ₀', σ₁']
        cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring)
      have hpair : vonNeumannEntropy (τ₀ y) + vonNeumannEntropy (τ₁ y) =
          vonNeumannEntropy σ₀' + vonNeumannEntropy σ₁' ∧
          vonNeumannEntropy (τm y) = vonNeumannEntropy (DensityOp.midpoint σ₀' σ₁') := by
        rcases le_total (q_raw y) (1 - q_raw y) with h | h
        · have hq_eq : qy = q_raw y := min_eq_left h
          have h0 : (τ₀ y).mat = σ₀'.mat := by simp [τ₀, σ₀', DensityOp.mix, hq_eq]
          have h1 : (τ₁ y).mat = σ₁'.mat := by simp [τ₁, σ₁', DensityOp.mix, hq_eq]
          have hm : (τm y).mat = (DensityOp.midpoint σ₀' σ₁').mat := by
            simp [τm, DensityOp.midpoint, DensityOp.mix, h0, h1]
          exact ⟨by rw [vonNeumannEntropy_eq_of_mat_eq h0, vonNeumannEntropy_eq_of_mat_eq h1],
                 vonNeumannEntropy_eq_of_mat_eq hm⟩
        · have hq_eq : qy = 1 - q_raw y := min_eq_right h
          have h0 : (τ₀ y).mat = σ₁'.mat := by
            ext i j; simp only [τ₀, σ₁', DensityOp.mix, Matrix.add_apply, Matrix.smul_apply,
              Complex.real_smul, hq_eq]; push_cast; ring
          have h1 : (τ₁ y).mat = σ₀'.mat := by
            ext i j; simp only [τ₁, σ₀', DensityOp.mix, Matrix.add_apply, Matrix.smul_apply,
              Complex.real_smul, hq_eq]; push_cast; ring
          have hm : (τm y).mat = (DensityOp.midpoint σ₀' σ₁').mat := by
            ext i j; simp only [τm, DensityOp.midpoint, DensityOp.mix, h0, h1, Matrix.add_apply,
              Matrix.smul_apply, Complex.real_smul]; ring
          exact ⟨by rw [vonNeumannEntropy_eq_of_mat_eq h0, vonNeumannEntropy_eq_of_mat_eq h1, add_comm],
                 vonNeumannEntropy_eq_of_mat_eq hm⟩
      unfold CQChannel.condEntropy qjs
      rw [hb0, hb1, hbm]
      simp only [Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false]
      linarith [hpair.1, hpair.2]
    unfold CQChannel.condEntropy qjs
    rw [hS0, hS1, hSm]
    calc 1 - (((∑ y : d₂, Real.negMulLog (w y)) / Real.log 2 + ∑ y : d₂, w y * vonNeumannEntropy (τm y)) -
            (((∑ y : d₂, Real.negMulLog (w y)) / Real.log 2 + ∑ y : d₂, w y * vonNeumannEntropy (τ₀ y)) +
             ((∑ y : d₂, Real.negMulLog (w y)) / Real.log 2 + ∑ y : d₂, w y * vonNeumannEntropy (τ₁ y))) / 2)
        = ∑ y : d₂, w y * (1 - (vonNeumannEntropy (τm y) - (vonNeumannEntropy (τ₀ y) + vonNeumannEntropy (τ₁ y)) / 2)) := by
            have h1 : (1 : ℝ) = ∑ y : d₂, w y := hw_sum.symm
            conv_lhs => rw [h1]
            simp only [mul_sub, mul_one, Finset.sum_sub_distrib, mul_div_assoc, ← Finset.sum_div,
              mul_add, Finset.sum_add_distrib]
            ring
      _ = ∑ y : d₂, w y * (CQChannel.checkCombine W₁ (bscChannel (q y) (hq0 y) (by linarith [hq1 y]))).condEntropy := by
            apply Finset.sum_congr rfl; intro y _; rw [hblk_bsc y]
  -- Apply `theorem_1_2a_bsc` term-by-term and Jensen's inequality via `convexOn_gc`!
  have hH₁_mem := condEntropy_mem_Icc W₁
  have hconv := convexOn_gc hH₁_mem.1 hH₁_mem.2
  have hgc_le : gc W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy := by
    rw [← hH₂_eq, ← hchk_eq, hH₂_decomp, hchk_decomp]
    have hjensen : gc W₁.condEntropy (∑ y : d₂, w y * h2 (q y)) ≤
        ∑ y : d₂, w y * gc W₁.condEntropy (h2 (q y)) := by
      have h := hconv.map_sum_le (t := Finset.univ) (w := w) (p := fun y ↦ h2 (q y))
        (fun y _ ↦ hw_nn y) hw_sum (fun y _ ↦ h2_mem_Icc (hq0 y) (by linarith [hq1 y]))
      simpa [smul_eq_mul] using h
    refine le_trans hjensen ?_
    apply Finset.sum_le_sum; intro y _
    exact mul_le_mul_of_nonneg_left (theorem_1_2a_bsc W₁ (hq0 y) (hq1 y)) (hw_nn y)
  have hH₂_mem := condEntropy_mem_Icc W₂
  exact ⟨hgc_le, le_trans (gq_le_gc hH₁_mem.1 hH₁_mem.2 hH₂_mem.1 hH₂_mem.2) hgc_le⟩

/-! ### Part 3: Proposition 4.2 — Four-Branch Purification Bound -/

/-- Helper: Branch 1 of Proposition 4.2 for arbitrary `W₁, W₂`:
`H(W₁ ⊠ W₂) ≥ H(W₁) + Δ(1 - H(W₁), 1 - 2^(H(W₂) - 1))`. -/
private lemma prop_4_2_branch1 (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    W₁.condEntropy + deltaGap (1 - W₁.condEntropy) (1 - (2 : ℝ) ^ (W₂.condEntropy - 1)) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy := by
  -- Step 1: Uhlmann purification of `W₂.out false, W₂.out true` with overlap `F₂ = W₂.fidelityParam`
  obtain ⟨φ₀, φ₁, hφ₀, hφ₁, htr₀, htr₁, hov⟩ := uhlmann_purification (W₂.out false) (W₂.out true)
  let W₂p : CQChannel (d₂ × d₂) :=
    { out := fun b ↦ match b with | false => pureState φ₀ hφ₀ | true => pureState φ₁ hφ₁ }
  have hW₂p_pure : W₂p.IsPureState := ⟨φ₀, φ₁, hφ₀, hφ₁, rfl, rfl⟩
  -- Step 2: DPI via `partialTrace₂` on `(d₁ × d₂) × d₂ ≃ d₁ × (d₂ × d₂)` gives `H(W₁ ⊠ W₂) ≥ H(W₁ ⊠ W₂p)`
  have hdpi : (CQChannel.checkCombine W₁ W₂p).condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy := by
    let e : (d₁ × d₂) × d₂ ≃ d₁ × (d₂ × d₂) := Equiv.prodAssoc d₁ d₂ d₂
    let reidx : DensityOp (d₁ × (d₂ × d₂)) → DensityOp ((d₁ × d₂) × d₂) := fun ρ ↦
      { mat := Matrix.of fun p q ↦ ρ.mat (e p) (e q)
        posSemidef := by
          rw [Matrix.posSemidef_iff_dotProduct_mulVec]
          refine ⟨?_, fun x ↦ ?_⟩
          · ext p q
            have hh := congr_fun (congr_fun ρ.isHermitian.eq (e p)) (e q)
            simpa [Matrix.conjTranspose_apply] using hh
          · have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp ρ.posSemidef).2 (fun a ↦ x (e.symm a))
            have heq : star x ⬝ᵥ (Matrix.of fun p q ↦ ρ.mat (e p) (e q)).mulVec x =
                star (fun a ↦ x (e.symm a)) ⬝ᵥ ρ.mat.mulVec (fun a ↦ x (e.symm a)) := by
              simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.of_apply]
              rw [← e.sum_comp]
              apply Finset.sum_congr rfl; intro p _
              simp only [Equiv.symm_apply_apply]
              congr 1
              rw [← e.sum_comp]
              apply Finset.sum_congr rfl; intro q _
              simp only [Equiv.symm_apply_apply]
            rw [heq]; exact hq
        trace_one := by
          rw [← ρ.trace_one]
          simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
          exact e.sum_comp (fun a ↦ ρ.mat a a) }
    have hS_reidx : ∀ ρ : DensityOp (d₁ × (d₂ × d₂)), vonNeumannEntropy (reidx ρ) = vonNeumannEntropy ρ := by
      intro ρ
      let P : Matrix ((d₁ × d₂) × d₂) (d₁ × (d₂ × d₂)) ℂ := Matrix.of fun p q ↦ if e p = q then 1 else 0
      have hPHP : Pᴴ * P = 1 := by
        ext p q
        simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
        rw [Finset.sum_eq_single (e.symm p)]
        · simp [e.symm_apply_eq, eq_comm]
        · intro r _ hr; simp [show e r ≠ p from fun h ↦ hr (e.symm_apply_eq.mpr h.symm).symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hmat : (reidx ρ).mat = P * ρ.mat * Pᴴ := by
        ext p q
        simp only [reidx, P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
        rw [Finset.sum_eq_single (e q)]
        · rw [Finset.sum_eq_single (e p)]
          · simp
          · intro r _ hr; simp [Ne.symm hr]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro r _ hr; simp [Ne.symm hr]
        · intro h; exact absurd (Finset.mem_univ _) h
      unfold vonNeumannEntropy DensityOp.eigvals
      congr 1
      let M : Matrix ((d₁ × d₂) × d₂) (d₁ × (d₂ × d₂)) ℂ := P * ρ.sqrtMat
      have hMMH : M * Mᴴ = (reidx ρ).mat := by
        calc M * Mᴴ = P * (ρ.sqrtMat * ρ.sqrtMat) * Pᴴ := by
              simp only [M, Matrix.conjTranspose_mul, ρ.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
          _ = P * ρ.mat * Pᴴ := by rw [ρ.sqrtMat_mul_self]
          _ = (reidx ρ).mat := hmat.symm
      have hMHM : Mᴴ * M = ρ.mat := by
        calc Mᴴ * M = ρ.sqrtMat * ((Pᴴ * P) * ρ.sqrtMat) := by
              simp only [M, Matrix.conjTranspose_mul, ρ.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
          _ = ρ.mat := by rw [hPHP, Matrix.one_mul, ρ.sqrtMat_mul_self]
      have hcp := charpoly_mul_conjTranspose_eq M
      rw [hMMH, hMHM] at hcp
      exact spectral_sum_eq_of_charpoly_mul_X_pow (reidx ρ).isHermitian ρ.isHermitian hcp (by simp [Real.negMulLog])
    have hpt0 : (partialTrace₂ (reidx ((CQChannel.checkCombine W₁ W₂p).out false))).mat =
        ((CQChannel.checkCombine W₁ W₂).out false).mat := by
      ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
      simp only [partialTrace₂, reidx, CQChannel.checkCombine, W₂p, Bool.not_false, DensityOp.midpoint,
        DensityOp.mix, DensityOp.tensor, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.kroneckerMap_apply, Complex.real_smul, e, Equiv.prodAssoc_apply, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      have h0 : ∑ k : d₂, (pureState φ₀ hφ₀).mat (i₂, k) (j₂, k) = (W₂.out false).mat i₂ j₂ := by
        have := congr_fun (congr_fun htr₀ i₂) j₂; simpa [partialTrace₂] using this
      have h1 : ∑ k : d₂, (pureState φ₁ hφ₁).mat (i₂, k) (j₂, k) = (W₂.out true).mat i₂ j₂ := by
        have := congr_fun (congr_fun htr₁ i₂) j₂; simpa [partialTrace₂] using this
      rw [h0, h1]
    have hpt1 : (partialTrace₂ (reidx ((CQChannel.checkCombine W₁ W₂p).out true))).mat =
        ((CQChannel.checkCombine W₁ W₂).out true).mat := by
      ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
      simp only [partialTrace₂, reidx, CQChannel.checkCombine, W₂p, Bool.not_true, DensityOp.midpoint,
        DensityOp.mix, DensityOp.tensor, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.kroneckerMap_apply, Complex.real_smul, e, Equiv.prodAssoc_apply, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      have h0 : ∑ k : d₂, (pureState φ₀ hφ₀).mat (i₂, k) (j₂, k) = (W₂.out false).mat i₂ j₂ := by
        have := congr_fun (congr_fun htr₀ i₂) j₂; simpa [partialTrace₂] using this
      have h1 : ∑ k : d₂, (pureState φ₁ hφ₁).mat (i₂, k) (j₂, k) = (W₂.out true).mat i₂ j₂ := by
        have := congr_fun (congr_fun htr₁ i₂) j₂; simpa [partialTrace₂] using this
      rw [h0, h1]
    have hq_le := qjs_partialTrace₂_le
      (reidx ((CQChannel.checkCombine W₁ W₂p).out false))
      (reidx ((CQChannel.checkCombine W₁ W₂p).out true))
    have hq_eq1 : qjs (partialTrace₂ (reidx ((CQChannel.checkCombine W₁ W₂p).out false)))
        (partialTrace₂ (reidx ((CQChannel.checkCombine W₁ W₂p).out true))) =
        qjs ((CQChannel.checkCombine W₁ W₂).out false) ((CQChannel.checkCombine W₁ W₂).out true) := by
      unfold qjs
      have hm : (DensityOp.midpoint (partialTrace₂ (reidx ((CQChannel.checkCombine W₁ W₂p).out false)))
          (partialTrace₂ (reidx ((CQChannel.checkCombine W₁ W₂p).out true)))).mat =
          (DensityOp.midpoint ((CQChannel.checkCombine W₁ W₂).out false) ((CQChannel.checkCombine W₁ W₂).out true)).mat := by
        simp [DensityOp.midpoint, DensityOp.mix, hpt0, hpt1]
      rw [vonNeumannEntropy_eq_of_mat_eq hpt0, vonNeumannEntropy_eq_of_mat_eq hpt1,
        vonNeumannEntropy_eq_of_mat_eq hm]
    have hq_eq2 : qjs (reidx ((CQChannel.checkCombine W₁ W₂p).out false))
        (reidx ((CQChannel.checkCombine W₁ W₂p).out true)) =
        qjs ((CQChannel.checkCombine W₁ W₂p).out false) ((CQChannel.checkCombine W₁ W₂p).out true) := by
      unfold qjs
      have hm : (DensityOp.midpoint (reidx ((CQChannel.checkCombine W₁ W₂p).out false))
          (reidx ((CQChannel.checkCombine W₁ W₂p).out true))).mat =
          (reidx (DensityOp.midpoint ((CQChannel.checkCombine W₁ W₂p).out false)
            ((CQChannel.checkCombine W₁ W₂p).out true))).mat := by
        ext p q; simp [reidx, DensityOp.midpoint, DensityOp.mix]
      rw [vonNeumannEntropy_eq_of_mat_eq hm, hS_reidx, hS_reidx, hS_reidx]
    unfold CQChannel.condEntropy
    linarith
  -- Step 3: Apply `theorem_1_2a_pure W₁ W₂p` and `antitoneOn_deltaGap`
  have hpure := (theorem_1_2a_pure W₁ W₂p hW₂p_pure).2.1
  have hF2 : W₂.fidelityParam = ‖∑ i : d₂ × d₂, star (φ₀ i) * φ₁ i‖ := by
    unfold CQChannel.fidelityParam; exact hov.symm
  have hF2_nn : 0 ≤ W₂.fidelityParam := by rw [hF2]; exact norm_nonneg _
  have hF2_le1 : W₂.fidelityParam ≤ 1 := by
    have := (lemma_4_1_gram_dephasing (W₁.out false) (W₁.out true) φ₀ φ₁ hφ₀ hφ₁).1
    rw [hF2]; linarith
  have hH₂p : W₂p.condEntropy = 1 - h2 ((1 - W₂.fidelityParam) / 2) := by
    unfold CQChannel.condEntropy W₂p
    dsimp only
    rw [qjs_pureState φ₀ φ₁ hφ₀ hφ₁, ← hF2]
  have hinv_p : h2Inv (1 - W₂p.condEntropy) = (1 - W₂.fidelityParam) / 2 := by
    rw [hH₂p, sub_sub_cancel, h2Inv_h2 ⟨by linarith, by linarith⟩]
  have hdelta_eq : W₁.condEntropy + W₂p.condEntropy - 1 + gc (1 - W₁.condEntropy) (1 - W₂p.condEntropy) =
      W₁.condEntropy + deltaGap (1 - W₁.condEntropy) ((1 - W₂.fidelityParam) / 2) := by
    unfold deltaGap gc
    rw [hinv_p, hH₂p]
    ring
  -- Fidelity-entropy bound `W₂.condEntropy ≤ logb 2 (1 + F₂)` ⇒ `(1 - F₂)/2 ≤ 1 - 2^(H₂ - 1)`
  have hfid_ent := condEntropy_le_logb_one_add_fidelityParam W₂
  have hH₂_mem := condEntropy_mem_Icc W₂
  have h2pow_le : (2 : ℝ) ^ W₂.condEntropy ≤ 1 + W₂.fidelityParam := by
    have h1 : Real.logb 2 ((2 : ℝ) ^ W₂.condEntropy) ≤ Real.logb 2 (1 + W₂.fidelityParam) := by
      rwa [Real.logb_rpow (by norm_num) (by norm_num)]
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog_le : Real.log ((2 : ℝ) ^ W₂.condEntropy) ≤ Real.log (1 + W₂.fidelityParam) := by
      unfold Real.logb at h1
      exact (div_le_div_iff_of_pos_right hlog2_pos).mp h1
    exact (Real.log_le_log_iff (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)).mp hlog_le
  have hp_le : (1 - W₂.fidelityParam) / 2 ≤ 1 - (2 : ℝ) ^ (W₂.condEntropy - 1) := by
    have hpow : (2 : ℝ) ^ (W₂.condEntropy - 1) = (2 : ℝ) ^ W₂.condEntropy / 2 := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    linarith
  have h2pow_mem : 1 - (2 : ℝ) ^ (W₂.condEntropy - 1) ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    have h1 : (2 : ℝ) ^ (W₂.condEntropy - 1) ≤ (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hH₂_mem.2])
    have h2 : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (W₂.condEntropy - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hH₂_mem.1])
    rw [Real.rpow_zero] at h1
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_one] at h2
    exact ⟨by linarith, by linarith⟩
  have hH₁_mem := condEntropy_mem_Icc W₁
  have hanti := antitoneOn_deltaGap (u := 1 - W₁.condEntropy) (by linarith [hH₁_mem.2]) (by linarith [hH₁_mem.1])
    (show (1 - W₂.fidelityParam) / 2 ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨by linarith, by linarith⟩)
    h2pow_mem hp_le
  linarith

/-- **Proposition 4.2 (Four-Branch Purification Bound, Eq. 1.6)**:
For all independent binary-input c-q channels `W₁, W₂`,
`H(W₁ ⊠ W₂) ≥ max { H₁ + Δ(1 - H₁, 1 - 2^(H₂ - 1)), H₂ + Δ(1 - H₂, 1 - 2^(H₁ - 1)),
                    H₂ + Δ(H₁, 1 - 2^(-H₂)),        H₁ + Δ(H₂, 1 - 2^(-H₁)) }`. -/
theorem prop_4_2_four_branch (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    max (max (W₁.condEntropy + deltaGap (1 - W₁.condEntropy) (1 - (2 : ℝ) ^ (W₂.condEntropy - 1)))
             (W₂.condEntropy + deltaGap (1 - W₂.condEntropy) (1 - (2 : ℝ) ^ (W₁.condEntropy - 1))))
        (max (W₂.condEntropy + deltaGap W₁.condEntropy (1 - (2 : ℝ) ^ (-W₂.condEntropy)))
             (W₁.condEntropy + deltaGap W₂.condEntropy (1 - (2 : ℝ) ^ (-W₁.condEntropy)))) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy := by
  have hb1 := prop_4_2_branch1 W₁ W₂
  have hb2 : W₂.condEntropy + deltaGap (1 - W₂.condEntropy) (1 - (2 : ℝ) ^ (W₁.condEntropy - 1)) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy := by
    rw [condEntropy_checkCombine_comm]; exact prop_4_2_branch1 W₂ W₁
  have hD1_1 := prop_2_2_D1 W₁
  have hD1_2 := prop_2_2_D1 W₂
  have h29 := checkCombine_duality W₁ W₂
  have hb3 : W₂.condEntropy + deltaGap W₁.condEntropy (1 - (2 : ℝ) ^ (-W₂.condEntropy)) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy := by
    have h := prop_4_2_branch1 W₁.dual W₂.dual
    have h1 : 1 - W₁.dual.condEntropy = W₁.condEntropy := by linarith
    have h2 : W₂.dual.condEntropy - 1 = -W₂.condEntropy := by linarith
    rw [h1, h2] at h
    linarith
  have hb4 : W₁.condEntropy + deltaGap W₂.condEntropy (1 - (2 : ℝ) ^ (-W₁.condEntropy)) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy := by
    have h := prop_4_2_branch1 W₂.dual W₁.dual
    rw [condEntropy_checkCombine_comm] at h
    have h1 : 1 - W₂.dual.condEntropy = W₂.condEntropy := by linarith
    have h2 : W₁.dual.condEntropy - 1 = -W₁.condEntropy := by linarith
    rw [h1, h2] at h
    linarith
  exact max_le (max_le hb1 hb2) (max_le hb3 hb4)

/-! ### Part 4: Theorem 1.2(b) — Linear-Scaling Splitting & Potential Contraction -/

/-- **Theorem 1.2(b), Eq. (1.7) (Linear-Scaling Polarization Splitting)**:
For every binary-input c-q channel `W`,
`H(W⁻) - H(W) = H(W) - H(W⁺) ≥ θ₀ H(W)(1 - H(W))` where `θ₀ > 0.05673`. -/
theorem theorem_1_2b_linear_splitting (W : CQChannel d) :
    W.minusChannel.condEntropy - W.condEntropy = W.condEntropy - W.plusChannel.condEntropy ∧
    theta0 * W.condEntropy * (1 - W.condEntropy) ≤ W.minusChannel.condEntropy - W.condEntropy := by
  have hcons := entropy_conservation W W
  have heq : W.minusChannel.condEntropy - W.condEntropy = W.condEntropy - W.plusChannel.condEntropy := by
    unfold CQChannel.minusChannel CQChannel.plusChannel; linarith
  refine ⟨heq, ?_⟩
  have hH_mem := condEntropy_mem_Icc W
  have hfb := prop_4_2_four_branch W W
  have hb1 : W.condEntropy + deltaGap (1 - W.condEntropy) (1 - (2 : ℝ) ^ (W.condEntropy - 1)) ≤
      W.minusChannel.condEntropy :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hfb
  have hb3 : W.condEntropy + deltaGap W.condEntropy (1 - (2 : ℝ) ^ (-W.condEntropy)) ≤
      W.minusChannel.condEntropy :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hfb
  have hsc := prop_4_3_scalar hH_mem.1 hH_mem.2
  have hmax : max (deltaGap (1 - W.condEntropy) (1 - (2 : ℝ) ^ (W.condEntropy - 1)))
      (deltaGap W.condEntropy (1 - (2 : ℝ) ^ (-W.condEntropy))) ≤
      W.minusChannel.condEntropy - W.condEntropy :=
    max_le (by linarith) (by linarith)
  exact le_trans hsc hmax

/-- **Theorem 1.2(b), Eq. (1.9) (Uniform Potential Contraction)**:
For every binary-input c-q channel `W`,
`½ (T(W⁻) + T(W⁺)) ≤ Λ₀ T(W)` where `T(W) = √(H(W)(1 - H(W)))` and `Λ₀ = √(1 - θ₀²/4) < 1`. -/
theorem theorem_1_2b_potential_contraction (W : CQChannel d) :
    (W.minusChannel.potential + W.plusChannel.potential) / 2 ≤ Lambda0 * W.potential := by
  have hH := condEntropy_mem_Icc W
  have hHm := condEntropy_mem_Icc W.minusChannel
  have hHp := condEntropy_mem_Icc W.plusChannel
  have hsplit := theorem_1_2b_linear_splitting W
  unfold CQChannel.potential
  exact prop_4_4_potential_contraction_general hH.1 hH.2 hHm.1 hHm.2 hHp.1 hHp.2
    (by linarith [hsplit.1]) hsplit.2

end PolarCodes
