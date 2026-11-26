/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.ChannelDuality
import PolarCodes.DephasingSDPI
import PolarCodes.SplittingBounds

/-!
# Hybrid Quantum Mrs. Gerber's Lemma — Pure-State & BSC Branches (Theorem 1.2(a))

This module formalizes the pure-state and binary symmetric channel (BSC) branches of
Theorem 1.2(a) from Section 4 of the manuscript:
1. Unitary invariance, commutativity, and `[0, 1]` bounds for `CQChannel.condEntropy`.
2. **Theorem 1.2(a) — Pure-State Branch** (`theorem_1_2a_pure`): for arbitrary `W₁` and
   pure-state `W₂`, `H(W₁ ⊛ W₂) ≤ 1 - gc(1 - H₁, 1 - H₂)` and
   `H(W₁ ⊠ W₂) ≥ H₁ + H₂ - 1 + gc(1 - H₁, 1 - H₂) ≥ gq(H₁, H₂)`.
3. **BSC Branch** (`theorem_1_2a_bsc`): for arbitrary `W₁` and `BSC(q)`,
   `H(W₁ ⊠ BSC(q)) ≥ gc(H₁, h₂(q))`.
-/

open Matrix BigOperators Real Filter Topology Set
open scoped ComplexOrder

namespace PolarCodes

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-! ### Helper: Unitary Equivalence and Channel Entropy Bounds -/

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
    push_cast; ring)
  have h1 := hS_swap ((CQChannel.checkCombine W₁ W₂).out true) ((CQChannel.checkCombine W₂ W₁).out true) (by
    intro i₁ i₂ j₁ j₂
    simp only [CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Bool.not_true, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul]
    push_cast; ring)
  have hm := hS_swap (DensityOp.midpoint ((CQChannel.checkCombine W₁ W₂).out false) ((CQChannel.checkCombine W₁ W₂).out true))
    (DensityOp.midpoint ((CQChannel.checkCombine W₂ W₁).out false) ((CQChannel.checkCombine W₂ W₁).out true)) (by
    intro i₁ i₂ j₁ j₂
    simp only [CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Bool.not_false, Bool.not_true, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul]
    push_cast; ring)
  rw [h0, h1, hm]

/-- Cauchy–Schwarz upper bound `‖∑ i, star (φ₀ i) * φ₁ i‖ ≤ 1` for unit vectors `φ₀, φ₁`. -/
lemma norm_inner_le_one {ι : Type*} [Fintype ι] {φ₀ φ₁ : ι → ℂ}
    (hφ₀ : ∑ i, ‖φ₀ i‖ ^ 2 = 1) (hφ₁ : ∑ i, ‖φ₁ i‖ ^ 2 = 1) :
    ‖∑ i, star (φ₀ i) * φ₁ i‖ ≤ 1 := by
  calc ‖∑ i, star (φ₀ i) * φ₁ i‖
      ≤ ∑ i, ‖star (φ₀ i) * φ₁ i‖ := norm_sum_le _ _
    _ = ∑ i, ‖φ₀ i‖ * ‖φ₁ i‖ := by
        apply Finset.sum_congr rfl; intro i _; rw [norm_mul, norm_star]
    _ ≤ ∑ i, (‖φ₀ i‖ ^ 2 + ‖φ₁ i‖ ^ 2) / 2 := by
        apply Finset.sum_le_sum; intro i _; nlinarith [sq_nonneg (‖φ₀ i‖ - ‖φ₁ i‖)]
    _ = 1 := by rw [← Finset.sum_div, Finset.sum_add_distrib, hφ₀, hφ₁]; norm_num

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
        let W' : CQChannel d := CQChannel.mk fun b ↦ if b = false then DensityOp.mix ε hc.1 hc.2 ρ (maxMixedState d)
            else DensityOp.mix ε hc.1 hc.2 σ (maxMixedState d)
        have hW' : W'.condEntropy ≥ 0 := by
          have h5 := condEntropy_ge_one_sub_h2 W'
          have hfid_nn : 0 ≤ W'.fidelityParam := Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _
          have hfid_le1 : W'.fidelityParam ≤ 1 := by
            obtain ⟨ψ₀, ψ₁, hψ₀, hψ₁, _, _, hov⟩ := exists_uhlmann_purification (W'.out false) (W'.out true)
            unfold CQChannel.fidelityParam; rw [← hov]; exact norm_inner_le_one hψ₀ hψ₁
          have hh2 : h2 ((1 - W'.fidelityParam) / 2) ≤ 1 := h2_le_one ⟨by linarith, by linarith⟩
          linarith
        simpa [CQChannel.condEntropy, W'] using hW'
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
  have hf₂_le1 : f₂ ≤ 1 := norm_inner_le_one hφ₀ hφ₁
  set p := (1 - f₂) / 2
  have hp0 : 0 ≤ p := by dsimp only [p]; linarith
  have hp1 : p ≤ 1 / 2 := by dsimp only [p]; linarith
  have hH₂ : W₂.condEntropy = 1 - h2 p := by
    unfold CQChannel.condEntropy
    have hq_eq : qjs (W₂.out false) (W₂.out true) = qjs σ₀ σ₁ := by
      unfold qjs
      have hm : (DensityOp.midpoint (W₂.out false) (W₂.out true)).mat = (DensityOp.midpoint σ₀ σ₁).mat := by
        simp only [DensityOp.midpoint, DensityOp.mix, σ₀, σ₁, pureState, hmat₀, hmat₁]
      have hmat0' : (W₂.out false).mat = σ₀.mat := hmat₀
      have hmat1' : (W₂.out true).mat = σ₁.mat := hmat₁
      rw [vonNeumannEntropy_eq_of_mat_eq hm, vonNeumannEntropy_eq_of_mat_eq hmat0',
        vonNeumannEntropy_eq_of_mat_eq hmat1']
    rw [hq_eq, qjs_pureState φ₀ φ₁ hφ₀ hφ₁]
  have hinv₂ : h2Inv (1 - W₂.condEntropy) = p := by
    rw [hH₂, sub_sub_cancel, h2Inv_h2 ⟨hp0, hp1⟩]
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
      rw [vonNeumannEntropy_eq_of_mat_eq hm, vonNeumannEntropy_eq_of_mat_eq h0,
        vonNeumannEntropy_eq_of_mat_eq h1]
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
    rw [vonNeumannEntropy_tensor, vonNeumannEntropy_tensor, hSσ₀, hSσ₁, add_zero, add_zero,
      hL.1, hL.2.2.1]
    ring
  have hbranch1 : 1 - qjs (DensityOp.tensor ρ₁ (W₂.out false)) (DensityOp.tensor ρ₀ (W₂.out true)) =
      dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₀ ρ₁) := by
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
          · cases a <;> cases b <;> by_cases hij : i = j <;> simp [hij]
          · intro r _ hr; simp [Ne.symm hr]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro r _ hr; simp [hr]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hXZ_conj : (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
          (DensityOp.conjUnitary (pauliZTensorI d₁) (gramState ρ₀ ρ₁)).mat *
          star (XI : Matrix (Bool × d₁) (Bool × d₁) ℂ) =
          (DensityOp.conjUnitary (pauliZTensorI d₁) (gramState ρ₁ ρ₀)).mat := by
        simp only [DensityOp.conjUnitary]
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
          rw [hXZ, hst, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
        simpa only [Matrix.mul_assoc] using h1
      simp only [DensityOp.conjUnitary] at hXZ_conj
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
      rw [vonNeumannEntropy_eq_of_mat_eq hm, vonNeumannEntropy_eq_of_mat_eq h0,
        vonNeumannEntropy_eq_of_mat_eq h1]
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
      hL.1, hS_deph, hL0]
    ring
  have hvar_eq : (CQChannel.varCombine W₁ W₂).condEntropy = dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) (gramState ρ₀ ρ₁) := by
    have h27 := condEntropy_varCombine_eq W₁ W₂
    linarith
  have hC0 : dephaseCoherence 0 le_rfl (by norm_num) (gramState ρ₀ ρ₁) = W₁.condEntropy := by
    have h4 := (lemma_4_1_gram_dephasing ρ₀ ρ₁ φ₀ φ₁ hφ₀ hφ₁).2.2.2.1
    unfold dephaseCoherence CQChannel.condEntropy at *
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
    exact le_trans (min_le_right _ _) hchk_ge
  exact ⟨hvar_le, hchk_ge, hgq_le⟩

/-! ### Part 2: BSC Hybrid Bound -/

/-- `H(W₁ ⊠ BSC(q)) ≥ gc(H(W₁), h₂(q))` for every `W₁` and `q ∈ [0, 1/2]`. -/
theorem theorem_1_2a_bsc (W₁ : CQChannel d₁) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    gc W₁.condEntropy (h2 q) ≤ (CQChannel.checkCombine W₁ (bscChannel q hq0 (by linarith))).condEntropy := by
  set W₂ := bscChannel q hq0 (by linarith)
  set Wp := pureChannel (1 - 2 * q) (by linarith) (by linarith)
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
    have hsqrt_bsc : ∀ (b : Bool) (i j : Bool),
        (W₂.out b).sqrtMat i j =
          if i = j then
            ((Real.sqrt (if i = b then 1 - q else q) : ℝ) : ℂ)
          else 0 := by
      intro b i j
      set D : Matrix Bool Bool ℂ := Matrix.diagonal (fun k ↦ ((Real.sqrt (if k = b then 1 - q else q) : ℝ) : ℂ))
      have hDD : D * D = (W₂.out b).mat := by
        ext x y
        cases b <;> cases x <;> cases y <;>
          simp only [D, W₂, bscChannel, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
            ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true]
        all_goals (rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)])
      have huniq : (W₂.out b).sqrtMat = D := by
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
    have hW2dual : ∀ (b a₁ c₁ a₂ c₂ : Bool),
        (W₂.dual.out b).mat (a₁, c₁) (a₂, c₂) =
          if c₁ = c₂ then
            (1 / 2 : ℂ) * (Wp.out b).mat (if c₁ = false then a₁ else !a₁) (if c₂ = false then a₂ else !a₂)
          else 0 := by
      intro b a₁ c₁ a₂ c₂
      have h1q : (1 + (1 - 2 * q)) / 2 = 1 - q := by ring
      have hq' : (1 - (1 - 2 * q)) / 2 = q := by ring
      have hs : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
        rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
          Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        push_cast; ring
      have hs2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by rw [sq, hs]
      simp only [CQChannel.dual, Wp, pureChannel, pureState, gramState, gramFactor,
        DensityOp.conjUnitary, pauliZTensorI, h1q, hq']
      cases b <;> cases c₁ <;> cases c₂ <;> cases a₁ <;> cases a₂ <;>
        (simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
          Matrix.star_apply, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_bool,
          hsqrt_bsc, ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, Bool.not_false, Bool.not_true,
          Prod.mk.injEq, and_false, false_and, and_true, true_and,
          mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, mul_neg, neg_mul, neg_neg,
          star_mul', star_neg, star_one, star_zero, Complex.star_def,
          map_inv₀, map_zero, map_one, map_neg, Complex.conj_ofReal] <;>
         ring_nf <;> simp only [hs2] <;> ring)
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
            simp only [B_tgt, CQChannel.checkCombine, CQChannel.ketBraBool, DensityOp.midpoint,
              DensityOp.mix, DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply,
              Matrix.kroneckerMap_apply, Matrix.of_apply, Complex.real_smul]
            rw [hW2dual, hW2dual]
            cases c₁ <;> cases c₂ <;> simp <;> push_cast <;> ring
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
      have hmat : (DensityOp.midpoint ((CQChannel.checkCombine W₁.dual W₂.dual).out false)
          ((CQChannel.checkCombine W₁.dual W₂.dual).out true)).mat = P * B_tgt.mat * Pᴴ := by
        ext ⟨p₁, a₁, c₁⟩ ⟨q₁, a₂, c₂⟩
        simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
        rw [Finset.sum_eq_single (e (q₁, a₂, c₂))]
        · rw [Finset.sum_eq_single (e (p₁, a₁, c₁))]
          · simp only [↓reduceIte, one_mul, star_one, mul_one, e, Equiv.coe_fn_mk]
            simp only [B_tgt, CQChannel.checkCombine, CQChannel.ketBraBool, DensityOp.midpoint,
              DensityOp.mix, DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply,
              Matrix.kroneckerMap_apply, Matrix.of_apply, Complex.real_smul]
            rw [hW2dual, hW2dual]
            cases c₁ <;> cases c₂ <;> simp <;> push_cast <;> ring
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

end PolarCodes
