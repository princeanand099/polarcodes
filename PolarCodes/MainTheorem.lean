/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.MrsGerber
import PolarCodes.PolarizationFine

/-!
# Main Theorems: Polynomial-Blocklength Quantum Polar Codes (Theorem 1.1 & Corollary 5.5)

This module instantiates the three-stage polarization martingale engine
(`PolarCodes.Polarization`, `PolarCodes.PolarizationFine`) on Arıkan's concrete synthetic
binary-input c-q channel tree `W^{(b)}` (`polarChannelTree`), using:
- Entropy conservation (`entropy_conservation`),
- Uniform potential contraction (`theorem_1_2b_potential_contraction`),
- Fidelity–entropy bound `F(W) ≤ √(2 ln 2 · H(W))` (`fidelityParam_le_sqrt_condEntropy`),
- Synthetic channel Bhattacharyya evolution `F(W⁺) = F(W)²` and `F(W⁻) ≤ 2 F(W)`
  (`fidelityParam_plusChannel`, `fidelityParam_minusChannel_le`),

to establish the manuscript's main results:
- **Theorem 1.1** (`theorem_1_1_quantum_polar_poly_blocklength`): Polynomial-blocklength
  capacity-achieving quantum polarization with universal scaling exponent `μ` and sub-exponential
  fidelity decay `F(W_N^{(i)}) ≤ 2^{-200 N^{0.49047}}`.
- **Corollary 5.5** (`corollary_5_5_simultaneous_css_polarization`): Simultaneous amplitude/phase
  polarization for any pair `(W_A, W_P)` of binary-input c-q channels at polynomial blocklength.
-/

open BigOperators Real Finset Set

namespace PolarCodes

universe u

/-- Universe-polymorphic bundle of a finite-dimensional binary-input c-q channel, allowing
recursive construction of Arıkan's synthetic channel tree `W^{(b)}` across depths `t : ℕ`. -/
structure BundledCQChannel where
  dim : Type u
  fintype : Fintype dim
  decEq : DecidableEq dim
  ch : CQChannel dim

attribute [instance] BundledCQChannel.fintype BundledCQChannel.decEq

/-- Minus synthetic channel step `W ↦ W⁻ = W ⊠ W`. -/
noncomputable def BundledCQChannel.minus (S : BundledCQChannel.{u}) : BundledCQChannel.{u} :=
  ⟨S.dim × S.dim, inferInstance, inferInstance, S.ch.minusChannel⟩

/-- Plus synthetic channel step `W ↦ W⁺ = W ⊛ W`. -/
noncomputable def BundledCQChannel.plus (S : BundledCQChannel.{u}) : BundledCQChannel.{u} :=
  ⟨Bool × (S.dim × S.dim), inferInstance, inferInstance, S.ch.plusChannel⟩

/-- Recursive construction of Arıkan's depth-`t` synthetic channel `W^{(b)}` along branch path
`b : Fin t → Bool` (`false` = minus channel `W⁻`, `true` = plus channel `W⁺`). -/
noncomputable def polarChannelTree {d : Type u} [Fintype d] [DecidableEq d]
    (W : CQChannel d) : (t : ℕ) → (Fin t → Bool) → BundledCQChannel.{u}
  | 0, _ => ⟨d, inferInstance, inferInstance, W⟩
  | t + 1, b =>
      if b (Fin.last t) = false then
        (polarChannelTree W t (Fin.init b)).minus
      else
        (polarChannelTree W t (Fin.init b)).plus

lemma polarChannelTree_zero {d : Type u} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (b : Fin 0 → Bool) :
    polarChannelTree W 0 b = ⟨d, inferInstance, inferInstance, W⟩ := rfl

lemma polarChannelTree_snoc_false {d : Type u} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (t : ℕ) (b : Fin t → Bool) :
    polarChannelTree W (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) =
      (polarChannelTree W t b).minus := by
  simp [polarChannelTree, Fin.snoc_last, Fin.init_snoc]

lemma polarChannelTree_snoc_true {d : Type u} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (t : ℕ) (b : Fin t → Bool) :
    polarChannelTree W (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) =
      (polarChannelTree W t b).plus := by
  simp [polarChannelTree, Fin.snoc_last, Fin.init_snoc]

/-- Conditional entropy `H(W^{(b)})` of the depth-`t` synthetic channel along path `b`. -/
noncomputable def polarCondEntropy {d : Type u} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (t : ℕ) (b : Fin t → Bool) : ℝ :=
  (polarChannelTree W t b).ch.condEntropy

/-- Bhattacharyya / fidelity parameter `F(W^{(b)})` of the depth-`t` synthetic channel along `b`. -/
noncomputable def polarFidelity {d : Type u} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (t : ℕ) (b : Fin t → Bool) : ℝ :=
  (polarChannelTree W t b).ch.fidelityParam

lemma polarCondEntropy_snoc_false {d : Type u} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (t : ℕ) (b : Fin t → Bool) :
    polarCondEntropy W (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) =
      (polarChannelTree W t b).ch.minusChannel.condEntropy :=
  congrArg (fun S : BundledCQChannel.{u} ↦ S.ch.condEntropy) (polarChannelTree_snoc_false W t b)

lemma polarCondEntropy_snoc_true {d : Type u} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (t : ℕ) (b : Fin t → Bool) :
    polarCondEntropy W (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) =
      (polarChannelTree W t b).ch.plusChannel.condEntropy :=
  congrArg (fun S : BundledCQChannel.{u} ↦ S.ch.condEntropy) (polarChannelTree_snoc_true W t b)

lemma polarFidelity_snoc_false {d : Type u} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (t : ℕ) (b : Fin t → Bool) :
    polarFidelity W (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) =
      (polarChannelTree W t b).ch.minusChannel.fidelityParam :=
  congrArg (fun S : BundledCQChannel.{u} ↦ S.ch.fidelityParam) (polarChannelTree_snoc_false W t b)

lemma polarFidelity_snoc_true {d : Type u} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (t : ℕ) (b : Fin t → Bool) :
    polarFidelity W (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) =
      (polarChannelTree W t b).ch.plusChannel.fidelityParam :=
  congrArg (fun S : BundledCQChannel.{u} ↦ S.ch.fidelityParam) (polarChannelTree_snoc_true W t b)

/-- Fidelity parameter of any `CQChannel` lies in `[0, 1]`. -/
lemma fidelityParam_mem_Icc {d : Type*} [Fintype d] [DecidableEq d] (W : CQChannel d) :
    W.fidelityParam ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · unfold CQChannel.fidelityParam rootFidelity
    exact Finset.sum_nonneg fun i _ ↦ Real.sqrt_nonneg _
  · obtain ⟨φ₀, φ₁, hφ₀, hφ₁, _, _, hov⟩ := exists_uhlmann_purification (W.out false) (W.out true)
    unfold CQChannel.fidelityParam
    rw [← hov]
    exact norm_inner_le_one hφ₀ hφ₁

/-- Instantiation of `PolarProcess` for any finite-dimensional binary-input c-q channel `W`. -/
noncomputable def cqPolarProcess {d : Type u} [Fintype d] [DecidableEq d]
    (W : CQChannel d) : PolarProcess where
  H := polarCondEntropy W
  Z := polarFidelity W
  H_mem := fun t b ↦ condEntropy_mem_Icc (polarChannelTree W t b).ch
  Z_mem := fun t b ↦ fidelityParam_mem_Icc (polarChannelTree W t b).ch
  H_cons := fun t b ↦ by
    rw [polarCondEntropy_snoc_false, polarCondEntropy_snoc_true]
    have h := entropy_conservation (polarChannelTree W t b).ch (polarChannelTree W t b).ch
    unfold polarCondEntropy CQChannel.minusChannel CQChannel.plusChannel
    linarith
  T_contract := fun t b ↦ by
    rw [polarCondEntropy_snoc_false, polarCondEntropy_snoc_true]
    simpa [CQChannel.potential, polarCondEntropy] using
      theorem_1_2b_potential_contraction (polarChannelTree W t b).ch
  Z_le_sqrt_H := fun t b ↦
    fidelityParam_le_sqrt_condEntropy (polarChannelTree W t b).ch
  Z_plus := fun t b ↦ by
    rw [polarFidelity_snoc_true]
    exact fidelityParam_plusChannel (polarChannelTree W t b).ch
  Z_minus := fun t b ↦ by
    rw [polarFidelity_snoc_false]
    exact fidelityParam_minusChannel_le (polarChannelTree W t b).ch

lemma cqPolarProcess_symCap {d : Type u} [Fintype d] [DecidableEq d] (W : CQChannel d) :
    (cqPolarProcess W).symCap = W.symCapacity := by
  change 1 - W.condEntropy = W.symCapacity
  unfold CQChannel.condEntropy CQChannel.symCapacity
  ring

/-- **Theorem 1.1 (Polynomial-Blocklength Quantum Polarization)**:
There exist universal constants `μ > 0` and `C₀ > 0` such that for every finite-dimensional
binary-input c-q channel `W`, every gap `ε ∈ (0, 1)`, and every depth `n : ℕ` with blocklength
`N = 2^n ≥ C₀ (1 / ε)^μ`, the fraction of depth-`n` synthetic channels `W^{(b)}` satisfying
`F(W^{(b)}) ≤ 2^{-200 · N^{0.49047}}` is at least `I(W) - ε`. -/
theorem theorem_1_1_quantum_polar_poly_blocklength :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ {d : Type u} [Fintype d] [DecidableEq d] (W : CQChannel d)
        {ε : ℝ}, 0 < ε → ε < 1 →
        ∀ (n : ℕ), C₀ * (1 / ε) ^ μ ≤ (2 : ℝ) ^ n →
          W.symCapacity - ε ≤
            treeProb n (fun b ↦
              polarFidelity W n b ≤
                (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))) := by
  rcases polar_process_poly_blocklength with ⟨μ, C₀, hμ, hC₀, hpoly⟩
  refine ⟨μ, C₀, hμ, hC₀, ?_⟩
  intro d _ _ W ε hε0 hε1 n hn
  have h := hpoly (cqPolarProcess W) hε0 hε1 n hn
  rwa [cqPolarProcess_symCap] at h

/-- **Corollary 5.5 (Simultaneous Amplitude/Phase Polarization for CSS Quantum Polar Codes)**:
There exist universal constants `μ > 0` and `C₀ > 0` such that for any pair `(W_A, W_P)` of
finite-dimensional binary-input c-q channels, every `ε ∈ (0, 1)`, and every depth `n : ℕ` with
blocklength `N = 2^n ≥ C₀ (4 / ε)^μ`, the fraction of indices `b : Fin n → Bool` simultaneously
good for both `W_A` and `W_P` (both `F(W_A^{(b)}), F(W_P^{(b)}) ≤ 2^{-200 N^{0.49047}}`) is at
least `I(W_A) + I(W_P) - 1 - ε / 2`. -/
theorem corollary_5_5_simultaneous_css_polarization :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
        (W_A : CQChannel d₁) (W_P : CQChannel d₂)
        {ε : ℝ}, 0 < ε → ε < 1 →
        ∀ (n : ℕ), C₀ * (4 / ε) ^ μ ≤ (2 : ℝ) ^ n →
          W_A.symCapacity + W_P.symCapacity - 1 - ε / 2 ≤
            treeProb n (fun b ↦
              polarFidelity W_A n b ≤
                (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ)) ∧
              polarFidelity W_P n b ≤
                (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))) := by
  rcases polar_process_dual_pair_poly_blocklength with ⟨μ, C₀, hμ, hC₀, hdual⟩
  refine ⟨μ, C₀, hμ, hC₀, ?_⟩
  intro d₁ d₂ _ _ _ _ W_A W_P ε hε0 hε1 n hn
  have h := hdual (cqPolarProcess W_A) (cqPolarProcess W_P) hε0 hε1 n hn
  rwa [cqPolarProcess_symCap, cqPolarProcess_symCap] at h

end PolarCodes
