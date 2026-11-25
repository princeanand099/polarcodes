/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import PolarCodes

/-!
# Comparator Solution Module for `PolarCodes`

Proves every locked headline theorem in `Challenge.lean` by structural transport to the
complete, verified formalization in `PolarCodes`.
-/

namespace PolarCodesChallenge

private def toPolarDensityOp {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : DensityOp d) : PolarCodes.DensityOp d :=
  ⟨ρ.mat, ρ.posSemidef, ρ.trace_one⟩

private def toPolarCQChannel {d : Type*} [Fintype d] [DecidableEq d]
    (W : CQChannel d) : PolarCodes.CQChannel d :=
  ⟨fun b ↦ toPolarDensityOp (W.out b)⟩

private def toPolarBundled (S : BundledCQChannel) : PolarCodes.BundledCQChannel.{0} :=
  ⟨S.dim, S.fintype, S.decEq, toPolarCQChannel S.ch⟩

private lemma toPolarBundled_polarChannelTree {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) :
    ∀ (t : ℕ) (b : Fin t → Bool),
      toPolarBundled (polarChannelTree W t b) =
        PolarCodes.polarChannelTree (toPolarCQChannel W) t b
  | 0, _ => rfl
  | t + 1, b => by
      simp only [polarChannelTree, PolarCodes.polarChannelTree]
      split_ifs
      · rw [← toPolarBundled_polarChannelTree W t (Fin.init b)]; rfl
      · rw [← toPolarBundled_polarChannelTree W t (Fin.init b)]; rfl

private lemma polarFidelity_eq {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (t : ℕ) (b : Fin t → Bool) :
    polarFidelity W t b = PolarCodes.polarFidelity (toPolarCQChannel W) t b := by
  have h := congrArg (fun S : PolarCodes.BundledCQChannel.{0} ↦ S.ch.fidelityParam)
    (toPolarBundled_polarChannelTree W t b)
  exact h

private lemma treeProb_eq (n : ℕ) (P : (Fin n → Bool) → Prop) :
    treeProb n P = PolarCodes.treeProb n P := by
  classical
  rw [PolarCodes.treeProb_eq_avg]
  unfold treeProb PolarCodes.treeAvg
  congr 1
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : P b
  · simp [hb, PolarCodes.ind_pos]
  · simp [hb, PolarCodes.ind_neg]

/-- **Theorem 1.1 (Polynomial-Blocklength Quantum Polarization)**. -/
theorem theorem_1_1_quantum_polar_poly_blocklength :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ {d : Type} [Fintype d] [DecidableEq d] (W : CQChannel d)
        {ε : ℝ}, 0 < ε → ε < 1 →
        ∀ (n : ℕ), C₀ * (1 / ε) ^ μ ≤ (2 : ℝ) ^ n →
          W.symCapacity - ε ≤
            treeProb n (fun b ↦
              polarFidelity W n b ≤
                (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))) := by
  rcases PolarCodes.theorem_1_1_quantum_polar_poly_blocklength.{0} with ⟨μ, C₀, hμ, hC₀, h⟩
  refine ⟨μ, C₀, hμ, hC₀, ?_⟩
  intro d _ _ W ε hε0 hε1 n hn
  have hW := h (toPolarCQChannel W) hε0 hε1 n hn
  have hpred : (fun b ↦ polarFidelity W n b ≤
      (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))) =
    (fun b ↦ PolarCodes.polarFidelity (toPolarCQChannel W) n b ≤
      (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))) := by
    ext b; rw [polarFidelity_eq]
  rw [treeProb_eq, hpred]
  exact hW

/-- **Corollary 5.5 (Simultaneous Amplitude/Phase Polarization for CSS Quantum Polar Codes)**. -/
theorem corollary_5_5_simultaneous_css_polarization :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
        (W_A : CQChannel d₁) (W_P : CQChannel d₂)
        {ε : ℝ}, 0 < ε → ε < 1 →
        ∀ (n : ℕ), C₀ * (4 / ε) ^ μ ≤ (2 : ℝ) ^ n →
          W_A.symCapacity + W_P.symCapacity - 1 - ε / 2 ≤
            treeProb n (fun b ↦
              polarFidelity W_A n b ≤
                (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ)) ∧
              polarFidelity W_P n b ≤
                (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))) := by
  rcases PolarCodes.corollary_5_5_simultaneous_css_polarization.{0} with ⟨μ, C₀, hμ, hC₀, h⟩
  refine ⟨μ, C₀, hμ, hC₀, ?_⟩
  intro d₁ d₂ _ _ _ _ W_A W_P ε hε0 hε1 n hn
  have hW := h (toPolarCQChannel W_A) (toPolarCQChannel W_P) hε0 hε1 n hn
  have hpred : (fun b ↦
      polarFidelity W_A n b ≤
        (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ)) ∧
      polarFidelity W_P n b ≤
        (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))) =
    (fun b ↦
      PolarCodes.polarFidelity (toPolarCQChannel W_A) n b ≤
        (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ)) ∧
      PolarCodes.polarFidelity (toPolarCQChannel W_P) n b ≤
        (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))) := by
    ext b; rw [polarFidelity_eq, polarFidelity_eq]
  rw [treeProb_eq, hpred]
  exact hW

/-- **Theorem 1.2(b), Eq. (1.7) (Linear-Scaling Polarization Splitting)**. -/
theorem theorem_1_2b_linear_splitting {d : Type} [Fintype d] [DecidableEq d] (W : CQChannel d) :
    W.minusChannel.condEntropy - W.condEntropy = W.condEntropy - W.plusChannel.condEntropy ∧
    theta0 * W.condEntropy * (1 - W.condEntropy) ≤ W.minusChannel.condEntropy - W.condEntropy :=
  PolarCodes.theorem_1_2b_linear_splitting (toPolarCQChannel W)

/-- **Theorem 1.2(b), Eq. (1.9) (Uniform Potential Contraction)**. -/
theorem theorem_1_2b_potential_contraction {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) :
    (W.minusChannel.potential + W.plusChannel.potential) / 2 ≤ Lambda0 * W.potential :=
  PolarCodes.theorem_1_2b_potential_contraction (toPolarCQChannel W)

/-- **Theorem 1.3 (Nonlinear SDPI for Qubit Dephasing)**. -/
theorem theorem_1_3_dephasing_sdpi {d : Type} [Fintype d] [DecidableEq d]
    (Ψ : DensityOp (Bool × d)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) Ψ ≤
      1 - h2 (binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) p) :=
  PolarCodes.theorem_1_3_dephasing_sdpi (toPolarDensityOp Ψ) hp0 hp1

/-- **Theorem 1.3 (Equatorial Equality)**. -/
theorem theorem_1_3_equatorial_equality {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1) =
      1 - h2 (binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num)
        (equatorialState x hx0 hx1))) p) :=
  PolarCodes.theorem_1_3_equatorial_equality hx0 hx1 hp0 hp1

end PolarCodesChallenge
