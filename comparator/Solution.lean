/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import PolarCodes

/-!
# Comparator Solution Module for `PolarCodes`

Proves all 13 locked headline theorems in `Challenge.lean` by structural transport to the
complete unconditional formalization in `PolarCodes`.
-/

namespace PolarCodesChallenge

private def toPolarDensityOp {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : DensityOp d) : PolarCodes.DensityOp d :=
  ⟨ρ.mat, ρ.posSemidef, ρ.trace_one⟩

private def toPolarCQChannel {d : Type*} [Fintype d] [DecidableEq d]
    (W : CQChannel d) : PolarCodes.CQChannel d :=
  ⟨fun b ↦ toPolarDensityOp (W.out b)⟩

private def toPolarCPTPMap {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (𝒩 : CPTPMap d₁ d₂) : PolarCodes.CPTPMap.{0} d₁ d₂ :=
  ⟨𝒩.env, 𝒩.fintypeEnv, 𝒩.decEqEnv, 𝒩.isom, 𝒩.isom_eq⟩

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

private lemma bitPathFwd_eq : ∀ (n : ℕ) (i : Fin (2 ^ n)),
    bitPathFwd n i = PolarCodes.bitPathFwd n i
  | 0, _ => rfl
  | n + 1, i => by
      simp only [bitPathFwd, PolarCodes.bitPathFwd, bitPathFwd_eq n]

private lemma bitPathInv_eq : ∀ (n : ℕ) (b : Fin n → Bool),
    bitPathInv n b = PolarCodes.bitPathInv n b
  | 0, _ => rfl
  | n + 1, b => by
      simp only [bitPathInv, PolarCodes.bitPathInv, bitPathInv_eq n]

private lemma bitPath_eq (n : ℕ) (i : Fin (2 ^ n)) :
    bitPath n i = PolarCodes.bitPath n i :=
  bitPathFwd_eq n i

private lemma dualIndex_eq (n : ℕ) (i : Fin (2 ^ n)) :
    dualIndex n i = PolarCodes.dualIndex n i := by
  simp only [dualIndex, PolarCodes.dualIndex, bitPath, PolarCodes.bitPath, Equiv.coe_fn_symm_mk,
    Equiv.coe_fn_mk, bitPathFwd_eq, bitPathInv_eq]

private lemma arikanTransform_eq : ∀ (n : ℕ) (u : Fin (2 ^ n) → Bool),
    arikanTransform n u = PolarCodes.arikanTransform n u
  | 0, _ => rfl
  | n + 1, u => by
      funext k
      simp only [arikanTransform, PolarCodes.arikanTransform]
      split_ifs
      · exact congr_fun (arikanTransform_eq n _) _
      · exact congr_fun (arikanTransform_eq n _) _

private def fromPolarCosetPolarCode {d : Type} [Fintype d] [DecidableEq d]
    {W : CQChannel d} {n : ℕ}
    (C : PolarCodes.CosetPolarCode (toPolarCQChannel W) n) : CosetPolarCode W n :=
  ⟨C.infoSet, C.frozenBits, C.povm, C.povm_posSemidef, C.povm_sum_one⟩

private lemma fromPolarCosetPolarCode_avgBlockError {d : Type} [Fintype d] [DecidableEq d]
    {W : CQChannel d} {n : ℕ}
    (C : PolarCodes.CosetPolarCode (toPolarCQChannel W) n) :
    (fromPolarCosetPolarCode C).avgBlockError = C.avgBlockError := by
  unfold CosetPolarCode.avgBlockError PolarCodes.CosetPolarCode.avgBlockError
  congr 1
  apply Finset.sum_congr rfl; intro m _
  have henc : (fromPolarCosetPolarCode C).encode m = C.encode m :=
    arikanTransform_eq n _
  rw [henc]
  rfl

private lemma unpolarizedSet_eq {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (δ : ℝ) :
    unpolarizedSet W n δ = PolarCodes.unpolarizedSet (toPolarCQChannel W) n δ := by
  ext i
  simp only [unpolarizedSet, PolarCodes.unpolarizedSet, goodSet, PolarCodes.goodSet,
    veryNoisySet, PolarCodes.veryNoisySet, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_filter]
  rw [PolarCodes.synthChannel_fidelityParam_eq, PolarCodes.synthChannel_fidelityParam_eq,
    ← bitPath_eq, ← dualIndex_eq, ← bitPath_eq, ← polarFidelity_eq]
  have hdual : toPolarCQChannel W.dual = (toPolarCQChannel W).dual := rfl
  rw [← hdual, ← polarFidelity_eq]

/-- **Theorem 1.1 (Polynomial-Blocklength Quantum Polarization — Fidelity Fraction)**. -/
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
  simpa only [hpred] using hW

/-- **Theorem 1.1 (Full Coding-Theoretic Polynomial-Blocklength C-Q Polar Codes)**. -/
theorem theorem_1_1_coding_poly_blocklength :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ {d : Type} [Fintype d] [DecidableEq d] (W : CQChannel d)
        {ε : ℝ}, 0 < ε → ε < 1 →
        ∀ (n : ℕ), C₀ * (1 / ε) ^ μ ≤ (2 : ℝ) ^ n →
          ∃ C : CosetPolarCode W n,
            W.symCapacity - ε ≤ C.rate ∧
            C.avgBlockError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := by
  rcases PolarCodes.theorem_1_1_coding_poly_blocklength.{0} with ⟨μ, C₀, hμ, hC₀, h⟩
  refine ⟨μ, C₀, hμ, hC₀, ?_⟩
  intro d _ _ W ε hε0 hε1 n hn
  obtain ⟨C, hrate, herr⟩ := h (toPolarCQChannel W) hε0 hε1 n hn
  refine ⟨fromPolarCosetPolarCode C, hrate, ?_⟩
  rwa [fromPolarCosetPolarCode_avgBlockError]

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
  simpa only [hpred] using hW

/-- **Corollary 5.5 (Full Quantum & Private Polar Coding — Renes–Wilde Reduction)**. -/
theorem corollary_5_5_quantum_private_polar_coding :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap Bool d)
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
  rcases PolarCodes.corollary_5_5_quantum_private_polar_coding with ⟨μ, C₀, hμ, hC₀, h⟩
  refine ⟨μ, C₀, hμ, hC₀, ?_⟩
  intro d _ _ 𝒩 ε hε0 hε1 n hn
  dsimp only
  obtain ⟨C, hrate, hamp, hphase, hcomb, hUA, hUP, hdeg⟩ :=
    h (toPolarCPTPMap 𝒩) hε0 hε1 n hn
  have halign : C.phaseCode.infoSet = C.ampCode.infoSet.image (dualIndex n) := by
    rw [C.infoSet_align]
    congr 1; funext i; exact (dualIndex_eq n i).symm
  let C' : CSSPrivatePolarCode 𝒩 n :=
    { ampCode := fromPolarCosetPolarCode C.ampCode
      phaseCode := fromPolarCosetPolarCode C.phaseCode
      infoSet_align := halign
      assistanceSet := C.assistanceSet }
  refine ⟨C', hrate, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [C', fromPolarCosetPolarCode_avgBlockError] using hamp
  · simpa only [C', fromPolarCosetPolarCode_avgBlockError] using hphase
  · unfold CSSPrivatePolarCode.combinedError
    simpa only [C', fromPolarCosetPolarCode_avgBlockError] using hcomb
  · rw [unpolarizedSet_eq]; exact hUA
  · rw [unpolarizedSet_eq]; exact hUP
  · intro hdegN
    apply hdeg
    rcases hdegN with ⟨𝒟, h𝒟⟩
    exact ⟨toPolarCPTPMap 𝒟, fun ρ ↦ h𝒟 ⟨ρ.mat, ρ.posSemidef, ρ.trace_one⟩⟩

/-- **Theorem 1.2(a) (Pure-State Hybrid Quantum Mrs. Gerber Bound)**. -/
theorem theorem_1_2a_pure {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂)
    (hW₂ : W₂.IsPureState) :
    (CQChannel.varCombine W₁ W₂).condEntropy ≤ 1 - gc (1 - W₁.condEntropy) (1 - W₂.condEntropy) ∧
    W₁.condEntropy + W₂.condEntropy - 1 + gc (1 - W₁.condEntropy) (1 - W₂.condEntropy) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy ∧
    gq W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy :=
  PolarCodes.theorem_1_2a_pure (toPolarCQChannel W₁) (toPolarCQChannel W₂) hW₂

/-- **Theorem 1.2(a) (Classical Hybrid Quantum Mrs. Gerber Bound)**. -/
theorem theorem_1_2a_classical {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂)
    (hW₂ : W₂.IsClassical) :
    gc W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy ∧
    gq W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy :=
  PolarCodes.theorem_1_2a_classical (toPolarCQChannel W₁) (toPolarCQChannel W₂) hW₂

/-- **Proposition 4.2 (Four-Branch Purification Bound)**. -/
theorem prop_4_2_four_branch {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    max (max (W₁.condEntropy + deltaGap (1 - W₁.condEntropy) (1 - (2 : ℝ) ^ (W₂.condEntropy - 1)))
             (W₂.condEntropy + deltaGap (1 - W₂.condEntropy) (1 - (2 : ℝ) ^ (W₁.condEntropy - 1))))
        (max (W₂.condEntropy + deltaGap W₁.condEntropy (1 - (2 : ℝ) ^ (-W₂.condEntropy)))
             (W₁.condEntropy + deltaGap W₂.condEntropy (1 - (2 : ℝ) ^ (-W₁.condEntropy)))) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy :=
  PolarCodes.prop_4_2_four_branch (toPolarCQChannel W₁) (toPolarCQChannel W₂)

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

/-- **Theorem 1.3 (Nonlinear SDPI for Qubit Dephasing — Entropy-Difference Form)**. -/
theorem theorem_1_3_dephasing_sdpi {d : Type} [Fintype d] [DecidableEq d]
    (Ψ : DensityOp (Bool × d)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) Ψ ≤
      1 - h2 (binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) p) :=
  PolarCodes.theorem_1_3_dephasing_sdpi (toPolarDensityOp Ψ) hp0 hp1

/-- **Theorem 1.3 (Equatorial Equality — Entropy-Difference Form)**. -/
theorem theorem_1_3_equatorial_equality {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1) =
      1 - h2 (binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num)
        (equatorialState x hx0 hx1))) p) :=
  PolarCodes.theorem_1_3_equatorial_equality hx0 hx1 hp0 hp1

/-- **Theorem 1.3 (Nonlinear SDPI for Qubit Dephasing — Umegaki Relative-Entropy Form)**. -/
theorem theorem_1_3_dephasing_sdpi_relEntropy {d : Type} [Fintype d] [DecidableEq d]
    (Ψ : DensityOp (Bool × d)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal ≤
      1 - h2 (binConv (h2Inv (1 -
        (relEntropy (dephaseState 0 le_rfl (by norm_num) Ψ)
          (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal)) p) :=
  PolarCodes.theorem_1_3_dephasing_sdpi_relEntropy (toPolarDensityOp Ψ) hp0 hp1

/-- **Theorem 1.3 (Equatorial Equality — Umegaki Relative-Entropy Form)**. -/
theorem theorem_1_3_equatorial_equality_relEntropy {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1))
      (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal =
      1 - h2 (binConv (h2Inv (1 -
        (relEntropy (dephaseState 0 le_rfl (by norm_num) (equatorialState x hx0 hx1))
          (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal)) p) :=
  PolarCodes.theorem_1_3_equatorial_equality_relEntropy hx0 hx1 hp0 hp1

end PolarCodesChallenge
