/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import PolarCodes

namespace PolarCodesChallenge

private def toPolarDensityOp {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : DensityOp d) : PolarCodes.DensityOp d :=
  ⟨ρ.mat, ρ.posSemidef, ρ.trace_one⟩

private lemma toPolarDensityOp_eq_of_mat {d : Type*} [Fintype d] [DecidableEq d]
    {ρ : DensityOp d} {σ : PolarCodes.DensityOp d} (h : ρ.mat = σ.mat) :
    toPolarDensityOp ρ = σ := by
  rcases ρ with ⟨m₁, p₁, t₁⟩
  rcases σ with ⟨m₂, p₂, t₂⟩
  dsimp only at h
  subst h
  rfl

private def toPolarCQChannel {d : Type*} [Fintype d] [DecidableEq d]
    (W : CQChannel d) : PolarCodes.CQChannel d :=
  ⟨fun b ↦ toPolarDensityOp (W.out b)⟩

private lemma toPolarCQChannel_eq_of_mat {d : Type*} [Fintype d] [DecidableEq d]
    {W : CQChannel d} {W' : PolarCodes.CQChannel d}
    (h : ∀ b, (W.out b).mat = (W'.out b).mat) :
    toPolarCQChannel W = W' := by
  rcases W' with ⟨out'⟩
  unfold toPolarCQChannel
  congr 1
  funext b
  exact toPolarDensityOp_eq_of_mat (h b)

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

private lemma polarFidelity_congr {d : Type} [Fintype d] [DecidableEq d]
    {W₁ W₂ : PolarCodes.CQChannel d} (h : ∀ b, (W₁.out b).mat = (W₂.out b).mat)
    (t : ℕ) (b : Fin t → Bool) :
    PolarCodes.polarFidelity W₁ t b = PolarCodes.polarFidelity W₂ t b := by
  have hW : W₁ = W₂ := by
    rcases W₁ with ⟨out₁⟩
    rcases W₂ with ⟨out₂⟩
    congr 1; funext z
    have hz := h z
    rcases h1 : out₁ z with ⟨m₁, p₁, t₁⟩
    rcases h2 : out₂ z with ⟨m₂, p₂, t₂⟩
    simp only [h1, h2] at hz
    subst hz; rfl
  rw [hW]

private lemma symCapacity_eq {d : Type*} [Fintype d] [DecidableEq d] (W : CQChannel d) :
    W.symCapacity = (toPolarCQChannel W).symCapacity := rfl

private lemma symCoherentInfo_eq {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap Bool d) :
    symCoherentInfo 𝒩 = PolarCodes.symCoherentInfo (toPolarCPTPMap 𝒩) := by
  unfold symCoherentInfo PolarCodes.symCoherentInfo
  have hm : (((Fintype.card Bool : ℝ)⁻¹ : ℂ) • (1 : Matrix Bool Bool ℂ)) =
      (PolarCodes.maxMixedState Bool).mat := by
    ext a b
    simp only [PolarCodes.maxMixedState, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Complex.ofReal_inv, Complex.ofReal_natCast]
  have h1 : toPolarDensityOp (𝒩.apply (maxMixedState Bool)) =
      (toPolarCPTPMap 𝒩).apply (PolarCodes.maxMixedState Bool) :=
    toPolarDensityOp_eq_of_mat (by
      ext i j
      change ∑ k : 𝒩.env, (𝒩.isom * (((Fintype.card Bool : ℝ)⁻¹ : ℂ) • (1 : Matrix Bool Bool ℂ)) * 𝒩.isomᴴ) (i, k) (j, k) =
        ∑ k : 𝒩.env, (𝒩.isom * (PolarCodes.maxMixedState Bool).mat * 𝒩.isomᴴ) (i, k) (j, k)
      rw [hm])
  have h2 : toPolarDensityOp (𝒩.complementary.apply (maxMixedState Bool)) =
      (toPolarCPTPMap 𝒩).complementary.apply (PolarCodes.maxMixedState Bool) :=
    toPolarDensityOp_eq_of_mat (by
      ext i j
      change ∑ k : d, ((Matrix.of fun p a ↦ 𝒩.isom (p.2, p.1) a) *
          (((Fintype.card Bool : ℝ)⁻¹ : ℂ) • (1 : Matrix Bool Bool ℂ)) *
          (Matrix.of fun p a ↦ 𝒩.isom (p.2, p.1) a)ᴴ) (i, k) (j, k) =
        ∑ k : d, ((Matrix.of fun p a ↦ 𝒩.isom (p.2, p.1) a) *
          (PolarCodes.maxMixedState Bool).mat *
          (Matrix.of fun p a ↦ 𝒩.isom (p.2, p.1) a)ᴴ) (i, k) (j, k)
      rw [hm])
  rw [← h1, ← h2]
  rfl

private lemma treeProb_eq (n : ℕ) (P : (Fin n → Bool) → Prop) :
    treeProb n P = PolarCodes.treeProb n P := by
  classical
  unfold treeProb PolarCodes.treeProb PolarCodes.treeAvg PolarCodes.ind
  dsimp only
  rw [Finset.sum_boole]

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
    {W : CQChannel d} {W' : PolarCodes.CQChannel d} {n : ℕ}
    (C : PolarCodes.CosetPolarCode W' n) : CosetPolarCode W n :=
  ⟨C.infoSet, C.frozenBits, C.povm, C.povm_posSemidef, C.povm_sum_one⟩

private lemma fromPolarCosetPolarCode_avgBlockError {d : Type} [Fintype d] [DecidableEq d]
    {W : CQChannel d} {W' : PolarCodes.CQChannel d}
    (hmat : ∀ b, (W.out b).mat = (W'.out b).mat) {n : ℕ}
    (C : PolarCodes.CosetPolarCode W' n) :
    (fromPolarCosetPolarCode (W := W) C).avgBlockError = C.avgBlockError := by
  unfold CosetPolarCode.avgBlockError PolarCodes.CosetPolarCode.avgBlockError
  congr 1
  apply Finset.sum_congr rfl; intro m _
  have henc : (fromPolarCosetPolarCode (W := W) C).encode m = C.encode m :=
    arikanTransform_eq n _
  rw [henc]
  have hprod : productStateMat W n (C.encode m) =
      (PolarCodes.productState W' n (C.encode m)).mat := by
    ext r s
    simp only [productStateMat, PolarCodes.productState, PolarCodes.productStateMat, Matrix.of_apply]
    apply Finset.prod_congr rfl; intro k _
    rw [hmat (C.encode m k)]
  rw [hprod]
  rfl

private lemma toPolarCQChannel_dual_mat {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (b : Bool) :
    ((toPolarCQChannel W.dual).out b).mat = ((toPolarCQChannel W).dual.out b).mat := by
  cases b <;> rfl

private lemma ampChannel_mat {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (b : Bool) :
    ((ampChannel 𝒩).out b).mat = ((PolarCodes.ampChannel (toPolarCPTPMap 𝒩)).out b).mat :=
  rfl

private lemma phaseChannel_mat {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (b : Bool) :
    ((phaseChannel 𝒩).out b).mat = ((PolarCodes.phaseChannel (toPolarCPTPMap 𝒩)).out b).mat := by
  cases b <;> rfl

private lemma unpolarizedSet_eq {d : Type} [Fintype d] [DecidableEq d]
    {W : CQChannel d} {W' : PolarCodes.CQChannel d}
    (hmat : ∀ b, (W.out b).mat = (W'.out b).mat) (n : ℕ) (δ : ℝ) :
    unpolarizedSet W n δ = PolarCodes.unpolarizedSet W' n δ := by
  ext i
  simp only [unpolarizedSet, PolarCodes.unpolarizedSet, goodSet, PolarCodes.goodSet,
    veryNoisySet, PolarCodes.veryNoisySet, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_filter]
  rw [PolarCodes.synthChannel_fidelityParam_eq, PolarCodes.synthChannel_fidelityParam_eq,
    ← bitPath_eq, ← dualIndex_eq, ← bitPath_eq]
  have h1 : polarFidelity W n (bitPath n i) = PolarCodes.polarFidelity W' n (bitPath n i) := by
    rw [polarFidelity_eq]
    exact polarFidelity_congr hmat n (bitPath n i)
  have h2 : polarFidelity W.dual n (bitPath n (dualIndex n i)) =
      PolarCodes.polarFidelity W'.dual n (bitPath n (dualIndex n i)) := by
    rw [polarFidelity_eq]
    refine polarFidelity_congr ?_ n (bitPath n (dualIndex n i))
    intro b
    rw [toPolarCQChannel_dual_mat, toPolarCQChannel_eq_of_mat hmat]
  rw [h1, h2]

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
  rw [symCapacity_eq, treeProb_eq, hpred]
  exact hW

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
  rwa [fromPolarCosetPolarCode_avgBlockError (fun _ ↦ rfl)]

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
  rw [symCapacity_eq W_A, symCapacity_eq W_P, treeProb_eq, hpred]
  exact hW

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
  refine ⟨C', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [symCoherentInfo_eq]; exact hrate
  · rw [fromPolarCosetPolarCode_avgBlockError (ampChannel_mat 𝒩)]; exact hamp
  · rw [fromPolarCosetPolarCode_avgBlockError (phaseChannel_mat 𝒩)]; exact hphase
  · unfold CSSPrivatePolarCode.combinedError
    rw [fromPolarCosetPolarCode_avgBlockError (ampChannel_mat 𝒩),
      fromPolarCosetPolarCode_avgBlockError (phaseChannel_mat 𝒩)]
    exact hcomb
  · rw [unpolarizedSet_eq (ampChannel_mat 𝒩)]; exact hUA
  · rw [unpolarizedSet_eq (phaseChannel_mat 𝒩)]; exact hUP
  · intro hdegN
    apply hdeg
    rcases hdegN with ⟨𝒟, h𝒟⟩
    exact ⟨toPolarCPTPMap 𝒟, fun ρ ↦ h𝒟 ⟨ρ.mat, ρ.posSemidef, ρ.trace_one⟩⟩

theorem theorem_1_2a_pure {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂)
    (hW₂ : W₂.IsPureState) :
    (CQChannel.varCombine W₁ W₂).condEntropy ≤ 1 - gc (1 - W₁.condEntropy) (1 - W₂.condEntropy) ∧
    W₁.condEntropy + W₂.condEntropy - 1 + gc (1 - W₁.condEntropy) (1 - W₂.condEntropy) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy ∧
    gq W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy :=
  PolarCodes.theorem_1_2a_pure (toPolarCQChannel W₁) (toPolarCQChannel W₂) hW₂

theorem theorem_1_2a_classical {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂)
    (hW₂ : W₂.IsClassical) :
    gc W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy ∧
    gq W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy :=
  PolarCodes.theorem_1_2a_classical (toPolarCQChannel W₁) (toPolarCQChannel W₂) hW₂

theorem prop_4_2_four_branch {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    max (max (W₁.condEntropy + deltaGap (1 - W₁.condEntropy) (1 - (2 : ℝ) ^ (W₂.condEntropy - 1)))
             (W₂.condEntropy + deltaGap (1 - W₂.condEntropy) (1 - (2 : ℝ) ^ (W₁.condEntropy - 1))))
        (max (W₂.condEntropy + deltaGap W₁.condEntropy (1 - (2 : ℝ) ^ (-W₂.condEntropy)))
             (W₁.condEntropy + deltaGap W₂.condEntropy (1 - (2 : ℝ) ^ (-W₁.condEntropy)))) ≤
      (CQChannel.checkCombine W₁ W₂).condEntropy :=
  PolarCodes.prop_4_2_four_branch (toPolarCQChannel W₁) (toPolarCQChannel W₂)

theorem theorem_1_2b_linear_splitting {d : Type} [Fintype d] [DecidableEq d] (W : CQChannel d) :
    W.minusChannel.condEntropy - W.condEntropy = W.condEntropy - W.plusChannel.condEntropy ∧
    theta0 * W.condEntropy * (1 - W.condEntropy) ≤ W.minusChannel.condEntropy - W.condEntropy :=
  PolarCodes.theorem_1_2b_linear_splitting (toPolarCQChannel W)

theorem theorem_1_2b_potential_contraction {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) :
    (W.minusChannel.potential + W.plusChannel.potential) / 2 ≤ Lambda0 * W.potential :=
  PolarCodes.theorem_1_2b_potential_contraction (toPolarCQChannel W)

theorem theorem_1_3_dephasing_sdpi {d : Type} [Fintype d] [DecidableEq d]
    (Ψ : DensityOp (Bool × d)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) Ψ ≤
      1 - h2 (binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) p) :=
  PolarCodes.theorem_1_3_dephasing_sdpi (toPolarDensityOp Ψ) hp0 hp1

theorem theorem_1_3_equatorial_equality {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1) =
      1 - h2 (binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num)
        (equatorialState x hx0 hx1))) p) :=
  PolarCodes.theorem_1_3_equatorial_equality hx0 hx1 hp0 hp1

theorem theorem_1_3_dephasing_sdpi_relEntropy {d : Type} [Fintype d] [DecidableEq d]
    (Ψ : DensityOp (Bool × d)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal ≤
      1 - h2 (binConv (h2Inv (1 -
        (relEntropy (dephaseState 0 le_rfl (by norm_num) Ψ)
          (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal)) p) :=
  PolarCodes.theorem_1_3_dephasing_sdpi_relEntropy (toPolarDensityOp Ψ) hp0 hp1

theorem theorem_1_3_equatorial_equality_relEntropy {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1))
      (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal =
      1 - h2 (binConv (h2Inv (1 -
        (relEntropy (dephaseState 0 le_rfl (by norm_num) (equatorialState x hx0 hx1))
          (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal)) p) :=
  PolarCodes.theorem_1_3_equatorial_equality_relEntropy hx0 hx1 hp0 hp1

end PolarCodesChallenge
