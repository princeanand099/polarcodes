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

private def fromPolarCPTPMap {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (𝒩 : PolarCodes.CPTPMap.{0} d₁ d₂) : CPTPMap d₁ d₂ :=
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
  have hm : (maxMixedState Bool).mat = (PolarCodes.maxMixedState Bool).mat := by
    ext a b
    simp only [maxMixedState, PolarCodes.maxMixedState, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  have h1 : toPolarDensityOp (𝒩.apply (maxMixedState Bool)) =
      (toPolarCPTPMap 𝒩).apply (PolarCodes.maxMixedState Bool) :=
    toPolarDensityOp_eq_of_mat (by
      ext i j
      change ∑ k : 𝒩.env,
          (𝒩.isom * (maxMixedState Bool).mat * 𝒩.isom.conjTranspose) (i, k) (j, k) =
        ∑ k : 𝒩.env,
          (𝒩.isom * (PolarCodes.maxMixedState Bool).mat * 𝒩.isom.conjTranspose) (i, k) (j, k)
      rw [hm])
  have h2 : toPolarDensityOp (𝒩.complementary.apply (maxMixedState Bool)) =
      (toPolarCPTPMap 𝒩).complementary.apply (PolarCodes.maxMixedState Bool) :=
    toPolarDensityOp_eq_of_mat (by
      ext i j
      change ∑ k : d,
          (𝒩.complementary.isom * (maxMixedState Bool).mat *
            𝒩.complementary.isom.conjTranspose) (i, k) (j, k) =
        ∑ k : d,
          (𝒩.complementary.isom * (PolarCodes.maxMixedState Bool).mat *
            𝒩.complementary.isom.conjTranspose) (i, k) (j, k)
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

private lemma condSynthStateMat_eq {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n)) (p : Fin i.val → Bool) (b : Bool) :
    condSynthStateMat W n i p b =
      (PolarCodes.condSynthState (toPolarCQChannel W) n i p b).mat := by
  unfold condSynthStateMat synthBlockMat PolarCodes.condSynthState PolarCodes.synthBlockMat
  dsimp only
  congr 1
  apply Finset.sum_congr
  · ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  · intro u _
    rw [arikanTransform_eq]
    rfl

private lemma helstromProjectorMat_eq {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Matrix α α ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {ρ₀ ρ₁ : PolarCodes.DensityOp α} (h0 : A = ρ₀.mat) (h1 : B = ρ₁.mat) :
    helstromProjectorMat hA hB = PolarCodes.helstromProjector ρ₀ ρ₁ := by
  subst h0; subst h1; rfl

private lemma qscStepProj_eq {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n)) (p : Fin i.val → Bool) (b : Bool) :
    qscStepProj W n i p b = PolarCodes.qscStepProj (toPolarCQChannel W) n i p b := by
  unfold qscStepProj PolarCodes.qscStepProj
  dsimp only
  rw [helstromProjectorMat_eq _ _ (condSynthStateMat_eq W n i p false)
    (condSynthStateMat_eq W n i p true)]

private lemma seqProd_eq {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ (Ps : List (Matrix α α ℂ)), seqProd Ps = PolarCodes.seqProd Ps
  | [] => rfl
  | P :: Ps => by simp only [seqProd, PolarCodes.seqProd, seqProd_eq Ps]

private lemma qscProjListPrefix_eq {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (infoSet : Finset (Fin (2 ^ n))) :
    ∀ (k : ℕ) (hk : k ≤ 2 ^ n) (u : Fin (2 ^ n) → Bool),
      qscProjListPrefix W n infoSet k hk u =
        PolarCodes.qscProjListPrefix (toPolarCQChannel W) n infoSet k hk u
  | 0, _, _ => rfl
  | k + 1, hk, u => by
      unfold qscProjListPrefix PolarCodes.qscProjListPrefix
      dsimp only
      rw [qscProjListPrefix_eq W n infoSet k (by omega) u]
      have hitem :
          (if (⟨k, by omega⟩ : Fin (2 ^ n)) ∈ infoSet then
            qscStepProj W n ⟨k, by omega⟩ (prefixOf ⟨k, by omega⟩ u) (u ⟨k, by omega⟩)
           else 1) =
          (if (⟨k, by omega⟩ : Fin (2 ^ n)) ∈ infoSet then
            PolarCodes.qscStepProj (toPolarCQChannel W) n ⟨k, by omega⟩
              (PolarCodes.prefixOf ⟨k, by omega⟩ u) (u ⟨k, by omega⟩)
           else 1) := by
        split_ifs
        · exact qscStepProj_eq W n ⟨k, by omega⟩ _ _
        · rfl
      rw [hitem]

private lemma qscPrefixKraus_eq {d : Type} [Fintype d] [DecidableEq d]
    (W : CQChannel d) (n : ℕ) (infoSet : Finset (Fin (2 ^ n)))
    (k : ℕ) (hk : k ≤ 2 ^ n) (u : Fin (2 ^ n) → Bool) :
    qscPrefixKraus W n infoSet k hk u =
      PolarCodes.qscPrefixKraus (toPolarCQChannel W) n infoSet k hk u := by
  unfold qscPrefixKraus PolarCodes.qscPrefixKraus
  rw [seqProd_eq, qscProjListPrefix_eq]

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

private lemma goodSet_eq {d : Type} [Fintype d] [DecidableEq d]
    {W : CQChannel d} {W' : PolarCodes.CQChannel d}
    (hmat : ∀ b, (W.out b).mat = (W'.out b).mat) (n : ℕ) (δ : ℝ) :
    goodSet W n δ = PolarCodes.goodSet W' n δ := by
  ext i
  simp only [goodSet, PolarCodes.goodSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [PolarCodes.synthChannel_fidelityParam_eq, ← bitPath_eq, polarFidelity_eq,
    polarFidelity_congr hmat n (bitPath n i)]

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

private lemma traceDist_eq {α : Type*} [Fintype α] [DecidableEq α]
    {ρ σ : DensityOp α} {ρ' σ' : PolarCodes.DensityOp α}
    (hρ : ρ.mat = ρ'.mat) (hσ : σ.mat = σ'.mat) :
    traceDist ρ σ = PolarCodes.traceDist ρ' σ' := by
  have h1 : toPolarDensityOp ρ = ρ' := toPolarDensityOp_eq_of_mat hρ
  have h2 : toPolarDensityOp σ = σ' := toPolarDensityOp_eq_of_mat hσ
  rw [← h1, ← h2]
  rfl

private lemma wiretapBobError_eq {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n))) (uF : Fin (2 ^ n) → Bool) :
    wiretapBobError 𝒩 n infoSet randSet assistSet uF =
      PolarCodes.wiretapBobError (toPolarCPTPMap 𝒩) n infoSet randSet assistSet uF := by
  unfold wiretapBobError PolarCodes.wiretapBobError
  apply congrArg (((2 : ℝ) ^ assistSet.card)⁻¹ * ·)
  apply Finset.sum_congr rfl; intro k _
  unfold qscAvgBlockError PolarCodes.CosetPolarCode.avgBlockError
  apply congrArg (((2 : ℝ) ^ (infoSet ∪ randSet).card)⁻¹ * ·)
  apply Finset.sum_congr rfl; intro m _
  have hW : toPolarCQChannel (ampChannel 𝒩) = PolarCodes.ampChannel (toPolarCPTPMap 𝒩) :=
    toPolarCQChannel_eq_of_mat (ampChannel_mat 𝒩)
  have hemb : embedMsg (infoSet ∪ randSet) (bobEffectiveFrozen assistSet uF k) m =
      PolarCodes.embedMsg (infoSet ∪ randSet) (PolarCodes.bobEffectiveFrozen assistSet uF k) m :=
    rfl
  have hkraus : qscPrefixKraus (ampChannel 𝒩) n (infoSet ∪ randSet) (2 ^ n) le_rfl
        (embedMsg (infoSet ∪ randSet) (bobEffectiveFrozen assistSet uF k) m) =
      PolarCodes.qscPrefixKraus (PolarCodes.ampChannel (toPolarCPTPMap 𝒩)) n (infoSet ∪ randSet)
        (2 ^ n) le_rfl
        (PolarCodes.embedMsg (infoSet ∪ randSet) (PolarCodes.bobEffectiveFrozen assistSet uF k) m) := by
    rw [qscPrefixKraus_eq, hW, hemb]
  have hprod : productStateMat (ampChannel 𝒩) n
        (arikanTransform n (embedMsg (infoSet ∪ randSet) (bobEffectiveFrozen assistSet uF k) m)) =
      (PolarCodes.productState (PolarCodes.ampChannel (toPolarCPTPMap 𝒩)) n
        (PolarCodes.arikanTransform n
          (PolarCodes.embedMsg (infoSet ∪ randSet) (PolarCodes.bobEffectiveFrozen assistSet uF k) m))).mat := by
    rw [arikanTransform_eq, hemb]
    ext r s
    simp only [productStateMat, PolarCodes.productState, PolarCodes.productStateMat, Matrix.of_apply]
    apply Finset.prod_congr rfl; intro j _
    exact congr_fun (congr_fun (ampChannel_mat 𝒩 _) (r j)) (s j)
  have hpovm : (PolarCodes.qscPolarCode (PolarCodes.ampChannel (toPolarCPTPMap 𝒩)) n
        (infoSet ∪ randSet) (PolarCodes.bobEffectiveFrozen assistSet uF k)).povm m =
      (PolarCodes.qscPrefixKraus (PolarCodes.ampChannel (toPolarCPTPMap 𝒩)) n (infoSet ∪ randSet)
        (2 ^ n) le_rfl
        (PolarCodes.embedMsg (infoSet ∪ randSet) (PolarCodes.bobEffectiveFrozen assistSet uF k) m))ᴴ *
      PolarCodes.qscPrefixKraus (PolarCodes.ampChannel (toPolarCPTPMap 𝒩)) n (infoSet ∪ randSet)
        (2 ^ n) le_rfl
        (PolarCodes.embedMsg (infoSet ∪ randSet) (PolarCodes.bobEffectiveFrozen assistSet uF k) m) :=
    rfl
  have henc : (PolarCodes.qscPolarCode (PolarCodes.ampChannel (toPolarCPTPMap 𝒩)) n
        (infoSet ∪ randSet) (PolarCodes.bobEffectiveFrozen assistSet uF k)).encode m =
      PolarCodes.arikanTransform n
        (PolarCodes.embedMsg (infoSet ∪ randSet) (PolarCodes.bobEffectiveFrozen assistSet uF k) m) :=
    rfl
  rw [hpovm, henc, hkraus, hprod]

private lemma fixedSubsetAvgState_mat {α : Type*} [Fintype α] [DecidableEq α]
    {W : CQChannel α} {W' : PolarCodes.CQChannel α}
    (hmat : ∀ b, (W.out b).mat = (W'.out b).mat)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (u : Fin (2 ^ n) → Bool) :
    (fixedSubsetAvgState W n S u).mat = (PolarCodes.fixedSubsetAvgState W' n S u).mat := by
  ext r s
  simp only [fixedSubsetAvgState, PolarCodes.fixedSubsetAvgState, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl; intro v _
  rw [arikanTransform_eq]
  simp only [productStateMat, PolarCodes.productState, PolarCodes.productStateMat, Matrix.of_apply]
  apply Finset.prod_congr rfl; intro j _
  exact congr_fun (congr_fun (hmat _) (r j)) (s j)

private lemma wiretapSecrecyError_eq {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n))) (uF : Fin (2 ^ n) → Bool) :
    wiretapSecrecyError 𝒩 n infoSet randSet assistSet uF =
      PolarCodes.wiretapSecrecyError (toPolarCPTPMap 𝒩) n infoSet randSet assistSet uF := by
  unfold wiretapSecrecyError PolarCodes.wiretapSecrecyError
  have hcomp : ∀ b, ((ampChannel 𝒩.complementary).out b).mat =
      ((PolarCodes.ampChannel (toPolarCPTPMap 𝒩).complementary).out b).mat := fun _ ↦ rfl
  apply traceDist_eq
  · ext ⟨m₁, r₁⟩ ⟨m₂, r₂⟩
    simp only [wiretapEveJointState, PolarCodes.wiretapEveJointState,
      wiretapEveCondState, PolarCodes.wiretapEveCondState,
      uniformBlockDiag, PolarCodes.uniformBlockDiag, Matrix.of_apply]
    split_ifs
    · exact congrArg (((Fintype.card (infoSet → Bool) : ℂ)⁻¹) * ·)
        (congr_fun (congr_fun (fixedSubsetAvgState_mat hcomp n _ _) r₁) r₂)
    · rfl
  · ext ⟨m₁, r₁⟩ ⟨m₂, r₂⟩
    simp only [wiretapIdealEveState, PolarCodes.wiretapIdealEveState,
      uniformBlockDiag, PolarCodes.uniformBlockDiag, Matrix.of_apply]
    split_ifs
    · exact congrArg (((Fintype.card (infoSet → Bool) : ℂ)⁻¹) * ·)
        (congr_fun (congr_fun (fixedSubsetAvgState_mat hcomp n _ _) r₁) r₂)
    · rfl

private lemma cssPolarEncoderIsom_eq (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (uF : Fin (2 ^ n) → Bool) (v : randSet → Bool) :
    cssPolarEncoderIsom n infoSet randSet assistSet uF v =
      PolarCodes.cssPolarEncoderIsom n infoSet randSet assistSet uF v := by
  ext x p
  simp only [cssPolarEncoderIsom, PolarCodes.cssPolarEncoderIsom, Matrix.of_apply]
  congr 1
  apply Finset.sum_congr rfl; intro r _
  rw [arikanTransform_eq]
  rfl

private lemma quantumEntanglementError_eq {d : Type} [Fintype d] [DecidableEq d]
    (𝒩 : CPTPMap Bool d) (n : ℕ)
    (infoSet randSet assistSet : Finset (Fin (2 ^ n)))
    (hdisj_ir : Disjoint infoSet randSet)
    (hdisj_ia : Disjoint infoSet assistSet)
    (hdisj_ra : Disjoint randSet assistSet)
    (uF : Fin (2 ^ n) → Bool) (v : randSet → Bool)
    (𝒟 : PolarCodes.CPTPMap.{0} ((Fin (2 ^ n) → d) × (assistSet → Bool)) (infoSet → Bool)) :
    quantumEntanglementError 𝒩 n infoSet assistSet
        (cssPolarEncoder n infoSet randSet assistSet hdisj_ir hdisj_ia hdisj_ra uF v)
        (fromPolarCPTPMap 𝒟) =
      PolarCodes.quantumEntanglementError (toPolarCPTPMap 𝒩) n infoSet assistSet
        (PolarCodes.cssPolarEncoder n infoSet randSet assistSet hdisj_ir hdisj_ia hdisj_ra uF v)
        𝒟 := by
  unfold quantumEntanglementError PolarCodes.quantumEntanglementError
  apply traceDist_eq _ rfl
  have henc_isom : (cssPolarEncoder n infoSet randSet assistSet hdisj_ir hdisj_ia hdisj_ra uF v).isom =
      (PolarCodes.cssPolarEncoder n infoSet randSet assistSet hdisj_ir hdisj_ia hdisj_ra uF v).isom := by
    ext p q
    simp only [cssPolarEncoder, PolarCodes.cssPolarEncoder, Matrix.of_apply]
    exact congr_fun (congr_fun (cssPolarEncoderIsom_eq n infoSet randSet assistSet uF v) p.1) q
  have hisom_eq :
      (CPTPMap.tensorIdLeft (infoSet → Bool)
        ((fromPolarCPTPMap 𝒟).seqComp
          (((𝒩.tensorPow n).seqComp
            (cssPolarEncoder n infoSet randSet assistSet hdisj_ir hdisj_ia hdisj_ra uF v)).tensor
            (CPTPMap.id (assistSet → Bool))))).isom =
      (PolarCodes.CPTPMap.tensorIdLeft (infoSet → Bool)
        (𝒟.seqComp
          ((((toPolarCPTPMap 𝒩).tensorPow n).seqComp
            (PolarCodes.cssPolarEncoder n infoSet randSet assistSet hdisj_ir hdisj_ia hdisj_ra uF v)).tensor
            (PolarCodes.CPTPMap.id (assistSet → Bool))))).isom := by
    ext p q
    simp only [CPTPMap.tensorIdLeft, PolarCodes.CPTPMap.tensorIdLeft,
      CPTPMap.seqComp, PolarCodes.CPTPMap.seqComp,
      CPTPMap.tensor, PolarCodes.CPTPMap.tensor,
      CPTPMap.tensorPow, PolarCodes.CPTPMap.tensorPow,
      CPTPMap.id, PolarCodes.CPTPMap.id,
      fromPolarCPTPMap, toPolarCPTPMap, Matrix.of_apply, henc_isom]
  unfold entanglementChannelOutput PolarCodes.entanglementChannelOutput
  dsimp only
  unfold CPTPMap.apply PolarCodes.CPTPMap.apply partialTrace₂Mat PolarCodes.partialTrace₂Mat
  dsimp only
  rw [hisom_eq]
  rfl

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
            C.IsQSCDecoder ∧
            W.symCapacity - ε ≤ C.rate ∧
            C.avgBlockError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := by
  rcases PolarCodes.theorem_1_1_coding_poly_blocklength.{0} with ⟨μ, C₀, hμ, hC₀, h⟩
  refine ⟨μ, C₀, hμ, hC₀, ?_⟩
  intro d _ _ W ε hε0 hε1 n hn
  obtain ⟨infoSet, frozen, hrate, herr⟩ := h (toPolarCQChannel W) hε0 hε1 n hn
  refine ⟨fromPolarCosetPolarCode (PolarCodes.qscPolarCode (toPolarCQChannel W) n infoSet frozen),
    ?_, hrate, ?_⟩
  · intro m
    change (PolarCodes.qscPrefixKraus (toPolarCQChannel W) n infoSet (2 ^ n) le_rfl
        (PolarCodes.embedMsg infoSet frozen m)).conjTranspose *
      PolarCodes.qscPrefixKraus (toPolarCQChannel W) n infoSet (2 ^ n) le_rfl
        (PolarCodes.embedMsg infoSet frozen m) =
      (qscPrefixKraus W n infoSet (2 ^ n) le_rfl (embedMsg infoSet frozen m)).conjTranspose *
      qscPrefixKraus W n infoSet (2 ^ n) le_rfl (embedMsg infoSet frozen m)
    rw [qscPrefixKraus_eq]
    rfl
  · rwa [fromPolarCosetPolarCode_avgBlockError (fun _ ↦ rfl)]

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
          ∃ C : CSSPrivatePolarCode 𝒩 n thresh,
            symCoherentInfo 𝒩 - ε / 2 ≤ C.rate ∧
            C.ampCode.avgBlockError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
            C.phaseCode.avgBlockError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
            C.ampPhaseErrorSum ≤ 2 * (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
            ((unpolarizedSet (ampChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n ≤ ε / 4 ∧
            ((unpolarizedSet (phaseChannel 𝒩) n thresh).card : ℝ) / (2 : ℝ) ^ n ≤ ε / 4 ∧
            (𝒩.IsDegradable → C.assistanceRate ≤ ε / 2) := by
  rcases PolarCodes.corollary_5_5_quantum_private_polar_coding with ⟨μ, C₀, hμ, hC₀, h⟩
  refine ⟨μ, C₀, hμ, hC₀, ?_⟩
  intro d _ _ 𝒩 ε hε0 hε1 n hn
  dsimp only
  set thresh : ℝ := (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))
  obtain ⟨C, hrate, hamp, hphase, hcomb, hUA, hUP, hdeg⟩ :=
    h (toPolarCPTPMap 𝒩) hε0 hε1 n hn
  have halign : C.phaseCode.infoSet = C.ampCode.infoSet.image (dualIndex n) := by
    rw [C.infoSet_align]
    congr 1; funext i; exact (dualIndex_eq n i).symm
  have hassist : C.assistanceSet =
      Finset.univ.filter (fun i : Fin (2 ^ n) ↦
        i ∉ goodSet (ampChannel 𝒩) n thresh ∧
        dualIndex n i ∉ goodSet (phaseChannel 𝒩) n thresh) := by
    rw [C.assistanceSet_spec]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      goodSet_eq (ampChannel_mat 𝒩), goodSet_eq (phaseChannel_mat 𝒩), dualIndex_eq]
    rfl
  let C' : CSSPrivatePolarCode 𝒩 n thresh :=
    { ampCode := fromPolarCosetPolarCode C.ampCode
      phaseCode := fromPolarCosetPolarCode C.phaseCode
      infoSet_align := halign
      assistanceSet := C.assistanceSet
      assistanceSet_spec := hassist }
  refine ⟨C', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [symCoherentInfo_eq]; exact hrate
  · rw [fromPolarCosetPolarCode_avgBlockError (ampChannel_mat 𝒩)]; exact hamp
  · rw [fromPolarCosetPolarCode_avgBlockError (phaseChannel_mat 𝒩)]; exact hphase
  · unfold CSSPrivatePolarCode.ampPhaseErrorSum
    rw [fromPolarCosetPolarCode_avgBlockError (ampChannel_mat 𝒩),
      fromPolarCosetPolarCode_avgBlockError (phaseChannel_mat 𝒩)]
    exact hcomb
  · rw [unpolarizedSet_eq (ampChannel_mat 𝒩)]; exact hUA
  · rw [unpolarizedSet_eq (phaseChannel_mat 𝒩)]; exact hUP
  · intro hdegN
    apply hdeg
    rcases hdegN with ⟨𝒟, h𝒟⟩
    exact ⟨toPolarCPTPMap 𝒟, fun ρ ↦ h𝒟 ⟨ρ.mat, ρ.posSemidef, ρ.trace_one⟩⟩

theorem corollary_5_5_operational_quantum_private_polar_coding :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ {d : Type} [Fintype d] [DecidableEq d] (𝒩 : CPTPMap Bool d)
        {ε : ℝ}, 0 < ε → ε < 1 →
        ∀ (n : ℕ), C₀ * (1 / ε) ^ μ ≤ (2 : ℝ) ^ n →
          let thresh : ℝ := (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))
          let assistPinned : Finset (Fin (2 ^ n)) :=
            Finset.univ.filter (fun i : Fin (2 ^ n) ↦
              i ∉ goodSet (ampChannel 𝒩) n thresh ∧
              dualIndex n i ∉ goodSet (phaseChannel 𝒩) n thresh)
          ∃ (C_priv : OperationalPrivatePolarCode 𝒩 n)
            (C_quant : OperationalQuantumPolarCode 𝒩 n),
            C_priv.assistSet = assistPinned ∧
            C_quant.assistSet = assistPinned ∧
            symCoherentInfo 𝒩 - ε / 2 ≤ C_priv.rate ∧
            symCoherentInfo 𝒩 - ε / 2 ≤ C_quant.rate ∧
            C_priv.bobDecodingError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
            C_priv.eveSecrecyError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
            C_quant.entanglementError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
            (𝒩.IsDegradable → C_priv.secretKeyRate ≤ ε / 2 ∧ C_quant.assistanceRate ≤ ε / 2) := by
  rcases PolarCodes.corollary_5_5_operational_quantum_private_polar_coding with ⟨μ, C₀, hμ, hC₀, h⟩
  refine ⟨μ, C₀, hμ, hC₀, ?_⟩
  intro d _ _ 𝒩 ε hε0 hε1 n hn
  dsimp only
  set thresh : ℝ := (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))
  obtain ⟨C_priv, C_quant, hpa, hqa, hpr, hqr, hbob, heve, hqerr, hdeg⟩ :=
    h (toPolarCPTPMap 𝒩) hε0 hε1 n hn
  let C_priv' : OperationalPrivatePolarCode 𝒩 n :=
    { infoSet := C_priv.infoSet
      randSet := C_priv.randSet
      assistSet := C_priv.assistSet
      disjoint_info_rand := C_priv.disjoint_info_rand
      disjoint_info_assist := C_priv.disjoint_info_assist
      disjoint_rand_assist := C_priv.disjoint_rand_assist
      publicFrozen := C_priv.publicFrozen }
  let C_quant' : OperationalQuantumPolarCode 𝒩 n :=
    { infoSet := C_quant.infoSet
      randSet := C_quant.randSet
      assistSet := C_quant.assistSet
      disj_ir := C_quant.disj_ir
      disj_ia := C_quant.disj_ia
      disj_ra := C_quant.disj_ra
      publicFrozen := C_quant.publicFrozen
      phaseChoice := C_quant.phaseChoice
      decoder := fromPolarCPTPMap C_quant.decoder }
  have hassist_eq :
      Finset.univ.filter (fun i : Fin (2 ^ n) ↦
        i ∉ PolarCodes.goodSet (PolarCodes.ampChannel (toPolarCPTPMap 𝒩)) n thresh ∧
        PolarCodes.dualIndex n i ∉ PolarCodes.goodSet (PolarCodes.phaseChannel (toPolarCPTPMap 𝒩)) n thresh) =
      Finset.univ.filter (fun i : Fin (2 ^ n) ↦
        i ∉ goodSet (ampChannel 𝒩) n thresh ∧
        dualIndex n i ∉ goodSet (phaseChannel 𝒩) n thresh) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      goodSet_eq (ampChannel_mat 𝒩), goodSet_eq (phaseChannel_mat 𝒩), dualIndex_eq]
  refine ⟨C_priv', C_quant', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change C_priv.assistSet = _
    rw [hpa, hassist_eq]
  · change C_quant.assistSet = _
    rw [hqa, hassist_eq]
  · rw [symCoherentInfo_eq]; exact hpr
  · rw [symCoherentInfo_eq]; exact hqr
  · change wiretapBobError 𝒩 n C_priv.infoSet C_priv.randSet C_priv.assistSet C_priv.publicFrozen ≤ _
    rw [wiretapBobError_eq]; exact hbob
  · change wiretapSecrecyError 𝒩 n C_priv.infoSet C_priv.randSet C_priv.assistSet C_priv.publicFrozen ≤ _
    rw [wiretapSecrecyError_eq]; exact heve
  · change quantumEntanglementError 𝒩 n C_quant.infoSet C_quant.assistSet
      (cssPolarEncoder n C_quant.infoSet C_quant.randSet C_quant.assistSet
        C_quant.disj_ir C_quant.disj_ia C_quant.disj_ra C_quant.publicFrozen C_quant.phaseChoice)
      (fromPolarCPTPMap C_quant.decoder) ≤ _
    rw [quantumEntanglementError_eq]; exact hqerr
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
    relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) ≠ ⊤ ∧
    relEntropy (dephaseState 0 le_rfl (by norm_num) Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) ≠ ⊤ ∧
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal ≤
      1 - h2 (binConv (h2Inv (1 -
        (relEntropy (dephaseState 0 le_rfl (by norm_num) Ψ)
          (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal)) p) :=
  PolarCodes.theorem_1_3_dephasing_sdpi_relEntropy (toPolarDensityOp Ψ) hp0 hp1

theorem theorem_1_3_equatorial_equality_relEntropy {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1))
      (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1)) ≠ ⊤ ∧
    relEntropy (dephaseState 0 le_rfl (by norm_num) (equatorialState x hx0 hx1))
      (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1)) ≠ ⊤ ∧
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1))
      (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal =
      1 - h2 (binConv (h2Inv (1 -
        (relEntropy (dephaseState 0 le_rfl (by norm_num) (equatorialState x hx0 hx1))
          (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal)) p) :=
  PolarCodes.theorem_1_3_equatorial_equality_relEntropy hx0 hx1 hp0 hp1

end PolarCodesChallenge
