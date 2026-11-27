/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Stieltjes
import PolarCodes.DataProcessing

/-!
# Hockey-Stick Integral Representation (Section 3.1)

This module proves Eq. (3.8) (`relEntropy_hockeyStick_integral`), together with convexity,
endpoint bounds, and Stieltjes right-derivative foundations for `s ↦ E_s(ρ ‖ σ)` on full-rank
density operators `ρ, σ ≻ 0`.

Downstream Section 3 results are split across:
- `PolarCodes.HockeyStickMeasure`: Lemma 3.2 (`lemma_3_2_hockeyStick_measure`) for full-rank states.
- `PolarCodes.QJJS`: Proposition 3.3 (`prop_3_3_qjjs`).
- `PolarCodes.Refinements`: equal-support Lemma 3.2 (`lemma_3_2_hockeyStick_measure_equalSupport`)
  and classical equality in Proposition 3.3 (`prop_3_3_qjjs_classical_equality`).
- `PolarCodes.RankDeficientFrenkel`: Eq. (3.7) and Eq. (3.8) under `suppSubset ρ σ`.
-/

open Matrix BigOperators Real Set Filter Topology MeasureTheory
open scoped ComplexOrder ENNReal

namespace PolarCodes

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### Part 1: Eq. (3.8) — Hockey-Stick Integral Formula -/

lemma hockeyStick_isHermitian (s : ℝ) (ρ σ : DensityOp d) :
    (ρ.mat - (s : ℂ) • σ.mat).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, ρ.isHermitian.eq, σ.isHermitian.eq]

lemma hockeyStick_eq_posPartTrace (s : ℝ) (ρ σ : DensityOp d) :
    hockeyStick s ρ σ = posPartTrace (hockeyStick_isHermitian s ρ σ) := rfl

lemma pencil_isHermitian (t : ℝ) (ρ σ : DensityOp d) :
    (((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat).IsHermitian := by
  have h1 : (((1 - t : ℝ) : ℂ) • ρ.mat).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      ρ.isHermitian.eq]
  have h2 : ((t : ℂ) • σ.mat).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      σ.isHermitian.eq]
  exact h1.add h2

/-- On `t ∈ [0, 1]`, `(1 - t) ρ + t σ ≽ 0`, so its negative spectral trace vanishes. -/
lemma negPartTrace_pencil_eq_zero_of_mem_Icc {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ρ σ : DensityOp d) :
    negPartTrace (pencil_isHermitian t ρ σ) = 0 := by
  have hpsd : ((((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat)).PosSemidef := by
    have h1 : (((1 - t : ℝ) : ℂ) • ρ.mat).PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨?_, fun x ↦ ?_⟩
      · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
          ρ.isHermitian.eq]
      · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        exact mul_nonneg (by exact_mod_cast (by linarith : 0 ≤ 1 - t))
          ((Matrix.posSemidef_iff_dotProduct_mulVec.mp ρ.posSemidef).2 x)
    have h2 : ((t : ℂ) • σ.mat).PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨?_, fun x ↦ ?_⟩
      · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
          σ.isHermitian.eq]
      · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        exact mul_nonneg (by exact_mod_cast ht0)
          ((Matrix.posSemidef_iff_dotProduct_mulVec.mp σ.posSemidef).2 x)
    exact h1.add h2
  unfold negPartTrace
  apply Finset.sum_eq_zero; intro i _
  have hnn : 0 ≤ (pencil_isHermitian t ρ σ).eigenvalues i := hpsd.eigenvalues_nonneg i
  exact max_eq_right (by linarith)

/-- Pure change-of-variables identity equating Frenkel's integral to the hockey-stick integral
for arbitrary (possibly rank-deficient) density operators `ρ, σ`. -/
lemma frenkel_lintegral_eq_hockeyStick_lintegral (ρ σ : DensityOp d) :
    (∫⁻ t : ℝ, ENNReal.ofReal (negPartTrace (pencil_isHermitian t ρ σ) / (|t| * (t - 1) ^ 2)) ∂volume) =
      ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal ((hockeyStick s ρ σ - max (1 - s) 0) / s) ∂volume := by
  let F : ℝ → ℝ≥0∞ := fun t ↦
    ENNReal.ofReal (negPartTrace (pencil_isHermitian t ρ σ) / (|t| * (t - 1) ^ 2))
  change ∫⁻ t : ℝ, F t ∂volume = _
  -- Split ℝ = Iio 0 ∪ Icc 0 1 ∪ Ioi 1
  have hsplit1 : ∫⁻ t : ℝ, F t ∂volume =
      (∫⁻ t in Iio (0 : ℝ), F t ∂volume) + (∫⁻ t in Ici (0 : ℝ), F t ∂volume) := by
    conv_lhs => rw [← Measure.restrict_univ (μ := volume), ← Set.Iio_union_Ici (a := (0 : ℝ))]
    exact lintegral_union measurableSet_Ici (Set.disjoint_left.mpr fun x h1 h2 ↦ not_lt.mpr (Set.mem_Ici.mp h2) (Set.mem_Iio.mp h1))
  have hsplit2 : ∫⁻ t in Ici (0 : ℝ), F t ∂volume =
      (∫⁻ t in Icc (0 : ℝ) 1, F t ∂volume) + (∫⁻ t in Ioi (1 : ℝ), F t ∂volume) := by
    rw [← lintegral_union measurableSet_Ioi
      (Set.disjoint_left.mpr fun x h1 h2 ↦ not_le.mpr h2 h1.2),
      Set.Icc_union_Ioi_eq_Ici (by norm_num : (0 : ℝ) ≤ 1)]
  have hzero : ∫⁻ t in Icc (0 : ℝ) 1, F t ∂volume = 0 := by
    apply setLIntegral_eq_zero measurableSet_Icc
    intro t ht
    simp only [F, Pi.zero_apply, negPartTrace_pencil_eq_zero_of_mem_Icc ht.1 ht.2, zero_div, ENNReal.ofReal_zero]
  rw [hsplit1, hsplit2, hzero, zero_add]
  -- Left piece: Iio 0 via s ↦ -s / (1 - s) on Ioo 0 1
  have hleft : ∫⁻ t in Iio (0 : ℝ), F t ∂volume =
      ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal ((hockeyStick s ρ σ - (1 - s)) / s) ∂volume := by
    let g₁ : ℝ → ℝ := fun s ↦ -s / (1 - s)
    let g₁' : ℝ → ℝ := fun s ↦ -1 / (1 - s) ^ 2
    have himg : g₁ '' Ioo (0 : ℝ) 1 = Iio (0 : ℝ) := by
      ext y; constructor
      · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
        simp only [Set.mem_Iio, g₁]
        exact div_neg_of_neg_of_pos (by linarith) (by linarith)
      · intro hy
        have hy' : y < 0 := hy
        refine ⟨-y / (1 - y), ⟨div_pos (by linarith) (by linarith), ?_⟩, ?_⟩
        · rw [div_lt_one (by linarith)]; linarith
        · simp only [g₁]
          have h1 : 1 - y ≠ 0 := by linarith
          field_simp [h1]; ring
    have hinj : Set.InjOn g₁ (Ioo (0 : ℝ) 1) := by
      intro s₁ hs₁ s₂ hs₂ h
      simp only [g₁] at h
      have h1 : 1 - s₁ ≠ 0 := by linarith [hs₁.2]
      have h2 : 1 - s₂ ≠ 0 := by linarith [hs₂.2]
      rw [div_eq_div_iff h1 h2] at h
      linarith
    have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt g₁ (g₁' s) (Ioo (0 : ℝ) 1) s := by
      intro s hs
      have h1 : 1 - s ≠ 0 := by linarith [hs.2]
      have hd : HasDerivAt g₁ (g₁' s) s := by
        have hnum : HasDerivAt (fun x : ℝ ↦ -x) (-1) s := (hasDerivAt_id' s).neg
        have hden : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) s := (hasDerivAt_id' s).const_sub 1
        convert hnum.div hden h1 using 1
        simp only [g₁']; ring
      exact hd.hasDerivWithinAt
    rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro s hs
    have hs0 : 0 < s := hs.1
    have hs1 : s < 1 := hs.2
    have h1ms : 0 < 1 - s := by linarith
    have h1ms_ne : 1 - s ≠ 0 := ne_of_gt h1ms
    have habs : |g₁' s| = 1 / (1 - s) ^ 2 := by
      simp only [g₁', abs_div, abs_neg, abs_one, abs_of_pos (sq_pos_of_pos h1ms)]
    have hmat : (((1 - g₁ s : ℝ) : ℂ) • ρ.mat + ((g₁ s : ℝ) : ℂ) • σ.mat) =
        (((1 / (1 - s) : ℝ) : ℂ) • (ρ.mat - (s : ℂ) • σ.mat)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, g₁]
      have h1 : (1 : ℝ) - (-s / (1 - s)) = 1 / (1 - s) := by field_simp [h1ms_ne]; ring
      have h2 : (-s / (1 - s)) = -(1 / (1 - s)) * s := by field_simp [h1ms_ne]
      rw [h1, h2]; push_cast; ring
    have hneg_eq : negPartTrace (pencil_isHermitian (g₁ s) ρ σ) =
        (1 / (1 - s)) * (hockeyStick s ρ σ - (1 - s)) := by
      rw [negPartTrace_eq_of_eq _ (by rw [← hmat]; exact pencil_isHermitian (g₁ s) ρ σ) hmat,
        negPartTrace_smul_nonneg (by positivity) (hockeyStick_isHermitian s ρ σ)]
      congr 1
      have hsub := posPartTrace_sub_negPartTrace (hockeyStick_isHermitian s ρ σ)
      have htr : (ρ.mat - (s : ℂ) • σ.mat).trace.re = 1 - s := by
        rw [Matrix.trace_sub, Matrix.trace_smul, ρ.trace_one, σ.trace_one, smul_eq_mul, mul_one]
        simp
      rw [htr, ← hockeyStick_eq_posPartTrace] at hsub
      linarith
    have hden_eq : |g₁ s| * (g₁ s - 1) ^ 2 = s / (1 - s) ^ 3 := by
      have hgt : g₁ s < 0 := div_neg_of_neg_of_pos (by linarith) h1ms
      rw [abs_of_neg hgt]
      simp only [g₁]
      field_simp [h1ms_ne]; ring
    simp only [F, habs, hneg_eq, hden_eq]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp [h1ms_ne, ne_of_gt hs0]
  -- Right piece: Ioi 1 via s ↦ s / (s - 1) on Ioi 1
  have hright : ∫⁻ t in Ioi (1 : ℝ), F t ∂volume =
      ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (hockeyStick s ρ σ / s) ∂volume := by
    let g₂ : ℝ → ℝ := fun s ↦ s / (s - 1)
    let g₂' : ℝ → ℝ := fun s ↦ -1 / (s - 1) ^ 2
    have himg : g₂ '' Ioi (1 : ℝ) = Ioi (1 : ℝ) := by
      ext y; constructor
      · rintro ⟨s, hs, rfl⟩
        simp only [Set.mem_Ioi, g₂] at hs ⊢
        rw [one_lt_div (by linarith)]; linarith
      · intro hy
        simp only [Set.mem_Ioi] at hy
        refine ⟨y / (y - 1), ?_, ?_⟩
        · simp only [Set.mem_Ioi]; rw [one_lt_div (by linarith)]; linarith
        · simp only [g₂]
          have h1 : y - 1 ≠ 0 := by linarith
          field_simp [h1]; ring
    have hinj : Set.InjOn g₂ (Ioi (1 : ℝ)) := by
      intro s₁ hs₁ s₂ hs₂ h
      simp only [g₂] at h
      have h1 : s₁ - 1 ≠ 0 := by linarith [Set.mem_Ioi.mp hs₁]
      have h2 : s₂ - 1 ≠ 0 := by linarith [Set.mem_Ioi.mp hs₂]
      rw [div_eq_div_iff h1 h2] at h
      linarith
    have hderiv : ∀ s ∈ Ioi (1 : ℝ), HasDerivWithinAt g₂ (g₂' s) (Ioi (1 : ℝ)) s := by
      intro s hs
      have h1 : s - 1 ≠ 0 := by linarith [Set.mem_Ioi.mp hs]
      have hd : HasDerivAt g₂ (g₂' s) s := by
        have hnum : HasDerivAt (fun x : ℝ ↦ x) 1 s := hasDerivAt_id' s
        have hden : HasDerivAt (fun x : ℝ ↦ x - 1) 1 s := (hasDerivAt_id' s).sub_const 1
        convert hnum.div hden h1 using 1
        simp only [g₂']; ring
      exact hd.hasDerivWithinAt
    conv_lhs => rw [← himg]
    rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hs1 : 1 < s := hs
    have hsm1 : 0 < s - 1 := by linarith
    have hsm1_ne : s - 1 ≠ 0 := ne_of_gt hsm1
    have hs0 : 0 < s := by linarith
    have habs : |g₂' s| = 1 / (s - 1) ^ 2 := by
      simp only [g₂', abs_div, abs_neg, abs_one, abs_of_pos (sq_pos_of_pos hsm1)]
    have hmat : (((1 - g₂ s : ℝ) : ℂ) • ρ.mat + ((g₂ s : ℝ) : ℂ) • σ.mat) =
        -(((1 / (s - 1) : ℝ) : ℂ) • (ρ.mat - (s : ℂ) • σ.mat)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
        smul_eq_mul, g₂]
      have h1 : (1 : ℝ) - s / (s - 1) = -(1 / (s - 1)) := by field_simp [hsm1_ne]; ring
      have h2 : s / (s - 1) = (1 / (s - 1)) * s := by field_simp [hsm1_ne]
      rw [h1, h2]; push_cast; ring
    have hneg_eq : negPartTrace (pencil_isHermitian (g₂ s) ρ σ) =
        (1 / (s - 1)) * hockeyStick s ρ σ := by
      have hsc : (((1 / (s - 1) : ℝ) : ℂ) • (ρ.mat - (s : ℂ) • σ.mat)).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
          (hockeyStick_isHermitian s ρ σ).eq]
      rw [negPartTrace_eq_of_eq _ hsc.neg hmat, negPartTrace_eq_posPartTrace_neg hsc.neg]
      have hnn : -(-(((1 / (s - 1) : ℝ) : ℂ) • (ρ.mat - (s : ℂ) • σ.mat))) =
          ((1 / (s - 1) : ℝ) : ℂ) • (ρ.mat - (s : ℂ) • σ.mat) := neg_neg _
      rw [posPartTrace_eq_of_eq _ hsc hnn,
        posPartTrace_smul_nonneg (by positivity) (hockeyStick_isHermitian s ρ σ),
        ← hockeyStick_eq_posPartTrace]
    have hden_eq : |g₂ s| * (g₂ s - 1) ^ 2 = s / (s - 1) ^ 3 := by
      have hgt : 0 < g₂ s := div_pos hs0 hsm1
      rw [abs_of_pos hgt]
      simp only [g₂]
      field_simp [hsm1_ne]; ring
    simp only [F, habs, hneg_eq, hden_eq]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp [hsm1_ne, ne_of_gt hs0]
  rw [hleft, hright]
  -- Recombine Ioo 0 1 and Ioi 1 into Ioi 0 (since volume {1} = 0)
  have hcomb : (∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal ((hockeyStick s ρ σ - max (1 - s) 0) / s) ∂volume) =
      (∫⁻ s in Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((hockeyStick s ρ σ - max (1 - s) 0) / s) ∂volume) +
      (∫⁻ s in Ioi (1 : ℝ),
        ENNReal.ofReal ((hockeyStick s ρ σ - max (1 - s) 0) / s) ∂volume) := by
    have hae : (Ioo (0 : ℝ) 1 ∪ Ioi (1 : ℝ) : Set ℝ) =ᵐ[volume] Ioi (0 : ℝ) := by
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine measure_mono_null (t := ∅) (fun x hx ↦ ?_) measure_empty
        simp only [Set.mem_diff, Set.mem_union, Set.mem_Ioo, Set.mem_Ioi] at hx
        rcases hx.1 with ⟨h0, _⟩ | h1 <;> exact absurd (by linarith) hx.2
      · refine measure_mono_null (t := {(1 : ℝ)}) (fun x hx ↦ ?_) Real.volume_singleton
        simp only [Set.mem_diff, Set.mem_union, Set.mem_Ioo, Set.mem_Ioi,
          Set.mem_singleton_iff] at hx ⊢
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact hx.2 (Or.inl ⟨hx.1, hlt⟩)
        · exact hx.2 (Or.inr hgt)
    rw [← setLIntegral_congr hae,
      lintegral_union measurableSet_Ioi (Set.disjoint_left.mpr fun x h1 h2 ↦ not_lt.mpr (le_of_lt h1.2) h2)]
  rw [hcomb]
  congr 1
  · apply setLIntegral_congr_fun measurableSet_Ioo
    intro s hs; dsimp only; rw [max_eq_left (by linarith [hs.2])]
  · apply setLIntegral_congr_fun measurableSet_Ioi
    intro s hs; dsimp only; rw [max_eq_right (by linarith [Set.mem_Ioi.mp hs]), sub_zero]

/-! ### Part 2: Convexity and Endpoint Behavior of `s ↦ E_s(ρ ‖ σ)` -/


/-- **Eq. (3.8)** (Hockey-Stick Integral Representation of Quantum Relative Entropy) for full-rank
density operators `ρ, σ ≻ 0`:
`D(ρ ‖ σ) * log 2 = ∫_{0}^{∞} (E_s(ρ ‖ σ) - (1 - s)_+) / s ds`. -/
theorem relEntropy_hockeyStick_integral {ρ σ : DensityOp d}
    (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    relEntropy ρ σ * ENNReal.ofReal (Real.log 2) =
      ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal ((hockeyStick s ρ σ - max (1 - s) 0) / s) ∂volume := by
  rw [relEntropy_frenkel_integral hρ hσ]
  exact frenkel_lintegral_eq_hockeyStick_lintegral ρ σ
/-- `s ↦ E_s(ρ ‖ σ)` is convex on all of `ℝ`. -/
lemma hockeyStick_convexOn (ρ σ : DensityOp d) :
    ConvexOn ℝ univ (fun s : ℝ ↦ hockeyStick s ρ σ) := by
  refine ⟨convex_univ, fun s₁ _ s₂ _ a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul]
  let hA₁ := hockeyStick_isHermitian s₁ ρ σ
  let hA₂ := hockeyStick_isHermitian s₂ ρ σ
  let hA := hockeyStick_isHermitian (a * s₁ + b * s₂) ρ σ
  let B : Matrix d d ℂ := (a : ℂ) • posPartMat hA₁ + (b : ℂ) • posPartMat hA₂
  have hB : B.PosSemidef := by
    have h1 : ((a : ℂ) • posPartMat hA₁).PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨?_, fun x ↦ ?_⟩
      · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
          (posPartMat_posSemidef hA₁).isHermitian.eq]
      · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        exact mul_nonneg (by exact_mod_cast ha)
          ((Matrix.posSemidef_iff_dotProduct_mulVec.mp (posPartMat_posSemidef hA₁)).2 x)
    have h2 : ((b : ℂ) • posPartMat hA₂).PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨?_, fun x ↦ ?_⟩
      · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
          (posPartMat_posSemidef hA₂).isHermitian.eq]
      · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        exact mul_nonneg (by exact_mod_cast hb)
          ((Matrix.posSemidef_iff_dotProduct_mulVec.mp (posPartMat_posSemidef hA₂)).2 x)
    exact h1.add h2
  have hBA_eq : B - (ρ.mat - ((a * s₁ + b * s₂ : ℝ) : ℂ) • σ.mat) =
      (a : ℂ) • negPartMat hA₁ + (b : ℂ) • negPartMat hA₂ := by
    have hcomb : ρ.mat - ((a * s₁ + b * s₂ : ℝ) : ℂ) • σ.mat =
        (a : ℂ) • (ρ.mat - (s₁ : ℂ) • σ.mat) + (b : ℂ) • (ρ.mat - (s₂ : ℂ) • σ.mat) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      have habC : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
      push_cast
      linear_combination -(ρ.mat i j) * habC
    conv_lhs => rw [hcomb, ← posPartMat_sub_negPartMat hA₁, ← posPartMat_sub_negPartMat hA₂]
    simp only [B, smul_sub]
    abel
  have hBA : (B - (ρ.mat - ((a * s₁ + b * s₂ : ℝ) : ℂ) • σ.mat)).PosSemidef := by
    rw [hBA_eq]
    have h1 : ((a : ℂ) • negPartMat hA₁).PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨?_, fun x ↦ ?_⟩
      · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
          (negPartMat_posSemidef hA₁).isHermitian.eq]
      · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        exact mul_nonneg (by exact_mod_cast ha)
          ((Matrix.posSemidef_iff_dotProduct_mulVec.mp (negPartMat_posSemidef hA₁)).2 x)
    have h2 : ((b : ℂ) • negPartMat hA₂).PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨?_, fun x ↦ ?_⟩
      · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
          (negPartMat_posSemidef hA₂).isHermitian.eq]
      · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        exact mul_nonneg (by exact_mod_cast hb)
          ((Matrix.posSemidef_iff_dotProduct_mulVec.mp (negPartMat_posSemidef hA₂)).2 x)
    exact h1.add h2
  have hle := posPartTrace_le_trace_of_le hA hB hBA
  rw [← hockeyStick_eq_posPartTrace] at hle
  have htr : B.trace.re = a * hockeyStick s₁ ρ σ + b * hockeyStick s₂ ρ σ := by
    simp only [B, Matrix.trace_add, Matrix.trace_smul, trace_posPartMat, smul_eq_mul,
      ← hockeyStick_eq_posPartTrace, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  linarith

/-- For full-rank `ρ, σ ≻ 0`, there exist `0 < a ≤ b` such that `E_s(ρ ‖ σ) = 1 - s` for `s ≤ a`
and `E_s(ρ ‖ σ) = 0` for `s ≥ b`. -/
lemma hockeyStick_bounds_posDef {ρ σ : DensityOp d} (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      (∀ s ≤ a, hockeyStick s ρ σ = 1 - s) ∧
      (∀ s ≥ b, hockeyStick s ρ σ = 0) := by
  have hne : (Finset.univ : Finset d).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 : ρ.mat.trace = 0 := by simp [Matrix.trace, hemp]
    rw [ρ.trace_one] at h0; exact one_ne_zero h0
  let ρ_min := Finset.univ.inf' hne ρ.eigvals
  let ρ_max := Finset.univ.sup' hne ρ.eigvals
  let σ_min := Finset.univ.inf' hne σ.eigvals
  let σ_max := Finset.univ.sup' hne σ.eigvals
  have hρ_min_pos : 0 < ρ_min :=
    (Finset.lt_inf'_iff hne).mpr fun i _ ↦ hρ.eigenvalues_pos i
  have hσ_min_pos : 0 < σ_min :=
    (Finset.lt_inf'_iff hne).mpr fun i _ ↦ hσ.eigenvalues_pos i
  have hρ_le : ρ_min ≤ ρ_max := by
    obtain ⟨i₀, hi₀⟩ := hne
    exact le_trans (Finset.inf'_le _ hi₀) (Finset.le_sup' _ hi₀)
  have hσ_le : σ_min ≤ σ_max := by
    obtain ⟨i₀, hi₀⟩ := hne
    exact le_trans (Finset.inf'_le _ hi₀) (Finset.le_sup' _ hi₀)
  have hσ_max_pos : 0 < σ_max := lt_of_lt_of_le hσ_min_pos hσ_le
  have hquad_bounds : ∀ (τ : DensityOp d) (x : d → ℂ),
      (Finset.univ.inf' hne τ.eigvals) * (∑ i : d, ‖x i‖ ^ 2) ≤ (star x ⬝ᵥ τ.mat.mulVec x).re ∧
      (star x ⬝ᵥ τ.mat.mulVec x).re ≤ (Finset.univ.sup' hne τ.eigvals) * (∑ i : d, ‖x i‖ ^ 2) := by
    intro τ x
    rw [re_quadForm_spectral τ.isHermitian x]
    set U : Matrix d d ℂ := (τ.isHermitian.eigenvectorUnitary : Matrix d d ℂ)
    have hU : U * star U = 1 := Unitary.coe_mul_star_self τ.isHermitian.eigenvectorUnitary
    set y : d → ℂ := (star U).mulVec x
    have hnorm : ∑ i : d, ‖y i‖ ^ 2 = ∑ i : d, ‖x i‖ ^ 2 := by
      have hdot : star y ⬝ᵥ y = star x ⬝ᵥ x := by
        have hst : star y = star x ᵥ* U := by
          ext k
          simp only [y, Pi.star_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
            Matrix.star_apply, star_sum, star_mul', star_star]
          apply Finset.sum_congr rfl; intro i _; ring
        rw [hst, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
      have hre := congr_arg Complex.re hdot
      simp only [dotProduct, Pi.star_apply, Complex.re_sum] at hre
      have hsq : ∀ (v : d → ℂ) (i : d), (star (v i) * v i).re = ‖v i‖ ^ 2 := by
        intro v i; rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      simp_rw [hsq] at hre; exact hre
    rw [← hnorm, Finset.mul_sum, Finset.mul_sum]
    constructor
    · exact Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_right (Finset.inf'_le τ.eigvals (Finset.mem_univ i)) (sq_nonneg _)
    · exact Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_right (Finset.le_sup' τ.eigvals (Finset.mem_univ i)) (sq_nonneg _)
  refine ⟨ρ_min / σ_max, ρ_max / σ_min, div_pos hρ_min_pos hσ_max_pos, ?_, ?_, ?_⟩
  · exact div_le_div₀ (le_of_lt (lt_of_lt_of_le hρ_min_pos hρ_le)) hρ_le hσ_min_pos hσ_le
  · intro s hs
    have hpsd : (ρ.mat - (s : ℂ) • σ.mat).PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨hockeyStick_isHermitian s ρ σ, fun x ↦ ?_⟩
      rw [Complex.nonneg_iff]
      have him : 0 = (star x ⬝ᵥ (ρ.mat - (s : ℂ) • σ.mat).mulVec x).im := by
        have himρ := (Complex.nonneg_iff.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp ρ.posSemidef).2 x)).2
        have himσ := (Complex.nonneg_iff.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp σ.posSemidef).2 x)).2
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        simp [Complex.sub_im, Complex.mul_im, ← himρ, ← himσ]
      refine ⟨?_, him⟩
      have hre : (star x ⬝ᵥ (ρ.mat - (s : ℂ) • σ.mat).mulVec x).re =
          (star x ⬝ᵥ ρ.mat.mulVec x).re - s * (star x ⬝ᵥ σ.mat.mulVec x).re := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        simp [Complex.sub_re, Complex.mul_re]
      rw [hre]
      have h1 := (hquad_bounds ρ x).1
      have h2 := (hquad_bounds σ x).2
      have hσ_nn : 0 ≤ (star x ⬝ᵥ σ.mat.mulVec x).re :=
        (Complex.nonneg_iff.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp σ.posSemidef).2 x)).1
      have hsum_nn : 0 ≤ ∑ i : d, ‖x i‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
      have hsσ : s * σ_max ≤ ρ_min := (le_div_iff₀ hσ_max_pos).mp hs
      by_cases hs0 : 0 ≤ s
      · nlinarith
      · nlinarith
    have hneg0 : negPartTrace (hockeyStick_isHermitian s ρ σ) = 0 := by
      unfold negPartTrace
      apply Finset.sum_eq_zero; intro i _
      exact max_eq_right (by linarith [hpsd.eigenvalues_nonneg i])
    have hsub := posPartTrace_sub_negPartTrace (hockeyStick_isHermitian s ρ σ)
    have htr : (ρ.mat - (s : ℂ) • σ.mat).trace.re = 1 - s := by
      rw [Matrix.trace_sub, Matrix.trace_smul, ρ.trace_one, σ.trace_one, smul_eq_mul, mul_one]; simp
    rw [hockeyStick_eq_posPartTrace]; linarith
  · intro s hs
    have hpsd : ((s : ℂ) • σ.mat - ρ.mat).PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      have hh : ((s : ℂ) • σ.mat - ρ.mat).IsHermitian := by
        have := (hockeyStick_isHermitian s ρ σ).neg
        simpa [neg_sub] using this
      refine ⟨hh, fun x ↦ ?_⟩
      rw [Complex.nonneg_iff]
      have him : 0 = (star x ⬝ᵥ ((s : ℂ) • σ.mat - ρ.mat).mulVec x).im := by
        have himρ := (Complex.nonneg_iff.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp ρ.posSemidef).2 x)).2
        have himσ := (Complex.nonneg_iff.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp σ.posSemidef).2 x)).2
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        simp [Complex.sub_im, Complex.mul_im, ← himρ, ← himσ]
      refine ⟨?_, him⟩
      have hre : (star x ⬝ᵥ ((s : ℂ) • σ.mat - ρ.mat).mulVec x).re =
          s * (star x ⬝ᵥ σ.mat.mulVec x).re - (star x ⬝ᵥ ρ.mat.mulVec x).re := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        simp [Complex.sub_re, Complex.mul_re]
      rw [hre]
      have h1 := (hquad_bounds ρ x).2
      have h2 := (hquad_bounds σ x).1
      have hs0 : 0 ≤ s := le_trans (le_of_lt (div_pos (lt_of_lt_of_le hρ_min_pos hρ_le) hσ_min_pos)) hs
      have hsum_nn : 0 ≤ ∑ i : d, ‖x i‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
      have hsσ : ρ_max ≤ s * σ_min := (div_le_iff₀ hσ_min_pos).mp hs
      nlinarith
    have hpos0 : posPartTrace (hockeyStick_isHermitian s ρ σ) = 0 := by
      have hsub_herm : ((s : ℂ) • σ.mat - ρ.mat).IsHermitian := by
        have := (hockeyStick_isHermitian s ρ σ).neg; simpa [neg_sub] using this
      have hneg_eq : negPartTrace hsub_herm = 0 := by
        unfold negPartTrace
        apply Finset.sum_eq_zero; intro i _
        exact max_eq_right (by linarith [hpsd.eigenvalues_nonneg i])
      rw [negPartTrace_eq_posPartTrace_neg] at hneg_eq
      rw [posPartTrace_eq_of_eq (hockeyStick_isHermitian s ρ σ) hsub_herm.neg (by abel)]
      exact hneg_eq
    rw [hockeyStick_eq_posPartTrace]; exact hpos0

/-! ### Part 3: Right Derivative & Stieltjes Measure for Convex Hockey-Stick Functions -/

/-- Right derivative of a function `f : ℝ → ℝ` at `s`, defined as the infimum of forward difference
quotients (for convex `f`, this is exact and avoids `derivWithin` API overhead). -/
noncomputable def convexRightDeriv (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  sInf ((fun h : ℝ ↦ (f (s + h) - f s) / h) '' Ioi 0)

section ConvexRightDeriv

variable {f : ℝ → ℝ} {a b : ℝ}

lemma slope_le_slope_of_convex (hf : ConvexOn ℝ univ f) {x y z : ℝ}
    (hxy : x < y) (hyz : y < z) :
    (f y - f x) / (y - x) ≤ (f z - f x) / (z - x) ∧
    (f z - f x) / (z - x) ≤ (f z - f y) / (z - y) := by
  have hxz : 0 < z - x := by linarith
  have h1 : (z - y) / (z - x) ≥ 0 := div_nonneg (by linarith) (le_of_lt hxz)
  have h2 : (y - x) / (z - x) ≥ 0 := div_nonneg (by linarith) (le_of_lt hxz)
  have hsum : (z - y) / (z - x) + (y - x) / (z - x) = 1 := by field_simp [ne_of_gt hxz]; ring
  have hcomb : ((z - y) / (z - x)) * x + ((y - x) / (z - x)) * z = y := by
    field_simp [ne_of_gt hxz]; ring
  have hconv := hf.2 (Set.mem_univ x) (Set.mem_univ z) h1 h2 hsum
  simp only [smul_eq_mul] at hconv
  rw [hcomb] at hconv
  constructor
  · rw [div_le_div_iff₀ (by linarith) hxz]
    have hmul := mul_le_mul_of_nonneg_right hconv (le_of_lt hxz)
    have hsimp : ((z - y) / (z - x) * f x + (y - x) / (z - x) * f z) * (z - x) =
        (z - y) * f x + (y - x) * f z := by field_simp [ne_of_gt hxz]
    linarith
  · rw [div_le_div_iff₀ hxz (by linarith)]
    have hmul := mul_le_mul_of_nonneg_right hconv (le_of_lt hxz)
    have hsimp : ((z - y) / (z - x) * f x + (y - x) / (z - x) * f z) * (z - x) =
        (z - y) * f x + (y - x) * f z := by field_simp [ne_of_gt hxz]
    linarith

lemma slope_bounds_of_hockeyStick (hf : ConvexOn ℝ univ f)
    (hleft : ∀ s ≤ a, f s = 1 - s) (hright : ∀ s ≥ b, f s = 0)
    {x y : ℝ} (hxy : x < y) :
    -1 ≤ (f y - f x) / (y - x) ∧ (f y - f x) / (y - x) ≤ 0 := by
  let x₀ := min x a - 1
  let y₀ := max y b + 1
  have hx₀ : x₀ < x := by dsimp [x₀]; linarith [min_le_left x a]
  have hx₀a : x₀ ≤ a := by dsimp [x₀]; linarith [min_le_right x a]
  have hy₀ : y < y₀ := by dsimp [y₀]; linarith [le_max_left y b]
  have hy₀b : b ≤ y₀ := by dsimp [y₀]; linarith [le_max_right y b]
  constructor
  · let x₁ := min x a - 2
    have hx₁ : x₁ < x₀ := by dsimp [x₁, x₀]; linarith
    have hx₁a : x₁ ≤ a := by linarith
    have h1 : (f x₀ - f x₁) / (x₀ - x₁) = -1 := by
      rw [hleft x₀ hx₀a, hleft x₁ hx₁a]
      have hne : x₀ - x₁ ≠ 0 := by linarith
      field_simp [hne]; ring
    have h2 := slope_le_slope_of_convex hf hx₁ hx₀
    have h3 := slope_le_slope_of_convex hf hx₀ hxy
    linarith [h2.1, h2.2, h3.1, h3.2]
  · let y₁ := max y b + 2
    have hy₁ : y₀ < y₁ := by dsimp [y₀, y₁]; linarith
    have hy₁b : b ≤ y₁ := by linarith
    have h1 : (f y₁ - f y₀) / (y₁ - y₀) = 0 := by
      rw [hright y₁ hy₁b, hright y₀ hy₀b]; simp
    have h2 := slope_le_slope_of_convex hf hxy hy₀
    have h3 := slope_le_slope_of_convex hf hy₀ hy₁
    linarith [h2.1, h2.2, h3.1, h3.2]

lemma convexRightDeriv_le_slope (hf : ConvexOn ℝ univ f)
    (hleft : ∀ s ≤ a, f s = 1 - s) (hright : ∀ s ≥ b, f s = 0)
    {x y : ℝ} (hxy : x < y) :
    convexRightDeriv f x ≤ (f y - f x) / (y - x) := by
  apply csInf_le
  · refine ⟨-1, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    have hh' : 0 < h := hh
    have h1 := (slope_bounds_of_hockeyStick hf hleft hright (by linarith : x < x + h)).1
    simpa [add_sub_cancel_left] using h1
  · exact ⟨y - x, show (0 : ℝ) < y - x by linarith, by simp [add_sub_cancel]⟩

lemma slope_le_convexRightDeriv (hf : ConvexOn ℝ univ f)
    (hleft : ∀ s ≤ a, f s = 1 - s) (hright : ∀ s ≥ b, f s = 0)
    {x y : ℝ} (hxy : x < y) :
    (f y - f x) / (y - x) ≤ convexRightDeriv f y := by
  apply le_csInf
  · exact ⟨(f (y + 1) - f y) / 1, 1, by norm_num, rfl⟩
  · rintro _ ⟨h, hh, rfl⟩
    have hh' : 0 < h := hh
    have h12 := slope_le_slope_of_convex hf hxy (by linarith : y < y + h)
    have h1 : (f y - f x) / (y - x) ≤ (f (y + h) - f y) / (y + h - y) := le_trans h12.1 h12.2
    simpa [add_sub_cancel_left] using h1

lemma convexRightDeriv_mono (hf : ConvexOn ℝ univ f)
    (hleft : ∀ s ≤ a, f s = 1 - s) (hright : ∀ s ≥ b, f s = 0) :
    Monotone (convexRightDeriv f) := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · exact le_trans (convexRightDeriv_le_slope hf hleft hright hlt)
      (slope_le_convexRightDeriv hf hleft hright hlt)

lemma convexRightDeriv_bounds (hf : ConvexOn ℝ univ f)
    (hleft : ∀ s ≤ a, f s = 1 - s) (hright : ∀ s ≥ b, f s = 0) (s : ℝ) :
    -1 ≤ convexRightDeriv f s ∧ convexRightDeriv f s ≤ 0 := by
  constructor
  · apply le_csInf
    · exact ⟨(f (s + 1) - f s) / 1, 1, by norm_num, rfl⟩
    · rintro _ ⟨h, hh, rfl⟩
      have hh' : 0 < h := hh
      simpa [add_sub_cancel_left] using
        (slope_bounds_of_hockeyStick hf hleft hright (by linarith : s < s + h)).1
  · exact le_trans (convexRightDeriv_le_slope hf hleft hright (by linarith : s < s + 1))
      (slope_bounds_of_hockeyStick hf hleft hright (by linarith : s < s + 1)).2

lemma convexRightDeriv_eq_neg_one (hf : ConvexOn ℝ univ f)
    (hleft : ∀ s ≤ a, f s = 1 - s) (hright : ∀ s ≥ b, f s = 0) {s : ℝ} (hs : s < a) :
    convexRightDeriv f s = -1 := by
  apply le_antisymm
  · have h := convexRightDeriv_le_slope hf hleft hright hs
    rw [hleft a le_rfl, hleft s (le_of_lt hs)] at h
    have hne : a - s ≠ 0 := by linarith
    have heq : (1 - a - (1 - s)) / (a - s) = -1 := by field_simp [hne]; ring
    linarith
  · exact (convexRightDeriv_bounds hf hleft hright s).1

lemma convexRightDeriv_eq_zero (hf : ConvexOn ℝ univ f)
    (hleft : ∀ s ≤ a, f s = 1 - s) (hright : ∀ s ≥ b, f s = 0) {s : ℝ} (hs : b ≤ s) :
    convexRightDeriv f s = 0 := by
  apply le_antisymm (convexRightDeriv_bounds hf hleft hright s).2
  apply le_csInf
  · exact ⟨(f (s + 1) - f s) / 1, 1, by norm_num, rfl⟩
  · rintro _ ⟨h, hh, rfl⟩
    have hh' : 0 < h := hh
    dsimp only
    rw [hright (s + h) (by linarith), hright s hs]; simp

lemma continuous_of_hockeyStick (hf : ConvexOn ℝ univ f)
    (hleft : ∀ s ≤ a, f s = 1 - s) (hright : ∀ s ≥ b, f s = 0) :
    Continuous f := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε, hε, fun y hy ↦ ?_⟩
  rw [Real.dist_eq] at hy ⊢
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · have hb := slope_bounds_of_hockeyStick hf hleft hright hlt
    have hdiff : -(y - x) ≤ f y - f x ∧ f y - f x ≤ 0 := by
      constructor
      · have := (le_div_iff₀ (by linarith : 0 < y - x)).mp hb.1; linarith
      · have := (div_le_iff₀ (by linarith : 0 < y - x)).mp hb.2; linarith
    rw [abs_lt]; rw [abs_lt] at hy; constructor <;> linarith
  · simpa using hε
  · have hb := slope_bounds_of_hockeyStick hf hleft hright hgt
    have hdiff : -(x - y) ≤ f x - f y ∧ f x - f y ≤ 0 := by
      constructor
      · have := (le_div_iff₀ (by linarith : 0 < x - y)).mp hb.1; linarith
      · have := (div_le_iff₀ (by linarith : 0 < x - y)).mp hb.2; linarith
    rw [abs_lt]; rw [abs_lt] at hy; constructor <;> linarith

lemma convexRightDeriv_right_continuous (hf : ConvexOn ℝ univ f)
    (hleft : ∀ s ≤ a, f s = 1 - s) (hright : ∀ s ≥ b, f s = 0) (s : ℝ) :
    ContinuousWithinAt (convexRightDeriv f) (Ici s) s := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hne : ((fun h : ℝ ↦ (f (s + h) - f s) / h) '' Ioi 0).Nonempty :=
    ⟨(f (s + 1) - f s) / 1, 1, by norm_num, rfl⟩
  obtain ⟨_, ⟨h, hh, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (by linarith : convexRightDeriv f s < convexRightDeriv f s + ε / 2)
  have hh' : 0 < h := hh
  have hcont_q : ContinuousAt (fun t : ℝ ↦ (f (s + h) - f t) / (s + h - t)) s := by
    have h1 : ContinuousAt (fun t : ℝ ↦ f (s + h) - f t) s :=
      continuousAt_const.sub (continuous_of_hockeyStick hf hleft hright).continuousAt
    have h2 : ContinuousAt (fun t : ℝ ↦ s + h - t) s :=
      continuousAt_const.sub continuousAt_id
    exact h1.div h2 (by simp; linarith)
  rw [Metric.continuousAt_iff] at hcont_q
  obtain ⟨δ, hδ, hδ_prop⟩ := hcont_q (ε / 2) (by linarith)
  refine ⟨min δ (h / 2), lt_min hδ (by linarith), fun t ht hdist ↦ ?_⟩
  have hts : s ≤ t := ht
  have ht_lt : t < s + h := by
    rw [Real.dist_eq] at hdist
    have := lt_of_lt_of_le hdist (min_le_right _ _)
    rw [abs_lt] at this; linarith
  have hdist_δ : dist t s < δ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hq := hδ_prop hdist_δ
  rw [Real.dist_eq] at hq ⊢
  simp only [add_sub_cancel_left] at hq
  have hmono : convexRightDeriv f s ≤ convexRightDeriv f t :=
    convexRightDeriv_mono hf hleft hright hts
  have hupper : convexRightDeriv f t ≤ (f (s + h) - f t) / (s + h - t) :=
    convexRightDeriv_le_slope hf hleft hright ht_lt
  rw [abs_lt] at hq ⊢
  constructor <;> linarith

/-- Riemann-sum sandwich: for convex `f` with right derivative `g = convexRightDeriv f`,
`f b - f s = ∫ u in s..b, g u` for every `s ≤ b`. -/
lemma sub_eq_intervalIntegral_convexRightDeriv (hf : ConvexOn ℝ univ f)
    (hleft : ∀ s ≤ a, f s = 1 - s) (hright : ∀ s ≥ b, f s = 0) {s : ℝ} (hsb : s ≤ b) :
    f b - f s = ∫ u in s..b, convexRightDeriv f u := by
  let g := convexRightDeriv f
  have hg_mono : Monotone g := convexRightDeriv_mono hf hleft hright
  have hg_int : ∀ x y : ℝ, IntervalIntegrable g volume x y := fun x y ↦
    hg_mono.intervalIntegrable
  -- Show `| (f b - f s) - ∫ u in s..b, g u | ≤ (b - s) / N` for all `N ≥ 1`
  have hbound : ∀ N : ℕ, 0 < N → |(f b - f s) - ∫ u in s..b, g u| ≤ (b - s) / (N : ℝ) := by
    intro N hN
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    let Δ : ℝ := (b - s) / (N : ℝ)
    have hΔ : 0 ≤ Δ := div_nonneg (by linarith) (le_of_lt hNpos)
    let u : ℕ → ℝ := fun k ↦ s + (k : ℝ) * Δ
    have hu_mono : ∀ k : ℕ, u k ≤ u (k + 1) := by
      intro k; simp only [u, Nat.cast_add, Nat.cast_one]; linarith
    have hu0 : u 0 = s := by simp [u]
    have huN : u N = b := by
      simp only [u, Δ]
      field_simp [ne_of_gt hNpos]; ring
    -- Step 1: telescoping sum for `f b - f s`
    have hf_tele : ∑ k ∈ Finset.range N, (f (u (k + 1)) - f (u k)) = f b - f s := by
      rw [Finset.sum_range_sub (fun k ↦ f (u k)) N, hu0, huN]
    -- Step 2: telescoping sum for `∫ u in s..b, g u`
    have hint_tele : ∑ k ∈ Finset.range N, (∫ t in u k..u (k + 1), g t) = ∫ t in s..b, g t := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ ↦ hg_int (u k) (u (k + 1))),
        hu0, huN]
    -- Step 3: sandwich each subinterval
    have hf_lower : ∑ k ∈ Finset.range N, g (u k) * Δ ≤ f b - f s := by
      rw [← hf_tele]
      apply Finset.sum_le_sum; intro k _
      rcases eq_or_lt_of_le (hu_mono k) with heq | hlt
      · have hΔ0 : Δ = 0 := by simp only [u, Nat.cast_add, Nat.cast_one] at heq; linarith
        rw [heq, sub_self, hΔ0, mul_zero]
      · have h := convexRightDeriv_le_slope hf hleft hright hlt
        have hdiff : u (k + 1) - u k = Δ := by simp only [u, Nat.cast_add, Nat.cast_one]; ring
        rw [hdiff] at h
        exact (le_div_iff₀ (by linarith)).mp h
    have hf_upper : f b - f s ≤ ∑ k ∈ Finset.range N, g (u (k + 1)) * Δ := by
      rw [← hf_tele]
      apply Finset.sum_le_sum; intro k _
      rcases eq_or_lt_of_le (hu_mono k) with heq | hlt
      · have hΔ0 : Δ = 0 := by simp only [u, Nat.cast_add, Nat.cast_one] at heq; linarith
        rw [heq, sub_self, hΔ0, mul_zero]
      · have h := slope_le_convexRightDeriv hf hleft hright hlt
        have hdiff : u (k + 1) - u k = Δ := by simp only [u, Nat.cast_add, Nat.cast_one]; ring
        rw [hdiff] at h
        exact (div_le_iff₀ (by linarith)).mp h
    have hi_lower : ∑ k ∈ Finset.range N, g (u k) * Δ ≤ ∫ t in s..b, g t := by
      rw [← hint_tele]
      apply Finset.sum_le_sum; intro k _
      have hle := intervalIntegral.integral_mono_on (hu_mono k) intervalIntegrable_const
        (hg_int (u k) (u (k + 1))) (fun t ht ↦ hg_mono ht.1)
      rw [intervalIntegral.integral_const, smul_eq_mul,
        show u (k + 1) - u k = Δ by simp only [u, Nat.cast_add, Nat.cast_one]; ring, mul_comm] at hle
      exact hle
    have hi_upper : ∫ t in s..b, g t ≤ ∑ k ∈ Finset.range N, g (u (k + 1)) * Δ := by
      rw [← hint_tele]
      apply Finset.sum_le_sum; intro k _
      have hle := intervalIntegral.integral_mono_on (hu_mono k) (hg_int (u k) (u (k + 1)))
        intervalIntegrable_const (fun t ht ↦ hg_mono ht.2)
      rw [intervalIntegral.integral_const, smul_eq_mul,
        show u (k + 1) - u k = Δ by simp only [u, Nat.cast_add, Nat.cast_one]; ring, mul_comm] at hle
      exact hle
    -- Gap between upper and lower sums is `(g b - g s) * Δ ≤ Δ`
    have hgap : (∑ k ∈ Finset.range N, g (u (k + 1)) * Δ) - (∑ k ∈ Finset.range N, g (u k) * Δ) ≤ Δ := by
      rw [← Finset.sum_sub_distrib]
      simp_rw [← sub_mul, ← Finset.sum_mul, Finset.sum_range_sub (fun k ↦ g (u k)) N, hu0, huN]
      have hgb := (convexRightDeriv_bounds hf hleft hright b).2
      have hgs := (convexRightDeriv_bounds hf hleft hright s).1
      nlinarith
    rw [abs_le]
    constructor <;> linarith
  by_contra hne
  have hpos : 0 < |(f b - f s) - ∫ u in s..b, g u| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - s) / |(f b - f s) - ∫ u in s..b, g u|)
  have hNpos : 0 < N := by
    by_contra h0; push Not at h0
    have hN0 : N = 0 := Nat.eq_zero_of_le_zero h0
    subst hN0; simp at hN
    have : 0 ≤ (b - s) / |(f b - f s) - ∫ u in s..b, g u| := div_nonneg (by linarith) (le_of_lt hpos)
    linarith
  have hb := hbound N hNpos
  have hgt : (b - s) / (N : ℝ) < |(f b - f s) - ∫ u in s..b, g u| := by
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hNpos)]
    have := (div_lt_iff₀ hpos).mp hN
    linarith
  linarith

end ConvexRightDeriv

/-! ### Part 4: Elementary 1D Integrals for Lemma 3.2 -/

/-- For `t > 0`:
`∫_{0}^{1} (s - t)_+ / s ds + ∫_{1}^{∞} (t - s)_+ / s ds = t log t - (t - 1)`. -/
lemma lintegral_hockeyStick_kernel_1 {t : ℝ} (ht : 0 < t) :
    (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s - t) 0 / s) ∂volume) +
    (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t - s) 0 / s) ∂volume) =
      ENNReal.ofReal (t * Real.log t - (t - 1)) := by
  rcases le_or_gt t 1 with ht1 | ht1
  · -- Case `0 < t ≤ 1`: second integral vanishes, first is `∫_t^1 (1 - t/s) ds`
    have h2 : ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t - s) 0 / s) ∂volume = 0 := by
      apply setLIntegral_eq_zero measurableSet_Ioi
      intro s hs
      dsimp only; simp only [Pi.zero_apply]
      rw [max_eq_right (by linarith [Set.mem_Ioi.mp hs]), zero_div, ENNReal.ofReal_zero]
    rw [h2, add_zero]
    have h1 : ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s - t) 0 / s) ∂volume =
        ∫⁻ s in Ioc t 1, ENNReal.ofReal (1 - t / s) ∂volume := by
      have hsplit : Ioc (0 : ℝ) 1 = Ioc (0 : ℝ) t ∪ Ioc t 1 :=
        (Set.Ioc_union_Ioc_eq_Ioc (le_of_lt ht) ht1).symm
      rw [hsplit, lintegral_union measurableSet_Ioc
        (Set.disjoint_left.mpr fun x h1 h2 ↦ not_lt.mpr h1.2 h2.1)]
      have hz : ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal (max (s - t) 0 / s) ∂volume = 0 := by
        apply setLIntegral_eq_zero measurableSet_Ioc
        intro s hs; dsimp only; simp only [Pi.zero_apply]
        rw [max_eq_right (by linarith [hs.2]), zero_div, ENNReal.ofReal_zero]
      rw [hz, zero_add]
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro s hs
      dsimp only
      have hs0 : 0 < s := lt_trans ht hs.1
      rw [max_eq_left (by linarith [hs.1]), sub_div, div_self (ne_of_gt hs0)]
    rw [h1]
    have hcont : ContinuousOn (fun s : ℝ ↦ 1 - t / s) (uIcc t 1) := by
      rw [Set.uIcc_of_le ht1]
      exact continuousOn_const.sub (continuousOn_const.div continuousOn_id fun s hs ↦ ne_of_gt (lt_of_lt_of_le ht hs.1))
    have hint : IntegrableOn (fun s : ℝ ↦ 1 - t / s) (Ioc t 1) volume :=
      (hcont.intervalIntegrable).1
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs ↦ by
        dsimp only; simp only [Pi.zero_apply]
        have hs0 : 0 < s := lt_trans ht hs.1
        rw [sub_nonneg, div_le_one hs0]; exact le_of_lt hs.1))]
    rw [← intervalIntegral.integral_of_le ht1]
    have hftc : ∫ s in t..1, (1 - t / s) = (1 - t * Real.log 1) - (t - t * Real.log t) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ ↦ x - t * Real.log x)
      · intro s hs
        rw [Set.uIcc_of_le ht1] at hs
        have hs0 : s ≠ 0 := by linarith [hs.1]
        convert (hasDerivAt_id' s).sub ((Real.hasDerivAt_log hs0).const_mul t) using 1
        ring
      · exact hcont.intervalIntegrable
    rw [hftc, Real.log_one]; congr 1; ring
  · -- Case `1 < t`: first integral vanishes, second is `∫_1^t (t/s - 1) ds`
    have h1 : ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s - t) 0 / s) ∂volume = 0 := by
      apply setLIntegral_eq_zero measurableSet_Ioc
      intro s hs
      dsimp only; simp only [Pi.zero_apply]
      rw [max_eq_right (by linarith [hs.2]), zero_div, ENNReal.ofReal_zero]
    rw [h1, zero_add]
    have h2 : ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t - s) 0 / s) ∂volume =
        ∫⁻ s in Ioc (1 : ℝ) t, ENNReal.ofReal (t / s - 1) ∂volume := by
      have hsplit : Ioi (1 : ℝ) = Ioc (1 : ℝ) t ∪ Ioi t :=
        (Set.Ioc_union_Ioi_eq_Ioi (le_of_lt ht1)).symm
      rw [hsplit, lintegral_union measurableSet_Ioi
        (Set.disjoint_left.mpr fun x h1 h2 ↦ not_lt.mpr h1.2 h2)]
      have hz : ∫⁻ s in Ioi t, ENNReal.ofReal (max (t - s) 0 / s) ∂volume = 0 := by
        apply setLIntegral_eq_zero measurableSet_Ioi
        intro s hs; dsimp only; simp only [Pi.zero_apply]
        rw [max_eq_right (by linarith [Set.mem_Ioi.mp hs]), zero_div, ENNReal.ofReal_zero]
      rw [hz, add_zero]
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro s hs
      dsimp only
      have hs0 : 0 < s := by linarith [hs.1]
      rw [max_eq_left (by linarith [hs.2]), sub_div, div_self (ne_of_gt hs0)]
    rw [h2]
    have hcont : ContinuousOn (fun s : ℝ ↦ t / s - 1) (uIcc (1 : ℝ) t) := by
      rw [Set.uIcc_of_le (le_of_lt ht1)]
      exact (continuousOn_const.div (continuousOn_id (s := Icc (1 : ℝ) t)) fun s hs ↦ ne_of_gt (by linarith [hs.1] : (0 : ℝ) < s)).sub continuousOn_const
    have hint : IntegrableOn (fun s : ℝ ↦ t / s - 1) (Ioc 1 t) volume :=
      (hcont.intervalIntegrable).1
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs ↦ by
        dsimp only; simp only [Pi.zero_apply]
        have hs0 : 0 < s := by linarith [hs.1]
        rw [sub_nonneg, one_le_div hs0]; exact hs.2))]
    rw [← intervalIntegral.integral_of_le (le_of_lt ht1)]
    have hftc : ∫ s in (1 : ℝ)..t, (t / s - 1) = (t * Real.log t - t) - (t * Real.log 1 - 1) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ ↦ t * Real.log x - x)
      · intro s hs
        rw [Set.uIcc_of_le (le_of_lt ht1)] at hs
        have hs0 : s ≠ 0 := by linarith [hs.1]
        convert ((Real.hasDerivAt_log hs0).const_mul t).sub (hasDerivAt_id' s) using 1
        ring
      · exact hcont.intervalIntegrable
    rw [hftc, Real.log_one]; congr 1; ring

/-- For `t > 0`:
`∫_{0}^{1} (s t - 1)_+ / s ds + ∫_{1}^{∞} (1 - s t)_+ / s ds = -log t + (t - 1)`. -/
lemma lintegral_hockeyStick_kernel_2 {t : ℝ} (ht : 0 < t) :
    (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * t - 1) 0 / s) ∂volume) +
    (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (1 - s * t) 0 / s) ∂volume) =
      ENNReal.ofReal (-Real.log t + (t - 1)) := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have h1 := lintegral_hockeyStick_kernel_1 (inv_pos.mpr ht)
  -- Change of variables: `max (s * t - 1) 0 / s = t * max (s - t⁻¹) 0 / s`
  have hl : (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * t - 1) 0 / s) ∂volume) =
      ENNReal.ofReal t * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s - t⁻¹) 0 / s) ∂volume := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro s hs; dsimp only
    rw [← ENNReal.ofReal_mul (le_of_lt ht)]
    congr 1
    have hmax : t * max (s - t⁻¹) 0 = max (s * t - 1) 0 := by
      rw [mul_max_of_nonneg _ _ (le_of_lt ht), mul_zero]
      congr 1; field_simp [ht_ne]
    rw [← hmax]; ring
  have hr : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (1 - s * t) 0 / s) ∂volume) =
      ENNReal.ofReal t * ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t⁻¹ - s) 0 / s) ∂volume := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro s hs; dsimp only
    rw [← ENNReal.ofReal_mul (le_of_lt ht)]
    congr 1
    have hmax : t * max (t⁻¹ - s) 0 = max (1 - s * t) 0 := by
      rw [mul_max_of_nonneg _ _ (le_of_lt ht), mul_zero]
      congr 1; field_simp [ht_ne]
    rw [← hmax]; ring
  rw [hl, hr, ← mul_add, h1, ← ENNReal.ofReal_mul (le_of_lt ht), Real.log_inv]
  congr 1; field_simp [ht_ne]; ring

/-- For `t > 0`: midpoint kernel integral for `D(ρ ‖ m)` is `t log(2t/(1+t)) + (1 - t)/2`. -/
lemma lintegral_hockeyStick_kernel_mid1 {t : ℝ} (ht : 0 < t) :
    (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * ((1 + t) / 2) - t) 0 / s) ∂volume) +
    (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t - s * ((1 + t) / 2)) 0 / s) ∂volume) =
      ENNReal.ofReal (t * Real.log (2 * t / (1 + t)) + (1 - t) / 2) := by
  set c : ℝ := (1 + t) / 2
  have hc : 0 < c := by positivity
  have hc_ne : c ≠ 0 := ne_of_gt hc
  set r : ℝ := t / c
  have hr : 0 < r := div_pos ht hc
  have h1 := lintegral_hockeyStick_kernel_1 hr
  have hl : (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * c - t) 0 / s) ∂volume) =
      ENNReal.ofReal c * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s - r) 0 / s) ∂volume := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro s _; dsimp only
    rw [← ENNReal.ofReal_mul (le_of_lt hc)]
    congr 1
    have hmax : c * max (s - r) 0 = max (s * c - t) 0 := by
      rw [mul_max_of_nonneg _ _ (le_of_lt hc), mul_zero]
      congr 1; simp only [r]; field_simp [hc_ne]
    rw [← hmax]; ring
  have hrr : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t - s * c) 0 / s) ∂volume) =
      ENNReal.ofReal c * ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (r - s) 0 / s) ∂volume := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro s _; dsimp only
    rw [← ENNReal.ofReal_mul (le_of_lt hc)]
    congr 1
    have hmax : c * max (r - s) 0 = max (t - s * c) 0 := by
      rw [mul_max_of_nonneg _ _ (le_of_lt hc), mul_zero]
      congr 1; simp only [r]; field_simp [hc_ne]
    rw [← hmax]; ring
  rw [hl, hrr, ← mul_add, h1, ← ENNReal.ofReal_mul (le_of_lt hc)]
  congr 1
  have h1t : 1 + t ≠ 0 := by linarith
  have hr_eq : r = 2 * t / (1 + t) := by simp only [r, c]; field_simp [h1t]
  rw [hr_eq]
  have hcr : c * (2 * t / (1 + t)) = t := by simp only [c]; field_simp [h1t]
  have h1c : c * (2 * t / (1 + t) - 1) = (t - 1) / 2 := by
    simp only [c]; field_simp [h1t]; ring
  calc c * (2 * t / (1 + t) * Real.log (2 * t / (1 + t)) - (2 * t / (1 + t) - 1))
      = (c * (2 * t / (1 + t))) * Real.log (2 * t / (1 + t)) - c * (2 * t / (1 + t) - 1) := by ring
    _ = t * Real.log (2 * t / (1 + t)) + (1 - t) / 2 := by rw [hcr, h1c]; ring

/-- For `t > 0`: midpoint kernel integral for `D(σ ‖ m)` is `log(2/(1+t)) + (t - 1)/2`. -/
lemma lintegral_hockeyStick_kernel_mid2 {t : ℝ} (ht : 0 < t) :
    (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * ((1 + t) / 2) - 1) 0 / s) ∂volume) +
    (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (1 - s * ((1 + t) / 2)) 0 / s) ∂volume) =
      ENNReal.ofReal (Real.log (2 / (1 + t)) + (t - 1) / 2) := by
  set c : ℝ := (1 + t) / 2
  have hc : 0 < c := by positivity
  have hc_ne : c ≠ 0 := ne_of_gt hc
  set r : ℝ := 1 / c
  have hr : 0 < r := div_pos one_pos hc
  have h1 := lintegral_hockeyStick_kernel_1 hr
  have hl : (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * c - 1) 0 / s) ∂volume) =
      ENNReal.ofReal c * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s - r) 0 / s) ∂volume := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro s _; dsimp only
    rw [← ENNReal.ofReal_mul (le_of_lt hc)]
    congr 1
    have hmax : c * max (s - r) 0 = max (s * c - 1) 0 := by
      rw [mul_max_of_nonneg _ _ (le_of_lt hc), mul_zero]
      congr 1; simp only [r]; field_simp [hc_ne]
    rw [← hmax]; ring
  have hrr : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (1 - s * c) 0 / s) ∂volume) =
      ENNReal.ofReal c * ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (r - s) 0 / s) ∂volume := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro s _; dsimp only
    rw [← ENNReal.ofReal_mul (le_of_lt hc)]
    congr 1
    have hmax : c * max (r - s) 0 = max (1 - s * c) 0 := by
      rw [mul_max_of_nonneg _ _ (le_of_lt hc), mul_zero]
      congr 1; simp only [r]; field_simp [hc_ne]
    rw [← hmax]; ring
  rw [hl, hrr, ← mul_add, h1, ← ENNReal.ofReal_mul (le_of_lt hc)]
  congr 1
  have h1t : 1 + t ≠ 0 := by linarith
  have hr_eq : r = 2 / (1 + t) := by simp only [r, c]; field_simp [h1t]
  rw [hr_eq]
  have hcr : c * (2 / (1 + t)) = 1 := by simp only [c]; field_simp [h1t]
  have h1c : c * (2 / (1 + t) - 1) = (1 - t) / 2 := by
    simp only [c]; field_simp [h1t]; ring
  calc c * (2 / (1 + t) * Real.log (2 / (1 + t)) - (2 / (1 + t) - 1))
      = (c * (2 / (1 + t))) * Real.log (2 / (1 + t)) - c * (2 / (1 + t) - 1) := by ring
    _ = Real.log (2 / (1 + t)) + (t - 1) / 2 := by rw [hcr, h1c]; ring

/-! ### Part 5: Lemma 3.2 — Simultaneous Hockey-Stick Representation -/

/-- Hockey-stick symmetry identity: for `s > 0`,
`E_s(σ ‖ ρ) = s * E_{1/s}(ρ ‖ σ) + (1 - s)`. -/
lemma hockeyStick_swap (ρ σ : DensityOp d) {s : ℝ} (hs : 0 < s) :
    hockeyStick s σ ρ = s * hockeyStick (1 / s) ρ σ + (1 - s) := by
  rw [hockeyStick_eq_posPartTrace, hockeyStick_eq_posPartTrace]
  have hsub := posPartTrace_sub_negPartTrace (hockeyStick_isHermitian s σ ρ)
  have htr : (σ.mat - (s : ℂ) • ρ.mat).trace.re = 1 - s := by
    rw [Matrix.trace_sub, Matrix.trace_smul, σ.trace_one, ρ.trace_one, smul_eq_mul, mul_one]; simp
  have hneg : negPartTrace (hockeyStick_isHermitian s σ ρ) =
      s * posPartTrace (hockeyStick_isHermitian (1 / s) ρ σ) := by
    rw [negPartTrace_eq_posPartTrace_neg]
    have hmat : -(σ.mat - (s : ℂ) • ρ.mat) = (s : ℂ) • (ρ.mat - ((1 / s : ℝ) : ℂ) • σ.mat) := by
      ext i j
      simp only [Matrix.neg_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
      push_cast; field_simp [hsC]; ring
    have hsc : ((s : ℂ) • (ρ.mat - ((1 / s : ℝ) : ℂ) • σ.mat)).IsHermitian := by
      rw [← hmat]; exact (hockeyStick_isHermitian s σ ρ).neg
    rw [posPartTrace_eq_of_eq _ hsc hmat, posPartTrace_smul_nonneg (le_of_lt hs)]
  linarith

/-- Midpoint hockey-stick identity (Eq. 3.9): for `s ∈ (0, 2)`,
`E_s(ρ ‖ m) = (1 - s/2) E_{s/(2-s)}(ρ ‖ σ)` and for `s ≥ 2`, `E_s(ρ ‖ m) = 0`. -/
lemma hockeyStick_midpoint_left (ρ σ : DensityOp d) {s : ℝ} (hs0 : 0 < s) :
    hockeyStick s ρ (DensityOp.midpoint ρ σ) =
      if s < 2 then (1 - s / 2) * hockeyStick (s / (2 - s)) ρ σ else 0 := by
  split_ifs with hs2
  · have hc : 0 < 1 - s / 2 := by linarith
    have hmat : ρ.mat - (s : ℂ) • (DensityOp.midpoint ρ σ).mat =
        (((1 - s / 2 : ℝ) : ℂ) • (ρ.mat - ((s / (2 - s) : ℝ) : ℂ) • σ.mat)) := by
      ext i j
      simp only [DensityOp.midpoint, DensityOp.mix, Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
      have hne : (2 : ℂ) - (s : ℂ) ≠ 0 := by exact_mod_cast (by linarith : 2 - s ≠ 0)
      push_cast; field_simp [hne]; ring
    rw [hockeyStick_eq_posPartTrace, hockeyStick_eq_posPartTrace]
    have hsc : (((1 - s / 2 : ℝ) : ℂ) • (ρ.mat - ((s / (2 - s) : ℝ) : ℂ) • σ.mat)).IsHermitian := by
      rw [← hmat]; exact hockeyStick_isHermitian s ρ (DensityOp.midpoint ρ σ)
    rw [posPartTrace_eq_of_eq _ hsc hmat, posPartTrace_smul_nonneg (le_of_lt hc)]
  · push Not at hs2
    -- `ρ - s * (ρ + σ)/2 = -((s/2 - 1) ρ + (s/2) σ) ≼ 0`
    have hpsd : (-((ρ.mat - (s : ℂ) • (DensityOp.midpoint ρ σ).mat))).PosSemidef := by
      have hmat : -(ρ.mat - (s : ℂ) • (DensityOp.midpoint ρ σ).mat) =
          (((s / 2 - 1 : ℝ) : ℂ) • ρ.mat + ((s / 2 : ℝ) : ℂ) • σ.mat) := by
        ext i j
        simp only [DensityOp.midpoint, DensityOp.mix, Matrix.neg_apply, Matrix.sub_apply,
          Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
        push_cast; ring
      rw [hmat]
      have h1 : (((s / 2 - 1 : ℝ) : ℂ) • ρ.mat).PosSemidef := by
        rw [Matrix.posSemidef_iff_dotProduct_mulVec]
        refine ⟨?_, fun x ↦ ?_⟩
        · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
            ρ.isHermitian.eq]
        · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
          exact mul_nonneg (by exact_mod_cast (by linarith : 0 ≤ s / 2 - 1))
            ((Matrix.posSemidef_iff_dotProduct_mulVec.mp ρ.posSemidef).2 x)
      have h2 : (((s / 2 : ℝ) : ℂ) • σ.mat).PosSemidef := by
        rw [Matrix.posSemidef_iff_dotProduct_mulVec]
        refine ⟨?_, fun x ↦ ?_⟩
        · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
            σ.isHermitian.eq]
        · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
          exact mul_nonneg (by exact_mod_cast (by linarith : 0 ≤ s / 2))
            ((Matrix.posSemidef_iff_dotProduct_mulVec.mp σ.posSemidef).2 x)
      exact h1.add h2
    rw [hockeyStick_eq_posPartTrace]
    have hneg0 : negPartTrace (hockeyStick_isHermitian s ρ (DensityOp.midpoint ρ σ)).neg = 0 := by
      unfold negPartTrace
      apply Finset.sum_eq_zero; intro i _
      exact max_eq_right (by linarith [hpsd.eigenvalues_nonneg i])
    rw [negPartTrace_eq_posPartTrace_neg] at hneg0
    rw [posPartTrace_eq_of_eq (hockeyStick_isHermitian s ρ (DensityOp.midpoint ρ σ)) _ (neg_neg _).symm]
    exact hneg0

end PolarCodes
