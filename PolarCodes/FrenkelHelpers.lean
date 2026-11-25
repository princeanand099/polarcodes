/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import PolarCodes.SpectralTrace

/-!
# Helper Lemmas for Frenkel's Integral Formula

Proves the layer-cake identity for `negEigCount`, the elementary 1D rational-fraction integral,
and measurability of `negEigCount` on the Hermitian pencil `(1 - t) ρ + t σ + r I`.
-/

open Matrix BigOperators Real Set Filter Topology MeasureTheory
open scoped ComplexOrder ENNReal

namespace PolarCodes

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-! ### Layer-Cake Formula and Elementary Rational-Fraction Integrals -/

lemma tendsto_setLIntegral_monotone {s : ℕ → Set ℝ} (hs_mono : Monotone s)
    (hs_meas : ∀ n, MeasurableSet (s n)) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Tendsto (fun n ↦ ∫⁻ x in s n, f x ∂volume) atTop
      (𝓝 (∫⁻ x in ⋃ n, s n, f x ∂volume)) := by
  have hrew : ∀ n, ∫⁻ x in s n, f x ∂volume = ∫⁻ x, (s n).indicator f x ∂volume :=
    fun n ↦ (lintegral_indicator (hs_meas n) f).symm
  have hunion : ∫⁻ x in ⋃ n, s n, f x ∂volume = ∫⁻ x, (⋃ n, s n).indicator f x ∂volume :=
    (lintegral_indicator (MeasurableSet.iUnion hs_meas) f).symm
  simp_rw [hrew, hunion]
  have hind_mono : Monotone (fun n ↦ (s n).indicator f) := by
    intro m n hmn x
    simp only [Set.indicator]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (hs_mono hmn h1) h2
    · exact bot_le
    · exact le_rfl
  have hsup : (⋃ n, s n).indicator f = fun x ↦ ⨆ n, (s n).indicator f x := by
    ext x
    simp only [Set.indicator]
    split_ifs with hx
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      apply le_antisymm
      · exact le_iSup_of_le n (by simp [hn])
      · refine iSup_le fun m ↦ ?_; split_ifs <;> simp
    · symm
      apply le_antisymm _ bot_le
      refine iSup_le fun n ↦ ?_
      have hn : x ∉ s n := fun h ↦ hx (Set.mem_iUnion.mpr ⟨n, h⟩)
      simp [hn]
  rw [hsup, lintegral_iSup (fun n ↦ hf.indicator (hs_meas n)) hind_mono]
  exact tendsto_atTop_iSup (fun m n hmn ↦ lintegral_mono (hind_mono hmn))

lemma lintegral_negEigCount_eq_negPartTrace {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    ∫⁻ r in Ioi (0 : ℝ),
      (negEigCount (hA.add (show ((r : ℂ) • (1 : Matrix d d ℂ)).IsHermitian by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          Complex.star_def, Complex.conj_ofReal])) : ℝ≥0∞) ∂volume =
      ENNReal.ofReal (negPartTrace hA) := by
  have heig_shift : ∀ r : ℝ,
      negEigCount (hA.add (show ((r : ℂ) • (1 : Matrix d d ℂ)).IsHermitian by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          Complex.star_def, Complex.conj_ofReal])) =
      (Finset.univ.filter fun i : d ↦ hA.eigenvalues i + r < 0).card := by
    intro r
    set hAr := hA.add (show ((r : ℂ) • (1 : Matrix d d ℂ)).IsHermitian by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
        Complex.star_def, Complex.conj_ofReal])
    set U : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
    have hU_mul : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    have hU_star : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    let lam : d → ℝ := fun i ↦ hA.eigenvalues i + r
    have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext i; simp
    have hspec : A = U * Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) * star U := by
      simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
    have hAr_eq : A + (r : ℂ) • (1 : Matrix d d ℂ) =
        U * Matrix.diagonal (Complex.ofReal ∘ lam) * star U := by
      have h1 : (r : ℂ) • (1 : Matrix d d ℂ) = U * Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star U := by
        have hdiag : Matrix.diagonal (fun _ : d ↦ (r : ℂ)) = (r : ℂ) • (1 : Matrix d d ℂ) := by
          ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]
        rw [hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU_mul]
      rw [hspec, h1, ← Matrix.add_mul, ← Matrix.mul_add]
      congr 2; ext i j
      simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply, lam]
      split_ifs
      · push_cast; ring
      · simp
    have hcp : (A + (r : ℂ) • 1).charpoly = (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
      rw [hAr_eq, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU_star, Matrix.one_mul]
    have hsum := spectral_sum_eq_of_charpoly_mul_X_pow hAr hD_herm (k := 0) (l := 0)
      (by rw [pow_zero, mul_one, mul_one, hcp]) (f := fun x : ℝ ↦ if x < 0 then (1 : ℝ) else 0) (by simp)
    have hsum2 := spectral_sum_diagonal lam hD_herm (f := fun x : ℝ ↦ if x < 0 then (1 : ℝ) else 0) (by simp)
    rw [hsum2] at hsum
    simp only [Finset.sum_boole] at hsum
    exact_mod_cast hsum
  have hcast : ∀ r : ℝ,
      (negEigCount (hA.add (show ((r : ℂ) • (1 : Matrix d d ℂ)).IsHermitian by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          Complex.star_def, Complex.conj_ofReal])) : ℝ≥0∞) =
      ∑ i : d, Set.indicator (Iio (-hA.eigenvalues i)) (fun _ ↦ (1 : ℝ≥0∞)) r := by
    intro r
    rw [heig_shift r, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl; intro i _
    simp only [Set.indicator, Set.mem_Iio]
    by_cases h : hA.eigenvalues i + r < 0
    · have h' : r < -hA.eigenvalues i := by linarith
      simp [h, h']
    · have h' : ¬ r < -hA.eigenvalues i := by linarith
      simp [h, h']
  simp_rw [hcast]
  rw [lintegral_finset_sum _ (fun i _ ↦ Measurable.indicator measurable_const measurableSet_Iio)]
  unfold negPartTrace
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ le_max_right _ _)]
  apply Finset.sum_congr rfl; intro i _
  rw [lintegral_indicator measurableSet_Iio, MeasureTheory.setLIntegral_one,
    Measure.restrict_apply measurableSet_Iio, Set.inter_comm]
  show volume (Ioi (0 : ℝ) ∩ Iio (-hA.eigenvalues i)) = ENNReal.ofReal (max (-hA.eigenvalues i) 0)
  rw [show Ioi (0 : ℝ) ∩ Iio (-hA.eigenvalues i) = Ioo (0 : ℝ) (-hA.eigenvalues i) from rfl,
    Real.volume_Ioo, sub_zero]
  rcases le_or_gt (-hA.eigenvalues i) 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_left (le_of_lt h)]

/-- Elementary rational-fraction Lebesgue integral for `λ > -1`:
`∫⁻ t, 1_{1 + t λ < 0} / (|t| (t - 1)²) dt = log(1 + λ) - λ / (1 + λ)`. -/
lemma lintegral_indicator_inv_abs_mul_sq_sub_one {lam : ℝ} (hlam : -1 < lam) :
    ∫⁻ t : ℝ, (if 1 + t * lam < 0 then ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) else 0) ∂volume =
      ENNReal.ofReal (Real.log (1 + lam) - lam / (1 + lam)) := by
  have h1pl : 0 < 1 + lam := by linarith
  rcases lt_trichotomy lam 0 with hneg | rfl | hpos
  · set c : ℝ := -1 / lam
    have hc1 : 1 < c := by
      simp only [c]; rw [one_lt_div_of_neg hneg]; linarith
    have heq_set : (fun t : ℝ ↦ if 1 + t * lam < 0 then ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) else 0) =
        Set.indicator (Ioi c) (fun t : ℝ ↦ ENNReal.ofReal (1 / (t * (t - 1) ^ 2))) := by
      ext t
      simp only [Set.indicator, Set.mem_Ioi]
      have hiff : 1 + t * lam < 0 ↔ c < t := by
        simp only [c]; rw [div_lt_iff_of_neg hneg]; constructor <;> intro h <;> linarith
      by_cases h : c < t
      · rw [if_pos (hiff.mpr h), if_pos h, abs_of_pos (by linarith)]
      · rw [if_neg (mt hiff.mp h), if_neg h]
    rw [heq_set, lintegral_indicator measurableSet_Ioi]
    let g : ℝ → ℝ := fun t ↦ Real.log (t / (t - 1)) - 1 / (t - 1)
    have hg_deriv : ∀ t > (1 : ℝ), HasDerivAt g (1 / (t * (t - 1) ^ 2)) t := by
      intro t ht
      have htm1 : 0 < t - 1 := by linarith
      have ht0 : 0 < t := by linarith
      have hq : HasDerivAt (fun s : ℝ ↦ s / (s - 1)) (-1 / (t - 1) ^ 2) t := by
        have h1 : HasDerivAt (fun s : ℝ ↦ s - 1) 1 t := (hasDerivAt_id' t).sub_const 1
        convert (hasDerivAt_id' t).fun_div h1 (ne_of_gt htm1) using 1; ring
      have hlog : HasDerivAt (fun s : ℝ ↦ Real.log (s / (s - 1)))
          ((-1 / (t - 1) ^ 2) / (t / (t - 1))) t :=
        hq.log (ne_of_gt (div_pos ht0 htm1))
      have hinv : HasDerivAt (fun s : ℝ ↦ 1 / (s - 1)) (-1 / (t - 1) ^ 2) t := by
        have h1 : HasDerivAt (fun s : ℝ ↦ s - 1) 1 t := (hasDerivAt_id' t).sub_const 1
        convert (hasDerivAt_const t (1 : ℝ)).fun_div h1 (ne_of_gt htm1) using 1; ring
      convert hlog.fun_sub hinv using 1
      field_simp [ne_of_gt ht0, ne_of_gt htm1]; ring
    have hg_tendsto : Tendsto g atTop (𝓝 0) := by
      have hsub_atTop : Tendsto (fun t : ℝ ↦ t - 1) atTop atTop := by
        simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
      have hinv : Tendsto (fun t : ℝ ↦ 1 / (t - 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hsub_atTop
      have h1 : Tendsto (fun t : ℝ ↦ t / (t - 1)) atTop (𝓝 1) := by
        have hrew : ∀ᶠ t : ℝ in atTop, t / (t - 1) = 1 + 1 / (t - 1) := by
          filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
          field_simp [ne_of_gt (by linarith : 0 < t - 1)]; ring
        rw [tendsto_congr' hrew]
        simpa using tendsto_const_nhds.add hinv
      have h2 : Tendsto (fun t : ℝ ↦ Real.log (t / (t - 1))) atTop (𝓝 0) := by
        change Tendsto (Real.log ∘ fun t : ℝ ↦ t / (t - 1)) atTop (𝓝 0)
        simpa [Real.log_one] using (Real.continuousAt_log one_ne_zero).tendsto.comp h1
      simpa [g, one_div] using h2.sub hinv
    have hunion : Ioi c = ⋃ n : ℕ, Ioc c (c + (n : ℝ) + 1) := by
      ext t; simp only [mem_Ioi, mem_iUnion, mem_Ioc]
      constructor
      · intro ht
        obtain ⟨n, hn⟩ := exists_nat_gt (t - c)
        exact ⟨n, ht, by linarith⟩
      · rintro ⟨n, h1, _⟩; exact h1
    have hmono_sets : Monotone (fun n : ℕ ↦ Ioc c (c + (n : ℝ) + 1)) := by
      intro m n hmn t ⟨h1, h2⟩
      exact ⟨h1, by linarith [show (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmn]⟩
    have hlim_int : Tendsto (fun n : ℕ ↦ ∫⁻ t in Ioc c (c + (n : ℝ) + 1),
        ENNReal.ofReal (1 / (t * (t - 1) ^ 2)) ∂volume) atTop
        (𝓝 (∫⁻ t in Ioi c, ENNReal.ofReal (1 / (t * (t - 1) ^ 2)) ∂volume)) := by
      rw [hunion]
      exact tendsto_setLIntegral_monotone hmono_sets (fun _ ↦ measurableSet_Ioc)
        (ENNReal.measurable_ofReal.comp (measurable_const.div
          (measurable_id.mul ((measurable_id.sub measurable_const).pow_const 2))))
    have hval_n : ∀ n : ℕ, ∫⁻ t in Ioc c (c + (n : ℝ) + 1),
        ENNReal.ofReal (1 / (t * (t - 1) ^ 2)) ∂volume =
        ENNReal.ofReal (g (c + (n : ℝ) + 1) - g c) := by
      intro n
      have hle : c ≤ c + (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hcont : ContinuousOn (fun t : ℝ ↦ 1 / (t * (t - 1) ^ 2)) (Icc c (c + (n : ℝ) + 1)) := by
        intro t ht
        have ht1 : 1 < t := lt_of_lt_of_le hc1 ht.1
        have hne : t * (t - 1) ^ 2 ≠ 0 := mul_ne_zero (by linarith) (pow_ne_zero 2 (by linarith))
        exact (continuousAt_const.div (continuousAt_id.mul ((continuousAt_id.sub continuousAt_const).pow 2)) hne).continuousWithinAt
      have hint : IntervalIntegrable (fun t : ℝ ↦ 1 / (t * (t - 1) ^ 2)) volume c (c + (n : ℝ) + 1) :=
        hcont.intervalIntegrable_of_Icc hle
      have hftc : ∫ t in c..(c + (n : ℝ) + 1), (1 / (t * (t - 1) ^ 2)) = g (c + (n : ℝ) + 1) - g c := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
        intro t ht
        rw [uIcc_of_le hle] at ht
        exact hg_deriv t (lt_of_lt_of_le hc1 ht.1)
      rw [← hftc, intervalIntegral.integral_of_le hle,
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint.1]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := by linarith [ht.1]
      positivity
    have hlim_rhs : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (g (c + (n : ℝ) + 1) - g c)) atTop
        (𝓝 (ENNReal.ofReal (0 - g c))) := by
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      have harg : Tendsto (fun n : ℕ ↦ c + (n : ℝ) + 1) atTop atTop :=
        Filter.tendsto_atTop_add_const_right atTop (1 : ℝ)
          (Filter.tendsto_atTop_add_const_left atTop c tendsto_natCast_atTop_atTop)
      exact (hg_tendsto.comp harg).sub tendsto_const_nhds
    simp_rw [hval_n] at hlim_int
    have hres := tendsto_nhds_unique hlim_int hlim_rhs
    rw [hres]
    congr 1
    have hcm1 : c - 1 = -(1 + lam) / lam := by simp only [c]; field_simp [ne_of_lt hneg]; ring
    have hdiv1 : c / (c - 1) = (1 + lam)⁻¹ := by
      rw [hcm1]; simp only [c]; field_simp [ne_of_lt hneg, ne_of_gt h1pl]
    have hdiv2 : 1 / (c - 1) = -lam / (1 + lam) := by
      rw [hcm1]; field_simp [ne_of_lt hneg, ne_of_gt h1pl]
    simp only [g, hdiv1, hdiv2, Real.log_inv]
    ring
  · simp [Real.log_one, show ¬(1 : ℝ) < 0 by norm_num]
  · set c : ℝ := -1 / lam
    have hc0 : c < 0 := by simp only [c]; exact div_neg_of_neg_of_pos (by norm_num) hpos
    have heq_set : (fun t : ℝ ↦ if 1 + t * lam < 0 then ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) else 0) =
        Set.indicator (Iio c) (fun t : ℝ ↦ ENNReal.ofReal (1 / ((-t) * (1 - t) ^ 2))) := by
      ext t
      simp only [Set.indicator, Set.mem_Iio]
      have hiff : 1 + t * lam < 0 ↔ t < c := by
        simp only [c]; rw [lt_div_iff₀ hpos]; constructor <;> intro h <;> linarith
      by_cases h : t < c
      · rw [if_pos (hiff.mpr h), if_pos h, abs_of_neg (lt_trans h hc0)]
        have hsq : (t - 1) ^ 2 = (1 - t) ^ 2 := by ring
        rw [hsq]
      · rw [if_neg (mt hiff.mp h), if_neg h]
    rw [heq_set, lintegral_indicator measurableSet_Iio]
    let g : ℝ → ℝ := fun t ↦ -Real.log ((-t) / (1 - t)) - 1 / (1 - t)
    have hg_deriv : ∀ t < (0 : ℝ), HasDerivAt g (1 / ((-t) * (1 - t) ^ 2)) t := by
      intro t ht
      have hmt : 0 < -t := by linarith
      have h1mt : 0 < 1 - t := by linarith
      have hq : HasDerivAt (fun s : ℝ ↦ (-s) / (1 - s)) (-1 / (1 - t) ^ 2) t := by
        have h1 : HasDerivAt (fun s : ℝ ↦ -s) (-1) t := (hasDerivAt_id' t).neg
        have h2 : HasDerivAt (fun s : ℝ ↦ 1 - s) (-1) t := by
          simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id' t)
        convert h1.fun_div h2 (ne_of_gt h1mt) using 1; ring
      have hlog : HasDerivAt (fun s : ℝ ↦ -Real.log ((-s) / (1 - s)))
          (-((-1 / (1 - t) ^ 2) / ((-t) / (1 - t)))) t :=
        (hq.log (ne_of_gt (div_pos hmt h1mt))).neg
      have hinv : HasDerivAt (fun s : ℝ ↦ 1 / (1 - s)) (1 / (1 - t) ^ 2) t := by
        have h2 : HasDerivAt (fun s : ℝ ↦ 1 - s) (-1) t := by
          simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id' t)
        convert (hasDerivAt_const t (1 : ℝ)).fun_div h2 (ne_of_gt h1mt) using 1; ring
      convert hlog.fun_sub hinv using 1
      field_simp [ne_of_lt ht, ne_of_gt h1mt]; ring
    have hg_tendsto : Tendsto g atBot (𝓝 0) := by
      have h1mt : Tendsto (fun t : ℝ ↦ 1 - t) atBot atTop := by
        simpa [sub_eq_add_neg] using
          Filter.tendsto_atTop_add_const_left atBot (1 : ℝ) tendsto_neg_atBot_atTop
      have hinv : Tendsto (fun t : ℝ ↦ 1 / (1 - t)) atBot (𝓝 0) :=
        tendsto_const_nhds.div_atTop h1mt
      have h1 : Tendsto (fun t : ℝ ↦ (-t) / (1 - t)) atBot (𝓝 1) := by
        have hrew : ∀ᶠ t : ℝ in atBot, (-t) / (1 - t) = 1 - 1 / (1 - t) := by
          filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
          field_simp [ne_of_gt (by linarith : 0 < 1 - t)]; ring
        rw [tendsto_congr' hrew]
        simpa using tendsto_const_nhds.sub hinv
      have h2 : Tendsto (fun t : ℝ ↦ -Real.log ((-t) / (1 - t))) atBot (𝓝 0) := by
        have h2' : Tendsto (Real.log ∘ fun t : ℝ ↦ (-t) / (1 - t)) atBot (𝓝 0) := by
          simpa [Real.log_one] using (Real.continuousAt_log one_ne_zero).tendsto.comp h1
        simpa using h2'.neg
      simpa [g, one_div] using h2.sub hinv
    have hunion : Iio c = ⋃ n : ℕ, Ioo (c - (n : ℝ) - 1) c := by
      ext t; simp only [mem_Iio, mem_iUnion, mem_Ioo]
      constructor
      · intro ht
        obtain ⟨n, hn⟩ := exists_nat_gt (c - t)
        exact ⟨n, by linarith, ht⟩
      · rintro ⟨n, _, h2⟩; exact h2
    have hmono_sets : Monotone (fun n : ℕ ↦ Ioo (c - (n : ℝ) - 1) c) := by
      intro m n hmn t ⟨h1, h2⟩
      exact ⟨by linarith [show (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmn], h2⟩
    have hlim_int : Tendsto (fun n : ℕ ↦ ∫⁻ t in Ioo (c - (n : ℝ) - 1) c,
        ENNReal.ofReal (1 / ((-t) * (1 - t) ^ 2)) ∂volume) atTop
        (𝓝 (∫⁻ t in Iio c, ENNReal.ofReal (1 / ((-t) * (1 - t) ^ 2)) ∂volume)) := by
      rw [hunion]
      exact tendsto_setLIntegral_monotone hmono_sets (fun _ ↦ measurableSet_Ioo)
        (ENNReal.measurable_ofReal.comp (measurable_const.div
          (measurable_id.neg.mul ((measurable_const.sub measurable_id).pow_const 2))))
    have hval_n : ∀ n : ℕ, ∫⁻ t in Ioo (c - (n : ℝ) - 1) c,
        ENNReal.ofReal (1 / ((-t) * (1 - t) ^ 2)) ∂volume =
        ENNReal.ofReal (g c - g (c - (n : ℝ) - 1)) := by
      intro n
      have hle : c - (n : ℝ) - 1 ≤ c := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hcont : ContinuousOn (fun t : ℝ ↦ 1 / ((-t) * (1 - t) ^ 2)) (Icc (c - (n : ℝ) - 1) c) := by
        intro t ht
        have ht0 : t < 0 := lt_of_le_of_lt ht.2 hc0
        have hne : (-t) * (1 - t) ^ 2 ≠ 0 := mul_ne_zero (by linarith) (pow_ne_zero 2 (by linarith))
        exact (continuousAt_const.div (continuousAt_id.neg.mul ((continuousAt_const.sub continuousAt_id).pow 2)) hne).continuousWithinAt
      have hint : IntervalIntegrable (fun t : ℝ ↦ 1 / ((-t) * (1 - t) ^ 2)) volume (c - (n : ℝ) - 1) c :=
        hcont.intervalIntegrable_of_Icc hle
      have hftc : ∫ t in (c - (n : ℝ) - 1)..c, (1 / ((-t) * (1 - t) ^ 2)) = g c - g (c - (n : ℝ) - 1) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
        intro t ht
        rw [uIcc_of_le hle] at ht
        exact hg_deriv t (lt_of_le_of_lt ht.2 hc0)
      rw [← hftc, intervalIntegral.integral_of_le hle,
        MeasureTheory.integral_Ioc_eq_integral_Ioo,
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint.1.mono_set Ioo_subset_Ioc_self)]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < -t := by linarith [ht.2]
      have h1mt : 0 < 1 - t := by linarith [ht.2]
      positivity
    have hlim_rhs : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (g c - g (c - (n : ℝ) - 1))) atTop
        (𝓝 (ENNReal.ofReal (g c - 0))) := by
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      have hbot : Tendsto (fun n : ℕ ↦ c - (n : ℝ) - 1) atTop atBot := by
        have hneg_nat : Tendsto (fun n : ℕ ↦ -(n : ℝ)) atTop atBot :=
          tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
        have h1 : Tendsto (fun n : ℕ ↦ c + -(n : ℝ)) atTop atBot :=
          Filter.tendsto_atBot_add_const_left atTop c hneg_nat
        have h2 : Tendsto (fun n : ℕ ↦ (c + -(n : ℝ)) + (-1 : ℝ)) atTop atBot :=
          Filter.tendsto_atBot_add_const_right atTop (-1 : ℝ) h1
        simpa [sub_eq_add_neg] using h2
      exact tendsto_const_nhds.sub (hg_tendsto.comp hbot)
    simp_rw [hval_n] at hlim_int
    have hres := tendsto_nhds_unique hlim_int hlim_rhs
    rw [hres]
    congr 1
    have h1mc : 1 - c = (1 + lam) / lam := by simp only [c]; field_simp [ne_of_gt hpos]; ring
    have hdiv1 : (-c) / (1 - c) = (1 + lam)⁻¹ := by
      rw [h1mc]; simp only [c]; field_simp [ne_of_gt hpos, ne_of_gt h1pl]
    have hdiv2 : 1 / (1 - c) = lam / (1 + lam) := by
      rw [h1mc]; field_simp [ne_of_gt hpos, ne_of_gt h1pl]
    simp only [g, hdiv1, hdiv2, Real.log_inv]
    ring

/-! ### Measurability of `negEigCount` on the Hermitian Pencil `(1 - t) ρ + t σ + r I` -/

lemma isHermitian_pencil (ρ σ : DensityOp d) (r t : ℝ) :
    (((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).IsHermitian := by
  have h1 : (((1 - t : ℝ) : ℂ) • ρ.mat).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, ρ.isHermitian.eq]
  have h2 : ((t : ℂ) • σ.mat).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, σ.isHermitian.eq]
  have h3 : ((r : ℂ) • (1 : Matrix d d ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_ofReal]
  exact (h1.add h2).add h3

/-- Upper level sets of `negEigCount` along `(r, t) ↦ (1 - t) ρ + t σ + r I` are open,
hence `(r, t) ↦ (negEigCount (...) : ℝ≥0∞)` is measurable. -/
lemma measurable_negEigCount_pencil (ρ σ : DensityOp d) :
    Measurable (fun p : ℝ × ℝ ↦ (negEigCount (isHermitian_pencil ρ σ p.1 p.2) : ℝ≥0∞)) := by
  have hnat : Measurable (fun p : ℝ × ℝ ↦ negEigCount (isHermitian_pencil ρ σ p.1 p.2)) := by
    have hopen : ∀ k : ℕ, IsOpen {p : ℝ × ℝ | k ≤ negEigCount (isHermitian_pencil ρ σ p.1 p.2)} := by
      intro k
      rw [Metric.isOpen_iff]
      intro p₀ hp₀
      by_cases hk : k = 0
      · exact ⟨1, one_pos, fun p _ ↦ by simp [hk]⟩
      set A₀ := ((1 - p₀.2 : ℝ) : ℂ) • ρ.mat + (p₀.2 : ℂ) • σ.mat + (p₀.1 : ℂ) • (1 : Matrix d d ℂ)
      have hA₀ := isHermitian_pencil ρ σ p₀.1 p₀.2
      set S := Finset.univ.filter (fun i : d ↦ hA₀.eigenvalues i < 0)
      have hS_card : k ≤ S.card := hp₀
      have hS_ne : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (Nat.pos_of_ne_zero hk) hS_card)
      obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image S (fun i ↦ -hA₀.eigenvalues i) hS_ne
      set δ : ℝ := -hA₀.eigenvalues i₀
      have hδ_pos : 0 < δ := by
        have := (Finset.mem_filter.mp hi₀).2; linarith
      set C : ℝ := (∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖) + 1
      have hC_pos : 0 < C := by
        have : 0 ≤ ∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖ :=
          Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg _
        linarith
      refine ⟨δ / (2 * C), div_pos hδ_pos (by positivity), fun p hp ↦ ?_⟩
      have hp1 : |p.1 - p₀.1| < δ / (2 * C) :=
        lt_of_le_of_lt (le_trans (le_max_left _ _) (le_rfl)) (by simpa [Prod.dist_eq, Real.dist_eq] using hp)
      have hp2 : |p.2 - p₀.2| < δ / (2 * C) :=
        lt_of_le_of_lt (le_trans (le_max_right _ _) (le_rfl)) (by simpa [Prod.dist_eq, Real.dist_eq] using hp)
      let U : Matrix d d ℂ := (hA₀.eigenvectorUnitary : Matrix d d ℂ)
      have hU_mul : U * star U = 1 := Unitary.coe_mul_star_self hA₀.eigenvectorUnitary
      have hU_star : star U * U = 1 := Unitary.coe_star_mul_self hA₀.eigenvectorUnitary
      let v : d → (d → ℂ) := fun i j ↦ U j i
      let V : Submodule ℂ (d → ℂ) := Submodule.span ℂ (v '' (S : Set d))
      have hv_lin : LinearIndependent ℂ (fun i : S ↦ v i.1) := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have hUc : U.mulVec (fun i : d ↦ if h : i ∈ S then c ⟨i, h⟩ else 0) = 0 := by
          ext j
          simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
          have hcj := congr_fun hc j
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at hcj
          trans ∑ i : d, if h : i ∈ S then U j i * c ⟨i, h⟩ else 0
          · apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp
          · rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : d ↦ i ∈ S)]
            have hzero_not : ∑ i ∈ Finset.univ.filter (fun i : d ↦ ¬ i ∈ S),
                (if h : i ∈ S then U j i * c ⟨i, h⟩ else 0) = 0 := by
              apply Finset.sum_eq_zero; intro i hi
              simp [(Finset.mem_filter.mp hi).2]
            rw [hzero_not, add_zero, ← hcj]
            refine Finset.sum_bij (fun i hi ↦ (⟨i, (Finset.mem_filter.mp hi).2⟩ : S))
              (fun _ _ ↦ Finset.mem_univ _)
              (fun _ _ _ _ h ↦ congr_arg Subtype.val h)
              (fun b _ ↦ ⟨b.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, Subtype.ext rfl⟩)
              (fun i hi ↦ by simp [(Finset.mem_filter.mp hi).2, mul_comm])
        have hzero : (fun i : d ↦ if h : i ∈ S then c ⟨i, h⟩ else 0) = 0 := by
          have := congr_arg (Matrix.mulVec (star U)) hUc
          rw [Matrix.mulVec_mulVec, hU_star, Matrix.one_mulVec, Matrix.mulVec_zero] at this
          exact this
        intro ⟨i, hi⟩
        have h := congr_fun hzero i
        dsimp only [Pi.zero_apply] at h
        rw [dif_pos hi] at h
        exact h
      have hdimV : Module.finrank ℂ V = S.card := by
        have hrange : V = Submodule.span ℂ (Set.range (fun i : S ↦ v i.1)) := by
          show Submodule.span ℂ (v '' (S : Set d)) = _
          congr 1; ext x
          simp only [Set.mem_image, Finset.mem_coe, Set.mem_range, Subtype.exists, exists_prop]
        rw [hrange, finrank_span_eq_card hv_lin, Fintype.card_coe]
      have hneg : ∀ x ∈ V, x ≠ 0 →
          (star x ⬝ᵥ (((1 - p.2 : ℝ) : ℂ) • ρ.mat + (p.2 : ℂ) • σ.mat +
            (p.1 : ℂ) • (1 : Matrix d d ℂ)).mulVec x).re < 0 := by
        intro x hx hx0
        have hA₀_le : (star x ⬝ᵥ A₀.mulVec x).re ≤ -δ * ∑ i : d, ‖x i‖ ^ 2 := by
          rw [re_quadForm_spectral hA₀ x]
          have horth : ∀ i : d, i ∉ S → ((star U).mulVec x) i = 0 := by
            intro i hi
            have hmem : x ∈ Submodule.span ℂ (v '' (S : Set d)) := hx
            refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
            · rintro _ ⟨j, hj, rfl⟩
              have hne : i ≠ j := fun h ↦ hi (h ▸ hj)
              have hu := congr_fun (congr_fun hU_star i) j
              simpa [Matrix.mulVec, Matrix.mul_apply, dotProduct, v, Matrix.one_apply, hne] using hu
            · simp
            · intro y z _ _ hy hz; rw [Matrix.mulVec_add, Pi.add_apply, hy, hz, add_zero]
            · intro a y _ hy; rw [Matrix.mulVec_smul, Pi.smul_apply, hy, smul_zero]
          have hnorm_eq : ∑ i : d, ‖((star U).mulVec x) i‖ ^ 2 = ∑ i : d, ‖x i‖ ^ 2 := by
            have h1 : star ((star U).mulVec x) ⬝ᵥ ((star U).mulVec x) = star x ⬝ᵥ x := by
              have hstar_vec : star ((star U).mulVec x) = (star x) ᵥ* U := by
                ext i
                simp only [Pi.star_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, star_sum,
                  star_mul', Matrix.star_apply, star_star]
                apply Finset.sum_congr rfl; intro j _; ring
              rw [hstar_vec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU_mul, Matrix.vecMul_one]
            have hre := congr_arg Complex.re h1
            have hsum_sq : ∀ w : d → ℂ, (star w ⬝ᵥ w).re = ∑ i : d, ‖w i‖ ^ 2 := by
              intro w
              simp only [dotProduct, Pi.star_apply, Complex.re_sum]
              apply Finset.sum_congr rfl; intro i _
              rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
            rw [hsum_sq, hsum_sq] at hre
            exact hre
          rw [← hnorm_eq, Finset.mul_sum]
          apply Finset.sum_le_sum; intro i _
          by_cases hi : i ∈ S
          · have hle_i : hA₀.eigenvalues i ≤ -δ := by
              have := hmin i hi; linarith
            exact mul_le_mul_of_nonneg_right hle_i (sq_nonneg _)
          · rw [horth i hi]; simp
        have hdiff_mat : (((1 - p.2 : ℝ) : ℂ) • ρ.mat + (p.2 : ℂ) • σ.mat + (p.1 : ℂ) • (1 : Matrix d d ℂ)) - A₀ =
            ((p.2 - p₀.2 : ℝ) : ℂ) • (σ.mat - ρ.mat) + ((p.1 - p₀.1 : ℝ) : ℂ) • (1 : Matrix d d ℂ) := by
          ext i j; simp only [A₀, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
          push_cast; ring
        have hdiff_re : (star x ⬝ᵥ (((1 - p.2 : ℝ) : ℂ) • ρ.mat + (p.2 : ℂ) • σ.mat +
            (p.1 : ℂ) • (1 : Matrix d d ℂ)).mulVec x).re - (star x ⬝ᵥ A₀.mulVec x).re ≤
            (|p.2 - p₀.2| * (∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖) + |p.1 - p₀.1|) * (∑ i : d, ‖x i‖ ^ 2) := by
          have hsub : (star x ⬝ᵥ (((1 - p.2 : ℝ) : ℂ) • ρ.mat + (p.2 : ℂ) • σ.mat +
              (p.1 : ℂ) • (1 : Matrix d d ℂ)).mulVec x) - (star x ⬝ᵥ A₀.mulVec x) =
              ((p.2 - p₀.2 : ℝ) : ℂ) * (star x ⬝ᵥ (σ.mat - ρ.mat).mulVec x) +
              ((p.1 - p₀.1 : ℝ) : ℂ) * (star x ⬝ᵥ x) := by
            rw [← dotProduct_sub, ← Matrix.sub_mulVec, hdiff_mat, Matrix.add_mulVec,
              Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
              dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
          rw [← Complex.sub_re, hsub, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
          have hsum_sq : (star x ⬝ᵥ x).re = ∑ i : d, ‖x i‖ ^ 2 := by
            simp only [dotProduct, Pi.star_apply, Complex.re_sum]
            apply Finset.sum_congr rfl; intro i _
            rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
          rw [hsum_sq]
          have hterm1 : (p.2 - p₀.2) * (star x ⬝ᵥ (σ.mat - ρ.mat).mulVec x).re ≤
              |p.2 - p₀.2| * (∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖) * (∑ i : d, ‖x i‖ ^ 2) := by
            have hq_le : |(star x ⬝ᵥ (σ.mat - ρ.mat).mulVec x).re| ≤
                (∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖) * (∑ i : d, ‖x i‖ ^ 2) := by
              calc |(star x ⬝ᵥ (σ.mat - ρ.mat).mulVec x).re|
                  ≤ ‖star x ⬝ᵥ (σ.mat - ρ.mat).mulVec x‖ := Complex.abs_re_le_norm _
                _ ≤ ∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖ * (‖x i‖ * ‖x j‖) := by
                    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.sub_apply, Finset.mul_sum]
                    calc ‖∑ i : d, ∑ j : d, star (x i) * ((σ.mat i j - ρ.mat i j) * x j)‖
                        ≤ ∑ i : d, ‖∑ j : d, star (x i) * ((σ.mat i j - ρ.mat i j) * x j)‖ := norm_sum_le _ _
                      _ ≤ ∑ i : d, ∑ j : d, ‖star (x i) * ((σ.mat i j - ρ.mat i j) * x j)‖ :=
                          Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _
                      _ = ∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖ * (‖x i‖ * ‖x j‖) := by
                          apply Finset.sum_congr rfl; intro i _
                          apply Finset.sum_congr rfl; intro j _
                          simp only [norm_mul, norm_star]; ring
                _ ≤ ∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖ * (∑ k : d, ‖x k‖ ^ 2) := by
                    apply Finset.sum_le_sum; intro i _
                    apply Finset.sum_le_sum; intro j _
                    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                    have hab : ‖x i‖ * ‖x j‖ ≤ (‖x i‖ ^ 2 + ‖x j‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖x i‖ - ‖x j‖)]
                    have hi_le : ‖x i‖ ^ 2 ≤ ∑ k : d, ‖x k‖ ^ 2 :=
                      Finset.single_le_sum (fun k _ ↦ sq_nonneg ‖x k‖) (Finset.mem_univ i)
                    have hj_le : ‖x j‖ ^ 2 ≤ ∑ k : d, ‖x k‖ ^ 2 :=
                      Finset.single_le_sum (fun k _ ↦ sq_nonneg ‖x k‖) (Finset.mem_univ j)
                    linarith
                _ = (∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖) * (∑ k : d, ‖x k‖ ^ 2) := by
                    simp_rw [← Finset.sum_mul]
            calc (p.2 - p₀.2) * (star x ⬝ᵥ (σ.mat - ρ.mat).mulVec x).re
                ≤ |p.2 - p₀.2| * |(star x ⬝ᵥ (σ.mat - ρ.mat).mulVec x).re| := by
                  rw [← abs_mul]; exact le_abs_self _
              _ ≤ |p.2 - p₀.2| * ((∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖) * (∑ i : d, ‖x i‖ ^ 2)) :=
                  mul_le_mul_of_nonneg_left hq_le (abs_nonneg _)
              _ = _ := by ring
          have hterm2 : (p.1 - p₀.1) * (∑ i : d, ‖x i‖ ^ 2) ≤ |p.1 - p₀.1| * (∑ i : d, ‖x i‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
          linarith
        have hx_pos : 0 < ∑ i : d, ‖x i‖ ^ 2 := by
          obtain ⟨i, hi⟩ : ∃ i : d, x i ≠ 0 := by
            by_contra hall; push Not at hall; exact hx0 (funext hall)
          exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hi))
            (Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖x j‖) (Finset.mem_univ i))
        have hbound : |p.2 - p₀.2| * (∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖) + |p.1 - p₀.1| < δ := by
          have hsum_nn : 0 ≤ ∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖ :=
            Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg _
          have h1 : |p.2 - p₀.2| * (∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖) ≤
              (δ / (2 * C)) * (∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖) :=
            mul_le_mul_of_nonneg_right (le_of_lt hp2) hsum_nn
          have h2 : (δ / (2 * C)) * (∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖) + δ / (2 * C) = δ / 2 := by
            have hC_ne : C ≠ 0 := ne_of_gt hC_pos
            have : (∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖) + 1 = C := rfl
            calc (δ / (2 * C)) * (∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖) + δ / (2 * C)
                = (δ / (2 * C)) * ((∑ i : d, ∑ j : d, ‖σ.mat i j - ρ.mat i j‖) + 1) := by ring
              _ = (δ / (2 * C)) * C := by rw [this]
              _ = δ / 2 := by field_simp [hC_ne]
          linarith
        nlinarith
      exact le_trans hS_card (hdimV ▸ finrank_le_negEigCount (isHermitian_pencil ρ σ p.1 p.2) V hneg)
    refine measurable_to_countable' (fun k ↦ ?_)
    have heq : (fun p : ℝ × ℝ ↦ negEigCount (isHermitian_pencil ρ σ p.1 p.2)) ⁻¹' {k} =
        {p : ℝ × ℝ | k ≤ negEigCount (isHermitian_pencil ρ σ p.1 p.2)} \
        {p : ℝ × ℝ | k + 1 ≤ negEigCount (isHermitian_pencil ρ σ p.1 p.2)} := by
      ext p; simp only [mem_preimage, mem_singleton_iff, mem_diff, mem_setOf_eq]; omega
    rw [heq]
    exact (hopen k).measurableSet.diff (hopen (k + 1)).measurableSet
  exact measurable_from_top.comp hnat

end PolarCodes
