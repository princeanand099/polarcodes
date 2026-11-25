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
# Frenkel's Integral Formula (Theorem 6 / Eq. 3.7)

Proves the layer-cake identity for `negEigCount`, the elementary 1D partial-fraction integral,
measurability of `negEigCount` on the Hermitian pencil `(1 - t) ρ + t σ + r I`, and
**Frenkel's Integral Formula (Eq. 3.7)** (`relEntropy_frenkel_integral`) for full-rank states.
-/

open Matrix BigOperators Real Set Filter Topology MeasureTheory
open scoped ComplexOrder ENNReal

namespace PolarCodes

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-! ### Layer-Cake Formula and Elementary Partial-Fraction Integrals -/

private lemma tendsto_setLIntegral_monotone {s : ℕ → Set ℝ} (hs_mono : Monotone s)
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
    -- Use `spectral_sum_eq_of_charpoly_mul_X_pow` on `f(x) = if x < 0 then 1 else 0`
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

/-- Elementary partial-fraction Lebesgue integral for `λ > -1`:
`∫⁻ t, 1_{1 + t λ < 0} / (|t| (t - 1)²) dt = log(1 + λ) - λ / (1 + λ)`. -/
lemma lintegral_indicator_inv_abs_mul_sq_sub_one {lam : ℝ} (hlam : -1 < lam) :
    ∫⁻ t : ℝ, (if 1 + t * lam < 0 then ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) else 0) ∂volume =
      ENNReal.ofReal (Real.log (1 + lam) - lam / (1 + lam)) := by
  have h1pl : 0 < 1 + lam := by linarith
  rcases lt_trichotomy lam 0 with hneg | rfl | hpos
  · -- Case `-1 < lam < 0`: `1 + t * lam < 0 ↔ -1 / lam < t` (with `-1 / lam > 1`)
    set c : ℝ := -1 / lam
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
    -- Antiderivative `g(t) = log (t / (t - 1)) - 1 / (t - 1)` on `(1, ∞)`
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
    -- Express `Ioi c = ⋃ n : ℕ, Ioc c (c + n + 1)`
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
  · -- Case `lam = 0`
    simp [Real.log_one, show ¬(1 : ℝ) < 0 by norm_num]
  · -- Case `0 < lam`: `1 + t * lam < 0 ↔ t < -1 / lam` (with `-1 / lam < 0`)
    set c : ℝ := -1 / lam
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

private lemma isHermitian_pencil (ρ σ : DensityOp d) (r t : ℝ) :
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
      -- Minimum gap `δ = min_{i ∈ S} (-λ_i) > 0`
      obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image S (fun i ↦ -hA₀.eigenvalues i) hS_ne
      set δ : ℝ := -hA₀.eigenvalues i₀
      have hδ_pos : 0 < δ := by
        have := (Finset.mem_filter.mp hi₀).2; linarith
      -- Bound `C` on quadratic form of `σ - ρ` and `I`
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
      -- Construct negative-definite subspace `V = span {U e_i | i ∈ S}` of dimension `S.card ≥ k`
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
      -- Show `A(p)` is strictly negative on `V \ {0}`
      have hneg : ∀ x ∈ V, x ≠ 0 →
          (star x ⬝ᵥ (((1 - p.2 : ℝ) : ℂ) • ρ.mat + (p.2 : ℂ) • σ.mat +
            (p.1 : ℂ) • (1 : Matrix d d ℂ)).mulVec x).re < 0 := by
        intro x hx hx0
        have hA₀_le : (star x ⬝ᵥ A₀.mulVec x).re ≤ -δ * ∑ i : d, ‖x i‖ ^ 2 := by
          rw [re_quadForm_spectral hA₀ x]
          -- Since `x ∈ V`, `(Uᴴ x)_i = 0` for `i ∉ S`
          have horth : ∀ i : d, i ∉ S → ((star U).mulVec x) i = 0 := by
            intro i hi
            have hmem : x ∈ Submodule.span ℂ (v '' (S : Set d)) := hx
            refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
            · rintro _ ⟨j, hj, rfl⟩
              have hne : i ≠ j := fun h ↦ hi (h ▸ hj)
              have hu := congr_fun (congr_fun (Unitary.coe_star_mul_self hA₀.eigenvectorUnitary) i) j
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
        -- Bound perturbation `(star x ⬝ᵥ (A(p) - A₀).mulVec x).re`
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
            by_contra hall; push_neg at hall; exact hx0 (funext hall)
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

/-! ### Frenkel's Integral Formula (Theorem 6 / Eq. 3.7) -/

/-- Determinant of a Hermitian matrix equals the product of its real eigenvalues. -/
private lemma det_isHermitian_eq_prod {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    A.det = ∏ i : d, (hA.eigenvalues i : ℂ) := by
  have hspec : A = (hA.eigenvectorUnitary : Matrix d d ℂ) *
      Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) *
      star (hA.eigenvectorUnitary : Matrix d d ℂ) := by
    simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  have hU_mul : (hA.eigenvectorUnitary : Matrix d d ℂ) * star (hA.eigenvectorUnitary : Matrix d d ℂ) = 1 :=
    Unitary.coe_mul_star_self hA.eigenvectorUnitary
  conv_lhs => rw [hspec]
  rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
    hU_mul, Matrix.det_one, one_mul, Matrix.det_diagonal]
  rfl

/-- Trace of a Hermitian matrix equals the sum of its real eigenvalues. -/
private lemma trace_isHermitian_eq_sum {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    A.trace = ∑ i : d, (hA.eigenvalues i : ℂ) := by
  have hspec : A = (hA.eigenvectorUnitary : Matrix d d ℂ) *
      Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) *
      star (hA.eigenvectorUnitary : Matrix d d ℂ) := by
    simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  have hU_star : star (hA.eigenvectorUnitary : Matrix d d ℂ) * (hA.eigenvectorUnitary : Matrix d d ℂ) = 1 :=
    Unitary.coe_star_mul_self hA.eigenvectorUnitary
  conv_lhs => rw [hspec]
  rw [Matrix.trace_mul_cycle, hU_star, Matrix.one_mul, Matrix.trace_diagonal]
  rfl

set_option maxHeartbeats 800000 in
/-- **Frenkel's Integral Formula (Theorem 6 / Eq. 3.7)** for full-rank density operators `ρ, σ ≻ 0`:
`D(ρ ‖ σ) * log 2 = ∫⁻ t : ℝ, Tr(((1 - t) ρ + t σ)_-) / (|t| (t - 1)²) dt`. -/
theorem relEntropy_frenkel_integral {ρ σ : DensityOp d}
    (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    relEntropy ρ σ * ENNReal.ofReal (Real.log 2) =
      ∫⁻ t : ℝ, ENNReal.ofReal (negPartTrace (show (((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat).IsHermitian by
        have h1 : (((1 - t : ℝ) : ℂ) • ρ.mat).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, ρ.isHermitian.eq]
        have h2 : ((t : ℂ) • σ.mat).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, σ.isHermitian.eq]
        exact h1.add h2) / (|t| * (t - 1) ^ 2)) ∂volume := by
  set α : d → ℝ := ρ.eigvals
  set β : d → ℝ := σ.eigvals
  set Uρ : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
  set Uσ : Matrix d d ℂ := (σ.eigUnitary : Matrix d d ℂ)
  set V : Matrix d d ℂ := star Uσ * Uρ
  have hα_pos : ∀ i : d, 0 < α i := fun i ↦ hρ.eigenvalues_pos i
  have hβ_pos : ∀ j : d, 0 < β j := fun j ↦ hσ.eigenvalues_pos j
  have hUρ_mul : Uρ * star Uρ = 1 := Unitary.coe_mul_star_self ρ.eigUnitary
  have hUρ_star : star Uρ * Uρ = 1 := Unitary.coe_star_mul_self ρ.eigUnitary
  have hUσ_mul : Uσ * star Uσ = 1 := Unitary.coe_mul_star_self σ.eigUnitary
  have hUσ_star : star Uσ * Uσ = 1 := Unitary.coe_star_mul_self σ.eigUnitary
  have hV_star_mul : star V * V = 1 := by
    simp only [V, star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uσ (star Uσ), hUσ_mul, Matrix.one_mul, hUρ_star]
  have hV_mul_star : V * star V = 1 := by
    simp only [V, star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uρ (star Uρ), hUρ_mul, Matrix.one_mul, hUσ_star]
  have hV_col : ∀ i : d, ∑ j : d, ‖V j i‖ ^ 2 = 1 := by
    intro i
    have h := congr_arg Complex.re (congr_fun (congr_fun hV_star_mul i) i)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at h
    convert h using 1
    apply Finset.sum_congr rfl; intro j _
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hV_row : ∀ j : d, ∑ i : d, ‖V j i‖ ^ 2 = 1 := by
    intro j
    have h := congr_arg Complex.re (congr_fun (congr_fun hV_mul_star j) j)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at h
    convert h using 1
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  -- Define shifted relative entropy `F(r)` and `g(r) = -F'(r)` for `r ≥ 0`
  let F : ℝ → ℝ := fun r ↦
    ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * ((α i + r) * (Real.log (α i + r) - Real.log (β j + r)))
  let g : ℝ → ℝ := fun r ↦
    (∑ j : d, Real.log (β j + r) - ∑ i : d, Real.log (α i + r)) -
      (Fintype.card d : ℝ) + ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * ((α i + r) / (β j + r))
  -- Step 1: `F(0) = relEntropy ρ σ * log 2`
  have hF0_eq : ENNReal.ofReal (F 0) = relEntropy ρ σ * ENNReal.ofReal (Real.log 2) := by
    have hsupp : suppSubset ρ σ := by
      intro i j _ hβ0; exact absurd hβ0 (ne_of_gt (hβ_pos j))
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    unfold relEntropy
    rw [if_pos hsupp, ← ENNReal.ofReal_mul (by
      have hnn : 0 ≤ F 0 := by
        -- `F(0) = ∑ i, ∑ j, ‖V j i‖² * (α_i log(α_i/β_j)) ≥ ∑ i, ∑ j, ‖V j i‖² (α_i - β_j) = 0`
        have hterm : ∀ i j : d, α i - β j ≤ α i * (Real.log (α i) - Real.log (β j)) := by
          intro i j
          have hlog := Real.add_one_le_exp (Real.log (β j) - Real.log (α i))
          rw [Real.exp_sub, Real.exp_log (hβ_pos j), Real.exp_log (hα_pos i)] at hlog
          have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt (hα_pos i))
          have hcancel : α i * (β j / α i) = β j := mul_div_cancel₀ _ (ne_of_gt (hα_pos i))
          linarith
        calc (0 : ℝ) = ∑ i : d, α i - ∑ j : d, β j := by
              have h1 := ρ.sum_eigvals; have h2 := σ.sum_eigvals; linarith
          _ = ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * (α i - β j) := by
              simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hV_col, one_mul]
              congr 1; rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro j _
              rw [← Finset.sum_mul, hV_row, one_mul]
          _ ≤ F 0 := by
              apply Finset.sum_le_sum; intro i _
              apply Finset.sum_le_sum; intro j _
              simp only [add_zero]
              exact mul_le_mul_of_nonneg_left (hterm i j) (sq_nonneg _)
      exact div_nonneg (by simpa [F, α, β, V, Uρ, Uσ] using hnn) (le_of_lt hlog2_pos))]
    congr 1
    rw [div_mul_cancel₀ _ (ne_of_gt hlog2_pos)]
    simp [F, α, β, V, Uρ, Uσ]
  -- Step 2: `HasDerivAt F (-g r) r` and `ContinuousOn g (Ici 0)`
  have hF_deriv : ∀ r ≥ (0 : ℝ), HasDerivAt F (-g r) r := by
    intro r hr
    have hterm : ∀ i j : d, HasDerivAt
        (fun s : ℝ ↦ ‖V j i‖ ^ 2 * ((α i + s) * (Real.log (α i + s) - Real.log (β j + s))))
        (‖V j i‖ ^ 2 * (Real.log (α i + r) - Real.log (β j + r) + 1 - (α i + r) / (β j + r))) r := by
      intro i j
      have hαr : 0 < α i + r := by linarith [hα_pos i]
      have hβr : 0 < β j + r := by linarith [hβ_pos j]
      have h1 : HasDerivAt (fun s : ℝ ↦ α i + s) 1 r := by
        simpa using (hasDerivAt_const r (α i)).fun_add (hasDerivAt_id' r)
      have h2 : HasDerivAt (fun s : ℝ ↦ Real.log (α i + s)) (1 / (α i + r)) r := by
        simpa using h1.log (ne_of_gt hαr)
      have h3 : HasDerivAt (fun s : ℝ ↦ β j + s) 1 r := by
        simpa using (hasDerivAt_const r (β j)).fun_add (hasDerivAt_id' r)
      have h4 : HasDerivAt (fun s : ℝ ↦ Real.log (β j + s)) (1 / (β j + r)) r := by
        simpa using h3.log (ne_of_gt hβr)
      have hprod := h1.fun_mul (h2.fun_sub h4)
      convert hprod.const_mul (‖V j i‖ ^ 2) using 1
      field_simp [ne_of_gt hαr, ne_of_gt hβr]; ring
    have hsum : HasDerivAt F
        (∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 *
          (Real.log (α i + r) - Real.log (β j + r) + 1 - (α i + r) / (β j + r))) r := by
      have houter := HasDerivAt.fun_sum (u := Finset.univ)
        (fun i _ ↦ HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hterm i j))
      exact houter
    convert hsum using 1
    simp only [g]
    have hsplit : (∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 *
        (Real.log (α i + r) - Real.log (β j + r) + 1 - (α i + r) / (β j + r))) =
        (∑ i : d, Real.log (α i + r)) - (∑ j : d, Real.log (β j + r)) +
        (Fintype.card d : ℝ) - ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * ((α i + r) / (β j + r)) := by
      have h1 : ∀ i j : d, ‖V j i‖ ^ 2 * (Real.log (α i + r) - Real.log (β j + r) + 1 - (α i + r) / (β j + r)) =
          (‖V j i‖ ^ 2 * Real.log (α i + r) - ‖V j i‖ ^ 2 * Real.log (β j + r)) +
          (‖V j i‖ ^ 2 - ‖V j i‖ ^ 2 * ((α i + r) / (β j + r))) := fun i j ↦ by ring
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have ha : ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * Real.log (α i + r) = ∑ i : d, Real.log (α i + r) := by
        apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_mul, hV_col, one_mul]
      have hb : ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * Real.log (β j + r) = ∑ j : d, Real.log (β j + r) := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [← Finset.sum_mul, hV_row, one_mul]
      have hc : ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 = (Fintype.card d : ℝ) := by
        simp_rw [hV_col]; simp
      rw [ha, hb, hc]; ring
    linarith
  have hg_cont : ContinuousOn g (Ici 0) := by
    have hcont_sum : ∀ (s : Finset d) (f : d → ℝ → ℝ) (x : ℝ),
        (∀ i ∈ s, ContinuousAt (f i) x) → ContinuousAt (fun y ↦ ∑ i ∈ s, f i y) x := by
      intro s f x hf
      induction s using Finset.induction_on with
      | empty => simpa using continuousAt_const
      | @insert a s ha ih =>
        have heq : (fun y ↦ ∑ i ∈ insert a s, f i y) = fun y ↦ f a y + ∑ i ∈ s, f i y := by
          ext y; exact Finset.sum_insert ha
        rw [heq]
        exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
    intro r hr
    have h1 : ContinuousAt (fun s : ℝ ↦ ∑ j : d, Real.log (β j + s)) r :=
      hcont_sum Finset.univ _ r fun j _ ↦
        (Real.continuousAt_log (ne_of_gt (by linarith [hβ_pos j, Set.mem_Ici.mp hr] : 0 < β j + r))).comp
          (continuousAt_const.add continuousAt_id)
    have h2 : ContinuousAt (fun s : ℝ ↦ ∑ i : d, Real.log (α i + s)) r :=
      hcont_sum Finset.univ _ r fun i _ ↦
        (Real.continuousAt_log (ne_of_gt (by linarith [hα_pos i, Set.mem_Ici.mp hr] : 0 < α i + r))).comp
          (continuousAt_const.add continuousAt_id)
    have h3 : ContinuousAt (fun s : ℝ ↦ ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * ((α i + s) / (β j + s))) r :=
      hcont_sum Finset.univ _ r fun i _ ↦ hcont_sum Finset.univ _ r fun j _ ↦
        continuousAt_const.mul ((continuousAt_const.add continuousAt_id).div
          (continuousAt_const.add continuousAt_id)
          (ne_of_gt (by linarith [hβ_pos j, Set.mem_Ici.mp hr] : 0 < β j + r)))
    exact (((h1.sub h2).sub continuousAt_const).add h3).continuousWithinAt
  -- Step 3: `F(r) → 0` as `r → ∞`
  have hF_tendsto : Tendsto F atTop (𝓝 0) := by
    have hterm : ∀ i j : d, Tendsto
        (fun r : ℝ ↦ ‖V j i‖ ^ 2 * ((α i + r) * (Real.log (α i + r) - Real.log (β j + r))))
        atTop (𝓝 (‖V j i‖ ^ 2 * (α i - β j))) := by
      intro i j
      apply Tendsto.const_mul
      -- Use squeeze: `(β_j + r) * (u / (1 + u)) ≤ (β_j + r) * log(1 + u) ≤ (β_j + r) * u` for `u = (α_i - β_j)/(β_j + r)`
      have hlo : ∀ᶠ r : ℝ in atTop,
          (α i + r) * ((α i - β j) / (α i + r)) ≤ (α i + r) * (Real.log (α i + r) - Real.log (β j + r)) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
        have hαr : 0 < α i + r := by linarith [hα_pos i]
        have hβr : 0 < β j + r := by linarith [hβ_pos j]
        have h1 : (β j + r) / (α i + r) ≤ Real.exp ((β j + r) / (α i + r) - 1) := by
          have := Real.add_one_le_exp ((β j + r) / (α i + r) - 1); linarith
        have h2 : Real.log ((β j + r) / (α i + r)) ≤ (β j + r) / (α i + r) - 1 := by
          have := Real.log_le_log (div_pos hβr hαr) h1
          rwa [Real.log_exp] at this
        rw [Real.log_div (ne_of_gt hβr) (ne_of_gt hαr)] at h2
        have h3 : (α i - β j) / (α i + r) ≤ Real.log (α i + r) - Real.log (β j + r) := by
          have : 1 - (β j + r) / (α i + r) = (α i - β j) / (α i + r) := by
            field_simp [ne_of_gt hαr]; ring
          linarith
        exact mul_le_mul_of_nonneg_left h3 (le_of_lt hαr)
      have hhi : ∀ᶠ r : ℝ in atTop,
          (α i + r) * (Real.log (α i + r) - Real.log (β j + r)) ≤ (α i + r) * ((α i - β j) / (β j + r)) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
        have hαr : 0 < α i + r := by linarith [hα_pos i]
        have hβr : 0 < β j + r := by linarith [hβ_pos j]
        have h1 : (α i + r) / (β j + r) ≤ Real.exp ((α i + r) / (β j + r) - 1) := by
          have := Real.add_one_le_exp ((α i + r) / (β j + r) - 1); linarith
        have h2 : Real.log ((α i + r) / (β j + r)) ≤ (α i + r) / (β j + r) - 1 := by
          have := Real.log_le_log (div_pos hαr hβr) h1
          rwa [Real.log_exp] at this
        rw [Real.log_div (ne_of_gt hαr) (ne_of_gt hβr)] at h2
        have h3 : Real.log (α i + r) - Real.log (β j + r) ≤ (α i - β j) / (β j + r) := by
          have : (α i + r) / (β j + r) - 1 = (α i - β j) / (β j + r) := by
            field_simp [ne_of_gt hβr]; ring
          linarith
        exact mul_le_mul_of_nonneg_left h3 (le_of_lt hαr)
      have hlo_lim : Tendsto (fun r : ℝ ↦ (α i + r) * ((α i - β j) / (α i + r))) atTop (𝓝 (α i - β j)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
        exact (mul_div_cancel₀ _ (ne_of_gt (by linarith [hα_pos i]))).symm
      have hhi_lim : Tendsto (fun r : ℝ ↦ (α i + r) * ((α i - β j) / (β j + r))) atTop (𝓝 (α i - β j)) := by
        have hrew : ∀ᶠ r : ℝ in atTop,
            (α i + r) * ((α i - β j) / (β j + r)) = (α i - β j) * (1 + (α i - β j) / (β j + r)) := by
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
          field_simp [ne_of_gt (by linarith [hβ_pos j] : 0 < β j + r)]; ring
        rw [tendsto_congr' hrew]
        have hinv : Tendsto (fun r : ℝ ↦ (α i - β j) / (β j + r)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_left atTop (β j) tendsto_id)
        simpa using (tendsto_const_nhds (x := α i - β j)).mul ((tendsto_const_nhds (x := (1 : ℝ))).add hinv)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_lim hhi_lim hlo hhi
    have hsum_lim := tendsto_finset_sum Finset.univ (fun i _ ↦
      tendsto_finset_sum Finset.univ (fun j _ ↦ hterm i j))
    have hsum_zero : ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * (α i - β j) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hV_col, one_mul]
      have h2 : ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * β j = ∑ j : d, β j := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [← Finset.sum_mul, hV_row, one_mul]
      rw [h2, ρ.sum_eigvals, σ.sum_eigvals, sub_self]
    rwa [hsum_zero] at hsum_lim
  -- Step 4: Spectral congruence `X(t, r) = S(r) (I + t M(r)) S(r)` for each `r > 0`
  have hg_pos_and_lintegral : ∀ r : ℝ, 0 < r →
      0 ≤ g r ∧
      ENNReal.ofReal (g r) =
        ∫⁻ t : ℝ, (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) *
          ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) ∂volume := by
    intro r hr
    -- `P = ρ + r I`, `Q = σ + r I`, `S = P^{1/2}`, `Sinv = P^{-1/2}`, `M = Sinv (σ - ρ) Sinv`
    let S : Matrix d d ℂ := Uρ * Matrix.diagonal (fun i ↦ ((Real.sqrt (α i + r) : ℝ) : ℂ)) * star Uρ
    let Sinv : Matrix d d ℂ := Uρ * Matrix.diagonal (fun i ↦ (((Real.sqrt (α i + r))⁻¹ : ℝ) : ℂ)) * star Uρ
    let Qinv : Matrix d d ℂ := Uσ * Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ)) * star Uσ
    have hS_herm : S.IsHermitian := by
      simp only [S, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
      congr 2; ext i j; simp [Matrix.diagonal_apply]
    have hSinv_herm : Sinv.IsHermitian := by
      simp only [Sinv, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
      congr 2; ext i j; simp [Matrix.diagonal_apply]
    have hdiag_r : Matrix.diagonal (fun _ : d ↦ (r : ℂ)) = (r : ℂ) • (1 : Matrix d d ℂ) := by
      ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]
    have hS_mul_Sinv : S * Sinv = 1 := by
      simp only [S, Sinv, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star Uρ) Uρ, hUρ_star, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      have hd : Matrix.diagonal (fun i : d ↦ ((Real.sqrt (α i + r) : ℝ) : ℂ) * (((Real.sqrt (α i + r))⁻¹ : ℝ) : ℂ)) = 1 := by
        rw [← Matrix.diagonal_one]; congr 1; ext i
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by linarith [hα_pos i]))), Complex.ofReal_one]
      rw [hd, Matrix.one_mul, hUρ_mul]
    have hSinv_mul_S : Sinv * S = 1 := by
      simp only [S, Sinv, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star Uρ) Uρ, hUρ_star, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      have hd : Matrix.diagonal (fun i : d ↦ (((Real.sqrt (α i + r))⁻¹ : ℝ) : ℂ) * ((Real.sqrt (α i + r) : ℝ) : ℂ)) = 1 := by
        rw [← Matrix.diagonal_one]; congr 1; ext i
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by linarith [hα_pos i]))), Complex.ofReal_one]
      rw [hd, Matrix.one_mul, hUρ_mul]
    have hS_sq : S * S = ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ) := by
      have hρ_spec : ρ.mat = Uρ * Matrix.diagonal (Complex.ofReal ∘ α) * star Uρ := by
        simpa [Uρ, α, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
      have hI_spec : (r : ℂ) • (1 : Matrix d d ℂ) = Uρ * Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star Uρ := by
        rw [hdiag_r, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUρ_mul]
      simp only [S, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star Uρ) Uρ, hUρ_star, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      have hd : Matrix.diagonal (fun i : d ↦ ((Real.sqrt (α i + r) : ℝ) : ℂ) * ((Real.sqrt (α i + r) : ℝ) : ℂ)) =
          Matrix.diagonal (Complex.ofReal ∘ α) + Matrix.diagonal (fun _ : d ↦ (r : ℂ)) := by
        ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
        split_ifs
        · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith [hα_pos i]), Complex.ofReal_add]
        · simp
      rw [hd, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hρ_spec, ← hI_spec]
    have hQ_mul_Qinv : (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Qinv = 1 := by
      have hσ_spec : σ.mat = Uσ * Matrix.diagonal (Complex.ofReal ∘ β) * star Uσ := by
        simpa [Uσ, β, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
      have hI_spec : (r : ℂ) • (1 : Matrix d d ℂ) = Uσ * Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star Uσ := by
        rw [hdiag_r, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUσ_mul]
      have hQ_spec : σ.mat + (r : ℂ) • (1 : Matrix d d ℂ) =
          Uσ * Matrix.diagonal (fun j ↦ ((β j + r : ℝ) : ℂ)) * star Uσ := by
        rw [hσ_spec, hI_spec, ← Matrix.add_mul, ← Matrix.mul_add]
        congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
        split_ifs <;> simp [Complex.ofReal_add]
      rw [hQ_spec]
      simp only [Qinv, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star Uσ) Uσ, hUσ_star, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      have hd : Matrix.diagonal (fun j : d ↦
          ((β j + r : ℝ) : ℂ) * (((β j + r)⁻¹ : ℝ) : ℂ)) = 1 := by
        rw [← Matrix.diagonal_one]; congr 1; ext j
        rw [← Complex.ofReal_mul,
          mul_inv_cancel₀ (ne_of_gt (by linarith [hβ_pos j] : 0 < β j + r)), Complex.ofReal_one]
      rw [hd, Matrix.one_mul, hUσ_mul]
    -- Define `M = Sinv * (σ - ρ) * Sinv`
    let M : Matrix d d ℂ := Sinv * (σ.mat - ρ.mat) * Sinv
    have hM_herm : M.IsHermitian := by
      simp only [M, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
        hSinv_herm.eq, σ.isHermitian.eq, ρ.isHermitian.eq, Matrix.mul_assoc]
    have hUM_mul : (hM_herm.eigenvectorUnitary : Matrix d d ℂ) * star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_mul_star_self hM_herm.eigenvectorUnitary
    have hUM_star : star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) * (hM_herm.eigenvectorUnitary : Matrix d d ℂ) = 1 :=
      Unitary.coe_star_mul_self hM_herm.eigenvectorUnitary
    have h1pM : 1 + M = Sinv * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Sinv := by
      have h1 : (1 : Matrix d d ℂ) = Sinv * (ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Sinv := by
        calc (1 : Matrix d d ℂ) = (Sinv * S) * (S * Sinv) := by rw [hSinv_mul_S, hS_mul_Sinv, Matrix.mul_one]
          _ = Sinv * (S * S) * Sinv := by simp [Matrix.mul_assoc]
          _ = Sinv * (ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Sinv := by rw [hS_sq]
      conv_lhs => rw [h1]
      simp only [M, ← Matrix.add_mul, ← Matrix.mul_add]
      congr 2; abel
    have h1pM_herm : (1 + M).IsHermitian := Matrix.isHermitian_one.add hM_herm
    -- Eigenvalues of `1 + M` are `1 + λ_k > 0`
    have h1pM_pos : (1 + M).PosDef := by
      rw [h1pM, Matrix.posDef_iff_dotProduct_mulVec]
      refine ⟨h1pM ▸ h1pM_herm, fun x hx ↦ ?_⟩
      have hQ_pos : (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).PosDef := by
        have hrI_herm : ((r : ℂ) • (1 : Matrix d d ℂ)).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
            Complex.star_def, Complex.conj_ofReal]
        rw [Matrix.posDef_iff_dotProduct_mulVec]
        refine ⟨σ.isHermitian.add hrI_herm, fun y hy ↦ ?_⟩
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
          dotProduct_smul, smul_eq_mul]
        have hσ_y := (Matrix.posDef_iff_dotProduct_mulVec.mp hσ).2 hy
        have hy_pos : (0 : ℂ) < star y ⬝ᵥ y := by
          rw [Complex.pos_iff]
          have hre : (star y ⬝ᵥ y).re = ∑ i : d, ‖y i‖ ^ 2 := by
            simp only [dotProduct, Pi.star_apply, Complex.re_sum]
            apply Finset.sum_congr rfl; intro i _
            rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
          have him : (star y ⬝ᵥ y).im = 0 := by
            simp only [dotProduct, Pi.star_apply, Complex.im_sum]
            apply Finset.sum_eq_zero; intro i _
            rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_im]
          have hre_pos : 0 < (star y ⬝ᵥ y).re := by
            rw [hre]
            obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
              by_contra h; exact hy (funext fun i ↦ by_contra fun hi ↦ h ⟨i, hi⟩)
            exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hi))
              (Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖y j‖) (Finset.mem_univ i))
          exact ⟨hre_pos, him.symm⟩
        have hr_c : (0 : ℂ) < (r : ℂ) := by rw [Complex.pos_iff]; exact ⟨hr, rfl⟩
        exact add_pos hσ_y (mul_pos hr_c hy_pos)
      have hSinv_x : Sinv.mulVec x ≠ 0 := by
        intro h0
        have := congr_arg (Matrix.mulVec S) h0
        rw [Matrix.mulVec_mulVec, hS_mul_Sinv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
        exact hx this
      have hquad : star x ⬝ᵥ (Sinv * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Sinv).mulVec x =
          star (Sinv.mulVec x) ⬝ᵥ (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).mulVec (Sinv.mulVec x) := by
        have hstar_Sinv : star (Sinv.mulVec x) = (star x) ᵥ* Sinv := by
          ext i
          simp only [Pi.star_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, star_sum, star_mul']
          apply Finset.sum_congr rfl; intro j _
          have hji : star (Sinv i j) = Sinv j i := by
            have := congr_fun (congr_fun hSinv_herm.eq j) i
            simpa [Matrix.conjTranspose_apply] using this
          rw [hji]; ring
        rw [hstar_Sinv, Matrix.mul_assoc Sinv, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
      rw [hquad]
      exact (Matrix.posDef_iff_dotProduct_mulVec.mp hQ_pos).2 hSinv_x
    have hlam_gt : ∀ k : d, -1 < hM_herm.eigenvalues k := by
      intro k
      -- `v = U_M e_k` is unit eigenvector of `M`, hence `⟨v, (1 + M) v⟩ = 1 + λ_k > 0`
      let v : d → ℂ := fun i ↦ (hM_herm.eigenvectorUnitary : Matrix d d ℂ) i k
      have hv_ne : v ≠ 0 := by
        intro h0
        have hu := congr_fun (congr_fun (hUM_star) k) k
        simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hu
        have hzero : ∑ i : d, star ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) i k) *
            (hM_herm.eigenvectorUnitary : Matrix d d ℂ) i k = 0 := by
          apply Finset.sum_eq_zero; intro i _; have := congr_fun h0 i; simp [v] at this; simp [this]
        rw [hzero] at hu; exact zero_ne_one hu
      have hpos_v := (Matrix.posDef_iff_dotProduct_mulVec.mp h1pM_pos).2 hv_ne
      have hval_v : (star v ⬝ᵥ (1 + M).mulVec v).re = 1 + hM_herm.eigenvalues k := by
        rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.add_re]
        have h1 : (star v ⬝ᵥ v).re = 1 := by
          have hu := congr_arg Complex.re (congr_fun (congr_fun (hUM_star) k) k)
          simpa [dotProduct, Matrix.mul_apply, Matrix.star_apply, Pi.star_apply, v] using hu
        have h2 : (star v ⬝ᵥ M.mulVec v).re = hM_herm.eigenvalues k := by
          rw [re_quadForm_spectral hM_herm v]
          have horth : ∀ i : d, ((star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)).mulVec v) i =
              if i = k then 1 else 0 := by
            intro i
            have hu := congr_fun (congr_fun (hUM_star) i) k
            simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply, v, Matrix.one_apply] using hu
          simp_rw [horth]
          rw [Finset.sum_eq_single k]
          · simp
          · intro i _ hik; simp [hik]
          · intro h; exact absurd (Finset.mem_univ k) h
        linarith
      have hre_pos : 0 < (star v ⬝ᵥ (1 + M).mulVec v).re := (Complex.pos_iff.mp hpos_v).1
      linarith
    -- Relate `g r` to `∑ k, (log (1 + λ_k) - λ_k / (1 + λ_k))`
    have hg_spectral : g r = ∑ k : d, (Real.log (1 + hM_herm.eigenvalues k) -
        hM_herm.eigenvalues k / (1 + hM_herm.eigenvalues k)) := by
      -- (a) `∑ k, log (1 + λ_k) = ∑ j, log (β_j + r) - ∑ i, log (α_i + r)` via `det(1 + M) = det(Q) / det(P)`
      have hdet_eq : ∏ k : d, (1 + hM_herm.eigenvalues k) =
          (∏ j : d, (β j + r)) / (∏ i : d, (α i + r)) := by
        have h1 : (1 + M).det = (∏ k : d, ((1 + hM_herm.eigenvalues k : ℝ) : ℂ)) := by
          have hspec : 1 + M = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
              Matrix.diagonal (fun k ↦ ((1 + hM_herm.eigenvalues k : ℝ) : ℂ)) *
              star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
            have hM_spec : M = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                Matrix.diagonal (Complex.ofReal ∘ hM_herm.eigenvalues) *
                star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
              simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM_herm.spectral_theorem
            have hI_spec : (1 : Matrix d d ℂ) = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
                star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
              rw [Matrix.diagonal_one, Matrix.mul_one, hUM_mul]
            calc (1 : Matrix d d ℂ) + M
                = ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) * Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
                    star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)) +
                  ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                    Matrix.diagonal (Complex.ofReal ∘ hM_herm.eigenvalues) *
                    star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)) := congr_arg₂ (· + ·) hI_spec hM_spec
              _ = _ := by
                  rw [← Matrix.add_mul, ← Matrix.mul_add]
                  congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
                  split_ifs <;> simp [Complex.ofReal_add]
          conv_lhs => rw [hspec]
          rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
            hUM_mul, Matrix.det_one, one_mul,
            Matrix.det_diagonal]
        have h2 : (1 + M).det * (ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det =
            (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det := by
          have hdet1 : (Sinv * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)) * Sinv).det =
              Sinv.det * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det * Sinv.det := by
            rw [Matrix.det_mul (Sinv * (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ))) Sinv,
              Matrix.det_mul Sinv (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ))]
          have hdet2 : (S * S).det = S.det * S.det := Matrix.det_mul S S
          rw [h1pM, ← hS_sq, hdet1, hdet2]
          calc Sinv.det * (σ.mat + (r : ℂ) • 1).det * Sinv.det * (S.det * S.det)
              = (Sinv.det * S.det) * (Sinv.det * S.det) * (σ.mat + (r : ℂ) • 1).det := by ring
            _ = (Sinv * S).det * (Sinv * S).det * (σ.mat + (r : ℂ) • 1).det := by rw [← Matrix.det_mul Sinv S]
            _ = (σ.mat + (r : ℂ) • 1).det := by rw [hSinv_mul_S, Matrix.det_one]; ring
        have hdetP : (ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det = ∏ i : d, ((α i + r : ℝ) : ℂ) := by
          have hP_spec : ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ) =
              Uρ * Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * star Uρ := by
            have hρ_spec : ρ.mat = Uρ * Matrix.diagonal (Complex.ofReal ∘ α) * star Uρ := by
              simpa [Uρ, α, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
                Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
            have hI_spec : (r : ℂ) • (1 : Matrix d d ℂ) = Uρ * Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star Uρ := by
              rw [hdiag_r, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUρ_mul]
            rw [hρ_spec, hI_spec, ← Matrix.add_mul, ← Matrix.mul_add]
            congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
            split_ifs <;> simp [Complex.ofReal_add]
          rw [hP_spec, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
            hUρ_mul, Matrix.det_one, one_mul, Matrix.det_diagonal]
        have hdetQ : (σ.mat + (r : ℂ) • (1 : Matrix d d ℂ)).det = ∏ j : d, ((β j + r : ℝ) : ℂ) := by
          have hQ_spec : σ.mat + (r : ℂ) • (1 : Matrix d d ℂ) =
              Uσ * Matrix.diagonal (fun j ↦ ((β j + r : ℝ) : ℂ)) * star Uσ := by
            have hσ_spec : σ.mat = Uσ * Matrix.diagonal (Complex.ofReal ∘ β) * star Uσ := by
              simpa [Uσ, β, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
                Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
            have hI_spec : (r : ℂ) • (1 : Matrix d d ℂ) = Uσ * Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star Uσ := by
              rw [hdiag_r, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUσ_mul]
            rw [hσ_spec, hI_spec, ← Matrix.add_mul, ← Matrix.mul_add]
            congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
            split_ifs <;> simp [Complex.ofReal_add]
          rw [hQ_spec, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
            hUσ_mul, Matrix.det_one, one_mul, Matrix.det_diagonal]
        rw [h1, hdetP, hdetQ] at h2
        have h2_re := congr_arg Complex.re h2
        simp only [← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_re] at h2_re
        have hP_pos : 0 < ∏ i : d, (α i + r) := Finset.prod_pos fun i _ ↦ by linarith [hα_pos i]
        exact (eq_div_iff (ne_of_gt hP_pos)).mpr h2_re
      have hlog_sum : ∑ k : d, Real.log (1 + hM_herm.eigenvalues k) =
          ∑ j : d, Real.log (β j + r) - ∑ i : d, Real.log (α i + r) := by
        rw [← Real.log_prod (fun k _ ↦ ne_of_gt (by linarith [hlam_gt k])), hdet_eq,
          Real.log_div (ne_of_gt (Finset.prod_pos fun j _ ↦ by linarith [hβ_pos j]))
            (ne_of_gt (Finset.prod_pos fun i _ ↦ by linarith [hα_pos i])),
          Real.log_prod (fun j _ ↦ ne_of_gt (by linarith [hβ_pos j])),
          Real.log_prod (fun i _ ↦ ne_of_gt (by linarith [hα_pos i]))]
      -- (b) `∑ k, (1 + λ_k)⁻¹ = ∑ i, ∑ j, ‖V j i‖² * (α_i + r) / (β_j + r)` via `Tr((1 + M)⁻¹) = Tr(P Q⁻¹)`
      have htr_inv : ∑ k : d, (1 + hM_herm.eigenvalues k)⁻¹ =
          ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * ((α i + r) / (β j + r)) := by
        let inv1pM : Matrix d d ℂ := (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
          Matrix.diagonal (fun k ↦ (((1 + hM_herm.eigenvalues k)⁻¹ : ℝ) : ℂ)) *
          star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)
        have hinv_eq : inv1pM = S * Qinv * S := by
          have h1 : (1 + M) * inv1pM = 1 := by
            have hspec : 1 + M = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                Matrix.diagonal (fun k ↦ ((1 + hM_herm.eigenvalues k : ℝ) : ℂ)) *
                star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
              have hM_spec : M = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                  Matrix.diagonal (Complex.ofReal ∘ hM_herm.eigenvalues) *
                  star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
                simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM_herm.spectral_theorem
              have hI_spec : (1 : Matrix d d ℂ) = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                  Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
                  star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
                rw [Matrix.diagonal_one, Matrix.mul_one, hUM_mul]
              calc (1 : Matrix d d ℂ) + M
                  = ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) * Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
                      star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)) +
                    ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                      Matrix.diagonal (Complex.ofReal ∘ hM_herm.eigenvalues) *
                      star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)) := congr_arg₂ (· + ·) hI_spec hM_spec
                _ = _ := by
                    rw [← Matrix.add_mul, ← Matrix.mul_add]
                    congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
                    split_ifs <;> simp [Complex.ofReal_add]
            rw [hspec]
            simp only [inv1pM, Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)),
              hUM_star, Matrix.one_mul,
              ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
            have hd : Matrix.diagonal (fun k : d ↦
                ((1 + hM_herm.eigenvalues k : ℝ) : ℂ) * (((1 + hM_herm.eigenvalues k)⁻¹ : ℝ) : ℂ)) = 1 := by
              rw [← Matrix.diagonal_one]; congr 1; ext k
              rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt (by linarith [hlam_gt k])), Complex.ofReal_one]
            rw [hd, Matrix.one_mul, hUM_mul]
          have h2 : (S * Qinv * S) * (1 + M) = 1 := by
            rw [h1pM]
            calc S * Qinv * S * (Sinv * (σ.mat + (r : ℂ) • 1) * Sinv)
                = S * Qinv * (S * Sinv) * (σ.mat + (r : ℂ) • 1) * Sinv := by simp [Matrix.mul_assoc]
              _ = S * (Qinv * (σ.mat + (r : ℂ) • 1)) * Sinv := by rw [hS_mul_Sinv, Matrix.mul_one]; simp [Matrix.mul_assoc]
              _ = S * 1 * Sinv := by
                  have hQinv_Q : Qinv * (σ.mat + (r : ℂ) • 1) = 1 := by
                    have hσ_spec : σ.mat = Uσ * Matrix.diagonal (Complex.ofReal ∘ β) * star Uσ := by
                      simpa [Uσ, β, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
                        Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
                    have hI_spec : (r : ℂ) • (1 : Matrix d d ℂ) = Uσ * Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star Uσ := by
                      rw [hdiag_r, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUσ_mul]
                    have hQ_spec : σ.mat + (r : ℂ) • (1 : Matrix d d ℂ) =
                        Uσ * Matrix.diagonal (fun j ↦ ((β j + r : ℝ) : ℂ)) * star Uσ := by
                      rw [hσ_spec, hI_spec, ← Matrix.add_mul, ← Matrix.mul_add]
                      congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
                      split_ifs <;> simp [Complex.ofReal_add]
                    rw [hQ_spec]
                    simp only [Qinv, Matrix.mul_assoc]
                    rw [← Matrix.mul_assoc (star Uσ) Uσ, hUσ_star, Matrix.one_mul,
                      ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
                    have hd : Matrix.diagonal (fun j : d ↦
                        (((β j + r)⁻¹ : ℝ) : ℂ) * ((β j + r : ℝ) : ℂ)) = 1 := by
                      rw [← Matrix.diagonal_one]; congr 1; ext j
                      rw [← Complex.ofReal_mul,
                        inv_mul_cancel₀ (ne_of_gt (by linarith [hβ_pos j] : 0 < β j + r)), Complex.ofReal_one]
                    rw [hd, Matrix.one_mul, hUσ_mul]
                  rw [hQinv_Q]
              _ = 1 := by rw [Matrix.mul_one, hS_mul_Sinv]
          calc inv1pM = 1 * inv1pM := (Matrix.one_mul _).symm
            _ = ((S * Qinv * S) * (1 + M)) * inv1pM := by rw [h2]
            _ = (S * Qinv * S) * ((1 + M) * inv1pM) := Matrix.mul_assoc _ _ _
            _ = S * Qinv * S := by rw [h1, Matrix.mul_one]
        have htr1 : inv1pM.trace = ∑ k : d, (((1 + hM_herm.eigenvalues k)⁻¹ : ℝ) : ℂ) := by
          simp only [inv1pM]
          rw [Matrix.trace_mul_cycle, hUM_star,
            Matrix.one_mul, Matrix.trace_diagonal]
        have htr2 : (S * Qinv * S).trace =
            ∑ i : d, ∑ j : d, ((‖V j i‖ ^ 2 * ((α i + r) / (β j + r)) : ℝ) : ℂ) := by
          rw [Matrix.trace_mul_cycle, hS_sq]
          have hP_spec : ρ.mat + (r : ℂ) • (1 : Matrix d d ℂ) =
              Uρ * Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * star Uρ := by
            have hρ_spec : ρ.mat = Uρ * Matrix.diagonal (Complex.ofReal ∘ α) * star Uρ := by
              simpa [Uρ, α, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
                Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
            have hI_spec : (r : ℂ) • (1 : Matrix d d ℂ) = Uρ * Matrix.diagonal (fun _ : d ↦ (r : ℂ)) * star Uρ := by
              rw [hdiag_r, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUρ_mul]
            rw [hρ_spec, hI_spec, ← Matrix.add_mul, ← Matrix.mul_add]
            congr 2; ext i j; simp only [Matrix.add_apply, Matrix.diagonal_apply, Function.comp_apply]
            split_ifs <;> simp [Complex.ofReal_add]
          rw [hP_spec]
          simp only [Qinv]
          -- `Tr(Uρ D_P Uρᴴ Uσ D_{Q⁻¹} Uσᴴ) = Tr(D_P Vᴴ D_{Q⁻¹} V)`
          have hcyc : (Uρ * Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * star Uρ *
              (Uσ * Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ)) * star Uσ)).trace =
              (Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * (star V) *
                Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ)) * V).trace := by
            have hVstar : star V = star Uρ * Uσ := by simp [V, star_mul]
            rw [hVstar]
            calc (Uρ * Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * star Uρ *
                  (Uσ * Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ)) * star Uσ)).trace
                = (Uρ * (Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * star Uρ *
                    Uσ * Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ))) * star Uσ).trace := by
                    simp [Matrix.mul_assoc]
              _ = (star Uσ * Uρ * (Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * star Uρ *
                    Uσ * Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ)))).trace := by
                    rw [Matrix.trace_mul_cycle]
              _ = (Matrix.diagonal (fun i ↦ ((α i + r : ℝ) : ℂ)) * (star Uρ * Uσ) *
                    Matrix.diagonal (fun j ↦ (((β j + r)⁻¹ : ℝ) : ℂ)) * (star Uσ * Uρ)).trace := by
                    rw [Matrix.trace_mul_comm]; simp [Matrix.mul_assoc]
          rw [hcyc]
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
            ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
            Finset.sum_ite_eq]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Complex.ofReal_mul, Complex.ofReal_div, div_eq_mul_inv]
          have hnorm : star (V j i) * V j i = ((‖V j i‖ ^ 2 : ℝ) : ℂ) := by
            rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          calc ((α i + r : ℝ) : ℂ) * star (V j i) * (((β j + r)⁻¹ : ℝ) : ℂ) * V j i
              = (star (V j i) * V j i) * (((α i + r : ℝ) : ℂ) * (((β j + r : ℝ) : ℂ)⁻¹)) := by
                  rw [Complex.ofReal_inv]; ring
            _ = _ := by rw [hnorm]
        have htr_re := congr_arg Complex.re (htr1.symm.trans (congr_arg Matrix.trace hinv_eq |>.trans htr2))
        simp only [← Complex.ofReal_sum, Complex.ofReal_re] at htr_re
        exact htr_re
      simp only [g, ← hlog_sum, ← htr_inv]
      have hterm_eq : ∀ k : d, hM_herm.eigenvalues k / (1 + hM_herm.eigenvalues k) =
          1 - (1 + hM_herm.eigenvalues k)⁻¹ := by
        intro k
        have hpos : 0 < 1 + hM_herm.eigenvalues k := by linarith [hlam_gt k]
        field_simp [ne_of_gt hpos]; ring
      simp_rw [hterm_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      ring
    -- Nonnegativity of `g r`
    have hg_nn : 0 ≤ g r := by
      rw [hg_spectral]
      apply Finset.sum_nonneg; intro k _
      have hpos : 0 < 1 + hM_herm.eigenvalues k := by linarith [hlam_gt k]
      have hlog := Real.add_one_le_exp (-Real.log (1 + hM_herm.eigenvalues k))
      rw [Real.exp_neg, Real.exp_log hpos] at hlog
      have h1 : 1 - (1 + hM_herm.eigenvalues k)⁻¹ = hM_herm.eigenvalues k / (1 + hM_herm.eigenvalues k) := by
        field_simp [ne_of_gt hpos]; ring
      linarith
    refine ⟨hg_nn, ?_⟩
    -- Congruence `(1 - t) ρ + t σ + r I = S (I + t M) S` ⇒ `negEigCount = #{k | 1 + t λ_k < 0}`
    have hneg_eq : ∀ t : ℝ,
        (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) =
          ∑ k : d, if 1 + t * hM_herm.eigenvalues k < 0 then (1 : ℝ≥0∞) else 0 := by
      intro t
      have h1ptM_herm : (1 + (t : ℂ) • M).IsHermitian := by
        have htM : ((t : ℂ) • M).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hM_herm.eq]
        exact Matrix.isHermitian_one.add htM
      have hcong_mat : S * (1 + (t : ℂ) • M) * Sᴴ =
          ((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat + (r : ℂ) • (1 : Matrix d d ℂ) := by
        rw [hS_herm.eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hS_sq,
          Matrix.mul_smul, Matrix.smul_mul]
        have hSMS : S * M * S = σ.mat - ρ.mat := by
          simp only [M, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc S Sinv, hS_mul_Sinv, Matrix.one_mul, hSinv_mul_S, Matrix.mul_one]
        rw [hSMS]
        ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
        push_cast; ring
      have hneg1 : negEigCount (isHermitian_pencil ρ σ r t) = negEigCount h1ptM_herm := by
        have hcong_herm : (S * (1 + (t : ℂ) • M) * Sᴴ).IsHermitian :=
          hcong_mat.symm ▸ isHermitian_pencil ρ σ r t
        calc negEigCount (isHermitian_pencil ρ σ r t)
            = negEigCount hcong_herm := negEigCount_eq_of_eq _ _ hcong_mat.symm
          _ = negEigCount h1ptM_herm := negEigCount_congruence h1ptM_herm hS_mul_Sinv hSinv_mul_S hcong_herm
      -- Eigenvalues of `1 + t M` are `1 + t λ_k` (via unitary conjugation by `U_M`)
      let D : Matrix d d ℂ := Matrix.diagonal (fun k ↦ ((1 + t * hM_herm.eigenvalues k : ℝ) : ℂ))
      have hD_herm : D.IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext k; simp
      have h1ptM_eq : (hM_herm.eigenvectorUnitary : Matrix d d ℂ) * D *
          (hM_herm.eigenvectorUnitary : Matrix d d ℂ)ᴴ = 1 + (t : ℂ) • M := by
        have hM_spec : M = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
            Matrix.diagonal (Complex.ofReal ∘ hM_herm.eigenvalues) *
            star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
          simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hM_herm.spectral_theorem
        have hI_spec : (1 : Matrix d d ℂ) = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
            Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
            star (hM_herm.eigenvectorUnitary : Matrix d d ℂ) := by
          rw [Matrix.diagonal_one, Matrix.mul_one, hUM_mul]
        symm
        calc (1 : Matrix d d ℂ) + (t : ℂ) • M
            = ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) * Matrix.diagonal (fun _ : d ↦ (1 : ℂ)) *
                star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)) +
              (t : ℂ) • ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) *
                Matrix.diagonal (Complex.ofReal ∘ hM_herm.eigenvalues) *
                star (hM_herm.eigenvectorUnitary : Matrix d d ℂ)) :=
                  congr_arg₂ (· + ·) hI_spec (congr_arg ((t : ℂ) • ·) hM_spec)
          _ = (hM_herm.eigenvectorUnitary : Matrix d d ℂ) * D *
                (hM_herm.eigenvectorUnitary : Matrix d d ℂ)ᴴ := by
                  rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add]
                  simp only [D, Matrix.star_eq_conjTranspose]
                  congr 2; ext i j
                  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply,
                    Complex.real_smul]
                  split_ifs <;> simp [Complex.ofReal_add, Complex.ofReal_mul]
      have hneg2 : negEigCount h1ptM_herm = negEigCount hD_herm := by
        have hUDU_herm : ((hM_herm.eigenvectorUnitary : Matrix d d ℂ) * D *
            (hM_herm.eigenvectorUnitary : Matrix d d ℂ)ᴴ).IsHermitian :=
          h1ptM_eq.symm ▸ h1ptM_herm
        calc negEigCount h1ptM_herm
            = negEigCount hUDU_herm := negEigCount_eq_of_eq _ _ h1ptM_eq.symm
          _ = negEigCount hD_herm := negEigCount_congruence hD_herm hUM_mul hUM_star hUDU_herm
      have hneg3 : negEigCount hD_herm = (Finset.univ.filter (fun k : d ↦ 1 + t * hM_herm.eigenvalues k < 0)).card := by
        have hsum_ind : ∑ k : d, (if hD_herm.eigenvalues k < 0 then (1 : ℝ) else 0) =
            ∑ k : d, (if 1 + t * hM_herm.eigenvalues k < 0 then (1 : ℝ) else 0) :=
          spectral_sum_diagonal (fun k ↦ 1 + t * hM_herm.eigenvalues k) hD_herm (by simp [lt_irrefl])
        have hcard1 : (Finset.univ.filter (fun k : d ↦ hD_herm.eigenvalues k < 0)).card =
            ((∑ k : d, if hD_herm.eigenvalues k < 0 then (1 : ℝ) else 0) : ℝ) := by
          simp [Finset.sum_boole]
        have hcard2 : (Finset.univ.filter (fun k : d ↦ 1 + t * hM_herm.eigenvalues k < 0)).card =
            ((∑ k : d, if 1 + t * hM_herm.eigenvalues k < 0 then (1 : ℝ) else 0) : ℝ) := by
          simp [Finset.sum_boole]
        exact Nat.cast_injective (α := ℝ) (by rw [← hcard1, hsum_ind, ← hcard2]; rfl)
      rw [hneg1, hneg2, hneg3]
      simp [Finset.sum_boole]
    -- Integrate over `t` and apply `lintegral_indicator_inv_abs_mul_sq_sub_one`
    have hlhs : ∫⁻ t : ℝ, (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) *
        ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) ∂volume =
        ∑ k : d, ENNReal.ofReal (Real.log (1 + hM_herm.eigenvalues k) -
          hM_herm.eigenvalues k / (1 + hM_herm.eigenvalues k)) := by
      simp_rw [hneg_eq, Finset.sum_mul]
      rw [MeasureTheory.lintegral_finset_sum]
      · apply Finset.sum_congr rfl; intro k _
        have hite : ∀ t : ℝ, (if 1 + t * hM_herm.eigenvalues k < 0 then (1 : ℝ≥0∞) else 0) *
            ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) =
            if 1 + t * hM_herm.eigenvalues k < 0 then ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) else 0 := by
          intro t; split_ifs <;> simp
        simp_rw [hite]
        exact lintegral_indicator_inv_abs_mul_sq_sub_one (hlam_gt k)
      · intro k _
        have hmeas_set : MeasurableSet {t : ℝ | 1 + t * hM_herm.eigenvalues k < 0} :=
          measurableSet_lt (measurable_const.add (measurable_id.mul measurable_const)) measurable_const
        have hmeas_w : Measurable (fun t : ℝ ↦ ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2))) :=
          ENNReal.measurable_ofReal.comp (measurable_const.div
            (continuous_abs.measurable.mul ((measurable_id.sub measurable_const).pow_const 2)))
        exact (Measurable.ite hmeas_set measurable_const measurable_const).mul hmeas_w
    rw [hlhs, hg_spectral, ENNReal.ofReal_sum_of_nonneg]
    intro k _
    have hpos : 0 < 1 + hM_herm.eigenvalues k := by linarith [hlam_gt k]
    have hlog := Real.add_one_le_exp (-Real.log (1 + hM_herm.eigenvalues k))
    rw [Real.exp_neg, Real.exp_log hpos] at hlog
    have h1 : 1 - (1 + hM_herm.eigenvalues k)⁻¹ = hM_herm.eigenvalues k / (1 + hM_herm.eigenvalues k) := by
      field_simp [ne_of_gt hpos]; ring
    linarith
  -- Step 5: `∫⁻ r in Ioi 0, ENNReal.ofReal (g r) = ENNReal.ofReal (F 0)` via FTC + MCT
  have hint_g : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (g r) ∂volume = ENNReal.ofReal (F 0) := by
    have hunion : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioc (0 : ℝ) ((n : ℝ) + 1) := by
      ext r; simp only [mem_Ioi, mem_iUnion, mem_Ioc]
      constructor
      · intro hr; obtain ⟨n, hn⟩ := exists_nat_gt r; exact ⟨n, hr, by linarith⟩
      · rintro ⟨n, h1, _⟩; exact h1
    have hmono_sets : Monotone (fun n : ℕ ↦ Ioc (0 : ℝ) ((n : ℝ) + 1)) := by
      intro m n hmn r ⟨h1, h2⟩
      exact ⟨h1, by linarith [show (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmn]⟩
    have hlim_int : Tendsto (fun n : ℕ ↦ ∫⁻ r in Ioc (0 : ℝ) ((n : ℝ) + 1),
        ENNReal.ofReal (g r) ∂volume) atTop
        (𝓝 (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (g r) ∂volume)) := by
      rw [hunion]
      have hg_meas : Measurable (fun r : ℝ ↦ ENNReal.ofReal (g r)) := by
        apply ENNReal.measurable_ofReal.comp
        have h1 : Measurable (fun r : ℝ ↦ ∑ j : d, Real.log (β j + r)) :=
          Finset.measurable_sum _ fun j _ ↦ Real.measurable_log.comp (measurable_const.add measurable_id)
        have h2 : Measurable (fun r : ℝ ↦ ∑ i : d, Real.log (α i + r)) :=
          Finset.measurable_sum _ fun i _ ↦ Real.measurable_log.comp (measurable_const.add measurable_id)
        have h3 : Measurable (fun r : ℝ ↦ ∑ i : d, ∑ j : d, ‖V j i‖ ^ 2 * ((α i + r) / (β j + r))) :=
          Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
            measurable_const.mul ((measurable_const.add measurable_id).div (measurable_const.add measurable_id))
        exact ((h1.sub h2).sub measurable_const).add h3
      exact tendsto_setLIntegral_monotone hmono_sets (fun _ ↦ measurableSet_Ioc) hg_meas
    have hval_n : ∀ n : ℕ, ∫⁻ r in Ioc (0 : ℝ) ((n : ℝ) + 1), ENNReal.ofReal (g r) ∂volume =
        ENNReal.ofReal (F 0 - F ((n : ℝ) + 1)) := by
      intro n
      have hle : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      have hint : IntervalIntegrable g volume 0 ((n : ℝ) + 1) :=
        (hg_cont.mono (fun r hr ↦ hr.1)).intervalIntegrable_of_Icc hle
      have hftc : ∫ r in (0 : ℝ)..((n : ℝ) + 1), g r = F 0 - F ((n : ℝ) + 1) := by
        have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun r ↦ -F r) (f' := g)
          (fun r hr ↦ by
            rw [uIcc_of_le hle] at hr
            simpa using (hF_deriv r hr.1).fun_neg) hint
        linarith
      rw [← hftc, intervalIntegral.integral_of_le hle,
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint.1]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact (hg_pos_and_lintegral r hr.1).1
    have hlim_rhs : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (F 0 - F ((n : ℝ) + 1))) atTop
        (𝓝 (ENNReal.ofReal (F 0 - 0))) := by
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      exact tendsto_const_nhds.sub
        (hF_tendsto.comp (Filter.tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
    simp_rw [hval_n] at hlim_int
    simpa using tendsto_nhds_unique hlim_int hlim_rhs
  -- Step 6: Swap integrals via Tonelli (`lintegral_lintegral_swap`) and apply layer-cake!
  rw [← hF0_eq, ← hint_g]
  have h1 : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (g r) ∂volume =
      ∫⁻ r in Ioi (0 : ℝ), ∫⁻ t : ℝ,
        (negEigCount (isHermitian_pencil ρ σ r t) : ℝ≥0∞) *
          ENNReal.ofReal (1 / (|t| * (t - 1) ^ 2)) ∂volume ∂volume := by
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    intro r hr; exact (hg_pos_and_lintegral r hr).2
  rw [h1]
  have hmeas_prod : Measurable (fun p : ℝ × ℝ ↦
      (negEigCount (isHermitian_pencil ρ σ p.1 p.2) : ℝ≥0∞) *
        ENNReal.ofReal (1 / (|p.2| * (p.2 - 1) ^ 2))) :=
    (measurable_negEigCount_pencil ρ σ).mul
      (ENNReal.measurable_ofReal.comp (measurable_const.div
        ((continuous_abs.measurable.comp measurable_snd).mul
          ((measurable_snd.sub measurable_const).pow_const 2))))
  rw [MeasureTheory.lintegral_lintegral_swap hmeas_prod.aemeasurable]
  apply MeasureTheory.lintegral_congr
  intro t
  rw [MeasureTheory.lintegral_mul_const _ (by
    exact (measurable_negEigCount_pencil ρ σ).comp (measurable_id.prodMk measurable_const))]
  have hA_t : (((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat).IsHermitian := by
    have h1 : (((1 - t : ℝ) : ℂ) • ρ.mat).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, ρ.isHermitian.eq]
    have h2 : ((t : ℂ) • σ.mat).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, σ.isHermitian.eq]
    exact h1.add h2
  have hlc := lintegral_negEigCount_eq_negPartTrace hA_t
  rw [hlc, ← ENNReal.ofReal_mul (negPartTrace_nonneg hA_t), mul_one_div]

end PolarCodes
