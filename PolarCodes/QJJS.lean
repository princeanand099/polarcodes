/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.HockeyStick

/-!
# Simultaneous Hockey-Stick Representation (Lemma 3.2) and QJJS Inequality (Proposition 3.3)

This module proves:
- **Lemma 3.2** (`lemma_3_2_hockeyStick_measure`): Simultaneous probability measure representation
  of `D(ρ ‖ σ)`, `D(σ ‖ ρ)`, and `QJS(ρ, σ)` for full-rank density operators `ρ, σ ≻ 0`.
- **Proposition 3.3** (`prop_3_3_qjjs_posDef`, `prop_3_3_qjjs`): Quantum Jeffreys–Jensen–Shannon
  inequality `φ(QJS(ρ, σ)) ≤ ¼ (D(ρ ‖ σ) + D(σ ‖ ρ))` for all finite-dimensional density operators.
-/

open Matrix BigOperators Real MeasureTheory Set Filter
open scoped ComplexOrder ENNReal Topology

namespace PolarCodes

variable {d : Type*} [Fintype d] [DecidableEq d]


/-- **Lemma 3.2 (Simultaneous Hockey-Stick Representation)** for full-rank `ρ, σ ≻ 0`:
there exists a Borel probability measure `μ` supported on `[a, b] ⊂ (0, ∞)` with `∫ t dμ = 1`
that simultaneously represents `E_s(ρ ‖ σ)`, `D(ρ ‖ σ)`, `D(σ ‖ ρ)`, and `QJS(ρ, σ)`. -/
theorem lemma_3_2_hockeyStick_measure {ρ σ : DensityOp d}
    (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    ∃ (a b : ℝ) (μ : Measure ℝ),
      0 < a ∧ a ≤ b ∧ IsProbabilityMeasure μ ∧ μ (Icc a b)ᶜ = 0 ∧
      (∀ s : ℝ, hockeyStick s ρ σ = ∫ t, max (t - s) 0 ∂μ) ∧
      (∫ t, t ∂μ = 1) ∧
      ((relEntropy ρ σ).toReal = ∫ t, (t * Real.logb 2 t - (t - 1) / Real.log 2) ∂μ) ∧
      ((relEntropy σ ρ).toReal = ∫ t, (-Real.logb 2 t + (t - 1) / Real.log 2) ∂μ) ∧
      (qjs ρ σ = ∫ t, (t / 2 * Real.logb 2 (2 * t / (1 + t)) +
        1 / 2 * Real.logb 2 (2 / (1 + t))) ∂μ) := by
  obtain ⟨a, b, ha, hab, hleft, hright⟩ := hockeyStick_bounds_posDef hρ hσ
  let f : ℝ → ℝ := fun s ↦ hockeyStick s ρ σ
  have hf_conv : ConvexOn ℝ univ f := hockeyStick_convexOn ρ σ
  let g : ℝ → ℝ := convexRightDeriv f
  -- Construct Stieltjes function `F(s) = g(s) + 1`
  let F : StieltjesFunction ℝ :=
    { toFun := fun s ↦ g s + 1
      mono' := fun x y hxy ↦ by linarith [convexRightDeriv_mono hf_conv hleft hright hxy]
      right_continuous' := fun s ↦
        (convexRightDeriv_right_continuous hf_conv hleft hright s).add continuousWithinAt_const }
  let μ : Measure ℝ := F.measure
  have hF_left : ∀ s < a, F s = 0 := fun s hs ↦ by
    show g s + 1 = 0; rw [convexRightDeriv_eq_neg_one hf_conv hleft hright hs]; ring
  have hF_right : ∀ s ≥ b, F s = 1 := fun s hs ↦ by
    show g s + 1 = 1; rw [convexRightDeriv_eq_zero hf_conv hleft hright hs]; ring
  -- Support on `[a, b]`
  have hsupp_left : μ (Iio a) = 0 := by
    have hIio : Iio a = ⋃ n : ℕ, Ioc (a - (n : ℝ) - 1) (a - 1 / ((n : ℝ) + 1)) := by
      ext x; simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Ioc]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt (max (a - x) (1 / (a - x)))
        refine ⟨n, ?_, ?_⟩
        · linarith [le_max_left (a - x) (1 / (a - x))]
        · have h1 : 1 / (a - x) < (n : ℝ) + 1 := by
            linarith [le_max_right (a - x) (1 / (a - x))]
          have h2 : 1 / ((n : ℝ) + 1) < a - x := by
            rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
            have := (div_lt_iff₀ (by linarith : 0 < a - x)).mp h1
            linarith
          linarith
      · rintro ⟨n, _, h2⟩
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    rw [hIio]
    refine measure_iUnion_null fun n ↦ ?_
    rw [StieltjesFunction.measure_Ioc]
    have h1 : a - 1 / ((n : ℝ) + 1) < a := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have h2 : a - (n : ℝ) - 1 < a := by linarith
    rw [hF_left _ h1, hF_left _ h2, sub_self, ENNReal.ofReal_zero]
  have hsupp_right : μ (Ioi b) = 0 := by
    have hIoi : Ioi b = ⋃ n : ℕ, Ioc b (b + (n : ℝ) + 1) := by
      ext x; simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt (x - b)
        exact ⟨n, hx, by linarith⟩
      · rintro ⟨_, h1, _⟩; exact h1
    rw [hIoi]
    refine measure_iUnion_null fun n ↦ ?_
    rw [StieltjesFunction.measure_Ioc, hF_right _ (by linarith), hF_right _ le_rfl, sub_self,
      ENNReal.ofReal_zero]
  have hsupp : μ (Icc a b)ᶜ = 0 := by
    have hcompl : (Icc a b)ᶜ = Iio a ∪ Ioi b := by
      ext x; simp [not_and_or, not_le]
    rw [hcompl]
    exact measure_union_null hsupp_left hsupp_right
  -- Probability measure: `μ univ = 1`
  have hμ_univ : μ univ = 1 := by
    have huniv : (univ : Set ℝ) = Iio (a - 1) ∪ Ioc (a - 1) b ∪ Ioi b := by
      ext x; simp only [Set.mem_univ, Set.mem_union, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioi, true_iff]
      rcases lt_or_ge x (a - 1) with h1 | h1
      · left; left; exact h1
      · rcases le_or_gt x b with h2 | h2
        · left; right; exact ⟨by linarith, h2⟩
        · right; exact h2
    have hIio1 : μ (Iio (a - 1)) = 0 := measure_mono_null (Set.Iio_subset_Iio (by linarith)) hsupp_left
    have h1 : μ (Iio (a - 1) ∪ Ioc (a - 1) b) = μ (Ioc (a - 1) b) := by
      rw [measure_union (Set.disjoint_left.mpr fun x h1 h2 ↦ not_lt.mpr (le_of_lt h2.1) h1)
        measurableSet_Ioc, hIio1, zero_add]
    have h2 : μ (Iio (a - 1) ∪ Ioc (a - 1) b ∪ Ioi b) = μ (Ioc (a - 1) b) := by
      rw [measure_union (Set.disjoint_left.mpr fun x h1 h2 ↦ by
        rcases h1 with h1 | h1
        · linarith [Set.mem_Iio.mp h1, Set.mem_Ioi.mp h2]
        · exact not_lt.mpr h1.2 h2) measurableSet_Ioi, hsupp_right, add_zero, h1]
    rw [huniv, h2, StieltjesFunction.measure_Ioc, hF_right b le_rfl, hF_left (a - 1) (by linarith),
      sub_zero, ENNReal.ofReal_one]
  haveI hprob : IsProbabilityMeasure μ := ⟨hμ_univ⟩
  -- Tail measure identity: `μ (Ioi u) = ENNReal.ofReal (-g u)`
  have hμ_Ioi : ∀ u : ℝ, μ (Ioi u) = ENNReal.ofReal (-g u) := by
    intro u
    rcases le_or_gt b u with hbu | hub
    · have h0 : μ (Ioi u) = 0 := measure_mono_null (Set.Ioi_subset_Ioi hbu) hsupp_right
      rw [h0, convexRightDeriv_eq_zero hf_conv hleft hright hbu, neg_zero, ENNReal.ofReal_zero]
    · have hsplit : Ioi u = Ioc u b ∪ Ioi b := (Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hub)).symm
      rw [hsplit, measure_union (Set.disjoint_left.mpr fun x h1 h2 ↦ not_lt.mpr h1.2 h2)
        measurableSet_Ioi, hsupp_right, add_zero, StieltjesFunction.measure_Ioc, hF_right b le_rfl]
      congr 1; show 1 - (g u + 1) = -g u; ring
  -- Hockey-stick representation: `f s = ∫ t, max (t - s) 0 ∂μ`
  have hrep : ∀ s : ℝ, f s = ∫ t, max (t - s) 0 ∂μ := by
    intro s
    rcases le_or_gt b s with hbs | hsb
    · rw [hright s hbs]
      symm
      apply integral_eq_zero_of_ae
      filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
      simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
      exact max_eq_right (by linarith [ht.2])
    · have hftc := sub_eq_intervalIntegral_convexRightDeriv hf_conv hleft hright (le_of_lt hsb)
      rw [hright b le_rfl, zero_sub] at hftc
      have hf_eq : f s = ∫ u in Ioc s b, (-g u) ∂volume := by
        rw [← intervalIntegral.integral_of_le (le_of_lt hsb), intervalIntegral.integral_neg]
        linarith
      have hf_nn : 0 ≤ f s := posPartTrace_nonneg _
      have hg_nn : ∀ u : ℝ, 0 ≤ -g u := fun u ↦ by
        linarith [(convexRightDeriv_bounds hf_conv hleft hright u).2]
      have hint_g : IntegrableOn (fun u ↦ -g u) (Ioc s b) volume :=
        ((convexRightDeriv_mono hf_conv hleft hright).intervalIntegrable.neg).1
      -- Tonelli on `Ioc s b × ℝ`
      have hton : ENNReal.ofReal (f s) = ∫⁻ t, ENNReal.ofReal (max (t - s) 0) ∂μ := by
        rw [hf_eq, ofReal_integral_eq_lintegral_ofReal hint_g
          ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u _ ↦ hg_nn u))]
        have hstep1 : ∫⁻ u in Ioc s b, ENNReal.ofReal (-g u) ∂volume =
            ∫⁻ u in Ioc s b, ∫⁻ t, Set.indicator (Ioi u) (fun _ ↦ (1 : ℝ≥0∞)) t ∂μ ∂volume := by
          apply setLIntegral_congr_fun measurableSet_Ioc
          intro u _
          rw [lintegral_indicator measurableSet_Ioi, setLIntegral_const, one_mul, hμ_Ioi u]
        rw [hstep1, lintegral_lintegral_swap]
        · apply lintegral_congr_ae
          filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
          simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
          have hset : ∫⁻ u in Ioc s b, Set.indicator (Ioi u) (fun _ ↦ (1 : ℝ≥0∞)) t ∂volume =
              ∫⁻ u in Ioc s b, Set.indicator (Iio t) (fun _ ↦ (1 : ℝ≥0∞)) u ∂volume := by
            apply setLIntegral_congr_fun measurableSet_Ioc
            intro u _; by_cases h : u < t <;> simp [Set.indicator, h]
          rw [hset, lintegral_indicator measurableSet_Iio, setLIntegral_const, one_mul,
            Measure.restrict_apply measurableSet_Iio]
          rcases le_or_gt t s with hts | hst
          · have hemp : Iio t ∩ Ioc s b = ∅ := by
              ext u; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_empty_iff_false,
                iff_false, not_and]; intro h1 h2; linarith [h2.1]
            rw [hemp, measure_empty, max_eq_right (by linarith), ENNReal.ofReal_zero]
          · have hinter : Iio t ∩ Ioc s b = Ioo s t := by
              ext u; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
              constructor
              · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
              · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans (le_of_lt h2) ht.2⟩
            rw [hinter, Real.volume_Ioo, max_eq_left (by linarith)]
        · have hmeas : Measurable (fun p : ℝ × ℝ ↦ Set.indicator {q : ℝ × ℝ | q.1 < q.2} (fun _ ↦ (1 : ℝ≥0∞)) p) :=
            measurable_const.indicator (measurableSet_lt measurable_fst measurable_snd)
          exact hmeas.aemeasurable
      have hint_max : Integrable (fun t : ℝ ↦ max (t - s) 0) μ := by
        apply Integrable.mono' (integrable_const (max (b - s) 0))
        · exact ((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable
        · filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
          simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
          rw [Real.norm_of_nonneg (le_max_right _ _)]
          exact max_le_max_right 0 (by linarith [ht.2])
      rw [← ofReal_integral_eq_lintegral_ofReal hint_max
        (Eventually.of_forall fun _ ↦ le_max_right _ _)] at hton
      exact (ENNReal.ofReal_eq_ofReal_iff hf_nn
        (integral_nonneg fun _ ↦ le_max_right _ _)).mp hton
  -- Mean 1: `∫ t, t ∂μ = 1`
  have hmean : ∫ t, t ∂μ = 1 := by
    have h0 := hrep 0
    rw [hleft 0 (by linarith), sub_zero] at h0
    rw [← h0]
    apply integral_congr_ae
    filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
    simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
    rw [sub_zero, max_eq_left (by linarith [ht.1])]
  have hmean_sub : ∫ t, (t - 1) ∂μ = 0 := by
    have hint_t : Integrable (fun t : ℝ ↦ t) μ := by
      apply Integrable.mono' (integrable_const b) continuous_id.aestronglyMeasurable
      filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
      simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
      rw [Real.norm_of_nonneg (by linarith [ht.1])]; exact ht.2
    rw [integral_sub hint_t (integrable_const 1), hmean, integral_const, smul_eq_mul,
      show (μ univ).toReal = 1 by rw [hμ_univ]; simp]
    ring
  -- Helper: integrability of any continuous function on `[a, b]` with respect to `μ`
  have hint_of_cont : ∀ (φ : ℝ → ℝ), ContinuousOn φ (Icc a b) → Integrable φ μ := by
    intro φ hφ
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
    have hae_meas : AEStronglyMeasurable φ μ := by
      have hmeas_ind : StronglyMeasurable (Set.indicator (Icc a b) φ) :=
        hφ.stronglyMeasurable_of_isClosed isClosed_Icc
      refine hmeas_ind.aestronglyMeasurable.congr ?_
      filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
      simp only [Set.mem_compl_iff, not_not] at ht
      exact Set.indicator_of_mem ht φ
    refine Integrable.mono' (integrable_const M) hae_meas ?_
    filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
    simp only [Set.mem_compl_iff, not_not] at ht
    exact hM t ht
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Eq. (3.4): `D(ρ ‖ σ)`
  have hEq34 : (relEntropy ρ σ).toReal = ∫ t, (t * Real.logb 2 t - (t - 1) / Real.log 2) ∂μ := by
    have h38 := relEntropy_hockeyStick_integral hρ hσ
    -- Split `Ioi 0 = Ioc 0 1 ∪ Ioi 1`
    have hsplit : (∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal ((hockeyStick s ρ σ - max (1 - s) 0) / s) ∂volume) =
        (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ((f s - (1 - s)) / s) ∂volume) +
        (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (f s / s) ∂volume) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
        lintegral_union measurableSet_Ioi
          (Set.disjoint_left.mpr fun x h1 h2 ↦ not_lt.mpr h1.2 h2)]
      congr 1
      · apply setLIntegral_congr_fun measurableSet_Ioc
        intro s hs; rw [max_eq_left (by linarith [hs.2])]
      · apply setLIntegral_congr_fun measurableSet_Ioi
        intro s hs; rw [max_eq_right (by linarith [Set.mem_Ioi.mp hs]), sub_zero]
    rw [hsplit] at h38
    -- Express `f s - (1 - s) = ∫ max (s - t) 0 ∂μ` for `s ∈ (0, 1]`
    have hleft_int : ∀ s ∈ Ioc (0 : ℝ) 1,
        ENNReal.ofReal ((f s - (1 - s)) / s) =
          ∫⁻ t, ENNReal.ofReal (max (s - t) 0 / s) ∂μ := by
      intro s hs
      have hs0 : 0 < s := hs.1
      have h1 : f s - (1 - s) = ∫ t, max (s - t) 0 ∂μ := by
        rw [hrep s]
        have heq : ∀ t : ℝ, max (t - s) 0 - (1 - s) = max (s - t) 0 + (t - 1) := by
          intro t; rcases le_or_gt t s with h | h
          · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
          · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
        have hI1 : Integrable (fun t : ℝ ↦ max (t - s) 0) μ :=
          hint_of_cont _ ((continuous_id.sub continuous_const).max continuous_const).continuousOn
        have hI2 : Integrable (fun t : ℝ ↦ max (s - t) 0) μ :=
          hint_of_cont _ ((continuous_const.sub continuous_id).max continuous_const).continuousOn
        have hI3 : Integrable (fun t : ℝ ↦ t - 1) μ :=
          hint_of_cont _ (continuous_id.sub continuous_const).continuousOn
        have hsub : (∫ t, max (t - s) 0 ∂μ) - (1 - s) = ∫ t, (max (t - s) 0 - (1 - s)) ∂μ := by
          rw [integral_sub hI1 (integrable_const _), integral_const, smul_eq_mul,
            show (μ univ).toReal = 1 by rw [hμ_univ]; simp, one_mul]
        rw [hsub]
        simp_rw [heq]
        rw [integral_add hI2 hI3, hmean_sub, add_zero]
      rw [h1, ← integral_div]
      have hI : Integrable (fun t : ℝ ↦ max (s - t) 0 / s) μ :=
        (hint_of_cont _ ((continuous_const.sub continuous_id).max continuous_const).continuousOn).div_const s
      exact ofReal_integral_eq_lintegral_ofReal hI
        (Eventually.of_forall fun t ↦ div_nonneg (le_max_right _ _) (le_of_lt hs0))
    have hright_int : ∀ s ∈ Ioi (1 : ℝ),
        ENNReal.ofReal (f s / s) = ∫⁻ t, ENNReal.ofReal (max (t - s) 0 / s) ∂μ := by
      intro s hs
      have hs0 : 0 < s := by linarith [Set.mem_Ioi.mp hs]
      rw [hrep s, ← integral_div]
      have hI : Integrable (fun t : ℝ ↦ max (t - s) 0 / s) μ :=
        (hint_of_cont _ ((continuous_id.sub continuous_const).max continuous_const).continuousOn).div_const s
      exact ofReal_integral_eq_lintegral_ofReal hI
        (Eventually.of_forall fun t ↦ div_nonneg (le_max_right _ _) (le_of_lt hs0))
    have hl_swap : (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ((f s - (1 - s)) / s) ∂volume) =
        ∫⁻ t, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s - t) 0 / s) ∂volume ∂μ := by
      rw [setLIntegral_congr_fun measurableSet_Ioc hleft_int, lintegral_lintegral_swap]
      exact (ENNReal.measurable_ofReal.comp
        (((measurable_fst.sub measurable_snd).max measurable_const).div measurable_fst)).aemeasurable
    have hr_swap : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (f s / s) ∂volume) =
        ∫⁻ t, ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t - s) 0 / s) ∂volume ∂μ := by
      rw [setLIntegral_congr_fun measurableSet_Ioi hright_int, lintegral_lintegral_swap]
      exact (ENNReal.measurable_ofReal.comp
        (((measurable_snd.sub measurable_fst).max measurable_const).div measurable_fst)).aemeasurable
    rw [hl_swap, hr_swap, ← lintegral_add_left] at h38
    · have hker : (∫⁻ t, ((∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s - t) 0 / s) ∂volume) +
            (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t - s) 0 / s) ∂volume)) ∂μ) =
          ∫⁻ t, ENNReal.ofReal (t * Real.log t - (t - 1)) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
        simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
        exact lintegral_hockeyStick_kernel_1 (lt_of_lt_of_le ha ht.1)
      rw [hker] at h38
      have hI_ker : Integrable (fun t : ℝ ↦ t * Real.log t - (t - 1)) μ := by
        apply hint_of_cont
        exact (continuousOn_id.mul (Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (lt_of_lt_of_le ha ht.1))).sub
          (continuousOn_id.sub continuousOn_const)
      have hnn_ker : ∀ᵐ t ∂μ, 0 ≤ t * Real.log t - (t - 1) := by
        filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
        simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
        have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
        have h := Real.log_le_sub_one_of_pos (inv_pos.mpr ht0)
        rw [Real.log_inv] at h
        have hmul := mul_le_mul_of_nonneg_left h (le_of_lt ht0)
        have hsimp : t * (t⁻¹ - 1) = 1 - t := by field_simp [ne_of_gt ht0]
        linarith
      rw [← ofReal_integral_eq_lintegral_ofReal hI_ker hnn_ker] at h38
      have htoReal := congr_arg ENNReal.toReal h38
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hlog2_pos),
        ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn_ker)] at htoReal
      have hdiv : (relEntropy ρ σ).toReal = (∫ t, (t * Real.log t - (t - 1)) ∂μ) / Real.log 2 :=
        eq_div_of_mul_eq (ne_of_gt hlog2_pos) htoReal
      rw [hdiv, ← integral_div]
      apply integral_congr_ae
      filter_upwards with t
      simp only [Real.logb, sub_div, mul_div_assoc]
    · exact Measurable.lintegral_prod_left
        (ENNReal.measurable_ofReal.comp
          (((measurable_fst.sub measurable_snd).max measurable_const).div measurable_fst))
  -- Eq. (3.5): `D(σ ‖ ρ)`
  have hEq35 : (relEntropy σ ρ).toReal = ∫ t, (-Real.logb 2 t + (t - 1) / Real.log 2) ∂μ := by
    have h38 := relEntropy_hockeyStick_integral hσ hρ
    have hrep_swap : ∀ s : ℝ, 0 < s → hockeyStick s σ ρ = ∫ t, max (1 - s * t) 0 ∂μ := by
      intro s hs
      rw [hockeyStick_swap ρ σ hs, hrep (1 / s)]
      have h1 : s * (∫ t, max (t - 1 / s) 0 ∂μ) + (1 - s) =
          ∫ t, (max (s * t - 1) 0 + (1 - s * t)) ∂μ := by
        have hI1 : Integrable (fun t : ℝ ↦ max (t - 1 / s) 0) μ :=
          hint_of_cont _ ((continuous_id.sub continuous_const).max continuous_const).continuousOn
        have hI2 : Integrable (fun t : ℝ ↦ max (s * t - 1) 0) μ :=
          hint_of_cont _ (((continuous_const.mul continuous_id).sub continuous_const).max continuous_const).continuousOn
        have hI3 : Integrable (fun t : ℝ ↦ 1 - s * t) μ :=
          hint_of_cont _ (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
        rw [integral_add hI2 hI3, integral_sub (integrable_const 1)
          ((hint_of_cont _ continuousOn_id).const_mul s), integral_const, smul_eq_mul,
          show (μ univ).toReal = 1 by rw [hμ_univ]; simp, one_mul, integral_const_mul, hmean, mul_one]
        congr 1
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        rw [mul_max_of_nonneg _ _ (le_of_lt hs), mul_zero]
        congr 1; field_simp [ne_of_gt hs]
      rw [h1]
      apply integral_congr_ae
      filter_upwards with t
      rcases le_or_gt (s * t) 1 with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    have hsplit : (∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal ((hockeyStick s σ ρ - max (1 - s) 0) / s) ∂volume) =
        (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ((hockeyStick s σ ρ - (1 - s)) / s) ∂volume) +
        (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (hockeyStick s σ ρ / s) ∂volume) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
        lintegral_union measurableSet_Ioi
          (Set.disjoint_left.mpr fun x h1 h2 ↦ not_lt.mpr h1.2 h2)]
      congr 1
      · apply setLIntegral_congr_fun measurableSet_Ioc
        intro s hs; rw [max_eq_left (by linarith [hs.2])]
      · apply setLIntegral_congr_fun measurableSet_Ioi
        intro s hs; rw [max_eq_right (by linarith [Set.mem_Ioi.mp hs]), sub_zero]
    rw [hsplit] at h38
    have hleft_int : ∀ s ∈ Ioc (0 : ℝ) 1,
        ENNReal.ofReal ((hockeyStick s σ ρ - (1 - s)) / s) =
          ∫⁻ t, ENNReal.ofReal (max (s * t - 1) 0 / s) ∂μ := by
      intro s hs
      have hs0 : 0 < s := hs.1
      have h1 : hockeyStick s σ ρ - (1 - s) = ∫ t, max (s * t - 1) 0 ∂μ := by
        rw [hrep_swap s hs0]
        have heq : ∀ t : ℝ, max (1 - s * t) 0 - (1 - s) = max (s * t - 1) 0 + s * (1 - t) := by
          intro t; rcases le_or_gt (s * t) 1 with h | h
          · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
          · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
        have hI1 : Integrable (fun t : ℝ ↦ max (1 - s * t) 0) μ :=
          hint_of_cont _ ((continuous_const.sub (continuous_const.mul continuous_id)).max continuous_const).continuousOn
        have hI2 : Integrable (fun t : ℝ ↦ max (s * t - 1) 0) μ :=
          hint_of_cont _ (((continuous_const.mul continuous_id).sub continuous_const).max continuous_const).continuousOn
        have hI3 : Integrable (fun t : ℝ ↦ s * (1 - t)) μ :=
          hint_of_cont _ (continuous_const.mul (continuous_const.sub continuous_id)).continuousOn
        have hsub : (∫ t, max (1 - s * t) 0 ∂μ) - (1 - s) = ∫ t, (max (1 - s * t) 0 - (1 - s)) ∂μ := by
          rw [integral_sub hI1 (integrable_const _), integral_const, smul_eq_mul,
            show (μ univ).toReal = 1 by rw [hμ_univ]; simp, one_mul]
        rw [hsub]
        simp_rw [heq]
        rw [integral_add hI2 hI3, integral_const_mul,
          show ∫ t, (1 - t) ∂μ = 0 by
            have := congr_arg Neg.neg hmean_sub; rw [← integral_neg] at this
            simpa [neg_sub] using this, mul_zero, add_zero]
      rw [h1, ← integral_div]
      have hI : Integrable (fun t : ℝ ↦ max (s * t - 1) 0 / s) μ :=
        (hint_of_cont _ (((continuous_const.mul continuous_id).sub continuous_const).max continuous_const).continuousOn).div_const s
      exact ofReal_integral_eq_lintegral_ofReal hI
        (Eventually.of_forall fun t ↦ div_nonneg (le_max_right _ _) (le_of_lt hs0))
    have hright_int : ∀ s ∈ Ioi (1 : ℝ),
        ENNReal.ofReal (hockeyStick s σ ρ / s) = ∫⁻ t, ENNReal.ofReal (max (1 - s * t) 0 / s) ∂μ := by
      intro s hs
      have hs0 : 0 < s := by linarith [Set.mem_Ioi.mp hs]
      rw [hrep_swap s hs0, ← integral_div]
      have hI : Integrable (fun t : ℝ ↦ max (1 - s * t) 0 / s) μ :=
        (hint_of_cont _ ((continuous_const.sub (continuous_const.mul continuous_id)).max continuous_const).continuousOn).div_const s
      exact ofReal_integral_eq_lintegral_ofReal hI
        (Eventually.of_forall fun t ↦ div_nonneg (le_max_right _ _) (le_of_lt hs0))
    have hl_swap : (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ((hockeyStick s σ ρ - (1 - s)) / s) ∂volume) =
        ∫⁻ t, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * t - 1) 0 / s) ∂volume ∂μ := by
      rw [setLIntegral_congr_fun measurableSet_Ioc hleft_int, lintegral_lintegral_swap]
      exact (ENNReal.measurable_ofReal.comp
        ((((measurable_fst.mul measurable_snd).sub measurable_const).max measurable_const).div measurable_fst)).aemeasurable
    have hr_swap : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (hockeyStick s σ ρ / s) ∂volume) =
        ∫⁻ t, ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (1 - s * t) 0 / s) ∂volume ∂μ := by
      rw [setLIntegral_congr_fun measurableSet_Ioi hright_int, lintegral_lintegral_swap]
      exact (ENNReal.measurable_ofReal.comp
        (((measurable_const.sub (measurable_fst.mul measurable_snd)).max measurable_const).div measurable_fst)).aemeasurable
    rw [hl_swap, hr_swap, ← lintegral_add_left] at h38
    · have hker : (∫⁻ t, ((∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * t - 1) 0 / s) ∂volume) +
            (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (1 - s * t) 0 / s) ∂volume)) ∂μ) =
          ∫⁻ t, ENNReal.ofReal (-Real.log t + (t - 1)) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
        simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
        exact lintegral_hockeyStick_kernel_2 (lt_of_lt_of_le ha ht.1)
      rw [hker] at h38
      have hI_ker : Integrable (fun t : ℝ ↦ -Real.log t + (t - 1)) μ := by
        apply hint_of_cont
        exact (Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (lt_of_lt_of_le ha ht.1)).neg.add
          (continuousOn_id.sub continuousOn_const)
      have hnn_ker : ∀ᵐ t ∂μ, 0 ≤ -Real.log t + (t - 1) := by
        filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
        simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
        linarith [Real.log_le_sub_one_of_pos (lt_of_lt_of_le ha ht.1)]
      rw [← ofReal_integral_eq_lintegral_ofReal hI_ker hnn_ker] at h38
      have htoReal := congr_arg ENNReal.toReal h38
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hlog2_pos),
        ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn_ker)] at htoReal
      have hdiv : (relEntropy σ ρ).toReal = (∫ t, (-Real.log t + (t - 1)) ∂μ) / Real.log 2 :=
        eq_div_of_mul_eq (ne_of_gt hlog2_pos) htoReal
      rw [hdiv, ← integral_div]
      apply integral_congr_ae
      filter_upwards with t
      simp only [Real.logb, add_div, neg_div]
    · exact Measurable.lintegral_prod_left
        (ENNReal.measurable_ofReal.comp
          ((((measurable_fst.mul measurable_snd).sub measurable_const).max measurable_const).div measurable_fst))
  -- Eq. (3.6): `QJS(ρ, σ) = ½ D(ρ ‖ m) + ½ D(σ ‖ m)`
  have hEq36 : qjs ρ σ = ∫ t, (t / 2 * Real.logb 2 (2 * t / (1 + t)) +
      1 / 2 * Real.logb 2 (2 / (1 + t))) ∂μ := by
    let m := DensityOp.midpoint ρ σ
    have hm_pd : m.mat.PosDef := by
      rw [Matrix.posDef_iff_dotProduct_mulVec]
      refine ⟨m.isHermitian, fun x hx ↦ ?_⟩
      simp only [m, DensityOp.midpoint, DensityOp.mix, Matrix.add_mulVec, Matrix.smul_mulVec,
        dotProduct_add, dotProduct_smul, Complex.real_smul, smul_eq_mul]
      have h1 := (Matrix.posDef_iff_dotProduct_mulVec.mp hρ).2 x hx
      have h2 := (Matrix.posDef_iff_dotProduct_mulVec.mp hσ).2 x hx
      have hhalf : (0 : ℂ) < ((1 / 2 : ℝ) : ℂ) := by exact_mod_cast (by norm_num : (0 : ℝ) < 1 / 2)
      have h1' : (0 : ℂ) < ((1 - (1 / 2 : ℝ) : ℝ) : ℂ) * (star x ⬝ᵥ ρ.mat.mulVec x) :=
        mul_pos (by exact_mod_cast (by norm_num : (0 : ℝ) < 1 - 1 / 2)) h1
      have h2' : (0 : ℂ) < ((1 / 2 : ℝ) : ℂ) * (star x ⬝ᵥ σ.mat.mulVec x) := mul_pos hhalf h2
      exact add_pos h1' h2'
    -- `E_s(ρ ‖ m) = ∫ max (t - s * (1+t)/2) 0 ∂μ` for `s > 0`
    have hrep_m1 : ∀ s : ℝ, 0 < s → hockeyStick s ρ m = ∫ t, max (t - s * ((1 + t) / 2)) 0 ∂μ := by
      intro s hs
      rw [hockeyStick_midpoint_left ρ σ hs]
      split_ifs with hs2
      · rw [hrep (s / (2 - s)), ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        rw [mul_max_of_nonneg _ _ (by linarith : 0 ≤ 1 - s / 2), mul_zero]
        congr 1; field_simp [by linarith : 2 - s ≠ 0]; ring
      · push_neg at hs2
        symm; apply integral_eq_zero_of_ae
        filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
        simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
        have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
        exact max_eq_right (by nlinarith)
    -- `E_s(σ ‖ m) = ∫ max (1 - s * (1+t)/2) 0 ∂μ` for `s > 0`
    have hrep_m2 : ∀ s : ℝ, 0 < s → hockeyStick s σ m = ∫ t, max (1 - s * ((1 + t) / 2)) 0 ∂μ := by
      intro s hs
      have hm_symm : m = DensityOp.midpoint σ ρ := by
        cases h1 : DensityOp.midpoint ρ σ
        cases h2 : DensityOp.midpoint σ ρ
        have hmat : (DensityOp.midpoint ρ σ).mat = (DensityOp.midpoint σ ρ).mat := by
          ext i j; simp [DensityOp.midpoint, DensityOp.mix, Complex.real_smul]; ring
        rw [h1, h2] at hmat; simp only [m, h1]; congr
      rw [hm_symm, hockeyStick_midpoint_left σ ρ hs]
      split_ifs with hs2
      · have hs' : 0 < s / (2 - s) := div_pos hs (by linarith)
        have hrep_swap_s : hockeyStick (s / (2 - s)) σ ρ =
            ∫ t, max (1 - (s / (2 - s)) * t) 0 ∂μ := by
          rw [hockeyStick_swap ρ σ hs', hrep (1 / (s / (2 - s)))]
          have hI2 : Integrable (fun t : ℝ ↦ max ((s / (2 - s)) * t - 1) 0) μ :=
            hint_of_cont _ (((continuous_const.mul continuous_id).sub continuous_const).max continuous_const).continuousOn
          have hI3 : Integrable (fun t : ℝ ↦ 1 - (s / (2 - s)) * t) μ :=
            hint_of_cont _ (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
          have hstep : (s / (2 - s)) * (∫ t, max (t - 1 / (s / (2 - s))) 0 ∂μ) + (1 - s / (2 - s)) =
              ∫ t, (max ((s / (2 - s)) * t - 1) 0 + (1 - (s / (2 - s)) * t)) ∂μ := by
            rw [integral_add hI2 hI3, integral_sub (integrable_const 1)
              ((hint_of_cont _ continuousOn_id).const_mul (s / (2 - s))), integral_const, smul_eq_mul,
              show (μ univ).toReal = 1 by rw [hμ_univ]; simp, one_mul, integral_const_mul, hmean, mul_one]
            congr 1; rw [← integral_const_mul]
            apply integral_congr_ae; filter_upwards with t
            rw [mul_max_of_nonneg _ _ (le_of_lt hs'), mul_zero]
            congr 1; field_simp [ne_of_gt hs']
          rw [hstep]; apply integral_congr_ae; filter_upwards with t
          rcases le_or_gt ((s / (2 - s)) * t) 1 with h | h
          · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
          · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
        rw [hrep_swap_s, ← integral_const_mul]
        apply integral_congr_ae; filter_upwards with t
        rw [mul_max_of_nonneg _ _ (by linarith : 0 ≤ 1 - s / 2), mul_zero]
        congr 1; field_simp [by linarith : 2 - s ≠ 0]; ring
      · push_neg at hs2
        symm; apply integral_eq_zero_of_ae
        filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
        simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
        have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
        exact max_eq_right (by nlinarith)
    -- `D(ρ ‖ m)` via Tonelli + `lintegral_hockeyStick_kernel_mid1`
    have hDm1 : (relEntropy ρ m).toReal =
        ∫ t, (t * Real.log (2 * t / (1 + t)) + (1 - t) / 2) / Real.log 2 ∂μ := by
      have h38 := relEntropy_hockeyStick_integral hρ hm_pd
      have hsplit : (∫⁻ s in Ioi (0 : ℝ),
            ENNReal.ofReal ((hockeyStick s ρ m - max (1 - s) 0) / s) ∂volume) =
          (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ((hockeyStick s ρ m - (1 - s)) / s) ∂volume) +
          (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (hockeyStick s ρ m / s) ∂volume) := by
        rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
          lintegral_union measurableSet_Ioi
            (Set.disjoint_left.mpr fun x h1 h2 ↦ not_lt.mpr h1.2 h2)]
        congr 1
        · apply setLIntegral_congr_fun measurableSet_Ioc
          intro s hs; rw [max_eq_left (by linarith [hs.2])]
        · apply setLIntegral_congr_fun measurableSet_Ioi
          intro s hs; rw [max_eq_right (by linarith [Set.mem_Ioi.mp hs]), sub_zero]
      rw [hsplit] at h38
      have hleft_int : ∀ s ∈ Ioc (0 : ℝ) 1,
          ENNReal.ofReal ((hockeyStick s ρ m - (1 - s)) / s) =
            ∫⁻ t, ENNReal.ofReal (max (s * ((1 + t) / 2) - t) 0 / s) ∂μ := by
        intro s hs
        have hs0 : 0 < s := hs.1
        have h1 : hockeyStick s ρ m - (1 - s) = ∫ t, max (s * ((1 + t) / 2) - t) 0 ∂μ := by
          rw [hrep_m1 s hs0]
          have heq : ∀ t : ℝ, max (t - s * ((1 + t) / 2)) 0 - (1 - s) =
              max (s * ((1 + t) / 2) - t) 0 + (1 - s / 2) * (t - 1) := by
            intro t; rcases le_or_gt t (s * ((1 + t) / 2)) with h | h
            · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
            · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
          have hI1 : Integrable (fun t : ℝ ↦ max (t - s * ((1 + t) / 2)) 0) μ :=
            hint_of_cont _ (by fun_prop)
          have hI2 : Integrable (fun t : ℝ ↦ max (s * ((1 + t) / 2) - t) 0) μ :=
            hint_of_cont _ (by fun_prop)
          have hI3 : Integrable (fun t : ℝ ↦ (1 - s / 2) * (t - 1)) μ :=
            hint_of_cont _ (by fun_prop)
          have hsub : (∫ t, max (t - s * ((1 + t) / 2)) 0 ∂μ) - (1 - s) =
              ∫ t, (max (t - s * ((1 + t) / 2)) 0 - (1 - s)) ∂μ := by
            rw [integral_sub hI1 (integrable_const _), integral_const, smul_eq_mul,
              show (μ univ).toReal = 1 by rw [hμ_univ]; simp, one_mul]
          rw [hsub]; simp_rw [heq]
          rw [integral_add hI2 hI3, integral_const_mul, hmean_sub, mul_zero, add_zero]
        rw [h1, ← integral_div]
        have hI : Integrable (fun t : ℝ ↦ max (s * ((1 + t) / 2) - t) 0 / s) μ :=
          (hint_of_cont _ (by fun_prop)).div_const s
        exact ofReal_integral_eq_lintegral_ofReal hI
          (Eventually.of_forall fun t ↦ div_nonneg (le_max_right _ _) (le_of_lt hs0))
      have hright_int : ∀ s ∈ Ioi (1 : ℝ),
          ENNReal.ofReal (hockeyStick s ρ m / s) =
            ∫⁻ t, ENNReal.ofReal (max (t - s * ((1 + t) / 2)) 0 / s) ∂μ := by
        intro s hs
        have hs0 : 0 < s := by linarith [Set.mem_Ioi.mp hs]
        rw [hrep_m1 s hs0, ← integral_div]
        have hI : Integrable (fun t : ℝ ↦ max (t - s * ((1 + t) / 2)) 0 / s) μ :=
          (hint_of_cont _ (by fun_prop)).div_const s
        exact ofReal_integral_eq_lintegral_ofReal hI
          (Eventually.of_forall fun t ↦ div_nonneg (le_max_right _ _) (le_of_lt hs0))
      have hl_swap : (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ((hockeyStick s ρ m - (1 - s)) / s) ∂volume) =
          ∫⁻ t, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * ((1 + t) / 2) - t) 0 / s) ∂volume ∂μ := by
        rw [setLIntegral_congr_fun measurableSet_Ioc hleft_int, lintegral_lintegral_swap]
        exact (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable
      have hr_swap : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (hockeyStick s ρ m / s) ∂volume) =
          ∫⁻ t, ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t - s * ((1 + t) / 2)) 0 / s) ∂volume ∂μ := by
        rw [setLIntegral_congr_fun measurableSet_Ioi hright_int, lintegral_lintegral_swap]
        exact (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable
      rw [hl_swap, hr_swap, ← lintegral_add_left] at h38
      · have hker : (∫⁻ t, ((∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * ((1 + t) / 2) - t) 0 / s) ∂volume) +
              (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t - s * ((1 + t) / 2)) 0 / s) ∂volume)) ∂μ) =
            ∫⁻ t, ENNReal.ofReal (t * Real.log (2 * t / (1 + t)) + (1 - t) / 2) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
          simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
          exact lintegral_hockeyStick_kernel_mid1 (lt_of_lt_of_le ha ht.1)
        rw [hker] at h38
        have hI_ker : Integrable (fun t : ℝ ↦ t * Real.log (2 * t / (1 + t)) + (1 - t) / 2) μ := by
          apply hint_of_cont
          refine ContinuousOn.add ?_ (by fun_prop)
          refine continuousOn_id.mul (Real.continuousOn_log.comp ?_ ?_)
          · exact (continuousOn_const.mul continuousOn_id).div (continuousOn_const.add continuousOn_id)
              fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
          · intro t ht; exact ne_of_gt (div_pos (by linarith [lt_of_lt_of_le ha ht.1])
              (by linarith [lt_of_lt_of_le ha ht.1]))
        have hnn_ker : ∀ᵐ t ∂μ, 0 ≤ t * Real.log (2 * t / (1 + t)) + (1 - t) / 2 := by
          filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
          simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
          have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
          have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1 + t) (by linarith : 0 < 2 * t))
          have hinv : Real.log ((1 + t) / (2 * t)) = -Real.log (2 * t / (1 + t)) := by
            rw [← Real.log_inv, inv_div]
          rw [hinv] at h
          have hmul := mul_le_mul_of_nonneg_left h (le_of_lt ht0)
          have hsimp : t * ((1 + t) / (2 * t) - 1) = (1 - t) / 2 := by field_simp [ne_of_gt ht0]; ring
          linarith
        rw [← ofReal_integral_eq_lintegral_ofReal hI_ker hnn_ker] at h38
        have htoReal := congr_arg ENNReal.toReal h38
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hlog2_pos),
          ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn_ker)] at htoReal
        rw [eq_div_of_mul_eq (ne_of_gt hlog2_pos) htoReal, ← integral_div]
      · exact Measurable.lintegral_prod_left (ENNReal.measurable_ofReal.comp (by fun_prop))
    -- `D(σ ‖ m)` via Tonelli + `lintegral_hockeyStick_kernel_mid2`
    have hDm2 : (relEntropy σ m).toReal =
        ∫ t, (Real.log (2 / (1 + t)) + (t - 1) / 2) / Real.log 2 ∂μ := by
      have h38 := relEntropy_hockeyStick_integral hσ hm_pd
      have hsplit : (∫⁻ s in Ioi (0 : ℝ),
            ENNReal.ofReal ((hockeyStick s σ m - max (1 - s) 0) / s) ∂volume) =
          (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ((hockeyStick s σ m - (1 - s)) / s) ∂volume) +
          (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (hockeyStick s σ m / s) ∂volume) := by
        rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
          lintegral_union measurableSet_Ioi
            (Set.disjoint_left.mpr fun x h1 h2 ↦ not_lt.mpr h1.2 h2)]
        congr 1
        · apply setLIntegral_congr_fun measurableSet_Ioc
          intro s hs; rw [max_eq_left (by linarith [hs.2])]
        · apply setLIntegral_congr_fun measurableSet_Ioi
          intro s hs; rw [max_eq_right (by linarith [Set.mem_Ioi.mp hs]), sub_zero]
      rw [hsplit] at h38
      have hleft_int : ∀ s ∈ Ioc (0 : ℝ) 1,
          ENNReal.ofReal ((hockeyStick s σ m - (1 - s)) / s) =
            ∫⁻ t, ENNReal.ofReal (max (s * ((1 + t) / 2) - 1) 0 / s) ∂μ := by
        intro s hs
        have hs0 : 0 < s := hs.1
        have h1 : hockeyStick s σ m - (1 - s) = ∫ t, max (s * ((1 + t) / 2) - 1) 0 ∂μ := by
          rw [hrep_m2 s hs0]
          have heq : ∀ t : ℝ, max (1 - s * ((1 + t) / 2)) 0 - (1 - s) =
              max (s * ((1 + t) / 2) - 1) 0 + (s / 2) * (1 - t) := by
            intro t; rcases le_or_gt 1 (s * ((1 + t) / 2)) with h | h
            · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
            · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
          have hI1 : Integrable (fun t : ℝ ↦ max (1 - s * ((1 + t) / 2)) 0) μ :=
            hint_of_cont _ (by fun_prop)
          have hI2 : Integrable (fun t : ℝ ↦ max (s * ((1 + t) / 2) - 1) 0) μ :=
            hint_of_cont _ (by fun_prop)
          have hI3 : Integrable (fun t : ℝ ↦ (s / 2) * (1 - t)) μ :=
            hint_of_cont _ (by fun_prop)
          have hsub : (∫ t, max (1 - s * ((1 + t) / 2)) 0 ∂μ) - (1 - s) =
              ∫ t, (max (1 - s * ((1 + t) / 2)) 0 - (1 - s)) ∂μ := by
            rw [integral_sub hI1 (integrable_const _), integral_const, smul_eq_mul,
              show (μ univ).toReal = 1 by rw [hμ_univ]; simp, one_mul]
          rw [hsub]; simp_rw [heq]
          rw [integral_add hI2 hI3, integral_const_mul,
            show ∫ t, (1 - t) ∂μ = 0 by
              have := congr_arg Neg.neg hmean_sub; rw [← integral_neg] at this
              simpa [neg_sub] using this, mul_zero, add_zero]
        rw [h1, ← integral_div]
        have hI : Integrable (fun t : ℝ ↦ max (s * ((1 + t) / 2) - 1) 0 / s) μ :=
          (hint_of_cont _ (by fun_prop)).div_const s
        exact ofReal_integral_eq_lintegral_ofReal hI
          (Eventually.of_forall fun t ↦ div_nonneg (le_max_right _ _) (le_of_lt hs0))
      have hright_int : ∀ s ∈ Ioi (1 : ℝ),
          ENNReal.ofReal (hockeyStick s σ m / s) =
            ∫⁻ t, ENNReal.ofReal (max (1 - s * ((1 + t) / 2)) 0 / s) ∂μ := by
        intro s hs
        have hs0 : 0 < s := by linarith [Set.mem_Ioi.mp hs]
        rw [hrep_m2 s hs0, ← integral_div]
        have hI : Integrable (fun t : ℝ ↦ max (1 - s * ((1 + t) / 2)) 0 / s) μ :=
          (hint_of_cont _ (by fun_prop)).div_const s
        exact ofReal_integral_eq_lintegral_ofReal hI
          (Eventually.of_forall fun t ↦ div_nonneg (le_max_right _ _) (le_of_lt hs0))
      have hl_swap : (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ((hockeyStick s σ m - (1 - s)) / s) ∂volume) =
          ∫⁻ t, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * ((1 + t) / 2) - 1) 0 / s) ∂volume ∂μ := by
        rw [setLIntegral_congr_fun measurableSet_Ioc hleft_int, lintegral_lintegral_swap]
        exact (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable
      have hr_swap : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (hockeyStick s σ m / s) ∂volume) =
          ∫⁻ t, ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (1 - s * ((1 + t) / 2)) 0 / s) ∂volume ∂μ := by
        rw [setLIntegral_congr_fun measurableSet_Ioi hright_int, lintegral_lintegral_swap]
        exact (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable
      rw [hl_swap, hr_swap, ← lintegral_add_left] at h38
      · have hker : (∫⁻ t, ((∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * ((1 + t) / 2) - 1) 0 / s) ∂volume) +
              (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (1 - s * ((1 + t) / 2)) 0 / s) ∂volume)) ∂μ) =
            ∫⁻ t, ENNReal.ofReal (Real.log (2 / (1 + t)) + (t - 1) / 2) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
          simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
          exact lintegral_hockeyStick_kernel_mid2 (lt_of_lt_of_le ha ht.1)
        rw [hker] at h38
        have hI_ker : Integrable (fun t : ℝ ↦ Real.log (2 / (1 + t)) + (t - 1) / 2) μ := by
          apply hint_of_cont
          refine ContinuousOn.add ?_ (by fun_prop)
          refine Real.continuousOn_log.comp ?_ ?_
          · exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
              fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
          · intro t ht; exact ne_of_gt (div_pos two_pos (by linarith [lt_of_lt_of_le ha ht.1]))
        have hnn_ker : ∀ᵐ t ∂μ, 0 ≤ Real.log (2 / (1 + t)) + (t - 1) / 2 := by
          filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
          simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
          have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
          have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1 + t) two_pos)
          have hinv : Real.log ((1 + t) / 2) = -Real.log (2 / (1 + t)) := by
            rw [← Real.log_inv, inv_div]
          rw [hinv] at h; linarith
        rw [← ofReal_integral_eq_lintegral_ofReal hI_ker hnn_ker] at h38
        have htoReal := congr_arg ENNReal.toReal h38
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hlog2_pos),
          ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn_ker)] at htoReal
        rw [eq_div_of_mul_eq (ne_of_gt hlog2_pos) htoReal, ← integral_div]
      · exact Measurable.lintegral_prod_left (ENNReal.measurable_ofReal.comp (by fun_prop))
    -- Average `D(ρ ‖ m)` and `D(σ ‖ m)`
    have hqjs := qjs_eq_half_relEntropy_midpoint hρ hσ
    have hfin1 : relEntropy ρ m ≠ ⊤ := by
      intro htop
      rw [htop] at hqjs
      have : (ENNReal.ofReal (qjs ρ σ)) ≠ ⊤ := ENNReal.ofReal_ne_top
      rw [hqjs] at this
      simp at this
    have hfin2 : relEntropy σ m ≠ ⊤ := by
      intro htop
      rw [htop] at hqjs
      have : (ENNReal.ofReal (qjs ρ σ)) ≠ ⊤ := ENNReal.ofReal_ne_top
      rw [hqjs] at this
      simp at this
    have hqjs_real : qjs ρ σ = ((relEntropy ρ m).toReal + (relEntropy σ m).toReal) / 2 := by
      have hto := congr_arg ENNReal.toReal hqjs
      rw [ENNReal.toReal_ofReal (qjs_nonneg ρ σ), ENNReal.toReal_mul,
        ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_ofReal (by norm_num)] at hto
      linarith
    rw [hqjs_real, hDm1, hDm2]
    have hI1 : Integrable (fun t : ℝ ↦ (t * Real.log (2 * t / (1 + t)) + (1 - t) / 2) / Real.log 2) μ := by
      apply (hint_of_cont _ _).div_const
      refine ContinuousOn.add ?_ (by fun_prop)
      refine continuousOn_id.mul (Real.continuousOn_log.comp ?_ ?_)
      · exact (continuousOn_const.mul continuousOn_id).div (continuousOn_const.add continuousOn_id)
          fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
      · intro t ht; exact ne_of_gt (div_pos (by linarith [lt_of_lt_of_le ha ht.1])
          (by linarith [lt_of_lt_of_le ha ht.1]))
    have hI2 : Integrable (fun t : ℝ ↦ (Real.log (2 / (1 + t)) + (t - 1) / 2) / Real.log 2) μ := by
      apply (hint_of_cont _ _).div_const
      refine ContinuousOn.add ?_ (by fun_prop)
      refine Real.continuousOn_log.comp ?_ ?_
      · exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
          fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
      · intro t ht; exact ne_of_gt (div_pos two_pos (by linarith [lt_of_lt_of_le ha ht.1]))
    rw [← integral_add hI1 hI2, ← integral_div]
    apply integral_congr_ae; filter_upwards with t
    simp only [Real.logb]; ring
  exact ⟨a, b, μ, ha, hab, hprob, hsupp, hrep, hmean, hEq34, hEq35, hEq36⟩

/-! ### Part 6: Proposition 3.3 — Quantum Jeffreys–Jensen–Shannon Inequality -/

/-- **Proposition 3.3 (QJJS, full-rank real form)**: For full-rank `ρ, σ ≻ 0`,
`φ(QJS(ρ, σ)) ≤ ¼ (D(ρ ‖ σ) + D(σ ‖ ρ))`. -/
theorem prop_3_3_qjjs_posDef {ρ σ : DensityOp d} (hρ : ρ.mat.PosDef) (hσ : σ.mat.PosDef) :
    phi (qjs ρ σ) ≤ (1 / 4 : ℝ) * ((relEntropy ρ σ).toReal + (relEntropy σ ρ).toReal) := by
  by_cases hc0 : qjs ρ σ = 0
  · rw [hc0, phi_zero]
    positivity
  have hc_pos : 0 < qjs ρ σ := lt_of_le_of_ne (qjs_nonneg ρ σ) (Ne.symm hc0)
  obtain ⟨a, b, μ, ha, hab, hprob, hsupp, _, hmean, hEq34, hEq35, hEq36⟩ :=
    lemma_3_2_hockeyStick_measure hρ hσ
  -- Show `QJS(ρ, σ) < 1` for full-rank `ρ, σ ≻ 0`
  have hc_lt1 : qjs ρ σ < 1 := by
    rw [hEq36]
    have hlt_pt : ∀ t ∈ Icc a b,
        t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t)) < (1 + t) / 2 := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
      have h1 : Real.logb 2 (2 * t / (1 + t)) < 1 := by
        rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity), Real.rpow_one,
          div_lt_iff₀ (by linarith)]
        linarith
      have h2 : Real.logb 2 (2 / (1 + t)) < 1 := by
        rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity), Real.rpow_one,
          div_lt_iff₀ (by linarith)]
        linarith
      nlinarith
    have hI_lhs : Integrable (fun t : ℝ ↦
        t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) μ := by
      have hcont : ContinuousOn (fun t : ℝ ↦
          t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) (Icc a b) := by
        refine ContinuousOn.add ?_ ?_
        · refine (continuousOn_id.div_const 2).mul (ContinuousOn.div_const ?_ _)
          refine Real.continuousOn_log.comp ?_ ?_
          · exact (continuousOn_const.mul continuousOn_id).div (continuousOn_const.add continuousOn_id)
              fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
          · intro t ht; exact ne_of_gt (div_pos (by linarith [lt_of_lt_of_le ha ht.1])
              (by linarith [lt_of_lt_of_le ha ht.1]))
        · refine continuousOn_const.mul (ContinuousOn.div_const ?_ _)
          refine Real.continuousOn_log.comp ?_ ?_
          · exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
              fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
          · intro t ht; exact ne_of_gt (div_pos two_pos (by linarith [lt_of_lt_of_le ha ht.1]))
      obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
      have hm : AEStronglyMeasurable (fun t : ℝ ↦
          t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) μ := by
        refine (hcont.stronglyMeasurable_of_isClosed isClosed_Icc).aestronglyMeasurable.congr ?_
        filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
        simp only [Set.mem_compl_iff, not_not] at ht
        exact Set.indicator_of_mem ht _
      refine Integrable.mono' (integrable_const M) hm ?_
      filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
      simp only [Set.mem_compl_iff, not_not] at ht; exact hM t ht
    have hI_rhs : Integrable (fun t : ℝ ↦ (1 + t) / 2) μ := by
      have hcont : ContinuousOn (fun t : ℝ ↦ (1 + t) / 2) (Icc a b) := by fun_prop
      obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
      refine Integrable.mono' (integrable_const M) (by fun_prop) ?_
      filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
      simp only [Set.mem_compl_iff, not_not] at ht; exact hM t ht
    -- Strict inequality via max gap on compact `[a, b]`
    have hcont_diff : ContinuousOn (fun t : ℝ ↦
        (1 + t) / 2 - (t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t)))) (Icc a b) := by
      refine ContinuousOn.sub (by fun_prop) (ContinuousOn.add ?_ ?_)
      · refine (continuousOn_id.div_const 2).mul (ContinuousOn.div_const ?_ _)
        refine Real.continuousOn_log.comp ?_ ?_
        · exact (continuousOn_const.mul continuousOn_id).div (continuousOn_const.add continuousOn_id)
            fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
        · intro t ht; exact ne_of_gt (div_pos (by linarith [lt_of_lt_of_le ha ht.1])
            (by linarith [lt_of_lt_of_le ha ht.1]))
      · refine continuousOn_const.mul (ContinuousOn.div_const ?_ _)
        refine Real.continuousOn_log.comp ?_ ?_
        · exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
            fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
        · intro t ht; exact ne_of_gt (div_pos two_pos (by linarith [lt_of_lt_of_le ha ht.1]))
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, left_mem_Icc.mpr hab⟩ hcont_diff
    set δ := (1 + t₀) / 2 - (t₀ / 2 * Real.logb 2 (2 * t₀ / (1 + t₀)) + 1 / 2 * Real.logb 2 (2 / (1 + t₀)))
    have hδ_pos : 0 < δ := sub_pos.mpr (hlt_pt t₀ ht₀)
    have hint_le : ∫ t, (t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) ∂μ ≤
        ∫ t, ((1 + t) / 2 - δ) ∂μ := by
      apply integral_mono_ae hI_lhs (hI_rhs.sub (integrable_const δ))
      filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
      simp only [Set.mem_compl_iff, not_not] at ht
      linarith [hmin ht]
    have hrhs_val : ∫ t, ((1 + t) / 2 - δ) ∂μ = 1 - δ := by
      have h1 : ∫ t, ((1 + t) / 2) ∂μ = 1 := by
        have hint_t : Integrable (fun t : ℝ ↦ t) μ := by
          refine Integrable.mono' (integrable_const b) continuous_id.aestronglyMeasurable ?_
          filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
          simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
          rw [Real.norm_of_nonneg (by linarith [ht.1])]; exact ht.2
        rw [integral_div, integral_add (integrable_const 1) hint_t, integral_const, smul_eq_mul,
          hmean, show (μ univ).toReal = 1 by rw [measure_univ]; simp]
        ring
      rw [integral_sub hI_rhs (integrable_const δ), h1, integral_const, smul_eq_mul,
        show (μ univ).toReal = 1 by rw [measure_univ]; simp, one_mul]
    linarith
  -- Let `x = 1 - 2 h₂⁻¹(1 - QJS(ρ, σ)) ∈ (0, 1)`
  let c := qjs ρ σ
  let x := 1 - 2 * h2Inv (1 - c)
  have h1mc0 : 0 < 1 - c := by linarith
  have h1mc1 : 1 - c < 1 := by linarith
  have hinv_mem := h2Inv_mem_Icc (le_of_lt h1mc0) (le_of_lt h1mc1)
  have hinv_pos : 0 < h2Inv (1 - c) := by
    by_contra h0; push_neg at h0
    have heq0 : h2Inv (1 - c) = 0 := le_antisymm h0 hinv_mem.1
    have := h2_h2Inv (le_of_lt h1mc0) (le_of_lt h1mc1)
    rw [heq0, h2_zero] at this; linarith
  have hinv_lt : h2Inv (1 - c) < 1 / 2 := by
    by_contra h1; push_neg at h1
    have heq : h2Inv (1 - c) = 1 / 2 := le_antisymm hinv_mem.2 h1
    have := h2_h2Inv (le_of_lt h1mc0) (le_of_lt h1mc1)
    rw [heq, h2_half] at this; linarith
  have hx0 : 0 < x := by simp only [x]; linarith
  have hx1 : x < 1 := by simp only [x]; linarith
  have hcx : cParam x = c := by
    simp only [cParam, x]
    have : (1 - (1 - 2 * h2Inv (1 - c))) / 2 = h2Inv (1 - c) := by ring
    rw [this, h2_h2Inv (le_of_lt h1mc0) (le_of_lt h1mc1)]; ring
  have hphi_eq : phi c = phiParam x := by
    unfold phi; simp only [x]
  -- Integrate `gx x t ≥ 0` (Lemma 3.1) against `μ`
  have hgx_nn : 0 ≤ ∫ t, gx x t ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
    simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
    exact lemma_3_1_gx_nonneg hx0 hx1 (lt_of_lt_of_le ha ht.1)
  -- Express `∫ gx x t ∂μ` in terms of `D(ρ‖σ)`, `D(σ‖ρ)`, `QJS(ρ, σ)`
  have hint_of_cont : ∀ (ψ : ℝ → ℝ), ContinuousOn ψ (Icc a b) → Integrable ψ μ := by
    intro ψ hψ
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ
    have hm : AEStronglyMeasurable ψ μ := by
      refine (hψ.stronglyMeasurable_of_isClosed isClosed_Icc).aestronglyMeasurable.congr ?_
      filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
      simp only [Set.mem_compl_iff, not_not] at ht
      exact Set.indicator_of_mem ht _
    refine Integrable.mono' (integrable_const M) hm ?_
    filter_upwards [measure_zero_iff_ae_nmem.mp hsupp] with t ht
    simp only [Set.mem_compl_iff, not_not] at ht; exact hM t ht
  have hI1 : Integrable (fun t : ℝ ↦ (1 / 4 : ℝ) * (t - 1) * Real.logb 2 t) μ :=
    hint_of_cont _ ((continuousOn_const.mul (continuousOn_id.sub continuousOn_const)).mul
      (ContinuousOn.div_const (Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (lt_of_lt_of_le ha ht.1)) _))
  have hI2 : Integrable (fun t : ℝ ↦
      phiDerivParam x * (t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t)))) μ := by
    apply (hint_of_cont _ _).const_mul
    refine ContinuousOn.add ?_ ?_
    · refine (continuousOn_id.div_const 2).mul (ContinuousOn.div_const ?_ _)
      refine Real.continuousOn_log.comp ?_ ?_
      · exact (continuousOn_const.mul continuousOn_id).div (continuousOn_const.add continuousOn_id)
          fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
      · intro t ht; exact ne_of_gt (div_pos (by linarith [lt_of_lt_of_le ha ht.1])
          (by linarith [lt_of_lt_of_le ha ht.1]))
    · refine continuousOn_const.mul (ContinuousOn.div_const ?_ _)
      refine Real.continuousOn_log.comp ?_ ?_
      · exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
          fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
      · intro t ht; exact ne_of_gt (div_pos two_pos (by linarith [lt_of_lt_of_le ha ht.1]))
  have hI3 : Integrable (fun t : ℝ ↦ betaParam x * ((1 + t) / 2)) μ :=
    hint_of_cont _ (by fun_prop)
  have hgx_split : ∫ t, gx x t ∂μ =
      (∫ t, (1 / 4 : ℝ) * (t - 1) * Real.logb 2 t ∂μ) -
      phiDerivParam x * (∫ t, (t / 2 * Real.logb 2 (2 * t / (1 + t)) +
        1 / 2 * Real.logb 2 (2 / (1 + t))) ∂μ) +
      betaParam x * (∫ t, (1 + t) / 2 ∂μ) := by
    unfold gx
    rw [integral_add (hI1.sub hI2) hI3, integral_sub hI1 hI2, integral_const_mul, integral_const_mul]
  have hJ : ∫ t, (1 / 4 : ℝ) * (t - 1) * Real.logb 2 t ∂μ =
      (1 / 4 : ℝ) * ((relEntropy ρ σ).toReal + (relEntropy σ ρ).toReal) := by
    rw [hEq34, hEq35]
    have hIa : Integrable (fun t : ℝ ↦ t * Real.logb 2 t - (t - 1) / Real.log 2) μ :=
      hint_of_cont _ ((continuousOn_id.mul (ContinuousOn.div_const
        (Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (lt_of_lt_of_le ha ht.1)) _)).sub (by fun_prop))
    have hIb : Integrable (fun t : ℝ ↦ -Real.logb 2 t + (t - 1) / Real.log 2) μ :=
      hint_of_cont _ (((ContinuousOn.div_const
        (Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (lt_of_lt_of_le ha ht.1)) _).neg).add (by fun_prop))
    rw [← integral_add hIa hIb, ← integral_const_mul]
    apply integral_congr_ae; filter_upwards with t; ring
  have hhalf_mean : ∫ t, (1 + t) / 2 ∂μ = 1 := by
    have hint_t : Integrable (fun t : ℝ ↦ t) μ := hint_of_cont _ continuousOn_id
    rw [integral_div, integral_add (integrable_const 1) hint_t, integral_const, smul_eq_mul,
      hmean, show (μ univ).toReal = 1 by rw [measure_univ]; simp]
    ring
  rw [hgx_split, hJ, ← hEq36, hhalf_mean, mul_one] at hgx_nn
  have hbeta : phiDerivParam x * c - betaParam x = phi c := by
    rw [hphi_eq, ← hcx]; unfold betaParam; ring
  linarith

/-- Support inclusion `suppSubset ρ σ` implies `ker σ ⊆ ker ρ`. -/
private lemma suppSubset_ker {ρ σ : DensityOp d} (hsupp : suppSubset ρ σ)
    (v : d → ℂ) (hσv : σ.mat.mulVec v = 0) : ρ.mat.mulVec v = 0 := by
  set Uρ : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
  set Uσ : Matrix d d ℂ := (σ.eigUnitary : Matrix d d ℂ)
  have hspecρ : ρ.mat = Uρ * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star Uρ := by
    simpa [Uρ, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
  have hspecσ : σ.mat = Uσ * Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) * star Uσ := by
    simpa [Uσ, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
      Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
  set y : d → ℂ := (star Uσ).mulVec v
  have hy : ∀ j : d, σ.eigvals j ≠ 0 → y j = 0 := by
    intro j hj
    have h1 := congr_arg (fun w ↦ ((star Uσ).mulVec w) j) hσv
    have hL : ((star Uσ).mulVec (σ.mat.mulVec v)) j = (σ.eigvals j : ℂ) * y j := by
      conv_lhs => rw [hspecσ]
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc (star Uσ), ← Matrix.mul_assoc (star Uσ),
        Unitary.coe_star_mul_self σ.eigUnitary, Matrix.one_mul, Matrix.mulVec_mulVec,
        Matrix.mulVec_diagonal]; rfl
    rw [hL, Matrix.mulVec_zero, Pi.zero_apply] at h1
    have hne : (σ.eigvals j : ℂ) ≠ 0 := by exact_mod_cast hj
    exact (mul_eq_zero.mp h1).resolve_left hne
  have hzero : (fun i : d ↦ (Complex.ofReal ∘ ρ.eigvals) i * ((star Uρ).mulVec v) i) = 0 := by
    ext i; simp only [Function.comp_apply, Pi.zero_apply]
    by_cases hρi : ρ.eigvals i = 0
    · simp [hρi]
    · suffices ((star Uρ).mulVec v) i = 0 by simp [this]
      have hv : v = Uσ.mulVec y := by
        simp only [y, Matrix.mulVec_mulVec, Unitary.coe_mul_star_self σ.eigUnitary, Matrix.one_mulVec]
      rw [hv, Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero; intro j _
      by_cases hσj : σ.eigvals j = 0
      · have hW := hsupp i j hρi hσj
        have hW' : (star Uρ * Uσ) i j = 0 := by
          have hstar : star (star Uσ * Uρ) = star Uρ * Uσ := by
            simp [Matrix.star_mul, star_star]
          have hji := congr_fun (congr_fun hstar i) j
          simp only [Matrix.star_apply] at hji
          rw [← hji, hW, star_zero]
        rw [hW', zero_mul]
      · rw [hy j hσj, mul_zero]
  conv_lhs => rw [hspecρ]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, hzero, Matrix.mulVec_zero]

/-- **Proposition 3.3 (Quantum Jeffreys–Jensen–Shannon Inequality)** for ALL density operators
`ρ, σ ∈ D(H)`: `φ(QJS(ρ, σ)) ≤ ¼ (D(ρ ‖ σ) + D(σ ‖ ρ))`. -/
theorem prop_3_3_qjjs (ρ σ : DensityOp d) :
    phiExt (qjs ρ σ) ≤ (1 / 4 : ℝ≥0∞) * (relEntropy ρ σ + relEntropy σ ρ) := by
  by_cases hsupp : suppSubset ρ σ ∧ suppSubset σ ρ
  · -- Restrict to the common support `S_pos = {i : d | 0 < ρ.eigvals i}`
    -- On `S_pos`, both `ρ` and `σ` are strictly positive definite (`PosDef`)!
    set S_pos : Finset d := Finset.univ.filter fun i : d ↦ 0 < ρ.eigvals i
    let d' := {i : d // i ∈ S_pos}
    set U : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
    let V : Matrix d d' ℂ := Matrix.of fun r k ↦ U r k.1
    have hVHV : Vᴴ * V = 1 := by
      ext j k
      simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
      have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) j.1) k.1
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h
      convert h using 1
      simp [Subtype.ext_iff]
    -- Helper: `ρ` vanishes on columns of `U` outside `S_pos`
    have hρ_ker : ∀ i : d, i ∉ S_pos → ρ.mat.mulVec (fun r ↦ U r i) = 0 := by
      intro i hi
      have h0 : ρ.eigvals i = 0 := by
        have hle : ρ.eigvals i ≤ 0 := by simp [S_pos] at hi; exact hi
        exact le_antisymm hle (ρ.eigvals_nonneg i)
      have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by
        simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
      have hcol : (star U).mulVec (fun r ↦ U r i) = Pi.single i 1 := by
        ext j
        have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) j) i
        simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
          Pi.single_apply, eq_comm] using h
      conv_lhs => rw [hspec]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcol, Matrix.mulVec_diagonal]
      have hzero : (fun j : d ↦ (Complex.ofReal ∘ ρ.eigvals) j * Pi.single i 1 j) = 0 := by
        ext j; by_cases hj : j = i
        · subst hj; simp [h0]
        · simp [Pi.single_eq_of_ne hj]
      rw [hzero, Matrix.mulVec_zero]
    have hσ_ker : ∀ i : d, i ∉ S_pos → σ.mat.mulVec (fun r ↦ U r i) = 0 := by
      intro i hi
      exact suppSubset_ker hsupp.2 (fun r ↦ U r i) (hρ_ker i hi)
    -- Projected density operators `ρ' = Vᴴ ρ V` and `σ' = Vᴴ σ V` on `d'`
    have hρ'_mat : Vᴴ * ρ.mat * V = Matrix.diagonal (fun k : d' ↦ (ρ.eigvals k.1 : ℂ)) := by
      have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by
        simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
          Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
      ext j k
      have hmul : Vᴴ * U = Matrix.of fun (a : d') (b : d) ↦ if a.1 = b then (1 : ℂ) else 0 := by
        ext a b
        have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) a.1) b
        simpa [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.star_apply, Matrix.of_apply,
          Matrix.one_apply] using h
      have hmul2 : star U * V = Matrix.of fun (a : d) (b : d') ↦ if a = b.1 then (1 : ℂ) else 0 := by
        ext a b
        have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) a) b.1
        simpa [V, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply] using h
      have hcalc : Vᴴ * ρ.mat * V =
          (Vᴴ * U) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * (star U * V) := by
        conv_lhs => rw [hspec]
        simp only [Matrix.mul_assoc]
      rw [hcalc, hmul, hmul2]
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, Function.comp_apply,
        ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ↓reduceIte, Finset.sum_ite_eq', Subtype.ext_iff]
      split_ifs <;> simp_all
    let ρ' : DensityOp d' :=
      { mat := Vᴴ * ρ.mat * V
        posSemidef := by
          simpa [Matrix.conjTranspose_conjTranspose] using ρ.posSemidef.mul_mul_conjTranspose_same Vᴴ
        trace_one := by
          rw [hρ'_mat, Matrix.trace_diagonal]
          have htr : ρ.mat.trace = ∑ i : d, (ρ.eigvals i : ℂ) := by
            have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by
              simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
                Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
            conv_lhs => rw [hspec]
            rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self ρ.eigUnitary, Matrix.one_mul,
              Matrix.trace_diagonal]; rfl
          rw [← ρ.trace_one, htr, Finset.sum_coe_sort S_pos (fun i ↦ (ρ.eigvals i : ℂ))]
          symm
          apply Finset.sum_subset (Finset.subset_univ S_pos)
          intro i _ hi
          have hle : ρ.eigvals i ≤ 0 := by simp [S_pos] at hi; exact hi
          simp [le_antisymm hle (ρ.eigvals_nonneg i)] }
    have hρ'_pd : ρ'.mat.PosDef := by
      simp only [ρ', hρ'_mat, Matrix.posDef_diagonal_iff]
      intro k
      have hk : 0 < ρ.eigvals k.1 := (Finset.mem_filter.mp k.2).2
      exact_mod_cast hk
    -- `V * Vᴴ` is the projection onto `supp(ρ)`, and `V * Vᴴ * σ * V * Vᴴ = σ`
    have hVVH_σ : (V * Vᴴ) * σ.mat = σ.mat := by
      -- Check on columns of `U` (which form a unitary basis)
      have hU_eq : ((V * Vᴴ) * σ.mat) * U = σ.mat * U := by
        ext r i
        simp only [Matrix.mul_apply]
        have hσUi : (σ.mat * U) r i = (σ.mat.mulVec (fun x ↦ U x i)) r := rfl
        have hVVH_apply : ∀ (v : d → ℂ) (x : d), ((V * Vᴴ).mulVec v) x =
            ∑ k : d', U x k.1 * (∑ y : d, star (U y k.1) * v y) := by
          intro v x
          simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, V, Matrix.conjTranspose_apply,
            Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro y _; ring
        have hLHS : ∑ y : d, (∑ z : d, (V * Vᴴ) r z * σ.mat z y) * U y i =
            ((V * Vᴴ).mulVec (σ.mat.mulVec (fun x ↦ U x i))) r := by
          simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro z _; apply Finset.sum_congr rfl; intro y _; ring
        rw [hLHS]
        -- Expand `σ (U e_i)` in the basis `U`: its coefficient along `U e_j` for `j ∉ S_pos` is 0!
        have horth : ∀ j : d, j ∉ S_pos →
            ∑ y : d, star (U y j) * (σ.mat.mulVec (fun x ↦ U x i)) y = 0 := by
          intro j hj
          have hsym : ∑ y : d, star (U y j) * (σ.mat.mulVec (fun x ↦ U x i)) y =
              star (∑ x : d, star (U x i) * (σ.mat.mulVec (fun y ↦ U y j)) x) := by
            simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', star_star, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro y _; apply Finset.sum_congr rfl; intro x _
            have hh := congr_fun (congr_fun σ.isHermitian.eq x) y
            simp only [Matrix.conjTranspose_apply] at hh
            rw [hh]; ring
          rw [hsym, hσ_ker j hj]; simp
        rw [hVVH_apply]
        have hfull : (σ.mat.mulVec (fun x ↦ U x i)) r =
            ∑ j : d, U r j * (∑ y : d, star (U y j) * (σ.mat.mulVec (fun x ↦ U x i)) y) := by
          calc (σ.mat.mulVec (fun x ↦ U x i)) r
              = ((U * star U).mulVec (σ.mat.mulVec (fun x ↦ U x i))) r := by
                rw [Unitary.coe_mul_star_self ρ.eigUnitary, Matrix.one_mulVec]
            _ = _ := by
                simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
                  Finset.sum_mul, Finset.mul_sum]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro y _; ring
        rw [hfull, Finset.sum_coe_sort S_pos (fun j ↦ U r j * (∑ y : d, star (U y j) * (σ.mat.mulVec (fun x ↦ U x i)) y))]
        symm
        apply Finset.sum_subset (Finset.subset_univ S_pos)
        intro j _ hj; rw [horth j hj, mul_zero]
      calc (V * Vᴴ) * σ.mat = ((V * Vᴴ) * σ.mat * U) * star U := by
            rw [Matrix.mul_assoc, Unitary.coe_mul_star_self ρ.eigUnitary, Matrix.mul_one]
        _ = (σ.mat * U) * star U := by rw [hU_eq]
        _ = σ.mat := by rw [Matrix.mul_assoc, Unitary.coe_mul_star_self ρ.eigUnitary, Matrix.mul_one]
    have hσ_VVH : σ.mat * (V * Vᴴ) = σ.mat := by
      have h := congr_arg Matrix.conjTranspose hVVH_σ
      simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, σ.isHermitian.eq] using h
    let σ' : DensityOp d' :=
      { mat := Vᴴ * σ.mat * V
        posSemidef := by
          simpa [Matrix.conjTranspose_conjTranspose] using σ.posSemidef.mul_mul_conjTranspose_same Vᴴ
        trace_one := by
          calc (Vᴴ * σ.mat * V).trace = ((V * Vᴴ) * σ.mat).trace := by
                rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
            _ = σ.mat.trace := by rw [hVVH_σ]
            _ = 1 := σ.trace_one }
    have hσ'_pd : σ'.mat.PosDef := by
      rw [Matrix.posDef_iff_dotProduct_mulVec]
      refine ⟨σ'.isHermitian, fun w hw ↦ ?_⟩
      have hVw_ne : V.mulVec w ≠ 0 := by
        intro h0; apply hw
        have := congr_arg Vᴴ.mulVec h0
        rw [Matrix.mulVec_mulVec, hVHV, Matrix.one_mulVec, Matrix.mulVec_zero] at this
        exact this
      have hρ_pos : (0 : ℂ) < star (V.mulVec w) ⬝ᵥ ρ.mat.mulVec (V.mulVec w) := by
        have hq : star (V.mulVec w) ⬝ᵥ ρ.mat.mulVec (V.mulVec w) = star w ⬝ᵥ ρ'.mat.mulVec w := by
          simp only [ρ', Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
          congr 1; ext j
          simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply,
            Matrix.conjTranspose_apply, star_sum, star_mul', star_star]
          apply Finset.sum_congr rfl; intro i _; ring
        rw [hq]; exact (Matrix.posDef_iff_dotProduct_mulVec.mp hρ'_pd).2 w hw
      have hσ_ne : σ.mat.mulVec (V.mulVec w) ≠ 0 := by
        intro h0
        have hρ0 := suppSubset_ker hsupp.1 (V.mulVec w) h0
        rw [hρ0, dotProduct_zero] at hρ_pos
        exact lt_irrefl 0 hρ_pos
      have hqσ : star w ⬝ᵥ σ'.mat.mulVec w = star (V.mulVec w) ⬝ᵥ σ.mat.mulVec (V.mulVec w) := by
        simp only [σ', Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
        congr 1; ext j
        simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply,
          Matrix.conjTranspose_apply, star_sum, star_mul', star_star]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hqσ]
      have hnn := (Matrix.posSemidef_iff_dotProduct_mulVec.mp σ.posSemidef).2 (V.mulVec w)
      rcases lt_or_eq_of_le hnn with hlt | heq
      · exact hlt
      · exfalso; apply hσ_ne
        -- If `⟨v, σ v⟩ = 0` for `σ ≽ 0`, then `σ v = 0`
        have hre0 := congr_arg Complex.re heq.symm
        rw [re_quadForm_spectral σ.isHermitian (V.mulVec w), Complex.zero_re] at hre0
        have hterm0 : ∀ i : d, σ.isHermitian.eigenvalues i *
            ‖((star (σ.isHermitian.eigenvectorUnitary : Matrix d d ℂ)).mulVec (V.mulVec w)) i‖ ^ 2 = 0 := by
          intro i
          exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
            mul_nonneg (σ.posSemidef.eigenvalues_nonneg j) (sq_nonneg _)).mp hre0 i (Finset.mem_univ i)
        have hspec : σ.mat = (σ.isHermitian.eigenvectorUnitary : Matrix d d ℂ) *
            Matrix.diagonal (Complex.ofReal ∘ σ.isHermitian.eigenvalues) *
            star (σ.isHermitian.eigenvectorUnitary : Matrix d d ℂ) := by
          simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
        conv_lhs => rw [hspec]
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
        have hzero : (fun i : d ↦ (Complex.ofReal ∘ σ.isHermitian.eigenvalues) i *
            ((star (σ.isHermitian.eigenvectorUnitary : Matrix d d ℂ)).mulVec (V.mulVec w)) i) = 0 := by
          ext i
          rcases mul_eq_zero.mp (hterm0 i) with h1 | h2
          · simp [h1]
          · simp [norm_eq_zero.mp (sq_eq_zero_iff.mp h2)]
        rw [hzero, Matrix.mulVec_zero]
    -- `V * ρ' * Vᴴ = ρ`, `V * σ' * Vᴴ = σ`, so `relEntropy` and `qjs` agree!
    have hVρ'VH : V * ρ'.mat * Vᴴ = ρ.mat := by
      have hVVH_ρ : (V * Vᴴ) * ρ.mat = ρ.mat := by
        have hU_eq : ((V * Vᴴ) * ρ.mat) * U = ρ.mat * U := by
          ext r i
          have hLHS : ((V * Vᴴ) * ρ.mat * U) r i =
              ((V * Vᴴ).mulVec (ρ.mat.mulVec (fun x ↦ U x i))) r := by
            simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro z _; apply Finset.sum_congr rfl; intro y _; ring
          rw [hLHS]
          have hVVH_apply : ∀ (v : d → ℂ) (x : d), ((V * Vᴴ).mulVec v) x =
              ∑ k : d', U x k.1 * (∑ y : d, star (U y k.1) * v y) := by
            intro v x
            simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, V, Matrix.conjTranspose_apply,
              Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro y _; ring
          rw [hVVH_apply]
          have horth : ∀ j : d, j ∉ S_pos →
              ∑ y : d, star (U y j) * (ρ.mat.mulVec (fun x ↦ U x i)) y = 0 := by
            intro j hj
            have hsym : ∑ y : d, star (U y j) * (ρ.mat.mulVec (fun x ↦ U x i)) y =
                star (∑ x : d, star (U x i) * (ρ.mat.mulVec (fun y ↦ U y j)) x) := by
              simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', star_star, Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro y _; apply Finset.sum_congr rfl; intro x _
              have hh := congr_fun (congr_fun ρ.isHermitian.eq x) y
              simp only [Matrix.conjTranspose_apply] at hh
              rw [hh]; ring
            rw [hsym, hρ_ker j hj]; simp
          have hfull : (ρ.mat * U) r i =
              ∑ j : d, U r j * (∑ y : d, star (U y j) * (ρ.mat.mulVec (fun x ↦ U x i)) y) := by
            calc (ρ.mat * U) r i
                = ((U * star U).mulVec (ρ.mat.mulVec (fun x ↦ U x i))) r := by
                  rw [Unitary.coe_mul_star_self ρ.eigUnitary, Matrix.one_mulVec]; rfl
              _ = _ := by
                  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
                    Finset.sum_mul, Finset.mul_sum]
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro y _; ring
          rw [hfull, Finset.sum_coe_sort S_pos (fun j ↦ U r j * (∑ y : d, star (U y j) * (ρ.mat.mulVec (fun x ↦ U x i)) y))]
          symm
          apply Finset.sum_subset (Finset.subset_univ S_pos)
          intro j _ hj; rw [horth j hj, mul_zero]
        calc (V * Vᴴ) * ρ.mat = ((V * Vᴴ) * ρ.mat * U) * star U := by
              rw [Matrix.mul_assoc, Unitary.coe_mul_star_self ρ.eigUnitary, Matrix.mul_one]
          _ = (ρ.mat * U) * star U := by rw [hU_eq]
          _ = ρ.mat := by rw [Matrix.mul_assoc, Unitary.coe_mul_star_self ρ.eigUnitary, Matrix.mul_one]
      have hρ_VVH : ρ.mat * (V * Vᴴ) = ρ.mat := by
        have h := congr_arg Matrix.conjTranspose hVVH_ρ
        simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ρ.isHermitian.eq] using h
      calc V * ρ'.mat * Vᴴ = ((V * Vᴴ) * ρ.mat) * (V * Vᴴ) := by simp only [ρ', Matrix.mul_assoc]
        _ = ρ.mat := by rw [hVVH_ρ, hρ_VVH]
    have hVσ'VH : V * σ'.mat * Vᴴ = σ.mat := by
      calc V * σ'.mat * Vᴴ = ((V * Vᴴ) * σ.mat) * (V * Vᴴ) := by simp only [σ', Matrix.mul_assoc]
        _ = σ.mat := by rw [hVVH_σ, hσ_VVH]
    -- Isometric embedding `τ' ↦ V τ' Vᴴ` preserves `vonNeumannEntropy`, `qjs`, and `relEntropy`
    have hS_iso : ∀ (τ' : DensityOp d') (τ : DensityOp d), V * τ'.mat * Vᴴ = τ.mat →
        vonNeumannEntropy τ = vonNeumannEntropy τ' := by
      intro τ' τ hmat
      unfold vonNeumannEntropy DensityOp.eigvals
      congr 1
      let A : Matrix d d' ℂ := V * τ'.sqrtMat
      have hAAH : A * Aᴴ = τ.mat := by
        calc A * Aᴴ = V * (τ'.sqrtMat * τ'.sqrtMat) * Vᴴ := by
              simp only [A, Matrix.conjTranspose_mul, τ'.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
          _ = V * τ'.mat * Vᴴ := by rw [τ'.sqrtMat_mul_self]
          _ = τ.mat := hmat
      have hAHA : Aᴴ * A = τ'.mat := by
        calc Aᴴ * A = τ'.sqrtMat * ((Vᴴ * V) * τ'.sqrtMat) := by
              simp only [A, Matrix.conjTranspose_mul, τ'.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
          _ = τ'.mat := by rw [hVHV, Matrix.one_mul, τ'.sqrtMat_mul_self]
      have hcp := charpoly_mul_conjTranspose_eq A
      rw [hAAH, hAHA] at hcp
      exact spectral_sum_eq_of_charpoly_mul_X_pow τ.isHermitian τ'.isHermitian hcp
        (by simp [Real.negMulLog])
    have hqjs_eq : qjs ρ σ = qjs ρ' σ' := by
      unfold qjs
      rw [hS_iso ρ' ρ hVρ'VH, hS_iso σ' σ hVσ'VH]
      have hmid : V * (DensityOp.midpoint ρ' σ').mat * Vᴴ = (DensityOp.midpoint ρ σ).mat := by
        simp only [DensityOp.midpoint, DensityOp.mix, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_smul, Matrix.smul_mul, hVρ'VH, hVσ'VH]
      rw [hS_iso (DensityOp.midpoint ρ' σ') (DensityOp.midpoint ρ σ) hmid]
    -- Show `relEntropy ρ σ = relEntropy ρ' σ'` and `relEntropy σ ρ = relEntropy σ' ρ'`
    -- via `relEntropy_eq_frenkel`? Even simpler: directly from `relEntropy` definition!
    have hD_iso : ∀ (τ₁' τ₂' : DensityOp d') (τ₁ τ₂ : DensityOp d),
        τ₁'.mat.PosDef → τ₂'.mat.PosDef →
        V * τ₁'.mat * Vᴴ = τ₁.mat → V * τ₂'.mat * Vᴴ = τ₂.mat →
        suppSubset τ₁ τ₂ →
        relEntropy τ₁ τ₂ = relEntropy τ₁' τ₂' := by
      intro τ₁' τ₂' τ₁ τ₂ h1pd h2pd hm1 hm2 hsup
      unfold relEntropy
      have hsup' : suppSubset τ₁' τ₂' := fun _ j _ hj ↦ absurd hj (ne_of_gt (h2pd.eigenvalues_pos j))
      simp only [hsup, hsup', ↓reduceIte]
      congr 1; congr 1
      -- Split `∑ i j ‖W j i‖² (τ₁_i (log τ₁_i - log τ₂_j))` into two sums
      have hsplit : ∀ {α : Type*} [Fintype α] [DecidableEq α] (A B : DensityOp α),
          (∑ i : α, ∑ j : α,
            ‖((star (B.eigUnitary : Matrix α α ℂ)) * (A.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 *
              (A.eigvals i * (Real.log (A.eigvals i) - Real.log (B.eigvals j)))) =
          (∑ i : α, A.eigvals i * Real.log (A.eigvals i)) -
          (∑ i : α, ∑ j : α, A.eigvals i * Real.log (B.eigvals j) *
            ‖((star (B.eigUnitary : Matrix α α ℂ)) * (A.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2) := by
        intro α _ _ A B
        set W : Matrix α α ℂ := star (B.eigUnitary : Matrix α α ℂ) * (A.eigUnitary : Matrix α α ℂ)
        have hcol1 : ∀ i : α, ∑ j : α, ‖W j i‖ ^ 2 = 1 := by
          intro i
          have hU : star W * W = 1 := by
            simp only [W, Matrix.star_mul, star_star, Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (B.eigUnitary : Matrix α α ℂ),
              Unitary.coe_mul_star_self B.eigUnitary, Matrix.one_mul,
              Unitary.coe_star_mul_self A.eigUnitary]
          have hii := congr_arg Complex.re (congr_fun (congr_fun hU i) i)
          simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.one_re,
            Complex.re_sum] at hii
          rw [← hii]
          apply Finset.sum_congr rfl; intro j _
          have hsq : star (W j i) * W j i = ((‖W j i‖ ^ 2 : ℝ) : ℂ) := by
            rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          rw [hsq, Complex.ofReal_re]
        have hrew : (∑ i : α, ∑ j : α, ‖W j i‖ ^ 2 * (A.eigvals i * (Real.log (A.eigvals i) - Real.log (B.eigvals j)))) =
            ∑ i : α, ((∑ j : α, ‖W j i‖ ^ 2) * (A.eigvals i * Real.log (A.eigvals i)) -
              ∑ j : α, A.eigvals i * Real.log (B.eigvals j) * ‖W j i‖ ^ 2) := by
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro j _; ring
        rw [hrew, Finset.sum_sub_distrib]
        congr 1; apply Finset.sum_congr rfl; intro i _; rw [hcol1 i, one_mul]
      rw [hsplit τ₁ τ₂, hsplit τ₁' τ₂']
      have hterm1 : (∑ i : d, τ₁.eigvals i * Real.log (τ₁.eigvals i)) =
          ∑ k : d', τ₁'.eigvals k * Real.log (τ₁'.eigvals k) := by
        have hS := hS_iso τ₁' τ₁ hm1
        unfold vonNeumannEntropy Real.negMulLog at hS
        have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
        have hS' : ∑ i : d, -(τ₁.eigvals i * Real.log (τ₁.eigvals i)) =
            ∑ k : d', -(τ₁'.eigvals k * Real.log (τ₁'.eigvals k)) := by
          field_simp [hlog2] at hS; linarith
        simp only [Finset.sum_neg_distrib] at hS'
        linarith
      have hterm2 : (∑ i : d, ∑ j : d, τ₁.eigvals i * Real.log (τ₂.eigvals j) *
            ‖((star (τ₂.eigUnitary : Matrix d d ℂ)) * (τ₁.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2) =
          ∑ i : d', ∑ j : d', τ₁'.eigvals i * Real.log (τ₂'.eigvals j) *
            ‖((star (τ₂'.eigUnitary : Matrix d' d' ℂ)) * (τ₁'.eigUnitary : Matrix d' d' ℂ)) j i‖ ^ 2 := by
        let L₂ : Matrix d d ℂ := (τ₂.eigUnitary : Matrix d d ℂ) *
          Matrix.diagonal (fun j ↦ (Real.log (τ₂.eigvals j) : ℂ)) *
          star (τ₂.eigUnitary : Matrix d d ℂ)
        let L₂' : Matrix d' d' ℂ := (τ₂'.eigUnitary : Matrix d' d' ℂ) *
          Matrix.diagonal (fun j ↦ (Real.log (τ₂'.eigvals j) : ℂ)) *
          star (τ₂'.eigUnitary : Matrix d' d' ℂ)
        have htr_eq : ∀ {α : Type*} [Fintype α] [DecidableEq α] (A B : DensityOp α),
            (∑ i : α, ∑ j : α, A.eigvals i * Real.log (B.eigvals j) *
              ‖((star (B.eigUnitary : Matrix α α ℂ)) * (A.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2) =
            (A.mat * ((B.eigUnitary : Matrix α α ℂ) *
              Matrix.diagonal (fun j ↦ (Real.log (B.eigvals j) : ℂ)) *
              star (B.eigUnitary : Matrix α α ℂ))).trace.re := by
          intro α _ _ A B
          set UA : Matrix α α ℂ := (A.eigUnitary : Matrix α α ℂ)
          set UB : Matrix α α ℂ := (B.eigUnitary : Matrix α α ℂ)
          have hspecA : A.mat = UA * Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * star UA := by
            simpa [UA, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
              Unitary.conjStarAlgAut_apply] using A.isHermitian.spectral_theorem
          set W : Matrix α α ℂ := star UB * UA
          have htrC : (A.mat * (UB * Matrix.diagonal (fun j ↦ (Real.log (B.eigvals j) : ℂ)) * star UB)).trace =
              (Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *
                (star W * Matrix.diagonal (fun j ↦ (Real.log (B.eigvals j) : ℂ)) * W)).trace := by
            conv_lhs => rw [hspecA]
            have hstarW : star W = star UA * UB := by
              simp [W, Matrix.star_mul, star_star]
            rw [hstarW]
            calc (UA * Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * star UA *
                    (UB * Matrix.diagonal (fun j ↦ (Real.log (B.eigvals j) : ℂ)) * star UB)).trace
                = (Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *
                    (star UA * UB * Matrix.diagonal (fun j ↦ (Real.log (B.eigvals j) : ℂ)) * (star UB * UA))).trace := by
                  rw [Matrix.trace_mul_comm UA]; simp only [Matrix.mul_assoc]
              _ = _ := rfl
          rw [htrC]
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
            Function.comp_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
            Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Complex.re_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _
          rw [Complex.re_sum]
          apply Finset.sum_congr rfl; intro j _
          have hsq : (star (W j i) * W j i) = ((‖W j i‖ ^ 2 : ℝ) : ℂ) := by
            rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          have hcalc : (A.eigvals i : ℂ) * (star (W j i) * (Real.log (B.eigvals j) : ℂ) * W j i) =
              ((A.eigvals i * Real.log (B.eigvals j) * ‖W j i‖ ^ 2 : ℝ) : ℂ) := by
            calc _ = (A.eigvals i : ℂ) * (Real.log (B.eigvals j) : ℂ) * (star (W j i) * W j i) := by ring
              _ = _ := by rw [hsq]; push_cast; ring
          simp only [Matrix.star_apply]
          rw [hcalc, Complex.ofReal_re]
        rw [htr_eq τ₁ τ₂, htr_eq τ₁' τ₂']
        have hL_eq : V * L₂' * Vᴴ = L₂ := by
          set U₂' : Matrix d' d' ℂ := (τ₂'.eigUnitary : Matrix d' d' ℂ)
          have hspec2' : τ₂'.mat = U₂' * Matrix.diagonal (Complex.ofReal ∘ τ₂'.eigvals) * star U₂' := by
            simpa [U₂', DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
              Unitary.conjStarAlgAut_apply] using τ₂'.isHermitian.spectral_theorem
          set U₂ : Matrix d d ℂ := (τ₂.eigUnitary : Matrix d d ℂ)
          have hspec2 : τ₂.mat = U₂ * Matrix.diagonal (Complex.ofReal ∘ τ₂.eigvals) * star U₂ := by
            simpa [U₂, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
              Unitary.conjStarAlgAut_apply] using τ₂.isHermitian.spectral_theorem
          have hcol_eq : ∀ j : d, (V * L₂' * Vᴴ).mulVec (fun r ↦ U₂ r j) =
              L₂.mulVec (fun r ↦ U₂ r j) := by
            intro j
            have hR : L₂.mulVec (fun r ↦ U₂ r j) =
                (Real.log (τ₂.eigvals j) : ℂ) • (fun r ↦ U₂ r j) := by
              have hcol : (star U₂).mulVec (fun r ↦ U₂ r j) = Pi.single j 1 := by
                ext k
                have h := congr_fun (congr_fun (Unitary.coe_star_mul_self τ₂.eigUnitary) k) j
                simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
                  Matrix.one_apply, Pi.single_apply, eq_comm] using h
              simp only [L₂]
              rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcol, Matrix.mulVec_diagonal]
              ext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
            rw [hR]
            have hτ2_eig : τ₂.mat.mulVec (fun r ↦ U₂ r j) =
                (τ₂.eigvals j : ℂ) • (fun r ↦ U₂ r j) := by
              have hcol : (star U₂).mulVec (fun r ↦ U₂ r j) = Pi.single j 1 := by
                ext k
                have h := congr_fun (congr_fun (Unitary.coe_star_mul_self τ₂.eigUnitary) k) j
                simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
                  Matrix.one_apply, Pi.single_apply, eq_comm] using h
              conv_lhs => rw [hspec2]
              rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcol, Matrix.mulVec_diagonal]
              ext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
            by_cases hj0 : τ₂.eigvals j = 0
            · rw [hj0, Real.log_zero, Complex.ofReal_zero, zero_smul]
              have hVh0 : Vᴴ.mulVec (fun r ↦ U₂ r j) = 0 := by
                have h0 : (V * τ₂'.mat * Vᴴ).mulVec (fun r ↦ U₂ r j) = 0 := by
                  rw [hm2, hτ2_eig, hj0, Complex.ofReal_zero, zero_smul]
                have h1 := congr_arg Vᴴ.mulVec h0
                rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc Vᴴ, ← Matrix.mul_assoc Vᴴ,
                  hVHV, Matrix.one_mul, Matrix.mulVec_zero, Matrix.mulVec_mulVec] at h1
                by_contra hne
                have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp h2pd).2 _ hne
                rw [h1, dotProduct_zero] at hp; exact lt_irrefl 0 hp
              rw [Matrix.mulVec_mulVec, hVh0, Matrix.mulVec_zero]
            · set w : d' → ℂ := Vᴴ.mulVec (fun r ↦ U₂ r j)
              have hVw : V.mulVec w = fun r ↦ U₂ r j := by
                have h1 : (V * Vᴴ).mulVec (τ₂.mat.mulVec (fun r ↦ U₂ r j)) =
                    τ₂.mat.mulVec (fun r ↦ U₂ r j) := by
                  rw [← Matrix.mulVec_mulVec, ← hm2, ← Matrix.mul_assoc (V * Vᴴ),
                    Matrix.mul_assoc V, hVHV, Matrix.mul_one]
                rw [hτ2_eig, Matrix.mulVec_smul] at h1
                have hneC : (τ₂.eigvals j : ℂ) ≠ 0 := by exact_mod_cast hj0
                have := congr_arg (fun v : d → ℂ ↦ (τ₂.eigvals j : ℂ)⁻¹ • v) h1
                simp only [smul_smul, inv_mul_cancel₀ hneC, one_smul] at this
                simpa [w, Matrix.mulVec_mulVec] using this
              have hτ2'_w : τ₂'.mat.mulVec w = (τ₂.eigvals j : ℂ) • w := by
                have h1 := congr_arg Vᴴ.mulVec hτ2_eig
                rw [← hm2, Matrix.mulVec_mulVec, ← Matrix.mul_assoc Vᴴ, ← Matrix.mul_assoc Vᴴ,
                  hVHV, Matrix.one_mul, Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h1
                exact h1
              set y : d' → ℂ := (star U₂').mulVec w
              have hy_coord : ∀ k : d', τ₂'.eigvals k ≠ τ₂.eigvals j → y k = 0 := by
                intro k hk
                have h1 := congr_arg (fun v ↦ ((star U₂').mulVec v) k) hτ2'_w
                have hL : ((star U₂').mulVec (τ₂'.mat.mulVec w)) k = (τ₂'.eigvals k : ℂ) * y k := by
                  conv_lhs => rw [hspec2']
                  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc (star U₂'), ← Matrix.mul_assoc (star U₂'),
                    Unitary.coe_star_mul_self τ₂'.eigUnitary, Matrix.one_mul, Matrix.mulVec_mulVec,
                    Matrix.mulVec_diagonal]
                  rfl
                rw [hL, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h1
                have hsub : ((τ₂'.eigvals k : ℂ) - (τ₂.eigvals j : ℂ)) * y k = 0 := by linear_combination h1
                have hneC : (τ₂'.eigvals k : ℂ) - (τ₂.eigvals j : ℂ) ≠ 0 := by
                  rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.mpr hk
                exact (mul_eq_zero.mp hsub).resolve_left hneC
              have hL2'_w : L₂'.mulVec w = (Real.log (τ₂.eigvals j) : ℂ) • w := by
                simp only [L₂']
                rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
                have hdiag : (fun k : d' ↦ (Real.log (τ₂'.eigvals k) : ℂ) * y k) =
                    (Real.log (τ₂.eigvals j) : ℂ) • y := by
                  ext k; simp only [Pi.smul_apply, smul_eq_mul]
                  by_cases hk : τ₂'.eigvals k = τ₂.eigvals j
                  · rw [hk]
                  · rw [hy_coord k hk, mul_zero, mul_zero]
                rw [hdiag, Matrix.mulVec_smul, show U₂'.mulVec y = w by
                  simp only [y, Matrix.mulVec_mulVec, Unitary.coe_mul_star_self τ₂'.eigUnitary,
                    Matrix.one_mulVec]]
              rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hL2'_w, Matrix.mulVec_smul, hVw]
          have hmulU : (V * L₂' * Vᴴ) * U₂ = L₂ * U₂ := by
            ext r j; exact congr_fun (hcol_eq j) r
          calc V * L₂' * Vᴴ = ((V * L₂' * Vᴴ) * U₂) * star U₂ := by
                rw [Matrix.mul_assoc, Unitary.coe_mul_star_self τ₂.eigUnitary, Matrix.mul_one]
            _ = (L₂ * U₂) * star U₂ := by rw [hmulU]
            _ = L₂ := by rw [Matrix.mul_assoc, Unitary.coe_mul_star_self τ₂.eigUnitary, Matrix.mul_one]
        rw [← hL_eq, ← hm1]
        congr 1
        calc (V * τ₁'.mat * Vᴴ * (V * L₂' * Vᴴ)).trace
            = (V * τ₁'.mat * ((Vᴴ * V) * L₂') * Vᴴ).trace := by simp only [Matrix.mul_assoc]
          _ = (V * (τ₁'.mat * L₂') * Vᴴ).trace := by rw [hVHV, Matrix.one_mul]; simp only [Matrix.mul_assoc]
          _ = (τ₁'.mat * L₂').trace := by
                rw [Matrix.trace_mul_cycle, hVHV, Matrix.one_mul]
      linarith
    have hD1 := hD_iso ρ' σ' ρ σ hρ'_pd hσ'_pd hVρ'VH hVσ'VH hsupp.1
    have hD2 := hD_iso σ' ρ' σ ρ hσ'_pd hρ'_pd hVσ'VH hVρ'VH hsupp.2
    rw [hqjs_eq, hD1, hD2]
    have hmain := prop_3_3_qjjs_posDef hρ'_pd hσ'_pd
    have hfin1 : relEntropy ρ' σ' ≠ ⊤ := by
      unfold relEntropy
      have hs : suppSubset ρ' σ' := fun _ j _ hj ↦ absurd hj (ne_of_gt (hσ'_pd.eigenvalues_pos j))
      simp [hs]
    have hfin2 : relEntropy σ' ρ' ≠ ⊤ := by
      unfold relEntropy
      have hs : suppSubset σ' ρ' := fun _ j _ hj ↦ absurd hj (ne_of_gt (hρ'_pd.eigenvalues_pos j))
      simp [hs]
    have hc_lt1 : qjs ρ' σ' < 1 := by
      -- Since `qjs ρ' σ' ≤ 1` and if `qjs ρ' σ' = 1` then `phi 1` wouldn't be needed;
      -- actually `lemma_3_2_hockeyStick_measure` gives `qjs ρ' σ' < 1` directly!
      by_contra hge; push_neg at hge
      -- From `prop_3_3_qjjs_posDef`'s proof, `qjs ρ' σ' < 1` always holds for `PosDef` states:
      -- we can deduce it cleanly from `qjs ρ' σ' ≤ 1` and strict concavity or `lemma_3_2`!
      obtain ⟨a, b, μ, ha, hab, hprob, hsuppμ, _, hmean, _, _, hEq36⟩ :=
        lemma_3_2_hockeyStick_measure hρ'_pd hσ'_pd
      have hlt_pt : ∀ t ∈ Icc a b,
          t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t)) < (1 + t) / 2 := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
        have h1 : Real.logb 2 (2 * t / (1 + t)) < 1 := by
          rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity), Real.rpow_one,
            div_lt_iff₀ (by linarith)]; linarith
        have h2 : Real.logb 2 (2 / (1 + t)) < 1 := by
          rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity), Real.rpow_one,
            div_lt_iff₀ (by linarith)]; linarith
        nlinarith
      have hcont_diff : ContinuousOn (fun t : ℝ ↦
          (1 + t) / 2 - (t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t)))) (Icc a b) := by
        refine ContinuousOn.sub (by fun_prop) (ContinuousOn.add ?_ ?_)
        · refine (continuousOn_id.div_const 2).mul (ContinuousOn.div_const ?_ _)
          refine Real.continuousOn_log.comp ?_ ?_
          · exact (continuousOn_const.mul continuousOn_id).div (continuousOn_const.add continuousOn_id)
              fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
          · intro t ht; exact ne_of_gt (div_pos (by linarith [lt_of_lt_of_le ha ht.1])
              (by linarith [lt_of_lt_of_le ha ht.1]))
        · refine continuousOn_const.mul (ContinuousOn.div_const ?_ _)
          refine Real.continuousOn_log.comp ?_ ?_
          · exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
              fun t ht ↦ ne_of_gt (by linarith [lt_of_lt_of_le ha ht.1])
          · intro t ht; exact ne_of_gt (div_pos two_pos (by linarith [lt_of_lt_of_le ha ht.1]))
      obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, left_mem_Icc.mpr hab⟩ hcont_diff
      set δ := (1 + t₀) / 2 - (t₀ / 2 * Real.logb 2 (2 * t₀ / (1 + t₀)) + 1 / 2 * Real.logb 2 (2 / (1 + t₀)))
      have hδ_pos : 0 < δ := sub_pos.mpr (hlt_pt t₀ ht₀)
      have hI_lhs : Integrable (fun t : ℝ ↦
          t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) μ := by
        have hcont : ContinuousOn (fun t : ℝ ↦
            t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) (Icc a b) := by
          have := (show ContinuousOn (fun t : ℝ ↦ (1 + t) / 2) (Icc a b) by fun_prop).sub hcont_diff
          exact this.congr fun t _ ↦ by ring
        obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
        have hm : AEStronglyMeasurable (fun t : ℝ ↦
            t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) μ := by
          refine (hcont.stronglyMeasurable_of_isClosed isClosed_Icc).aestronglyMeasurable.congr ?_
          filter_upwards [measure_zero_iff_ae_nmem.mp hsuppμ] with t ht
          simp only [Set.mem_compl_iff, not_not] at ht; exact Set.indicator_of_mem ht _
        refine Integrable.mono' (integrable_const M) hm ?_
        filter_upwards [measure_zero_iff_ae_nmem.mp hsuppμ] with t ht
        simp only [Set.mem_compl_iff, not_not] at ht; exact hM t ht
      have hI_rhs : Integrable (fun t : ℝ ↦ (1 + t) / 2) μ := by
        have hcont : ContinuousOn (fun t : ℝ ↦ (1 + t) / 2) (Icc a b) := by fun_prop
        obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
        refine Integrable.mono' (integrable_const M) (by fun_prop) ?_
        filter_upwards [measure_zero_iff_ae_nmem.mp hsuppμ] with t ht
        simp only [Set.mem_compl_iff, not_not] at ht; exact hM t ht
      have hint_le : ∫ t, (t / 2 * Real.logb 2 (2 * t / (1 + t)) + 1 / 2 * Real.logb 2 (2 / (1 + t))) ∂μ ≤
          ∫ t, ((1 + t) / 2 - δ) ∂μ := by
        apply integral_mono_ae hI_lhs (hI_rhs.sub (integrable_const δ))
        filter_upwards [measure_zero_iff_ae_nmem.mp hsuppμ] with t ht
        simp only [Set.mem_compl_iff, not_not] at ht; linarith [hmin ht]
      have hrhs_val : ∫ t, ((1 + t) / 2 - δ) ∂μ = 1 - δ := by
        have hint_t : Integrable (fun t : ℝ ↦ t) μ := by
          refine Integrable.mono' (integrable_const b) continuous_id.aestronglyMeasurable ?_
          filter_upwards [measure_zero_iff_ae_nmem.mp hsuppμ] with t ht
          simp only [Set.mem_compl_iff, not_not, Set.mem_Icc] at ht
          rw [Real.norm_of_nonneg (by linarith [ht.1])]; exact ht.2
        rw [integral_sub hI_rhs (integrable_const δ), integral_div, integral_add (integrable_const 1) hint_t,
          integral_const, smul_eq_mul, hmean, show (μ univ).toReal = 1 by rw [measure_univ]; simp,
          integral_const, smul_eq_mul, show (μ univ).toReal = 1 by rw [measure_univ]; simp]
        ring
      linarith
    unfold phiExt
    simp only [hc_lt1, ↓reduceIte]
    have hRHS : (1 / 4 : ℝ≥0∞) * (relEntropy ρ' σ' + relEntropy σ' ρ') =
        ENNReal.ofReal ((1 / 4 : ℝ) * ((relEntropy ρ' σ').toReal + (relEntropy σ' ρ').toReal)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hfin1, ENNReal.ofReal_toReal hfin2]
      congr 1; norm_num
    rw [hRHS]
    exact ENNReal.ofReal_le_ofReal hmain
  · -- If `supp(ρ) ≠ supp(σ)`, then `D(ρ ‖ σ) + D(σ ‖ ρ) = ⊤`
    have htop : relEntropy ρ σ + relEntropy σ ρ = ⊤ := by
      by_cases h1 : suppSubset ρ σ
      · have h2 : ¬ suppSubset σ ρ := fun h2 ↦ hsupp ⟨h1, h2⟩
        unfold relEntropy; simp [h2]
      · unfold relEntropy; simp [h1]
    rw [htop, ENNReal.mul_top (by norm_num : (1 / 4 : ℝ≥0∞) ≠ 0)]
    exact le_top

end PolarCodes
