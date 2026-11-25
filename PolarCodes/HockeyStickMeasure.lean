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

private lemma tonelli_set_real {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S : Set ℝ} {K : ℝ → ℝ → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) :
    ∫⁻ s in S, ∫⁻ t, K s t ∂μ ∂volume = ∫⁻ t, ∫⁻ s in S, K s t ∂volume ∂μ :=
  lintegral_lintegral_swap hK.aemeasurable

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
    show convexRightDeriv f s + 1 = 0; rw [convexRightDeriv_eq_neg_one hf_conv hleft hright hs]; ring
  have hF_right : ∀ s ≥ b, F s = 1 := fun s hs ↦ by
    show convexRightDeriv f s + 1 = 1; rw [convexRightDeriv_eq_zero hf_conv hleft hright hs]; ring
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
      ext x; simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
        not_and_or, not_le]
    rw [hcompl]
    exact measure_union_null hsupp_left hsupp_right
  have hae_supp : ∀ᵐ t ∂μ, t ∈ Icc a b := ae_iff.mpr hsupp
  -- Probability measure: `μ univ = 1`
  have hμ_univ : μ univ = 1 := by
    have huniv : (univ : Set ℝ) = Iic (a - 1) ∪ Ioc (a - 1) b ∪ Ioi b := by
      ext x; simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioc, Set.mem_Ioi, true_iff]
      rcases le_or_gt x (a - 1) with h1 | h1
      · left; left; exact h1
      · rcases le_or_gt x b with h2 | h2
        · left; right; exact ⟨h1, h2⟩
        · right; exact h2
    have hIic1 : μ (Iic (a - 1)) = 0 :=
      measure_mono_null (fun x hx ↦ lt_of_le_of_lt (Set.mem_Iic.mp hx) (by linarith)) hsupp_left
    have hdisj1 : Disjoint (Iic (a - 1)) (Ioc (a - 1) b) :=
      Set.disjoint_left.mpr fun x h1 h2 ↦ not_lt.mpr (Set.mem_Iic.mp h1) h2.1
    have h1 : μ (Iic (a - 1) ∪ Ioc (a - 1) b) = μ (Ioc (a - 1) b) := by
      rw [measure_union hdisj1 measurableSet_Ioc, hIic1, zero_add]
    have hdisj2 : Disjoint (Iic (a - 1) ∪ Ioc (a - 1) b) (Ioi b) :=
      Set.disjoint_left.mpr fun x h1 h2 ↦ by
        rcases h1 with h1 | h1
        · linarith [Set.mem_Iic.mp h1, Set.mem_Ioi.mp h2]
        · exact not_lt.mpr h1.2 (Set.mem_Ioi.mp h2)
    have h2 : μ (Iic (a - 1) ∪ Ioc (a - 1) b ∪ Ioi b) = μ (Ioc (a - 1) b) := by
      rw [measure_union hdisj2 measurableSet_Ioi, hsupp_right, add_zero, h1]
    rw [huniv, h2, StieltjesFunction.measure_Ioc, hF_right b le_rfl, hF_left (a - 1) (by linarith),
      sub_zero, ENNReal.ofReal_one]
  haveI hprob : IsProbabilityMeasure μ := ⟨hμ_univ⟩
  have hμ_real_univ : μ.real univ = 1 := by simp [Measure.real, hμ_univ]
  -- Tail measure identity: `μ (Ioi u) = ENNReal.ofReal (-g u)`
  have hμ_Ioi : ∀ u : ℝ, μ (Ioi u) = ENNReal.ofReal (-g u) := by
    intro u
    rcases le_or_gt b u with hbu | hub
    · have h0 : μ (Ioi u) = 0 := measure_mono_null (Set.Ioi_subset_Ioi hbu) hsupp_right
      dsimp only [g]
      rw [h0, convexRightDeriv_eq_zero hf_conv hleft hright hbu, neg_zero, ENNReal.ofReal_zero]
    · have hsplit : Ioi u = Ioc u b ∪ Ioi b := (Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hub)).symm
      have hdisj : Disjoint (Ioc u b) (Ioi b) :=
        Set.disjoint_left.mpr fun x h1 h2 ↦ not_lt.mpr h1.2 (Set.mem_Ioi.mp h2)
      rw [hsplit, measure_union hdisj measurableSet_Ioi, hsupp_right, add_zero,
        StieltjesFunction.measure_Ioc, hF_right b le_rfl]
      congr 1; show 1 - (g u + 1) = -g u; ring
  -- Hockey-stick representation: `hockeyStick s ρ σ = ∫ t, max (t - s) 0 ∂μ`
  have hrep : ∀ s : ℝ, hockeyStick s ρ σ = ∫ t, max (t - s) 0 ∂μ := by
    intro s
    rcases le_or_gt b s with hbs | hsb
    · rw [hright s hbs]
      symm
      apply integral_eq_zero_of_ae
      filter_upwards [hae_supp] with t ht
      exact max_eq_right (by linarith [ht.2])
    · have hftc := sub_eq_intervalIntegral_convexRightDeriv hf_conv hleft hright (le_of_lt hsb)
      change hockeyStick b ρ σ - hockeyStick s ρ σ = _ at hftc
      rw [hright b le_rfl, zero_sub] at hftc
      have hf_eq : hockeyStick s ρ σ = ∫ u in Ioc s b, (-g u) ∂volume := by
        rw [← intervalIntegral.integral_of_le (le_of_lt hsb), intervalIntegral.integral_neg]
        linarith
      have hf_nn : 0 ≤ hockeyStick s ρ σ := posPartTrace_nonneg _
      have hg_nn : ∀ u : ℝ, 0 ≤ -g u := fun u ↦ by
        linarith [(convexRightDeriv_bounds hf_conv hleft hright u).2]
      have hint_g : IntegrableOn (fun u ↦ -g u) (Ioc s b) volume :=
        ((convexRightDeriv_mono hf_conv hleft hright).intervalIntegrable.neg).1
      -- Tonelli on `Ioc s b × ℝ`
      have hton : ENNReal.ofReal (hockeyStick s ρ σ) = ∫⁻ t, ENNReal.ofReal (max (t - s) 0) ∂μ := by
        rw [hf_eq, ofReal_integral_eq_lintegral_ofReal hint_g
          ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u _ ↦ hg_nn u))]
        have hstep1 : ∫⁻ u in Ioc s b, ENNReal.ofReal (-g u) ∂volume =
            ∫⁻ u in Ioc s b, ∫⁻ t, Set.indicator (Ioi u) (fun _ ↦ (1 : ℝ≥0∞)) t ∂μ ∂volume := by
          apply setLIntegral_congr_fun measurableSet_Ioc
          intro u _; dsimp only
          rw [lintegral_indicator measurableSet_Ioi, setLIntegral_const, one_mul, hμ_Ioi u]
        have hmeas_ind : Measurable (Function.uncurry fun u t : ℝ ↦ Set.indicator (Ioi u) (fun _ ↦ (1 : ℝ≥0∞)) t) := by
          have heq : (Function.uncurry fun u t : ℝ ↦ Set.indicator (Ioi u) (fun _ ↦ (1 : ℝ≥0∞)) t) =
              Set.indicator {q : ℝ × ℝ | q.1 < q.2} (fun _ ↦ (1 : ℝ≥0∞)) := by
            ext ⟨u, t⟩; rfl
          rw [heq]; exact measurable_const.indicator (measurableSet_lt measurable_fst measurable_snd)
        rw [hstep1, tonelli_set_real hmeas_ind]
        apply lintegral_congr_ae
        filter_upwards [hae_supp] with t ht
        have hset : ∫⁻ u in Ioc s b, Set.indicator (Ioi u) (fun _ ↦ (1 : ℝ≥0∞)) t ∂volume =
            ∫⁻ u in Ioc s b, Set.indicator (Iio t) (fun _ ↦ (1 : ℝ≥0∞)) u ∂volume := by
          apply setLIntegral_congr_fun measurableSet_Ioc
          intro u _; dsimp only; by_cases h : u < t <;> simp [Set.indicator, h]
        rw [hset, lintegral_indicator measurableSet_Iio, setLIntegral_const, one_mul,
          Measure.restrict_apply measurableSet_Iio]
        rcases le_or_gt t s with hts | hst
        · have hemp : Iio t ∩ Ioc s b = ∅ := by
            ext u; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_empty_iff_false,
              iff_false, not_and]; intro h1 h2 _; linarith
          rw [hemp, measure_empty, max_eq_right (by linarith), ENNReal.ofReal_zero]
        · have hinter : Iio t ∩ Ioc s b = Ioo s t := by
            ext u; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
            constructor
            · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
            · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans (le_of_lt h2) ht.2⟩
          rw [hinter, Real.volume_Ioo, max_eq_left (by linarith)]
      have hint_max : Integrable (fun t : ℝ ↦ max (t - s) 0) μ := by
        apply Integrable.mono' (integrable_const (max (b - s) 0))
        · exact ((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable
        · filter_upwards [hae_supp] with t ht
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
    rw [h0]
    apply integral_congr_ae
    filter_upwards [hae_supp] with t ht
    rw [sub_zero, max_eq_left (by linarith [ht.1])]
  have hmean_sub : ∫ t, (t - 1) ∂μ = 0 := by
    have hint_t : Integrable (fun t : ℝ ↦ t) μ := by
      apply Integrable.mono' (integrable_const b) (continuous_id : Continuous (fun t : ℝ ↦ t)).aestronglyMeasurable
      filter_upwards [hae_supp] with t ht
      dsimp only [id]; rw [Real.norm_of_nonneg (by linarith [ht.1])]; exact ht.2
    rw [integral_sub hint_t (integrable_const 1), hmean, integral_const, smul_eq_mul,
      hμ_real_univ]
    ring
  -- Helper: integrability of any continuous function on `[a, b]` with respect to `μ`
  have hint_of_cont : ∀ (φ : ℝ → ℝ), ContinuousOn φ (Icc a b) → Integrable φ μ := by
    intro φ hφ
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
    have hae_meas : AEStronglyMeasurable φ μ := by
      have hrest : μ.restrict (Icc a b) = μ := Measure.restrict_eq_self_of_ae_mem hae_supp
      rw [← hrest]
      exact hφ.aestronglyMeasurable measurableSet_Icc
    refine Integrable.mono' (integrable_const M) hae_meas ?_
    filter_upwards [hae_supp] with t ht
    exact hM t ht
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Eq. (3.4): `D(ρ ‖ σ)`
  have hEq34 : (relEntropy ρ σ).toReal = ∫ t, (t * Real.logb 2 t - (t - 1) / Real.log 2) ∂μ := by
    have h38 := relEntropy_hockeyStick_integral hρ hσ
    -- Split `Ioi 0 = Ioc 0 1 ∪ Ioi 1`
    have hsplit : (∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal ((hockeyStick s ρ σ - max (1 - s) 0) / s) ∂volume) =
        (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ((hockeyStick s ρ σ - (1 - s)) / s) ∂volume) +
        (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (hockeyStick s ρ σ / s) ∂volume) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
        lintegral_union measurableSet_Ioi
          (Set.disjoint_left.mpr fun x h1 h2 ↦ not_lt.mpr h1.2 h2)]
      congr 1
      · apply setLIntegral_congr_fun measurableSet_Ioc
        intro s hs; dsimp only; rw [max_eq_left (by linarith [hs.2])]
      · apply setLIntegral_congr_fun measurableSet_Ioi
        intro s hs; dsimp only; rw [max_eq_right (by linarith [Set.mem_Ioi.mp hs]), sub_zero]
    rw [hsplit] at h38
    -- Express `hockeyStick s ρ σ - (1 - s) = ∫ max (s - t) 0 ∂μ` for `s ∈ (0, 1]`
    have hleft_int : ∀ s ∈ Ioc (0 : ℝ) 1,
        ENNReal.ofReal ((hockeyStick s ρ σ - (1 - s)) / s) =
          ∫⁻ t, ENNReal.ofReal (max (s - t) 0 / s) ∂μ := by
      intro s hs
      have hs0 : 0 < s := hs.1
      have h1 : hockeyStick s ρ σ - (1 - s) = ∫ t, max (s - t) 0 ∂μ := by
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
            hμ_real_univ, one_mul]
        rw [hsub]
        simp_rw [heq]
        rw [integral_add hI2 hI3, hmean_sub, add_zero]
      rw [h1, ← integral_div]
      have hI : Integrable (fun t : ℝ ↦ max (s - t) 0 / s) μ :=
        (hint_of_cont _ ((continuous_const.sub continuous_id).max continuous_const).continuousOn).div_const s
      exact ofReal_integral_eq_lintegral_ofReal hI
        (Eventually.of_forall fun t ↦ div_nonneg (le_max_right _ _) (le_of_lt hs0))
    have hright_int : ∀ s ∈ Ioi (1 : ℝ),
        ENNReal.ofReal (hockeyStick s ρ σ / s) = ∫⁻ t, ENNReal.ofReal (max (t - s) 0 / s) ∂μ := by
      intro s hs
      have hs0 : 0 < s := by linarith [Set.mem_Ioi.mp hs]
      rw [hrep s, ← integral_div]
      have hI : Integrable (fun t : ℝ ↦ max (t - s) 0 / s) μ :=
        (hint_of_cont _ ((continuous_id.sub continuous_const).max continuous_const).continuousOn).div_const s
      exact ofReal_integral_eq_lintegral_ofReal hI
        (Eventually.of_forall fun t ↦ div_nonneg (le_max_right _ _) (le_of_lt hs0))
    have hl_swap : (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ((hockeyStick s ρ σ - (1 - s)) / s) ∂volume) =
        ∫⁻ t, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s - t) 0 / s) ∂volume ∂μ := by
      rw [setLIntegral_congr_fun measurableSet_Ioc hleft_int]
      exact tonelli_set_real (ENNReal.measurable_ofReal.comp
        (((measurable_fst.sub measurable_snd).max measurable_const).div measurable_fst))
    have hr_swap : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (hockeyStick s ρ σ / s) ∂volume) =
        ∫⁻ t, ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t - s) 0 / s) ∂volume ∂μ := by
      rw [setLIntegral_congr_fun measurableSet_Ioi hright_int]
      exact tonelli_set_real (ENNReal.measurable_ofReal.comp
        (((measurable_snd.sub measurable_fst).max measurable_const).div measurable_fst))
    rw [hl_swap, hr_swap, ← lintegral_add_left] at h38
    · have hker : (∫⁻ t, ((∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s - t) 0 / s) ∂volume) +
            (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t - s) 0 / s) ∂volume)) ∂μ) =
          ∫⁻ t, ENNReal.ofReal (t * Real.log t - (t - 1)) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hae_supp] with t ht
        exact lintegral_hockeyStick_kernel_1 (lt_of_lt_of_le ha ht.1)
      rw [hker] at h38
      have hI_ker : Integrable (fun t : ℝ ↦ t * Real.log t - (t - 1)) μ := by
        apply hint_of_cont
        exact (continuousOn_id.mul (Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (lt_of_lt_of_le ha ht.1))).sub
          (continuousOn_id.sub continuousOn_const)
      have hnn_ker : ∀ᵐ t ∂μ, 0 ≤ t * Real.log t - (t - 1) := by
        filter_upwards [hae_supp] with t ht
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
          ((hint_of_cont (fun t : ℝ ↦ t) continuousOn_id).const_mul s), integral_const, smul_eq_mul,
          hμ_real_univ, one_mul, integral_const_mul, hmean, mul_one]
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
        intro s hs; dsimp only; rw [max_eq_left (by linarith [hs.2])]
      · apply setLIntegral_congr_fun measurableSet_Ioi
        intro s hs; dsimp only; rw [max_eq_right (by linarith [Set.mem_Ioi.mp hs]), sub_zero]
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
            hμ_real_univ, one_mul]
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
      rw [setLIntegral_congr_fun measurableSet_Ioc hleft_int]
      exact tonelli_set_real (ENNReal.measurable_ofReal.comp
        ((((measurable_fst.mul measurable_snd).sub measurable_const).max measurable_const).div measurable_fst))
    have hr_swap : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (hockeyStick s σ ρ / s) ∂volume) =
        ∫⁻ t, ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (1 - s * t) 0 / s) ∂volume ∂μ := by
      rw [setLIntegral_congr_fun measurableSet_Ioi hright_int]
      exact tonelli_set_real (ENNReal.measurable_ofReal.comp
        (((measurable_const.sub (measurable_fst.mul measurable_snd)).max measurable_const).div measurable_fst))
    rw [hl_swap, hr_swap, ← lintegral_add_left] at h38
    · have hker : (∫⁻ t, ((∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * t - 1) 0 / s) ∂volume) +
            (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (1 - s * t) 0 / s) ∂volume)) ∂μ) =
          ∫⁻ t, ENNReal.ofReal (-Real.log t + (t - 1)) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hae_supp] with t ht
        exact lintegral_hockeyStick_kernel_2 (lt_of_lt_of_le ha ht.1)
      rw [hker] at h38
      have hI_ker : Integrable (fun t : ℝ ↦ -Real.log t + (t - 1)) μ := by
        apply hint_of_cont
        exact (Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (lt_of_lt_of_le ha ht.1)).neg.add
          (continuousOn_id.sub continuousOn_const)
      have hnn_ker : ∀ᵐ t ∂μ, 0 ≤ -Real.log t + (t - 1) := by
        filter_upwards [hae_supp] with t ht
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
    have hm_pd : m.mat.PosDef :=
      (hρ.smul (by norm_num : (0 : ℝ) < 1 - 1 / 2)).add_posSemidef
        (σ.posSemidef.smul (by norm_num : (0 : ℝ) ≤ 1 / 2))
    -- `E_s(ρ ‖ m) = ∫ max (t - s * (1+t)/2) 0 ∂μ` for `s > 0`
    have hrep_m1 : ∀ s : ℝ, 0 < s → hockeyStick s ρ m = ∫ t, max (t - s * ((1 + t) / 2)) 0 ∂μ := by
      intro s hs
      rw [hockeyStick_midpoint_left ρ σ hs]
      split_ifs with hs2
      · rw [hrep (s / (2 - s)), ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        rw [mul_max_of_nonneg _ _ (by linarith : 0 ≤ 1 - s / 2), mul_zero]
        congr 1
        have h2s : 2 - s ≠ 0 := by linarith
        have hmul : (1 - s / 2) * (s / (2 - s)) = s / 2 := by
          rw [show (1 - s / 2 : ℝ) = (2 - s) / 2 by ring, div_mul_div_comm,
            mul_comm (2 - s) s, mul_div_mul_right _ _ h2s]
        calc (1 - s / 2) * (t - s / (2 - s))
            = (1 - s / 2) * t - (1 - s / 2) * (s / (2 - s)) := by ring
          _ = (1 - s / 2) * t - s / 2 := by rw [hmul]
          _ = t - s * ((1 + t) / 2) := by ring
      · push Not at hs2
        symm; apply integral_eq_zero_of_ae
        filter_upwards [hae_supp] with t ht
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
              ((hint_of_cont (fun t : ℝ ↦ t) continuousOn_id).const_mul (s / (2 - s))), integral_const, smul_eq_mul,
              hμ_real_univ, one_mul, integral_const_mul, hmean, mul_one]
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
        congr 1
        have h2s : 2 - s ≠ 0 := by linarith
        have hmul : (1 - s / 2) * (s / (2 - s)) = s / 2 := by
          rw [show (1 - s / 2 : ℝ) = (2 - s) / 2 by ring, div_mul_div_comm,
            mul_comm (2 - s) s, mul_div_mul_right _ _ h2s]
        calc (1 - s / 2) * (1 - s / (2 - s) * t)
            = (1 - s / 2) - ((1 - s / 2) * (s / (2 - s))) * t := by ring
          _ = (1 - s / 2) - (s / 2) * t := by rw [hmul]
          _ = 1 - s * ((1 + t) / 2) := by ring
      · push Not at hs2
        symm; apply integral_eq_zero_of_ae
        filter_upwards [hae_supp] with t ht
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
          intro s hs; dsimp only; rw [max_eq_left (by linarith [hs.2])]
        · apply setLIntegral_congr_fun measurableSet_Ioi
          intro s hs; dsimp only; rw [max_eq_right (by linarith [Set.mem_Ioi.mp hs]), sub_zero]
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
              hμ_real_univ, one_mul]
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
        rw [setLIntegral_congr_fun measurableSet_Ioc hleft_int]
        exact tonelli_set_real (ENNReal.measurable_ofReal.comp (by fun_prop))
      have hr_swap : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (hockeyStick s ρ m / s) ∂volume) =
          ∫⁻ t, ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t - s * ((1 + t) / 2)) 0 / s) ∂volume ∂μ := by
        rw [setLIntegral_congr_fun measurableSet_Ioi hright_int]
        exact tonelli_set_real (ENNReal.measurable_ofReal.comp (by fun_prop))
      rw [hl_swap, hr_swap, ← lintegral_add_left] at h38
      · have hker : (∫⁻ t, ((∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * ((1 + t) / 2) - t) 0 / s) ∂volume) +
              (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (t - s * ((1 + t) / 2)) 0 / s) ∂volume)) ∂μ) =
            ∫⁻ t, ENNReal.ofReal (t * Real.log (2 * t / (1 + t)) + (1 - t) / 2) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [hae_supp] with t ht
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
          filter_upwards [hae_supp] with t ht
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
          intro s hs; dsimp only; rw [max_eq_left (by linarith [hs.2])]
        · apply setLIntegral_congr_fun measurableSet_Ioi
          intro s hs; dsimp only; rw [max_eq_right (by linarith [Set.mem_Ioi.mp hs]), sub_zero]
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
              hμ_real_univ, one_mul]
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
        rw [setLIntegral_congr_fun measurableSet_Ioc hleft_int]
        exact tonelli_set_real (ENNReal.measurable_ofReal.comp (by fun_prop))
      have hr_swap : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (hockeyStick s σ m / s) ∂volume) =
          ∫⁻ t, ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (1 - s * ((1 + t) / 2)) 0 / s) ∂volume ∂μ := by
        rw [setLIntegral_congr_fun measurableSet_Ioi hright_int]
        exact tonelli_set_real (ENNReal.measurable_ofReal.comp (by fun_prop))
      rw [hl_swap, hr_swap, ← lintegral_add_left] at h38
      · have hker : (∫⁻ t, ((∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (max (s * ((1 + t) / 2) - 1) 0 / s) ∂volume) +
              (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (max (1 - s * ((1 + t) / 2)) 0 / s) ∂volume)) ∂μ) =
            ∫⁻ t, ENNReal.ofReal (Real.log (2 / (1 + t)) + (t - 1) / 2) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [hae_supp] with t ht
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
          filter_upwards [hae_supp] with t ht
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
    obtain ⟨hqjs_nn, hqjs⟩ := qjs_eq_half_relEntropy_midpoint hρ hσ
    have hfin1 : relEntropy ρ m ≠ ⊤ := by
      intro htop
      have hne : ENNReal.ofReal (qjs ρ σ) ≠ ⊤ := ENNReal.ofReal_ne_top
      rw [hqjs, htop, top_add, ENNReal.top_div_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)] at hne
      exact hne rfl
    have hfin2 : relEntropy σ m ≠ ⊤ := by
      intro htop
      have hne : ENNReal.ofReal (qjs ρ σ) ≠ ⊤ := ENNReal.ofReal_ne_top
      rw [hqjs, htop, add_top, ENNReal.top_div_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)] at hne
      exact hne rfl
    have hqjs_real : qjs ρ σ = ((relEntropy ρ m).toReal + (relEntropy σ m).toReal) / 2 := by
      have hto := congr_arg ENNReal.toReal hqjs
      rw [ENNReal.toReal_ofReal hqjs_nn, ENNReal.toReal_div,
        ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_ofNat] at hto
      exact hto
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

end PolarCodes
