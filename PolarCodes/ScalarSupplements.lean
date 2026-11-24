/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.SplittingBounds

/-!
# Scalar Supplements: Wyner–Ziv Convexity and Endpoint Asymptotics

This module proves two scalar results needed in Section 4:
1. **Wyner–Ziv Convexity (`convexOn_gc`)**: For every fixed `u ∈ [0, 1]`, the map
   `v ↦ gc u v = h₂(h₂⁻¹(u) * h₂⁻¹(v))` is convex on `[0, 1]` (used in Theorem 1.2(a)).
2. **Endpoint Asymptotics (`prop_4_3_asymptotic`)**: Eq. (1.8) of Proposition 4.3,
   `lim_{δ → 0+} Δ(δ, 1 - 2^(-δ)) / δ = 1`.
-/

open Real Set Filter Topology

namespace PolarCodes

/-! ### Continuity and Differentiability of `h2Inv` -/

/-- `h2Inv` is continuous on `[0, 1]`, as the inverse of the strictly increasing continuous
bijection `h2 : [0, 1/2] → [0, 1]`. -/
lemma continuousOn_h2Inv : ContinuousOn h2Inv (Icc (0 : ℝ) 1) := by
  rw [Metric.continuousOn_iff]
  intro v hv ε hε
  set q := h2Inv v
  have hq : q ∈ Icc (0 : ℝ) (1 / 2) := h2Inv_mem_Icc hv
  -- Pick `q_lo < q < q_hi` inside `[0, 1/2]` within `ε/2` of `q`
  have hlt_lo : q = 0 ∨ 0 < q := (eq_or_lt_of_le hq.1).imp Eq.symm id
  have hlt_hi : q = 1 / 2 ∨ q < 1 / 2 := eq_or_lt_of_le hq.2
  -- Left radius `δ_lo`
  obtain ⟨δ_lo, hδ_lo_pos, hδ_lo⟩ : ∃ δ > 0, ∀ w ∈ Icc (0 : ℝ) 1, v - δ < w → q - ε < h2Inv w := by
    rcases hlt_lo with hq0 | hq0
    · refine ⟨1, one_pos, fun w hw _ ↦ ?_⟩
      have := (h2Inv_mem_Icc hw).1
      linarith
    · set q₁ := max 0 (q - ε / 2)
      have hq₁_mem : q₁ ∈ Icc (0 : ℝ) (1 / 2) := ⟨le_max_left _ _, max_le (by norm_num) (by linarith [hq.2])⟩
      have hq₁_lt : q₁ < q := max_lt hq0 (by linarith)
      have hv₁_lt : h2 q₁ < v := by
        rw [← h2_h2Inv hv]
        exact strictMonoOn_h2 hq₁_mem hq hq₁_lt
      refine ⟨v - h2 q₁, by linarith, fun w hw hvw ↦ ?_⟩
      have hlt : h2 q₁ < w := by linarith
      have hinv := strictMonoOn_h2Inv ⟨h2_nonneg ⟨hq₁_mem.1, by linarith [hq₁_mem.2]⟩,
        h2_le_one ⟨hq₁_mem.1, by linarith [hq₁_mem.2]⟩⟩ hw hlt
      rw [h2Inv_h2 hq₁_mem] at hinv
      have : q - ε / 2 ≤ q₁ := le_max_right _ _
      linarith
  -- Right radius `δ_hi`
  obtain ⟨δ_hi, hδ_hi_pos, hδ_hi⟩ : ∃ δ > 0, ∀ w ∈ Icc (0 : ℝ) 1, w < v + δ → h2Inv w < q + ε := by
    rcases hlt_hi with hq1 | hq1
    · refine ⟨1, one_pos, fun w hw _ ↦ ?_⟩
      have := (h2Inv_mem_Icc hw).2
      linarith
    · set q₂ := min (1 / 2) (q + ε / 2)
      have hq₂_mem : q₂ ∈ Icc (0 : ℝ) (1 / 2) := ⟨le_min (by norm_num) (by linarith [hq.1]), min_le_left _ _⟩
      have hq₂_gt : q < q₂ := lt_min hq1 (by linarith)
      have hv₂_gt : v < h2 q₂ := by
        rw [← h2_h2Inv hv]
        exact strictMonoOn_h2 hq hq₂_mem hq₂_gt
      refine ⟨h2 q₂ - v, by linarith, fun w hw hvw ↦ ?_⟩
      have hlt : w < h2 q₂ := by linarith
      have hinv := strictMonoOn_h2Inv hw ⟨h2_nonneg ⟨hq₂_mem.1, by linarith [hq₂_mem.2]⟩,
        h2_le_one ⟨hq₂_mem.1, by linarith [hq₂_mem.2]⟩⟩ hlt
      rw [h2Inv_h2 hq₂_mem] at hinv
      have : q₂ ≤ q + ε / 2 := min_le_right _ _
      linarith
  refine ⟨min δ_lo δ_hi, lt_min hδ_lo_pos hδ_hi_pos, fun w hw hdist ↦ ?_⟩
  rw [Real.dist_eq, abs_lt] at hdist ⊢
  have h1 : v - δ_lo < w := by linarith [min_le_left δ_lo δ_hi]
  have h2 : w < v + δ_hi := by linarith [min_le_right δ_lo δ_hi]
  exact ⟨by linarith [hδ_lo w hw h1], by linarith [hδ_hi w hw h2]⟩

lemma h2Inv_mem_Ioo {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) : h2Inv v ∈ Ioo (0 : ℝ) (1 / 2) := by
  have hmem := h2Inv_mem_Icc ⟨le_of_lt hv.1, le_of_lt hv.2⟩
  constructor
  · rw [← h2Inv_zero]
    exact strictMonoOn_h2Inv ⟨le_rfl, by norm_num⟩ ⟨le_of_lt hv.1, le_of_lt hv.2⟩ hv.1
  · rw [← h2Inv_one]
    exact strictMonoOn_h2Inv ⟨le_of_lt hv.1, le_of_lt hv.2⟩ ⟨by norm_num, le_rfl⟩ hv.2

lemma hasDerivAt_h2Inv {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt h2Inv ((Real.log ((1 - h2Inv v) / h2Inv v) / Real.log 2)⁻¹) v := by
  set q := h2Inv v
  have hq : q ∈ Ioo (0 : ℝ) (1 / 2) := h2Inv_mem_Ioo hv
  have hd_h2 : HasDerivAt h2 (Real.log ((1 - q) / q) / Real.log 2) q :=
    hasDerivAt_h2 hq.1 (by linarith [hq.2])
  have hderiv_pos : 0 < Real.log ((1 - q) / q) / Real.log 2 := by
    apply div_pos
    · exact Real.log_pos (by rw [one_lt_div hq.1]; linarith [hq.2])
    · exact Real.log_pos (by norm_num)
  have hcont : ContinuousAt h2Inv v :=
    continuousOn_h2Inv.continuousAt (Icc_mem_nhds hv.1 hv.2)
  have hinv : ∀ᶠ w in 𝓝 v, h2 (h2Inv w) = w := by
    filter_upwards [Icc_mem_nhds hv.1 hv.2] with w hw
    exact h2_h2Inv hw
  have hfv : h2 q = v := h2_h2Inv ⟨le_of_lt hv.1, le_of_lt hv.2⟩
  have hd_h2' : HasDerivAt h2 (Real.log ((1 - q) / q) / Real.log 2) (h2Inv (h2 q)) := by
    rw [h2Inv_h2 ⟨le_of_lt hq.1, le_of_lt hq.2⟩]; exact hd_h2
  rw [← hfv] at hcont hinv ⊢
  exact HasDerivAt.of_local_left_inverse hcont hd_h2' (ne_of_gt hderiv_pos) hinv

/-! ### Wyner–Ziv Convexity of `v ↦ gc u v` on `[0, 1]` -/

private lemma two_mul_le_log_one_add_div_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    2 * t ≤ Real.log ((1 + t) / (1 - t)) := by
  let g : ℝ → ℝ := fun s ↦ Real.log ((1 + s) / (1 - s)) - 2 * s
  have hg0 : g 0 = 0 := by simp [g]
  have hmono : MonotoneOn g (Ico 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · apply ContinuousOn.sub
      · apply ContinuousOn.log
        · exact (continuousOn_const.add continuousOn_id).div
            (continuousOn_const.sub continuousOn_id) (fun s hs ↦ by linarith [hs.2])
        · intro s hs
          exact ne_of_gt (div_pos (by linarith [hs.1]) (by linarith [hs.2]))
      · exact continuousOn_const.mul continuousOn_id
    · intro s hs
      rw [interior_Ico] at hs
      have h1 : HasDerivAt (fun r : ℝ ↦ (1 + r) / (1 - r)) (2 / (1 - s) ^ 2) s := by
        have ha : HasDerivAt (fun r : ℝ ↦ 1 + r) 1 s := (hasDerivAt_id s).const_add 1
        have hb : HasDerivAt (fun r : ℝ ↦ 1 - r) (-1) s := (hasDerivAt_id s).const_sub 1
        convert ha.fun_div hb (by linarith [hs.2]) using 1; ring
      have h2 : HasDerivAt (fun r : ℝ ↦ Real.log ((1 + r) / (1 - r)))
          ((2 / (1 - s) ^ 2) / ((1 + s) / (1 - s))) s :=
        h1.log (ne_of_gt (div_pos (by linarith [hs.1]) (by linarith [hs.2])))
      have h3 : HasDerivAt (fun r : ℝ ↦ 2 * r) 2 s := by
        simpa using (hasDerivAt_id s).const_mul 2
      exact (h2.fun_sub h3).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      have h1 : HasDerivAt (fun r : ℝ ↦ (1 + r) / (1 - r)) (2 / (1 - s) ^ 2) s := by
        have ha : HasDerivAt (fun r : ℝ ↦ 1 + r) 1 s := (hasDerivAt_id s).const_add 1
        have hb : HasDerivAt (fun r : ℝ ↦ 1 - r) (-1) s := (hasDerivAt_id s).const_sub 1
        convert ha.fun_div hb (by linarith [hs.2]) using 1; ring
      have h2 : HasDerivAt (fun r : ℝ ↦ Real.log ((1 + r) / (1 - r)))
          (2 / (1 - s ^ 2)) s := by
        have h := h1.log (ne_of_gt (div_pos (by linarith [hs.1]) (by linarith [hs.2])))
        convert h using 1
        have hne1 : 1 - s ≠ 0 := by linarith [hs.2]
        have hne2 : 1 + s ≠ 0 := by linarith [hs.1]
        have hne3 : 1 - s ^ 2 ≠ 0 := by nlinarith [hs.1, hs.2]
        field_simp [hne1, hne2, hne3]; ring
      have h3 : HasDerivAt (fun r : ℝ ↦ 2 * r) 2 s := by
        simpa using (hasDerivAt_id s).const_mul 2
      rw [(h2.fun_sub h3).deriv]
      have hden : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
      rw [sub_nonneg, le_div_iff₀ hden]
      nlinarith [sq_nonneg s]
  have hgt := hmono ⟨le_rfl, zero_lt_one⟩ ⟨ht0, ht1⟩ ht0
  simp only [g] at hgt hg0
  linarith

private lemma antitoneOn_wyner_ziv_aux :
    AntitoneOn (fun t : ℝ ↦ ((1 - t ^ 2) / t) * Real.log ((1 + t) / (1 - t))) (Ioo 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
  · apply ContinuousOn.mul
    · exact (continuousOn_const.sub (continuousOn_id.pow 2)).div continuousOn_id
        (fun t ht ↦ ne_of_gt ht.1)
    · apply ContinuousOn.log
      · exact (continuousOn_const.add continuousOn_id).div
          (continuousOn_const.sub continuousOn_id) (fun t ht ↦ by linarith [ht.2])
      · intro t ht; exact ne_of_gt (div_pos (by linarith [ht.1]) (by linarith [ht.2]))
  · intro t ht
    rw [interior_Ioo] at ht
    have h1 : HasDerivAt (fun s : ℝ ↦ (1 - s ^ 2) / s) (-(1 + t ^ 2) / t ^ 2) t := by
      have ha : HasDerivAt (fun s : ℝ ↦ 1 - s ^ 2) (-(2 * t)) t := by
        convert (hasDerivAt_pow 2 t).const_sub 1 using 1; ring
      convert ha.fun_div (hasDerivAt_id' t) (ne_of_gt ht.1) using 1
      field_simp [ne_of_gt ht.1]; ring
    have h2 : HasDerivAt (fun s : ℝ ↦ Real.log ((1 + s) / (1 - s))) (2 / (1 - t ^ 2)) t := by
      have hq : HasDerivAt (fun s : ℝ ↦ (1 + s) / (1 - s)) (2 / (1 - t) ^ 2) t := by
        have ha : HasDerivAt (fun r : ℝ ↦ 1 + r) 1 t := (hasDerivAt_id t).const_add 1
        have hb : HasDerivAt (fun r : ℝ ↦ 1 - r) (-1) t := (hasDerivAt_id t).const_sub 1
        convert ha.fun_div hb (by linarith [ht.2]) using 1; ring
      have h := hq.log (ne_of_gt (div_pos (by linarith [ht.1]) (by linarith [ht.2])))
      convert h using 1
      have hne1 : 1 - t ≠ 0 := by linarith [ht.2]
      have hne2 : 1 + t ≠ 0 := by linarith [ht.1]
      have hne3 : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
      field_simp [hne1, hne2, hne3]; ring
    exact (h1.fun_mul h2).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    have h1 : HasDerivAt (fun s : ℝ ↦ (1 - s ^ 2) / s) (-(1 + t ^ 2) / t ^ 2) t := by
      have ha : HasDerivAt (fun s : ℝ ↦ 1 - s ^ 2) (-(2 * t)) t := by
        convert (hasDerivAt_pow 2 t).const_sub 1 using 1; ring
      convert ha.fun_div (hasDerivAt_id' t) (ne_of_gt ht.1) using 1
      field_simp [ne_of_gt ht.1]; ring
    have h2 : HasDerivAt (fun s : ℝ ↦ Real.log ((1 + s) / (1 - s))) (2 / (1 - t ^ 2)) t := by
      have hq : HasDerivAt (fun s : ℝ ↦ (1 + s) / (1 - s)) (2 / (1 - t) ^ 2) t := by
        have ha : HasDerivAt (fun r : ℝ ↦ 1 + r) 1 t := (hasDerivAt_id t).const_add 1
        have hb : HasDerivAt (fun r : ℝ ↦ 1 - r) (-1) t := (hasDerivAt_id t).const_sub 1
        convert ha.fun_div hb (by linarith [ht.2]) using 1; ring
      have h := hq.log (ne_of_gt (div_pos (by linarith [ht.1]) (by linarith [ht.2])))
      convert h using 1
      have hne1 : 1 - t ≠ 0 := by linarith [ht.2]
      have hne2 : 1 + t ≠ 0 := by linarith [ht.1]
      have hne3 : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
      field_simp [hne1, hne2, hne3]; ring
    rw [(h1.fun_mul h2).deriv]
    have hne : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
    have hsimp : -(1 + t ^ 2) / t ^ 2 * Real.log ((1 + t) / (1 - t)) +
        (1 - t ^ 2) / t * (2 / (1 - t ^ 2)) =
        (2 * t - (1 + t ^ 2) * Real.log ((1 + t) / (1 - t))) / t ^ 2 := by
      field_simp [ne_of_gt ht.1, hne]; ring
    rw [hsimp]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg t)
    have hlog := two_mul_le_log_one_add_div_one_sub (le_of_lt ht.1) ht.2
    nlinarith [sq_nonneg t, ht.1]

/-- **Wyner–Ziv Convexity (1973)**: For every fixed `u ∈ [0, 1]`, the map `v ↦ gc u v` is
convex on `[0, 1]`. -/
theorem convexOn_gc {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun v ↦ gc u v) := by
  rcases eq_or_lt_of_le hu.1 with rfl | hu0
  · -- `u = 0`: `gc 0 v = v` on `[0, 1]`
    have heq : EqOn (fun v ↦ gc 0 v) id (Icc (0 : ℝ) 1) := by
      intro v hv
      simp only [gc, h2Inv_zero, binConv_zero_left, h2_h2Inv hv, id_eq]
    exact (convexOn_id (convex_Icc (0 : ℝ) 1)).congr heq.symm
  · rcases eq_or_lt_of_le hu.2 with rfl | hu1
    · -- `u = 1`: `gc 1 v = 1`
      have heq : EqOn (fun v ↦ gc 1 v) (fun _ ↦ 1) (Icc (0 : ℝ) 1) := by
        intro v _
        simp only [gc, h2Inv_one, binConv_half_left, h2_half]
      exact (convexOn_const 1 (convex_Icc (0 : ℝ) 1)).congr heq.symm
    · -- `u ∈ (0, 1)`: `p = h2Inv u ∈ (0, 1/2)`, `α = 1 - 2p ∈ (0, 1)`
      set p := h2Inv u
      have hp : p ∈ Ioo (0 : ℝ) (1 / 2) := h2Inv_mem_Ioo ⟨hu0, hu1⟩
      set α := 1 - 2 * p
      have hα0 : 0 < α := by simp only [α]; linarith [hp.2]
      have hα1 : α < 1 := by simp only [α]; linarith [hp.1]
      -- Compute derivative of `gc u` on `(0, 1)`
      have hderiv : ∀ v ∈ Ioo (0 : ℝ) 1,
          HasDerivAt (fun w ↦ gc u w)
            (α * Real.log ((1 - binConv p (h2Inv v)) / binConv p (h2Inv v)) /
              Real.log ((1 - h2Inv v) / h2Inv v)) v := by
        intro v hv
        set q := h2Inv v
        have hq : q ∈ Ioo (0 : ℝ) (1 / 2) := h2Inv_mem_Ioo hv
        set r := binConv p q
        have hr_mem : r ∈ Ioo (0 : ℝ) (1 / 2) := by
          simp only [r, binConv]
          constructor <;> nlinarith [hp.1, hp.2, hq.1, hq.2]
        have hd1 : HasDerivAt h2Inv ((Real.log ((1 - q) / q) / Real.log 2)⁻¹) v :=
          hasDerivAt_h2Inv hv
        have hd2 : HasDerivAt (fun s : ℝ ↦ binConv p s) α q := by
          have hfun : (fun s : ℝ ↦ binConv p s) = fun s ↦ p + (1 - 2 * p) * s := by
            ext s; unfold binConv; ring
          rw [hfun]
          simpa [α] using ((hasDerivAt_id' q).const_mul (1 - 2 * p)).const_add p
        have hd3 : HasDerivAt h2 (Real.log ((1 - r) / r) / Real.log 2) r :=
          hasDerivAt_h2 hr_mem.1 (by linarith [hr_mem.2])
        have hcomp := (hd3.comp q hd2).comp v hd1
        have hfun : (fun w ↦ gc u w) = (h2 ∘ fun s ↦ binConv p s) ∘ h2Inv := rfl
        rw [hfun]
        convert hcomp using 1
        have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
        have hlogq : Real.log ((1 - q) / q) ≠ 0 :=
          ne_of_gt (Real.log_pos (by rw [one_lt_div hq.1]; linarith [hq.2]))
        rw [inv_div]
        simp only [q, r]
        field_simp [hlog2, hlogq]
      -- Show `x ↦ log((1 + α x)/(1 - α x)) / log((1 + x)/(1 - x))` is antitone on `(0, 1)`
      have hanti_ratio : AntitoneOn
          (fun x : ℝ ↦ Real.log ((1 + α * x) / (1 - α * x)) / Real.log ((1 + x) / (1 - x)))
          (Ioo 0 1) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
        · apply ContinuousOn.div
          · apply ContinuousOn.log
            · exact (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).div
                (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
                (fun x hx ↦ by nlinarith [hx.1, hx.2])
            · intro x hx; exact ne_of_gt (div_pos (by nlinarith [hx.1]) (by nlinarith [hx.2]))
          · apply ContinuousOn.log
            · exact (continuousOn_const.add continuousOn_id).div
                (continuousOn_const.sub continuousOn_id) (fun x hx ↦ by linarith [hx.2])
            · intro x hx; exact ne_of_gt (div_pos (by linarith [hx.1]) (by linarith [hx.2]))
          · intro x hx
            exact ne_of_gt (Real.log_pos (by rw [one_lt_div (by linarith [hx.2])]; linarith [hx.1]))
        · intro x hx
          rw [interior_Ioo] at hx
          have hnum : HasDerivAt (fun s : ℝ ↦ Real.log ((1 + α * s) / (1 - α * s)))
              (2 * α / (1 - (α * x) ^ 2)) x := by
            have hq : HasDerivAt (fun s : ℝ ↦ (1 + α * s) / (1 - α * s))
                (2 * α / (1 - α * x) ^ 2) x := by
              have ha : HasDerivAt (fun r : ℝ ↦ 1 + α * r) α x := by
                simpa using ((hasDerivAt_id x).const_mul α).const_add 1
              have hb : HasDerivAt (fun r : ℝ ↦ 1 - α * r) (-α) x := by
                simpa using ((hasDerivAt_id x).const_mul α).const_sub 1
              convert ha.fun_div hb (by nlinarith [hx.2]) using 1; ring
            have h := hq.log (ne_of_gt (div_pos (by nlinarith [hx.1]) (by nlinarith [hx.2])))
            convert h using 1
            have hax_lt : α * x < 1 := by nlinarith [hα1, hx.2]
            have hax_pos : 0 < α * x := mul_pos hα0 hx.1
            have hne1 : 1 - α * x ≠ 0 := by linarith
            have hne2 : 1 + α * x ≠ 0 := by linarith
            have hne3 : 1 - (α * x) ^ 2 ≠ 0 := by nlinarith
            have hfac : 1 - (α * x) ^ 2 = (1 - α * x) * (1 + α * x) := by ring
            rw [hfac]
            field_simp [hne1, hne2]
          have hden : HasDerivAt (fun s : ℝ ↦ Real.log ((1 + s) / (1 - s)))
              (2 / (1 - x ^ 2)) x := by
            have hq : HasDerivAt (fun s : ℝ ↦ (1 + s) / (1 - s)) (2 / (1 - x) ^ 2) x := by
              have ha : HasDerivAt (fun r : ℝ ↦ 1 + r) 1 x := (hasDerivAt_id x).const_add 1
              have hb : HasDerivAt (fun r : ℝ ↦ 1 - r) (-1) x := (hasDerivAt_id x).const_sub 1
              convert ha.fun_div hb (by linarith [hx.2]) using 1; ring
            have h := hq.log (ne_of_gt (div_pos (by linarith [hx.1]) (by linarith [hx.2])))
            convert h using 1
            have hne1 : 1 - x ≠ 0 := by linarith [hx.2]
            have hne2 : 1 + x ≠ 0 := by linarith [hx.1]
            have hne3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
            field_simp [hne1, hne2, hne3]; ring
          have hlogx : Real.log ((1 + x) / (1 - x)) ≠ 0 :=
            ne_of_gt (Real.log_pos (by rw [one_lt_div (by linarith [hx.2])]; linarith [hx.1]))
          exact (hnum.fun_div hden hlogx).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Ioo] at hx
          have hnum : HasDerivAt (fun s : ℝ ↦ Real.log ((1 + α * s) / (1 - α * s)))
              (2 * α / (1 - (α * x) ^ 2)) x := by
            have hq : HasDerivAt (fun s : ℝ ↦ (1 + α * s) / (1 - α * s))
                (2 * α / (1 - α * x) ^ 2) x := by
              have ha : HasDerivAt (fun r : ℝ ↦ 1 + α * r) α x := by
                simpa using ((hasDerivAt_id x).const_mul α).const_add 1
              have hb : HasDerivAt (fun r : ℝ ↦ 1 - α * r) (-α) x := by
                simpa using ((hasDerivAt_id x).const_mul α).const_sub 1
              convert ha.fun_div hb (by nlinarith [hx.2]) using 1; ring
            have h := hq.log (ne_of_gt (div_pos (by nlinarith [hx.1]) (by nlinarith [hx.2])))
            convert h using 1
            have hax_lt : α * x < 1 := by nlinarith [hα1, hx.2]
            have hax_pos : 0 < α * x := mul_pos hα0 hx.1
            have hne1 : 1 - α * x ≠ 0 := by linarith
            have hne2 : 1 + α * x ≠ 0 := by linarith
            have hne3 : 1 - (α * x) ^ 2 ≠ 0 := by nlinarith
            have hfac : 1 - (α * x) ^ 2 = (1 - α * x) * (1 + α * x) := by ring
            rw [hfac]
            field_simp [hne1, hne2]
          have hden : HasDerivAt (fun s : ℝ ↦ Real.log ((1 + s) / (1 - s)))
              (2 / (1 - x ^ 2)) x := by
            have hq : HasDerivAt (fun s : ℝ ↦ (1 + s) / (1 - s)) (2 / (1 - x) ^ 2) x := by
              have ha : HasDerivAt (fun r : ℝ ↦ 1 + r) 1 x := (hasDerivAt_id x).const_add 1
              have hb : HasDerivAt (fun r : ℝ ↦ 1 - r) (-1) x := (hasDerivAt_id x).const_sub 1
              convert ha.fun_div hb (by linarith [hx.2]) using 1; ring
            have h := hq.log (ne_of_gt (div_pos (by linarith [hx.1]) (by linarith [hx.2])))
            convert h using 1
            have hne1 : 1 - x ≠ 0 := by linarith [hx.2]
            have hne2 : 1 + x ≠ 0 := by linarith [hx.1]
            have hne3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
            field_simp [hne1, hne2, hne3]; ring
          have hlogx : Real.log ((1 + x) / (1 - x)) ≠ 0 :=
            ne_of_gt (Real.log_pos (by rw [one_lt_div (by linarith [hx.2])]; linarith [hx.1]))
          rw [(hnum.fun_div hden hlogx).deriv]
          apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
          have hax : α * x ∈ Ioo (0 : ℝ) 1 := ⟨mul_pos hα0 hx.1, by nlinarith [hx.1, hx.2]⟩
          have hle := antitoneOn_wyner_ziv_aux hax hx (by nlinarith [hx.1])
          have h1 : 0 < 1 - (α * x) ^ 2 := by nlinarith [hax.1, hax.2]
          have h2 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
          have h3 : 0 < α * x := hax.1
          -- From `((1 - x^2) / x) * log((1+x)/(1-x)) ≤ ((1 - (αx)^2) / (αx)) * log((1+αx)/(1-αx))`,
          -- multiply by `2 α x / ((1 - (αx)^2)(1 - x^2)) > 0`!
          have hmul := mul_le_mul_of_nonneg_left hle
            (show 0 ≤ 2 * (α * x) / ((1 - (α * x) ^ 2) * (1 - x ^ 2)) by positivity)
          have hL : 2 * (α * x) / ((1 - (α * x) ^ 2) * (1 - x ^ 2)) *
              ((1 - x ^ 2) / x * Real.log ((1 + x) / (1 - x))) =
              2 * α / (1 - (α * x) ^ 2) * Real.log ((1 + x) / (1 - x)) := by
            field_simp [ne_of_gt hx.1, ne_of_gt h1, ne_of_gt h2]
          have hR : 2 * (α * x) / ((1 - (α * x) ^ 2) * (1 - x ^ 2)) *
              ((1 - (α * x) ^ 2) / (α * x) * Real.log ((1 + α * x) / (1 - α * x))) =
              Real.log ((1 + α * x) / (1 - α * x)) * (2 / (1 - x ^ 2)) := by
            have hne_a : 1 - (α * x) ^ 2 ≠ 0 := ne_of_gt h1
            have hne_x : 1 - x ^ 2 ≠ 0 := ne_of_gt h2
            have hne_α : α ≠ 0 := ne_of_gt hα0
            have hne_x0 : x ≠ 0 := ne_of_gt hx.1
            have hne_ax : 1 - α ^ 2 * x ^ 2 ≠ 0 := by convert hne_a using 1; ring
            field_simp [hne_a, hne_ax, hne_x, hne_α, hne_x0]
          linarith
      -- Apply `convexOn_of_deriv_mono` on `Icc 0 1`
      let f' : ℝ → ℝ := fun v ↦
        α * Real.log ((1 - binConv p (h2Inv v)) / binConv p (h2Inv v)) /
          Real.log ((1 - h2Inv v) / h2Inv v)
      have hf'_mono : MonotoneOn f' (Ioo (0 : ℝ) 1) := by
        intro v₁ hv₁ v₂ hv₂ hv12
        simp only [f']
        set q₁ := h2Inv v₁
        set q₂ := h2Inv v₂
        have hq₁ : q₁ ∈ Ioo (0 : ℝ) (1 / 2) := h2Inv_mem_Ioo hv₁
        have hq₂ : q₂ ∈ Ioo (0 : ℝ) (1 / 2) := h2Inv_mem_Ioo hv₂
        have hq12 : q₁ ≤ q₂ := strictMonoOn_h2Inv.monotoneOn
          ⟨le_of_lt hv₁.1, le_of_lt hv₁.2⟩ ⟨le_of_lt hv₂.1, le_of_lt hv₂.2⟩ hv12
        set x₁ := 1 - 2 * q₁
        set x₂ := 1 - 2 * q₂
        have hx₁ : x₁ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hq₁.2], by linarith [hq₁.1]⟩
        have hx₂ : x₂ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hq₂.2], by linarith [hq₂.1]⟩
        have hx21 : x₂ ≤ x₁ := by linarith
        have hrew : ∀ (q : ℝ), q ∈ Ioo (0 : ℝ) (1 / 2) →
            α * Real.log ((1 - binConv p q) / binConv p q) / Real.log ((1 - q) / q) =
              α * (Real.log ((1 + α * (1 - 2 * q)) / (1 - α * (1 - 2 * q))) /
                Real.log ((1 + (1 - 2 * q)) / (1 - (1 - 2 * q)))) := by
          intro q hq
          rw [mul_div_assoc]
          congr 2
          · congr 1
            have hbc : 1 - 2 * binConv p q = α * (1 - 2 * q) := by unfold binConv; simp only [α]; ring
            have hne1 : binConv p q ≠ 0 := by unfold binConv; nlinarith [hp.1, hp.2, hq.1, hq.2]
            have hne2 : 1 - α * (1 - 2 * q) ≠ 0 := by nlinarith [hα0, hα1, hq.1, hq.2]
            field_simp [hne1, hne2]; linarith
          · congr 1
            have hne1 : q ≠ 0 := ne_of_gt hq.1
            have hne2 : 1 - (1 - 2 * q) ≠ 0 := by linarith [hq.1]
            field_simp [hne1, hne2]; ring
        rw [hrew q₁ hq₁, hrew q₂ hq₂]
        exact mul_le_mul_of_nonneg_left (hanti_ratio hx₂ hx₁ hx21) (le_of_lt hα0)
      have hcont_gc : ContinuousOn (fun w ↦ gc u w) (Icc (0 : ℝ) 1) := by
        have hcont_bc : Continuous (fun q : ℝ ↦ binConv p q) := by unfold binConv; fun_prop
        exact continuous_h2.comp_continuousOn (hcont_bc.comp_continuousOn continuousOn_h2Inv)
      refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
      intro x hx y hy a b ha hb hab
      simp only [smul_eq_mul]
      rcases eq_or_lt_of_le ha with rfl | ha_pos
      · have hb1 : b = 1 := by linarith
        subst hb1; simp
      rcases eq_or_lt_of_le hb with rfl | hb_pos
      · have ha1 : a = 1 := by linarith
        subst ha1; simp
      suffices hsym : ∀ x' y' a' b' : ℝ, x' ∈ Icc (0 : ℝ) 1 → y' ∈ Icc (0 : ℝ) 1 →
          x' < y' → 0 < a' → 0 < b' → a' + b' = 1 →
          gc u (a' * x' + b' * y') ≤ a' * gc u x' + b' * gc u y' by
        rcases lt_trichotomy x y with hlt | rfl | hgt
        · exact hsym x y a b hx hy hlt ha_pos hb_pos hab
        · have : a * x + b * x = x := by linear_combination hab * x
          rw [this]; linear_combination -hab * gc u x
        · have h := hsym y x b a hy hx hgt hb_pos ha_pos (by linarith)
          rw [add_comm (b * y)] at h
          linarith
      intro x' y' a' b' hx' hy' hxy ha' hb' hab'
      set z := a' * x' + b' * y'
      have hpos_d : 0 < y' - x' := by linarith
      have hzx : z - x' = b' * (y' - x') := by
        simp only [z]; rw [show a' = 1 - b' by linarith]; ring
      have hyz : y' - z = a' * (y' - x') := by
        simp only [z]; rw [show b' = 1 - a' by linarith]; ring
      have hxz : x' < z := by linarith [mul_pos hb' hpos_d]
      have hzy : z < y' := by linarith [mul_pos ha' hpos_d]
      have ⟨c₁, hc₁, hceq₁⟩ := exists_hasDerivAt_eq_slope (fun w ↦ gc u w) f' hxz
        (hcont_gc.mono (Icc_subset_Icc hx'.1 (le_trans (le_of_lt hzy) hy'.2)))
        (fun w hw ↦ hderiv w ⟨lt_of_le_of_lt hx'.1 hw.1, lt_of_lt_of_le hw.2 (le_trans (le_of_lt hzy) hy'.2)⟩)
      have ⟨c₂, hc₂, hceq₂⟩ := exists_hasDerivAt_eq_slope (fun w ↦ gc u w) f' hzy
        (hcont_gc.mono (Icc_subset_Icc (le_trans hx'.1 (le_of_lt hxz)) hy'.2))
        (fun w hw ↦ hderiv w ⟨lt_of_le_of_lt (le_trans hx'.1 (le_of_lt hxz)) hw.1, lt_of_lt_of_le hw.2 hy'.2⟩)
      have hc₁_mem : c₁ ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hx'.1 hc₁.1, lt_of_lt_of_le (lt_trans hc₁.2 hzy) hy'.2⟩
      have hc₂_mem : c₂ ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt (le_trans hx'.1 (le_of_lt hxz)) hc₂.1, lt_of_lt_of_le hc₂.2 hy'.2⟩
      have hslope_le : (gc u z - gc u x') / (z - x') ≤ (gc u y' - gc u z) / (y' - z) := by
        rw [← hceq₁, ← hceq₂]
        exact hf'_mono hc₁_mem hc₂_mem (le_of_lt (lt_trans hc₁.2 hc₂.1))
      rw [hzx, hyz, div_le_div_iff₀ (mul_pos hb' hpos_d) (mul_pos ha' hpos_d)] at hslope_le
      have hcancel : (gc u z - gc u x') * a' ≤ (gc u y' - gc u z) * b' := by
        apply le_of_mul_le_mul_right _ hpos_d
        linarith only [hslope_le]
      have hcombine : (a' + b') * gc u z ≤ a' * gc u x' + b' * gc u y' := by linarith only [hcancel]
      rw [hab', one_mul] at hcombine
      exact hcombine

/-! ### Proposition 4.3 Endpoint Asymptotics (Eq. 1.8) -/

/-- For `δ ∈ (0, 1/4]`, `h2Inv δ * logb 2 (1 / δ) ≤ δ`. -/
lemma h2Inv_mul_logb_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    h2Inv δ * Real.logb 2 (1 / δ) ≤ δ := by
  set p1 := h2Inv δ
  have hp1_pos : 0 < p1 := (h2Inv_mem_Ioo ⟨hδ0, by linarith⟩).1
  have hp1_lt_half : p1 < 1 / 2 := (h2Inv_mem_Ioo ⟨hδ0, by linarith⟩).2
  have hp1_le_δ : p1 ≤ δ := by
    have h1 : δ ≤ h2 (δ / 2) := by
      have hconc := strictConcaveOn_h2.concaveOn.2
        (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, by norm_num⟩)
        (show (1 / 8 : ℝ) ∈ Icc 0 1 from ⟨by norm_num, by norm_num⟩)
        (show 0 ≤ 1 - 4 * δ by linarith) (show 0 ≤ 4 * δ by linarith) (by ring)
      simp only [smul_eq_mul, h2_zero, mul_zero, zero_add] at hconc
      have harg : 4 * δ * (1 / 8 : ℝ) = δ / 2 := by ring
      rw [harg] at hconc
      have h8 := h2_one_eighth_gt_quarter
      nlinarith
    have h2 : h2 p1 ≤ h2 (δ / 2) := by rw [h2_h2Inv ⟨le_of_lt hδ0, by linarith⟩]; exact h1
    have h3 : p1 ≤ δ / 2 := by
      by_contra hgt
      have := strictMonoOn_h2 ⟨by linarith, by linarith⟩ ⟨le_of_lt hp1_pos, le_of_lt hp1_lt_half⟩
        (lt_of_not_ge hgt)
      linarith
    linarith
  have hlog_le : Real.logb 2 (1 / δ) ≤ Real.logb 2 (1 / p1) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity)
      (one_div_le_one_div_of_le hp1_pos hp1_le_δ)
  have hh2_ge : p1 * Real.logb 2 (1 / p1) ≤ h2 p1 := by
    rw [h2_eq_negMulLog, Real.logb, one_div, Real.log_inv]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hlog2]
    unfold Real.negMulLog
    have h1mp : 0 ≤ -(1 - p1) * Real.log (1 - p1) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (Real.log_nonpos (by linarith) (by linarith))
    linarith
  rw [h2_h2Inv ⟨le_of_lt hδ0, by linarith⟩] at hh2_ge
  calc p1 * Real.logb 2 (1 / δ)
      ≤ p1 * Real.logb 2 (1 / p1) := mul_le_mul_of_nonneg_left hlog_le (le_of_lt hp1_pos)
    _ ≤ δ := hh2_ge

set_option maxHeartbeats 800000 in
/-- **Proposition 4.3 (Endpoint Asymptotic, Eq. 1.8)**:
`lim_{δ → 0+} Δ(δ, 1 - 2^(-δ)) / δ = 1`. -/
theorem prop_4_3_asymptotic :
    Tendsto (fun δ : ℝ ↦ deltaGap δ (1 - (2 : ℝ) ^ (-δ)) / δ) (𝓝[>] 0) (𝓝 1) := by
  -- Use ε-δ directly on `(0, 1/4]` via concavity of `h2`
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- Work with `η = min (ε / 4) (1 / 4) ∈ (0, 1/4]`
  set η : ℝ := min (ε / 4) (1 / 4)
  have hη_pos : 0 < η := lt_min (by linarith) (by norm_num)
  have hη_le : η ≤ 1 / 4 := min_le_right _ _
  have hη_le_ε : η ≤ ε / 4 := min_le_left _ _
  -- Choose `L₀ > 0` large enough that `(1 + logb 2 (e / (1 - η)) + logb 2 L) / L ≤ η`
  -- and `(logb 2 4) / L ≤ η` for all `L ≥ L₀`
  have hL_tendsto : Tendsto (fun L : ℝ ↦ Real.logb 2 L / L) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simp only [pow_one, one_mul, add_zero] at h
    have hdiv : Tendsto (fun L : ℝ ↦ (Real.log L / L) / Real.log 2) atTop (𝓝 (0 / Real.log 2)) :=
      h.div_const (Real.log 2)
    rw [zero_div] at hdiv
    refine hdiv.congr (fun L ↦ ?_)
    rw [Real.logb, div_right_comm]
  rw [Metric.tendsto_atTop] at hL_tendsto
  obtain ⟨L₁, hL₁⟩ := hL_tendsto (η / 2) (by linarith)
  set C : ℝ := Real.logb 2 (Real.exp 1 / (1 - η)) + 4
  set L₀ : ℝ := max (max L₁ 16) (max (2 * |C| / η + 1) (2 / η + 1))
  have hL₀_ge16 : 16 ≤ L₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hL₀_pos : 0 < L₀ := by linarith
  -- Take `δ₀ = min (1 / 4) (min (η / 4) (2 ^ (-L₀)))`
  set δ₀ : ℝ := min (1 / 4) (min (η / 4) ((2 : ℝ) ^ (-L₀)))
  have hδ₀_pos : 0 < δ₀ := lt_min (by norm_num) (lt_min (by linarith) (Real.rpow_pos_of_pos (by norm_num) _))
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_dist ↦ ?_⟩
  rw [Set.mem_Ioi] at hδ_pos
  rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos] at hδ_dist
  have hδ_le_q : δ ≤ 1 / 4 := le_trans (le_of_lt hδ_dist) (min_le_left _ _)
  have hδ_le_η : δ ≤ η / 4 := le_trans (le_of_lt hδ_dist) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ_le_pow : δ ≤ (2 : ℝ) ^ (-L₀) :=
    le_trans (le_of_lt hδ_dist) (le_trans (min_le_right _ _) (min_le_right _ _))
  set L : ℝ := Real.logb 2 (1 / δ)
  have hL_ge_L₀ : L₀ ≤ L := by
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hδ_pos hδ_le_pow
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at hlog
    have hinv : L = -Real.logb 2 δ := by simp only [L, one_div, Real.logb_inv]
    linarith
  have hL_ge16 : 16 ≤ L := le_trans hL₀_ge16 hL_ge_L₀
  have hL_pos : 0 < L := by linarith
  have hL_ge_L₁ : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL_ge_L₀
  have hlogL_div : Real.logb 2 L / L < η / 2 := by
    have h := hL₁ L hL_ge_L₁
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  set p1 := h2Inv δ
  set p2 := 1 - (2 : ℝ) ^ (-δ)
  set q := binConv p1 p2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlog2_gt_half : (1 / 2 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  -- Bounds on `p2 = 1 - exp(-(ln 2) δ)`
  have hp2_ub : p2 ≤ Real.log 2 * δ := by
    have h := Real.add_one_le_exp (-(Real.log 2 * δ))
    have hpow : (2 : ℝ) ^ (-δ) = Real.exp (-(Real.log 2 * δ)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]; congr 1; ring
    simp only [p2]; rw [hpow]; linarith
  have hp2_lb : (1 / 4 : ℝ) * δ ≤ p2 := by
    have h := Real.add_one_le_exp (Real.log 2 * δ)
    have hpow : (2 : ℝ) ^ (-δ) = (Real.exp (Real.log 2 * δ))⁻¹ := by
      rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_neg]; congr 1; ring
    have h1 : (Real.exp (Real.log 2 * δ))⁻¹ ≤ (1 + Real.log 2 * δ)⁻¹ :=
      inv_anti₀ (by positivity) (by linarith)
    have h2 : (1 / 4 : ℝ) * δ ≤ 1 - (1 + Real.log 2 * δ)⁻¹ := by
      have hpos : 0 < 1 + Real.log 2 * δ := by positivity
      rw [le_sub_iff_add_le, ← le_sub_iff_add_le', inv_le_comm₀ hpos (by nlinarith)]
      rw [inv_le_iff_one_le_mul₀ (by nlinarith)]
      have hhalf_δ : (1 / 2 : ℝ) * δ ≤ Real.log 2 * δ := by nlinarith
      have hlog_δ : Real.log 2 * δ ≤ δ := by nlinarith
      nlinarith
    simp only [p2]; rw [hpow]; linarith
  have hp2_pos : 0 < p2 := by linarith
  have hp2_lt_quarter : p2 < 1 / 4 := by nlinarith
  -- Bounds on `p1`: `(1 - η) δ / L ≤ p1 ≤ δ / L`
  have hp1_ub : p1 ≤ δ / L := (le_div_iff₀ hL_pos).mpr (h2Inv_mul_logb_le hδ_pos hδ_le_q)
  have hp1_lb : (1 - η) * δ / L ≤ p1 := by
    have h1mη : 0 < 1 - η := by linarith
    set t := (1 - η) * δ / L
    have ht_pos : 0 < t := by positivity
    have ht_lt1 : t < 1 / 2 := by
      have : (1 - η) * δ ≤ 1 / 4 := by nlinarith
      rw [div_lt_iff₀ hL_pos]; linarith
    have hh2_t : h2 t ≤ δ := by
      have h1 := h2_le_mul_logb_exp_div ht_pos (by linarith)
      have hdiv : Real.exp 1 / t = (Real.exp 1 / (1 - η)) * (1 / δ) * L := by
        simp only [t]; field_simp [ne_of_gt hL_pos, ne_of_gt hδ_pos, show 1 - η ≠ 0 by linarith]
      rw [hdiv, Real.logb_mul (by positivity) (ne_of_gt hL_pos),
        Real.logb_mul (by positivity) (by positivity)] at h1
      have hC_bound : Real.logb 2 (Real.exp 1 / (1 - η)) / L ≤ η / 2 := by
        have h1' : |C| / L ≤ η / 2 := by
          have hL_ge_C : 2 * |C| / η + 1 ≤ L :=
            le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL_ge_L₀
          rw [div_le_iff₀ hL_pos]
          have : 2 * |C| ≤ η * L := by
            have := mul_le_mul_of_nonneg_left hL_ge_C (le_of_lt hη_pos)
            have hsimp : η * (2 * |C| / η + 1) = 2 * |C| + η := by field_simp [ne_of_gt hη_pos]
            linarith
          linarith
        have hleC : Real.logb 2 (Real.exp 1 / (1 - η)) ≤ |C| := by
          have : Real.logb 2 (Real.exp 1 / (1 - η)) ≤ C := by simp only [C]; linarith
          exact le_trans this (le_abs_self C)
        exact le_trans (div_le_div_of_nonneg_right hleC (le_of_lt hL_pos)) h1'
      have hsum_le : (Real.logb 2 (Real.exp 1 / (1 - η)) + L + Real.logb 2 L) / L ≤ 1 + η := by
        rw [add_div, add_div, div_self (ne_of_gt hL_pos)]
        linarith only [hC_bound, hlogL_div]
      have ht_eq : t * (Real.logb 2 (Real.exp 1 / (1 - η)) + L + Real.logb 2 L) =
          (1 - η) * δ * ((Real.logb 2 (Real.exp 1 / (1 - η)) + L + Real.logb 2 L) / L) := by
        simp only [t]; ring
      rw [ht_eq] at h1
      have hprod : (1 - η) * (1 + η) ≤ 1 := by nlinarith only [hη_pos]
      have hnn : 0 ≤ (1 - η) * δ := by nlinarith only [h1mη, hδ_pos]
      have hstep : (1 - η) * δ * ((Real.logb 2 (Real.exp 1 / (1 - η)) + L + Real.logb 2 L) / L) ≤
          (1 - η) * δ * (1 + η) := mul_le_mul_of_nonneg_left hsum_le hnn
      nlinarith only [h1, hstep, hprod, hδ_pos]
    have hle : h2 t ≤ h2 p1 := by rwa [h2_h2Inv ⟨le_of_lt hδ_pos, by linarith⟩]
    by_contra hgt
    have := strictMonoOn_h2 (h2Inv_mem_Icc ⟨le_of_lt hδ_pos, by linarith⟩)
      ⟨le_of_lt ht_pos, le_of_lt ht_lt1⟩ (lt_of_not_ge hgt)
    linarith
  have hp1_pos : 0 < p1 := (h2Inv_mem_Ioo ⟨hδ_pos, by linarith⟩).1
  have hp1_lt_half : p1 < 1 / 2 := (h2Inv_mem_Ioo ⟨hδ_pos, by linarith⟩).2
  have hq_gt_p2 : p2 < q := by
    simp only [q, binConv]; nlinarith
  have hq_ub : q ≤ 2 * δ := by
    have : p1 ≤ δ := le_trans hp1_ub ((div_le_iff₀ hL_pos).mpr (by nlinarith))
    simp only [q, binConv]; nlinarith
  have hq_lt_half : q < 1 / 2 := by nlinarith
  -- Concavity sandwich: `(q - p2) * h2'(q) ≤ deltaGap δ p2 ≤ (q - p2) * h2'(p2)`
  have hgap_lb : (q - p2) * (Real.logb 2 ((1 - q) / q)) ≤ deltaGap δ p2 := by
    have hsec : (h2 q - h2 p2) / (q - p2) ≥ Real.log ((1 - q) / q) / Real.log 2 := by
      have hderiv_le := exists_hasDerivAt_eq_slope h2
        (fun x ↦ Real.log ((1 - x) / x) / Real.log 2) hq_gt_p2
        continuous_h2.continuousOn
        (fun x hx ↦ by simpa [Real.logb] using hasDerivAt_h2 (by linarith [hx.1]) (by linarith [hx.2]))
      rcases hderiv_le with ⟨c, hc, hceq⟩
      rw [← hceq]
      apply div_le_div_of_nonneg_right _ (le_of_lt hlog2_pos)
      apply Real.log_le_log (div_pos (by linarith) (by linarith))
      rw [div_le_div_iff₀ (by linarith) (by linarith [hc.1])]
      nlinarith [hc.2]
    unfold deltaGap
    rw [Real.logb, mul_comm]
    exact (le_div_iff₀ (by linarith)).mp hsec
  have hgap_ub : deltaGap δ p2 ≤ (q - p2) * (Real.logb 2 ((1 - p2) / p2)) := by
    have hderiv_ge := exists_hasDerivAt_eq_slope h2
      (fun x ↦ Real.log ((1 - x) / x) / Real.log 2) hq_gt_p2
      continuous_h2.continuousOn
      (fun x hx ↦ by simpa [Real.logb] using hasDerivAt_h2 (by linarith [hx.1]) (by linarith [hx.2]))
    rcases hderiv_ge with ⟨c, hc, hceq⟩
    have hsec : (h2 q - h2 p2) / (q - p2) ≤ Real.log ((1 - p2) / p2) / Real.log 2 := by
      rw [← hceq]
      apply div_le_div_of_nonneg_right _ (le_of_lt hlog2_pos)
      apply Real.log_le_log (div_pos (by linarith [hc.2]) (by linarith [hc.1]))
      rw [div_le_div_iff₀ (by linarith [hc.1]) (by linarith)]
      nlinarith [hc.1]
    unfold deltaGap
    rw [Real.logb, mul_comm]
    exact (div_le_iff₀ (by linarith)).mp hsec
  have hq_sub_p2 : q - p2 = p1 * (1 - 2 * p2) := by simp only [q, binConv]; ring
  -- Bound `logb 2 ((1 - q) / q) ≥ L - 2` and `logb 2 ((1 - p2) / p2) ≤ L + 2`
  have hlogq_lb : L - 2 ≤ Real.logb 2 ((1 - q) / q) := by
    have hrat : (1 / 4 : ℝ) * (1 / δ) ≤ (1 - q) / q := by
      rw [le_div_iff₀ (by linarith)]
      have : (1 / 4 : ℝ) * (1 / δ) * q ≤ 1 / 2 := by
        have hq2 : q / δ ≤ 2 := (div_le_iff₀ hδ_pos).mpr hq_ub
        have : (1 / 4 : ℝ) * (1 / δ) * q = (1 / 4) * (q / δ) := by ring
        linarith
      linarith
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hrat
    rw [Real.logb_mul (by norm_num) (by positivity),
      show (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) by norm_num,
      Real.logb_rpow (by norm_num) (by norm_num)] at h
    push_cast at h
    linarith
  have hlogp2_ub : Real.logb 2 ((1 - p2) / p2) ≤ L + 2 := by
    have hrat : (1 - p2) / p2 ≤ 4 * (1 / δ) := by
      rw [div_le_iff₀ hp2_pos]
      have : 4 * (1 / δ) * p2 = 4 * (p2 / δ) := by ring
      have hp2d : (1 / 4 : ℝ) ≤ p2 / δ := (le_div_iff₀ hδ_pos).mpr hp2_lb
      linarith
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (div_pos (by linarith) hp2_pos) hrat
    rw [Real.logb_mul (by norm_num) (by positivity),
      show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num,
      Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
    push_cast at h
    linarith
  -- Combine lower and upper bounds on `deltaGap δ p2 / δ`
  have h2_div_L : 2 / L ≤ η := by
    have hL_ge_2 : 2 / η + 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL_ge_L₀
    rw [div_le_iff₀ hL_pos]
    have := mul_le_mul_of_nonneg_left hL_ge_2 (le_of_lt hη_pos)
    have hsimp : η * (2 / η + 1) = 2 + η := by field_simp [ne_of_gt hη_pos]
    linarith
  have h1m2p2_lb : 1 - η ≤ 1 - 2 * p2 := by nlinarith
  have h1m2p2_ub : 1 - 2 * p2 ≤ 1 := by linarith
  have hlb_final : 1 - 3 * η ≤ deltaGap δ p2 / δ := by
    rw [le_div_iff₀ hδ_pos]
    have h1 : (1 - η) * δ / L * (1 - η) * (L - 2) ≤ (q - p2) * Real.logb 2 ((1 - q) / q) := by
      rw [hq_sub_p2]
      have hA : (1 - η) * δ / L * (1 - η) ≤ p1 * (1 - 2 * p2) :=
        mul_le_mul hp1_lb h1m2p2_lb (by linarith) (le_of_lt hp1_pos)
      exact mul_le_mul hA hlogq_lb (by linarith) (mul_nonneg (le_of_lt hp1_pos) (by linarith))
    have h2 : (1 - η) * δ / L * (1 - η) * (L - 2) =
        (1 - η) * (1 - η) * (1 - 2 / L) * δ := by
      field_simp [ne_of_gt hL_pos]
    have h3 : 1 - 3 * η ≤ (1 - η) * (1 - η) * (1 - 2 / L) := by
      have hsq : 1 - 2 * η ≤ (1 - η) * (1 - η) := by nlinarith
      nlinarith
    nlinarith
  have hub_final : deltaGap δ p2 / δ ≤ 1 + η := by
    rw [div_le_iff₀ hδ_pos]
    have h1 : (q - p2) * Real.logb 2 ((1 - p2) / p2) ≤ (δ / L) * 1 * (L + 2) := by
      rw [hq_sub_p2]
      have hA : p1 * (1 - 2 * p2) ≤ (δ / L) * 1 :=
        mul_le_mul hp1_ub h1m2p2_ub (by linarith) (by positivity)
      exact mul_le_mul hA hlogp2_ub (by
        exact Real.logb_nonneg (by norm_num) (by rw [one_le_div hp2_pos]; linarith))
        (by positivity)
    have h2 : (δ / L) * 1 * (L + 2) = (1 + 2 / L) * δ := by
      field_simp [ne_of_gt hL_pos]
    nlinarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end PolarCodes
