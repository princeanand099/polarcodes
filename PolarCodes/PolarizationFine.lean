/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.Polarization

/-!
# Stage 3 Fine Polarization and Polynomial-Blocklength Scaling (Section 5.2–5.3)

This module proves **Lemma 5.4** (Stage 3 via the golden-ratio supermartingale and Hoeffding's
inequality), the error-exponent bound `2 √(N · 2^(-200 N^0.49047)) ≤ 2^(-N^0.49)` for all
`N = 2^n ≥ 2`, the abstract polynomial-blocklength polarization theorem (**Theorem 1.1** core),
and the simultaneous dual-pair polarization theorem (**Corollary 5.5** core).
-/

open BigOperators Real Finset Set

namespace PolarCodes

/-! ### Lemma 5.4: Stage 3 (Fine Polarization via Golden-Ratio Supermartingale) -/

/-- Golden-ratio exponent `α_φ := log₂ φ`. -/
noncomputable def alphaGold : ℝ := Real.logb 2 phiGold

/-- Stage-3 golden-ratio potential `g_φ(z) := φ^200 · z^(log₂ φ)` (with `g_φ(0) = 0`). -/
noncomputable def phiPot (z : ℝ) : ℝ :=
  if z ≤ 0 then 0 else phiGold ^ 200 * z ^ alphaGold

lemma alphaGold_pos : 0 < alphaGold :=
  Real.logb_pos (by norm_num) phiGold_gt_one

lemma two_rpow_alphaGold : (2 : ℝ) ^ alphaGold = phiGold :=
  Real.rpow_logb (by norm_num) (by norm_num) (by linarith [phiGold_gt_one])

lemma phiPot_nonneg (z : ℝ) : 0 ≤ phiPot z := by
  unfold phiPot
  split_ifs
  · exact le_rfl
  · have hφ : 0 < phiGold := by linarith [phiGold_gt_one]
    have hz : 0 < z := lt_of_not_ge ‹_›
    positivity

lemma phiPot_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : phiPot x ≤ phiPot y := by
  unfold phiPot
  split_ifs with h1 h2 h2
  · exact le_rfl
  · have hφ : 0 < phiGold := by linarith [phiGold_gt_one]
    have hy : 0 < y := lt_of_not_ge h2
    positivity
  · exfalso; linarith
  · have hφ : 0 < phiGold := by linarith [phiGold_gt_one]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hx hxy (le_of_lt alphaGold_pos)) (by positivity)

lemma phiPot_two_rpow_neg (y : ℝ) : phiPot ((2 : ℝ) ^ (-y)) = phiGold ^ (200 - y) := by
  have hpos : 0 < (2 : ℝ) ^ (-y) := Real.rpow_pos_of_pos (by norm_num) _
  have hφ : 0 < phiGold := by linarith [phiGold_gt_one]
  unfold phiPot
  rw [if_neg (not_le.mpr hpos)]
  have hpow : ((2 : ℝ) ^ (-y)) ^ alphaGold = phiGold ^ (-y) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), two_rpow_alphaGold]
  rw [hpow, ← Real.rpow_natCast phiGold 200, ← Real.rpow_add hφ]
  push_cast; rw [sub_eq_add_neg]

lemma stage3_exponent_ineq :
    (495376 / 1000000 : ℝ) * Real.log 2 ≤
      (499 / 1000 : ℝ) * Real.log 2 + (501 / 1000 : ℝ) * Real.log (199 / 200) := by
  have hlog2_gt := Real.log_two_gt_d9
  have hlog2_lt := Real.log_two_lt_d9
  have hexp : (200 / 199 : ℝ) ≤ Real.exp (5013 / 1000000) := by
    have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 5013 / 1000000 by norm_num) 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hsum
    norm_num at hsum ⊢
    linarith
  have hlog_ub : Real.log (200 / 199 : ℝ) ≤ 5013 / 1000000 :=
    (Real.log_le_iff_le_exp (by norm_num)).mpr hexp
  have hlog_inv : Real.log (199 / 200 : ℝ) = -Real.log (200 / 199 : ℝ) := by
    rw [show (199 / 200 : ℝ) = (200 / 199 : ℝ)⁻¹ by norm_num, Real.log_inv]
  linarith

/-- **Lemma 5.4 (Stage 3: Fine Polarization via Golden-Ratio Supermartingale)**:
For any `ε ∈ (0, 1)`, any `m₃ ≥ max(100 (m₁ + m₂), ⌈5 × 10⁵ ln(16/ε)⌉)`, and any
Stage-2 path `w : Fin (m₁ + m₂) → Bool` with `Z(w) ≤ 2^(-Y₀)`, the conditional probability
that `Z(W_{m₁ + m₂ + m₃}) ≤ 2^(-200 N^0.49047)` (where `N = 2^(m₁ + m₂ + m₃)`) is at least
`1 - ε / 8`. -/
theorem lemma_5_4_stage3 (P : PolarProcess) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (m₃ : ℕ) (hm₃ : stage3MinDepth ε ≤ m₃)
    (w : Fin (stage1Depth ε + stage2Depth ε) → Bool)
    (hw : P.Z (stage1Depth ε + stage2Depth ε) w ≤ (2 : ℝ) ^ (-(stage2Y0 ε : ℝ))) :
    1 - ε / 8 ≤ treeProb m₃
      (fun b ↦ P.Z ((stage1Depth ε + stage2Depth ε) + m₃) (Fin.append w b) ≤
        (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ ((stage1Depth ε + stage2Depth ε) + m₃)) ^
          (49047 / 100000 : ℝ))) := by
  let m₁₂ := stage1Depth ε + stage2Depth ε
  set Y₀ := stage2Y0 ε
  let thr : ℝ := (2 : ℝ) ^ (-(200 : ℝ))
  let Z' : (t : ℕ) → (Fin t → Bool) → ℝ := fun t b ↦ P.Z (m₁₂ + t) (Fin.append w b)
  have hZ'_nn : ∀ t b, 0 ≤ Z' t b := fun t b ↦ (P.Z_mem (m₁₂ + t) (Fin.append w b)).1
  have hZ'_plus : ∀ (t : ℕ) (b : Fin t → Bool),
      Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) = (Z' t b) ^ 2 := by
    intro t b
    change P.Z (m₁₂ + (t + 1)) (Fin.append w (Fin.snoc (α := fun _ ↦ Bool) b true)) = _
    rw [← fin_append_snoc]
    exact P.Z_plus (m₁₂ + t) (Fin.append w b)
  have hZ'_minus : ∀ (t : ℕ) (b : Fin t → Bool),
      Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) ≤ 2 * Z' t b := by
    intro t b
    change P.Z (m₁₂ + (t + 1)) (Fin.append w (Fin.snoc (α := fun _ ↦ Bool) b false)) ≤ _
    rw [← fin_append_snoc]
    exact P.Z_minus (m₁₂ + t) (Fin.append w b)
  have hZ'0 : Z' 0 Fin.elim0 = P.Z m₁₂ w := by
    simp only [Z']
    congr 1; ext i; simp [Fin.append, Fin.addCases]; rfl
  -- Stopped golden-ratio supermartingale `N_t = phiPot(Z'_{t ∧ σ})`
  let N := stoppedTransform Z' thr phiPot
  have hN_nn : ∀ t b, 0 ≤ N t b := stoppedTransform_nonneg Z' thr phiPot phiPot_nonneg
  have hN_super : ∀ t b,
      (N (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) +
        N (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)) / 2 ≤ N t b := by
    intro t b
    by_cases hhit : hitAbove Z' thr t b
    · simp only [N]
      rw [stoppedTransform_snoc_hit Z' thr phiPot hhit false,
          stoppedTransform_snoc_hit Z' thr phiPot hhit true]
      linarith
    · have hZle : Z' t b ≤ thr := by
        by_contra hgt
        apply hhit
        refine ⟨Fin.last t, ?_⟩
        have hpre : pathPrefix (Nat.le_of_lt_succ (Fin.last t).isLt) b = b := by ext i; rfl
        simpa [hpre] using lt_of_not_ge hgt
      simp only [N]
      rw [stoppedTransform_snoc_not_hit Z' thr phiPot hhit false,
          stoppedTransform_snoc_not_hit Z' thr phiPot hhit true,
          stoppedTransform_not_hit Z' thr phiPot t b hhit, hZ'_plus]
      by_cases hz0 : Z' t b = 0
      · have hzm : Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) = 0 :=
          le_antisymm (by linarith [hZ'_minus t b, hz0]) (hZ'_nn _ _)
        simp [phiPot, hz0, hzm]
      · have hzpos : 0 < Z' t b := lt_of_le_of_ne (hZ'_nn t b) (Ne.symm hz0)
        have hφ : 0 < phiGold := by linarith [phiGold_gt_one]
        -- `phiPot (Z' (t+1) false) ≤ phiGold * phiPot (Z' t b)`
        have hminus_le : phiPot (Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false)) ≤
            phiGold * phiPot (Z' t b) := by
          calc phiPot (Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false))
              ≤ phiPot (2 * Z' t b) := phiPot_mono (hZ'_nn _ _) (hZ'_minus t b)
            _ = phiGold * phiPot (Z' t b) := by
                unfold phiPot
                rw [if_neg (not_le.mpr (by positivity)), if_neg (not_le.mpr hzpos),
                  Real.mul_rpow (by norm_num) (le_of_lt hzpos), two_rpow_alphaGold]
                ring
        -- `phiPot ((Z' t b)^2) ≤ phiGold^(-2 : ℤ) * phiPot (Z' t b)` since `Z' t b ≤ 2^(-200) ≤ 1/4`
        have hthr_le : thr ≤ 1 / 4 := by
          simp only [thr]
          calc (2 : ℝ) ^ (-(200 : ℝ)) ≤ (2 : ℝ) ^ (-(2 : ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 1 / 4 := by norm_num
        have hplus_le : phiPot ((Z' t b) ^ 2) ≤ phiGold ^ (-2 : ℤ) * phiPot (Z' t b) := by
          have hsq_le : (Z' t b) ^ 2 ≤ (1 / 4) * Z' t b := by
            rw [sq]
            exact mul_le_mul_of_nonneg_right (le_trans hZle hthr_le) (le_of_lt hzpos)
          calc phiPot ((Z' t b) ^ 2)
              ≤ phiPot ((1 / 4) * Z' t b) := phiPot_mono (sq_nonneg _) hsq_le
            _ = phiGold ^ (-2 : ℤ) * phiPot (Z' t b) := by
                unfold phiPot
                rw [if_neg (not_le.mpr (by positivity)), if_neg (not_le.mpr hzpos),
                  Real.mul_rpow (by norm_num) (le_of_lt hzpos)]
                have hq : (1 / 4 : ℝ) ^ alphaGold = phiGold ^ (-2 : ℤ) := by
                  have h14 : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by norm_num
                  rw [h14, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm,
                    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), two_rpow_alphaGold]
                  rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
                rw [hq]; ring
        have hsum_id := phiGold_add_inv_sq
        have hpot_nn := phiPot_nonneg (Z' t b)
        nlinarith
  -- Step 1: Doob maximal inequality gives `P(hitAbove Z' thr m₃) ≤ ε / 16`
  have hY0_ge : (200 : ℝ) ≤ (Y₀ : ℝ) := by
    simp only [Y₀, stage2Y0]; exact_mod_cast Nat.le_add_right 200 _
  have hZ0_le_thr : Z' 0 Fin.elim0 ≤ thr := by
    rw [hZ'0]
    exact le_trans hw (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  have hprob_hit : treeProb m₃ (hitAbove Z' thr m₃) ≤ ε / 16 := by
    have hdoob := tree_doob_maximal m₃ (fun t _ b ↦ N t b) (fun t _ b ↦ hN_nn t b)
      (fun t _ b ↦ hN_super t b) 1 one_pos
    have hsub : treeProb m₃ (hitAbove Z' thr m₃) ≤
        treeProb m₃ (fun b ↦ ∃ t : Fin (m₃ + 1),
          (1 : ℝ) ≤ N t.val (pathPrefix (Nat.le_of_lt_succ t.isLt) b)) := by
      apply treeProb_mono
      intro b hhit
      exact hitAbove_imp_stoppedTransform_ge Z' thr 1 phiPot hZ0_le_thr
        (fun x hx ↦ by
          have h1 : phiPot thr = 1 := by
            simp only [thr, phiPot_two_rpow_neg, sub_self, Real.rpow_zero]
          rw [← h1]
          exact phiPot_mono (Real.rpow_nonneg (by norm_num) _) (le_of_lt hx))
        m₃ b hhit
    have hN0_le : N 0 Fin.elim0 ≤ ε / 16 := by
      have hN0 : N 0 Fin.elim0 = phiPot (P.Z m₁₂ w) := by simp [N, stoppedTransform, hZ'0]
      rw [hN0]
      calc phiPot (P.Z m₁₂ w)
          ≤ phiPot ((2 : ℝ) ^ (-(Y₀ : ℝ))) := phiPot_mono (P.Z_mem m₁₂ w).1 hw
        _ = phiGold ^ (200 - (Y₀ : ℝ)) := phiPot_two_rpow_neg (Y₀ : ℝ)
        _ ≤ ε / 16 := by
            have hφ : 0 < phiGold := by linarith [phiGold_gt_one]
            have hlogφ : 0 < Real.log phiGold := Real.log_pos phiGold_gt_one
            have hceil : Real.log (16 / ε) / Real.log phiGold ≤ ((Y₀ : ℝ) - 200) := by
              have h1 : Real.log (16 / ε) / Real.log phiGold ≤
                  (Nat.ceil (Real.log (16 / ε) / Real.log phiGold) : ℝ) := Nat.le_ceil _
              have hY : (Y₀ : ℝ) = 200 + (Nat.ceil (Real.log (16 / ε) / Real.log phiGold) : ℝ) := by
                simp only [Y₀, stage2Y0]; push_cast; rfl
              linarith
            rw [Real.rpow_def_of_pos hφ]
            have hε16 : ε / 16 = Real.exp (-Real.log (16 / ε)) := by
              rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
            rw [hε16]
            apply Real.exp_le_exp.mpr
            have hmul := mul_le_mul_of_nonneg_left hceil (le_of_lt hlogφ)
            have hsimp : Real.log phiGold * (Real.log (16 / ε) / Real.log phiGold) =
                Real.log (16 / ε) := by field_simp [ne_of_gt hlogφ]
            linarith
    rw [div_one] at hdoob
    exact le_trans hsub (le_trans hdoob hN0_le)
  -- Step 2: Hoeffding gives `P(S < 0.499 m₃) ≤ ε / 16`
  have hm₃_hoeff : (500000 : ℝ) * Real.log (16 / ε) ≤ (m₃ : ℝ) := by
    have h1 : Nat.ceil (500000 * Real.log (16 / ε)) ≤ m₃ := le_trans (le_max_right _ _) hm₃
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
  have hprob_hoeff : treeProb m₃ (fun b ↦
      (∑ i : Fin m₃, if b i then (1 : ℝ) else 0) < (499 / 1000 : ℝ) * m₃) ≤ ε / 16 := by
    have hhoeff := tree_hoeffding_lower m₃ (1 / 1000) (by norm_num)
    have h499 : (1 / 2 - 1 / 1000 : ℝ) = 499 / 1000 := by norm_num
    rw [h499] at hhoeff
    have hexp_le : Real.exp (-2 * (1 / 1000 : ℝ) ^ 2 * m₃) ≤ ε / 16 := by
      have hε16 : ε / 16 = Real.exp (-Real.log (16 / ε)) := by
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
      rw [hε16]
      apply Real.exp_le_exp.mpr
      linarith
    linarith only [hhoeff, hexp_le]
  -- Step 3: Deterministic path bound on `{¬ hitAbove Z' thr m₃} ∩ {S ≥ 0.499 m₃}`
  have hgood_imp : ∀ b : Fin m₃ → Bool,
      ¬ hitAbove Z' thr m₃ b →
      (499 / 1000 : ℝ) * m₃ ≤ (∑ i : Fin m₃, if b i then (1 : ℝ) else 0) →
      Z' m₃ b ≤ (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ (m₁₂ + m₃)) ^ (49047 / 100000 : ℝ)) := by
    intro b hnot hS
    by_cases hz0 : Z' m₃ b = 0
    · rw [hz0]; exact Real.rpow_nonneg (by norm_num) _
    · -- All prefixes have `0 < Z' t (pathPrefix _ b) ≤ 2^(-200)`
      have hpos_all : ∀ (t : ℕ) (ht : t ≤ m₃), 0 < Z' t (pathPrefix ht b) := by
        intro t ht
        by_contra hle
        have hz_t : Z' t (pathPrefix ht b) = 0 :=
          le_antisymm (not_lt.mp hle) (hZ'_nn t _)
        -- Propagate zero forward from `t` to `m₃`
        have hzero_fwd : ∀ s (hts : t ≤ s) (hsm : s ≤ m₃), Z' s (pathPrefix hsm b) = 0 := by
          intro s
          induction s with
          | zero =>
            intro hts hsm
            have ht0 : t = 0 := Nat.eq_zero_of_le_zero hts
            subst ht0; exact hz_t
          | succ s ih =>
            intro hts hsm
            by_cases hteq : t = s + 1
            · subst hteq; exact hz_t
            · have hts' : t ≤ s := by omega
              have hsm' : s ≤ m₃ := Nat.le_of_succ_le hsm
              have hprev := ih hts' hsm'
              have hsnoc_eq : pathPrefix hsm b =
                  Fin.snoc (α := fun _ ↦ Bool) (pathPrefix hsm' b) (b ⟨s, hsm⟩) := by
                ext i
                refine Fin.lastCases ?_ ?_ i
                · simp [pathPrefix, Fin.snoc_last]
                · intro j; simp [pathPrefix, Fin.snoc_castSucc]
              rw [hsnoc_eq]
              cases hb : b ⟨s, hsm⟩
              · exact le_antisymm (by linarith [hZ'_minus s (pathPrefix hsm' b), hprev])
                  (hZ'_nn _ _)
              · rw [hZ'_plus, hprev]; norm_num
        have hfinal := hzero_fwd m₃ ht le_rfl
        have hpre_id : pathPrefix (le_refl m₃) b = b := by ext i; rfl
        rw [hpre_id] at hfinal
        exact hz0 hfinal
      have hle_all : ∀ (t : ℕ) (ht : t ≤ m₃), Z' t (pathPrefix ht b) ≤ thr := by
        intro t ht
        by_contra hgt
        exact hnot ⟨⟨t, Nat.lt_succ_of_le ht⟩, lt_of_not_ge hgt⟩
      -- Inductively lower-bound `Y_t := -log₂(Z'_t) ≥ 200 · 2^(S_t) · (199/200)^(t - S_t)`
      have hY_ind : ∀ (t : ℕ) (ht : t ≤ m₃),
          200 * (2 : ℝ) ^ (∑ i : Fin t, if b ⟨i.val, lt_of_lt_of_le i.isLt ht⟩ then (1 : ℝ) else 0) *
            (199 / 200 : ℝ) ^ ((t : ℝ) -
              ∑ i : Fin t, if b ⟨i.val, lt_of_lt_of_le i.isLt ht⟩ then (1 : ℝ) else 0) ≤
            -Real.logb 2 (Z' t (pathPrefix ht b)) := by
        intro t
        induction t with
        | zero =>
          intro ht
          simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, sub_zero,
            Real.rpow_zero, mul_one]
          have hle := hle_all 0 ht
          have hpos := hpos_all 0 ht
          have hlog : Real.logb 2 (Z' 0 (pathPrefix ht b)) ≤ Real.logb 2 thr :=
            Real.logb_le_logb_of_le (by norm_num) hpos hle
          have hlogthr : Real.logb 2 thr = -200 :=
            Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
          linarith
        | succ t ih =>
          intro ht
          have ht' : t ≤ m₃ := Nat.le_of_succ_le ht
          have hprev := ih ht'
          have hY_ge_200 : (200 : ℝ) ≤ -Real.logb 2 (Z' t (pathPrefix ht' b)) := by
            have hle := hle_all t ht'
            have hpos := hpos_all t ht'
            have hlog : Real.logb 2 (Z' t (pathPrefix ht' b)) ≤ Real.logb 2 thr :=
              Real.logb_le_logb_of_le (by norm_num) hpos hle
            have hlogthr : Real.logb 2 thr = -200 :=
              Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
            linarith
          have hsnoc_eq : pathPrefix ht b =
              Fin.snoc (α := fun _ ↦ Bool) (pathPrefix ht' b) (b ⟨t, ht⟩) := by
            ext i
            refine Fin.lastCases ?_ ?_ i
            · simp [pathPrefix, Fin.snoc_last]
            · intro j; simp [pathPrefix, Fin.snoc_castSucc]
          set St : ℝ := ∑ i : Fin t, if b ⟨i.val, lt_of_lt_of_le i.isLt ht'⟩ then (1 : ℝ) else 0
          have hsum_succ : (∑ i : Fin (t + 1), if b ⟨i.val, lt_of_lt_of_le i.isLt ht⟩ then (1 : ℝ) else 0) =
              St + (if b ⟨t, ht⟩ then (1 : ℝ) else 0) := by
            rw [Fin.sum_univ_castSucc]
            rfl
          rw [hsum_succ, hsnoc_eq]
          cases hb : b ⟨t, ht⟩
          · -- `false` step: `Y_{t+1} ≥ Y_t - 1 ≥ (199/200) Y_t`
            simp only [Bool.false_eq_true, ↓reduceIte, add_zero, Nat.cast_add, Nat.cast_one]
            have hlog_step : -Real.logb 2 (Z' t (pathPrefix ht' b)) - 1 ≤
                -Real.logb 2 (Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) (pathPrefix ht' b) false)) := by
              have hpos_next := hpos_all (t + 1) ht
              rw [hsnoc_eq, hb] at hpos_next
              have hpos_prev := hpos_all t ht'
              have hle := hZ'_minus t (pathPrefix ht' b)
              have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos_next hle
              rw [Real.logb_mul (by norm_num) (ne_of_gt hpos_prev), Real.logb_self_eq_one (by norm_num)] at hlog
              linarith
            have hscale : (199 / 200 : ℝ) * (-Real.logb 2 (Z' t (pathPrefix ht' b))) ≤
                -Real.logb 2 (Z' t (pathPrefix ht' b)) - 1 := by linarith
            have hexp : ((t : ℝ) + 1 - St) = ((t : ℝ) - St) + 1 := by ring
            rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 199 / 200), Real.rpow_one]
            nlinarith
          · -- `true` step: `Y_{t+1} = 2 Y_t`
            simp only [↓reduceIte, Nat.cast_add, Nat.cast_one]
            have hsub_eq : (t : ℝ) + 1 - (St + 1) = (t : ℝ) - St := by ring
            rw [hsub_eq, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, hZ'_plus]
            rw [Real.logb_pow]
            push_cast
            linarith
      -- Specialize to `t = m₃` and apply `stage3_exponent_ineq`
      have hYm3 := hY_ind m₃ le_rfl
      have hpre_id : pathPrefix (le_refl m₃) b = b := by ext i; rfl
      rw [hpre_id] at hYm3
      set S : ℝ := ∑ i : Fin m₃, if b i then (1 : ℝ) else 0
      have hS_le : S ≤ (m₃ : ℝ) := by
        calc S ≤ ∑ _i : Fin m₃, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ by split_ifs <;> norm_num
          _ = (m₃ : ℝ) := by simp
      have hpow_ge : ((2 : ℝ) ^ (m₁₂ + m₃)) ^ (49047 / 100000 : ℝ) ≤
          (2 : ℝ) ^ S * (199 / 200 : ℝ) ^ ((m₃ : ℝ) - S) := by
        rw [← Real.rpow_natCast (2 : ℝ) (m₁₂ + m₃), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have hLHS_pos : 0 < (2 : ℝ) ^ (((m₁₂ + m₃ : ℕ) : ℝ) * (49047 / 100000 : ℝ)) :=
          Real.rpow_pos_of_pos (by norm_num) _
        have hRHS_pos : 0 < (2 : ℝ) ^ S * (199 / 200 : ℝ) ^ ((m₃ : ℝ) - S) :=
          mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)
        rw [← Real.log_le_log_iff hLHS_pos hRHS_pos,
          Real.log_rpow (by norm_num),
          Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _))
            (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)),
          Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)]
        have hm₃_ratio : 100 * (m₁₂ : ℝ) ≤ (m₃ : ℝ) := by
          have h1 : 100 * m₁₂ ≤ m₃ := le_trans (le_max_left _ _) hm₃
          exact_mod_cast h1
        have hn_le : ((m₁₂ + m₃ : ℕ) : ℝ) * (49047 / 100000 : ℝ) ≤
            (495376 / 1000000 : ℝ) * (m₃ : ℝ) := by
          push_cast; linarith
        have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hlog199_neg : Real.log (199 / 200 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
        have h1 : ((m₁₂ + m₃ : ℕ) : ℝ) * (49047 / 100000 : ℝ) * Real.log 2 ≤
            (495376 / 1000000 : ℝ) * Real.log 2 * (m₃ : ℝ) := by nlinarith
        have h2 : (495376 / 1000000 : ℝ) * Real.log 2 * (m₃ : ℝ) ≤
            ((499 / 1000 : ℝ) * Real.log 2 + (501 / 1000 : ℝ) * Real.log (199 / 200)) * (m₃ : ℝ) :=
          mul_le_mul_of_nonneg_right stage3_exponent_ineq (Nat.cast_nonneg m₃)
        have h3 : ((499 / 1000 : ℝ) * Real.log 2 + (501 / 1000 : ℝ) * Real.log (199 / 200)) * (m₃ : ℝ) ≤
            S * Real.log 2 + ((m₃ : ℝ) - S) * Real.log (199 / 200) := by
          have hdiff : (S * Real.log 2 + ((m₃ : ℝ) - S) * Real.log (199 / 200)) -
              ((499 / 1000 : ℝ) * Real.log 2 + (501 / 1000 : ℝ) * Real.log (199 / 200)) * (m₃ : ℝ) =
              (S - (499 / 1000 : ℝ) * (m₃ : ℝ)) * (Real.log 2 - Real.log (199 / 200)) := by ring
          have hnn : 0 ≤ (S - (499 / 1000 : ℝ) * (m₃ : ℝ)) * (Real.log 2 - Real.log (199 / 200)) :=
            mul_nonneg (by linarith) (by linarith)
          linarith
        linarith
      have hlog_final : Real.logb 2 (Z' m₃ b) ≤
          -(200 : ℝ) * ((2 : ℝ) ^ (m₁₂ + m₃)) ^ (49047 / 100000 : ℝ) := by linarith
      have hpos_m3 : 0 < Z' m₃ b := by
        have := hpos_all m₃ le_rfl
        rwa [hpre_id] at this
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      rw [← Real.log_le_log_iff hpos_m3 (Real.rpow_pos_of_pos (by norm_num) _),
        Real.log_rpow (by norm_num)]
      rw [Real.logb, div_le_iff₀ hlog2_pos] at hlog_final
      exact hlog_final
  -- Step 4: Union bound and complement
  have hbad : treeProb m₃ (fun b ↦
      (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ (m₁₂ + m₃)) ^ (49047 / 100000 : ℝ)) < Z' m₃ b) ≤ ε / 8 := by
    have hsub : treeProb m₃ (fun b ↦
        (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ (m₁₂ + m₃)) ^ (49047 / 100000 : ℝ)) < Z' m₃ b) ≤
        treeProb m₃ (fun b ↦ hitAbove Z' thr m₃ b ∨
          (∑ i : Fin m₃, if b i then (1 : ℝ) else 0) < (499 / 1000 : ℝ) * m₃) := by
      apply treeProb_mono
      intro b hgt
      by_contra hnor
      push Not at hnor
      exact not_le_of_gt hgt (hgood_imp b hnor.1 hnor.2)
    have hunion := treeProb_union m₃ (hitAbove Z' thr m₃)
      (fun b ↦ (∑ i : Fin m₃, if b i then (1 : ℝ) else 0) < (499 / 1000 : ℝ) * m₃)
    linarith only [hsub, hunion, hprob_hit, hprob_hoeff]
  have hcompl := treeProb_compl m₃ (fun b ↦
    Z' m₃ b ≤ (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ (m₁₂ + m₃)) ^ (49047 / 100000 : ℝ)))
  have heq : treeProb m₃ (fun b ↦ ¬ (Z' m₃ b ≤
      (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ (m₁₂ + m₃)) ^ (49047 / 100000 : ℝ)))) =
      treeProb m₃ (fun b ↦
        (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ (m₁₂ + m₃)) ^ (49047 / 100000 : ℝ)) < Z' m₃ b) :=
    treeProb_congr m₃ (fun _ ↦ not_le)
  rw [heq] at hcompl
  linarith only [hbad, hcompl]

/-! ### Error-Exponent Bound and Abstract Polynomial-Blocklength Polarization -/

/-- For every `n ≥ 1` (so `N = 2^n ≥ 2`),
`2 √(N · 2^(-200 N^0.49047)) ≤ 2^(-N^0.49)`. -/
theorem polar_error_exponent_bound {n : ℕ} (hn : 1 ≤ n) :
    2 * Real.sqrt ((2 : ℝ) ^ n *
      (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))) ≤
      (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := by
  set N : ℝ := (2 : ℝ) ^ n
  have hN_ge2 : (2 : ℝ) ≤ N := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hN_pos : 0 < N := by linarith
  have hN_ge1 : (1 : ℝ) ≤ N := by linarith
  have hpow_mono : N ^ (49 / 100 : ℝ) ≤ N ^ (49047 / 100000 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
  have hpow_ge1 : (1 : ℝ) ≤ N ^ (49 / 100 : ℝ) := Real.one_le_rpow hN_ge1 (by norm_num)
  have hlogN_le : Real.log N ≤ (100 / 49 : ℝ) * N ^ (49 / 100 : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hN_pos (49 / 100 : ℝ))
    rw [Real.log_rpow hN_pos] at h1
    linarith
  have hn_le : (n : ℝ) ≤ 4 * N ^ (49 / 100 : ℝ) := by
    have hlogN_eq : Real.log N = (n : ℝ) * Real.log 2 := by
      simp only [N, Real.log_pow]
    have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hexp : 1 + (n : ℝ) / 2 - 100 * N ^ (49047 / 100000 : ℝ) ≤ -N ^ (49 / 100 : ℝ) := by
    linarith
  have hLHS_eq : 2 * Real.sqrt (N * (2 : ℝ) ^ (-(200 : ℝ) * N ^ (49047 / 100000 : ℝ))) =
      (2 : ℝ) ^ (1 + (n : ℝ) / 2 - 100 * N ^ (49047 / 100000 : ℝ)) := by
    have hprod : N * (2 : ℝ) ^ (-(200 : ℝ) * N ^ (49047 / 100000 : ℝ)) =
        (2 : ℝ) ^ ((n : ℝ) - 200 * N ^ (49047 / 100000 : ℝ)) := by
      simp only [N]
      rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1; ring
    rw [hprod, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show (2 : ℝ) * (2 : ℝ) ^ (((n : ℝ) - 200 * N ^ (49047 / 100000 : ℝ)) * (1 / 2)) =
        (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (((n : ℝ) - 200 * N ^ (49047 / 100000 : ℝ)) * (1 / 2)) by
          rw [Real.rpow_one],
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  rw [hLHS_eq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- **Abstract Theorem 1.1 (Polynomial-Blocklength Polarization)**:
There exist universal constants `μ, C₀ > 0` (independent of the channel / process and of `ε`)
such that for every `PolarProcess P`, every `ε ∈ (0, 1)`, and every `n : ℕ` with
`2^n ≥ C₀ (1/ε)^μ`, the fraction of synthetic paths with
`Z_n(b) ≤ 2^(-200 (2^n)^0.49047)` is at least `I(W) - ε`. -/
theorem polar_process_poly_blocklength :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ (P : PolarProcess) {ε : ℝ}, 0 < ε → ε < 1 →
        ∀ (n : ℕ), C₀ * (1 / ε) ^ μ ≤ (2 : ℝ) ^ n →
          P.symCap - ε ≤ treeProb n (fun b ↦
            P.Z n b ≤ (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))) := by
  have hL0 : 0 < Lambda0 := Lambda0_pos
  have hL1 : Lambda0 < 1 := Lambda0_lt_one
  have hlogL : 0 < Real.logb 2 (1 / Lambda0) :=
    Real.logb_pos (by norm_num) ((one_lt_div hL0).mpr hL1)
  have hlogg : 0 < Real.logb 2 (1 / gamma2) :=
    Real.logb_pos (by norm_num) ((one_lt_div gamma2_pos).mpr gamma2_lt_one)
  have hlogφ : 0 < Real.log phiGold := Real.log_pos phiGold_gt_one
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set A₁ : ℝ := 8 / Real.logb 2 (1 / Lambda0)
  set B₁ : ℝ := 48 / Real.logb 2 (1 / Lambda0) + 1
  set AY : ℝ := Real.log 2 / Real.log phiGold
  set BY : ℝ := 201 + 4 * Real.log 2 / Real.log phiGold
  set A₂ : ℝ := (AY / 2 + 1) / Real.logb 2 (1 / gamma2)
  set B₂ : ℝ := (BY / 2 + 3) / Real.logb 2 (1 / gamma2) + 1
  set μ : ℝ := 101 * (A₁ + A₂) + 500000 * Real.log 2
  set B : ℝ := 101 * (B₁ + B₂) + 2000000 * Real.log 2 + 1
  refine ⟨μ, (2 : ℝ) ^ B, by positivity, Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro P ε hε0 hε1 n hn
  set L : ℝ := Real.logb 2 (1 / ε)
  have hL_pos : 0 < L := Real.logb_pos (by norm_num) ((one_lt_div hε0).mpr hε1)
  have hlog_inv : Real.log (1 / ε) = L * Real.log 2 := by
    simp only [L, Real.logb]
    field_simp [ne_of_gt hlog2]
  have hm₁_ub : (stage1Depth ε : ℝ) ≤ A₁ * L + B₁ := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ (8 / Real.logb 2 (1 / Lambda0)) * Real.logb 2 (64 / ε) by
      have h64 : 0 < Real.logb 2 (64 / ε) :=
        Real.logb_pos (by norm_num) (by rw [lt_div_iff₀ hε0]; linarith)
      positivity)
    have h64_eq : Real.logb 2 (64 / ε) = 6 + L := by
      rw [show (64 / ε : ℝ) = 64 * (1 / ε) by ring,
        Real.logb_mul (by norm_num) (by positivity),
        show (64 : ℝ) = (2 : ℝ) ^ (6 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      push_cast; ring
    unfold stage1Depth
    rw [h64_eq] at hceil ⊢
    have : A₁ * L + B₁ = (8 / Real.logb 2 (1 / Lambda0)) * (6 + L) + 1 := by
      simp only [A₁, B₁]; ring
    linarith
  have hY₀_ub : (stage2Y0 ε : ℝ) ≤ AY * L + BY := by
    have h16_pos : 0 < Real.log (16 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε0]; linarith)
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.log (16 / ε) / Real.log phiGold by positivity)
    have h16_eq : Real.log (16 / ε) = 4 * Real.log 2 + L * Real.log 2 := by
      rw [show (16 / ε : ℝ) = 16 * (1 / ε) by ring,
        Real.log_mul (by norm_num) (by positivity),
        show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow, hlog_inv]
      push_cast; ring
    have hYeq : (stage2Y0 ε : ℝ) = 200 + (Nat.ceil (Real.log (16 / ε) / Real.log phiGold) : ℝ) := by
      simp only [stage2Y0]; push_cast; rfl
    rw [h16_eq] at hceil hYeq
    have : AY * L + BY = 200 + ((4 * Real.log 2 + L * Real.log 2) / Real.log phiGold + 1) := by
      simp only [AY, BY]; ring
    linarith
  have hm₂_ub : (stage2Depth ε : ℝ) ≤ A₂ * L + B₂ := by
    have h8_eq : Real.logb 2 (8 / ε) = 3 + L := by
      rw [show (8 / ε : ℝ) = 8 * (1 / ε) by ring,
        Real.logb_mul (by norm_num) (by positivity),
        show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      push_cast; ring
    have harg_nn : 0 ≤ ((stage2Y0 ε : ℝ) / 2 + Real.logb 2 (8 / ε)) / Real.logb 2 (1 / gamma2) := by
      rw [h8_eq]; positivity
    have hceil := Nat.ceil_lt_add_one harg_nn
    unfold stage2Depth
    rw [h8_eq] at hceil ⊢
    have hdiv_le : ((stage2Y0 ε : ℝ) / 2 + (3 + L)) / Real.logb 2 (1 / gamma2) ≤
        ((AY * L + BY) / 2 + (3 + L)) / Real.logb 2 (1 / gamma2) :=
      div_le_div_of_nonneg_right (by linarith) (le_of_lt hlogg)
    have : A₂ * L + B₂ = ((AY * L + BY) / 2 + (3 + L)) / Real.logb 2 (1 / gamma2) + 1 := by
      simp only [A₂, B₂]; ring
    linarith
  have hm₃_ub : (stage3MinDepth ε : ℝ) ≤
      max (100 * ((A₁ + A₂) * L + (B₁ + B₂)))
        (500000 * Real.log 2 * L + 2000000 * Real.log 2 + 1) := by
    unfold stage3MinDepth
    push_cast
    apply max_le_max
    · linarith
    · have h16_pos : 0 < Real.log (16 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε0]; linarith)
      have hceil := Nat.ceil_lt_add_one (show 0 ≤ 500000 * Real.log (16 / ε) by positivity)
      have h16_eq : Real.log (16 / ε) = 4 * Real.log 2 + L * Real.log 2 := by
        rw [show (16 / ε : ℝ) = 16 * (1 / ε) by ring,
          Real.log_mul (by norm_num) (by positivity),
          show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow, hlog_inv]
        push_cast; ring
      rw [h16_eq] at hceil ⊢
      linarith
  have hn_ge_real : μ * L + B ≤ (n : ℝ) := by
    have hLHS_pos : 0 < (2 : ℝ) ^ B * (1 / ε) ^ μ :=
      mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by positivity) _)
    have hlog_le : Real.logb 2 ((2 : ℝ) ^ B * (1 / ε) ^ μ) ≤ Real.logb 2 ((2 : ℝ) ^ n) :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hLHS_pos hn
    rw [Real.logb_mul (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _))
        (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)),
      Real.logb_rpow (by norm_num) (by norm_num),
      Real.logb_rpow_eq_mul_logb_of_pos (by positivity),
      Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog_le
    linarith
  have hsum_le_n : stage1Depth ε + stage2Depth ε + stage3MinDepth ε ≤ n := by
    have hreal : ((stage1Depth ε + stage2Depth ε + stage3MinDepth ε : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      have hmax_le : max (100 * ((A₁ + A₂) * L + (B₁ + B₂)))
          (500000 * Real.log 2 * L + 2000000 * Real.log 2 + 1) ≤
          100 * ((A₁ + A₂) * L + (B₁ + B₂)) +
            (500000 * Real.log 2 * L + 2000000 * Real.log 2 + 1) := by
        apply max_le <;> linarith [show 0 ≤ 100 * ((A₁ + A₂) * L + (B₁ + B₂)) by positivity,
          show 0 ≤ 500000 * Real.log 2 * L + 2000000 * Real.log 2 + 1 by positivity]
      have htot : μ * L + B =
          (A₁ * L + B₁) + (A₂ * L + B₂) +
            (100 * ((A₁ + A₂) * L + (B₁ + B₂)) +
              (500000 * Real.log 2 * L + 2000000 * Real.log 2 + 1)) := by
        simp only [μ, B]; ring
      linarith
    exact_mod_cast hreal
  by_cases htriv : P.symCap ≤ ε
  · exact le_trans (by linarith) (treeProb_nonneg n _)
  · let m₁ := stage1Depth ε
    let m₂ := stage2Depth ε
    let m₃ := n - (m₁ + m₂)
    have hm₃_ge : stage3MinDepth ε ≤ m₃ := by omega
    have hn_eq : (m₁ + m₂) + m₃ = n := by omega
    rw [← hn_eq]
    have h1 := lemma_5_2_stage1 P hε0 hε1
    have hstage3_avg : (1 - ε / 8) *
        treeProb (m₁ + m₂) (fun w ↦ P.Z (m₁ + m₂) w ≤ (2 : ℝ) ^ (-(stage2Y0 ε : ℝ))) ≤
        treeProb ((m₁ + m₂) + m₃) (fun b ↦
          P.Z ((m₁ + m₂) + m₃) b ≤
            (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ ((m₁ + m₂) + m₃)) ^ (49047 / 100000 : ℝ))) := by
      rw [treeProb_append (m₁ + m₂) m₃, treeProb_eq_avg, ← treeAvg_mul_const]
      apply treeAvg_mono
      intro w
      by_cases hw : P.Z (m₁ + m₂) w ≤ (2 : ℝ) ^ (-(stage2Y0 ε : ℝ))
      · rw [ind_pos hw, mul_one]
        exact lemma_5_4_stage3 P hε0 hε1 m₃ hm₃_ge w hw
      · rw [ind_neg hw, mul_zero]
        exact treeProb_nonneg m₃ _
    have hstage2_avg : (1 - ε / 4) *
        treeProb m₁ (fun w ↦ P.H m₁ w ≤ stage1Eta ε) ≤
        treeProb (m₁ + m₂) (fun w ↦ P.Z (m₁ + m₂) w ≤ (2 : ℝ) ^ (-(stage2Y0 ε : ℝ))) := by
      rw [treeProb_append m₁ m₂, treeProb_eq_avg, ← treeAvg_mul_const]
      apply treeAvg_mono
      intro w
      by_cases hw : P.H m₁ w ≤ stage1Eta ε
      · rw [ind_pos hw, mul_one]
        exact lemma_5_3_stage2 P hε0 hε1 w (h1.2.1 w hw)
      · rw [ind_neg hw, mul_zero]
        exact treeProb_nonneg m₂ _
    have hE1 := h1.1
    have hcap_le : P.symCap ≤ 1 := by
      unfold PolarProcess.symCap; linarith [(P.H_mem 0 Fin.elim0).1]
    have hprod_ge : P.symCap - ε ≤ (1 - ε / 8) * ((1 - ε / 4) * (P.symCap - ε / 4)) := by
      have hcap_pos : 0 < P.symCap - ε / 4 := by linarith
      have h1 : 1 - 3 * ε / 8 ≤ (1 - ε / 8) * (1 - ε / 4) := by nlinarith
      have h2 : (1 - 3 * ε / 8) * (P.symCap - ε / 4) ≤
          (1 - ε / 8) * ((1 - ε / 4) * (P.symCap - ε / 4)) := by
        have := mul_le_mul_of_nonneg_right h1 (le_of_lt hcap_pos)
        linarith
      have h3 : P.symCap - ε ≤ (1 - 3 * ε / 8) * (P.symCap - ε / 4) := by nlinarith
      linarith
    have hchain : (1 - ε / 8) * ((1 - ε / 4) * (P.symCap - ε / 4)) ≤
        (1 - ε / 8) * ((1 - ε / 4) * treeProb m₁ (fun w ↦ P.H m₁ w ≤ stage1Eta ε)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_left hE1 (by linarith)
    have hchain2 : (1 - ε / 8) * ((1 - ε / 4) * treeProb m₁ (fun w ↦ P.H m₁ w ≤ stage1Eta ε)) ≤
        (1 - ε / 8) * treeProb (m₁ + m₂) (fun w ↦ P.Z (m₁ + m₂) w ≤ (2 : ℝ) ^ (-(stage2Y0 ε : ℝ))) :=
      mul_le_mul_of_nonneg_left hstage2_avg (by linarith)
    linarith

/-- **Abstract Corollary 5.5 (Simultaneous Amplitude/Phase Polarization)**:
Applying `polar_process_poly_blocklength` with gap `ε' = ε / 4` to a pair of polarization
processes `(P_A, P_P)` yields a joint good set `G_N(W_A) ∩ G_N(W_P)` of rate at least
`I(W_A) + I(W_P) - 1 - ε / 2` at polynomial blocklength `N = 2^n ≥ C₀ (4 / ε)^μ`. -/
theorem polar_process_dual_pair_poly_blocklength :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ (P_A P_P : PolarProcess) {ε : ℝ}, 0 < ε → ε < 1 →
        ∀ (n : ℕ), C₀ * (4 / ε) ^ μ ≤ (2 : ℝ) ^ n →
          P_A.symCap + P_P.symCap - 1 - ε / 2 ≤
            treeProb n (fun b ↦
              P_A.Z n b ≤ (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ)) ∧
              P_P.Z n b ≤ (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))) := by
  rcases polar_process_poly_blocklength with ⟨μ, C₀, hμ, hC₀, hpoly⟩
  refine ⟨μ, C₀, hμ, hC₀, ?_⟩
  intro P_A P_P ε hε0 hε1 n hn
  have hε4_0 : 0 < ε / 4 := by linarith
  have hε4_1 : ε / 4 < 1 := by linarith
  have hn' : C₀ * (1 / (ε / 4)) ^ μ ≤ (2 : ℝ) ^ n := by
    have h4 : (1 / (ε / 4) : ℝ) = 4 / ε := by ring
    rwa [h4]
  have hA := hpoly P_A hε4_0 hε4_1 n hn'
  have hP := hpoly P_P hε4_0 hε4_1 n hn'
  set thr := (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))
  have hunion := treeProb_union n (fun b ↦ ¬ P_A.Z n b ≤ thr) (fun b ↦ ¬ P_P.Z n b ≤ thr)
  have hcompl_A := treeProb_compl n (fun b ↦ P_A.Z n b ≤ thr)
  have hcompl_P := treeProb_compl n (fun b ↦ P_P.Z n b ≤ thr)
  have hcompl_AP := treeProb_compl n (fun b ↦ P_A.Z n b ≤ thr ∧ P_P.Z n b ≤ thr)
  have hdemorgan : treeProb n (fun b ↦ ¬ (P_A.Z n b ≤ thr ∧ P_P.Z n b ≤ thr)) =
      treeProb n (fun b ↦ ¬ P_A.Z n b ≤ thr ∨ ¬ P_P.Z n b ≤ thr) :=
    treeProb_congr n (fun _ ↦ not_and_or)
  rw [hdemorgan] at hcompl_AP
  linarith

end PolarCodes
