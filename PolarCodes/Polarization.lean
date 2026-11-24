/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import PolarCodes.SplittingBounds

/-!
# Three-Stage Polarization Martingale Engine (Section 5.2)

This module formalizes the binary-tree probability space on `Fin n → Bool`, discrete-time
supermartingale Doob maximal inequality, Hoeffding's inequality for i.i.d. Bernoulli(1/2) sums,
and the three-stage polarization lemmas (**Lemmas 5.2, 5.3, 5.4**) that drive **Theorem 1.1**.
-/

open BigOperators Real Finset

namespace PolarCodes

/-- Uniform expectation of `f : (Fin n → Bool) → ℝ` over the `2^n` binary paths. -/
noncomputable def treeAvg (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ b : Fin n → Bool, f b) / (2 : ℝ) ^ n

/-- Uniform probability of an event `P` on `Fin n → Bool`. -/
noncomputable def treeProb (n : ℕ) (P : (Fin n → Bool) → Prop) [DecidablePred P] : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (2 : ℝ) ^ n

lemma treeAvg_const (n : ℕ) (c : ℝ) : treeAvg n (fun _ ↦ c) = c := by
  unfold treeAvg
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hpos : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp [hpos]

lemma treeAvg_add (n : ℕ) (f g : (Fin n → Bool) → ℝ) :
    treeAvg n (fun b ↦ f b + g b) = treeAvg n f + treeAvg n g := by
  unfold treeAvg
  rw [Finset.sum_add_distrib, add_div]

lemma treeAvg_mono (n : ℕ) {f g : (Fin n → Bool) → ℝ} (h : ∀ b, f b ≤ g b) :
    treeAvg n f ≤ treeAvg n g := by
  unfold treeAvg
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun b _ ↦ h b) (by positivity)

lemma treeAvg_nonneg (n : ℕ) {f : (Fin n → Bool) → ℝ} (h : ∀ b, 0 ≤ f b) :
    0 ≤ treeAvg n f := by
  unfold treeAvg
  exact div_nonneg (Finset.sum_nonneg fun b _ ↦ h b) (by positivity)

/-- One-step splitting of `treeAvg (n + 1)` by the first coordinate `b 0`. -/
lemma treeAvg_succ (n : ℕ) (f : (Fin (n + 1) → Bool) → ℝ) :
    treeAvg (n + 1) f =
      (treeAvg n (fun b ↦ f (Fin.cons false b)) + treeAvg n (fun b ↦ f (Fin.cons true b))) / 2 := by
  unfold treeAvg
  have hsum : (∑ b : Fin (n + 1) → Bool, f b) =
      (∑ b : Fin n → Bool, f (Fin.cons false b)) + (∑ b : Fin n → Bool, f (Fin.cons true b)) := by
    let e : (Bool × (Fin n → Bool)) ≃ (Fin (n + 1) → Bool) :=
      { toFun := fun p ↦ Fin.cons p.1 p.2
        invFun := fun b ↦ (b 0, fun i ↦ b i.succ)
        left_inv := fun ⟨a, b⟩ ↦ by ext <;> simp
        right_inv := fun b ↦ by
          ext i
          refine Fin.cases ?_ ?_ i <;> simp }
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    simp [e]
  rw [hsum, pow_succ]
  ring

/-- Markov's inequality on `Fin n → Bool`. -/
lemma treeProb_markov (n : ℕ) {f : (Fin n → Bool) → ℝ} (hf : ∀ b, 0 ≤ f b)
    {c : ℝ} (hc : 0 < c) {P : (Fin n → Bool) → Prop} [DecidablePred P]
    (hP : ∀ b, P b → c ≤ f b) :
    treeProb n P ≤ treeAvg n f / c := by
  unfold treeProb treeAvg
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hle : ((Finset.univ.filter P).card : ℝ) * c ≤ ∑ b : Fin n → Bool, f b := by
    calc ((Finset.univ.filter P).card : ℝ) * c
        = ∑ _b ∈ Finset.univ.filter P, c := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ Finset.univ.filter P, f b :=
          Finset.sum_le_sum fun b hb ↦ hP b (Finset.mem_filter.mp hb).2
      _ ≤ ∑ b : Fin n → Bool, f b :=
          Finset.sum_le_univ_sum_of_nonneg hf
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  nlinarith

/-- Binary-tree supermartingale Doob maximal inequality:
if `M` is a nonnegative supermartingale along a binary tree of depth `m`, then for any `c > 0`,
`P[∃ t ≤ m, M_t ≥ c] ≤ M_0 / c`. -/
lemma tree_doob_maximal :
    ∀ (m : ℕ) (M : ∀ t : ℕ, t ≤ m → (Fin t → Bool) → ℝ)
      (_hnn : ∀ t (ht : t ≤ m) b, 0 ≤ M t ht b)
      (_hsuper : ∀ t (ht : t + 1 ≤ m) b,
        (M (t + 1) ht (Fin.snoc b false) + M (t + 1) ht (Fin.snoc b true)) / 2 ≤
          M t (Nat.le_of_succ_le ht) b)
      (c : ℝ) (_hc : 0 < c),
      letI : DecidablePred (fun b : Fin m → Bool ↦
        ∃ t : Fin (m + 1), c ≤ M t.val (Nat.le_of_lt_succ t.isLt) (fun i ↦ b ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ t.isLt)⟩)) :=
        Classical.decPred _
      treeProb m (fun b ↦ ∃ t : Fin (m + 1),
        c ≤ M t.val (Nat.le_of_lt_succ t.isLt)
          (fun i ↦ b ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ t.isLt)⟩)) ≤
        M 0 (Nat.zero_le m) Fin.elim0 / c := by
  intro m
  induction m with
  | zero =>
    intro M hnn _ c hc
    classical
    unfold treeProb
    simp only [pow_zero, div_one]
    by_cases h0 : c ≤ M 0 (Nat.zero_le 0) Fin.elim0
    · have hcard : ((Finset.univ.filter (fun b : Fin 0 → Bool ↦
          ∃ t : Fin 1, c ≤ M t.val (Nat.le_of_lt_succ t.isLt)
            (fun i ↦ b ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ t.isLt)⟩))).card : ℝ) ≤ 1 := by
        have hsub : (Finset.univ.filter _).card ≤ (Finset.univ : Finset (Fin 0 → Bool)).card :=
          Finset.card_filter_le _ _
        have h1 : (Finset.univ : Finset (Fin 0 → Bool)).card = 1 := by simp
        exact_mod_cast le_trans hsub (le_of_eq h1)
      have h1le : 1 ≤ M 0 (Nat.zero_le 0) Fin.elim0 / c := (one_le_div hc).mpr h0
      linarith
    · have hempty : (Finset.univ.filter (fun b : Fin 0 → Bool ↦
          ∃ t : Fin 1, c ≤ M t.val (Nat.le_of_lt_succ t.isLt)
            (fun i ↦ b ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ t.isLt)⟩))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro b _ ⟨t, ht⟩
        have ht0 : t.val = 0 := Nat.lt_one_iff.mp t.isLt
        have hfun : (fun i : Fin t.val ↦ b ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ t.isLt)⟩) =
            Fin.elim0 := by
          subst ht0; ext i; exact Fin.elim0 i
        subst ht0
        exact h0 (by simpa [hfun] using ht)
      rw [hempty, Nat.cast_zero]
      exact div_nonneg (hnn 0 (Nat.zero_le 0) Fin.elim0) (le_of_lt hc)
  | succ m ih =>
    intro M hnn hsuper c hc
    classical
    by_cases h0 : c ≤ M 0 (Nat.zero_le (m + 1)) Fin.elim0
    · -- Already hit at t = 0: probability ≤ 1 ≤ M_0 / c
      have hprob_le_one : treeProb (m + 1) _ ≤ 1 := by
        unfold treeProb
        rw [div_le_one (by positivity)]
        have hsub := Finset.card_filter_le (Finset.univ : Finset (Fin (m + 1) → Bool)) _
        have hcard : (Finset.univ : Finset (Fin (m + 1) → Bool)).card = 2 ^ (m + 1) := by simp
        exact_mod_cast le_trans hsub (le_of_eq hcard)
      have h1le : 1 ≤ M 0 (Nat.zero_le (m + 1)) Fin.elim0 / c := (one_le_div hc).mpr h0
      linarith
    · -- Not hit at t = 0: split on the first bit `b 0 ∈ {false, true}` and apply IH to both subtrees!
      let Mbranch : Bool → ∀ t : ℕ, t ≤ m → (Fin t → Bool) → ℝ :=
        fun a t ht b ↦ M (t + 1) (Nat.succ_le_succ ht) (Fin.cons a b)
      have hih : ∀ a : Bool,
          treeProb m (fun b ↦ ∃ t : Fin (m + 1),
            c ≤ Mbranch a t.val (Nat.le_of_lt_succ t.isLt)
              (fun i ↦ b ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ t.isLt)⟩)) ≤
          Mbranch a 0 (Nat.zero_le m) Fin.elim0 / c := by
        intro a
        apply ih (Mbranch a)
        · intro t ht b; exact hnn (t + 1) (Nat.succ_le_succ ht) (Fin.cons a b)
        · intro t ht b
          have hcons_snoc : ∀ x : Bool,
              Fin.cons a (Fin.snoc b x) = Fin.snoc (Fin.cons a b) x := by
            intro x; ext i
            refine Fin.cases ?_ ?_ i
            · simp [Fin.snoc]
            · intro j
              simp only [Fin.cons_succ, Fin.snoc]
              split_ifs with h1 h2
              · rfl
              · omega
              · omega
              · rfl
          simp only [Mbranch, hcons_snoc]
          exact hsuper (t + 1) (Nat.succ_le_succ ht) (Fin.cons a b)
        · exact hc
      -- Relate `treeProb (m + 1)` to average of the two branches via `treeAvg_succ`
      have hprob_eq_avg : ∀ (k : ℕ) (P : (Fin k → Bool) → Prop) [DecidablePred P],
          treeProb k P = treeAvg k (fun b ↦ if P b then (1 : ℝ) else 0) := by
        intro k P _
        unfold treeProb treeAvg
        rw [Finset.sum_boole]
      rw [hprob_eq_avg, treeAvg_succ]
      have hbranch_eq : ∀ a : Bool,
          treeAvg m (fun b ↦
            if (∃ t : Fin (m + 2), c ≤ M t.val (Nat.le_of_lt_succ t.isLt)
              (fun i ↦ (Fin.cons a b) ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ t.isLt)⟩))
            then (1 : ℝ) else 0) =
          treeProb m (fun b ↦ ∃ t : Fin (m + 1),
            c ≤ Mbranch a t.val (Nat.le_of_lt_succ t.isLt)
              (fun i ↦ b ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ t.isLt)⟩)) := by
        intro a
        rw [hprob_eq_avg]
        congr 1; ext b
        congr 1; apply propext
        constructor
        · rintro ⟨t, ht⟩
          refine Fin.cases ?_ ?_ t ht
          · intro ht0
            exfalso; apply h0
            convert ht0 using 2
            ext i; exact Fin.elim0 i
          · intro t' ht'
            refine ⟨t', ?_⟩
            convert ht' using 2
            ext i
            refine Fin.cases ?_ ?_ i <;> simp
        · rintro ⟨t', ht'⟩
          refine ⟨t'.succ, ?_⟩
          convert ht' using 2
          ext i
          refine Fin.cases ?_ ?_ i <;> simp
      rw [hbranch_eq false, hbranch_eq true]
      have hstep0 := hsuper 0 (Nat.succ_le_succ (Nat.zero_le m)) Fin.elim0
      have hsnoc0 : ∀ a : Bool, Fin.snoc (Fin.elim0 : Fin 0 → Bool) a = Fin.cons a Fin.elim0 := by
        intro a; ext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi; simp [Fin.snoc]
      simp only [hsnoc0] at hstep0
      have hf := hih false
      have ht := hih true
      have hsum_le : (Mbranch false 0 (Nat.zero_le m) Fin.elim0 / c +
          Mbranch true 0 (Nat.zero_le m) Fin.elim0 / c) / 2 ≤
          M 0 (Nat.zero_le (m + 1)) Fin.elim0 / c := by
        have hcomb : (Mbranch false 0 (Nat.zero_le m) Fin.elim0 / c +
            Mbranch true 0 (Nat.zero_le m) Fin.elim0 / c) / 2 =
            ((M 1 (Nat.succ_le_succ (Nat.zero_le m)) (Fin.cons false Fin.elim0) +
              M 1 (Nat.succ_le_succ (Nat.zero_le m)) (Fin.cons true Fin.elim0)) / 2) / c := by
          simp only [Mbranch]; ring
        rw [hcomb]
        exact div_le_div_of_nonneg_right hstep0 (le_of_lt hc)
      linarith

/-- Elementary Hoeffding moment bound: `(e^u + e^(-u)) / 2 ≤ e^(u²/2)` for all `u ∈ ℝ`. -/
lemma cosh_le_exp_half_sq (u : ℝ) :
    (Real.exp u + Real.exp (-u)) / 2 ≤ Real.exp (u ^ 2 / 2) := by
  suffices h : ∀ x : ℝ, 0 ≤ x → (Real.exp x + Real.exp (-x)) / 2 ≤ Real.exp (x ^ 2 / 2) by
    rcases le_or_gt 0 u with hu | hu
    · exact h u hu
    · have := h (-u) (by linarith)
      simpa [add_comm] using this
  intro x hx
  -- Equivalent to `f(x) := log((e^x + e^(-x))/2) - x²/2 ≤ 0` for `x ≥ 0`
  have hpos : 0 < (Real.exp x + Real.exp (-x)) / 2 := by positivity
  rw [← Real.log_le_iff_le_exp hpos]
  let f : ℝ → ℝ := fun t ↦ Real.log ((Real.exp t + Real.exp (-t)) / 2) - t ^ 2 / 2
  have hf0 : f 0 = 0 := by simp [f]
  have hanti : AntitoneOn f (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · have hcont : Continuous f := by
        unfold f
        apply Continuous.sub
        · exact Continuous.log (by fun_prop) (fun t ↦ ne_of_gt (by positivity))
        · fun_prop
      exact hcont.continuousOn
    · intro t _
      have hd_in : HasDerivAt (fun s : ℝ ↦ (Real.exp s + Real.exp (-s)) / 2)
          ((Real.exp t - Real.exp (-t)) / 2) t := by
        have h1 := Real.hasDerivAt_exp t
        have h2 : HasDerivAt (fun s : ℝ ↦ Real.exp (-s)) (Real.exp (-t) * (-1)) t :=
          (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
        convert (h1.fun_add h2).div_const 2 using 1; ring
      have hd_log : HasDerivAt (fun s : ℝ ↦ Real.log ((Real.exp s + Real.exp (-s)) / 2))
          (((Real.exp t - Real.exp (-t)) / 2) / ((Real.exp t + Real.exp (-t)) / 2)) t :=
        hd_in.log (ne_of_gt (by positivity))
      have hd_sq : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
        convert ((hasDerivAt_pow 2 t).div_const 2) using 1; ring
      exact (hd_log.fun_sub hd_sq).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have hd_in : HasDerivAt (fun s : ℝ ↦ (Real.exp s + Real.exp (-s)) / 2)
          ((Real.exp t - Real.exp (-t)) / 2) t := by
        have h1 := Real.hasDerivAt_exp t
        have h2 : HasDerivAt (fun s : ℝ ↦ Real.exp (-s)) (Real.exp (-t) * (-1)) t :=
          (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
        convert (h1.fun_add h2).div_const 2 using 1; ring
      have hd_log : HasDerivAt (fun s : ℝ ↦ Real.log ((Real.exp s + Real.exp (-s)) / 2))
          (((Real.exp t - Real.exp (-t)) / 2) / ((Real.exp t + Real.exp (-t)) / 2)) t :=
        hd_in.log (ne_of_gt (by positivity))
      have hd_sq : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
        convert ((hasDerivAt_pow 2 t).div_const 2) using 1; ring
      rw [(hd_log.fun_sub hd_sq).deriv]
      -- Need `tanh t ≤ t`, i.e., `e^t - e^(-t) ≤ t (e^t + e^(-t))`, i.e., `e^(2t)(1-t) ≤ 1 + t`
      -- Simpler: `g(t) := t(e^t + e^(-t)) - (e^t - e^(-t))` has `g(0)=0` and `g'(t) = t(e^t - e^(-t)) ≥ 0`!
      have htanh : (Real.exp t - Real.exp (-t)) / 2 ≤ t * ((Real.exp t + Real.exp (-t)) / 2) := by
        let g : ℝ → ℝ := fun s ↦ s * (Real.exp s + Real.exp (-s)) - (Real.exp s - Real.exp (-s))
        have hg0 : g 0 = 0 := by simp [g]
        have hgmono : MonotoneOn g (Ici 0) := by
          apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
          · exact (by simp only [g]; fun_prop : Continuous g).continuousOn
          · intro s _
            have h1 : HasDerivAt (fun r : ℝ ↦ Real.exp r + Real.exp (-r))
                (Real.exp s - Real.exp (-s)) s := by
              have ha := Real.hasDerivAt_exp s
              have hb : HasDerivAt (fun r : ℝ ↦ Real.exp (-r)) (Real.exp (-s) * (-1)) s :=
                (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id s).neg
              convert ha.fun_add hb using 1; ring
            have h2 : HasDerivAt (fun r : ℝ ↦ Real.exp r - Real.exp (-r))
                (Real.exp s + Real.exp (-s)) s := by
              have ha := Real.hasDerivAt_exp s
              have hb : HasDerivAt (fun r : ℝ ↦ Real.exp (-r)) (Real.exp (-s) * (-1)) s :=
                (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id s).neg
              convert ha.fun_sub hb using 1; ring
            exact (((hasDerivAt_id' s).fun_mul h1).fun_sub h2).differentiableAt.differentiableWithinAt
          · intro s hs
            rw [interior_Ici] at hs
            have h1 : HasDerivAt (fun r : ℝ ↦ Real.exp r + Real.exp (-r))
                (Real.exp s - Real.exp (-s)) s := by
              have ha := Real.hasDerivAt_exp s
              have hb : HasDerivAt (fun r : ℝ ↦ Real.exp (-r)) (Real.exp (-s) * (-1)) s :=
                (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id s).neg
              convert ha.fun_add hb using 1; ring
            have h2 : HasDerivAt (fun r : ℝ ↦ Real.exp r - Real.exp (-r))
                (Real.exp s + Real.exp (-s)) s := by
              have ha := Real.hasDerivAt_exp s
              have hb : HasDerivAt (fun r : ℝ ↦ Real.exp (-r)) (Real.exp (-s) * (-1)) s :=
                (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id s).neg
              convert ha.fun_sub hb using 1; ring
            have hd : HasDerivAt g (s * (Real.exp s - Real.exp (-s))) s := by
              convert ((hasDerivAt_id' s).fun_mul h1).fun_sub h2 using 1; ring
            rw [hd.deriv]
            have hexp : Real.exp (-s) ≤ Real.exp s := Real.exp_le_exp.mpr (by linarith)
            nlinarith
        have hgt := hgmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (le_of_lt ht)) (le_of_lt ht)
        simp only [g] at hgt hg0
        linarith
      have hden : 0 < (Real.exp t + Real.exp (-t)) / 2 := by positivity
      rw [sub_nonpos, div_le_iff₀ hden]
      exact htanh
  have hfx := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp only [f] at hfx hf0
  linarith

/-- Hoeffding's inequality for the sum of `m` i.i.d. Bernoulli(1/2) random variables:
`P[∑ B_i < (1/2 - δ) m] ≤ exp(-2 δ² m)` for all `δ ≥ 0`. -/
theorem tree_hoeffding_lower (m : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    letI : DecidablePred (fun b : Fin m → Bool ↦
      (∑ i : Fin m, if b i then (1 : ℝ) else 0) < (1 / 2 - δ) * m) := Classical.decPred _
    treeProb m (fun b ↦ (∑ i : Fin m, if b i then (1 : ℝ) else 0) < (1 / 2 - δ) * m) ≤
      Real.exp (-2 * δ ^ 2 * m) := by
  classical
  set t : ℝ := 4 * δ
  have hmgf : ∀ k : ℕ,
      treeAvg k (fun b ↦ Real.exp (t * ((k : ℝ) / 2 - ∑ i : Fin k, if b i then (1 : ℝ) else 0))) =
        ((Real.exp (t / 2) + Real.exp (-(t / 2))) / 2) ^ k := by
    intro k
    induction k with
    | zero => simp [treeAvg]
    | succ k ih =>
      rw [treeAvg_succ]
      have hfalse : ∀ b : Fin k → Bool,
          Real.exp (t * (((k + 1 : ℕ) : ℝ) / 2 - ∑ i : Fin (k + 1), if Fin.cons false b i then (1 : ℝ) else 0)) =
            Real.exp (t / 2) * Real.exp (t * ((k : ℝ) / 2 - ∑ i : Fin k, if b i then (1 : ℝ) else 0)) := by
        intro b
        rw [Fin.sum_univ_succ, ← Real.exp_add]
        simp only [Fin.cons_zero, Bool.false_eq_true, ↓reduceIte, zero_add, Fin.cons_succ, Nat.cast_add,
          Nat.cast_one]
        congr 1; ring
      have htrue : ∀ b : Fin k → Bool,
          Real.exp (t * (((k + 1 : ℕ) : ℝ) / 2 - ∑ i : Fin (k + 1), if Fin.cons true b i then (1 : ℝ) else 0)) =
            Real.exp (-(t / 2)) * Real.exp (t * ((k : ℝ) / 2 - ∑ i : Fin k, if b i then (1 : ℝ) else 0)) := by
        intro b
        rw [Fin.sum_univ_succ, ← Real.exp_add]
        simp only [Fin.cons_zero, ↓reduceIte, Fin.cons_succ, Nat.cast_add, Nat.cast_one]
        congr 1; ring
      have hpull : ∀ (c : ℝ) (g : (Fin k → Bool) → ℝ),
          treeAvg k (fun b ↦ c * g b) = c * treeAvg k g := by
        intro c g; unfold treeAvg; rw [← Finset.mul_sum, mul_div_assoc]
      simp_rw [hfalse, htrue, hpull, ih]
      rw [pow_succ]; ring
  have hmarkov := treeProb_markov m
    (f := fun b ↦ Real.exp (t * ((m : ℝ) / 2 - ∑ i : Fin m, if b i then (1 : ℝ) else 0)))
    (fun _ ↦ le_of_lt (Real.exp_pos _))
    (c := Real.exp (t * δ * m)) (Real.exp_pos _)
    (P := fun b ↦ (∑ i : Fin m, if b i then (1 : ℝ) else 0) < (1 / 2 - δ) * m)
    (fun b hb ↦ by
      apply Real.exp_le_exp.mpr
      have ht0 : 0 ≤ t := by simp only [t]; linarith
      nlinarith)
  calc treeProb m (fun b ↦ (∑ i : Fin m, if b i then (1 : ℝ) else 0) < (1 / 2 - δ) * m)
      ≤ ((Real.exp (t / 2) + Real.exp (-(t / 2))) / 2) ^ m / Real.exp (t * δ * m) := by
        rwa [hmgf m] at hmarkov
    _ ≤ (Real.exp ((t / 2) ^ 2 / 2)) ^ m / Real.exp (t * δ * m) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
        exact pow_le_pow_left₀ (by positivity) (cosh_le_exp_half_sq (t / 2)) m
    _ = Real.exp (-2 * δ ^ 2 * m) := by
        rw [← Real.exp_nat_mul, ← Real.exp_sub]
        congr 1; simp only [t]; ring

end PolarCodes
