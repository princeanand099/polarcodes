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

open BigOperators Real Finset Set

namespace PolarCodes

/-! ### Binary-Tree Expectation and Probability on `Fin n → Bool` -/

/-- Canonical `{0, 1}`-valued indicator of a proposition `P`. -/
noncomputable def ind (P : Prop) : ℝ := by
  classical
  exact if P then 1 else 0

lemma ind_pos {P : Prop} (h : P) : ind P = 1 := by
  unfold ind; classical simp [h]

lemma ind_neg {P : Prop} (h : ¬ P) : ind P = 0 := by
  unfold ind; classical simp [h]

lemma ind_nonneg (P : Prop) : 0 ≤ ind P := by
  by_cases h : P
  · rw [ind_pos h]; norm_num
  · rw [ind_neg h]

lemma ind_le_one (P : Prop) : ind P ≤ 1 := by
  by_cases h : P
  · rw [ind_pos h]
  · rw [ind_neg h]; norm_num

/-- Uniform expectation of `f : (Fin n → Bool) → ℝ` over the `2^n` binary paths. -/
noncomputable def treeAvg (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ b : Fin n → Bool, f b) / (2 : ℝ) ^ n

/-- Uniform probability of an event `P` on `Fin n → Bool`. -/
noncomputable def treeProb (n : ℕ) (P : (Fin n → Bool) → Prop) : ℝ :=
  treeAvg n (fun b ↦ ind (P b))

lemma treeProb_eq_avg (n : ℕ) (P : (Fin n → Bool) → Prop) :
    treeProb n P = treeAvg n (fun b ↦ ind (P b)) := rfl

lemma treeAvg_zero (f : (Fin 0 → Bool) → ℝ) : treeAvg 0 f = f Fin.elim0 := by
  unfold treeAvg
  rw [pow_zero, div_one, Finset.univ_unique, Finset.sum_singleton]
  congr 1

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

lemma treeAvg_sub (n : ℕ) (f g : (Fin n → Bool) → ℝ) :
    treeAvg n (fun b ↦ f b - g b) = treeAvg n f - treeAvg n g := by
  unfold treeAvg
  rw [Finset.sum_sub_distrib, sub_div]

lemma treeAvg_mul_const (n : ℕ) (c : ℝ) (f : (Fin n → Bool) → ℝ) :
    treeAvg n (fun b ↦ c * f b) = c * treeAvg n f := by
  unfold treeAvg
  rw [← Finset.mul_sum, mul_div_assoc]

lemma treeAvg_mono (n : ℕ) {f g : (Fin n → Bool) → ℝ} (h : ∀ b, f b ≤ g b) :
    treeAvg n f ≤ treeAvg n g := by
  unfold treeAvg
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun b _ ↦ h b) (by positivity)

lemma treeAvg_nonneg (n : ℕ) {f : (Fin n → Bool) → ℝ} (h : ∀ b, 0 ≤ f b) :
    0 ≤ treeAvg n f := by
  unfold treeAvg
  exact div_nonneg (Finset.sum_nonneg fun b _ ↦ h b) (by positivity)

lemma treeProb_le_one (n : ℕ) (P : (Fin n → Bool) → Prop) : treeProb n P ≤ 1 := by
  calc treeProb n P
      = treeAvg n (fun b ↦ ind (P b)) := rfl
    _ ≤ treeAvg n (fun _ ↦ 1) := treeAvg_mono n (fun b ↦ ind_le_one (P b))
    _ = 1 := treeAvg_const n 1

lemma treeProb_nonneg (n : ℕ) (P : (Fin n → Bool) → Prop) : 0 ≤ treeProb n P :=
  treeAvg_nonneg n (fun b ↦ ind_nonneg (P b))

lemma treeProb_mono (n : ℕ) {P Q : (Fin n → Bool) → Prop} (h : ∀ b, P b → Q b) :
    treeProb n P ≤ treeProb n Q := by
  apply treeAvg_mono
  intro b
  by_cases hp : P b
  · rw [ind_pos hp, ind_pos (h b hp)]
  · rw [ind_neg hp]; exact ind_nonneg (Q b)

lemma treeProb_congr (n : ℕ) {P Q : (Fin n → Bool) → Prop} (h : ∀ b, P b ↔ Q b) :
    treeProb n P = treeProb n Q := by
  apply le_antisymm
  · exact treeProb_mono n (fun b hp ↦ (h b).mp hp)
  · exact treeProb_mono n (fun b hq ↦ (h b).mpr hq)

lemma treeProb_union (n : ℕ) (P Q : (Fin n → Bool) → Prop) :
    treeProb n (fun b ↦ P b ∨ Q b) ≤ treeProb n P + treeProb n Q := by
  rw [treeProb_eq_avg, treeProb_eq_avg, treeProb_eq_avg, ← treeAvg_add]
  apply treeAvg_mono
  intro b
  by_cases hp : P b <;> by_cases hq : Q b
  · rw [ind_pos (Or.inl hp), ind_pos hp, ind_pos hq]; norm_num
  · rw [ind_pos (Or.inl hp), ind_pos hp, ind_neg hq]; norm_num
  · rw [ind_pos (Or.inr hq), ind_neg hp, ind_pos hq]; norm_num
  · rw [ind_neg (by tauto), ind_neg hp, ind_neg hq]; norm_num

lemma treeProb_compl (n : ℕ) (P : (Fin n → Bool) → Prop) :
    treeProb n (fun b ↦ ¬ P b) = 1 - treeProb n P := by
  have hsum : treeProb n (fun b ↦ ¬ P b) + treeProb n P = 1 := by
    rw [treeProb_eq_avg, treeProb_eq_avg, ← treeAvg_add]
    trans treeAvg n (fun _ ↦ 1)
    · congr 1; ext b
      by_cases hp : P b
      · rw [ind_neg (not_not.mpr hp), ind_pos hp]; norm_num
      · rw [ind_pos hp, ind_neg hp]; norm_num
    · exact treeAvg_const n 1
  linarith

/-- One-step splitting of `treeAvg (n + 1)` by the first coordinate `b 0`. -/
lemma treeAvg_succ (n : ℕ) (f : (Fin (n + 1) → Bool) → ℝ) :
    treeAvg (n + 1) f =
      (treeAvg n (fun b ↦ f (Fin.cons (α := fun _ ↦ Bool) false b)) +
        treeAvg n (fun b ↦ f (Fin.cons (α := fun _ ↦ Bool) true b))) / 2 := by
  unfold treeAvg
  have hsum : (∑ b : Fin (n + 1) → Bool, f b) =
      (∑ b : Fin n → Bool, f (Fin.cons (α := fun _ ↦ Bool) false b)) +
      (∑ b : Fin n → Bool, f (Fin.cons (α := fun _ ↦ Bool) true b)) := by
    let e : (Bool × (Fin n → Bool)) ≃ (Fin (n + 1) → Bool) :=
      { toFun := fun p ↦ Fin.cons (α := fun _ ↦ Bool) p.1 p.2
        invFun := fun b ↦ (b 0, fun i ↦ b i.succ)
        left_inv := fun ⟨a, b⟩ ↦ by ext <;> simp
        right_inv := fun b ↦ by
          ext i
          refine Fin.cases ?_ ?_ i <;> simp }
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    simp [e, add_comm]
  rw [hsum, pow_succ]
  ring

/-- One-step splitting of `treeAvg (n + 1)` by the last coordinate `b (Fin.last n)`. -/
lemma treeAvg_snoc (n : ℕ) (f : (Fin (n + 1) → Bool) → ℝ) :
    treeAvg (n + 1) f =
      (treeAvg n (fun b ↦ f (Fin.snoc (α := fun _ ↦ Bool) b false)) +
        treeAvg n (fun b ↦ f (Fin.snoc (α := fun _ ↦ Bool) b true))) / 2 := by
  unfold treeAvg
  have hsum : (∑ b : Fin (n + 1) → Bool, f b) =
      (∑ b : Fin n → Bool, f (Fin.snoc (α := fun _ ↦ Bool) b false)) +
      (∑ b : Fin n → Bool, f (Fin.snoc (α := fun _ ↦ Bool) b true)) := by
    let e : (Bool × (Fin n → Bool)) ≃ (Fin (n + 1) → Bool) :=
      { toFun := fun p ↦ Fin.snoc (α := fun _ ↦ Bool) p.2 p.1
        invFun := fun b ↦ (b (Fin.last n), fun i ↦ b i.castSucc)
        left_inv := fun ⟨a, b⟩ ↦ by
          ext
          · simp [Fin.snoc_last]
          · simp [Fin.snoc_castSucc]
        right_inv := fun b ↦ by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · simp [Fin.snoc_last]
          · intro j; simp [Fin.snoc_castSucc] }
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    simp [e, add_comm]
  rw [hsum, pow_succ]
  ring

lemma treeProb_succ (n : ℕ) (P : (Fin (n + 1) → Bool) → Prop) :
    treeProb (n + 1) P =
      (treeProb n (fun b ↦ P (Fin.cons (α := fun _ ↦ Bool) false b)) +
        treeProb n (fun b ↦ P (Fin.cons (α := fun _ ↦ Bool) true b))) / 2 := by
  rw [treeProb_eq_avg, treeAvg_succ, treeProb_eq_avg, treeProb_eq_avg]

lemma fin_append_snoc {m₁ m₂ : ℕ} (b₁ : Fin m₁ → Bool) (b₂ : Fin m₂ → Bool) (a : Bool) :
    Fin.snoc (α := fun _ ↦ Bool) (Fin.append b₁ b₂) a =
      Fin.append b₁ (Fin.snoc (α := fun _ ↦ Bool) b₂ a) := by
  ext i
  refine Fin.addCases (m := m₁) (n := m₂ + 1) ?_ ?_ i
  · intro j
    rw [Fin.append_left]
    have hcast : Fin.castAdd (m₂ + 1) j = (Fin.castAdd m₂ j).castSucc := rfl
    rw [hcast, Fin.snoc_castSucc, Fin.append_left]
  · intro j
    rw [Fin.append_right]
    refine Fin.lastCases ?_ ?_ j
    · have hlast : Fin.natAdd m₁ (Fin.last m₂) = Fin.last (m₁ + m₂) := by ext; simp
      rw [hlast, Fin.snoc_last, Fin.snoc_last]
    · intro k
      have hcast : Fin.natAdd m₁ k.castSucc = (Fin.natAdd m₁ k).castSucc := rfl
      rw [hcast, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.append_right]

/-- Tower property for `treeAvg` over concatenated binary paths `Fin (m₁ + m₂) → Bool`. -/
lemma treeAvg_append (m₁ m₂ : ℕ) (f : (Fin (m₁ + m₂) → Bool) → ℝ) :
    treeAvg (m₁ + m₂) f =
      treeAvg m₁ (fun b₁ ↦ treeAvg m₂ (fun b₂ ↦ f (Fin.append b₁ b₂))) := by
  induction m₂ with
  | zero =>
    have heq : ∀ b₁ : Fin m₁ → Bool,
        treeAvg 0 (fun b₂ ↦ f (Fin.append b₁ b₂)) = f b₁ := by
      intro b₁
      rw [treeAvg_zero]
      congr 1; ext i; simp [Fin.append, Fin.addCases]; rfl
    simp_rw [heq]
    rfl
  | succ m₂ ih =>
    change treeAvg ((m₁ + m₂) + 1) f = _
    rw [treeAvg_snoc (m₁ + m₂)]
    rw [ih (fun b ↦ f (Fin.snoc (α := fun _ ↦ Bool) b false)),
        ih (fun b ↦ f (Fin.snoc (α := fun _ ↦ Bool) b true))]
    simp_rw [fin_append_snoc]
    rw [← treeAvg_add]
    have hdiv : ∀ (g : (Fin m₁ → Bool) → ℝ), treeAvg m₁ g / 2 = treeAvg m₁ (fun b ↦ g b / 2) := by
      intro g; unfold treeAvg; rw [← Finset.sum_div, div_div, div_div, mul_comm]
    rw [hdiv]
    congr 1; ext b₁
    exact (treeAvg_snoc m₂ (fun b₂ ↦ f (Fin.append b₁ b₂))).symm

/-- Tower property for `treeProb` over concatenated binary paths. -/
lemma treeProb_append (m₁ m₂ : ℕ) (P : (Fin (m₁ + m₂) → Bool) → Prop) :
    treeProb (m₁ + m₂) P =
      treeAvg m₁ (fun b₁ ↦ treeProb m₂ (fun b₂ ↦ P (Fin.append b₁ b₂))) :=
  treeAvg_append m₁ m₂ (fun b ↦ ind (P b))

/-- Markov's inequality on `Fin n → Bool`. -/
lemma treeProb_markov (n : ℕ) {f : (Fin n → Bool) → ℝ} (hf : ∀ b, 0 ≤ f b)
    {c : ℝ} (hc : 0 < c) {P : (Fin n → Bool) → Prop}
    (hP : ∀ b, P b → c ≤ f b) :
    treeProb n P ≤ treeAvg n f / c := by
  rw [treeProb_eq_avg, le_div_iff₀ hc, mul_comm, ← treeAvg_mul_const]
  apply treeAvg_mono
  intro b
  by_cases hp : P b
  · rw [ind_pos hp, mul_one]; exact hP b hp
  · rw [ind_neg hp, mul_zero]; exact hf b

/-! ### Prefix Projection and Doob's Maximal Inequality on Binary Trees -/

/-- Prefix of length `t ≤ m` of a binary path `b : Fin m → Bool`. -/
def pathPrefix {t m : ℕ} (ht : t ≤ m) (b : Fin m → Bool) : Fin t → Bool :=
  fun i ↦ b ⟨i.val, lt_of_lt_of_le i.isLt ht⟩

lemma pathPrefix_pathPrefix {s t m : ℕ} (hs : s ≤ t) (ht : t ≤ m) (b : Fin m → Bool) :
    pathPrefix hs (pathPrefix ht b) = pathPrefix (le_trans hs ht) b := rfl

lemma pathPrefix_snoc {t : ℕ} (b : Fin t → Bool) (a : Bool) :
    pathPrefix (Nat.le_succ t) (Fin.snoc (α := fun _ ↦ Bool) b a) = b := by
  ext i
  exact Fin.snoc_castSucc (α := fun _ ↦ Bool) a b i

lemma pathPrefix_snoc_le {s t : ℕ} (hs : s ≤ t) (b : Fin t → Bool) (a : Bool) :
    pathPrefix (le_trans hs (Nat.le_succ t)) (Fin.snoc (α := fun _ ↦ Bool) b a) =
      pathPrefix hs b := by
  rw [← pathPrefix_pathPrefix hs (Nat.le_succ t), pathPrefix_snoc]

/-- Binary-tree supermartingale Doob maximal inequality:
if `M` is a nonnegative supermartingale along a binary tree of depth `m`, then for any `c > 0`,
`P[∃ t ≤ m, M_t ≥ c] ≤ M_0 / c`. -/
theorem tree_doob_maximal :
    ∀ (m : ℕ) (M : ∀ t : ℕ, t ≤ m → (Fin t → Bool) → ℝ)
      (_hnn : ∀ t (ht : t ≤ m) b, 0 ≤ M t ht b)
      (_hsuper : ∀ t (ht : t + 1 ≤ m) b,
        (M (t + 1) ht (Fin.snoc (α := fun _ ↦ Bool) b false) +
          M (t + 1) ht (Fin.snoc (α := fun _ ↦ Bool) b true)) / 2 ≤
          M t (Nat.le_of_succ_le ht) b)
      (c : ℝ) (_hc : 0 < c),
      treeProb m (fun b ↦ ∃ t : Fin (m + 1),
        c ≤ M t.val (Nat.le_of_lt_succ t.isLt)
          (pathPrefix (Nat.le_of_lt_succ t.isLt) b)) ≤
        M 0 (Nat.zero_le m) Fin.elim0 / c := by
  intro m
  induction m with
  | zero =>
    intro M hnn _ c hc
    by_cases h0 : c ≤ M 0 (Nat.zero_le 0) Fin.elim0
    · have h1le : 1 ≤ M 0 (Nat.zero_le 0) Fin.elim0 / c := (one_le_div hc).mpr h0
      exact le_trans (treeProb_le_one 0 _) h1le
    · have hzero : treeProb 0 (fun b ↦ ∃ t : Fin 1,
          c ≤ M t.val (Nat.le_of_lt_succ t.isLt)
            (pathPrefix (Nat.le_of_lt_succ t.isLt) b)) = 0 := by
        rw [treeProb_eq_avg, treeAvg_zero]
        apply ind_neg
        rintro ⟨t, ht⟩
        have ht0 : t = 0 := Subsingleton.elim t 0
        subst ht0
        have hfun : pathPrefix (Nat.le_of_lt_succ (0 : Fin 1).isLt) Fin.elim0 = Fin.elim0 := by
          ext i; exact Fin.elim0 i
        exact h0 (by simpa [hfun] using ht)
      rw [hzero]
      exact div_nonneg (hnn 0 (Nat.zero_le 0) Fin.elim0) (le_of_lt hc)
  | succ m ih =>
    intro M hnn hsuper c hc
    by_cases h0 : c ≤ M 0 (Nat.zero_le (m + 1)) Fin.elim0
    · have h1le : 1 ≤ M 0 (Nat.zero_le (m + 1)) Fin.elim0 / c := (one_le_div hc).mpr h0
      exact le_trans (treeProb_le_one (m + 1) _) h1le
    · let Mbranch : Bool → ∀ t : ℕ, t ≤ m → (Fin t → Bool) → ℝ :=
        fun a t ht b ↦ M (t + 1) (Nat.succ_le_succ ht) (Fin.cons (α := fun _ ↦ Bool) a b)
      have hih : ∀ a : Bool,
          treeProb m (fun b ↦ ∃ t : Fin (m + 1),
            c ≤ Mbranch a t.val (Nat.le_of_lt_succ t.isLt)
              (pathPrefix (Nat.le_of_lt_succ t.isLt) b)) ≤
          Mbranch a 0 (Nat.zero_le m) Fin.elim0 / c := by
        intro a
        apply ih (Mbranch a)
        · intro t ht b
          exact hnn (t + 1) (Nat.succ_le_succ ht) (Fin.cons (α := fun _ ↦ Bool) a b)
        · intro t ht b
          have hcons_snoc : ∀ x : Bool,
              Fin.cons (α := fun _ ↦ Bool) a (Fin.snoc (α := fun _ ↦ Bool) b x) =
                Fin.snoc (α := fun _ ↦ Bool) (Fin.cons (α := fun _ ↦ Bool) a b) x := by
            intro x; ext i
            refine Fin.cases ?_ ?_ i
            · simp [Fin.snoc]
            · intro j
              simp only [Fin.cons_succ, Fin.snoc, Fin.val_succ, Nat.add_lt_add_iff_right]
              split_ifs <;> rfl
          simp only [Mbranch, hcons_snoc]
          exact hsuper (t + 1) (Nat.succ_le_succ ht) (Fin.cons (α := fun _ ↦ Bool) a b)
        · exact hc
      rw [treeProb_succ]
      have hbranch : ∀ a : Bool,
          treeProb m (fun b ↦ ∃ t : Fin (m + 2),
            c ≤ M t.val (Nat.le_of_lt_succ t.isLt)
              (pathPrefix (Nat.le_of_lt_succ t.isLt) (Fin.cons (α := fun _ ↦ Bool) a b))) =
          treeProb m (fun b ↦ ∃ t : Fin (m + 1),
            c ≤ Mbranch a t.val (Nat.le_of_lt_succ t.isLt)
              (pathPrefix (Nat.le_of_lt_succ t.isLt) b)) := by
        intro a
        apply treeProb_congr
        intro b
        constructor
        · rintro ⟨t, ht⟩
          refine Fin.cases ?_ ?_ t ht
          · intro ht0
            exfalso; apply h0
            have hp : pathPrefix (Nat.zero_le (m + 1)) (Fin.cons (α := fun _ ↦ Bool) a b) =
                Fin.elim0 := by ext i; exact Fin.elim0 i
            simpa [hp] using ht0
          · intro t' ht'
            refine ⟨t', ?_⟩
            have hp : pathPrefix (Nat.le_of_lt_succ t'.succ.isLt)
                (Fin.cons (α := fun _ ↦ Bool) a b) =
                Fin.cons (α := fun _ ↦ Bool) a (pathPrefix (Nat.le_of_lt_succ t'.isLt) b) := by
              ext i
              refine Fin.cases ?_ ?_ i
              · simp [pathPrefix]
              · intro j
                change Fin.cons (α := fun _ ↦ Bool) a b
                    (Fin.succ ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ t'.isLt)⟩) =
                  b ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ t'.isLt)⟩
                exact Fin.cons_succ _ _ _
            simpa [Mbranch, hp] using ht'
        · rintro ⟨t', ht'⟩
          refine ⟨t'.succ, ?_⟩
          have hp : pathPrefix (Nat.le_of_lt_succ t'.succ.isLt)
              (Fin.cons (α := fun _ ↦ Bool) a b) =
              Fin.cons (α := fun _ ↦ Bool) a (pathPrefix (Nat.le_of_lt_succ t'.isLt) b) := by
            ext i
            refine Fin.cases ?_ ?_ i
            · simp [pathPrefix]
            · intro j
              change Fin.cons (α := fun _ ↦ Bool) a b
                  (Fin.succ ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ t'.isLt)⟩) =
                b ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ t'.isLt)⟩
              exact Fin.cons_succ _ _ _
          simpa [Mbranch, hp] using ht'
      rw [hbranch false, hbranch true]
      have hstep0 := hsuper 0 (Nat.succ_le_succ (Nat.zero_le m)) Fin.elim0
      have hsnoc0 : ∀ a : Bool,
          Fin.snoc (α := fun _ ↦ Bool) (Fin.elim0 : Fin 0 → Bool) a =
            Fin.cons (α := fun _ ↦ Bool) a Fin.elim0 := by
        intro a; ext i
        have hi : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
        subst hi; simp [Fin.snoc]
      simp only [hsnoc0] at hstep0
      have hf := hih false
      have ht := hih true
      have hsum_le : (Mbranch false 0 (Nat.zero_le m) Fin.elim0 / c +
          Mbranch true 0 (Nat.zero_le m) Fin.elim0 / c) / 2 ≤
          M 0 (Nat.zero_le (m + 1)) Fin.elim0 / c := by
        have hcomb : (Mbranch false 0 (Nat.zero_le m) Fin.elim0 / c +
            Mbranch true 0 (Nat.zero_le m) Fin.elim0 / c) / 2 =
            ((M 1 (Nat.succ_le_succ (Nat.zero_le m)) (Fin.cons (α := fun _ ↦ Bool) false Fin.elim0) +
              M 1 (Nat.succ_le_succ (Nat.zero_le m)) (Fin.cons (α := fun _ ↦ Bool) true Fin.elim0)) / 2) / c := by
          simp only [Mbranch]; ring
        rw [hcomb]
        exact div_le_div_of_nonneg_right hstep0 (le_of_lt hc)
      linarith

/-! ### Hoeffding's Inequality for i.i.d. Bernoulli(1/2) Sums -/

/-- Elementary Hoeffding moment bound: `(e^u + e^(-u)) / 2 ≤ e^(u²/2)` for all `u ∈ ℝ`. -/
lemma cosh_le_exp_half_sq (u : ℝ) :
    (Real.exp u + Real.exp (-u)) / 2 ≤ Real.exp (u ^ 2 / 2) := by
  suffices h : ∀ x : ℝ, 0 ≤ x → (Real.exp x + Real.exp (-x)) / 2 ≤ Real.exp (x ^ 2 / 2) by
    rcases le_or_gt 0 u with hu | hu
    · exact h u hu
    · have := h (-u) (by linarith)
      simpa [add_comm] using this
  intro x hx
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
      rw [interior_Ici, Set.mem_Ioi] at ht
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
            rw [interior_Ici, Set.mem_Ioi] at hs
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
            exact mul_nonneg (le_of_lt hs) (sub_nonneg.mpr hexp)
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
    treeProb m (fun b ↦ (∑ i : Fin m, if b i then (1 : ℝ) else 0) < (1 / 2 - δ) * m) ≤
      Real.exp (-2 * δ ^ 2 * m) := by
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
          Real.exp (t * (((k + 1 : ℕ) : ℝ) / 2 -
            ∑ i : Fin (k + 1), if Fin.cons (α := fun _ ↦ Bool) false b i then (1 : ℝ) else 0)) =
            Real.exp (t / 2) *
              Real.exp (t * ((k : ℝ) / 2 - ∑ i : Fin k, if b i then (1 : ℝ) else 0)) := by
        intro b
        rw [Fin.sum_univ_succ, ← Real.exp_add]
        simp only [Fin.cons_zero, Bool.false_eq_true, ↓reduceIte, zero_add, Fin.cons_succ,
          Nat.cast_add, Nat.cast_one]
        congr 1; ring
      have htrue : ∀ b : Fin k → Bool,
          Real.exp (t * (((k + 1 : ℕ) : ℝ) / 2 -
            ∑ i : Fin (k + 1), if Fin.cons (α := fun _ ↦ Bool) true b i then (1 : ℝ) else 0)) =
            Real.exp (-(t / 2)) *
              Real.exp (t * ((k : ℝ) / 2 - ∑ i : Fin k, if b i then (1 : ℝ) else 0)) := by
        intro b
        rw [Fin.sum_univ_succ, ← Real.exp_add]
        simp only [Fin.cons_zero, ↓reduceIte, Fin.cons_succ, Nat.cast_add, Nat.cast_one]
        congr 1; ring
      simp_rw [hfalse, htrue, treeAvg_mul_const, ih]
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

/-! ### Abstract Polarization Process and Three-Stage Parameters (Section 5.2) -/

/-- An abstract polarization process `(H, Z)` on the binary tree of all finite depths `t : ℕ`,
encoding the four structural laws of Section 5:
- bounds `H_t ∈ [0, 1]` and `Z_t ∈ [0, 1]`,
- entropy conservation `½ (H_{t+1}(b, 0) + H_{t+1}(b, 1)) = H_t(b)` (Eq. 2.8),
- potential contraction `½ (T(H_{t+1}(b, 0)) + T(H_{t+1}(b, 1))) ≤ Λ₀ T(H_t(b))` (Eq. 1.9),
- Bhattacharyya-entropy relation `Z_t(b) ≤ √((2 ln 2) H_t(b))` (Lemma 5.1(a)),
- Bhattacharyya evolution `Z_{t+1}(b, true) = Z_t(b)²` and `Z_{t+1}(b, false) ≤ 2 Z_t(b)` (Lemma 5.1(b)). -/
structure PolarProcess where
  H : (t : ℕ) → (Fin t → Bool) → ℝ
  Z : (t : ℕ) → (Fin t → Bool) → ℝ
  H_mem : ∀ t b, H t b ∈ Set.Icc (0 : ℝ) 1
  Z_mem : ∀ t b, Z t b ∈ Set.Icc (0 : ℝ) 1
  H_cons : ∀ t b, (H (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) +
      H (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)) / 2 = H t b
  T_contract : ∀ t b,
    (Real.sqrt (H (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) *
        (1 - H (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false))) +
      Real.sqrt (H (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) *
        (1 - H (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)))) / 2 ≤
    Lambda0 * Real.sqrt (H t b * (1 - H t b))
  Z_le_sqrt_H : ∀ t b, Z t b ≤ Real.sqrt (2 * Real.log 2 * H t b)
  Z_plus : ∀ t b, Z (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) = (Z t b) ^ 2
  Z_minus : ∀ t b, Z (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) ≤ 2 * Z t b

namespace PolarProcess

/-- Initial symmetric capacity `I(W) = 1 - H(W₀)`. -/
noncomputable def symCap (P : PolarProcess) : ℝ := 1 - P.H 0 Fin.elim0

lemma avg_H (P : PolarProcess) (t : ℕ) : treeAvg t (P.H t) = P.H 0 Fin.elim0 := by
  induction t with
  | zero => exact treeAvg_zero (P.H 0)
  | succ t ih =>
    rw [treeAvg_snoc, ← treeAvg_add]
    have hdiv : ∀ (g : (Fin t → Bool) → ℝ), treeAvg t g / 2 = treeAvg t (fun b ↦ g b / 2) := by
      intro g; unfold treeAvg; rw [← Finset.sum_div, div_div, div_div, mul_comm]
    rw [hdiv]
    have heq : (fun b ↦ (P.H (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) +
        P.H (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)) / 2) = P.H t := by
      ext b; exact P.H_cons t b
    rw [heq, ih]

lemma avg_T_le (P : PolarProcess) (t : ℕ) :
    treeAvg t (fun b ↦ Real.sqrt (P.H t b * (1 - P.H t b))) ≤
      Lambda0 ^ t * Real.sqrt (P.H 0 Fin.elim0 * (1 - P.H 0 Fin.elim0)) := by
  induction t with
  | zero =>
    rw [treeAvg_zero, pow_zero, one_mul]
  | succ t ih =>
    rw [treeAvg_snoc, ← treeAvg_add]
    have hdiv : ∀ (g : (Fin t → Bool) → ℝ), treeAvg t g / 2 = treeAvg t (fun b ↦ g b / 2) := by
      intro g; unfold treeAvg; rw [← Finset.sum_div, div_div, div_div, mul_comm]
    rw [hdiv]
    have hstep : treeAvg t (fun b ↦
        (Real.sqrt (P.H (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) *
            (1 - P.H (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false))) +
          Real.sqrt (P.H (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) *
            (1 - P.H (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)))) / 2) ≤
        Lambda0 * treeAvg t (fun b ↦ Real.sqrt (P.H t b * (1 - P.H t b))) := by
      rw [← treeAvg_mul_const]
      exact treeAvg_mono t (fun b ↦ P.T_contract t b)
    have hLnn : 0 ≤ Lambda0 := Real.sqrt_nonneg _
    calc _ ≤ Lambda0 * treeAvg t (fun b ↦ Real.sqrt (P.H t b * (1 - P.H t b))) := hstep
      _ ≤ Lambda0 * (Lambda0 ^ t * Real.sqrt (P.H 0 Fin.elim0 * (1 - P.H 0 Fin.elim0))) :=
          mul_le_mul_of_nonneg_left ih hLnn
      _ = Lambda0 ^ (t + 1) * Real.sqrt (P.H 0 Fin.elim0 * (1 - P.H 0 Fin.elim0)) := by
          rw [pow_succ']; ring

end PolarProcess

/-! ### Stage 1, 2, 3 Constants and Helpers -/

/-- Golden ratio `φ := (1 + √5) / 2`. -/
noncomputable def phiGold : ℝ := (1 + Real.sqrt 5) / 2

/-- Stage-2 contraction factor `γ₂ := (1/4 + √2) / 2 ≈ 0.832106 < 1`. -/
noncomputable def gamma2 : ℝ := (1 / 4 + Real.sqrt 2) / 2

/-- Stage-1 depth `m₁(ε) := ⌈(8 / log₂(1/Λ₀)) log₂(64/ε)⌉`. -/
noncomputable def stage1Depth (ε : ℝ) : ℕ :=
  Nat.ceil ((8 / Real.logb 2 (1 / Lambda0)) * Real.logb 2 (64 / ε))

/-- Stage-1 entropy threshold `η(ε) := Λ₀^(m₁(ε) / 2)`. -/
noncomputable def stage1Eta (ε : ℝ) : ℝ :=
  Lambda0 ^ ((stage1Depth ε : ℝ) / 2)

/-- Stage-1 fidelity threshold `Z₀(ε) := √((2 ln 2) η(ε))`. -/
noncomputable def stage1Z0 (ε : ℝ) : ℝ :=
  Real.sqrt (2 * Real.log 2 * stage1Eta ε)

/-- Stage-2 exponent threshold `Y₀(ε) := 200 + ⌈ln(16/ε) / ln φ⌉`. -/
noncomputable def stage2Y0 (ε : ℝ) : ℕ :=
  200 + Nat.ceil (Real.log (16 / ε) / Real.log phiGold)

/-- Stage-2 depth `m₂(ε) := ⌈(Y₀/2 + log₂(8/ε)) / log₂(1/γ₂)⌉`. -/
noncomputable def stage2Depth (ε : ℝ) : ℕ :=
  Nat.ceil (((stage2Y0 ε : ℝ) / 2 + Real.logb 2 (8 / ε)) / Real.logb 2 (1 / gamma2))

/-- Minimum Stage-3 depth `m₃,min(ε) := max(100 (m₁ + m₂), ⌈5 × 10⁵ ln(16/ε)⌉)`. -/
noncomputable def stage3MinDepth (ε : ℝ) : ℕ :=
  max (100 * (stage1Depth ε + stage2Depth ε)) (Nat.ceil (500000 * Real.log (16 / ε)))

lemma Lambda0_lt_one : Lambda0 < 1 := lt_trans Lambda0_lt (by norm_num)

lemma gamma2_pos : 0 < gamma2 := by
  unfold gamma2
  have : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  linarith

lemma gamma2_lt_one : gamma2 < 1 := by
  unfold gamma2
  have hsqrt2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

lemma phiGold_gt_one : 1 < phiGold := by
  unfold phiGold
  have hsqrt5 : (2 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

lemma phiGold_sq : phiGold ^ 2 = phiGold + 1 := by
  unfold phiGold
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma phiGold_add_inv_sq : phiGold + phiGold ^ (-2 : ℤ) = 2 := by
  have hpos : phiGold + 1 ≠ 0 := by linarith [phiGold_gt_one]
  rw [zpow_neg, zpow_two, ← sq, phiGold_sq]
  field_simp [hpos]
  nlinarith [phiGold_sq]

/-- Top-level stopped process helper: given a tree process `Z'` and a threshold `thr`,
`hitAbove Z' thr t b` holds iff `Z'` strictly exceeded `thr` at some step `s ≤ t`. -/
def hitAbove (Z' : (t : ℕ) → (Fin t → Bool) → ℝ) (thr : ℝ) (t : ℕ) (b : Fin t → Bool) : Prop :=
  ∃ s : Fin (t + 1), thr < Z' s.val (pathPrefix (Nat.le_of_lt_succ s.isLt) b)

/-- Top-level stopped transform `g(Z'_{t ∧ τ})` defined by recursion on `t`
(kept at top level to avoid `whnf` unfolding inside proofs). -/
noncomputable def stoppedTransform (Z' : (t : ℕ) → (Fin t → Bool) → ℝ) (thr : ℝ) (g : ℝ → ℝ) :
    (t : ℕ) → (Fin t → Bool) → ℝ
  | 0, _ => g (Z' 0 Fin.elim0)
  | t + 1, b => by
      classical
      exact if hitAbove Z' thr t (pathPrefix (Nat.le_succ t) b) then
        stoppedTransform Z' thr g t (pathPrefix (Nat.le_succ t) b)
      else g (Z' (t + 1) b)

lemma stoppedTransform_nonneg (Z' : (t : ℕ) → (Fin t → Bool) → ℝ) (thr : ℝ) (g : ℝ → ℝ)
    (hg : ∀ x, 0 ≤ g x) : ∀ t b, 0 ≤ stoppedTransform Z' thr g t b
  | 0, _ => hg _
  | t + 1, b => by
      simp only [stoppedTransform]; classical
      split_ifs
      · exact stoppedTransform_nonneg Z' thr g hg t _
      · exact hg _

lemma stoppedTransform_not_hit (Z' : (t : ℕ) → (Fin t → Bool) → ℝ) (thr : ℝ) (g : ℝ → ℝ) :
    ∀ t b, ¬ hitAbove Z' thr t b → stoppedTransform Z' thr g t b = g (Z' t b)
  | 0, b, _ => by
      have hb : b = Fin.elim0 := Subsingleton.elim b Fin.elim0
      subst hb; rfl
  | t + 1, b, hnot => by
      simp only [stoppedTransform]; classical
      have hnot_prev : ¬ hitAbove Z' thr t (pathPrefix (Nat.le_succ t) b) := by
        rintro ⟨s, hs⟩
        apply hnot
        refine ⟨s.castSucc, ?_⟩
        rw [pathPrefix_pathPrefix] at hs
        exact hs
      simp [hnot_prev]

lemma stoppedTransform_snoc_hit (Z' : (t : ℕ) → (Fin t → Bool) → ℝ) (thr : ℝ) (g : ℝ → ℝ)
    {t : ℕ} {b : Fin t → Bool} (hhit : hitAbove Z' thr t b) (a : Bool) :
    stoppedTransform Z' thr g (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b a) =
      stoppedTransform Z' thr g t b := by
  simp only [stoppedTransform]; classical
  simp [pathPrefix_snoc, hhit]

lemma stoppedTransform_snoc_not_hit (Z' : (t : ℕ) → (Fin t → Bool) → ℝ) (thr : ℝ) (g : ℝ → ℝ)
    {t : ℕ} {b : Fin t → Bool} (hnot : ¬ hitAbove Z' thr t b) (a : Bool) :
    stoppedTransform Z' thr g (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b a) =
      g (Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b a)) := by
  simp only [stoppedTransform]; classical
  simp [pathPrefix_snoc, hnot]

lemma hitAbove_snoc_of_hit (Z' : (t : ℕ) → (Fin t → Bool) → ℝ) (thr : ℝ)
    {t : ℕ} {b : Fin t → Bool} (hhit : hitAbove Z' thr t b) (a : Bool) :
    hitAbove Z' thr (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b a) := by
  rcases hhit with ⟨s, hs⟩
  refine ⟨s.castSucc, ?_⟩
  have hpre : pathPrefix (Nat.le_of_lt_succ s.castSucc.isLt) (Fin.snoc (α := fun _ ↦ Bool) b a) =
      pathPrefix (Nat.le_of_lt_succ s.isLt) b :=
    pathPrefix_snoc_le (Nat.le_of_lt_succ s.isLt) b a
  simpa [hpre] using hs

/-- If `Z'_0 ≤ thr` and `g` maps `(thr, ∞)` into `[c, ∞)`, then hitting `thr` up to time `m`
implies the stopped process `stoppedTransform Z' thr g` reaches `c` up to time `m`. -/
lemma hitAbove_imp_stoppedTransform_ge (Z' : (t : ℕ) → (Fin t → Bool) → ℝ) (thr c : ℝ) (g : ℝ → ℝ)
    (h0 : Z' 0 Fin.elim0 ≤ thr) (hg : ∀ x, thr < x → c ≤ g x)
    (m : ℕ) (b : Fin m → Bool) (hhit : hitAbove Z' thr m b) :
    ∃ t : Fin (m + 1), c ≤ stoppedTransform Z' thr g t.val (pathPrefix (Nat.le_of_lt_succ t.isLt) b) := by
  have hex : ∃ k : ℕ, ∃ hk : k ≤ m, thr < Z' k (pathPrefix hk b) := by
    rcases hhit with ⟨s, hs⟩
    exact ⟨s.val, Nat.le_of_lt_succ s.isLt, hs⟩
  classical
  let k₀ := Nat.find hex
  have hk₀ : ∃ hk : k₀ ≤ m, thr < Z' k₀ (pathPrefix hk b) := Nat.find_spec hex
  rcases hk₀ with ⟨hk₀_le, hk₀_gt⟩
  have hk₀_bound : c ≤ stoppedTransform Z' thr g k₀ (pathPrefix hk₀_le b) := by
    have hstep : ∀ (k : ℕ) (hk : k ≤ m), k = k₀ →
        thr < Z' k (pathPrefix hk b) → c ≤ stoppedTransform Z' thr g k (pathPrefix hk b) := by
      intro k hk hkeq hgt
      cases k with
      | zero =>
        exfalso
        have hpre0 : pathPrefix hk b = Fin.elim0 := by ext i; exact Fin.elim0 i
        rw [hpre0] at hgt
        linarith
      | succ k' =>
        have hnot_prev : ¬ hitAbove Z' thr k' (pathPrefix (Nat.le_of_succ_le hk) b) := by
          rintro ⟨s, hs⟩
          have hs_lt : s.val < k₀ := by omega
          have hmin := Nat.find_min hex hs_lt
          apply hmin
          refine ⟨le_trans (Nat.le_of_lt_succ s.isLt) (Nat.le_of_succ_le hk), ?_⟩
          rw [pathPrefix_pathPrefix] at hs
          exact hs
        have hMeq : stoppedTransform Z' thr g (k' + 1) (pathPrefix hk b) =
            g (Z' (k' + 1) (pathPrefix hk b)) := by
          simp only [stoppedTransform]; classical
          rw [pathPrefix_pathPrefix]
          simp [hnot_prev]
        rw [hMeq]
        exact hg _ hgt
    exact hstep k₀ hk₀_le rfl hk₀_gt
  exact ⟨⟨k₀, Nat.lt_succ_of_le hk₀_le⟩, hk₀_bound⟩

/-! ### Lemma 5.2: Stage 1 (Rough Polarization) -/

/-- **Lemma 5.2 (Stage 1: Rough Polarization)**:
For `ε ∈ (0, 1)`, `P(H(W_{m₁}) ≤ η) ≥ I(W) - ε / 4`, and on `E₁`,
`Z(W_{m₁}) ≤ Z₀ < 1/16` and `4 √Z₀ < ε / 8`. -/
theorem lemma_5_2_stage1 (P : PolarProcess) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    P.symCap - ε / 4 ≤ treeProb (stage1Depth ε) (fun b ↦ P.H (stage1Depth ε) b ≤ stage1Eta ε) ∧
    (∀ b, P.H (stage1Depth ε) b ≤ stage1Eta ε → P.Z (stage1Depth ε) b ≤ stage1Z0 ε) ∧
    stage1Z0 ε < 1 / 16 ∧
    4 * Real.sqrt (stage1Z0 ε) < ε / 8 := by
  set m₁ := stage1Depth ε
  set η := stage1Eta ε
  set Z₀ := stage1Z0 ε
  have hL0 : 0 < Lambda0 := Lambda0_pos
  have hL1 : Lambda0 < 1 := Lambda0_lt_one
  have hlogL : 0 < Real.logb 2 (1 / Lambda0) :=
    Real.logb_pos (by norm_num) ((one_lt_div hL0).mpr hL1)
  have hm₁_ge : (8 / Real.logb 2 (1 / Lambda0)) * Real.logb 2 (64 / ε) ≤ (m₁ : ℝ) :=
    Nat.le_ceil _
  have hη_pos : 0 < η := Real.rpow_pos_of_pos hL0 _
  have hη_le : η ≤ (ε / 64) ^ 4 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : Real.logb 2 η ≤ Real.logb 2 ((ε / 64) ^ 4) := by
      have hLHS : Real.logb 2 η = -((m₁ : ℝ) / 2) * Real.logb 2 (1 / Lambda0) := by
        simp only [η, stage1Eta]
        rw [Real.logb_rpow_eq_mul_logb_of_pos hL0, one_div, Real.logb_inv]
        ring
      have hRHS : Real.logb 2 ((ε / 64) ^ 4) = -4 * Real.logb 2 (64 / ε) := by
        rw [Real.logb_pow, show ε / 64 = (64 / ε)⁻¹ by field_simp [ne_of_gt hε0], Real.logb_inv]
        ring
      rw [hLHS, hRHS]
      have hmul := mul_le_mul_of_nonneg_right hm₁_ge (le_of_lt hlogL)
      have hsimp : (8 / Real.logb 2 (1 / Lambda0)) * Real.logb 2 (64 / ε) *
          Real.logb 2 (1 / Lambda0) = 8 * Real.logb 2 (64 / ε) := by
        field_simp [ne_of_gt hlogL]
      linarith
    rw [Real.logb, Real.logb, div_le_div_iff_of_pos_right hlog2] at h1
    exact (Real.log_le_log_iff hη_pos (by positivity)).mp h1
  have hη_lt_quarter : η < 1 / 4 := by
    have hpow : (ε / 64) ^ 4 ≤ (1 / 64 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    norm_num at hpow
    linarith
  have hmid : treeProb m₁ (fun b ↦ η < P.H m₁ b ∧ P.H m₁ b < 1 - η) ≤ η := by
    have havgT : treeAvg m₁ (fun b ↦ Real.sqrt (P.H m₁ b * (1 - P.H m₁ b))) ≤
        (1 / 2) * Lambda0 ^ m₁ := by
      have h1 := P.avg_T_le m₁
      have hT0 : Real.sqrt (P.H 0 Fin.elim0 * (1 - P.H 0 Fin.elim0)) ≤ 1 / 2 := by
        have hsq : P.H 0 Fin.elim0 * (1 - P.H 0 Fin.elim0) ≤ (1 / 2) ^ 2 := by
          nlinarith [sq_nonneg (P.H 0 Fin.elim0 - 1 / 2)]
        calc Real.sqrt (P.H 0 Fin.elim0 * (1 - P.H 0 Fin.elim0))
            ≤ Real.sqrt ((1 / 2) ^ 2) := Real.sqrt_le_sqrt hsq
          _ = 1 / 2 := Real.sqrt_sq (by norm_num)
      have hpow_nn : 0 ≤ Lambda0 ^ m₁ := pow_nonneg (le_of_lt hL0) m₁
      nlinarith
    have hc_pos : 0 < Real.sqrt ((3 / 4) * η) := Real.sqrt_pos.mpr (by linarith)
    have hmarkov := treeProb_markov m₁
      (f := fun b ↦ Real.sqrt (P.H m₁ b * (1 - P.H m₁ b)))
      (fun _ ↦ Real.sqrt_nonneg _)
      hc_pos
      (P := fun b ↦ η < P.H m₁ b ∧ P.H m₁ b < 1 - η)
      (fun b ⟨hb1, hb2⟩ ↦ by
        apply Real.sqrt_le_sqrt
        have h1 : η * (1 - η) ≤ P.H m₁ b * (1 - P.H m₁ b) := by nlinarith
        nlinarith)
    have hη_sq : η ^ 2 = Lambda0 ^ m₁ := by
      simp only [η, stage1Eta]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hL0)]
      have : ((m₁ : ℝ) / 2) * (2 : ℕ) = (m₁ : ℝ) := by push_cast; ring
      rw [this, Real.rpow_natCast]
    have hsqrt_ge : (1 / 2) * η ≤ Real.sqrt ((3 / 4) * η) := by
      rw [← Real.sqrt_sq (show 0 ≤ (1 / 2) * η by linarith)]
      apply Real.sqrt_le_sqrt
      nlinarith
    calc treeProb m₁ (fun b ↦ η < P.H m₁ b ∧ P.H m₁ b < 1 - η)
        ≤ treeAvg m₁ (fun b ↦ Real.sqrt (P.H m₁ b * (1 - P.H m₁ b))) /
            Real.sqrt ((3 / 4) * η) := hmarkov
      _ ≤ ((1 / 2) * Lambda0 ^ m₁) / Real.sqrt ((3 / 4) * η) :=
          div_le_div_of_nonneg_right havgT (le_of_lt hc_pos)
      _ ≤ ((1 / 2) * Lambda0 ^ m₁) / ((1 / 2) * η) :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) hsqrt_ge
      _ = η := by
          rw [← hη_sq]
          have hηne : η ≠ 0 := ne_of_gt hη_pos
          field_simp [hηne]
  have hI_le : P.symCap ≤
      treeProb m₁ (fun b ↦ P.H m₁ b ≤ η) +
        treeProb m₁ (fun b ↦ η < P.H m₁ b ∧ P.H m₁ b < 1 - η) + η := by
    have hcap : P.symCap = treeAvg m₁ (fun b ↦ 1 - P.H m₁ b) := by
      rw [treeAvg_sub, treeAvg_const, P.avg_H]; rfl
    have hmono : treeAvg m₁ (fun b ↦ 1 - P.H m₁ b) ≤
        treeAvg m₁ (fun b ↦
          (ind (P.H m₁ b ≤ η) + ind (η < P.H m₁ b ∧ P.H m₁ b < 1 - η)) + η) := by
      apply treeAvg_mono
      intro b
      have hH := P.H_mem m₁ b
      by_cases h1 : P.H m₁ b ≤ η
      · rw [ind_pos h1, ind_neg (by linarith)]; linarith [hH.1, hη_pos]
      · by_cases h2 : P.H m₁ b < 1 - η
        · rw [ind_neg h1, ind_pos ⟨lt_of_not_ge h1, h2⟩]; linarith [hH.1, hη_pos]
        · rw [ind_neg h1, ind_neg (fun h ↦ h2 h.2)]; linarith
    rw [treeAvg_add, treeAvg_add, treeAvg_const] at hmono
    exact hcap.symm ▸ hmono
  have h2η : 2 * η ≤ ε / 4 := by
    have h3 : (ε / 64) ^ 3 ≤ (1 / 64 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    have h4 : (ε / 64) ^ 4 = (ε / 64) * (ε / 64) ^ 3 := by ring
    norm_num at h3
    nlinarith
  have hlog2_lt : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hZ0_le : Z₀ ≤ 2 * (ε / 64) ^ 2 := by
    simp only [Z₀, stage1Z0]
    have harg : 2 * Real.log 2 * η ≤ (2 * (ε / 64) ^ 2) ^ 2 := by
      have h1 : 2 * Real.log 2 * η ≤ 2 * η := by nlinarith
      have hnn : 0 ≤ (ε / 64) ^ 4 := by positivity
      have hsq : (2 * (ε / 64) ^ 2) ^ 2 = 4 * (ε / 64) ^ 4 := by ring
      linarith
    calc Real.sqrt (2 * Real.log 2 * η)
        ≤ Real.sqrt ((2 * (ε / 64) ^ 2) ^ 2) := Real.sqrt_le_sqrt harg
      _ = 2 * (ε / 64) ^ 2 := Real.sqrt_sq (by positivity)
  have hZ0_lt : Z₀ < 1 / 16 := by
    have : 2 * (ε / 64) ^ 2 < 1 / 16 := by nlinarith
    linarith
  have h4sqrtZ0 : 4 * Real.sqrt Z₀ < ε / 8 := by
    have hstrict : Real.sqrt Z₀ < 2 * (ε / 64) := by
      have harg : Z₀ < (2 * (ε / 64)) ^ 2 := by
        have hpos2 : 0 < (ε / 64) ^ 2 := by positivity
        have hsq : (2 * (ε / 64)) ^ 2 = 4 * (ε / 64) ^ 2 := by ring
        linarith
      rw [Real.sqrt_lt' (by positivity)]
      exact harg
    linarith
  refine ⟨by linarith, ?_, hZ0_lt, h4sqrtZ0⟩
  intro b hb
  exact le_trans (P.Z_le_sqrt_H m₁ b) (Real.sqrt_le_sqrt (by nlinarith))

/-! ### Lemma 5.3: Stage 2 (Bootstrap Polarization) -/

/-- **Lemma 5.3 (Stage 2: Bootstrap Polarization)**:
For every `ε ∈ (0, 1)` and every Stage-1 path `w` with `Z(w) ≤ Z₀`,
the conditional probability that `Z(W_{m₁ + m₂}) ≤ 2^(-Y₀)` given `w` is at least `1 - ε / 4`. -/
theorem lemma_5_3_stage2 (P : PolarProcess) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (w : Fin (stage1Depth ε) → Bool) (hw : P.Z (stage1Depth ε) w ≤ stage1Z0 ε) :
    1 - ε / 4 ≤ treeProb (stage2Depth ε)
      (fun b ↦ P.Z (stage1Depth ε + stage2Depth ε) (Fin.append w b) ≤
        (2 : ℝ) ^ (-(stage2Y0 ε : ℝ))) := by
  let m₁ := stage1Depth ε
  set m₂ := stage2Depth ε
  set Y₀ := stage2Y0 ε
  set Z₀ := stage1Z0 ε
  have ⟨_, _, hZ0_lt, h4sqrtZ0⟩ := lemma_5_2_stage1 P hε0 hε1
  let Z' : (t : ℕ) → (Fin t → Bool) → ℝ := fun t b ↦ P.Z (m₁ + t) (Fin.append w b)
  have hZ'_nn : ∀ t b, 0 ≤ Z' t b := fun t b ↦ (P.Z_mem (m₁ + t) (Fin.append w b)).1
  have hZ'_plus : ∀ (t : ℕ) (b : Fin t → Bool),
      Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) = (Z' t b) ^ 2 := by
    intro t b
    change P.Z (m₁ + (t + 1)) (Fin.append w (Fin.snoc (α := fun _ ↦ Bool) b true)) = _
    rw [← fin_append_snoc]
    exact P.Z_plus (m₁ + t) (Fin.append w b)
  have hZ'_minus : ∀ (t : ℕ) (b : Fin t → Bool),
      Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) ≤ 2 * Z' t b := by
    intro t b
    change P.Z (m₁ + (t + 1)) (Fin.append w (Fin.snoc (α := fun _ ↦ Bool) b false)) ≤ _
    rw [← fin_append_snoc]
    exact P.Z_minus (m₁ + t) (Fin.append w b)
  have hZ'0 : Z' 0 Fin.elim0 = P.Z m₁ w := by
    simp only [Z']
    congr 1; ext i; simp [Fin.append, Fin.addCases]; rfl
  let M := stoppedTransform Z' (1 / 16) Real.sqrt
  have hM_nn : ∀ t b, 0 ≤ M t b := stoppedTransform_nonneg Z' (1 / 16) Real.sqrt Real.sqrt_nonneg
  have hM_step_not_hit : ∀ t b, ¬ hitAbove Z' (1 / 16) t b →
      (M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) +
        M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)) / 2 ≤ gamma2 * M t b := by
    intro t b hnot
    have hZle : Z' t b ≤ 1 / 16 := by
      by_contra hgt
      apply hnot
      refine ⟨Fin.last t, ?_⟩
      have hpre : pathPrefix (Nat.le_of_lt_succ (Fin.last t).isLt) b = b := by ext i; rfl
      simpa [hpre] using lt_of_not_ge hgt
    rw [stoppedTransform_snoc_not_hit Z' (1 / 16) Real.sqrt hnot false,
        stoppedTransform_snoc_not_hit Z' (1 / 16) Real.sqrt hnot true,
        stoppedTransform_not_hit Z' (1 / 16) Real.sqrt t b hnot, hZ'_plus]
    rw [Real.sqrt_sq (hZ'_nn t b)]
    have h1 : Z' t b ≤ (1 / 4) * Real.sqrt (Z' t b) := by
      have hs : Real.sqrt (Z' t b) ≤ 1 / 4 := by
        calc Real.sqrt (Z' t b) ≤ Real.sqrt ((1 / 4) ^ 2) := Real.sqrt_le_sqrt (by linarith)
          _ = 1 / 4 := Real.sqrt_sq (by norm_num)
      have hsq : Real.sqrt (Z' t b) * Real.sqrt (Z' t b) = Z' t b :=
        Real.mul_self_sqrt (hZ'_nn t b)
      nlinarith [Real.sqrt_nonneg (Z' t b)]
    have h2 : Real.sqrt (Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false)) ≤
        Real.sqrt 2 * Real.sqrt (Z' t b) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (hZ'_minus t b)
    unfold gamma2
    linarith
  have hM_super : ∀ t b,
      (M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) +
        M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)) / 2 ≤ M t b := by
    intro t b
    by_cases hhit : hitAbove Z' (1 / 16) t b
    · rw [stoppedTransform_snoc_hit Z' (1 / 16) Real.sqrt hhit false,
          stoppedTransform_snoc_hit Z' (1 / 16) Real.sqrt hhit true]
      linarith
    · have h1 := hM_step_not_hit t b hhit
      have h2 := gamma2_lt_one
      have h3 := hM_nn t b
      nlinarith
  have hprob_hit : treeProb m₂ (hitAbove Z' (1 / 16) m₂) < ε / 8 := by
    have hdoob := tree_doob_maximal m₂ (fun t _ b ↦ M t b) (fun t _ b ↦ hM_nn t b)
      (fun t _ b ↦ hM_super t b) (1 / 4) (by norm_num)
    have hsub : treeProb m₂ (hitAbove Z' (1 / 16) m₂) ≤
        treeProb m₂ (fun b ↦ ∃ t : Fin (m₂ + 1),
          (1 / 4 : ℝ) ≤ M t.val (pathPrefix (Nat.le_of_lt_succ t.isLt) b)) := by
      apply treeProb_mono
      intro b hhit
      exact hitAbove_imp_stoppedTransform_ge Z' (1 / 16) (1 / 4) Real.sqrt
        (by rw [hZ'0]; linarith)
        (fun x hx ↦ by
          calc (1 / 4 : ℝ) = Real.sqrt ((1 / 4) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
            _ ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith))
        m₂ b hhit
    have hM0_le : M 0 Fin.elim0 / (1 / 4) ≤ 4 * Real.sqrt Z₀ := by
      have hM0 : M 0 Fin.elim0 = Real.sqrt (P.Z m₁ w) := by simp [M, stoppedTransform, hZ'0]
      rw [hM0]
      have hsq : Real.sqrt (P.Z m₁ w) ≤ Real.sqrt Z₀ := Real.sqrt_le_sqrt hw
      linarith
    linarith only [hsub, hdoob, hM0_le, h4sqrtZ0]
  have hdecay : ∀ t : ℕ,
      treeAvg t (fun b ↦ ind (¬ hitAbove Z' (1 / 16) t b) * M t b) ≤
        gamma2 ^ t * Real.sqrt Z₀ := by
    intro t
    induction t with
    | zero =>
      rw [treeAvg_zero, pow_zero, one_mul]
      have hM0 : M 0 Fin.elim0 = Real.sqrt (P.Z m₁ w) := by simp [M, stoppedTransform, hZ'0]
      rw [hM0]
      have hle1 : ind (¬ hitAbove Z' (1 / 16) 0 Fin.elim0) ≤ 1 := ind_le_one _
      have hsq : Real.sqrt (P.Z m₁ w) ≤ Real.sqrt Z₀ := Real.sqrt_le_sqrt hw
      nlinarith [Real.sqrt_nonneg (P.Z m₁ w)]
    | succ t ih =>
      rw [treeAvg_snoc, ← treeAvg_add]
      have hdiv : ∀ (g : (Fin t → Bool) → ℝ), treeAvg t g / 2 = treeAvg t (fun b ↦ g b / 2) := by
        intro g; unfold treeAvg; rw [← Finset.sum_div, div_div, div_div, mul_comm]
      rw [hdiv]
      have hstep : treeAvg t (fun b ↦
          (ind (¬ hitAbove Z' (1 / 16) (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false)) *
              M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) +
           ind (¬ hitAbove Z' (1 / 16) (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)) *
              M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)) / 2) ≤
          gamma2 * treeAvg t (fun b ↦ ind (¬ hitAbove Z' (1 / 16) t b) * M t b) := by
        rw [← treeAvg_mul_const]
        apply treeAvg_mono
        intro b
        by_cases hhit : hitAbove Z' (1 / 16) t b
        · have hf := hitAbove_snoc_of_hit Z' (1 / 16) hhit false
          have ht := hitAbove_snoc_of_hit Z' (1 / 16) hhit true
          rw [ind_neg (not_not.mpr hhit), ind_neg (not_not.mpr hf), ind_neg (not_not.mpr ht)]
          ring_nf; exact le_rfl
        · rw [ind_pos hhit, one_mul]
          have h1 : ind (¬ hitAbove Z' (1 / 16) (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false)) *
              M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) ≤
              M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) := by
            have := ind_le_one (¬ hitAbove Z' (1 / 16) (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false))
            nlinarith [hM_nn (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false)]
          have h2 : ind (¬ hitAbove Z' (1 / 16) (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)) *
              M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) ≤
              M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) := by
            have := ind_le_one (¬ hitAbove Z' (1 / 16) (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true))
            nlinarith [hM_nn (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)]
          linarith only [h1, h2, hM_step_not_hit t b hhit]
      calc _ ≤ gamma2 * treeAvg t (fun b ↦ ind (¬ hitAbove Z' (1 / 16) t b) * M t b) := hstep
        _ ≤ gamma2 * (gamma2 ^ t * Real.sqrt Z₀) :=
              mul_le_mul_of_nonneg_left ih (le_of_lt gamma2_pos)
        _ = gamma2 ^ (t + 1) * Real.sqrt Z₀ := by rw [pow_succ']; ring
  have hprob_tail : treeProb m₂ (fun b ↦ ¬ hitAbove Z' (1 / 16) m₂ b ∧
      (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b) ≤ ε / 8 := by
    have hc_pos : 0 < (2 : ℝ) ^ (-(Y₀ : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have hmarkov := treeProb_markov m₂
      (f := fun b ↦ ind (¬ hitAbove Z' (1 / 16) m₂ b) * M m₂ b)
      (fun b ↦ mul_nonneg (ind_nonneg _) (hM_nn m₂ b))
      hc_pos
      (P := fun b ↦ ¬ hitAbove Z' (1 / 16) m₂ b ∧ (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b)
      (fun b ⟨hnot, hgt⟩ ↦ by
        rw [ind_pos hnot, one_mul, stoppedTransform_not_hit Z' (1 / 16) Real.sqrt m₂ b hnot]
        have hsq : ((2 : ℝ) ^ (-(Y₀ : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ (-(Y₀ : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1; push_cast; ring
        calc (2 : ℝ) ^ (-(Y₀ : ℝ) / 2)
            = Real.sqrt (((2 : ℝ) ^ (-(Y₀ : ℝ) / 2)) ^ 2) :=
                (Real.sqrt_sq (le_of_lt hc_pos)).symm
          _ = Real.sqrt ((2 : ℝ) ^ (-(Y₀ : ℝ))) := by rw [hsq]
          _ ≤ Real.sqrt (Z' m₂ b) := Real.sqrt_le_sqrt (le_of_lt hgt))
    have hsqrtZ0_le : Real.sqrt Z₀ ≤ 1 := by
      calc Real.sqrt Z₀ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
        _ = 1 := Real.sqrt_one
    have hγ_bound : gamma2 ^ m₂ * (2 : ℝ) ^ ((Y₀ : ℝ) / 2) ≤ ε / 8 := by
      have hlogg : 0 < Real.logb 2 (1 / gamma2) :=
        Real.logb_pos (by norm_num) ((one_lt_div gamma2_pos).mpr gamma2_lt_one)
      have hm₂_ge : ((Y₀ : ℝ) / 2 + Real.logb 2 (8 / ε)) / Real.logb 2 (1 / gamma2) ≤ (m₂ : ℝ) :=
        Nat.le_ceil _
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hprod_pos : 0 < gamma2 ^ m₂ * (2 : ℝ) ^ ((Y₀ : ℝ) / 2) :=
        mul_pos (pow_pos gamma2_pos m₂) (Real.rpow_pos_of_pos (by norm_num) _)
      have hlog_le : Real.logb 2 (gamma2 ^ m₂ * (2 : ℝ) ^ ((Y₀ : ℝ) / 2)) ≤
          Real.logb 2 (ε / 8) := by
        rw [Real.logb_mul (ne_of_gt (pow_pos gamma2_pos m₂))
            (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)),
          Real.logb_pow, Real.logb_rpow (by norm_num) (by norm_num)]
        have hinv : Real.logb 2 gamma2 = -Real.logb 2 (1 / gamma2) := by
          rw [one_div, Real.logb_inv, neg_neg]
        have hrhs : Real.logb 2 (ε / 8) = -Real.logb 2 (8 / ε) := by
          rw [show ε / 8 = (8 / ε)⁻¹ by field_simp [ne_of_gt hε0], Real.logb_inv]
        rw [hinv, hrhs]
        have hmul := mul_le_mul_of_nonneg_right hm₂_ge (le_of_lt hlogg)
        have hsimp : ((Y₀ : ℝ) / 2 + Real.logb 2 (8 / ε)) / Real.logb 2 (1 / gamma2) *
            Real.logb 2 (1 / gamma2) = (Y₀ : ℝ) / 2 + Real.logb 2 (8 / ε) := by
          field_simp [ne_of_gt hlogg]
        linarith
      rw [Real.logb, Real.logb, div_le_div_iff_of_pos_right hlog2] at hlog_le
      exact (Real.log_le_log_iff hprod_pos (by positivity)).mp hlog_le
    calc treeProb m₂ (fun b ↦ ¬ hitAbove Z' (1 / 16) m₂ b ∧ (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b)
        ≤ treeAvg m₂ (fun b ↦ ind (¬ hitAbove Z' (1 / 16) m₂ b) * M m₂ b) /
            (2 : ℝ) ^ (-(Y₀ : ℝ) / 2) := hmarkov
      _ ≤ (gamma2 ^ m₂ * Real.sqrt Z₀) / (2 : ℝ) ^ (-(Y₀ : ℝ) / 2) :=
          div_le_div_of_nonneg_right (hdecay m₂) (le_of_lt hc_pos)
      _ ≤ (gamma2 ^ m₂ * 1) / (2 : ℝ) ^ (-(Y₀ : ℝ) / 2) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hc_pos)
          exact mul_le_mul_of_nonneg_left hsqrtZ0_le (pow_nonneg (le_of_lt gamma2_pos) m₂)
      _ = gamma2 ^ m₂ * (2 : ℝ) ^ ((Y₀ : ℝ) / 2) := by
          rw [mul_one, div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          congr 2; ring
      _ ≤ ε / 8 := hγ_bound
  have hbad : treeProb m₂ (fun b ↦ (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b) ≤ ε / 4 := by
    have hsub : treeProb m₂ (fun b ↦ (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b) ≤
        treeProb m₂ (fun b ↦ hitAbove Z' (1 / 16) m₂ b ∨
          (¬ hitAbove Z' (1 / 16) m₂ b ∧ (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b)) := by
      apply treeProb_mono
      intro b hgt
      by_cases h : hitAbove Z' (1 / 16) m₂ b
      · exact Or.inl h
      · exact Or.inr ⟨h, hgt⟩
    have hunion := treeProb_union m₂ (hitAbove Z' (1 / 16) m₂)
      (fun b ↦ ¬ hitAbove Z' (1 / 16) m₂ b ∧ (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b)
    linarith only [hsub, hunion, hprob_hit, hprob_tail]
  have hcompl := treeProb_compl m₂ (fun b ↦ Z' m₂ b ≤ (2 : ℝ) ^ (-(Y₀ : ℝ)))
  have heq : treeProb m₂ (fun b ↦ ¬ (Z' m₂ b ≤ (2 : ℝ) ^ (-(Y₀ : ℝ)))) =
      treeProb m₂ (fun b ↦ (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b) :=
    treeProb_congr m₂ (fun _ ↦ not_le)
  rw [heq] at hcompl
  linarith only [hbad, hcompl]

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
  congr 1; push_cast; ring

lemma stage3_exponent_ineq :
    (495376 / 1000000 : ℝ) * Real.log 2 ≤
      (499 / 1000 : ℝ) * Real.log 2 + (501 / 1000 : ℝ) * Real.log (199 / 200) := by
  have hlog2 := Real.log_two_gt_d9
  have h199 : (199 / 200 : ℝ) = 1 - 1 / 200 := by norm_num
  rw [h199]
  have hlb := log_one_sub_ge (x := 1 / 200) (by norm_num) (by norm_num)
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
  let N := stoppedTransform Z' thr phiPot
  have hN_nn : ∀ t b, 0 ≤ N t b := stoppedTransform_nonneg Z' thr phiPot phiPot_nonneg
  have hN_super : ∀ t b,
      (N (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) +
        N (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)) / 2 ≤ N t b := by
    intro t b
    by_cases hhit : hitAbove Z' thr t b
    · rw [stoppedTransform_snoc_hit Z' thr phiPot hhit false,
          stoppedTransform_snoc_hit Z' thr phiPot hhit true]
      linarith
    · have hZle : Z' t b ≤ thr := by
        by_contra hgt
        apply hhit
        refine ⟨Fin.last t, ?_⟩
        have hpre : pathPrefix (Nat.le_of_lt_succ (Fin.last t).isLt) b = b := by ext i; rfl
        simpa [hpre] using lt_of_not_ge hgt
      rw [stoppedTransform_snoc_not_hit Z' thr phiPot hhit false,
          stoppedTransform_snoc_not_hit Z' thr phiPot hhit true,
          stoppedTransform_not_hit Z' thr phiPot t b hhit, hZ'_plus]
      by_cases hz0 : Z' t b = 0
      · have hzm : Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) = 0 :=
          le_antisymm (by linarith [hZ'_minus t b, hz0]) (hZ'_nn _ _)
        simp [phiPot, hz0, hzm]
      · have hzpos : 0 < Z' t b := lt_of_le_of_ne (hZ'_nn t b) (Ne.symm hz0)
        have hφ : 0 < phiGold := by linarith [phiGold_gt_one]
        have hminus_le : phiPot (Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false)) ≤
            phiGold * phiPot (Z' t b) := by
          calc phiPot (Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false))
              ≤ phiPot (2 * Z' t b) := phiPot_mono (hZ'_nn _ _) (hZ'_minus t b)
            _ = phiGold * phiPot (Z' t b) := by
                unfold phiPot
                rw [if_neg (not_le.mpr (by positivity)), if_neg (not_le.mpr hzpos),
                  Real.mul_rpow (by norm_num) (le_of_lt hzpos), two_rpow_alphaGold]
                ring
        have hthr_le : thr ≤ 1 / 4 := by
          simp only [thr]
          calc (2 : ℝ) ^ (-(200 : ℝ)) ≤ (2 : ℝ) ^ (-(2 : ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 1 / 4 := by norm_num
        have hplus_le : phiPot ((Z' t b) ^ 2) ≤ phiGold ^ (-2 : ℤ) * phiPot (Z' t b) := by
          have hsq_le : (Z' t b) ^ 2 ≤ (1 / 4) * Z' t b := by nlinarith
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
    linarith only [hsub, hdoob, hN0_le]
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
  have hgood_imp : ∀ b : Fin m₃ → Bool,
      ¬ hitAbove Z' thr m₃ b →
      (499 / 1000 : ℝ) * m₃ ≤ (∑ i : Fin m₃, if b i then (1 : ℝ) else 0) →
      Z' m₃ b ≤ (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ (m₁₂ + m₃)) ^ (49047 / 100000 : ℝ)) := by
    intro b hnot hS
    by_cases hz0 : Z' m₃ b = 0
    · rw [hz0]; exact Real.rpow_nonneg (by norm_num) _
    · have hpos_all : ∀ (t : ℕ) (ht : t ≤ m₃), 0 < Z' t (pathPrefix ht b) := by
        intro t ht
        by_contra hle
        have hz_t : Z' t (pathPrefix ht b) = 0 :=
          le_antisymm (not_lt.mp hle) (hZ'_nn t _)
        have hzero_fwd : ∀ k (hk : t + k ≤ m₃), Z' (t + k) (pathPrefix hk b) = 0 := by
          intro k
          induction k with
          | zero => intro hk; simpa using hz_t
          | succ k ih =>
            intro hk
            have hk' : t + k ≤ m₃ := Nat.le_of_succ_le hk
            have hprev := ih hk'
            have hsnoc_eq : pathPrefix hk b =
                Fin.snoc (α := fun _ ↦ Bool) (pathPrefix hk' b) (b ⟨t + k, hk⟩) := by
              ext i
              refine Fin.lastCases ?_ ?_ i
              · simp [pathPrefix, Fin.snoc_last]
              · intro j; simp [pathPrefix, Fin.snoc_castSucc]
            rw [hsnoc_eq]
            cases hb : b ⟨t + k, hk⟩
            · exact le_antisymm (by linarith [hZ'_minus (t + k) (pathPrefix hk' b), hprev])
                (hZ'_nn _ _)
            · rw [hZ'_plus, hprev]; norm_num
        have hfinal := hzero_fwd (m₃ - t) (by omega)
        have hm3eq : t + (m₃ - t) = m₃ := Nat.add_sub_of_le ht
        have hpref_m3 : Z' m₃ b = 0 := by
          have : pathPrefix (le_refl m₃) b = b := by ext i; rfl
          simpa [hm3eq, this] using hfinal
        exact hz0 hpref_m3
      have hle_all : ∀ (t : ℕ) (ht : t ≤ m₃), Z' t (pathPrefix ht b) ≤ thr := by
        intro t ht
        by_contra hgt
        exact hnot ⟨⟨t, Nat.lt_succ_of_le ht⟩, lt_of_not_ge hgt⟩
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
          have hlogthr : Real.logb 2 thr = -200 := by
            simp only [thr, Real.logb_rpow (by norm_num) (by norm_num)]
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
            have hlogthr : Real.logb 2 thr = -200 := by
              simp only [thr, Real.logb_rpow (by norm_num) (by norm_num)]
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
          · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, Nat.cast_add, Nat.cast_one]
            have hlog_step : -Real.logb 2 (Z' t (pathPrefix ht' b)) - 1 ≤
                -Real.logb 2 (Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) (pathPrefix ht' b) false)) := by
              have hpos_next := hpos_all (t + 1) ht
              rw [hsnoc_eq, hb] at hpos_next
              have hpos_prev := hpos_all t ht'
              have hle := hZ'_minus t (pathPrefix ht' b)
              have hlog := Real.logb_le_logb_of_le (by norm_num) hpos_next hle
              rw [Real.logb_mul (by norm_num) (ne_of_gt hpos_prev), Real.logb_self_eq_one (by norm_num)] at hlog
              linarith
            have hscale : (199 / 200 : ℝ) * (-Real.logb 2 (Z' t (pathPrefix ht' b))) ≤
                -Real.logb 2 (Z' t (pathPrefix ht' b)) - 1 := by linarith
            have hexp : ((t : ℝ) + 1 - St) = ((t : ℝ) - St) + 1 := by ring
            rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 199 / 200), Real.rpow_one]
            nlinarith
          · simp only [↓reduceIte, Nat.cast_add, Nat.cast_one]
            have hsub_eq : (t : ℝ) + 1 - (St + 1) = (t : ℝ) - St := by ring
            rw [hsub_eq, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, hZ'_plus]
            rw [Real.logb_pow]
            push_cast
            linarith
      have hYm3 := hY_ind m₃ le_rfl
      have hpre_id : pathPrefix (le_refl m₃) b = b := by ext i; rfl
      rw [hpre_id] at hYm3
      set S : ℝ := ∑ i : Fin m₃, if b i then (1 : ℝ) else 0
      have hS_eq : (∑ i : Fin m₃, if b ⟨i.val, lt_of_lt_of_le i.isLt le_rfl⟩ then (1 : ℝ) else 0) = S := rfl
      rw [hS_eq] at hYm3
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

end PolarCodes
