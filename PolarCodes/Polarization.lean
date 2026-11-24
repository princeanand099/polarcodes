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

/-- Uniform expectation of `f : (Fin n → Bool) → ℝ` over the `2^n` binary paths. -/
noncomputable def treeAvg (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ b : Fin n → Bool, f b) / (2 : ℝ) ^ n

/-- Uniform probability of an event `P` on `Fin n → Bool`. -/
noncomputable def treeProb (n : ℕ) (P : (Fin n → Bool) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (2 : ℝ) ^ n

lemma treeProb_eq_avg (n : ℕ) (P : (Fin n → Bool) → Prop) :
    treeProb n P = treeAvg n (fun b ↦ by classical exact if P b then (1 : ℝ) else 0) := by
  classical
  unfold treeProb treeAvg
  rw [Finset.sum_boole]

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
      = treeAvg n (fun b ↦ by classical exact if P b then (1 : ℝ) else 0) := treeProb_eq_avg n P
    _ ≤ treeAvg n (fun _ ↦ 1) := treeAvg_mono n (fun b ↦ by classical split_ifs <;> norm_num)
    _ = 1 := treeAvg_const n 1

lemma treeProb_nonneg (n : ℕ) (P : (Fin n → Bool) → Prop) : 0 ≤ treeProb n P := by
  rw [treeProb_eq_avg]
  exact treeAvg_nonneg n (fun b ↦ by classical split_ifs <;> norm_num)

lemma treeProb_mono (n : ℕ) {P Q : (Fin n → Bool) → Prop} (h : ∀ b, P b → Q b) :
    treeProb n P ≤ treeProb n Q := by
  rw [treeProb_eq_avg, treeProb_eq_avg]
  apply treeAvg_mono
  intro b; classical
  by_cases hp : P b
  · simp [hp, h b hp]
  · simp only [hp, ↓reduceIte]; split_ifs <;> norm_num

lemma treeProb_congr (n : ℕ) {P Q : (Fin n → Bool) → Prop} (h : ∀ b, P b ↔ Q b) :
    treeProb n P = treeProb n Q := by
  apply le_antisymm
  · exact treeProb_mono n (fun b hp ↦ (h b).mp hp)
  · exact treeProb_mono n (fun b hq ↦ (h b).mpr hq)

lemma treeProb_union (n : ℕ) (P Q : (Fin n → Bool) → Prop) :
    treeProb n (fun b ↦ P b ∨ Q b) ≤ treeProb n P + treeProb n Q := by
  rw [treeProb_eq_avg, treeProb_eq_avg, treeProb_eq_avg, ← treeAvg_add]
  apply treeAvg_mono
  intro b; classical
  by_cases hp : P b <;> by_cases hq : Q b <;> simp [hp, hq]

lemma treeProb_compl (n : ℕ) (P : (Fin n → Bool) → Prop) :
    treeProb n (fun b ↦ ¬ P b) = 1 - treeProb n P := by
  have hsum : treeProb n (fun b ↦ ¬ P b) + treeProb n P = 1 := by
    rw [treeProb_eq_avg, treeProb_eq_avg, ← treeAvg_add]
    trans treeAvg n (fun _ ↦ 1)
    · congr 1; ext b; classical by_cases hp : P b <;> simp [hp]
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
      treeAvg m₁ (fun b₁ ↦ treeProb m₂ (fun b₂ ↦ P (Fin.append b₁ b₂))) := by
  rw [treeProb_eq_avg, treeAvg_append]
  congr 1; ext b₁
  exact (treeProb_eq_avg m₂ (fun b₂ ↦ P (Fin.append b₁ b₂))).symm

/-- Markov's inequality on `Fin n → Bool`. -/
lemma treeProb_markov (n : ℕ) {f : (Fin n → Bool) → ℝ} (hf : ∀ b, 0 ≤ f b)
    {c : ℝ} (hc : 0 < c) {P : (Fin n → Bool) → Prop}
    (hP : ∀ b, P b → c ≤ f b) :
    treeProb n P ≤ treeAvg n f / c := by
  rw [treeProb_eq_avg]
  rw [le_div_iff₀ hc]
  have hmul : treeAvg n (fun b ↦ by classical exact if P b then (1 : ℝ) else 0) * c =
      treeAvg n (fun b ↦ by classical exact if P b then c else 0) := by
    rw [mul_comm, ← treeAvg_mul_const]
    congr 1; ext b; classical split_ifs <;> ring
  rw [hmul]
  apply treeAvg_mono
  intro b; classical
  split_ifs with hp
  · exact hP b hp
  · exact hf b

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
        classical
        split_ifs with h
        · exfalso
          rcases h with ⟨t, ht⟩
          have ht0 : t = 0 := Subsingleton.elim t 0
          subst ht0
          have hfun : pathPrefix (Nat.le_of_lt_succ (0 : Fin 1).isLt) Fin.elim0 = Fin.elim0 := by
            ext i; exact Fin.elim0 i
          exact h0 (by simpa [hfun] using ht)
        · rfl
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

/-! ### Stage 1 & Stage 2 Constants and Lemmas 5.2–5.3 -/

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
          ((by classical exact if P.H m₁ b ≤ η then (1 : ℝ) else 0) +
           (by classical exact if η < P.H m₁ b ∧ P.H m₁ b < 1 - η then (1 : ℝ) else 0)) + η) := by
      apply treeAvg_mono
      intro b; classical
      have hH := P.H_mem m₁ b
      split_ifs with h1 h2 h3
      · linarith [hH.1, hη_pos]
      · linarith [hH.1, hη_pos]
      · linarith [hH.1, hη_pos]
      · have hge : 1 - η ≤ P.H m₁ b := by
          by_contra hlt
          exact h3 ⟨lt_of_not_ge h1, lt_of_not_ge hlt⟩
        linarith
    rw [treeAvg_add, treeAvg_add, treeAvg_const] at hmono
    rw [← treeProb_eq_avg, ← treeProb_eq_avg] at hmono
    linarith [hcap, hmono]
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
  let hit16 : (t : ℕ) → (Fin t → Bool) → Prop :=
    fun t b ↦ ∃ s : Fin (t + 1), (1 / 16 : ℝ) < Z' s.val (pathPrefix (Nat.le_of_lt_succ s.isLt) b)
  let M : (t : ℕ) → (Fin t → Bool) → ℝ :=
    Nat.rec (fun _ ↦ Real.sqrt (Z' 0 Fin.elim0))
      (fun t Mprev b ↦ by
        classical
        exact if hit16 t (pathPrefix (Nat.le_succ t) b) then
          Mprev (pathPrefix (Nat.le_succ t) b)
        else Real.sqrt (Z' (t + 1) b))
  have hM_nn : ∀ t b, 0 ≤ M t b := by
    intro t
    induction t with
    | zero => intro _; exact Real.sqrt_nonneg _
    | succ t ih =>
      intro b; simp only [M]; classical
      split_ifs
      · exact ih _
      · exact Real.sqrt_nonneg _
  have hM_not_hit : ∀ t b, ¬ hit16 t b → M t b = Real.sqrt (Z' t b) := by
    intro t
    cases t with
    | zero =>
      intro b _
      have hb : b = Fin.elim0 := Subsingleton.elim b Fin.elim0
      subst hb; rfl
    | succ t =>
      intro b hnot
      simp only [M]; classical
      have hnot_prev : ¬ hit16 t (pathPrefix (Nat.le_succ t) b) := by
        rintro ⟨s, hs⟩
        apply hnot
        refine ⟨s.castSucc, ?_⟩
        rw [pathPrefix_pathPrefix] at hs
        exact hs
      simp [hnot_prev]
  have hM_step_not_hit : ∀ t b, ¬ hit16 t b →
      (M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) +
        M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)) / 2 ≤ gamma2 * M t b := by
    intro t b hnot
    have hZle : Z' t b ≤ 1 / 16 := by
      by_contra hgt
      apply hnot
      refine ⟨Fin.last t, ?_⟩
      have hpre : pathPrefix (Nat.le_of_lt_succ (Fin.last t).isLt) b = b := by
        ext i; rfl
      simpa [hpre] using lt_of_not_ge hgt
    have hM_eq : M t b = Real.sqrt (Z' t b) := hM_not_hit t b hnot
    have hM_f : M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) =
        Real.sqrt (Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false)) := by
      simp only [M]; classical simp [pathPrefix_snoc, hnot]
    have hM_t : M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) =
        Real.sqrt (Z' (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)) := by
      simp only [M]; classical simp [pathPrefix_snoc, hnot]
    rw [hM_f, hM_t, hM_eq, hZ'_plus]
    have hsqrt_sq : Real.sqrt ((Z' t b) ^ 2) = Z' t b := Real.sqrt_sq (hZ'_nn t b)
    rw [hsqrt_sq]
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
    by_cases hhit : hit16 t b
    · have hf : M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) = M t b := by
        simp only [M]; classical simp [pathPrefix_snoc, hhit]
      have ht : M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) = M t b := by
        simp only [M]; classical simp [pathPrefix_snoc, hhit]
      rw [hf, ht]; linarith
    · have h1 := hM_step_not_hit t b hhit
      have h2 := gamma2_lt_one
      have h3 := hM_nn t b
      nlinarith
  have hprob_hit : treeProb m₂ (hit16 m₂) < ε / 8 := by
    have hdoob := tree_doob_maximal m₂ (fun t _ b ↦ M t b) (fun t _ b ↦ hM_nn t b)
      (fun t _ b ↦ hM_super t b) (1 / 4) (by norm_num)
    have hsub : treeProb m₂ (hit16 m₂) ≤
        treeProb m₂ (fun b ↦ ∃ t : Fin (m₂ + 1),
          (1 / 4 : ℝ) ≤ M t.val (pathPrefix (Nat.le_of_lt_succ t.isLt) b)) := by
      apply treeProb_mono
      intro b hhit
      have hex : ∃ k : ℕ, ∃ hk : k ≤ m₂, (1 / 16 : ℝ) < Z' k (pathPrefix hk b) := by
        rcases hhit with ⟨s, hs⟩
        exact ⟨s.val, Nat.le_of_lt_succ s.isLt, hs⟩
      classical
      let k₀ := Nat.find hex
      have hk₀ : ∃ hk : k₀ ≤ m₂, (1 / 16 : ℝ) < Z' k₀ (pathPrefix hk b) := Nat.find_spec hex
      rcases hk₀ with ⟨hk₀_le, hk₀_gt⟩
      have hk₀_bound : (1 / 4 : ℝ) ≤ M k₀ (pathPrefix hk₀_le b) := by
        have hstep : ∀ (k : ℕ) (hk : k ≤ m₂), k = k₀ →
            (1 / 16 : ℝ) < Z' k (pathPrefix hk b) → (1 / 4 : ℝ) ≤ M k (pathPrefix hk b) := by
          intro k hk hkeq hgt
          cases k with
          | zero =>
            exfalso
            have hpre0 : pathPrefix hk b = Fin.elim0 := by ext i; exact Fin.elim0 i
            rw [hpre0, hZ'0] at hgt
            linarith
          | succ k' =>
            have hnot_prev : ¬ hit16 k' (pathPrefix (Nat.le_of_succ_le hk) b) := by
              rintro ⟨s, hs⟩
              have hs_lt : s.val < k₀ := by omega
              have hmin := Nat.find_min hex hs_lt
              apply hmin
              refine ⟨le_trans (Nat.le_of_lt_succ s.isLt) (Nat.le_of_succ_le hk), ?_⟩
              rw [pathPrefix_pathPrefix] at hs
              exact hs
            have hMeq : M (k' + 1) (pathPrefix hk b) = Real.sqrt (Z' (k' + 1) (pathPrefix hk b)) := by
              simp only [M]; classical
              rw [pathPrefix_pathPrefix]
              simp [hnot_prev]
            rw [hMeq]
            calc (1 / 4 : ℝ) = Real.sqrt ((1 / 4) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
              _ ≤ Real.sqrt (Z' (k' + 1) (pathPrefix hk b)) := Real.sqrt_le_sqrt (by linarith)
        exact hstep k₀ hk₀_le rfl hk₀_gt
      exact ⟨⟨k₀, Nat.lt_succ_of_le hk₀_le⟩, hk₀_bound⟩
    have hM0_le : M 0 Fin.elim0 / (1 / 4) ≤ 4 * Real.sqrt Z₀ := by
      have hM0 : M 0 Fin.elim0 = Real.sqrt (P.Z m₁ w) := by simp [M, hZ'0]
      rw [hM0]
      have hsq : Real.sqrt (P.Z m₁ w) ≤ Real.sqrt Z₀ := Real.sqrt_le_sqrt hw
      linarith
    linarith only [hsub, hdoob, hM0_le, h4sqrtZ0]
  have hdecay : ∀ t : ℕ,
      treeAvg t (fun b ↦ by classical exact if ¬ hit16 t b then M t b else 0) ≤
        gamma2 ^ t * Real.sqrt Z₀ := by
    intro t
    induction t with
    | zero =>
      rw [treeAvg_zero, pow_zero, one_mul]; classical
      split_ifs
      · exact Real.sqrt_nonneg _
      · have hM0 : M 0 Fin.elim0 = Real.sqrt (P.Z m₁ w) := by simp [M, hZ'0]
        rw [hM0]
        exact Real.sqrt_le_sqrt hw
    | succ t ih =>
      rw [treeAvg_snoc, ← treeAvg_add]
      have hdiv : ∀ (g : (Fin t → Bool) → ℝ), treeAvg t g / 2 = treeAvg t (fun b ↦ g b / 2) := by
        intro g; unfold treeAvg; rw [← Finset.sum_div, div_div, div_div, mul_comm]
      rw [hdiv]
      have hstep : treeAvg t (fun b ↦
          ((by classical exact if ¬ hit16 (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false)
              then (M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false)) else 0) +
           (by classical exact if ¬ hit16 (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)
              then (M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)) else 0)) / 2) ≤
          gamma2 * treeAvg t (fun b ↦ by classical exact if ¬ hit16 t b then M t b else 0) := by
        rw [← treeAvg_mul_const]
        apply treeAvg_mono
        intro b; classical
        by_cases hhit : hit16 t b
        · have hf : hit16 (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) := by
            rcases hhit with ⟨s, hs⟩
            refine ⟨s.castSucc, ?_⟩
            have hpre : pathPrefix (Nat.le_of_lt_succ s.castSucc.isLt)
                (Fin.snoc (α := fun _ ↦ Bool) b false) =
                pathPrefix (Nat.le_of_lt_succ s.isLt) b := by
              ext i; exact Fin.snoc_castSucc (α := fun _ ↦ Bool) false b _
            simpa [hpre] using hs
          have ht : hit16 (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) := by
            rcases hhit with ⟨s, hs⟩
            refine ⟨s.castSucc, ?_⟩
            have hpre : pathPrefix (Nat.le_of_lt_succ s.castSucc.isLt)
                (Fin.snoc (α := fun _ ↦ Bool) b true) =
                pathPrefix (Nat.le_of_lt_succ s.isLt) b := by
              ext i; exact Fin.snoc_castSucc (α := fun _ ↦ Bool) true b _
            simpa [hpre] using hs
          simp [hhit, hf, ht]
        · simp only [hhit, not_false_eq_true, ↓reduceIte]
          have h1 : (if ¬ hit16 (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false)
              then M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) else 0) ≤
              M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b false) := by
            split_ifs
            · exact hM_nn _ _
            · exact le_rfl
          have h2 : (if ¬ hit16 (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true)
              then M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) else 0) ≤
              M (t + 1) (Fin.snoc (α := fun _ ↦ Bool) b true) := by
            split_ifs
            · exact hM_nn _ _
            · exact le_rfl
          linarith only [h1, h2, hM_step_not_hit t b hhit]
      calc _ ≤ gamma2 * treeAvg t (fun b ↦ by classical exact if ¬ hit16 t b then M t b else 0) :=
              hstep
        _ ≤ gamma2 * (gamma2 ^ t * Real.sqrt Z₀) :=
              mul_le_mul_of_nonneg_left ih (le_of_lt gamma2_pos)
        _ = gamma2 ^ (t + 1) * Real.sqrt Z₀ := by rw [pow_succ']; ring
  have hprob_tail : treeProb m₂ (fun b ↦ ¬ hit16 m₂ b ∧ (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b) ≤
      ε / 8 := by
    have hc_pos : 0 < (2 : ℝ) ^ (-(Y₀ : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have hmarkov := treeProb_markov m₂
      (f := fun b ↦ by classical exact if ¬ hit16 m₂ b then M m₂ b else 0)
      (fun b ↦ by
        classical
        split_ifs
        · exact le_rfl
        · exact hM_nn m₂ b)
      hc_pos
      (P := fun b ↦ ¬ hit16 m₂ b ∧ (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b)
      (fun b ⟨hnot, hgt⟩ ↦ by
        classical
        simp only [hnot, not_false_eq_true, ↓reduceIte]
        rw [hM_not_hit m₂ b hnot]
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
      have hprod_pos : 0 < gamma2 ^ m₂ * (2 : ℝ) ^ ((Y₀ : ℝ) / 2) := by
        exact mul_pos (pow_pos gamma2_pos m₂) (Real.rpow_pos_of_pos (by norm_num) _)
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
    calc treeProb m₂ (fun b ↦ ¬ hit16 m₂ b ∧ (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b)
        ≤ treeAvg m₂ (fun b ↦ by classical exact if ¬ hit16 m₂ b then M m₂ b else 0) /
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
        treeProb m₂ (fun b ↦ hit16 m₂ b ∨ (¬ hit16 m₂ b ∧ (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b)) := by
      apply treeProb_mono
      intro b hgt
      by_cases h : hit16 m₂ b
      · exact Or.inl h
      · exact Or.inr ⟨h, hgt⟩
    have hunion := treeProb_union m₂ (hit16 m₂)
      (fun b ↦ ¬ hit16 m₂ b ∧ (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b)
    linarith only [hsub, hunion, hprob_hit, hprob_tail]
  have hcompl := treeProb_compl m₂ (fun b ↦ Z' m₂ b ≤ (2 : ℝ) ^ (-(Y₀ : ℝ)))
  have heq : treeProb m₂ (fun b ↦ ¬ (Z' m₂ b ≤ (2 : ℝ) ^ (-(Y₀ : ℝ)))) =
      treeProb m₂ (fun b ↦ (2 : ℝ) ^ (-(Y₀ : ℝ)) < Z' m₂ b) :=
    treeProb_congr m₂ (fun _ ↦ not_le)
  rw [heq] at hcompl
  linarith only [hbad, hcompl]

end PolarCodes
