/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.MainTheorem
import PolarCodes.ChannelEquiv
import PolarCodes.NoncommutativeUnion

/-!
# Arıkan Polar Transform `G_N`, Product Channel `W^{\otimes N}`, and Synthesized Channels `W_n^{(i)}`

This module constructs the explicit blocklength-`N = 2^n` coding objects of Section 5:
- `productState W n x`: the `N`-copy product c-q channel output `W^{\otimes N}(x)` on `Fin (2^n) → d`
- `arikanTransform n`: Arıkan's polar transform `u ↦ u G_N` where `G_N = B_N F^{\otimes n}` over `𝔽₂^N`
- `arikanMatrix n`: the explicit `N × N` binary matrix `G_N` over `ZMod 2`
- `synthChannel W n i`: the `i`-th synthesized binary-input c-q channel `W_n^{(i)}` outputting the
  quantum register `B^N` together with the classical prior bits `U_1^{i-1}`
- `bitPath n`: the bijection `Fin (2^n) ≃ (Fin n → Bool)`
- `synthChannel_reindex_polarChannelTree`: exact basis-permutation equivalence between
  `synthChannel W n i` and `polarChannelTree W n (bitPath n i)`
- `synthChannel_condEntropy_eq` and `synthChannel_fidelityParam_eq`: exact equality of conditional
  entropy and root fidelity between `W_n^{(i)}` and `polarChannelTree W n (bitPath n i)`.
-/

open Matrix BigOperators Real
open scoped ComplexOrder

namespace PolarCodes

universe u

section ProductAndArikan

variable {d : Type u} [Fintype d] [DecidableEq d]

/-! ### Product Channel `W^{\otimes 2^n}` -/

/-- Matrix of the `2^n`-copy product state `W^{\otimes 2^n}(x)` on `Fin (2^n) → d`. -/
noncomputable def productStateMat (W : CQChannel d) (n : ℕ) (x : Fin (2 ^ n) → Bool) :
    Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ :=
  Matrix.of fun r s ↦ ∏ k : Fin (2 ^ n), (W.out (x k)).mat (r k) (s k)

/-- The `2^n`-copy product output density operator `W^{\otimes 2^n}(x)`. -/
noncomputable def productState (W : CQChannel d) (n : ℕ) (x : Fin (2 ^ n) → Bool) :
    DensityOp (Fin (2 ^ n) → d) where
  mat := productStateMat W n x
  posSemidef := by
    let A : Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ :=
      Matrix.of fun r s ↦ ∏ k : Fin (2 ^ n), (W.out (x k)).sqrtMat (r k) (s k)
    have hAA : A * Aᴴ = productStateMat W n x := by
      ext r s
      simp only [A, productStateMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
      have hterm : ∀ t : Fin (2 ^ n) → d,
          (∏ k : Fin (2 ^ n), (W.out (x k)).sqrtMat (r k) (t k)) *
            star (∏ k : Fin (2 ^ n), (W.out (x k)).sqrtMat (s k) (t k)) =
          ∏ k : Fin (2 ^ n),
            (W.out (x k)).sqrtMat (r k) (t k) * star ((W.out (x k)).sqrtMat (s k) (t k)) := by
        intro t
        rw [star_prod, ← Finset.prod_mul_distrib]
      simp_rw [hterm]
      rw [← Fintype.prod_sum (fun k a ↦
        (W.out (x k)).sqrtMat (r k) a * star ((W.out (x k)).sqrtMat (s k) a))]
      apply Finset.prod_congr rfl; intro k _
      have hsq := congr_fun (congr_fun (W.out (x k)).sqrtMat_mul_self (r k)) (s k)
      rw [← hsq]; simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro a _
      have hhk : star ((W.out (x k)).sqrtMat (s k) a) = (W.out (x k)).sqrtMat a (s k) := by
        have := congr_fun (congr_fun (W.out (x k)).sqrtMat_isHermitian.eq a) (s k)
        simpa [Matrix.conjTranspose_apply] using this
      rw [hhk]
    rw [← hAA]
    exact posSemidef_mul_conjTranspose A
  trace_one := by
    simp only [Matrix.trace, Matrix.diag, productStateMat, Matrix.of_apply]
    rw [← Fintype.prod_sum (fun k a ↦ (W.out (x k)).mat a a)]
    have h1 : ∀ k : Fin (2 ^ n), ∑ a : d, (W.out (x k)).mat a a = 1 := fun k ↦ (W.out (x k)).trace_one
    simp [h1]

/-! ### Arıkan's Polar Transform `G_N = B_N F^{\otimes n}` -/

/-- Even-pair XOR half `v₁_j = u_{2j} ⊕ u_{2j+1}` in Arıkan's butterfly recursion. -/
def arikanEven (n : ℕ) (u : Fin (2 ^ (n + 1)) → Bool) : Fin (2 ^ n) → Bool :=
  fun j ↦ xor (u ⟨2 * j.val, by omega⟩) (u ⟨2 * j.val + 1, by omega⟩)

/-- Odd-index half `v₂_j = u_{2j+1}` in Arıkan's butterfly recursion. -/
def arikanOdd (n : ℕ) (u : Fin (2 ^ (n + 1)) → Bool) : Fin (2 ^ n) → Bool :=
  fun j ↦ u ⟨2 * j.val + 1, by omega⟩

/-- Arıkan's polar transform `u ↦ u G_N` (`G_N = B_N F^{\otimes n}`, `N = 2^n`) on `Bool^N`. -/
def arikanTransform : (n : ℕ) → (Fin (2 ^ n) → Bool) → (Fin (2 ^ n) → Bool)
  | 0, u => u
  | n + 1, u => fun k ↦
      if hk : k.val < 2 ^ n then
        arikanTransform n (arikanEven n u) ⟨k.val, hk⟩
      else
        arikanTransform n (arikanOdd n u) ⟨k.val - 2 ^ n, by omega⟩

/-- `𝔽₂`-linearity of Arıkan's transform: `(u ⊕ v) G_N = (u G_N) ⊕ (v G_N)`. -/
lemma arikanTransform_xor : ∀ (n : ℕ) (u v : Fin (2 ^ n) → Bool),
    arikanTransform n (fun j ↦ xor (u j) (v j)) =
      fun k ↦ xor (arikanTransform n u k) (arikanTransform n v k)
  | 0, _, _ => rfl
  | n + 1, u, v => by
    funext k
    simp only [arikanTransform]
    split_ifs with hk
    · have hev : arikanEven n (fun j ↦ xor (u j) (v j)) =
          fun j ↦ xor (arikanEven n u j) (arikanEven n v j) := by
        funext j; simp only [arikanEven]
        cases u ⟨2 * j.val, by omega⟩ <;> cases u ⟨2 * j.val + 1, by omega⟩ <;>
          cases v ⟨2 * j.val, by omega⟩ <;> cases v ⟨2 * j.val + 1, by omega⟩ <;> rfl
      rw [hev, arikanTransform_xor n]
    · have hodd : arikanOdd n (fun j ↦ xor (u j) (v j)) =
          fun j ↦ xor (arikanOdd n u j) (arikanOdd n v j) := by
        funext j; rfl
      rw [hodd, arikanTransform_xor n]

/-- Pairing equivalence `(Fin (2^(n+1)) → Bool) ≃ (Fin (2^n) → Bool) × (Fin (2^n) → Bool)`
induced by the Arıkan butterfly `(u_{2j}, u_{2j+1}) ↦ (u_{2j} ⊕ u_{2j+1}, u_{2j+1})`. -/
def arikanSplitEquiv (n : ℕ) :
    (Fin (2 ^ (n + 1)) → Bool) ≃ (Fin (2 ^ n) → Bool) × (Fin (2 ^ n) → Bool) where
  toFun u := (arikanEven n u, arikanOdd n u)
  invFun p := fun k ↦
    if k.val % 2 = 0 then xor (p.1 ⟨k.val / 2, by omega⟩) (p.2 ⟨k.val / 2, by omega⟩)
    else p.2 ⟨k.val / 2, by omega⟩
  left_inv u := by
    funext k
    simp only [arikanEven, arikanOdd]
    split_ifs with h
    · have h1 : 2 * (k.val / 2) = k.val := by omega
      have h2 : (⟨2 * (k.val / 2), by omega⟩ : Fin (2 ^ (n + 1))) = k := Fin.ext h1
      rw [h2]
      cases u k <;> cases u ⟨2 * (k.val / 2) + 1, by omega⟩ <;> rfl
    · have h1 : 2 * (k.val / 2) + 1 = k.val := by omega
      exact congr_arg u (Fin.ext h1)
  right_inv p := by
    rcases p with ⟨v₁, v₂⟩
    ext j
    · simp only [arikanEven]
      have h1 : (2 * j.val) % 2 = 0 := by omega
      have h2 : (2 * j.val + 1) % 2 ≠ 0 := by omega
      have h3 : (2 * j.val) / 2 = j.val := by omega
      have h4 : (2 * j.val + 1) / 2 = j.val := by omega
      simp only [h1, h2, ↓reduceIte, h3, h4]
      cases v₁ j <;> cases v₂ j <;> rfl
    · simp only [arikanOdd]
      have h2 : (2 * j.val + 1) % 2 ≠ 0 := by omega
      have h4 : (2 * j.val + 1) / 2 = j.val := by omega
      simp only [h2, ↓reduceIte, h4]

/-- `arikanTransform n` is a bijection on `Bool^{2^n}`. -/
lemma arikanTransform_bijective : ∀ n : ℕ, Function.Bijective (arikanTransform n)
  | 0 => Function.bijective_id
  | n + 1 => by
    have ih := arikanTransform_bijective n
    let eConcat : (Fin (2 ^ n) → Bool) × (Fin (2 ^ n) → Bool) ≃ (Fin (2 ^ (n + 1)) → Bool) :=
      { toFun := fun p k ↦ if hk : k.val < 2 ^ n then p.1 ⟨k.val, hk⟩ else p.2 ⟨k.val - 2 ^ n, by omega⟩
        invFun := fun x ↦ (fun j ↦ x ⟨j.val, by omega⟩, fun j ↦ x ⟨j.val + 2 ^ n, by omega⟩)
        left_inv := fun ⟨x₁, x₂⟩ ↦ by
          ext j
          · simp [j.isLt]
          · have h1 : ¬ (j.val + 2 ^ n < 2 ^ n) := by omega
            have h2 : j.val + 2 ^ n - 2 ^ n = j.val := by omega
            simp [h1, h2]
        right_inv := fun x ↦ by
          funext k
          dsimp only
          split_ifs with hk
          · rfl
          · exact congr_arg x (Fin.ext (by dsimp; omega)) }
    have hcomp : arikanTransform (n + 1) =
        eConcat ∘ (Prod.map (arikanTransform n) (arikanTransform n)) ∘ arikanSplitEquiv n := rfl
    rw [hcomp]
    exact eConcat.bijective.comp ((ih.prodMap ih).comp (arikanSplitEquiv n).bijective)

/-- Explicit binary generator matrix `G_N = B_N F^{\otimes n}` over `ZMod 2`. -/
def arikanMatrix (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) (ZMod 2) :=
  Matrix.of fun i k ↦ if arikanTransform n (fun j ↦ decide (j = i)) k then 1 else 0

/-- Register splitting equivalence `(Fin (2^(n+1)) → d) ≃ (Fin (2^n) → d) × (Fin (2^n) → d)`. -/
def splitRegEquiv (d : Type u) (n : ℕ) :
    (Fin (2 ^ (n + 1)) → d) ≃ (Fin (2 ^ n) → d) × (Fin (2 ^ n) → d) where
  toFun r := (fun j ↦ r ⟨j.val, by omega⟩, fun j ↦ r ⟨j.val + 2 ^ n, by omega⟩)
  invFun p := fun k ↦ if hk : k.val < 2 ^ n then p.1 ⟨k.val, hk⟩ else p.2 ⟨k.val - 2 ^ n, by omega⟩
  left_inv r := by
    funext k
    dsimp only
    split_ifs with hk
    · rfl
    · exact congr_arg r (Fin.ext (by dsimp; omega))
  right_inv p := by
    rcases p with ⟨r₁, r₂⟩
    ext j
    · simp [j.isLt]
    · have h1 : ¬ (j.val + 2 ^ n < 2 ^ n) := by omega
      have h2 : j.val + 2 ^ n - 2 ^ n = j.val := by omega
      simp [h1, h2]

/-- Factorization of `productState W (n + 1) (arikanTransform (n + 1) u)` into the tensor product
of the two depth-`n` Arıkan-transformed product states on `arikanEven n u` and `arikanOdd n u`. -/
lemma productState_arikan_succ (W : CQChannel d) (n : ℕ) (u : Fin (2 ^ (n + 1)) → Bool)
    (r s : Fin (2 ^ (n + 1)) → d) :
    (productState W (n + 1) (arikanTransform (n + 1) u)).mat r s =
      (productState W n (arikanTransform n (arikanEven n u))).mat
          (splitRegEquiv d n r).1 (splitRegEquiv d n s).1 *
      (productState W n (arikanTransform n (arikanOdd n u))).mat
          (splitRegEquiv d n r).2 (splitRegEquiv d n s).2 := by
  simp only [productState, productStateMat, Matrix.of_apply, splitRegEquiv, Equiv.coe_fn_mk]
  have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
  let e : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
    { toFun := fun s ↦ match s with
        | Sum.inl j => ⟨j.val, by omega⟩
        | Sum.inr j => ⟨j.val + 2 ^ n, by omega⟩
      invFun := fun k ↦ if hk : k.val < 2 ^ n then Sum.inl ⟨k.val, hk⟩
        else Sum.inr ⟨k.val - 2 ^ n, by omega⟩
      left_inv := fun s ↦ by
        cases s with
        | inl j => simp [j.isLt]
        | inr j =>
          have h1 : ¬ (j.val + 2 ^ n < 2 ^ n) := by omega
          have h2 : j.val + 2 ^ n - 2 ^ n = j.val := by omega
          simp [h1, h2]
      right_inv := fun k ↦ by
        dsimp only
        split_ifs with hk
        · rfl
        · exact Fin.ext (by dsimp; omega) }
  rw [← Equiv.prod_comp e]
  rw [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl; intro j _
    simp only [e, Equiv.coe_fn_mk, arikanTransform, j.isLt, ↓reduceDIte]
  · apply Finset.prod_congr rfl; intro j _
    have h1 : ¬ (j.val + 2 ^ n < 2 ^ n) := by omega
    have h2 : (⟨j.val + 2 ^ n - 2 ^ n, by omega⟩ : Fin (2 ^ n)) = j := Fin.ext (by dsimp; omega)
    simp only [e, Equiv.coe_fn_mk, arikanTransform, h1, ↓reduceDIte, h2]

/-! ### Explicit Synthesized Channels `W_n^{(i)}` -/

/-- Classical prefix `u_{<i} : Fin i.val → Bool` of `u : Fin N → Bool`. -/
def prefixOf {N : ℕ} (i : Fin N) (u : Fin N → Bool) : Fin i.val → Bool :=
  fun j ↦ u ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

/-- Unnormalized conditional output block of `W_n^{(i)}` given prefix `p` and input bit `b`. -/
noncomputable def synthBlockMat (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n))
    (p : Fin i.val → Bool) (b : Bool) :
    Matrix (Fin (2 ^ n) → d) (Fin (2 ^ n) → d) ℂ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ prefixOf i u = p ∧ u i = b),
    (productState W n (arikanTransform n u)).mat

/-- Number of vectors `u : Fin N → Bool` with `u i = b` is `2^(N - 1)`. -/
lemma card_filter_at_eq {N : ℕ} (i : Fin N) (b : Bool) :
    (Finset.univ.filter (fun u : Fin N → Bool ↦ u i = b)).card = 2 ^ (N - 1) := by
  have h1 : N = (N - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero (by rintro rfl; exact Fin.elim0 i))).symm
  let S_true := Finset.univ.filter (fun u : Fin N → Bool ↦ u i = b)
  let S_false := Finset.univ.filter (fun u : Fin N → Bool ↦ u i = !b)
  have hdisj : Disjoint S_true S_false := by
    rw [Finset.disjoint_filter]; intro u _ h1 h2; rw [h1] at h2; cases b <;> simp at h2
  have hunion : S_true ∪ S_false = Finset.univ := by
    ext u; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true,
      S_true, S_false]
    cases u i <;> cases b <;> simp
  have hbij : S_true.card = S_false.card := by
    apply Finset.card_bij (fun u _ ↦ Function.update u i (!b))
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S_false]
      simp [Function.update_self]
    · intro u₁ hu₁ u₂ hu₂ h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S_true] at hu₁ hu₂
      funext k
      by_cases hk : k = i
      · subst hk; rw [hu₁, hu₂]
      · have := congr_fun h k; simpa [Function.update_of_ne hk] using this
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S_false] at hv
      refine ⟨Function.update v i b, ?_, ?_⟩
      · simp [S_true, Function.update_self]
      · funext k; by_cases hk : k = i
        · subst hk; simp [Function.update_self, hv]
        · simp [Function.update_of_ne hk]
  have htot : S_true.card + S_false.card = 2 ^ N := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  have hpow : 2 ^ N = 2 * 2 ^ (N - 1) := by
    conv_lhs => rw [h1, pow_succ, mul_comm]
  change S_true.card = 2 ^ (N - 1)
  omega

/-- Number of vectors `u : Fin N → Bool` with `prefixOf i u = p` and `u i = b` is `2^(N - 1 - i.val)`. -/
lemma card_filter_prefix_at_eq {N : ℕ} (i : Fin N) (p : Fin i.val → Bool) (b : Bool) :
    (Finset.univ.filter (fun u : Fin N → Bool ↦ prefixOf i u = p ∧ u i = b)).card =
      2 ^ (N - 1 - i.val) := by
  let e : {u : Fin N → Bool // prefixOf i u = p ∧ u i = b} ≃ (Fin (N - 1 - i.val) → Bool) :=
    { toFun := fun u k ↦ u.1 ⟨i.val + 1 + k.val, by omega⟩
      invFun := fun s ↦
        ⟨fun k ↦ if h1 : k.val < i.val then p ⟨k.val, h1⟩
          else if h2 : k.val = i.val then b
          else s ⟨k.val - i.val - 1, by omega⟩, by
          refine ⟨?_, ?_⟩
          · funext j; simp [prefixOf, j.isLt]
          · simp⟩
      left_inv := fun ⟨u, hp, hb⟩ ↦ by
        apply Subtype.ext; funext k
        dsimp only
        split_ifs with h1 h2
        · have := congr_fun hp ⟨k.val, h1⟩
          simpa [prefixOf] using this.symm
        · have hk : k = i := Fin.ext h2
          rw [hk, hb]
        · exact congr_arg u (Fin.ext (by dsimp; omega))
      right_inv := fun s ↦ by
        funext k
        have h1 : ¬ (i.val + 1 + k.val < i.val) := by omega
        have h2 : i.val + 1 + k.val ≠ i.val := by omega
        have h3 : (⟨i.val + 1 + k.val - i.val - 1, by omega⟩ : Fin (N - 1 - i.val)) = k :=
          Fin.ext (by dsimp; omega)
        simp [h1, h2, h3] }
  have hcard : Fintype.card {u : Fin N → Bool // prefixOf i u = p ∧ u i = b} =
      (Finset.univ.filter (fun u : Fin N → Bool ↦ prefixOf i u = p ∧ u i = b)).card :=
    Fintype.card_subtype _
  rw [← hcard, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Normalized output state of the `i`-th synthesized channel `W_n^{(i)}` on input `b : Bool`. -/
noncomputable def synthState (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n)) (b : Bool) :
    DensityOp ((Fin i.val → Bool) × (Fin (2 ^ n) → d)) where
  mat := Matrix.of fun (p₁, r₁) (p₂, r₂) ↦
    if p₁ = p₂ then ((2 : ℂ) ^ (2 ^ n - 1))⁻¹ * synthBlockMat W n i p₁ b r₁ r₂ else 0
  posSemidef := by
    let c : ℝ := ((2 : ℝ) ^ (2 ^ n - 1))⁻¹
    have hc : 0 ≤ c := by positivity
    let block (u : Fin (2 ^ n) → Bool) :
        Matrix ((Fin i.val → Bool) × (Fin (2 ^ n) → d))
               ((Fin i.val → Bool) × (Fin (2 ^ n) → d)) ℂ :=
      Matrix.of fun (p₁, r₁) (p₂, r₂) ↦
        if p₁ = prefixOf i u ∧ p₂ = prefixOf i u then
          (productState W n (arikanTransform n u)).mat r₁ r₂
        else 0
    have hblock_psd : ∀ u, (block u).PosSemidef := by
      intro u
      let E : Matrix ((Fin i.val → Bool) × (Fin (2 ^ n) → d)) (Fin (2 ^ n) → d) ℂ :=
        Matrix.of fun (p, r) s ↦ if p = prefixOf i u ∧ r = s then 1 else 0
      have hE : block u = E * (productState W n (arikanTransform n u)).mat * Eᴴ := by
        ext ⟨p₁, r₁⟩ ⟨p₂, r₂⟩
        simp only [block, E, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
        rw [Finset.sum_eq_single r₂]
        · rw [Finset.sum_eq_single r₁]
          · by_cases h1 : p₁ = prefixOf i u <;> by_cases h2 : p₂ = prefixOf i u <;> simp [h1, h2]
          · intro s₁ _ hne; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ r₁) h
        · intro s₂ _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ r₂) h
      rw [hE]
      exact (productState W n (arikanTransform n u)).posSemidef.mul_mul_conjTranspose_same E
    have hsum_eq : (Matrix.of fun (p₁, r₁) (p₂, r₂) ↦
        if p₁ = p₂ then ((2 : ℂ) ^ (2 ^ n - 1))⁻¹ * synthBlockMat W n i p₁ b r₁ r₂ else 0) =
        (c : ℂ) • ∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ u i = b), block u := by
      ext ⟨p₁, r₁⟩ ⟨p₂, r₂⟩
      simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.sum_apply, block, synthBlockMat,
        smul_eq_mul, c, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_ofNat]
      by_cases hp : p₁ = p₂
      · subst hp
        simp only [↓reduceIte, and_self]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        congr 1
        refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
        ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      · simp only [hp, ↓reduceIte]
        have hzero : ∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ u i = b),
            (if p₁ = prefixOf i u ∧ p₂ = prefixOf i u then
              (productState W n (arikanTransform n u)).mat r₁ r₂ else 0) = 0 := by
          apply Finset.sum_eq_zero; intro u _
          have : ¬ (p₁ = prefixOf i u ∧ p₂ = prefixOf i u) := fun ⟨h1, h2⟩ ↦ hp (h1.trans h2.symm)
          simp [this]
        rw [hzero, mul_zero]
    rw [hsum_eq]
    have hsum_psd : (∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ u i = b), block u).PosSemidef := by
      exact Finset.sum_induction _ (fun M : Matrix _ _ ℂ ↦ M.PosSemidef) (fun _ _ ha hb ↦ ha.add hb)
        Matrix.PosSemidef.zero (fun u _ ↦ hblock_psd u)
    simpa [Complex.real_smul] using hsum_psd.smul hc
  trace_one := by
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, ↓reduceIte, Fintype.sum_prod_type]
    have h1 : ∀ p : Fin i.val → Bool,
        ∑ r : Fin (2 ^ n) → d, ((2 : ℂ) ^ (2 ^ n - 1))⁻¹ * synthBlockMat W n i p b r r =
        ((2 : ℂ) ^ (2 ^ n - 1))⁻¹ *
          ∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ prefixOf i u = p ∧ u i = b), (1 : ℂ) := by
      intro p
      rw [← Finset.mul_sum]
      congr 1
      simp only [synthBlockMat, Matrix.sum_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro u _
      exact (productState W n (arikanTransform n u)).trace_one
    simp_rw [h1]
    rw [← Finset.mul_sum]
    have hpart : ∑ p : Fin i.val → Bool,
        ∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ prefixOf i u = p ∧ u i = b), (1 : ℂ) =
        ∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ u i = b), (1 : ℂ) := by
      have hcard_each : ∀ p : Fin i.val → Bool,
          ∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ n) → Bool ↦ prefixOf i u = p ∧ u i = b), (1 : ℂ) =
          ((2 ^ (2 ^ n - 1 - i.val) : ℕ) : ℂ) := by
        intro p
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_filter_prefix_at_eq]
      simp_rw [hcard_each]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
        nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul, mul_one, card_filter_at_eq]
      have hexp : i.val + (2 ^ n - 1 - i.val) = 2 ^ n - 1 := by omega
      rw [← Nat.cast_mul, ← pow_add, hexp]
    rw [hpart, Finset.sum_const, nsmul_eq_mul, mul_one, card_filter_at_eq]
    push_cast
    exact inv_mul_cancel₀ (by positivity)

/-- The `i`-th synthesized binary-input c-q channel `W_n^{(i)}` from `W^{\otimes 2^n} ∘ G_{2^n}`. -/
noncomputable def synthChannel (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n)) :
    CQChannel ((Fin i.val → Bool) × (Fin (2 ^ n) → d)) where
  out b := synthState W n i b

/-! ### Exact Correspondence Between `synthChannel W n i` and `polarChannelTree W n b` -/

/-- Inverse of `bitPath`: maps a branch path `b : Fin n → Bool` to its coordinate in `Fin (2^n)`. -/
def bitPathInv : (n : ℕ) → (Fin n → Bool) → Fin (2 ^ n)
  | 0, _ => ⟨0, by norm_num⟩
  | n + 1, b =>
      ⟨2 * (bitPathInv n (Fin.init b)).val + if b (Fin.last n) then 1 else 0, by
        have h := (bitPathInv n (Fin.init b)).isLt
        cases b (Fin.last n) <;> simp <;> omega⟩

/-- Forward map of `bitPath`: maps a coordinate in `Fin (2^n)` to its branch path `Fin n → Bool`. -/
def bitPathFwd : (n : ℕ) → Fin (2 ^ n) → (Fin n → Bool)
  | 0, _ => Fin.elim0
  | n + 1, i => Fin.snoc (α := fun _ ↦ Bool) (bitPathFwd n ⟨i.val / 2, by omega⟩) (decide (i.val % 2 = 1))

private lemma bitPathInv_fwd : ∀ (n : ℕ) (i : Fin (2 ^ n)), bitPathInv n (bitPathFwd n i) = i
  | 0, i => Fin.ext (by omega)
  | n + 1, i => by
    apply Fin.ext
    simp only [bitPathInv, bitPathFwd, Fin.init_snoc, Fin.snoc_last]
    rw [bitPathInv_fwd n ⟨i.val / 2, by omega⟩]
    dsimp only
    by_cases hmod : i.val % 2 = 1 <;> simp [hmod] <;> omega

private lemma bitPathFwd_inv : ∀ (n : ℕ) (b : Fin n → Bool), bitPathFwd n (bitPathInv n b) = b
  | 0, b => funext (fun j ↦ Fin.elim0 j)
  | n + 1, b => by
    have hdiv : (bitPathInv (n + 1) b).val / 2 = (bitPathInv n (Fin.init b)).val := by
      simp only [bitPathInv]
      cases b (Fin.last n) <;> simp <;> omega
    have hmod : decide ((bitPathInv (n + 1) b).val % 2 = 1) = b (Fin.last n) := by
      have hval : (bitPathInv (n + 1) b).val =
          2 * (bitPathInv n (Fin.init b)).val + if b (Fin.last n) then 1 else 0 := rfl
      rw [hval]
      by_cases hb : b (Fin.last n) = true <;> simp [hb] <;> omega
    have hfin : (⟨(bitPathInv (n + 1) b).val / 2, by omega⟩ : Fin (2 ^ n)) = bitPathInv n (Fin.init b) :=
      Fin.ext hdiv
    change Fin.snoc (α := fun _ ↦ Bool) (bitPathFwd n ⟨(bitPathInv (n + 1) b).val / 2, _⟩)
      (decide ((bitPathInv (n + 1) b).val % 2 = 1)) = b
    rw [hfin, hmod, bitPathFwd_inv n (Fin.init b), Fin.snoc_init_self]

/-- Bijection `Fin (2^n) ≃ (Fin n → Bool)` matching Arıkan's synthesized channel indices with
tree paths (`false` = minus branch `2j`, `true` = plus branch `2j + 1`). -/
def bitPath (n : ℕ) : Fin (2 ^ n) ≃ (Fin n → Bool) where
  toFun := bitPathFwd n
  invFun := bitPathInv n
  left_inv := bitPathInv_fwd n
  right_inv := bitPathFwd_inv n

private lemma bundled_cast_mat {A B : BundledCQChannel.{u}} (h : A = B) (b : Bool) (x y : B.dim) :
    (A.ch.out b).mat (cast (congrArg BundledCQChannel.dim h.symm) x)
      (cast (congrArg BundledCQChannel.dim h.symm) y) = (B.ch.out b).mat x y := by
  subst h; rfl

/-- Exact basis-permutation equivalence between the explicit synthesized channel `synthChannel W n i`
and the recursive tree channel `polarChannelTree W n (bitPath n i)`. -/
theorem synthChannel_reindex_polarChannelTree (W : CQChannel d) :
    ∀ (n : ℕ) (i : Fin (2 ^ n)),
      ∃ e : ((Fin i.val → Bool) × (Fin (2 ^ n) → d)) ≃ (polarChannelTree W n (bitPath n i)).dim,
        ∀ (b : Bool) (x y : (Fin i.val → Bool) × (Fin (2 ^ n) → d)),
          ((polarChannelTree W n (bitPath n i)).ch.out b).mat (e x) (e y) =
            ((synthChannel W n i).out b).mat x y
  | 0, i => by
    have hi : i.val = 0 := by have := i.isLt; omega
    let e : ((Fin i.val → Bool) × (Fin (2 ^ 0) → d)) ≃ d :=
      { toFun := fun p ↦ p.2 ⟨0, by norm_num⟩
        invFun := fun a ↦ (fun j ↦ False.elim (by have := j.isLt; omega), fun _ ↦ a)
        left_inv := fun ⟨p, r⟩ ↦ by
          ext j
          · exact False.elim (by have := j.isLt; omega)
          · exact congr_arg r (Fin.ext (by have := j.isLt; omega))
        right_inv := fun _ ↦ rfl }
    refine ⟨e, fun b ⟨p₁, r₁⟩ ⟨p₂, r₂⟩ ↦ ?_⟩
    have hp : p₁ = p₂ := funext fun j ↦ False.elim (by have := j.isLt; omega)
    subst hp
    simp only [polarChannelTree, synthChannel, synthState, synthBlockMat, Matrix.of_apply,
      ↓reduceIte, pow_zero, Nat.sub_self, inv_one, one_mul, e, Equiv.coe_fn_mk]
    have hfilt : Finset.univ.filter (fun u : Fin 1 → Bool ↦ prefixOf i u = p₁ ∧ u i = b) =
        {fun _ ↦ b} := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro ⟨_, hu⟩; funext k; have hk : k = i := Fin.ext (by have := k.isLt; omega); rw [hk, hu]
      · intro hu; subst hu; refine ⟨funext fun j ↦ False.elim (by have := j.isLt; omega), rfl⟩
    rw [hfilt, Finset.sum_singleton]
    simp [productState, productStateMat, arikanTransform]
  | n + 1, i => by
    set j : Fin (2 ^ n) := ⟨i.val / 2, by omega⟩
    have hj : j.val = i.val / 2 := rfl
    obtain ⟨e_j, he_j⟩ := synthChannel_reindex_polarChannelTree W n j
    by_cases hmod : i.val % 2 = 0
    · -- Even case: `i = 2j`, minus branch `W_j⁻`
      have hi_eq : i.val = 2 * j.val := by omega
      have htree : polarChannelTree W (n + 1) (bitPath (n + 1) i) =
          (polarChannelTree W n (bitPath n j)).minus := by
        have hbp : bitPath (n + 1) i = Fin.snoc (α := fun _ ↦ Bool) (bitPath n j) false := by
          simp [bitPath, bitPathFwd, j, show ¬ (i.val % 2 = 1) by omega]
        rw [hbp, polarChannelTree_snoc_false]
      let ePref : (Fin i.val → Bool) ≃ (Fin j.val → Bool) × (Fin j.val → Bool) :=
        { toFun := fun p ↦
            (fun k ↦ xor (p ⟨2 * k.val, by omega⟩) (p ⟨2 * k.val + 1, by omega⟩),
             fun k ↦ p ⟨2 * k.val + 1, by omega⟩)
          invFun := fun q k ↦
            if k.val % 2 = 0 then xor (q.1 ⟨k.val / 2, by omega⟩) (q.2 ⟨k.val / 2, by omega⟩)
            else q.2 ⟨k.val / 2, by omega⟩
          left_inv := fun p ↦ by
            funext k; dsimp only; split_ifs with hk
            · have h1 : (⟨2 * (k.val / 2), by omega⟩ : Fin i.val) = k := Fin.ext (by dsimp; omega)
              rw [h1]; cases p k <;> cases p ⟨2 * (k.val / 2) + 1, by omega⟩ <;> rfl
            · exact congr_arg p (Fin.ext (by dsimp; omega))
          right_inv := fun ⟨q₁, q₂⟩ ↦ by
            ext k
            · have h1 : (2 * k.val) % 2 = 0 := by omega
              have h2 : (2 * k.val + 1) % 2 ≠ 0 := by omega
              have h3 : (2 * k.val) / 2 = k.val := by omega
              have h4 : (2 * k.val + 1) / 2 = k.val := by omega
              simp only [h1, h2, ↓reduceIte, h3, h4]
              cases q₁ k <;> cases q₂ k <;> rfl
            · have h2 : (2 * k.val + 1) % 2 ≠ 0 := by omega
              have h4 : (2 * k.val + 1) / 2 = k.val := by omega
              simp only [h2, ↓reduceIte, h4] }
      let eRaw : ((Fin i.val → Bool) × (Fin (2 ^ (n + 1)) → d)) ≃
          (polarChannelTree W n (bitPath n j)).dim × (polarChannelTree W n (bitPath n j)).dim :=
        { toFun := fun ⟨p, r⟩ ↦
            (e_j ((ePref p).1, (splitRegEquiv d n r).1),
             e_j ((ePref p).2, (splitRegEquiv d n r).2))
          invFun := fun ⟨a, b⟩ ↦
            (ePref.symm ((e_j.symm a).1, (e_j.symm b).1),
             (splitRegEquiv d n).symm ((e_j.symm a).2, (e_j.symm b).2))
          left_inv := fun ⟨p, r⟩ ↦ by
            simp only [Equiv.symm_apply_apply]
            exact Prod.ext (ePref.symm_apply_apply p) ((splitRegEquiv d n).symm_apply_apply r)
          right_inv := fun ⟨a, b⟩ ↦ by
            simp only [Equiv.apply_symm_apply, Prod.mk.eta]; rfl }
      let e : ((Fin i.val → Bool) × (Fin (2 ^ (n + 1)) → d)) ≃
          (polarChannelTree W (n + 1) (bitPath (n + 1) i)).dim :=
        eRaw.trans (Equiv.cast (congrArg BundledCQChannel.dim htree.symm))
      refine ⟨e, fun b ⟨p₁, r₁⟩ ⟨p₂, r₂⟩ ↦ ?_⟩
      have hcast : ((polarChannelTree W (n + 1) (bitPath (n + 1) i)).ch.out b).mat (e (p₁, r₁)) (e (p₂, r₂)) =
          (((polarChannelTree W n (bitPath n j)).minus).ch.out b).mat (eRaw (p₁, r₁)) (eRaw (p₂, r₂)) :=
        bundled_cast_mat htree b (eRaw (p₁, r₁)) (eRaw (p₂, r₂))
      rw [hcast]
      have hminus_entry : ∀ (b' : Bool)
          (x₁ y₁ x₂ y₂ : (polarChannelTree W n (bitPath n j)).dim),
          (((polarChannelTree W n (bitPath n j)).minus).ch.out b').mat (x₁, y₁) (x₂, y₂) =
            (1 / 2 : ℂ) *
              (((polarChannelTree W n (bitPath n j)).ch.out b').mat x₁ x₂ *
               ((polarChannelTree W n (bitPath n j)).ch.out false).mat y₁ y₂ +
               ((polarChannelTree W n (bitPath n j)).ch.out !b').mat x₁ x₂ *
               ((polarChannelTree W n (bitPath n j)).ch.out true).mat y₁ y₂) := by
        intro b' x₁ y₁ x₂ y₂
        simp only [BundledCQChannel.minus, CQChannel.minusChannel, CQChannel.checkCombine,
          DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply,
          Matrix.kroneckerMap_apply, Complex.real_smul]
        push_cast; ring
      simp only [eRaw, Equiv.coe_fn_mk]
      rw [hminus_entry, he_j, he_j, he_j, he_j]
      simp only [synthChannel, synthState, Matrix.of_apply]
      by_cases hp : p₁ = p₂
      · subst hp
        simp only [↓reduceIte]
        have hpref_split : ∀ u : Fin (2 ^ (n + 1)) → Bool,
            prefixOf i u = p₁ ↔
              prefixOf j (arikanEven n u) = (ePref p₁).1 ∧
              prefixOf j (arikanOdd n u) = (ePref p₁).2 := by
          intro u
          have heq_ePref : ePref (prefixOf i u) = (prefixOf j (arikanEven n u), prefixOf j (arikanOdd n u)) := rfl
          constructor
          · intro h; rw [← h, heq_ePref]
          · rintro ⟨h1, h2⟩
            exact ePref.injective (heq_ePref.trans (Prod.ext h1 h2))
        have hsum_split : synthBlockMat W (n + 1) i p₁ b r₁ r₂ =
            (synthBlockMat W n j (ePref p₁).1 (xor b false) (splitRegEquiv d n r₁).1 (splitRegEquiv d n r₂).1 *
             synthBlockMat W n j (ePref p₁).2 false (splitRegEquiv d n r₁).2 (splitRegEquiv d n r₂).2) +
            (synthBlockMat W n j (ePref p₁).1 (xor b true) (splitRegEquiv d n r₁).1 (splitRegEquiv d n r₂).1 *
             synthBlockMat W n j (ePref p₁).2 true (splitRegEquiv d n r₁).2 (splitRegEquiv d n r₂).2) := by
          unfold synthBlockMat
          simp only [Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]
          have h1 := Equiv.sum_comp (arikanSplitEquiv n).symm
            (fun u : Fin (2 ^ (n + 1)) → Bool ↦
              if prefixOf i u = p₁ ∧ u i = b then
                (productState W (n + 1) (arikanTransform (n + 1) u)).mat r₁ r₂
              else 0)
          rw [Finset.sum_filter, ← h1]
          simp only [Fintype.sum_prod_type]
          have hcond : ∀ (v₁ v₂ : Fin (2 ^ n) → Bool),
              (prefixOf i ((arikanSplitEquiv n).symm (v₁, v₂)) = p₁ ∧
               (arikanSplitEquiv n).symm (v₁, v₂) i = b) ↔
                (prefixOf j v₁ = (ePref p₁).1 ∧ prefixOf j v₂ = (ePref p₁).2 ∧
                 ((v₁ j = xor b false ∧ v₂ j = false) ∨ (v₁ j = xor b true ∧ v₂ j = true))) := by
            intro v₁ v₂
            have huv : arikanEven n ((arikanSplitEquiv n).symm (v₁, v₂)) = v₁ ∧
                arikanOdd n ((arikanSplitEquiv n).symm (v₁, v₂)) = v₂ :=
              Prod.mk.inj ((arikanSplitEquiv n).apply_symm_apply (v₁, v₂))
            rw [hpref_split, huv.1, huv.2]
            have hui : (arikanSplitEquiv n).symm (v₁, v₂) i = xor (v₁ j) (v₂ j) := by
              simp [arikanSplitEquiv, hmod, j]
            rw [hui]
            constructor
            · rintro ⟨⟨h1, h2⟩, h3⟩
              refine ⟨h1, h2, ?_⟩
              cases hv : v₂ j <;> cases h1v : v₁ j <;> cases b <;> simp_all
            · rintro ⟨h1, h2, h3 | h3⟩ <;> refine ⟨⟨h1, h2⟩, ?_⟩ <;>
                rcases h3 with ⟨ha, hb⟩ <;> rw [ha, hb] <;> cases b <;> rfl
          have hmat_uv : ∀ (v₁ v₂ : Fin (2 ^ n) → Bool),
              (productState W (n + 1) (arikanTransform (n + 1) ((arikanSplitEquiv n).symm (v₁, v₂)))).mat r₁ r₂ =
                (productState W n (arikanTransform n v₁)).mat (splitRegEquiv d n r₁).1 (splitRegEquiv d n r₂).1 *
                (productState W n (arikanTransform n v₂)).mat (splitRegEquiv d n r₁).2 (splitRegEquiv d n r₂).2 := by
            intro v₁ v₂
            have huv := Prod.mk.inj ((arikanSplitEquiv n).apply_symm_apply (v₁, v₂))
            rw [productState_arikan_succ, huv.1, huv.2]
          simp_rw [hcond, hmat_uv]
          simp only [Finset.sum_filter]
          rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro v₂ _
          by_cases h2 : prefixOf j v₂ = (ePref p₁).2
          · cases h4 : v₂ j
            · simp only [h2, h4, true_and, and_true, Bool.false_eq_true, and_false, or_false,
                ↓reduceIte, add_zero]
            · simp only [h2, h4, true_and, and_true, Bool.true_eq_false, and_false, false_or,
                ↓reduceIte, zero_add]
          · simp [h2]
        rw [hsum_split]
        have hpow_eq : ((2 : ℂ) ^ (2 ^ (n + 1) - 1))⁻¹ =
            (1 / 2 : ℂ) * (((2 : ℂ) ^ (2 ^ n - 1))⁻¹ * ((2 : ℂ) ^ (2 ^ n - 1))⁻¹) := by
          have hexp : 2 ^ (n + 1) - 1 = 1 + ((2 ^ n - 1) + (2 ^ n - 1)) := by
            have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
            omega
          rw [hexp, pow_add, pow_add, pow_one, mul_inv, mul_inv]
          ring
        rw [hpow_eq]
        cases b <;> simp <;> ring
      · have hne : ¬ ((ePref p₁).1 = (ePref p₂).1 ∧ (ePref p₁).2 = (ePref p₂).2) := by
          intro ⟨h1, h2⟩
          exact hp (ePref.injective (Prod.ext h1 h2))
        by_cases h1 : (ePref p₁).1 = (ePref p₂).1
        · have h2 : (ePref p₁).2 ≠ (ePref p₂).2 := fun h ↦ hne ⟨h1, h⟩
          simp [hp, h1, h2]
        · simp [hp, h1]
    · -- Odd case: `i = 2j + 1`, plus branch `W_j⁺`
      have hmod1 : i.val % 2 = 1 := by omega
      have hi_eq : i.val = 2 * j.val + 1 := by omega
      have htree : polarChannelTree W (n + 1) (bitPath (n + 1) i) =
          (polarChannelTree W n (bitPath n j)).plus := by
        have hbp : bitPath (n + 1) i = Fin.snoc (α := fun _ ↦ Bool) (bitPath n j) true := by
          simp [bitPath, bitPathFwd, j, hmod1]
        rw [hbp, polarChannelTree_snoc_true]
      let ePref : (Fin i.val → Bool) ≃ Bool × ((Fin j.val → Bool) × (Fin j.val → Bool)) :=
        { toFun := fun p ↦
            (p ⟨2 * j.val, by omega⟩,
             (fun k ↦ xor (p ⟨2 * k.val, by omega⟩) (p ⟨2 * k.val + 1, by omega⟩),
              fun k ↦ p ⟨2 * k.val + 1, by omega⟩))
          invFun := fun ⟨w, q₁, q₂⟩ k ↦
            if hk0 : k.val = 2 * j.val then w
            else if k.val % 2 = 0 then xor (q₁ ⟨k.val / 2, by have := k.isLt; omega⟩) (q₂ ⟨k.val / 2, by have := k.isLt; omega⟩)
            else q₂ ⟨k.val / 2, by have := k.isLt; omega⟩
          left_inv := fun p ↦ by
            funext k; dsimp only; split_ifs with hk0 hk
            · exact congr_arg p (Fin.ext (by dsimp; omega))
            · have h1 : (⟨2 * (k.val / 2), by have := k.isLt; omega⟩ : Fin i.val) = k := Fin.ext (by dsimp; omega)
              rw [h1]; cases p k <;> cases p ⟨2 * (k.val / 2) + 1, by have := k.isLt; omega⟩ <;> rfl
            · exact congr_arg p (Fin.ext (by dsimp; omega))
          right_inv := fun ⟨w, q₁, q₂⟩ ↦ by
            refine Prod.ext (by simp) (Prod.ext ?_ ?_)
            · funext k
              have h0 : 2 * k.val ≠ 2 * j.val := by have := k.isLt; omega
              have h0' : 2 * k.val + 1 ≠ 2 * j.val := by have := k.isLt; omega
              have h1 : (2 * k.val) % 2 = 0 := by omega
              have h2 : (2 * k.val + 1) % 2 ≠ 0 := by omega
              have h3 : (2 * k.val) / 2 = k.val := by omega
              have h4 : (2 * k.val + 1) / 2 = k.val := by omega
              simp only [h0, h0', h1, h2, ↓reduceDIte, ↓reduceIte, h3, h4]
              cases q₁ k <;> cases q₂ k <;> rfl
            · funext k
              have h0' : 2 * k.val + 1 ≠ 2 * j.val := by have := k.isLt; omega
              have h2 : (2 * k.val + 1) % 2 ≠ 0 := by omega
              have h4 : (2 * k.val + 1) / 2 = k.val := by omega
              simp only [h0', h2, ↓reduceDIte, ↓reduceIte, h4] }
      let eRaw : ((Fin i.val → Bool) × (Fin (2 ^ (n + 1)) → d)) ≃
          Bool × (polarChannelTree W n (bitPath n j)).dim × (polarChannelTree W n (bitPath n j)).dim :=
        { toFun := fun ⟨p, r⟩ ↦
            ((ePref p).1,
             (e_j ((ePref p).2.1, (splitRegEquiv d n r).1),
              e_j ((ePref p).2.2, (splitRegEquiv d n r).2)))
          invFun := fun ⟨w, a, b⟩ ↦
            (ePref.symm (w, ((e_j.symm a).1, (e_j.symm b).1)),
             (splitRegEquiv d n).symm ((e_j.symm a).2, (e_j.symm b).2))
          left_inv := fun ⟨p, r⟩ ↦ by
            simp only [Equiv.symm_apply_apply]
            exact Prod.ext (ePref.symm_apply_apply p) ((splitRegEquiv d n).symm_apply_apply r)
          right_inv := fun ⟨w, a, b⟩ ↦ by
            simp only [Equiv.apply_symm_apply, Prod.mk.eta] }
      let e : ((Fin i.val → Bool) × (Fin (2 ^ (n + 1)) → d)) ≃
          (polarChannelTree W (n + 1) (bitPath (n + 1) i)).dim :=
        eRaw.trans (Equiv.cast (congrArg BundledCQChannel.dim htree.symm))
      refine ⟨e, fun b ⟨p₁, r₁⟩ ⟨p₂, r₂⟩ ↦ ?_⟩
      have hcast : ((polarChannelTree W (n + 1) (bitPath (n + 1) i)).ch.out b).mat (e (p₁, r₁)) (e (p₂, r₂)) =
          (((polarChannelTree W n (bitPath n j)).plus).ch.out b).mat (eRaw (p₁, r₁)) (eRaw (p₂, r₂)) :=
        bundled_cast_mat htree b (eRaw (p₁, r₁)) (eRaw (p₂, r₂))
      rw [hcast]
      have hplus_entry : ∀ (b' : Bool) (w₁ w₂ : Bool)
          (x₁ y₁ x₂ y₂ : (polarChannelTree W n (bitPath n j)).dim),
          (((polarChannelTree W n (bitPath n j)).plus).ch.out b').mat (w₁, x₁, y₁) (w₂, x₂, y₂) =
            if w₁ = w₂ then
              (1 / 2 : ℂ) *
                ((polarChannelTree W n (bitPath n j)).ch.out (if w₁ = false then b' else !b')).mat x₁ x₂ *
                ((polarChannelTree W n (bitPath n j)).ch.out b').mat y₁ y₂
            else 0 := by
        intro b' w₁ w₂ x₁ y₁ x₂ y₂
        simp only [BundledCQChannel.plus, CQChannel.plusChannel, CQChannel.varCombine,
          DensityOp.midpoint, DensityOp.mix, DensityOp.tensor, CQChannel.ketBraBool,
          Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.of_apply,
          Complex.real_smul]
        cases w₁ <;> cases w₂ <;> simp <;> push_cast <;> ring
      simp only [eRaw, Equiv.coe_fn_mk]
      rw [hplus_entry]
      by_cases hp : p₁ = p₂
      · subst hp
        simp only [↓reduceIte, synthChannel, synthState, Matrix.of_apply]
        have hpref_split : ∀ u : Fin (2 ^ (n + 1)) → Bool,
            (prefixOf i u = p₁ ∧ u i = b) ↔
              (prefixOf j (arikanEven n u) = (ePref p₁).2.1 ∧
               prefixOf j (arikanOdd n u) = (ePref p₁).2.2 ∧
               arikanEven n u j = xor (ePref p₁).1 b ∧
               arikanOdd n u j = b) := by
          intro u
          have h2j1 : (⟨2 * j.val + 1, by omega⟩ : Fin (2 ^ (n + 1))) = i := Fin.ext (by dsimp; omega)
          have heq_ePref : ePref (prefixOf i u) =
              (u ⟨2 * j.val, by omega⟩, (prefixOf j (arikanEven n u), prefixOf j (arikanOdd n u))) := rfl
          constructor
          · rintro ⟨h1, h2⟩
            have h1' : ePref (prefixOf i u) = ePref p₁ := congr_arg ePref h1
            rw [heq_ePref] at h1'
            rcases Prod.mk.inj h1' with ⟨hw, hq⟩
            rcases Prod.mk.inj hq with ⟨hq1, hq2⟩
            refine ⟨hq1, hq2, ?_, ?_⟩
            · simp only [arikanEven, h2j1, h2, hw]; rfl
            · simp only [arikanOdd, h2j1, h2]
          · rintro ⟨h1, h2, h3, h4⟩
            have hui : u i = b := by rw [← h2j1]; exact h4
            have hw : u ⟨2 * j.val, by omega⟩ = (ePref p₁).1 := by
              simp only [arikanEven, h2j1, hui] at h3
              cases hu0 : u ⟨2 * j.val, by omega⟩ <;> cases hw0 : (ePref p₁).1 <;> cases b <;>
                simp only [hu0, hw0, Bool.xor_false, Bool.xor_true, Bool.false_xor, Bool.true_xor] at h3 ⊢ <;>
                first | rfl | contradiction
            refine ⟨ePref.injective (heq_ePref.trans (Prod.ext hw (Prod.ext h1 h2))), hui⟩
        have hsum_split : synthBlockMat W (n + 1) i p₁ b r₁ r₂ =
            synthBlockMat W n j (ePref p₁).2.1 (xor (ePref p₁).1 b) (splitRegEquiv d n r₁).1 (splitRegEquiv d n r₂).1 *
            synthBlockMat W n j (ePref p₁).2.2 b (splitRegEquiv d n r₁).2 (splitRegEquiv d n r₂).2 := by
          unfold synthBlockMat
          simp only [Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]
          have h1 := Equiv.sum_comp (arikanSplitEquiv n).symm
            (fun u : Fin (2 ^ (n + 1)) → Bool ↦
              if prefixOf i u = p₁ ∧ u i = b then
                (productState W (n + 1) (arikanTransform (n + 1) u)).mat r₁ r₂
              else 0)
          rw [Finset.sum_filter, ← h1]
          simp only [Fintype.sum_prod_type]
          have hcond : ∀ (v₁ v₂ : Fin (2 ^ n) → Bool),
              (prefixOf i ((arikanSplitEquiv n).symm (v₁, v₂)) = p₁ ∧
               (arikanSplitEquiv n).symm (v₁, v₂) i = b) ↔
                ((prefixOf j v₁ = (ePref p₁).2.1 ∧ v₁ j = xor (ePref p₁).1 b) ∧
                 (prefixOf j v₂ = (ePref p₁).2.2 ∧ v₂ j = b)) := by
            intro v₁ v₂
            have huv := Prod.mk.inj ((arikanSplitEquiv n).apply_symm_apply (v₁, v₂))
            rw [hpref_split, huv.1, huv.2]; tauto
          have hmat_uv : ∀ (v₁ v₂ : Fin (2 ^ n) → Bool),
              (productState W (n + 1) (arikanTransform (n + 1) ((arikanSplitEquiv n).symm (v₁, v₂)))).mat r₁ r₂ =
                (productState W n (arikanTransform n v₁)).mat (splitRegEquiv d n r₁).1 (splitRegEquiv d n r₂).1 *
                (productState W n (arikanTransform n v₂)).mat (splitRegEquiv d n r₁).2 (splitRegEquiv d n r₂).2 := by
            intro v₁ v₂
            have huv := Prod.mk.inj ((arikanSplitEquiv n).apply_symm_apply (v₁, v₂))
            rw [productState_arikan_succ, huv.1, huv.2]
          simp_rw [hcond, hmat_uv]
          simp only [Finset.sum_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro v₂ _
          by_cases h2 : prefixOf j v₂ = (ePref p₁).2.2 ∧ v₂ j = b
          · simp only [h2, and_true, ↓reduceIte]
          · simp [h2]
        have hpow_eq : ((2 : ℂ) ^ (2 ^ (n + 1) - 1))⁻¹ =
            (1 / 2 : ℂ) * (((2 : ℂ) ^ (2 ^ n - 1))⁻¹ * ((2 : ℂ) ^ (2 ^ n - 1))⁻¹) := by
          have hexp : 2 ^ (n + 1) - 1 = 1 + ((2 ^ n - 1) + (2 ^ n - 1)) := by
            have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
            omega
          rw [hexp, pow_add, pow_add, pow_one, mul_inv, mul_inv]
          ring
        rw [he_j, he_j, hsum_split, hpow_eq]
        simp only [synthChannel, synthState, Matrix.of_apply, ↓reduceIte]
        cases hwv : (ePref p₁).1 <;> cases b <;> simp <;> ring
      · have hne : ¬ ((ePref p₁).1 = (ePref p₂).1 ∧ (ePref p₁).2.1 = (ePref p₂).2.1 ∧
            (ePref p₁).2.2 = (ePref p₂).2.2) := by
          intro ⟨h1, h2, h3⟩
          exact hp (ePref.injective (Prod.ext h1 (Prod.ext h2 h3)))
        simp only [synthChannel, synthState, Matrix.of_apply, hp, ↓reduceIte]
        by_cases hw : (ePref p₁).1 = (ePref p₂).1
        · simp only [hw, ↓reduceIte]
          rw [he_j, he_j]
          simp only [synthChannel, synthState, Matrix.of_apply]
          by_cases h1 : (ePref p₁).2.1 = (ePref p₂).2.1
          · have h2 : (ePref p₁).2.2 ≠ (ePref p₂).2.2 := fun h ↦ hne ⟨hw, h1, h⟩
            simp [h1, h2]
          · simp [h1]
        · simp [hw]

/-- Exact equality of conditional entropy between the explicit synthesized channel `W_n^{(i)}`
and `polarChannelTree W n (bitPath n i)`. -/
theorem synthChannel_condEntropy_eq (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n)) :
    (synthChannel W n i).condEntropy = polarCondEntropy W n (bitPath n i) := by
  obtain ⟨e, he⟩ := synthChannel_reindex_polarChannelTree W n i
  unfold polarCondEntropy
  unfold CQChannel.condEntropy qjs
  have hmid : ∀ x y,
      (DensityOp.midpoint ((polarChannelTree W n (bitPath n i)).ch.out false)
        ((polarChannelTree W n (bitPath n i)).ch.out true)).mat (e x) (e y) =
        (DensityOp.midpoint ((synthChannel W n i).out false) ((synthChannel W n i).out true)).mat x y := by
    intro x y
    simp only [DensityOp.midpoint, DensityOp.mix, Matrix.add_apply, Matrix.smul_apply, he]
  have hS0 := vonNeumannEntropy_of_reindex e ((synthChannel W n i).out false)
    ((polarChannelTree W n (bitPath n i)).ch.out false) (he false)
  have hS1 := vonNeumannEntropy_of_reindex e ((synthChannel W n i).out true)
    ((polarChannelTree W n (bitPath n i)).ch.out true) (he true)
  have hSm := vonNeumannEntropy_of_reindex e
    (DensityOp.midpoint ((synthChannel W n i).out false) ((synthChannel W n i).out true))
    (DensityOp.midpoint ((polarChannelTree W n (bitPath n i)).ch.out false)
      ((polarChannelTree W n (bitPath n i)).ch.out true)) hmid
  linarith

/-- Exact equality of Bhattacharyya / root fidelity between the explicit synthesized channel
`W_n^{(i)}` and `polarChannelTree W n (bitPath n i)`. -/
theorem synthChannel_fidelityParam_eq (W : CQChannel d) (n : ℕ) (i : Fin (2 ^ n)) :
    (synthChannel W n i).fidelityParam = polarFidelity W n (bitPath n i) := by
  obtain ⟨e, he⟩ := synthChannel_reindex_polarChannelTree W n i
  unfold CQChannel.fidelityParam polarFidelity
  exact (rootFidelity_of_reindex e ((synthChannel W n i).out false) ((synthChannel W n i).out true)
    ((polarChannelTree W n (bitPath n i)).ch.out false)
    ((polarChannelTree W n (bitPath n i)).ch.out true) (he false) (he true)).symm

end ProductAndArikan

end PolarCodes
