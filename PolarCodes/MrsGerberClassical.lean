/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.MrsGerberHybrid

/-!
# Hybrid Quantum Mrs. Gerber's Lemma — Classical Branch (Theorem 1.2(a))

This module formalizes the classical branch of Theorem 1.2(a) from Section 4 of the manuscript:
1. Simultaneous unitary diagonalization of commuting Hermitian matrices
   (`simultaneous_diagonalization`).
2. Block-diagonal von Neumann entropy decomposition (`vonNeumannEntropy_block_diag`).
3. **Theorem 1.2(a) — Classical Branch** (`theorem_1_2a_classical`): for arbitrary `W₁` and
   classical `W₂`, `H(W₁ ⊠ W₂) ≥ gc(H₁, H₂) ≥ gq(H₁, H₂)`.
-/

open Matrix BigOperators Real Filter Topology Set
open scoped ComplexOrder

namespace PolarCodes

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-- Simultaneous unitary diagonalization of two commuting Hermitian matrices `A, B`. -/
lemma simultaneous_diagonalization {A B : Matrix d d ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hcomm : A * B = B * A) :
    ∃ (U : Matrix.unitaryGroup d ℂ) (α β : d → ℝ),
      star (U : Matrix d d ℂ) * A * (U : Matrix d d ℂ) = Matrix.diagonal (Complex.ofReal ∘ α) ∧
      star (U : Matrix d d ℂ) * B * (U : Matrix d d ℂ) = Matrix.diagonal (Complex.ofReal ∘ β) := by
  set U₀ := hA.eigenvectorUnitary
  set α := hA.eigenvalues
  set B' : Matrix d d ℂ := star (U₀ : Matrix d d ℂ) * B * (U₀ : Matrix d d ℂ)
  have hU₀_mul : (U₀ : Matrix d d ℂ) * star (U₀ : Matrix d d ℂ) = 1 := Unitary.coe_mul_star_self U₀
  have hU₀_star : star (U₀ : Matrix d d ℂ) * (U₀ : Matrix d d ℂ) = 1 := Unitary.coe_star_mul_self U₀
  have hA_diag : star (U₀ : Matrix d d ℂ) * A * (U₀ : Matrix d d ℂ) = Matrix.diagonal (Complex.ofReal ∘ α) := by
    have hspec : A = (U₀ : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ α) * star (U₀ : Matrix d d ℂ) := by
      simpa [U₀, α, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
    conv_lhs => rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (U₀ : Matrix d d ℂ)) (U₀ : Matrix d d ℂ), hU₀_star,
      Matrix.one_mul, Matrix.mul_one]
  have hB'_herm : B'.IsHermitian := by
    rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose]
    simp only [B', star_mul, star_star, Matrix.mul_assoc]
    have hBs : star B = B := by rw [Matrix.star_eq_conjTranspose]; exact hB.eq
    rw [hBs]
  have hB'_block : ∀ i j : d, α i ≠ α j → B' i j = 0 := by
    intro i j hij
    have hcomm' : Matrix.diagonal (Complex.ofReal ∘ α) * B' = B' * Matrix.diagonal (Complex.ofReal ∘ α) := by
      rw [← hA_diag]
      simp only [B', Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U₀ : Matrix d d ℂ) (star (U₀ : Matrix d d ℂ)), hU₀_mul,
        Matrix.one_mul, ← Matrix.mul_assoc A B, hcomm, Matrix.mul_assoc B A]
      conv_rhs =>
        rw [← Matrix.mul_assoc (U₀ : Matrix d d ℂ) (star (U₀ : Matrix d d ℂ)), hU₀_mul,
          Matrix.one_mul]
    have hij_eq := congr_fun (congr_fun hcomm' i) j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Function.comp_apply] at hij_eq
    have hsub : ((α i : ℂ) - (α j : ℂ)) * B' i j = 0 := by linear_combination hij_eq
    have hne : (α i : ℂ) - (α j : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.mpr hij
    exact (mul_eq_zero.mp hsub).resolve_left hne
  let Bblk : ∀ c : ℝ, Matrix {i : d // α i = c} {i : d // α i = c} ℂ :=
    fun c ↦ Matrix.of fun i j ↦ B' i.1 j.1
  have hBblk_herm : ∀ c : ℝ, (Bblk c).IsHermitian := by
    intro c; ext i j
    have hh := congr_fun (congr_fun hB'_herm.eq i.1) j.1
    simpa [Bblk, Matrix.conjTranspose_apply] using hh
  let V : Matrix d d ℂ := Matrix.of fun i j ↦
    if h : α i = α j then
      ((hBblk_herm (α i)).eigenvectorUnitary :
        Matrix {k : d // α k = α i} {k : d // α k = α i} ℂ) ⟨i, rfl⟩ ⟨j, h.symm⟩
    else 0
  have hV_val : ∀ (c : ℝ) (a b : d) (hac : α a = c) (hbc : α b = c),
      V a b = ((hBblk_herm c).eigenvectorUnitary :
        Matrix {x : d // α x = c} {x : d // α x = c} ℂ) ⟨a, hac⟩ ⟨b, hbc⟩ := by
    intro c a b hac hbc
    have hab : α a = α b := hac.trans hbc.symm
    simp only [V, Matrix.of_apply, hab, ↓reduceDIte]
    subst hac
    rfl
  have hV_unit : V ∈ Matrix.unitaryGroup d ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply]
    by_cases hij : α i = α j
    · have hsum : (∑ k : d, star (V k i) * V k j) =
          ∑ k : {k : d // α k = α i},
            star (((hBblk_herm (α i)).eigenvectorUnitary :
              Matrix {k : d // α k = α i} {k : d // α k = α i} ℂ) k ⟨i, rfl⟩) *
              (((hBblk_herm (α i)).eigenvectorUnitary :
                Matrix {k : d // α k = α i} {k : d // α k = α i} ℂ) k ⟨j, hij.symm⟩) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : d ↦ α k = α i)]
        have hzero : ∑ k ∈ Finset.univ.filter (fun k : d ↦ ¬ α k = α i), star (V k i) * V k j = 0 := by
          apply Finset.sum_eq_zero; intro k hk
          have hne : α k ≠ α i := (Finset.mem_filter.mp hk).2
          simp [V, hne]
        rw [hzero, add_zero]
        refine Finset.sum_bij (fun k hk ↦ (⟨k, (Finset.mem_filter.mp hk).2⟩ : {k : d // α k = α i}))
          (fun _ _ ↦ Finset.mem_univ _)
          (fun _ _ _ _ h ↦ congr_arg Subtype.val h)
          (fun b _ ↦ ⟨b.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, Subtype.ext rfl⟩)
          (fun k hk ↦ ?_)
        have hki : α k = α i := (Finset.mem_filter.mp hk).2
        rw [hV_val (α i) k i hki rfl, hV_val (α i) k j hki hij.symm]
      rw [hsum]
      have hu := congr_fun (congr_fun (Unitary.coe_star_mul_self (hBblk_herm (α i)).eigenvectorUnitary)
        ⟨i, rfl⟩) ⟨j, hij.symm⟩
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at hu
      rw [hu]
      by_cases h : i = j
      · subst h; simp
      · have hne : (⟨i, rfl⟩ : {k : d // α k = α i}) ≠ ⟨j, hij.symm⟩ := fun heq ↦ h (congr_arg Subtype.val heq)
        simp [h, hne]
    · have hne_ij : i ≠ j := fun h ↦ hij (by rw [h])
      simp only [hne_ij, ↓reduceIte]
      apply Finset.sum_eq_zero; intro k _
      by_cases hk : α k = α i
      · have hk' : α k ≠ α j := by rw [hk]; exact hij
        simp only [V, Matrix.of_apply, dif_neg hk', mul_zero]
      · simp only [V, Matrix.of_apply, dif_neg hk, star_zero, zero_mul]
  let V_u : Matrix.unitaryGroup d ℂ := ⟨V, hV_unit⟩
  let U : Matrix.unitaryGroup d ℂ := U₀ * V_u
  let β : d → ℝ := fun i ↦ (hBblk_herm (α i)).eigenvalues ⟨i, rfl⟩
  refine ⟨U, α, β, ?_, ?_⟩
  · have hcomm_V : Matrix.diagonal (Complex.ofReal ∘ α) * V = V * Matrix.diagonal (Complex.ofReal ∘ α) := by
      ext i j
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Function.comp_apply, V, Matrix.of_apply]
      split_ifs with h
      · rw [mul_comm]; congr 1; exact congr_arg Complex.ofReal h
      · simp
    calc star (U : Matrix d d ℂ) * A * (U : Matrix d d ℂ)
        = star V * (star (U₀ : Matrix d d ℂ) * A * (U₀ : Matrix d d ℂ)) * V := by
            have hU_coe : (U : Matrix d d ℂ) = (U₀ : Matrix d d ℂ) * V := rfl
            rw [hU_coe, star_mul]; simp only [Matrix.mul_assoc]
      _ = star V * (Matrix.diagonal (Complex.ofReal ∘ α) * V) := by rw [hA_diag, Matrix.mul_assoc]
      _ = (star V * V) * Matrix.diagonal (Complex.ofReal ∘ α) := by rw [hcomm_V, Matrix.mul_assoc]
      _ = Matrix.diagonal (Complex.ofReal ∘ α) := by
            have hVs : star V * V = 1 := Unitary.coe_star_mul_self V_u
            rw [hVs, Matrix.one_mul]
  · have hVB'V : star V * B' * V = Matrix.diagonal (Complex.ofReal ∘ β) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply, Function.comp_apply]
      by_cases hij : α i = α j
      · have hsum : (∑ l : d, (∑ k : d, star (V k i) * B' k l) * V l j) =
            ∑ l : {x : d // α x = α i},
              (∑ k : {x : d // α x = α i},
                star (((hBblk_herm (α i)).eigenvectorUnitary :
                  Matrix {x : d // α x = α i} {x : d // α x = α i} ℂ) k ⟨i, rfl⟩) *
                  Bblk (α i) k l) *
                (((hBblk_herm (α i)).eigenvectorUnitary :
                  Matrix {x : d // α x = α i} {x : d // α x = α i} ℂ) l ⟨j, hij.symm⟩) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : d ↦ α l = α i)]
          have hzero_l : ∑ l ∈ Finset.univ.filter (fun l : d ↦ ¬ α l = α i),
              (∑ k : d, star (V k i) * B' k l) * V l j = 0 := by
            apply Finset.sum_eq_zero; intro l hl
            have hne : α l ≠ α j := by
              intro h; exact (Finset.mem_filter.mp hl).2 (h.trans hij.symm)
            simp [V, hne]
          rw [hzero_l, add_zero]
          refine Finset.sum_bij (fun l hl ↦ (⟨l, (Finset.mem_filter.mp hl).2⟩ : {x : d // α x = α i}))
            (fun _ _ ↦ Finset.mem_univ _)
            (fun _ _ _ _ h ↦ congr_arg Subtype.val h)
            (fun b _ ↦ ⟨b.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, Subtype.ext rfl⟩)
            (fun l hl ↦ ?_)
          have hli : α l = α i := (Finset.mem_filter.mp hl).2
          rw [hV_val (α i) l j hli hij.symm]
          congr 1
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : d ↦ α k = α i)]
          have hzero_k : ∑ k ∈ Finset.univ.filter (fun k : d ↦ ¬ α k = α i),
              star (V k i) * B' k l = 0 := by
            apply Finset.sum_eq_zero; intro k hk
            have hne : α k ≠ α i := (Finset.mem_filter.mp hk).2
            simp [V, hne]
          rw [hzero_k, add_zero]
          refine Finset.sum_bij (fun k hk ↦ (⟨k, (Finset.mem_filter.mp hk).2⟩ : {x : d // α x = α i}))
            (fun _ _ ↦ Finset.mem_univ _)
            (fun _ _ _ _ h ↦ congr_arg Subtype.val h)
            (fun b _ ↦ ⟨b.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, Subtype.ext rfl⟩)
            (fun k hk ↦ ?_)
          have hki : α k = α i := (Finset.mem_filter.mp hk).2
          rw [hV_val (α i) k i hki rfl]
          rfl
        rw [hsum]
        have hdiag_blk : star ((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) * Bblk (α i) *
            ((hBblk_herm (α i)).eigenvectorUnitary : Matrix _ _ ℂ) =
            Matrix.diagonal (Complex.ofReal ∘ (hBblk_herm (α i)).eigenvalues) := by
          let Ublk : Matrix {x : d // α x = α i} {x : d // α x = α i} ℂ :=
            ((hBblk_herm (α i)).eigenvectorUnitary :
              Matrix {x : d // α x = α i} {x : d // α x = α i} ℂ)
          have hspec : Bblk (α i) = Ublk *
              Matrix.diagonal (Complex.ofReal ∘ (hBblk_herm (α i)).eigenvalues) * star Ublk := by
            simpa [Ublk, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using
              (hBblk_herm (α i)).spectral_theorem
          have hVstar : star Ublk * Ublk = 1 := Unitary.coe_star_mul_self (hBblk_herm (α i)).eigenvectorUnitary
          calc star Ublk * Bblk (α i) * Ublk
              = star Ublk * (Ublk * Matrix.diagonal (Complex.ofReal ∘ (hBblk_herm (α i)).eigenvalues) * star Ublk) * Ublk :=
                  congrArg (fun X ↦ star Ublk * X * Ublk) hspec
            _ = (star Ublk * Ublk) * Matrix.diagonal (Complex.ofReal ∘ (hBblk_herm (α i)).eigenvalues) * (star Ublk * Ublk) := by
                  simp only [Matrix.mul_assoc]
            _ = Matrix.diagonal (Complex.ofReal ∘ (hBblk_herm (α i)).eigenvalues) := by
                  rw [hVstar, Matrix.one_mul, Matrix.mul_one]
        have hentry := congr_fun (congr_fun hdiag_blk ⟨i, rfl⟩) ⟨j, hij.symm⟩
        simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply, Function.comp_apply] at hentry
        rw [hentry]
        by_cases h : i = j
        · subst h; simp [β]
        · have hne : (⟨i, rfl⟩ : {x : d // α x = α i}) ≠ ⟨j, hij.symm⟩ := fun heq ↦ h (congr_arg Subtype.val heq)
          simp [h, hne]
      · have hne_ij : i ≠ j := fun h ↦ hij (by rw [h])
        simp only [hne_ij, ↓reduceIte]
        apply Finset.sum_eq_zero; intro l _
        by_cases hlj : α l = α j
        · have hzero : ∑ k : d, star (V k i) * B' k l = 0 := by
            apply Finset.sum_eq_zero; intro k _
            by_cases hki : α k = α i
            · have hkl : α k ≠ α l := by rw [hki, hlj]; exact hij
              rw [hB'_block k l hkl, mul_zero]
            · simp only [V, Matrix.of_apply, dif_neg hki, star_zero, zero_mul]
          rw [hzero, zero_mul]
        · simp only [V, Matrix.of_apply, dif_neg hlj, mul_zero]
    calc star (U : Matrix d d ℂ) * B * (U : Matrix d d ℂ)
        = star V * B' * V := by
            have hU_coe : (U : Matrix d d ℂ) = (U₀ : Matrix d d ℂ) * V := rfl
            rw [hU_coe, star_mul]; simp only [B', Matrix.mul_assoc]
      _ = Matrix.diagonal (Complex.ofReal ∘ β) := hVB'V

/-- Entropy of a block-diagonal density operator `ρ = ⨁_y w_y τ_y` on `d₁ × d₂`:
`S(ρ) = (∑ y, negMulLog (w y)) / log 2 + ∑ y, w y * S(τ y)`. -/
private lemma vonNeumannEntropy_block_diag {w : d₂ → ℝ} (hw_nn : ∀ y, 0 ≤ w y)
    (τ : d₂ → DensityOp d₁) (ρ : DensityOp (d₁ × d₂))
    (hρ : ∀ i₁ j₁ y₁ y₂, ρ.mat (i₁, y₁) (j₁, y₂) = if y₁ = y₂ then (w y₁ : ℂ) * (τ y₁).mat i₁ j₁ else 0) :
    vonNeumannEntropy ρ =
      (∑ y : d₂, Real.negMulLog (w y)) / Real.log 2 + ∑ y : d₂, w y * vonNeumannEntropy (τ y) := by
  let U : Matrix (d₁ × d₂) (d₁ × d₂) ℂ := Matrix.of fun p q ↦
    if p.2 = q.2 then ((τ p.2).eigUnitary : Matrix d₁ d₁ ℂ) p.1 q.1 else 0
  let lam : d₁ × d₂ → ℝ := fun p ↦ w p.2 * (τ p.2).eigvals p.1
  have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext p; simp
  have hU_star : star U * U = 1 := by
    ext ⟨i₁, y₁⟩ ⟨j₁, y₂⟩
    simp only [U, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type_right]
    by_cases hy : y₁ = y₂
    · subst hy
      rw [Finset.sum_eq_single y₁]
      · simp only [↓reduceIte, Prod.mk.injEq, and_true]
        have hu := congr_fun (congr_fun (Unitary.coe_star_mul_self (τ y₁).eigUnitary) i₁) j₁
        simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using hu
      · intro y _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [Prod.mk.injEq, hy, and_false, ↓reduceIte]
      apply Finset.sum_eq_zero; intro y _
      apply Finset.sum_eq_zero; intro i _
      by_cases h1 : y = y₁
      · subst h1; simp [hy]
      · simp [h1]
  have hρ_eq : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ lam) * star U := by
    ext ⟨i₁, y₁⟩ ⟨j₁, y₂⟩
    rw [hρ i₁ j₁ y₁ y₂]
    simp only [U, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.diagonal_apply,
      Function.comp_apply, Fintype.sum_prod_type_right, lam]
    by_cases hy : y₁ = y₂
    · subst hy
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single y₁]
      · simp only [↓reduceIte]
        have hspec := congr_fun (congr_fun (τ y₁).isHermitian.spectral_theorem i₁) j₁
        simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
          Matrix.star_apply, Function.comp_apply] at hspec
        rw [hspec]
        simp only [DensityOp.eigUnitary, DensityOp.eigvals, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.sum_eq_single y₁]
        · simp only [Prod.mk.injEq, and_true, mul_ite, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, ↓reduceIte, Complex.ofReal_mul,
            show (RCLike.ofReal : ℝ → ℂ) = Complex.ofReal from rfl]
          ring
        · intro z _ hz; simp [Ne.symm hz]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro y _ hne
        apply Finset.sum_eq_zero; intro k _
        simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [hy, ↓reduceIte]
      symm
      apply Finset.sum_eq_zero; intro y _
      apply Finset.sum_eq_zero; intro k _
      by_cases h2 : y₂ = y
      · subst h2
        have hsum0 : ∑ z : d₂, ∑ l : d₁,
            (if y₁ = z then ((τ y₁).eigUnitary : Matrix d₁ d₁ ℂ) i₁ l else 0) *
              (if (l, z) = (k, y₂) then ((w z * (τ z).eigvals l : ℝ) : ℂ) else 0) = 0 := by
          apply Finset.sum_eq_zero; intro z _
          apply Finset.sum_eq_zero; intro l _
          by_cases hz : y₁ = z
          · subst hz; simp [hy]
          · simp [hz]
        rw [hsum0, zero_mul]
      · simp [h2]
  have hcp : ρ.mat.charpoly = (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
    rw [hρ_eq, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU_star, Matrix.one_mul]
  unfold vonNeumannEntropy DensityOp.eigvals
  have hspec_sum : ∑ p : d₁ × d₂, Real.negMulLog (ρ.isHermitian.eigenvalues p) =
      ∑ p : d₁ × d₂, Real.negMulLog (lam p) := by
    trans ∑ p : d₁ × d₂, Real.negMulLog (hD_herm.eigenvalues p)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow ρ.isHermitian hD_herm (k := 0) (l := 0)
        (by rw [pow_zero, mul_one, mul_one, hcp]) (by simp [Real.negMulLog])
    · exact spectral_sum_diagonal lam hD_herm (by simp [Real.negMulLog])
  rw [hspec_sum, Fintype.sum_prod_type_right]
  have hinner : ∀ y : d₂, ∑ i : d₁, Real.negMulLog (w y * (τ y).eigvals i) =
      Real.negMulLog (w y) + w y * ∑ i : d₁, Real.negMulLog ((τ y).eigvals i) := by
    intro y
    simp_rw [Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      (τ y).sum_eigvals, one_mul]
  simp_rw [lam, hinner, Finset.sum_add_distrib, add_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl; intro y _
  rw [← Finset.sum_div]; unfold DensityOp.eigvals; ring

/-- **Theorem 1.2(a) (Classical Hybrid Q-MGL)**:
For any binary-input c-q channel `W₁` and any classical channel `W₂` (commuting outputs),
`H(W₁ ⊠ W₂) ≥ gc(H(W₁), H(W₂)) ≥ gq(H(W₁), H(W₂))`. -/
theorem theorem_1_2a_classical (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) (hW₂ : W₂.IsClassical) :
    gc W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy ∧
    gq W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy := by
  obtain ⟨U, p₀, p₁, hdiag₀, hdiag₁⟩ :=
    simultaneous_diagonalization (W₂.out false).isHermitian (W₂.out true).isHermitian hW₂
  have hU_mul : (U : Matrix d₂ d₂ ℂ) * star (U : Matrix d₂ d₂ ℂ) = 1 := Unitary.coe_mul_star_self U
  have hU_star : star (U : Matrix d₂ d₂ ℂ) * (U : Matrix d₂ d₂ ℂ) = 1 := Unitary.coe_star_mul_self U
  have hp₀_nn : ∀ y : d₂, 0 ≤ p₀ y := by
    intro y
    have hpsd : (Matrix.diagonal (Complex.ofReal ∘ p₀)).PosSemidef := by
      rw [← hdiag₀]
      simpa [Matrix.star_eq_conjTranspose] using (W₂.out false).posSemidef.conjTranspose_mul_mul_same (U : Matrix d₂ d₂ ℂ)
    exact (Complex.le_def.mp ((Matrix.posSemidef_diagonal_iff.mp hpsd) y)).1
  have hp₁_nn : ∀ y : d₂, 0 ≤ p₁ y := by
    intro y
    have hpsd : (Matrix.diagonal (Complex.ofReal ∘ p₁)).PosSemidef := by
      rw [← hdiag₁]
      simpa [Matrix.star_eq_conjTranspose] using (W₂.out true).posSemidef.conjTranspose_mul_mul_same (U : Matrix d₂ d₂ ℂ)
    exact (Complex.le_def.mp ((Matrix.posSemidef_diagonal_iff.mp hpsd) y)).1
  have hp₀_sum : ∑ y : d₂, p₀ y = 1 := by
    have htr : (Matrix.diagonal (Complex.ofReal ∘ p₀)).trace = 1 := by
      rw [← hdiag₀, Matrix.trace_mul_cycle, hU_mul, Matrix.one_mul, (W₂.out false).trace_one]
    have hre := congr_arg Complex.re htr
    simpa [Matrix.trace, Matrix.diag, Complex.re_sum] using hre
  have hp₁_sum : ∑ y : d₂, p₁ y = 1 := by
    have htr : (Matrix.diagonal (Complex.ofReal ∘ p₁)).trace = 1 := by
      rw [← hdiag₁, Matrix.trace_mul_cycle, hU_mul, Matrix.one_mul, (W₂.out true).trace_one]
    have hre := congr_arg Complex.re htr
    simpa [Matrix.trace, Matrix.diag, Complex.re_sum] using hre
  let W₂d : CQChannel d₂ := { out := fun b ↦ DensityOp.conjUnitary (star U) (W₂.out b) }
  have hW₂d_0 : (W₂d.out false).mat = Matrix.diagonal (Complex.ofReal ∘ p₀) := by
    simpa [W₂d, DensityOp.conjUnitary, star_star] using hdiag₀
  have hW₂d_1 : (W₂d.out true).mat = Matrix.diagonal (Complex.ofReal ∘ p₁) := by
    simpa [W₂d, DensityOp.conjUnitary, star_star] using hdiag₁
  have hH₂_eq : W₂d.condEntropy = W₂.condEntropy :=
    condEntropy_eq_of_conjUnitary (star U) rfl rfl
  let IU : Matrix.unitaryGroup (d₁ × d₂) ℂ :=
    ⟨Matrix.kroneckerMap (· * ·) (1 : Matrix d₁ d₁ ℂ) (star (U : Matrix d₂ d₂ ℂ)), by
      rw [Matrix.mem_unitaryGroup_iff']
      ext ⟨i₁, y₁⟩ ⟨j₁, y₂⟩
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
        Fintype.sum_prod_type]
      rw [Finset.sum_eq_single i₁]
      · simp only [↓reduceIte, one_mul, star_one, star_star]
        by_cases hi : i₁ = j₁
        · subst hi; simp only [↓reduceIte, one_mul, Prod.mk.injEq, true_and]
          have hu := congr_fun (congr_fun hU_mul y₁) y₂
          simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using hu
        · simp [hi]
      · intro k _ hk; simp [hk]
      · intro h; exact absurd (Finset.mem_univ _) h⟩
  have hIU_kron : ∀ (A : Matrix d₁ d₁ ℂ) (B : Matrix d₂ d₂ ℂ),
      (IU : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) * Matrix.kroneckerMap (· * ·) A B *
        star (IU : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) =
      Matrix.kroneckerMap (· * ·) A (star (U : Matrix d₂ d₂ ℂ) * B * (U : Matrix d₂ d₂ ℂ)) := by
    intro A B
    ext ⟨i₁, y₁⟩ ⟨j₁, y₂⟩
    simp only [IU, Matrix.mul_apply, Matrix.star_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_eq_single j₁]
    · simp only [↓reduceIte, one_mul, star_one, star_star]
      have hinner : ∀ z : d₂,
          (∑ k : d₁, ∑ w : d₂,
            (if i₁ = k then 1 else 0) * star ((U : Matrix d₂ d₂ ℂ) w y₁) * (A k j₁ * B w z)) =
          A i₁ j₁ * (∑ w : d₂, star ((U : Matrix d₂ d₂ ℂ) w y₁) * B w z) := by
        intro z
        rw [Finset.sum_eq_single i₁]
        · simp only [↓reduceIte, one_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro w _; ring
        · intro k _ hk; simp [Ne.symm hk]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [hinner]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro z _
      simp_rw [mul_assoc]
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hchk_eq : (CQChannel.checkCombine W₁ W₂d).condEntropy = (CQChannel.checkCombine W₁ W₂).condEntropy := by
    have hUs : ((star U : Matrix.unitaryGroup d₂ ℂ) : Matrix d₂ d₂ ℂ) = star (U : Matrix d₂ d₂ ℂ) := rfl
    apply condEntropy_eq_of_conjUnitary IU
    · simp only [CQChannel.checkCombine, W₂d, DensityOp.conjUnitary, DensityOp.midpoint, DensityOp.mix,
        DensityOp.tensor, Bool.not_false, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul, hUs, star_star, hIU_kron]
    · simp only [CQChannel.checkCombine, W₂d, DensityOp.conjUnitary, DensityOp.midpoint, DensityOp.mix,
        DensityOp.tensor, Bool.not_true, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul, hUs, star_star, hIU_kron]
  let w : d₂ → ℝ := fun y ↦ (p₀ y + p₁ y) / 2
  have hw_nn : ∀ y : d₂, 0 ≤ w y := fun y ↦ by dsimp [w]; linarith [hp₀_nn y, hp₁_nn y]
  have hw_sum : ∑ y : d₂, w y = 1 := by
    simp only [w, ← Finset.sum_div, Finset.sum_add_distrib, hp₀_sum, hp₁_sum]; norm_num
  let q_raw : d₂ → ℝ := fun y ↦ if w y = 0 then 0 else p₁ y / (2 * w y)
  have hq_raw0 : ∀ y : d₂, 0 ≤ q_raw y := by
    intro y; dsimp [q_raw]; split_ifs with h
    · exact le_rfl
    · exact div_nonneg (hp₁_nn y) (by linarith [hw_nn y])
  have hq_raw1 : ∀ y : d₂, q_raw y ≤ 1 := by
    intro y; dsimp [q_raw]; split_ifs with h
    · norm_num
    · have hw_pos : 0 < w y := lt_of_le_of_ne (hw_nn y) (Ne.symm h)
      rw [div_le_one (by linarith)]
      dsimp [w]; linarith [hp₀_nn y]
  let q : d₂ → ℝ := fun y ↦ min (q_raw y) (1 - q_raw y)
  have hq0 : ∀ y : d₂, 0 ≤ q y := fun y ↦ le_min (hq_raw0 y) (by linarith [hq_raw1 y])
  have hq1 : ∀ y : d₂, q y ≤ 1 / 2 := fun y ↦ by
    rcases le_or_gt (q_raw y) (1 / 2) with h | h
    · exact le_trans (min_le_left _ _) h
    · exact le_trans (min_le_right _ _) (by linarith)
  have hH₂_decomp : W₂d.condEntropy = ∑ y : d₂, w y * h2 (q y) := by
    have hS_diag : ∀ (v : d₂ → ℝ) (ρ : DensityOp d₂), ρ.mat = Matrix.diagonal (Complex.ofReal ∘ v) →
        vonNeumannEntropy ρ = (∑ y : d₂, Real.negMulLog (v y)) / Real.log 2 := by
      intro v ρ hmat
      have hD : (Matrix.diagonal (Complex.ofReal ∘ v)).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext y; simp
      unfold vonNeumannEntropy DensityOp.eigvals
      congr 1
      trans ∑ y : d₂, Real.negMulLog (hD.eigenvalues y)
      · exact spectral_sum_eq_of_charpoly_mul_X_pow ρ.isHermitian hD (k := 0) (l := 0)
          (by rw [pow_zero, mul_one, mul_one, hmat]) (by simp [Real.negMulLog])
      · exact spectral_sum_diagonal v hD (by simp [Real.negMulLog])
    have hS0 := hS_diag p₀ (W₂d.out false) hW₂d_0
    have hS1 := hS_diag p₁ (W₂d.out true) hW₂d_1
    have hSm := hS_diag w (DensityOp.midpoint (W₂d.out false) (W₂d.out true)) (by
      ext i j
      simp only [DensityOp.midpoint, DensityOp.mix, hW₂d_0, hW₂d_1, Matrix.add_apply, Matrix.smul_apply,
        Matrix.diagonal_apply, Function.comp_apply, Complex.real_smul, w]
      split_ifs <;> simp <;> push_cast <;> ring)
    unfold CQChannel.condEntropy qjs
    rw [hS0, hS1, hSm]
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hterm : ∀ y : d₂,
        w y * h2 (q y) =
          w y - (Real.negMulLog (w y) - (Real.negMulLog (p₀ y) + Real.negMulLog (p₁ y)) / 2) / Real.log 2 := by
      intro y
      by_cases hw0 : w y = 0
      · have hp0 : p₀ y = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y, hp₁_nn y]
        have hp1 : p₁ y = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y, hp₁_nn y]
        simp [hw0, hp0, hp1, Real.negMulLog]
      · have hw_pos : 0 < w y := lt_of_le_of_ne (hw_nn y) (Ne.symm hw0)
        have hq_h2 : h2 (q y) = h2 (q_raw y) := by
          dsimp [q]; rcases le_total (q_raw y) (1 - q_raw y) with h | h
          · rw [min_eq_left h]
          · rw [min_eq_right h, h2_symm]
        rw [hq_h2, h2_eq_negMulLog]
        have hp1_eq : p₁ y = (2 * w y) * q_raw y := by
          dsimp [q_raw]; rw [if_neg hw0]; field_simp [ne_of_gt hw_pos]
        have hp0_eq : p₀ y = (2 * w y) * (1 - q_raw y) := by
          have : p₀ y + p₁ y = 2 * w y := by dsimp [w]; ring
          linarith
        have h2w : Real.negMulLog (2 * w y) = -2 * w y * Real.log 2 + 2 * Real.negMulLog (w y) := by
          rw [Real.negMulLog_mul]; unfold Real.negMulLog; ring
        have hp0_nml : Real.negMulLog (p₀ y) =
            (1 - q_raw y) * Real.negMulLog (2 * w y) + (2 * w y) * Real.negMulLog (1 - q_raw y) := by
          rw [hp0_eq, Real.negMulLog_mul]
        have hp1_nml : Real.negMulLog (p₁ y) =
            q_raw y * Real.negMulLog (2 * w y) + (2 * w y) * Real.negMulLog (q_raw y) := by
          rw [hp1_eq, Real.negMulLog_mul]
        rw [hp0_nml, hp1_nml, h2w]
        field_simp [hlog2]
        ring
    calc 1 - ((∑ y : d₂, Real.negMulLog (w y)) / Real.log 2 -
            ((∑ y : d₂, Real.negMulLog (p₀ y)) / Real.log 2 + (∑ y : d₂, Real.negMulLog (p₁ y)) / Real.log 2) / 2)
        = ∑ y : d₂, (w y - (Real.negMulLog (w y) - (Real.negMulLog (p₀ y) + Real.negMulLog (p₁ y)) / 2) / Real.log 2) := by
            rw [Finset.sum_sub_distrib, hw_sum]
            congr 1
            simp_rw [sub_div, Finset.sum_sub_distrib, ← Finset.sum_div, div_div, ← add_div,
              Finset.sum_add_distrib]
            field_simp [hlog2]
      _ = ∑ y : d₂, w y * h2 (q y) := by
            apply Finset.sum_congr rfl; intro y _; exact (hterm y).symm
  have hchk_decomp : (CQChannel.checkCombine W₁ W₂d).condEntropy =
      ∑ y : d₂, w y * (CQChannel.checkCombine W₁ (bscChannel (q y) (hq0 y) (by linarith [hq1 y]))).condEntropy := by
    let τ₀ : d₂ → DensityOp d₁ := fun y ↦ DensityOp.mix (q_raw y) (hq_raw0 y) (hq_raw1 y) (W₁.out false) (W₁.out true)
    let τ₁ : d₂ → DensityOp d₁ := fun y ↦ DensityOp.mix (q_raw y) (hq_raw0 y) (hq_raw1 y) (W₁.out true) (W₁.out false)
    let τm : d₂ → DensityOp d₁ := fun y ↦ DensityOp.midpoint (τ₀ y) (τ₁ y)
    have hS0 := vonNeumannEntropy_block_diag hw_nn τ₀ ((CQChannel.checkCombine W₁ W₂d).out false) (by
      intro i₁ j₁ y₁ y₂
      simp only [CQChannel.checkCombine, Bool.not_false, DensityOp.midpoint, DensityOp.mix,
        DensityOp.tensor, hW₂d_0, hW₂d_1, Matrix.add_apply, Matrix.smul_apply,
        Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Function.comp_apply, Complex.real_smul, τ₀]
      split_ifs with hy
      · subst hy
        by_cases hw0 : w y₁ = 0
        · have hp0 : p₀ y₁ = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y₁, hp₁_nn y₁]
          have hp1 : p₁ y₁ = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y₁, hp₁_nn y₁]
          simp [hw0, hp0, hp1]
        · have hp1_eq : p₁ y₁ = 2 * w y₁ * q_raw y₁ := by
            dsimp [q_raw]; rw [if_neg hw0]; field_simp [hw0]
          have hp0_eq : p₀ y₁ = 2 * w y₁ * (1 - q_raw y₁) := by
            have : p₀ y₁ + p₁ y₁ = 2 * w y₁ := by dsimp [w]; ring
            linarith
          rw [hp0_eq, hp1_eq]; push_cast; ring
      · simp)
    have hS1 := vonNeumannEntropy_block_diag hw_nn τ₁ ((CQChannel.checkCombine W₁ W₂d).out true) (by
      intro i₁ j₁ y₁ y₂
      simp only [CQChannel.checkCombine, Bool.not_true, DensityOp.midpoint, DensityOp.mix,
        DensityOp.tensor, hW₂d_0, hW₂d_1, Matrix.add_apply, Matrix.smul_apply,
        Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Function.comp_apply, Complex.real_smul, τ₁]
      split_ifs with hy
      · subst hy
        by_cases hw0 : w y₁ = 0
        · have hp0 : p₀ y₁ = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y₁, hp₁_nn y₁]
          have hp1 : p₁ y₁ = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y₁, hp₁_nn y₁]
          simp [hw0, hp0, hp1]
        · have hp1_eq : p₁ y₁ = 2 * w y₁ * q_raw y₁ := by
            dsimp [q_raw]; rw [if_neg hw0]; field_simp [hw0]
          have hp0_eq : p₀ y₁ = 2 * w y₁ * (1 - q_raw y₁) := by
            have : p₀ y₁ + p₁ y₁ = 2 * w y₁ := by dsimp [w]; ring
            linarith
          rw [hp0_eq, hp1_eq]; push_cast; ring
      · simp)
    have hSm := vonNeumannEntropy_block_diag hw_nn τm
      (DensityOp.midpoint ((CQChannel.checkCombine W₁ W₂d).out false) ((CQChannel.checkCombine W₁ W₂d).out true)) (by
      intro i₁ j₁ y₁ y₂
      simp only [CQChannel.checkCombine, Bool.not_false, Bool.not_true, DensityOp.midpoint, DensityOp.mix,
        DensityOp.tensor, hW₂d_0, hW₂d_1, Matrix.add_apply, Matrix.smul_apply,
        Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Function.comp_apply, Complex.real_smul, τm, τ₀, τ₁]
      split_ifs with hy
      · subst hy
        by_cases hw0 : w y₁ = 0
        · have hp0 : p₀ y₁ = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y₁, hp₁_nn y₁]
          have hp1 : p₁ y₁ = 0 := by dsimp [w] at hw0; linarith [hp₀_nn y₁, hp₁_nn y₁]
          simp [hw0, hp0, hp1]
        · have hp1_eq : p₁ y₁ = 2 * w y₁ * q_raw y₁ := by
            dsimp [q_raw]; rw [if_neg hw0]; field_simp [hw0]
          have hp0_eq : p₀ y₁ = 2 * w y₁ * (1 - q_raw y₁) := by
            have : p₀ y₁ + p₁ y₁ = 2 * w y₁ := by dsimp [w]; ring
            linarith
          rw [hp0_eq, hp1_eq]; push_cast; ring
      · simp)
    have hblk_bsc : ∀ y : d₂,
        1 - (vonNeumannEntropy (τm y) - (vonNeumannEntropy (τ₀ y) + vonNeumannEntropy (τ₁ y)) / 2) =
          (CQChannel.checkCombine W₁ (bscChannel (q y) (hq0 y) (by linarith [hq1 y]))).condEntropy := by
      intro y
      let qy := q y
      let σ₀' := DensityOp.mix qy (hq0 y) (by linarith [hq1 y]) (W₁.out false) (W₁.out true)
      let σ₁' := DensityOp.mix qy (hq0 y) (by linarith [hq1 y]) (W₁.out true) (W₁.out false)
      have hb0 := vonNeumannEntropy_block_diag (w := fun _ : Bool ↦ (1 / 2 : ℝ)) (fun _ ↦ by norm_num)
        (fun b ↦ if b = false then σ₀' else σ₁')
        ((CQChannel.checkCombine W₁ (bscChannel qy (hq0 y) (by linarith [hq1 y]))).out false) (by
        intro i₁ j₁ b₁ b₂
        simp only [CQChannel.checkCombine, bscChannel, Bool.not_false, DensityOp.midpoint, DensityOp.mix,
          DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
          Matrix.diagonal_apply, Complex.real_smul, σ₀', σ₁']
        cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring)
      have hb1 := vonNeumannEntropy_block_diag (w := fun _ : Bool ↦ (1 / 2 : ℝ)) (fun _ ↦ by norm_num)
        (fun b ↦ if b = false then σ₁' else σ₀')
        ((CQChannel.checkCombine W₁ (bscChannel qy (hq0 y) (by linarith [hq1 y]))).out true) (by
        intro i₁ j₁ b₁ b₂
        simp only [CQChannel.checkCombine, bscChannel, Bool.not_true, DensityOp.midpoint, DensityOp.mix,
          DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
          Matrix.diagonal_apply, Complex.real_smul, σ₀', σ₁']
        cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring)
      have hbm := vonNeumannEntropy_block_diag (w := fun _ : Bool ↦ (1 / 2 : ℝ)) (fun _ ↦ by norm_num)
        (fun _ ↦ DensityOp.midpoint σ₀' σ₁')
        (DensityOp.midpoint ((CQChannel.checkCombine W₁ (bscChannel qy (hq0 y) (by linarith [hq1 y]))).out false)
          ((CQChannel.checkCombine W₁ (bscChannel qy (hq0 y) (by linarith [hq1 y]))).out true)) (by
        intro i₁ j₁ b₁ b₂
        simp only [CQChannel.checkCombine, bscChannel, Bool.not_false, Bool.not_true, DensityOp.midpoint,
          DensityOp.mix, DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
          Matrix.diagonal_apply, Complex.real_smul, σ₀', σ₁']
        cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring)
      have hpair : vonNeumannEntropy (τ₀ y) + vonNeumannEntropy (τ₁ y) =
          vonNeumannEntropy σ₀' + vonNeumannEntropy σ₁' ∧
          vonNeumannEntropy (τm y) = vonNeumannEntropy (DensityOp.midpoint σ₀' σ₁') := by
        rcases le_total (q_raw y) (1 - q_raw y) with h | h
        · have hq_eq : qy = q_raw y := min_eq_left h
          have h0 : (τ₀ y).mat = σ₀'.mat := by simp [τ₀, σ₀', DensityOp.mix, hq_eq]
          have h1 : (τ₁ y).mat = σ₁'.mat := by simp [τ₁, σ₁', DensityOp.mix, hq_eq]
          have hm : (τm y).mat = (DensityOp.midpoint σ₀' σ₁').mat := by
            simp [τm, DensityOp.midpoint, DensityOp.mix, h0, h1]
          exact ⟨by rw [vonNeumannEntropy_eq_of_mat_eq h0, vonNeumannEntropy_eq_of_mat_eq h1],
                 vonNeumannEntropy_eq_of_mat_eq hm⟩
        · have hq_eq : qy = 1 - q_raw y := min_eq_right h
          have h0 : (τ₀ y).mat = σ₁'.mat := by
            ext i j; simp only [τ₀, σ₁', DensityOp.mix, Matrix.add_apply, Matrix.smul_apply,
              Complex.real_smul, hq_eq]; push_cast; ring
          have h1 : (τ₁ y).mat = σ₀'.mat := by
            ext i j; simp only [τ₁, σ₀', DensityOp.mix, Matrix.add_apply, Matrix.smul_apply,
              Complex.real_smul, hq_eq]; push_cast; ring
          have hm : (τm y).mat = (DensityOp.midpoint σ₀' σ₁').mat := by
            ext i j; simp only [τm, DensityOp.midpoint, DensityOp.mix, h0, h1, Matrix.add_apply,
              Matrix.smul_apply, Complex.real_smul]; push_cast; ring
          exact ⟨by rw [vonNeumannEntropy_eq_of_mat_eq h0, vonNeumannEntropy_eq_of_mat_eq h1, add_comm],
                 vonNeumannEntropy_eq_of_mat_eq hm⟩
      unfold CQChannel.condEntropy qjs
      rw [hb0, hb1, hbm]
      simp only [Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false]
      linarith [hpair.1, hpair.2]
    unfold CQChannel.condEntropy qjs
    rw [hS0, hS1, hSm]
    calc 1 - (((∑ y : d₂, Real.negMulLog (w y)) / Real.log 2 + ∑ y : d₂, w y * vonNeumannEntropy (τm y)) -
            (((∑ y : d₂, Real.negMulLog (w y)) / Real.log 2 + ∑ y : d₂, w y * vonNeumannEntropy (τ₀ y)) +
             ((∑ y : d₂, Real.negMulLog (w y)) / Real.log 2 + ∑ y : d₂, w y * vonNeumannEntropy (τ₁ y))) / 2)
        = ∑ y : d₂, w y * (1 - (vonNeumannEntropy (τm y) - (vonNeumannEntropy (τ₀ y) + vonNeumannEntropy (τ₁ y)) / 2)) := by
            have h1 : (1 : ℝ) = ∑ y : d₂, w y := hw_sum.symm
            conv_lhs => rw [h1]
            simp only [mul_sub, mul_one, ← mul_div_assoc, mul_add, Finset.sum_sub_distrib,
              ← Finset.sum_div, Finset.sum_add_distrib]
            ring
      _ = ∑ y : d₂, w y * (CQChannel.checkCombine W₁ (bscChannel (q y) (hq0 y) (by linarith [hq1 y]))).condEntropy := by
            apply Finset.sum_congr rfl; intro y _; rw [hblk_bsc y]
  have hH₁_mem := condEntropy_mem_Icc W₁
  have hconv := convexOn_gc hH₁_mem
  have hgc_le : gc W₁.condEntropy W₂.condEntropy ≤ (CQChannel.checkCombine W₁ W₂).condEntropy := by
    rw [← hH₂_eq, ← hchk_eq, hH₂_decomp, hchk_decomp]
    have hjensen : gc W₁.condEntropy (∑ y : d₂, w y * h2 (q y)) ≤
        ∑ y : d₂, w y * gc W₁.condEntropy (h2 (q y)) := by
      have h := hconv.map_sum_le (t := Finset.univ) (w := w) (p := fun y ↦ h2 (q y))
        (fun y _ ↦ hw_nn y) hw_sum (fun y _ ↦ ⟨h2_nonneg ⟨hq0 y, by linarith [hq1 y]⟩,
          h2_le_one ⟨hq0 y, by linarith [hq1 y]⟩⟩)
      simpa [smul_eq_mul] using h
    refine le_trans hjensen ?_
    apply Finset.sum_le_sum; intro y _
    exact mul_le_mul_of_nonneg_left (theorem_1_2a_bsc W₁ (hq0 y) (hq1 y)) (hw_nn y)
  exact ⟨hgc_le, le_trans (by unfold gq; exact min_le_left _ _) hgc_le⟩

end PolarCodes
