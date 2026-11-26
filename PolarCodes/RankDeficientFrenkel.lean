/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.Refinements

/-!
# Rank-Deficient Frenkel and Hockey-Stick Integral Formulas (Eqs. 3.7–3.8)

This module extends Frenkel's integral formula (Eq. 3.7) and the hockey-stick integral
representation (Eq. 3.8) from full-rank states (`ρ, σ ≻ 0`) to arbitrary finite-dimensional
density operators satisfying support inclusion `suppSubset ρ σ`:
- `relEntropy_frenkel_integral_of_suppSubset`
- `relEntropy_hockeyStick_integral_of_suppSubset`
-/

open Matrix BigOperators Real Set Filter MeasureTheory Polynomial
open scoped ComplexOrder ENNReal Topology

namespace PolarCodes

section RankDeficientFrenkel

/-! ### 4. Rank-Deficient Frenkel & Hockey-Stick Integrals under `suppSubset ρ σ` (Gap 4B) -/

variable {d : Type*} [Fintype d] [DecidableEq d]

private lemma charpoly_mul_rect_eq {d₁ d₂ : Type*}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (A : Matrix d₁ d₂ ℂ) (B : Matrix d₂ d₁ ℂ) :
    (A * B).charpoly * Polynomial.X ^ (Fintype.card d₂) =
      (B * A).charpoly * Polynomial.X ^ (Fintype.card d₁) := by
  let P : Matrix (d₁ ⊕ d₂) (d₁ ⊕ d₂) ℂ := Matrix.fromBlocks 0 A 0 0
  let Q : Matrix (d₁ ⊕ d₂) (d₁ ⊕ d₂) ℂ := Matrix.fromBlocks 0 0 B 0
  have hPQ : P * Q = Matrix.fromBlocks (A * B) 0 0 0 := by
    simp [P, Q, Matrix.fromBlocks_multiply]
  have hQP : Q * P = Matrix.fromBlocks 0 0 0 (B * A) := by
    simp [P, Q, Matrix.fromBlocks_multiply]
  have hzero : ∀ (α : Type*) [Fintype α] [DecidableEq α],
      (0 : Matrix α α ℂ).charpoly = Polynomial.X ^ Fintype.card α := fun α _ _ ↦ by
    have h0 : (0 : Matrix α α ℂ) = Matrix.diagonal (fun _ : α ↦ (0 : ℂ)) := by
      ext i j; simp [Matrix.diagonal_apply]
    rw [h0, charpoly_diagonal_complex]
    simp [Finset.prod_const]
  have hcomm := Matrix.charpoly_mul_comm P Q
  rw [hPQ, hQP, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_fromBlocks_zero₁₂,
    hzero d₂, hzero d₁, mul_comm (Polynomial.X ^ Fintype.card d₁)] at hcomm
  exact hcomm

private lemma relEntropy_toReal_eq_trace_log_posDef {α : Type*} [Fintype α] [DecidableEq α]
    {ρ σ : DensityOp α} (hσ : σ.mat.PosDef) :
    let Lσ : Matrix α α ℂ := (σ.eigUnitary : Matrix α α ℂ) *
      Matrix.diagonal (fun j ↦ (Real.log (σ.eigvals j) : ℂ)) *
      star (σ.eigUnitary : Matrix α α ℂ)
    relEntropy ρ σ ≠ ⊤ ∧
    (relEntropy ρ σ).toReal = -vonNeumannEntropy ρ - ((ρ.mat * Lσ).trace).re / Real.log 2 := by
  intro Lσ
  have hsupp : suppSubset ρ σ := fun _ j _ hj ↦ absurd hj (ne_of_gt (hσ.eigenvalues_pos j))
  have hne : relEntropy ρ σ ≠ ⊤ := by unfold relEntropy; rw [if_pos hsupp]; exact ENNReal.ofReal_ne_top
  refine ⟨hne, ?_⟩
  have hcol : ∀ i : α, ∑ j : α,
      ‖(star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 = 1 := by
    intro i
    have hW : (star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ))ᴴ *
        (star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) = 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (star (σ.eigUnitary : Matrix α α ℂ))ᴴ,
        ← Matrix.star_eq_conjTranspose, star_star, Unitary.coe_mul_star_self σ.eigUnitary,
        Matrix.one_mul, ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self ρ.eigUnitary]
    have h := congr_arg Complex.re (congr_fun (congr_fun hW i) i)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      Complex.re_sum, Complex.one_re] at h
    rw [← h]; apply Finset.sum_congr rfl; intro j _
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hrow : ∀ j : α, ∑ i : α,
      ‖(star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 = 1 := by
    intro j
    have hW : (star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) *
        (star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ))ᴴ = 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (ρ.eigUnitary : Matrix α α ℂ),
        ← Matrix.star_eq_conjTranspose, Unitary.coe_mul_star_self ρ.eigUnitary,
        Matrix.one_mul, ← Matrix.star_eq_conjTranspose, star_star, Unitary.coe_star_mul_self σ.eigUnitary]
    have h := congr_arg Complex.re (congr_fun (congr_fun hW j) j)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      Complex.re_sum, Complex.one_re] at h
    rw [← h]; apply Finset.sum_congr rfl; intro i _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have htrρ : ∑ i : α, ρ.eigvals i = 1 := by
    have h := congr_arg Complex.re (ρ.isHermitian.trace_eq_sum_eigenvalues.symm.trans ρ.trace_one)
    simpa [DensityOp.eigvals, Complex.re_sum] using h
  have htrσ : ∑ j : α, σ.eigvals j = 1 := by
    have h := congr_arg Complex.re (σ.isHermitian.trace_eq_sum_eigenvalues.symm.trans σ.trace_one)
    simpa [DensityOp.eigvals, Complex.re_sum] using h
  have hnn : 0 ≤ (∑ i : α, ∑ j : α,
      ‖(star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 *
        (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j)))) / Real.log 2 := by
    apply div_nonneg _ (le_of_lt (Real.log_pos (by norm_num)))
    have hge : 0 ≤ ∑ i : α, ∑ j : α,
        ‖(star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 *
          (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j)) - (ρ.eigvals i - σ.eigvals j)) := by
      apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
      by_cases hρi : ρ.eigvals i = 0
      · rw [hρi]; simp only [zero_mul, zero_sub, neg_neg]
        exact mul_nonneg (sq_nonneg _) (σ.eigvals_nonneg j)
      · have hρp : 0 < ρ.eigvals i := lt_of_le_of_ne (ρ.eigvals_nonneg i) (Ne.symm hρi)
        have hσp : 0 < σ.eigvals j := hσ.eigenvalues_pos j
        apply mul_nonneg (sq_nonneg _)
        have hlog := Real.log_le_sub_one_of_pos (div_pos hσp hρp)
        rw [Real.log_div (ne_of_gt hσp) (ne_of_gt hρp)] at hlog
        have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hρp)
        have hsimp : ρ.eigvals i * (σ.eigvals j / ρ.eigvals i - 1) = σ.eigvals j - ρ.eigvals i := by
          field_simp [ne_of_gt hρp]
        linarith
    have hdiff0 : ∑ i : α, ∑ j : α,
        ‖(star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 *
          (ρ.eigvals i - σ.eigvals j) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hcol, one_mul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hrow, one_mul, htrρ, htrσ, sub_self]
    simp_rw [mul_sub, Finset.sum_sub_distrib] at hge
    linarith
  have htr_L : ((ρ.mat * Lσ).trace).re =
      ∑ i : α, ∑ j : α,
        ‖(star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 *
          (ρ.eigvals i * Real.log (σ.eigvals j)) := by
    have hW_def : (ρ.mat * Lσ).trace =
        ∑ i : α, ∑ j : α,
          ((‖(star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 : ℝ) : ℂ) *
            ((ρ.eigvals i : ℂ) * (Real.log (σ.eigvals j) : ℂ)) := by
      rw [density_spectral_eq ρ]
      simp only [Lσ, Matrix.mul_assoc]
      rw [Matrix.trace_mul_cycle]
      simp only [Matrix.mul_assoc]
      set W := star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)
      have hW_star : star (ρ.eigUnitary : Matrix α α ℂ) * (σ.eigUnitary : Matrix α α ℂ) = Wᴴ := by
        simp [W, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose]
      have hcy : (star (σ.eigUnitary : Matrix α α ℂ) * ((ρ.eigUnitary : Matrix α α ℂ) *
          (Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * (star (ρ.eigUnitary : Matrix α α ℂ) *
          ((σ.eigUnitary : Matrix α α ℂ) * Matrix.diagonal (fun j ↦ (Real.log (σ.eigvals j) : ℂ))))))).trace =
          (W * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * Wᴴ *
            Matrix.diagonal (fun j ↦ (Real.log (σ.eigvals j) : ℂ))).trace := by
        simp only [Matrix.mul_assoc, W, hW_star]
      rw [hcy]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.mul_diagonal,
        Matrix.diagonal_mul, Matrix.conjTranspose_apply, Function.comp_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [mul_comm (W j i) (ρ.eigvals i : ℂ), mul_assoc, ← mul_assoc (W j i),
        Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      ring
    rw [hW_def, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro j _
    simp
  unfold relEntropy
  rw [if_pos hsupp, ENNReal.toReal_ofReal hnn, htr_L]
  have hsplit : ∑ i : α, ∑ j : α,
      ‖(star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 *
        (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j))) =
      (∑ i : α, ρ.eigvals i * Real.log (ρ.eigvals i)) -
      (∑ i : α, ∑ j : α, ‖(star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 *
        (ρ.eigvals i * Real.log (σ.eigvals j))) := by
    have h1 : ∀ i j, ‖(star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 *
        (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j))) =
        ‖(star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 *
          (ρ.eigvals i * Real.log (ρ.eigvals i)) -
        ‖(star (σ.eigUnitary : Matrix α α ℂ) * (ρ.eigUnitary : Matrix α α ℂ)) j i‖ ^ 2 *
          (ρ.eigvals i * Real.log (σ.eigvals j)) := fun _ _ ↦ by ring
    simp_rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul, hcol, one_mul]
  rw [hsplit, sub_div]
  unfold vonNeumannEntropy
  have hneg : -(∑ i : α, Real.negMulLog (ρ.eigvals i)) / Real.log 2 =
      (∑ i : α, ρ.eigvals i * Real.log (ρ.eigvals i)) / Real.log 2 := by
    congr 1; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; simp [Real.negMulLog]
  linarith

private lemma relEntropy_le_neg_logb_of_scale {α : Type*} [Fintype α] [DecidableEq α]
    {ρ M : DensityOp α} (hρ : ρ.mat.PosDef) (hM : M.mat.PosDef)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hdom : (M.mat - (c : ℂ) • ρ.mat).PosSemidef) :
    (relEntropy ρ M).toReal ≤ -Real.logb 2 c := by
  have hhs_eq := relEntropy_hockeyStick_integral hρ hM
  have h1c_ge1 : (1 : ℝ) ≤ 1 / c := by rw [le_div_iff₀ hc0, one_mul]; exact hc1
  have hhs_bound : ∀ s : ℝ, 0 < s →
      (hockeyStick s ρ M - max (1 - s) 0) / s ≤
        if s < 1 then 1 - c else if s < 1 / c then 1 / s - c else 0 := by
    intro s hs
    have hE_le : ∀ (hs' : s < 1 / c), hockeyStick s ρ M ≤ 1 - s * c := by
      intro hs'
      have h1sc : 0 ≤ 1 - s * c := by
        have := (lt_div_iff₀ hc0).mp hs'; linarith
      have hB_psd : (((1 - s * c : ℝ) : ℂ) • ρ.mat).PosSemidef := by
        simpa [Complex.real_smul] using ρ.posSemidef.smul h1sc
      have hdiff_psd : (((1 - s * c : ℝ) : ℂ) • ρ.mat - (ρ.mat - (s : ℂ) • M.mat)).PosSemidef := by
        have hmat : ((1 - s * c : ℝ) : ℂ) • ρ.mat - (ρ.mat - (s : ℂ) • M.mat) =
            (s : ℂ) • (M.mat - (c : ℂ) • ρ.mat) := by
          ext i j; simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; push_cast; ring
        rw [hmat]
        simpa [Complex.real_smul] using hdom.smul (le_of_lt hs)
      rw [hockeyStick_eq_posPartTrace]
      have hle := posPartTrace_le_trace_of_le (hockeyStick_isHermitian s ρ M) hB_psd hdiff_psd
      rw [Matrix.trace_smul, ρ.trace_one, smul_eq_mul, mul_one, Complex.ofReal_re] at hle
      exact hle
    split_ifs with hs1 hs2
    · have hE := hE_le (lt_of_lt_of_le hs1 h1c_ge1)
      rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - s), div_le_iff₀ hs]
      linarith
    · have hE := hE_le hs2
      rw [max_eq_right (by linarith : 1 - s ≤ 0), sub_zero, div_le_iff₀ hs]
      have hsimp : (1 / s - c) * s = 1 - s * c := by field_simp [ne_of_gt hs]
      linarith
    · push Not at hs1 hs2
      have hE0 : hockeyStick s ρ M = 0 := by
        rw [hockeyStick_eq_posPartTrace]
        have hneg_psd : (-(ρ.mat - (s : ℂ) • M.mat)).PosSemidef := by
          have h1sc : 0 ≤ s * c - 1 := by
            have := (div_le_iff₀ hc0).mp hs2; linarith
          have hmat : -(ρ.mat - (s : ℂ) • M.mat) =
              ((s * c - 1 : ℝ) : ℂ) • ρ.mat + (s : ℂ) • (M.mat - (c : ℂ) • ρ.mat) := by
            ext i j; simp only [Matrix.neg_apply, Matrix.sub_apply, Matrix.add_apply,
              Matrix.smul_apply, smul_eq_mul]; push_cast; ring
          rw [hmat]
          exact (by simpa [Complex.real_smul] using ρ.posSemidef.smul h1sc).add
            (by simpa [Complex.real_smul] using hdom.smul (le_of_lt hs))
        unfold posPartTrace
        apply Finset.sum_eq_zero; intro i _
        have hle0 : (hockeyStick_isHermitian s ρ M).eigenvalues i ≤ 0 := by
          have hnn := hneg_psd.eigenvalues_nonneg
          -- For any unit vector `v`, `vᴴ (ρ - s M) v ≤ 0`, so every eigenvalue of `ρ - s M` is `≤ 0`
          have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hneg_psd).2
            (fun k ↦ ((hockeyStick_isHermitian s ρ M).eigenvectorUnitary : Matrix α α ℂ) k i)
          set U := ((hockeyStick_isHermitian s ρ M).eigenvectorUnitary : Matrix α α ℂ)
          set v : α → ℂ := fun k ↦ U k i
          have hv : star v ⬝ᵥ ((ρ.mat - (s : ℂ) • M.mat) *ᵥ v) =
              ((hockeyStick_isHermitian s ρ M).eigenvalues i : ℂ) := by
            have hspec : ρ.mat - (s : ℂ) • M.mat =
                U * Matrix.diagonal (Complex.ofReal ∘ (hockeyStick_isHermitian s ρ M).eigenvalues) * star U := by
              simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using
                (hockeyStick_isHermitian s ρ M).spectral_theorem
            rw [hspec]; simp only [Matrix.mulVec_mulVec]
            have h1 : star U *ᵥ v = Pi.single i 1 := by
              ext k
              have h := congr_fun (congr_fun (Unitary.coe_star_mul_self (hockeyStick_isHermitian s ρ M).eigenvectorUnitary) k) i
              simpa [v, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using h
            rw [h1]
            have h2 : Matrix.diagonal (Complex.ofReal ∘ (hockeyStick_isHermitian s ρ M).eigenvalues) *ᵥ Pi.single i (1 : ℂ) =
                Pi.single i ((hockeyStick_isHermitian s ρ M).eigenvalues i : ℂ) := by
              ext k; simp [Matrix.mulVec_diagonal, Pi.single_apply]
            rw [h2]
            have h3 : star v ⬝ᵥ (U *ᵥ Pi.single i ((hockeyStick_isHermitian s ρ M).eigenvalues i : ℂ)) =
                (star U *ᵥ v) i * ((hockeyStick_isHermitian s ρ M).eigenvalues i : ℂ) := by
              simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.single_apply, mul_ite, mul_zero,
                Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Matrix.star_apply]
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl; intro k _; simp [v]; ring
            rw [h3, h1]; simp
          rw [Matrix.neg_mulVec, dotProduct_neg, hv] at hq
          rw [Complex.le_def] at hq
          simpa using hq.1
        exact max_eq_right hle0
      rw [hE0, max_eq_right (by linarith), sub_self, zero_div]
  -- Bound the lintegral by `∫_0^1 (1 - c) + ∫_1^{1/c} (1/s - c) = -log c`
  let g : ℝ → ℝ := fun s ↦ if s < 1 then 1 - c else if s < 1 / c then 1 / s - c else 0
  have hlint_le : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal ((hockeyStick s ρ M - max (1 - s) 0) / s) ∂volume) ≤
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (g s) ∂volume := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro s hs
    exact ENNReal.ofReal_le_ofReal (hhs_bound s hs)
  have hsplit1 : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (g s) ∂volume) =
      (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - c) ∂volume) +
      (∫⁻ s in Ico (1 : ℝ) (1 / c), ENNReal.ofReal (1 / s - c) ∂volume) := by
    have hU : Ioi (0 : ℝ) = Ioo 0 1 ∪ (Ico 1 (1 / c) ∪ Ici (1 / c)) := by
      ext s; simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ico, mem_Ici]
      constructor
      · intro hs
        by_cases h1 : s < 1
        · exact Or.inl ⟨hs, h1⟩
        · by_cases h2 : s < 1 / c
          · exact Or.inr (Or.inl ⟨not_lt.mp h1, h2⟩)
          · exact Or.inr (Or.inr (not_lt.mp h2))
      · rintro (⟨hs, _⟩ | ⟨h1, _⟩ | h2)
        · exact hs
        · linarith
        · linarith
    rw [hU, lintegral_union (measurableSet_Ico.union measurableSet_Ici)
      (Set.disjoint_left.mpr fun x h1 h2 ↦ by
        rcases h2 with h2 | h2 <;> linarith [h1.2, h2.1]),
      lintegral_union measurableSet_Ici
      (Set.disjoint_left.mpr fun x h1 h2 ↦ not_le.mpr h1.2 h2)]
    have hz : ∫⁻ s in Ici (1 / c), ENNReal.ofReal (g s) ∂volume = 0 := by
      apply setLIntegral_eq_zero measurableSet_Ici; intro s hs
      have h1 : ¬ s < 1 := not_lt.mpr (le_trans h1c_ge1 hs)
      have h2 : ¬ s < 1 / c := not_lt.mpr hs
      simp [g, h1, h2]
    rw [hz, add_zero]
    congr 1
    · apply setLIntegral_congr_fun measurableSet_Ioo; intro s hs
      simp [g, hs.2]
    · apply setLIntegral_congr_fun measurableSet_Ico; intro s hs
      have h1 : ¬ s < 1 := not_lt.mpr hs.1
      simp [g, h1, hs.2]
  have hI1 : ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - c) ∂volume = ENNReal.ofReal (1 - c) := by
    rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
  have hI2 : ∫⁻ s in Ico (1 : ℝ) (1 / c), ENNReal.ofReal (1 / s - c) ∂volume =
      ENNReal.ofReal (-Real.log c - (1 - c)) := by
    have hcont : ContinuousOn (fun s : ℝ ↦ 1 / s - c) (Icc 1 (1 / c)) := by
      refine ContinuousOn.sub ?_ continuousOn_const
      exact continuousOn_const.div continuousOn_id fun s hs ↦ ne_of_gt (by linarith [hs.1])
    have hnn_g : ∀ s ∈ Ioc (1 : ℝ) (1 / c), 0 ≤ 1 / s - c := by
      intro s hs; have h := (le_div_iff₀ (by linarith [hs.1] : (0 : ℝ) < s)).mpr
        (by linarith [(le_div_iff₀ hc0).mp hs.2] : c * s ≤ 1)
      linarith
    have hint : IntervalIntegrable (fun s : ℝ ↦ 1 / s - c) volume 1 (1 / c) :=
      hcont.intervalIntegrable_of_Icc h1c_ge1
    rw [MeasureTheory.restrict_Ico_eq_restrict_Ioc,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_iff_integrableOn_Ioc_of_le h1c_ge1 |>.mp hint)
        (ae_restrict_of_forall_mem measurableSet_Ioc hnn_g),
      ← intervalIntegral.integral_of_le h1c_ge1]
    congr 1
    have hsub : ∫ s in (1 : ℝ)..(1 / c), (1 / s - c) =
        (∫ s in (1 : ℝ)..(1 / c), (1 / s)) - (∫ _ in (1 : ℝ)..(1 / c), c) :=
      intervalIntegral.integral_sub
        ((continuousOn_const.div continuousOn_id fun s hs ↦ ne_of_gt (by linarith [hs.1])).intervalIntegrable_of_Icc h1c_ge1)
        intervalIntegrable_const
    rw [hsub]
    have hinv : ∫ s in (1 : ℝ)..(1 / c), (1 / s) = -Real.log c := by
      have h0 : (0 : ℝ) ∉ uIcc (1 : ℝ) (1 / c) := by
        rw [uIcc_of_le h1c_ge1]; intro h; linarith [h.1]
      have := integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) (div_pos one_pos hc0)
      simpa [one_div, Real.log_div one_ne_zero (ne_of_gt hc0), Real.log_one] using this
    rw [hinv, intervalIntegral.integral_const, smul_eq_mul]
    field_simp [ne_of_gt hc0]; ring
  have htotal : relEntropy ρ M * ENNReal.ofReal (Real.log 2) ≤ ENNReal.ofReal (-Real.log c) := by
    rw [hhs_eq]
    calc _ ≤ ENNReal.ofReal (1 - c) + ENNReal.ofReal (-Real.log c - (1 - c)) := by
          rw [← hI1, ← hI2, ← hsplit1]; exact hlint_le
      _ = ENNReal.ofReal (-Real.log c) := by
          rw [← ENNReal.ofReal_add (by linarith) (by
            have hlog := Real.log_le_sub_one_of_pos hc0
            linarith)]
          congr 1; ring
  have hne : relEntropy ρ M ≠ ⊤ := (relEntropy_toReal_eq_trace_log_posDef hM).1
  have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top htotal
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (Real.log_pos (by norm_num))),
    ENNReal.toReal_ofReal (by linarith [Real.log_nonpos (le_of_lt hc0) hc1])] at hto
  rw [Real.logb, neg_div]
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr hto

private lemma vonNeumannEntropy_mix_bounds {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (ρ σ : DensityOp α) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    (1 - ε) * vonNeumannEntropy ρ + ε * vonNeumannEntropy σ ≤
      vonNeumannEntropy (DensityOp.mix ε (le_of_lt hε0) (le_of_lt hε1) ρ σ) ∧
    vonNeumannEntropy (DensityOp.mix ε (le_of_lt hε0) (le_of_lt hε1) ρ σ) ≤
      (1 - ε) * vonNeumannEntropy ρ + ε * vonNeumannEntropy σ + h2 ε := by
  let M := DensityOp.mix ε (le_of_lt hε0) (le_of_lt hε1) ρ σ
  -- Prove for δ-perturbed states `ρ_δ, σ_δ, M_δ` where all three are `PosDef`, then send `δ → 0⁺`
  let seq : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 2)
  have hseq0 : ∀ k, 0 < seq k := fun k ↦ by simp only [seq]; positivity
  have hseq1 : ∀ k, seq k < 1 := fun k ↦ by
    simp only [seq]; rw [div_lt_one (by positivity)]; linarith
  have hpd_mix : ∀ (A : DensityOp α) (k : ℕ),
      (DensityOp.mix (seq k) (le_of_lt (hseq0 k)) (le_of_lt (hseq1 k)) A (maxMixedState α)).mat.PosDef := by
    intro A k
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨(DensityOp.mix _ _ _ A (maxMixedState α)).posSemidef.isHermitian, fun v hv ↦ ?_⟩
    have h1 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp A.posSemidef).2 v
    have hI_pd : (maxMixedState α).mat.PosDef := by
      have hpos : (0 : ℝ) < (Fintype.card α : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
      simpa [maxMixedState, Complex.real_smul] using (Matrix.PosDef.one (n := α) (R := ℂ)).smul hpos
    have h2' := (Matrix.posDef_iff_dotProduct_mulVec.mp hI_pd).2 hv
    simp only [DensityOp.mix, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    rw [Complex.lt_def] at h2' ⊢; rw [Complex.le_def] at h1
    simp only [Complex.zero_re, Complex.zero_im] at h1 h2' ⊢
    exact ⟨by simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]; nlinarith [h1.1, h2'.1, hseq0 k, hseq1 k],
      by simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, h1.2.symm, h2'.2.symm, mul_zero]⟩
  have hstep : ∀ k : ℕ,
      let ρk := DensityOp.mix (seq k) (le_of_lt (hseq0 k)) (le_of_lt (hseq1 k)) ρ (maxMixedState α)
      let σk := DensityOp.mix (seq k) (le_of_lt (hseq0 k)) (le_of_lt (hseq1 k)) σ (maxMixedState α)
      let Mk := DensityOp.mix (seq k) (le_of_lt (hseq0 k)) (le_of_lt (hseq1 k)) M (maxMixedState α)
      (1 - ε) * vonNeumannEntropy ρk + ε * vonNeumannEntropy σk ≤ vonNeumannEntropy Mk ∧
      vonNeumannEntropy Mk ≤ (1 - ε) * vonNeumannEntropy ρk + ε * vonNeumannEntropy σk + h2 ε := by
    intro k ρk σk Mk
    have hMk_mat : Mk.mat = ((1 - ε : ℝ) : ℂ) • ρk.mat + (ε : ℂ) • σk.mat := by
      ext i j
      simp only [Mk, M, ρk, σk, DensityOp.mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast; ring
    have hρk_pd := hpd_mix ρ k
    have hσk_pd := hpd_mix σ k
    have hMk_pd := hpd_mix M k
    have hD1 := (relEntropy_toReal_eq_trace_log_posDef (ρ := ρk) hMk_pd).2
    have hD2 := (relEntropy_toReal_eq_trace_log_posDef (ρ := σk) hMk_pd).2
    set LM := (Mk.eigUnitary : Matrix α α ℂ) *
      Matrix.diagonal (fun j ↦ (Real.log (Mk.eigvals j) : ℂ)) *
      star (Mk.eigUnitary : Matrix α α ℂ)
    have htr_M : ((Mk.mat * LM).trace).re / Real.log 2 = -vonNeumannEntropy Mk := by
      rw [density_spectral_eq Mk]
      simp only [LM, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star (Mk.eigUnitary : Matrix α α ℂ)), Unitary.coe_star_mul_self Mk.eigUnitary,
        Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal,
        Matrix.trace_mul_cycle, Unitary.coe_star_mul_self Mk.eigUnitary, Matrix.one_mul,
        Matrix.trace_diagonal, Complex.re_sum]
      unfold vonNeumannEntropy
      rw [← neg_div, ← Finset.sum_neg_distrib]
      congr 1; apply Finset.sum_congr rfl; intro j _; simp [Real.negMulLog]
    have hcomb : (1 - ε) * (relEntropy ρk Mk).toReal + ε * (relEntropy σk Mk).toReal =
        vonNeumannEntropy Mk - ((1 - ε) * vonNeumannEntropy ρk + ε * vonNeumannEntropy σk) := by
      rw [hD1, hD2]
      have htr_lin : (1 - ε) * ((ρk.mat * LM).trace).re + ε * ((σk.mat * LM).trace).re =
          ((Mk.mat * LM).trace).re := by
        rw [hMk_mat, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_add,
          Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
      have hdiv_lin : (1 - ε) * (((ρk.mat * LM).trace).re / Real.log 2) +
          ε * (((σk.mat * LM).trace).re / Real.log 2) = -vonNeumannEntropy Mk := by
        rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, htr_lin, htr_M]
      linarith
    have hdom1 : (Mk.mat - ((1 - ε : ℝ) : ℂ) • ρk.mat).PosSemidef := by
      have h : Mk.mat - ((1 - ε : ℝ) : ℂ) • ρk.mat = (ε : ℂ) • σk.mat := by
        rw [hMk_mat]; abel
      rw [h]; simpa [Complex.real_smul] using σk.posSemidef.smul (le_of_lt hε0)
    have hdom2 : (Mk.mat - (ε : ℂ) • σk.mat).PosSemidef := by
      have h : Mk.mat - (ε : ℂ) • σk.mat = ((1 - ε : ℝ) : ℂ) • ρk.mat := by
        rw [hMk_mat]; abel
      rw [h]; simpa [Complex.real_smul] using ρk.posSemidef.smul (by linarith)
    have hle1 := relEntropy_le_neg_logb_of_scale hρk_pd hMk_pd (by linarith) (by linarith) hdom1
    have hle2 := relEntropy_le_neg_logb_of_scale hσk_pd hMk_pd hε0 (le_of_lt hε1) hdom2
    have hnn1 : 0 ≤ (relEntropy ρk Mk).toReal := ENNReal.toReal_nonneg
    have hnn2 : 0 ≤ (relEntropy σk Mk).toReal := ENNReal.toReal_nonneg
    constructor
    · nlinarith
    · have h2_eq : (1 - ε) * (-Real.logb 2 (1 - ε)) + ε * (-Real.logb 2 ε) = h2 ε := by
        unfold h2; ring
      nlinarith
  have hseq_tend : Tendsto seq atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun k ↦ hseq0 k⟩
    simpa [seq] using tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  have hT : ∀ A : DensityOp α,
      Tendsto (fun k ↦ vonNeumannEntropy (DensityOp.mix (seq k) (le_of_lt (hseq0 k))
        (le_of_lt (hseq1 k)) A (maxMixedState α))) atTop (𝓝 (vonNeumannEntropy A)) := by
    intro A
    have h := tendsto_vonNeumannEntropy_mix_maxMixed A
    exact (h.comp hseq_tend).congr fun k ↦ by
      simp only [Function.comp_apply]
      have hle : seq k ≤ 1 := le_of_lt (hseq1 k)
      have hnn : 0 ≤ seq k := le_of_lt (hseq0 k)
      rfl
  constructor
  · exact le_of_tendsto_of_tendsto
      (((hT ρ).const_mul (1 - ε)).add ((hT σ).const_mul ε)) (hT M)
      (Eventually.of_forall fun k ↦ (hstep k).1)
  · exact le_of_tendsto_of_tendsto (hT M)
      ((((hT ρ).const_mul (1 - ε)).add ((hT σ).const_mul ε)).add tendsto_const_nhds)
      (Eventually.of_forall fun k ↦ (hstep k).2)

private lemma relEntropy_frenkel_integral_of_posDef_right {α : Type*} [Fintype α] [DecidableEq α]
    {ρ σ : DensityOp α} (hσ : σ.mat.PosDef) :
    relEntropy ρ σ * ENNReal.ofReal (Real.log 2) =
      ∫⁻ t : ℝ, ENNReal.ofReal (negPartTrace (pencil_isHermitian t ρ σ) / (|t| * (t - 1) ^ 2)) ∂volume := by
  haveI : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    have htr := ρ.trace_one
    simp [Matrix.trace] at htr
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 2)
  have hε0 : ∀ n, 0 < ε n := fun n ↦ by simp only [ε]; positivity
  have hε1 : ∀ n, ε n < 1 := fun n ↦ by
    simp only [ε]; rw [div_lt_one (by positivity)]; linarith
  let ρn : ℕ → DensityOp α := fun n ↦ DensityOp.mix (ε n) (le_of_lt (hε0 n)) (le_of_lt (hε1 n)) ρ σ
  have hρn_pd : ∀ n, (ρn n).mat.PosDef := by
    intro n
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨(ρn n).posSemidef.isHermitian, fun v hv ↦ ?_⟩
    have h1 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp ρ.posSemidef).2 v
    have h2' := (Matrix.posDef_iff_dotProduct_mulVec.mp hσ).2 hv
    simp only [ρn, DensityOp.mix, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    rw [Complex.lt_def] at h2' ⊢; rw [Complex.le_def] at h1
    simp only [Complex.zero_re, Complex.zero_im] at h1 h2' ⊢
    exact ⟨by simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]; nlinarith [h1.1, h2'.1, hε0 n, hε1 n],
      by simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, h1.2.symm, h2'.2.symm, mul_zero]⟩
  -- Step 1: LHS converges `relEntropy (ρn n) σ * ofReal (log 2) → relEntropy ρ σ * ofReal (log 2)`
  have hε_tend : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  have hS_tend : Tendsto (fun n ↦ vonNeumannEntropy (ρn n)) atTop (𝓝 (vonNeumannEntropy ρ)) := by
    have hlow : Tendsto (fun n ↦ (1 - ε n) * vonNeumannEntropy ρ + ε n * vonNeumannEntropy σ)
        atTop (𝓝 (vonNeumannEntropy ρ)) := by
      have h := ((tendsto_const_nhds.sub hε_tend).mul_const (vonNeumannEntropy ρ)).add
        (hε_tend.mul_const (vonNeumannEntropy σ))
      simpa using h
    have hh2_tend : Tendsto (fun n ↦ h2 (ε n)) atTop (𝓝 0) := by
      have hc : ContinuousWithinAt h2 (Icc (0 : ℝ) (1 / 2)) 0 :=
        continuousOn_h2 0 (by norm_num)
      have hmem : ∀ n, ε n ∈ Icc (0 : ℝ) (1 / 2) := fun n ↦
        ⟨le_of_lt (hε0 n), by simp only [ε]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith⟩
      have h := hc.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hε_tend
        (Eventually.of_forall hmem))
      simpa [h2_zero] using h
    have hhigh : Tendsto (fun n ↦ (1 - ε n) * vonNeumannEntropy ρ + ε n * vonNeumannEntropy σ + h2 (ε n))
        atTop (𝓝 (vonNeumannEntropy ρ)) := by
      simpa using hlow.add hh2_tend
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hhigh
      (fun n ↦ (vonNeumannEntropy_mix_bounds ρ σ (hε0 n) (hε1 n)).1)
      (fun n ↦ (vonNeumannEntropy_mix_bounds ρ σ (hε0 n) (hε1 n)).2)
  have hLHS_tend : Tendsto (fun n ↦ relEntropy (ρn n) σ * ENNReal.ofReal (Real.log 2))
      atTop (𝓝 (relEntropy ρ σ * ENNReal.ofReal (Real.log 2))) := by
    have hD_tend : Tendsto (fun n ↦ (relEntropy (ρn n) σ).toReal) atTop (𝓝 (relEntropy ρ σ).toReal) := by
      set Lσ := (σ.eigUnitary : Matrix α α ℂ) *
        Matrix.diagonal (fun j ↦ (Real.log (σ.eigvals j) : ℂ)) *
        star (σ.eigUnitary : Matrix α α ℂ)
      have htr_tend : Tendsto (fun n ↦ (((ρn n).mat * Lσ).trace).re) atTop (𝓝 (((ρ.mat * Lσ).trace).re)) := by
        have hlin : ∀ n, (((ρn n).mat * Lσ).trace).re =
            (1 - ε n) * ((ρ.mat * Lσ).trace).re + ε n * ((σ.mat * Lσ).trace).re := fun n ↦ by
          simp only [ρn, DensityOp.mix, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
            Matrix.trace_smul, smul_eq_mul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero]
        simp_rw [hlin]
        simpa using ((tendsto_const_nhds.sub hε_tend).mul_const _).add (hε_tend.mul_const _)
      have h1 : ∀ n, (relEntropy (ρn n) σ).toReal = -vonNeumannEntropy (ρn n) -
          (((ρn n).mat * Lσ).trace).re / Real.log 2 :=
        fun n ↦ (relEntropy_toReal_eq_trace_log_posDef (ρ := ρn n) hσ).2
      have h0 := (relEntropy_toReal_eq_trace_log_posDef (ρ := ρ) hσ).2
      simp_rw [h1]; rw [h0]
      exact hS_tend.neg.sub (htr_tend.div_const _)
    have hrel_tend : Tendsto (fun n ↦ relEntropy (ρn n) σ) atTop (𝓝 (relEntropy ρ σ)) := by
      have h := (ENNReal.continuous_ofReal.tendsto _).comp hD_tend
      have h1 : ∀ n, ENNReal.ofReal (relEntropy (ρn n) σ).toReal = relEntropy (ρn n) σ :=
        fun n ↦ ENNReal.ofReal_toReal (relEntropy_toReal_eq_trace_log_posDef (ρ := ρn n) hσ).1
      have h0 : ENNReal.ofReal (relEntropy ρ σ).toReal = relEntropy ρ σ :=
        ENNReal.ofReal_toReal (relEntropy_toReal_eq_trace_log_posDef (ρ := ρ) hσ).1
      simpa only [Function.comp_apply, h1, h0] using h
    exact ENNReal.Tendsto.mul_const hrel_tend (Or.inr ENNReal.ofReal_ne_top)
  -- Step 2: RHS via affine substitution `s = (1 - ε n) * t + ε n` and monotone convergence `lintegral_iSup`
  let G : ℕ → ℝ → ℝ≥0∞ := fun n s ↦
    if s < 0 then
      ENNReal.ofReal ((1 - ε n) ^ 2 * negPartTrace (pencil_isHermitian s ρ σ) / ((-s + ε n) * (1 - s) ^ 2))
    else if 1 < s then
      ENNReal.ofReal ((1 - ε n) ^ 2 * negPartTrace (pencil_isHermitian s ρ σ) / ((s - ε n) * (s - 1) ^ 2))
    else 0
  have hRHS_eq : ∀ n, relEntropy (ρn n) σ * ENNReal.ofReal (Real.log 2) = ∫⁻ s : ℝ, G n s ∂volume := by
    intro n
    rw [relEntropy_frenkel_integral (hρn_pd n) hσ]
    have h1mε : 0 < 1 - ε n := by linarith [hε1 n]
    -- Substitute `s = (1 - ε n) * t + ε n`, i.e., `t = (s - ε n) / (1 - ε n)`
    have hsub := MeasureTheory.lintegral_comp_mul_left_add (μ := volume)
      (fun s : ℝ ↦ ENNReal.ofReal (negPartTrace (pencil_isHermitian ((s - ε n) / (1 - ε n)) (ρn n) σ) /
        (|(s - ε n) / (1 - ε n)| * ((s - ε n) / (1 - ε n) - 1) ^ 2)))
      (ne_of_gt h1mε) (ε n)
    have hsimp_l : (fun t : ℝ ↦ ENNReal.ofReal (negPartTrace (pencil_isHermitian (((1 - ε n) * t + ε n - ε n) / (1 - ε n)) (ρn n) σ) /
        (|((1 - ε n) * t + ε n - ε n) / (1 - ε n)| * (((1 - ε n) * t + ε n - ε n) / (1 - ε n) - 1) ^ 2))) =
        (fun t : ℝ ↦ ENNReal.ofReal (negPartTrace (pencil_isHermitian t (ρn n) σ) / (|t| * (t - 1) ^ 2))) := by
      ext t
      have ht : ((1 - ε n) * t + ε n - ε n) / (1 - ε n) = t := by field_simp [ne_of_gt h1mε]; ring
      rw [ht]
    rw [hsimp_l] at hsub
    rw [hsub, ← lintegral_const_mul' _ _ (by simp [ENNReal.ofReal_ne_top])]
    apply lintegral_congr_ae
    filter_upwards [ae_iff.mpr (show volume ({(0 : ℝ), 1} : Set ℝ) = 0 by simp)] with s hs
    simp only [mem_singleton_iff, mem_insert_iff, not_or] at hs
    have hpencil_eq : negPartTrace (pencil_isHermitian ((s - ε n) / (1 - ε n)) (ρn n) σ) =
        negPartTrace (pencil_isHermitian s ρ σ) := by
      apply negPartTrace_eq_of_eq
      ext i j
      simp only [ρn, DensityOp.mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast; field_simp [ne_of_gt h1mε]; ring
    rw [hpencil_eq]
    have hscale : ENNReal.ofReal |1 - ε n|⁻¹ = ENNReal.ofReal (1 - ε n)⁻¹ := by
      rw [abs_of_pos h1mε]
    rw [hscale, ← ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt h1mε))]
    by_cases hs0 : s < 0
    · simp only [G, hs0, ↓reduceIte]
      congr 1
      have hneg : (s - ε n) / (1 - ε n) < 0 := div_neg_of_neg_of_pos (by linarith [hε0 n]) h1mε
      rw [abs_of_neg hneg]
      field_simp [ne_of_gt h1mε, ne_of_gt (by linarith [hε0 n] : 0 < -s + ε n), ne_of_gt (by linarith : 0 < 1 - s)]
      ring
    · by_cases hs1 : 1 < s
      · simp only [G, hs0, hs1, ↓reduceIte]
        congr 1
        have hpos : 0 < (s - ε n) / (1 - ε n) := div_pos (by linarith [hε1 n]) h1mε
        rw [abs_of_pos hpos]
        field_simp [ne_of_gt h1mε, ne_of_gt (by linarith [hε1 n] : 0 < s - ε n), ne_of_gt (by linarith : 0 < s - 1)]
        ring
      · have hmem : s ∈ Icc (0 : ℝ) 1 := ⟨not_lt.mp hs0, not_lt.mp hs1⟩
        simp only [G, hs0, hs1, ↓reduceIte, negPartTrace_pencil_eq_zero_of_mem_Icc hmem.1 hmem.2,
          zero_div, mul_zero, ENNReal.ofReal_zero]
  -- Monotonicity of `G n s` in `n`
  have hG_mono : Monotone G := by
    intro m n hmn s
    have hε_le : ε n ≤ ε m := by
      simp only [ε]; exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by exact_mod_cast (by omega : m + 2 ≤ n + 2))
    have hnn := negPartTrace_nonneg (pencil_isHermitian s ρ σ)
    simp only [G]
    split_ifs with hs0 hs1
    · apply ENNReal.ofReal_le_ofReal
      have hd1 : 0 < (-s + ε n) * (1 - s) ^ 2 := mul_pos (by linarith [hε0 n]) (by positivity)
      have hd2 : 0 < (-s + ε m) * (1 - s) ^ 2 := mul_pos (by linarith [hε0 m]) (by positivity)
      rw [div_le_div_iff₀ hd2 hd1]
      have hsq : (1 - ε m) ^ 2 ≤ (1 - ε n) ^ 2 := by nlinarith [hε1 m, hε1 n]
      nlinarith [mul_nonneg hnn (sq_nonneg (1 - s))]
    · apply ENNReal.ofReal_le_ofReal
      have hd1 : 0 < (s - ε n) * (s - 1) ^ 2 := mul_pos (by linarith [hε1 n]) (by positivity)
      have hd2 : 0 < (s - ε m) * (s - 1) ^ 2 := mul_pos (by linarith [hε1 m]) (by positivity)
      rw [div_le_div_iff₀ hd2 hd1]
      -- Need `(1 - ε m)² * (s - ε n) ≤ (1 - ε n)² * (s - ε m)` for `ε n ≤ ε m < 1 < s`
      have hpoly : (1 - ε m) ^ 2 * (s - ε n) ≤ (1 - ε n) ^ 2 * (s - ε m) := by
        have hdiff : (1 - ε n) ^ 2 * (s - ε m) - (1 - ε m) ^ 2 * (s - ε n) =
            (ε m - ε n) * ((2 - ε m - ε n) * (s - 1) + (1 - ε m) * (1 - ε n)) := by ring
        have h1 : 0 ≤ ε m - ε n := by linarith
        have h2 : 0 ≤ (2 - ε m - ε n) * (s - 1) + (1 - ε m) * (1 - ε n) := by nlinarith [hε1 m, hε1 n]
        nlinarith
      have hmul := mul_le_mul_of_nonneg_right hpoly (mul_nonneg hnn (sq_nonneg (s - 1)))
      linarith
    · exact le_rfl
  have hG_meas : ∀ n, Measurable (G n) := by
    intro n
    have hcont_neg : Continuous (fun s : ℝ ↦ negPartTrace (pencil_isHermitian s ρ σ)) :=
      continuous_negPartTrace_pencil ρ σ
    refine Measurable.ite measurableSet_Iio ?_ (Measurable.ite measurableSet_Ioi ?_ measurable_const)
    · exact ENNReal.measurable_ofReal.comp ((measurable_const.mul hcont_neg.measurable).div
        ((measurable_neg.add measurable_const).mul ((measurable_const.sub measurable_id).pow_const 2)))
    · exact ENNReal.measurable_ofReal.comp ((measurable_const.mul hcont_neg.measurable).div
        ((measurable_id.sub measurable_const).mul ((measurable_id.sub measurable_const).pow_const 2)))
  have hG_sup : ∀ s : ℝ, s ≠ 0 → s ≠ 1 →
      (⨆ n, G n s) = ENNReal.ofReal (negPartTrace (pencil_isHermitian s ρ σ) / (|s| * (s - 1) ^ 2)) := by
    intro s hs0 hs1
    apply tendsto_nhds_unique (tendsto_atTop_iSup fun m n hmn ↦ hG_mono hmn s)
    by_cases hlt0 : s < 0
    · have h1 : ∀ n, G n s = ENNReal.ofReal ((1 - ε n) ^ 2 * negPartTrace (pencil_isHermitian s ρ σ) /
          ((-s + ε n) * (1 - s) ^ 2)) := fun n ↦ by simp [G, hlt0]
      simp_rw [h1]
      apply (ENNReal.continuous_ofReal.tendsto _).comp
      have hnum : Tendsto (fun n ↦ (1 - ε n) ^ 2 * negPartTrace (pencil_isHermitian s ρ σ)) atTop
          (𝓝 (negPartTrace (pencil_isHermitian s ρ σ))) := by
        simpa using ((tendsto_const_nhds.sub hε_tend).pow 2).mul_const _
      have hden : Tendsto (fun n ↦ (-s + ε n) * (1 - s) ^ 2) atTop (𝓝 ((-s) * (1 - s) ^ 2)) := by
        simpa using (tendsto_const_nhds.add hε_tend).mul_const _
      have hdiv := hnum.div hden (ne_of_gt (mul_pos (by linarith) (by positivity)))
      simpa [abs_of_neg hlt0, show (1 - s) ^ 2 = (s - 1) ^ 2 by ring] using hdiv
    · by_cases hgt1 : 1 < s
      · have h1 : ∀ n, G n s = ENNReal.ofReal ((1 - ε n) ^ 2 * negPartTrace (pencil_isHermitian s ρ σ) /
            ((s - ε n) * (s - 1) ^ 2)) := fun n ↦ by simp [G, hlt0, hgt1]
        simp_rw [h1]
        apply (ENNReal.continuous_ofReal.tendsto _).comp
        have hnum : Tendsto (fun n ↦ (1 - ε n) ^ 2 * negPartTrace (pencil_isHermitian s ρ σ)) atTop
            (𝓝 (negPartTrace (pencil_isHermitian s ρ σ))) := by
          simpa using ((tendsto_const_nhds.sub hε_tend).pow 2).mul_const _
        have hden : Tendsto (fun n ↦ (s - ε n) * (s - 1) ^ 2) atTop (𝓝 (s * (s - 1) ^ 2)) := by
          simpa using (tendsto_const_nhds.sub hε_tend).mul_const _
        have hdiv := hnum.div hden (ne_of_gt (mul_pos (by linarith) (by positivity)))
        simpa [abs_of_pos (by linarith : 0 < s)] using hdiv
      · have hmem : s ∈ Icc (0 : ℝ) 1 := ⟨not_lt.mp hlt0, not_lt.mp hgt1⟩
        simp only [G, hlt0, hgt1, ↓reduceIte, negPartTrace_pencil_eq_zero_of_mem_Icc hmem.1 hmem.2,
          zero_div, ENNReal.ofReal_zero]
        exact tendsto_const_nhds
  have hRHS_tend : Tendsto (fun n ↦ ∫⁻ s : ℝ, G n s ∂volume) atTop
      (𝓝 (∫⁻ s : ℝ, ENNReal.ofReal (negPartTrace (pencil_isHermitian s ρ σ) / (|s| * (s - 1) ^ 2)) ∂volume)) := by
    have hsup_int : (⨆ n, ∫⁻ s : ℝ, G n s ∂volume) =
        ∫⁻ s : ℝ, ENNReal.ofReal (negPartTrace (pencil_isHermitian s ρ σ) / (|s| * (s - 1) ^ 2)) ∂volume := by
      rw [← MeasureTheory.lintegral_iSup hG_meas hG_mono]
      apply lintegral_congr_ae
      filter_upwards [ae_iff.mpr (show volume ({(0 : ℝ), 1} : Set ℝ) = 0 by simp)] with s hs
      simp only [mem_singleton_iff, mem_insert_iff, not_or] at hs
      exact hG_sup s hs.1 hs.2
    rw [← hsup_int]
    exact tendsto_atTop_iSup fun m n hmn ↦ lintegral_mono (hG_mono hmn)
  simp_rw [hRHS_eq] at hLHS_tend
  exact tendsto_nhds_unique hLHS_tend hRHS_tend

/-- **Eq. (3.7) (Frenkel's Integral Formula under Support Inclusion `suppSubset ρ σ`, Gap 4B)**:
Valid for arbitrary (possibly rank-deficient) finite-dimensional density operators `ρ, σ`
satisfying `supp(ρ) ⊆ supp(σ)`. -/
theorem relEntropy_frenkel_integral_of_suppSubset {ρ σ : DensityOp d} (hsupp : suppSubset ρ σ) :
    relEntropy ρ σ * ENNReal.ofReal (Real.log 2) =
      ∫⁻ t : ℝ, ENNReal.ofReal (negPartTrace (pencil_isHermitian t ρ σ) / (|t| * (t - 1) ^ 2)) ∂volume := by
  -- Compress onto `supp(σ)` via the subspace isometry `V : Matrix d {j // 0 < σ.eigvals j} ℂ`
  set S_pos : Finset d := Finset.univ.filter fun j : d ↦ 0 < σ.eigvals j
  let d' := {j : d // j ∈ S_pos}
  set U : Matrix d d ℂ := (σ.eigUnitary : Matrix d d ℂ)
  let V : Matrix d d' ℂ := Matrix.of fun i k ↦ U i k.1
  have hVHV : Vᴴ * V = 1 := by
    ext a b
    have h := congr_fun (congr_fun (Unitary.coe_star_mul_self σ.eigUnitary) a.1) b.1
    simpa [V, U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      Subtype.ext_iff] using h
  have hσ_comp : V * (Vᴴ * σ.mat * V) * Vᴴ = σ.mat := by
    have hVV : V * Vᴴ = U * Matrix.diagonal (fun j : d ↦ if j ∈ S_pos then (1 : ℂ) else 0) * star U := by
      ext i j
      simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.mul_diagonal, Matrix.star_apply]
      rw [← Finset.sum_subtype S_pos (fun _ ↦ Iff.rfl)]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr rfl; intro k hk
      simp [S_pos, Finset.mem_filter.mp hk]
    have hD_idem : Matrix.diagonal (fun j : d ↦ if j ∈ S_pos then (1 : ℂ) else 0) *
        Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) = Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) := by
      rw [Matrix.diagonal_mul_diagonal]; congr 1; ext j
      simp only [Function.comp_apply, S_pos, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h
      · exact one_mul _
      · have h0 : σ.eigvals j = 0 := le_antisymm (not_lt.mp h) (σ.eigvals_nonneg j)
        simp [h0]
    have hD_idem_r : Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) *
        Matrix.diagonal (fun j : d ↦ if j ∈ S_pos then (1 : ℂ) else 0) =
        Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) := by
      rw [Matrix.diagonal_mul_diagonal]; congr 1; ext j
      simp only [Function.comp_apply, S_pos, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h
      · exact mul_one _
      · have h0 : σ.eigvals j = 0 := le_antisymm (not_lt.mp h) (σ.eigvals_nonneg j)
        simp [h0]
    calc V * (Vᴴ * σ.mat * V) * Vᴴ
        = (V * Vᴴ) * σ.mat * (V * Vᴴ) := by simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal (fun j : d ↦ if j ∈ S_pos then (1 : ℂ) else 0) *
            ((star U * U) * Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) * (star U * U)) *
            Matrix.diagonal (fun j : d ↦ if j ∈ S_pos then (1 : ℂ) else 0) * star U := by
          rw [hVV]; conv_lhs => rw [density_spectral_eq σ]; simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal (fun j : d ↦ if j ∈ S_pos then (1 : ℂ) else 0) *
            Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) *
            Matrix.diagonal (fun j : d ↦ if j ∈ S_pos then (1 : ℂ) else 0)) * star U := by
          rw [Unitary.coe_star_mul_self σ.eigUnitary, Matrix.one_mul, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = σ.mat := by rw [hD_idem, hD_idem_r, ← density_spectral_eq σ]
  have hρ_comp : V * (Vᴴ * ρ.mat * V) * Vᴴ = ρ.mat := by
    have hVV : V * Vᴴ = U * Matrix.diagonal (fun j : d ↦ if j ∈ S_pos then (1 : ℂ) else 0) * star U := by
      ext i j
      simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.mul_diagonal, Matrix.star_apply]
      rw [← Finset.sum_subtype S_pos (fun _ ↦ Iff.rfl)]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr rfl; intro k hk
      simp [S_pos, Finset.mem_filter.mp hk]
    have hVV_ρ : (V * Vᴴ) * ρ.mat = ρ.mat := by
      rw [hVV]; conv_lhs => rw [density_spectral_eq ρ]
      set Uρ : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
      have hcomm : Matrix.diagonal (fun j : d ↦ if j ∈ S_pos then (1 : ℂ) else 0) *
          (star U * Uρ) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) =
          (star U * Uρ) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) := by
        ext j i
        simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Function.comp_apply,
          S_pos, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs with hj
        · simp
        · have hj0 : σ.eigvals j = 0 := le_antisymm (not_lt.mp hj) (σ.eigvals_nonneg j)
          by_cases hi0 : ρ.eigvals i = 0
          · simp [hi0]
          · have h0 := hsupp i j hi0 hj0
            simp [U, Uρ, h0]
      calc U * Matrix.diagonal (fun j : d ↦ if j ∈ S_pos then (1 : ℂ) else 0) * star U *
            (Uρ * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star Uρ)
          = U * (Matrix.diagonal (fun j : d ↦ if j ∈ S_pos then (1 : ℂ) else 0) *
              (star U * Uρ) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals)) * star Uρ := by
            simp only [Matrix.mul_assoc]
        _ = U * ((star U * Uρ) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals)) * star Uρ := by
            rw [hcomm]
        _ = (U * star U) * Uρ * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star Uρ := by
            simp only [Matrix.mul_assoc]
        _ = ρ.mat := by rw [Unitary.coe_mul_star_self σ.eigUnitary, Matrix.one_mul, ← density_spectral_eq ρ]
    have hρ_VV : ρ.mat * (V * Vᴴ) = ρ.mat := by
      have h := congr_arg Matrix.conjTranspose hVV_ρ
      simpa [Matrix.conjTranspose_mul, ρ.isHermitian.eq, Matrix.mul_assoc] using h
    calc V * (Vᴴ * ρ.mat * V) * Vᴴ
        = (V * Vᴴ) * ρ.mat * (V * Vᴴ) := by simp only [Matrix.mul_assoc]
      _ = ρ.mat := by rw [hVV_ρ, hρ_VV]
  let ρ' : DensityOp d' :=
    { mat := Vᴴ * ρ.mat * V
      posSemidef := by simpa [Matrix.conjTranspose_conjTranspose] using ρ.posSemidef.mul_mul_conjTranspose_same Vᴴ
      trace_one := by
        have h : (Vᴴ * ρ.mat * V).trace = (V * (Vᴴ * ρ.mat * V) * Vᴴ).trace := by
          rw [Matrix.trace_mul_cycle, Matrix.mul_assoc, hVHV, Matrix.one_mul]
        rw [h, hρ_comp, ρ.trace_one] }
  let σ' : DensityOp d' :=
    { mat := Vᴴ * σ.mat * V
      posSemidef := by simpa [Matrix.conjTranspose_conjTranspose] using σ.posSemidef.mul_mul_conjTranspose_same Vᴴ
      trace_one := by
        have h : (Vᴴ * σ.mat * V).trace = (V * (Vᴴ * σ.mat * V) * Vᴴ).trace := by
          rw [Matrix.trace_mul_cycle, Matrix.mul_assoc, hVHV, Matrix.one_mul]
        rw [h, hσ_comp, σ.trace_one] }
  have hσ'_pd : σ'.mat.PosDef := by
    have hdiag : σ'.mat = Matrix.diagonal (fun k : d' ↦ (σ.eigvals k.1 : ℂ)) := by
      ext a b
      simp only [σ', V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.diagonal_apply]
      have h := congr_fun (congr_fun (by
        have h1 := density_spectral_eq σ
        have h2 := congr_arg (fun M ↦ star U * M * U) h1
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star U) U,
          Unitary.coe_star_mul_self σ.eigUnitary, Matrix.one_mul, Matrix.mul_one] at h2
        exact h2 : star U * σ.mat * U = Matrix.diagonal (Complex.ofReal ∘ σ.eigvals)) a.1) b.1
      simpa [U, Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply, Subtype.ext_iff] using h
    rw [hdiag, Matrix.posDef_diagonal_iff]
    intro k
    exact_mod_cast (Finset.mem_filter.mp k.2).2
  have hneg_eq : ∀ t : ℝ, negPartTrace (pencil_isHermitian t ρ σ) = negPartTrace (pencil_isHermitian t ρ' σ') := by
    intro t
    have hmat : V * (((1 - t : ℝ) : ℂ) • ρ'.mat + (t : ℂ) • σ'.mat) * Vᴴ =
        ((1 - t : ℝ) : ℂ) • ρ.mat + (t : ℂ) • σ.mat := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hρ_comp, hσ_comp]
    set B := ((1 - t : ℝ) : ℂ) • ρ'.mat + (t : ℂ) • σ'.mat
    have hcp : (V * B * Vᴴ).charpoly * Polynomial.X ^ Fintype.card d' =
        B.charpoly * Polynomial.X ^ Fintype.card d := by
      have h := charpoly_mul_rect_eq (V * B) Vᴴ
      rw [Matrix.mul_assoc Vᴴ V B, hVHV, Matrix.one_mul] at h
      exact h
    rw [hmat] at hcp
    exact spectral_sum_eq_of_charpoly_mul_X_pow (pencil_isHermitian t ρ σ) (pencil_isHermitian t ρ' σ')
      hcp (by simp)
  have hrel_eq : relEntropy ρ σ = relEntropy ρ' σ' := by
    have hS_eq : vonNeumannEntropy ρ = vonNeumannEntropy ρ' := by
      have hcp : ρ.mat.charpoly * Polynomial.X ^ Fintype.card d' =
          ρ'.mat.charpoly * Polynomial.X ^ Fintype.card d := by
        have h := charpoly_mul_rect_eq (V * ρ'.mat) Vᴴ
        rw [hρ_comp, Matrix.mul_assoc Vᴴ V ρ'.mat, hVHV, Matrix.one_mul] at h
        exact h
      unfold vonNeumannEntropy DensityOp.eigvals
      congr 1
      exact spectral_sum_eq_of_charpoly_mul_X_pow ρ.isHermitian ρ'.isHermitian hcp (by simp [Real.negMulLog])
    -- Both `relEntropy ρ σ` and `relEntropy ρ' σ'` are finite; compare via trace-log!
    have htr_eq : ((ρ.mat * ((σ.eigUnitary : Matrix d d ℂ) *
        Matrix.diagonal (fun j ↦ if σ.eigvals j = 0 then (0 : ℂ) else (Real.log (σ.eigvals j) : ℂ)) *
        star (σ.eigUnitary : Matrix d d ℂ))).trace).re =
        ((ρ'.mat * ((σ'.eigUnitary : Matrix d' d' ℂ) *
          Matrix.diagonal (fun k ↦ (Real.log (σ'.eigvals k) : ℂ)) *
          star (σ'.eigUnitary : Matrix d' d' ℂ))).trace).re := by
      -- Since `σ'.mat = diag(σ.eigvals k.1)`, `L_{σ'} = diag(log (σ.eigvals k.1))`!
      set Lσ := U * Matrix.diagonal (fun j ↦ if σ.eigvals j = 0 then (0 : ℂ) else (Real.log (σ.eigvals j) : ℂ)) * star U
      set Lσ' := (σ'.eigUnitary : Matrix d' d' ℂ) * Matrix.diagonal (fun k ↦ (Real.log (σ'.eigvals k) : ℂ)) *
        star (σ'.eigUnitary : Matrix d' d' ℂ)
      have hL_rel : V * Lσ' * Vᴴ = Lσ := by
        have hL'_diag : Lσ' = Matrix.diagonal (fun k : d' ↦ (Real.log (σ.eigvals k.1) : ℂ)) := by
          have hσ'_diag : σ'.mat = Matrix.diagonal (fun k : d' ↦ (σ.eigvals k.1 : ℂ)) := by
            ext a b
            have h := congr_fun (congr_fun (by
              have h1 := density_spectral_eq σ
              have h2 := congr_arg (fun M ↦ star U * M * U) h1
              simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star U) U,
                Unitary.coe_star_mul_self σ.eigUnitary, Matrix.one_mul, Matrix.mul_one] at h2
              exact h2 : star U * σ.mat * U = Matrix.diagonal (Complex.ofReal ∘ σ.eigvals)) a.1) b.1
            simpa [σ', V, U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
              Matrix.star_apply, Matrix.diagonal_apply, Subtype.ext_iff] using h
          set U' := (σ'.eigUnitary : Matrix d' d' ℂ)
          have hcomm : U' * Matrix.diagonal (Complex.ofReal ∘ σ'.eigvals) =
              Matrix.diagonal (fun k : d' ↦ (σ.eigvals k.1 : ℂ)) * U' := by
            have h1 := (density_spectral_eq σ').symm.trans hσ'_diag
            have h2 := congr_arg (fun M ↦ M * U') h1
            simp only [Matrix.mul_assoc, Unitary.coe_star_mul_self σ'.eigUnitary, Matrix.mul_one] at h2
            exact h2
          have hcomm_log : U' * Matrix.diagonal (fun k ↦ (Real.log (σ'.eigvals k) : ℂ)) =
              Matrix.diagonal (fun k : d' ↦ (Real.log (σ.eigvals k.1) : ℂ)) * U' := by
            ext a b
            have h := congr_fun (congr_fun hcomm a) b
            simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply] at h ⊢
            by_cases h0 : U' a b = 0
            · simp [h0]
            · have heig : σ'.eigvals b = σ.eigvals a.1 :=
                Complex.ofReal_injective (mul_left_cancel₀ h0 (by rw [h, mul_comm]))
              rw [heig, mul_comm]
          calc Lσ' = (U' * Matrix.diagonal (fun k ↦ (Real.log (σ'.eigvals k) : ℂ))) * star U' := rfl
            _ = Matrix.diagonal (fun k : d' ↦ (Real.log (σ.eigvals k.1) : ℂ)) * (U' * star U') := by
              rw [hcomm_log, Matrix.mul_assoc]
            _ = Matrix.diagonal (fun k : d' ↦ (Real.log (σ.eigvals k.1) : ℂ)) := by
              rw [Unitary.coe_mul_star_self σ'.eigUnitary, Matrix.mul_one]
        rw [hL'_diag]
        ext i j
        simp only [Lσ, V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Matrix.mul_diagonal, Matrix.star_apply]
        rw [← Finset.sum_subtype S_pos (fun _ ↦ Iff.rfl)]
        rw [← Finset.sum_filter]
        symm
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k ↦ k ∈ S_pos)]
        have hzero_rest : ∑ k ∈ Finset.univ.filter (fun k ↦ k ∉ S_pos),
            U i k * (if σ.eigvals k = 0 then (0 : ℂ) else (Real.log (σ.eigvals k) : ℂ)) * star (U j k) = 0 := by
          apply Finset.sum_eq_zero; intro k hk
          have hnot := (Finset.mem_filter.mp hk).2
          simp only [S_pos, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
          have h0 : σ.eigvals k = 0 := le_antisymm hnot (σ.eigvals_nonneg k)
          simp [h0]
        rw [hzero_rest, add_zero]
        apply Finset.sum_congr rfl; intro k hk
        have hpos : 0 < σ.eigvals k := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).2).2
        simp [ne_of_gt hpos]
      congr 1
      rw [← hρ_comp, ← hL_rel]
      calc (V * ρ'.mat * Vᴴ * (V * Lσ' * Vᴴ)).trace
          = (V * (ρ'.mat * (Vᴴ * V) * Lσ') * Vᴴ).trace := by simp only [Matrix.mul_assoc]
        _ = (V * (ρ'.mat * Lσ') * Vᴴ).trace := by rw [hVHV, Matrix.mul_one]
        _ = (Vᴴ * V * (ρ'.mat * Lσ')).trace := by rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
        _ = (ρ'.mat * Lσ').trace := by rw [hVHV, Matrix.one_mul]
    -- Compare `relEntropy ρ σ` and `relEntropy ρ' σ'` using `ENNReal.ofReal` + `htr_eq` + `hS_eq`
    have h1 := (relEntropy_toReal_eq_trace_log_posDef (ρ := ρ') hσ'_pd)
    have hcol : ∀ i : d, ∑ j : d,
        ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 = 1 := by
      intro i
      have hW : (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ))ᴴ *
          (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) = 1 := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (star (σ.eigUnitary : Matrix d d ℂ))ᴴ,
          ← Matrix.star_eq_conjTranspose, star_star, Unitary.coe_mul_star_self σ.eigUnitary,
          Matrix.one_mul, ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self ρ.eigUnitary]
      have h := congr_arg Complex.re (congr_fun (congr_fun hW i) i)
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
        Complex.re_sum, Complex.one_re] at h
      rw [← h]; apply Finset.sum_congr rfl; intro j _
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    have htr_L : ((ρ.mat * ((σ.eigUnitary : Matrix d d ℂ) *
        Matrix.diagonal (fun j ↦ if σ.eigvals j = 0 then (0 : ℂ) else (Real.log (σ.eigvals j) : ℂ)) *
        star (σ.eigUnitary : Matrix d d ℂ))).trace).re =
        ∑ i : d, ∑ j : d,
          ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
            (ρ.eigvals i * Real.log (σ.eigvals j)) := by
      have hW_def : (ρ.mat * ((σ.eigUnitary : Matrix d d ℂ) *
          Matrix.diagonal (fun j ↦ if σ.eigvals j = 0 then (0 : ℂ) else (Real.log (σ.eigvals j) : ℂ)) *
          star (σ.eigUnitary : Matrix d d ℂ))).trace =
          ∑ i : d, ∑ j : d,
            ((‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 : ℝ) : ℂ) *
              ((ρ.eigvals i : ℂ) * (if σ.eigvals j = 0 then (0 : ℂ) else (Real.log (σ.eigvals j) : ℂ))) := by
        rw [density_spectral_eq ρ]; simp only [Matrix.mul_assoc]; rw [Matrix.trace_mul_cycle]
        simp only [Matrix.mul_assoc]
        set W := star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)
        have hW_star : star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ) = Wᴴ := by
          simp [W, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose]
        have hcy : (star (σ.eigUnitary : Matrix d d ℂ) * ((ρ.eigUnitary : Matrix d d ℂ) *
            (Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * (star (ρ.eigUnitary : Matrix d d ℂ) *
            ((σ.eigUnitary : Matrix d d ℂ) *
              Matrix.diagonal (fun j ↦ if σ.eigvals j = 0 then (0 : ℂ) else (Real.log (σ.eigvals j) : ℂ))))))).trace =
            (W * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * Wᴴ *
              Matrix.diagonal (fun j ↦ if σ.eigvals j = 0 then (0 : ℂ) else (Real.log (σ.eigvals j) : ℂ))).trace := by
          simp only [Matrix.mul_assoc, W, hW_star]
        rw [hcy]
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.mul_diagonal,
          Matrix.diagonal_mul, Matrix.conjTranspose_apply, Function.comp_apply]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
        rw [mul_comm (W j i) (ρ.eigvals i : ℂ), mul_assoc, ← mul_assoc (W j i),
          Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; ring
      rw [hW_def, Complex.re_sum]
      apply Finset.sum_congr rfl; intro i _; rw [Complex.re_sum]
      apply Finset.sum_congr rfl; intro j _
      by_cases hσj : σ.eigvals j = 0 <;> simp [hσj]
    have hLHS_ofReal : relEntropy ρ σ = ENNReal.ofReal (-vonNeumannEntropy ρ -
        ((ρ.mat * ((σ.eigUnitary : Matrix d d ℂ) *
          Matrix.diagonal (fun j ↦ if σ.eigvals j = 0 then (0 : ℂ) else (Real.log (σ.eigvals j) : ℂ)) *
          star (σ.eigUnitary : Matrix d d ℂ))).trace).re / Real.log 2) := by
      unfold relEntropy; rw [if_pos hsupp]; congr 1
      rw [htr_L]
      have hsplit : ∑ i : d, ∑ j : d,
          ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
            (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j))) =
          (∑ i : d, ρ.eigvals i * Real.log (ρ.eigvals i)) -
          (∑ i : d, ∑ j : d, ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
            (ρ.eigvals i * Real.log (σ.eigvals j))) := by
        have h1' : ∀ i j, ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
            (ρ.eigvals i * (Real.log (ρ.eigvals i) - Real.log (σ.eigvals j))) =
            ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
              (ρ.eigvals i * Real.log (ρ.eigvals i)) -
            ‖(star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2 *
              (ρ.eigvals i * Real.log (σ.eigvals j)) := fun _ _ ↦ by ring
        simp_rw [h1', Finset.sum_sub_distrib, ← Finset.sum_mul, hcol, one_mul]
      rw [hsplit, sub_div]
      unfold vonNeumannEntropy
      have hneg : -(∑ i : d, Real.negMulLog (ρ.eigvals i)) / Real.log 2 =
          (∑ i : d, ρ.eigvals i * Real.log (ρ.eigvals i)) / Real.log 2 := by
        congr 1; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; simp [Real.negMulLog]
      linarith
    rw [hLHS_ofReal, hS_eq, htr_eq, ← h1.2, ENNReal.ofReal_toReal h1.1]
  rw [hrel_eq, relEntropy_frenkel_integral_of_posDef_right hσ'_pd]
  apply lintegral_congr; intro t
  rw [hneg_eq t]

/-- **Eq. (3.8) (Hockey-Stick Integral Representation under Support Inclusion `suppSubset ρ σ`, Gap 4B)**:
Valid for arbitrary (possibly rank-deficient) finite-dimensional density operators `ρ, σ`
satisfying `supp(ρ) ⊆ supp(σ)`. -/
theorem relEntropy_hockeyStick_integral_of_suppSubset {ρ σ : DensityOp d} (hsupp : suppSubset ρ σ) :
    relEntropy ρ σ * ENNReal.ofReal (Real.log 2) =
      ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal ((hockeyStick s ρ σ - max (1 - s) 0) / s) ∂volume := by
  rw [relEntropy_frenkel_integral_of_suppSubset hsupp]
  exact frenkel_lintegral_eq_hockeyStick_lintegral ρ σ

end RankDeficientFrenkel

end PolarCodes
