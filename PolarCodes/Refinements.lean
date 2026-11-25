/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.QuantumChannels
import PolarCodes.QJJS
import PolarCodes.DephasingSDPI
import PolarCodes.Bhattacharyya

/-!
# Refinements of Intermediate Propositions and Theorems

This module closes the intermediate formalization refinements matching the manuscript:
1. **Equal-Support Lemma 3.2** (`lemma_3_2_hockeyStick_measure_equalSupport`): Extends the
   simultaneous hockey-stick probability measure representation from strictly positive definite
   states to all density-operator pairs with equal support (`suppSubset ρ σ ∧ suppSubset σ ρ`).
2. **Proposition 3.3 Classical Equality** (`prop_3_3_qjjs_classical_equality`): Proves that
   every symmetric classical binary pair `diag((1+x)/2, (1-x)/2)` vs `diag((1-x)/2, (1+x)/2)`
   attains equality in Proposition 3.3 for all `x ∈ [0, 1]` (including `x = 1`, where both
   sides equal `⊤`).
3. **Relative-Entropy Theorem 1.3** (`relEntropy_dephaseState_eq`,
   `theorem_1_3_dephasing_sdpi_relEntropy`, `theorem_1_3_equatorial_equality_relEntropy`):
   Establishes `supp(Ψ_p) ⊆ supp(Ψ_{1/2})` and `D(Ψ_p ‖ Ψ_{1/2}) = S(Ψ_{1/2}) - S(Ψ_p)`
   directly via Umegaki relative entropy, stating Theorem 1.3 and equatorial equality in terms
   of `(relEntropy (dephaseState p ...) (dephaseState (1/2) ...)).toReal`.
4. **Channel-Level Equivalence for Proposition 2.2 (D2)–(D3)** (`CQChannel.IsoEquiv`,
   `CQChannel.ChannelEquiv`, `prop_2_2_D3_isoEquiv_pure`, `prop_2_2_D3_channelEquiv`,
   `prop_2_2_D2_channelEquiv`): Formalizes output-isometry equivalence and reversible CPTP
   channel equivalence, proving all five canonical and polarization dualities of
   Proposition 2.2 at the channel level with entropic equalities as immediate corollaries.
-/

open Matrix BigOperators Real MeasureTheory Set Filter
open scoped ComplexOrder ENNReal Topology

namespace PolarCodes

universe u

/-! ### Helper Lemmas on Support, Diagonalization, and Relative Entropy -/

section Helpers

variable {d : Type*} [Fintype d] [DecidableEq d]

private lemma suppSubset_ker_aux {ρ σ : DensityOp d} (hsupp : suppSubset ρ σ)
    {v : d → ℂ} (hv : σ.mat *ᵥ v = 0) : ρ.mat *ᵥ v = 0 := by
  have h1 : star v ⬝ᵥ (σ.mat *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
  have hspec_σ : σ.mat = (σ.eigUnitary : Matrix d d ℂ) *
      Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) * star (σ.eigUnitary : Matrix d d ℂ) :=
    σ.posSemidef.isHermitian.spectral_theorem
  set w := star (σ.eigUnitary : Matrix d d ℂ) *ᵥ v
  have hsum_σ : ∑ j : d, σ.eigvals j * ‖w j‖ ^ 2 = 0 := by
    have hre : (star v ⬝ᵥ (σ.mat *ᵥ v)).re = ∑ j : d, σ.eigvals j * ‖w j‖ ^ 2 := by
      rw [hspec_σ]
      have hassoc : ((σ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) *
          star (σ.eigUnitary : Matrix d d ℂ)) *ᵥ v =
          (σ.eigUnitary : Matrix d d ℂ) *ᵥ (Matrix.diagonal (Complex.ofReal ∘ σ.eigvals) *ᵥ w) := by
        simp [w, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [hassoc, ← Matrix.vecMul_mulVec]
      have hvec : star v ᵥ* (σ.eigUnitary : Matrix d d ℂ) = star w := by
        ext j
        simp [w, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.star_apply, mul_comm]
      rw [hvec, dotProduct]
      simp only [Matrix.mulVec_diagonal, Function.comp_apply, Complex.re_sum]
      apply Finset.sum_congr rfl; intro j _
      have hsq : star (w j) * w j = ((‖w j‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc (star (w j) * ((σ.eigvals j : ℂ) * w j)).re
          = (((σ.eigvals j : ℂ) * (star (w j) * w j))).re := by ring_nf
        _ = (((σ.eigvals j * ‖w j‖ ^ 2 : ℝ) : ℂ)).re := by rw [hsq]; push_cast; ring_nf
        _ = σ.eigvals j * ‖w j‖ ^ 2 := Complex.ofReal_re _
    rw [← hre, h1, Complex.zero_re]
  have hw_zero : ∀ j : d, σ.eigvals j ≠ 0 → w j = 0 := by
    intro j hj
    have hterm : σ.eigvals j * ‖w j‖ ^ 2 = 0 := by
      have hnn : ∀ k ∈ Finset.univ, 0 ≤ σ.eigvals k * ‖w k‖ ^ 2 := fun k _ ↦
        mul_nonneg (σ.eigvals_nonneg k) (sq_nonneg _)
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_σ j (Finset.mem_univ j)
    rcases mul_eq_zero.mp hterm with h0 | h0
    · exact absurd h0 hj
    · exact norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
  have hsum_ρ : star v ⬝ᵥ (ρ.mat *ᵥ v) = 0 := by
    have hspec_ρ : ρ.mat = (ρ.eigUnitary : Matrix d d ℂ) *
        Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star (ρ.eigUnitary : Matrix d d ℂ) :=
      ρ.posSemidef.isHermitian.spectral_theorem
    set u := star (ρ.eigUnitary : Matrix d d ℂ) *ᵥ v
    have hu_expr : ∀ i : d, u i = ∑ j : d,
        ((star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ)) i j) * w j := by
      intro i
      have hUσ : (σ.eigUnitary : Matrix d d ℂ) * star (σ.eigUnitary : Matrix d d ℂ) = 1 :=
        Unitary.coe_mul_star_self σ.eigUnitary
      have hv_eq : v = (σ.eigUnitary : Matrix d d ℂ) *ᵥ w := by
        simp [w, Matrix.mulVec_mulVec, hUσ]
      calc u i = (star (ρ.eigUnitary : Matrix d d ℂ) *ᵥ ((σ.eigUnitary : Matrix d d ℂ) *ᵥ w)) i := by
              rw [← hv_eq]
        _ = ((star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ)) *ᵥ w) i := by
              rw [Matrix.mulVec_mulVec]
        _ = _ := rfl
    have hρu : ∀ i : d, ρ.eigvals i ≠ 0 → u i = 0 := by
      intro i hi
      rw [hu_expr i]
      apply Finset.sum_eq_zero; intro j _
      by_cases hj : σ.eigvals j = 0
      · have hW0 : (star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ)) i j = 0 := by
          have h := hsupp i j hi hj
          have hst : (star (σ.eigUnitary : Matrix d d ℂ) * (ρ.eigUnitary : Matrix d d ℂ)) j i =
              star ((star (ρ.eigUnitary : Matrix d d ℂ) * (σ.eigUnitary : Matrix d d ℂ)) i j) := by
            simp [Matrix.mul_apply, Matrix.star_apply, mul_comm]
          rw [hst] at h
          exact star_eq_zero.mp h
        rw [hW0, zero_mul]
      · rw [hw_zero j hj, mul_zero]
    rw [hspec_ρ]
    have hassoc : ((ρ.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *
        star (ρ.eigUnitary : Matrix d d ℂ)) *ᵥ v =
        (ρ.eigUnitary : Matrix d d ℂ) *ᵥ (Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *ᵥ u) := by
      simp [u, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hassoc, ← Matrix.vecMul_mulVec]
    have hvec : star v ᵥ* (ρ.eigUnitary : Matrix d d ℂ) = star u := by
      ext i
      simp [u, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.star_apply, mul_comm]
    rw [hvec, dotProduct]
    apply Finset.sum_eq_zero; intro i _
    simp only [Matrix.mulVec_diagonal, Function.comp_apply]
    by_cases hi : ρ.eigvals i = 0
    · simp [hi]
    · simp [hρu i hi]
  exact ρ.posSemidef.mulVec_eq_zero_of_dotProduct_eq_zero hsum_ρ

private lemma relEntropy_eq_trace_log {α : Type*} [Fintype α] [DecidableEq α]
    (A B : DensityOp α) (hsupp : suppSubset A B) :
    let L_B : Matrix α α ℂ :=
      (B.eigUnitary : Matrix α α ℂ) *
      Matrix.diagonal (fun j ↦ if B.eigvals j = 0 then (0 : ℂ) else (Real.log (B.eigvals j) : ℂ)) *
      star (B.eigUnitary : Matrix α α ℂ)
    relEntropy A B = ENNReal.ofReal (-vonNeumannEntropy A - (A.mat * L_B).trace.re / Real.log 2) := by
  intro L_B
  unfold relEntropy
  rw [if_pos hsupp]
  congr 1
  set W : Matrix α α ℂ := star (B.eigUnitary : Matrix α α ℂ) * (A.eigUnitary : Matrix α α ℂ)
  have hW_col : ∀ i : α, ∑ j : α, ‖W j i‖ ^ 2 = 1 := by
    intro i
    have hWW : star W * W = 1 := by
      simp only [W, star_mul, star_star, Matrix.mul_assoc]
      have h1 : (B.eigUnitary : Matrix α α ℂ) * star (B.eigUnitary : Matrix α α ℂ) = 1 :=
        Unitary.coe_mul_star_self B.eigUnitary
      have h2 : star (A.eigUnitary : Matrix α α ℂ) * (A.eigUnitary : Matrix α α ℂ) = 1 :=
        Unitary.coe_star_mul_self A.eigUnitary
      calc star (A.eigUnitary : Matrix α α ℂ) *
            ((B.eigUnitary : Matrix α α ℂ) * (star (B.eigUnitary : Matrix α α ℂ) * (A.eigUnitary : Matrix α α ℂ)))
          = star (A.eigUnitary : Matrix α α ℂ) *
            (((B.eigUnitary : Matrix α α ℂ) * star (B.eigUnitary : Matrix α α ℂ)) * (A.eigUnitary : Matrix α α ℂ)) := by
              simp [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.one_mul, h2]
    have hdiag := congr_fun (congr_fun hWW i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hdiag
    have hre := congr_arg Complex.re hdiag
    simp only [Complex.one_re, Complex.re_sum] at hre
    rw [← hre]
    apply Finset.sum_congr rfl; intro j _
    have hsq : star (W j i) * W j i = ((‖W j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hsq, Complex.ofReal_re]
  have hsplit : ∑ i : α, ∑ j : α,
      (A.eigvals i * (Real.log (A.eigvals i) - Real.log (B.eigvals j)) * ‖W j i‖ ^ 2) =
      (∑ i : α, A.eigvals i * Real.log (A.eigvals i)) -
      (∑ i : α, ∑ j : α, A.eigvals i * Real.log (B.eigvals j) * ‖W j i‖ ^ 2) := by
    simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.mul_sum, hW_col i, mul_one]
  have hS : (∑ i : α, A.eigvals i * Real.log (A.eigvals i)) / Real.log 2 = -vonNeumannEntropy A := by
    unfold vonNeumannEntropy
    rw [← Finset.sum_div, neg_eq_iff_eq_neg, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i _
    by_cases hi : A.eigvals i = 0
    · simp [hi]
    · simp only [Real.logb]; ring
  have hcross : (A.mat * L_B).trace.re =
      ∑ i : α, ∑ j : α, A.eigvals i * Real.log (B.eigvals j) * ‖W j i‖ ^ 2 := by
    have hspec_A : A.mat = (A.eigUnitary : Matrix α α ℂ) *
        Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * star (A.eigUnitary : Matrix α α ℂ) :=
      A.posSemidef.isHermitian.spectral_theorem
    let dB : α → ℂ := fun j ↦ if B.eigvals j = 0 then 0 else (Real.log (B.eigvals j) : ℂ)
    have htr : (A.mat * L_B).trace =
        (Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * (star W * Matrix.diagonal dB * W)).trace := by
      rw [hspec_A]
      have h1 : ((A.eigUnitary : Matrix α α ℂ) * Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *
          star (A.eigUnitary : Matrix α α ℂ)) * L_B =
          (A.eigUnitary : Matrix α α ℂ) * (Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *
          (star (A.eigUnitary : Matrix α α ℂ) * L_B)) := by simp [Matrix.mul_assoc]
      rw [h1, Matrix.trace_mul_comm]
      have h2 : Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *
          (star (A.eigUnitary : Matrix α α ℂ) * L_B) * (A.eigUnitary : Matrix α α ℂ) =
          Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *
          (star W * Matrix.diagonal dB * W) := by
        simp only [L_B, W, dB, star_mul, star_star, Matrix.mul_assoc]
      rw [h2]
    rw [htr, Matrix.trace, Matrix.diag]
    simp only [Complex.re_sum, Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Function.comp_apply]
    apply Finset.sum_congr rfl; intro i _
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl; intro j _
    simp only [Matrix.star_apply, dB]
    have hsq : star (W j i) * W j i = ((‖W j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    by_cases hj : B.eigvals j = 0
    · simp [hj, Real.log_zero]
    · simp only [hj, ↓reduceIte]
      have hcalc : (A.eigvals i : ℂ) * (star (W j i) * (Real.log (B.eigvals j) : ℂ) * W j i) =
          ((A.eigvals i * Real.log (B.eigvals j) * ‖W j i‖ ^ 2 : ℝ) : ℂ) := by
        calc _ = (A.eigvals i : ℂ) * (Real.log (B.eigvals j) : ℂ) * (star (W j i) * W j i) := by ring
          _ = _ := by rw [hsq]; push_cast; ring
      rw [hcalc, Complex.ofReal_re]
  rw [hsplit, sub_div, hS, hcross]

end Helpers

/-! ### Part 1: Equal-Support Lemma 3.2 (Gap 5.2) -/

section EqualSupportLemma32

/-- Isometric embedding `H = V H' Vᴴ` with `Vᴴ V = I` preserves `posPartTrace`. -/
lemma posPartTrace_eq_of_isom {d d' : Type*} [Fintype d] [DecidableEq d]
    [Fintype d'] [DecidableEq d']
    {H : Matrix d d ℂ} {H' : Matrix d' d' ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (V : Matrix d d' ℂ) (hVHV : Vᴴ * V = 1) (hmat : V * H' * Vᴴ = H) :
    posPartTrace hH = posPartTrace hH' := by
  have hle1 : posPartTrace hH ≤ posPartTrace hH' := by
    have hP_psd : (V * posPartMat hH' * Vᴴ).PosSemidef :=
      (posPartMat_posSemidef hH').mul_mul_conjTranspose_same V
    have hdiff_psd : (V * posPartMat hH' * Vᴴ - H).PosSemidef := by
      rw [← hmat]
      have hsub : V * posPartMat hH' * Vᴴ - V * H' * Vᴴ = V * negPartMat hH' * Vᴴ := by
        rw [← Matrix.sub_mul, ← Matrix.mul_sub]
        have hdecomp := posPartMat_sub_negPartMat hH'
        have heq : posPartMat hH' - H' = negPartMat hH' := by
          rw [← hdecomp]; abel
        rw [heq]
      rw [hsub]
      exact (negPartMat_posSemidef hH').mul_mul_conjTranspose_same V
    have hle := posPartTrace_le_trace_of_posSemidef hH hP_psd hdiff_psd
    have htr : (V * posPartMat hH' * Vᴴ).trace = (posPartMat hH').trace := by
      rw [Matrix.trace_mul_cycle, hVHV, Matrix.one_mul]
    rw [htr, posPartTrace_eq_trace hH'] at hle
    exact hle
  have hH'_eq : Vᴴ * H * V = H' := by
    rw [← hmat]
    calc Vᴴ * (V * H' * Vᴴ) * V = (Vᴴ * V) * H' * (Vᴴ * V) := by simp [Matrix.mul_assoc]
      _ = H' := by rw [hVHV, Matrix.one_mul, Matrix.mul_one]
  have hle2 : posPartTrace hH' ≤ posPartTrace hH := by
    have hP_psd : (Vᴴ * posPartMat hH * V).PosSemidef :=
      (posPartMat_posSemidef hH).conjTranspose_mul_mul_same V
    have hdiff_psd : (Vᴴ * posPartMat hH * V - H').PosSemidef := by
      rw [← hH'_eq]
      have hsub : Vᴴ * posPartMat hH * V - Vᴴ * H * V = Vᴴ * negPartMat hH * V := by
        rw [← Matrix.sub_mul, ← Matrix.mul_sub]
        have hdecomp := posPartMat_sub_negPartMat hH
        have heq : posPartMat hH - H = negPartMat hH := by
          rw [← hdecomp]; abel
        rw [heq]
      rw [hsub]
      exact (negPartMat_posSemidef hH).conjTranspose_mul_mul_same V
    have hle := posPartTrace_le_trace_of_posSemidef hH' hP_psd hdiff_psd
    have htr : (Vᴴ * posPartMat hH * V).trace.re ≤ (posPartMat hH).trace.re := by
      have hVV_le : (1 - V * Vᴴ).PosSemidef := by
        have hproj : (1 - V * Vᴴ) = (1 - V * Vᴴ)ᴴ * (1 - V * Vᴴ) := by
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_one, Matrix.one_mul]
          have hsq : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
            calc V * Vᴴ * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp [Matrix.mul_assoc]
              _ = V * Vᴴ := by rw [hVHV, Matrix.mul_one]
          rw [hsq]; abel
        rw [hproj]
        exact Matrix.posSemidef_conjTranspose_mul_self _
      have htr_eq : (Vᴴ * posPartMat hH * V).trace = (posPartMat hH * (V * Vᴴ)).trace := by
        rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
      have hdiff : ((posPartMat hH).trace - (Vᴴ * posPartMat hH * V).trace).re =
          (posPartMat hH * (1 - V * Vᴴ)).trace.re := by
        rw [htr_eq, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
      have hnn : 0 ≤ (posPartMat hH * (1 - V * Vᴴ)).trace.re :=
        trace_mul_posSemidef_nonneg (posPartMat_posSemidef hH) hVV_le
      rw [Complex.sub_re] at hdiff
      linarith
    rw [posPartTrace_eq_trace hH] at htr
    exact le_trans hle htr
  exact le_antisymm hle1 hle2

/-- **Lemma 3.2 (Simultaneous Hockey-Stick Representation under Equal Support)**:
For any finite-dimensional density operators `ρ, σ` with equal support
(`suppSubset ρ σ ∧ suppSubset σ ρ`), there exists a Borel probability measure `μ` supported
on a compact subinterval `[a, b] ⊂ (0, ∞)` with `∫ t dμ = 1` simultaneously representing
`E_s(ρ ‖ σ)`, `D(ρ ‖ σ)`, `D(σ ‖ ρ)`, and `QJS(ρ, σ)`. -/
theorem lemma_3_2_hockeyStick_measure_equalSupport {d : Type*} [Fintype d] [DecidableEq d]
    {ρ σ : DensityOp d} (hsupp : suppSubset ρ σ ∧ suppSubset σ ρ) :
    ∃ (a b : ℝ) (μ : Measure ℝ),
      0 < a ∧ a ≤ b ∧ IsProbabilityMeasure μ ∧ μ (Icc a b)ᶜ = 0 ∧
      (∀ s : ℝ, hockeyStick s ρ σ = ∫ t, max (t - s) 0 ∂μ) ∧
      (∫ t, t ∂μ = 1) ∧
      ((relEntropy ρ σ).toReal = ∫ t, (t * Real.logb 2 t - (t - 1) / Real.log 2) ∂μ) ∧
      ((relEntropy σ ρ).toReal = ∫ t, (-Real.logb 2 t + (t - 1) / Real.log 2) ∂μ) ∧
      (qjs ρ σ = ∫ t, (t / 2 * Real.logb 2 (2 * t / (1 + t)) +
        1 / 2 * Real.logb 2 (2 / (1 + t))) ∂μ) := by
  set S_pos : Finset d := Finset.univ.filter fun i : d ↦ 0 < ρ.eigvals i
  let d' := {i : d // i ∈ S_pos}
  set U : Matrix d d ℂ := (ρ.eigUnitary : Matrix d d ℂ)
  have hU_mul : U * star U = 1 := Unitary.coe_mul_star_self ρ.eigUnitary
  have hU_star : star U * U = 1 := Unitary.coe_star_mul_self ρ.eigUnitary
  let V : Matrix d d' ℂ := Matrix.of fun r k ↦ U r k.1
  have hVHV : Vᴴ * V = 1 := by
    ext j k
    simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    have h := congr_fun (congr_fun hU_star j.1) k.1
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h
    convert h using 2
    simp [Subtype.ext_iff]
  have hρ_ker : ∀ i ∉ S_pos, ρ.mat *ᵥ (fun r ↦ U r i) = 0 := by
    intro i hi
    have hi0 : ρ.eigvals i = 0 :=
      le_antisymm (not_lt.mp (by simpa [S_pos] using hi)) (ρ.eigvals_nonneg i)
    have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U :=
      ρ.posSemidef.isHermitian.spectral_theorem
    rw [hspec]
    have hvec : star U *ᵥ (fun r ↦ U r i) = Pi.single i 1 := by
      ext j
      have h := congr_fun (congr_fun hU_star j) i
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply, eq_comm] using h
    calc (U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U) *ᵥ (fun r ↦ U r i)
        = U *ᵥ (Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *ᵥ (star U *ᵥ (fun r ↦ U r i))) := by
            simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = U *ᵥ (Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *ᵥ Pi.single i 1) := by rw [hvec]
      _ = 0 := by
            have h0 : Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *ᵥ Pi.single i 1 = 0 := by
              ext j; simp [Matrix.mulVec_diagonal, Pi.single_apply, hi0]
            rw [h0, Matrix.mulVec_zero]
  have hσ_ker : ∀ i ∉ S_pos, σ.mat *ᵥ (fun r ↦ U r i) = 0 :=
    fun i hi ↦ suppSubset_ker_aux hsupp.2 (hρ_ker i hi)
  have hcompress : ∀ (τ : DensityOp d), (∀ i ∉ S_pos, τ.mat *ᵥ (fun r ↦ U r i) = 0) →
      V * (Vᴴ * τ.mat * V) * Vᴴ = τ.mat := by
    intro τ hker
    have hVV : V * Vᴴ = U * Matrix.diagonal (fun i : d ↦ if i ∈ S_pos then (1 : ℂ) else 0) * star U := by
      ext r s
      simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.diagonal_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ↓reduceIte, Matrix.star_apply]
      rw [← Finset.sum_coe_sort S_pos (fun i ↦ U r i * star (U s i))]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_mem_eq_inter,
        Finset.univ_inter]
      rfl
    have hPτ : (V * Vᴴ) * τ.mat = τ.mat := by
      rw [hVV]
      have hcomp : ∀ r s, ((U * Matrix.diagonal (fun i : d ↦ if i ∈ S_pos then (1 : ℂ) else 0) *
          star U) * τ.mat) r s = τ.mat r s := by
        intro r s
        have hτU : ∀ i ∉ S_pos, (star U * τ.mat) i s = 0 := by
          intro i hi
          have hherm : τ.matᴴ = τ.mat := τ.posSemidef.isHermitian
          have hcol := congr_fun (hker i hi) s
          simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hcol
          have hconj : star (∑ x : d, τ.mat s x * U x i) = 0 := by rw [hcol, star_zero]
          simp only [star_sum, star_mul'] at hconj
          have hentry : (star U * τ.mat) i s = ∑ x : d, star (U x i) * τ.mat x s := by
            simp [Matrix.mul_apply, Matrix.star_apply]
          rw [hentry]
          convert hconj using 2 with x
          have hxs : star (τ.mat s x) = τ.mat x s := by
            have := congr_fun (congr_fun hherm x) s
            simpa [Matrix.conjTranspose_apply] using this
          rw [hxs]
        calc ((U * Matrix.diagonal (fun i : d ↦ if i ∈ S_pos then (1 : ℂ) else 0) * star U) * τ.mat) r s
            = (U * (Matrix.diagonal (fun i : d ↦ if i ∈ S_pos then (1 : ℂ) else 0) * (star U * τ.mat))) r s := by
                simp [Matrix.mul_assoc]
          _ = ∑ i : d, U r i * (if i ∈ S_pos then (star U * τ.mat) i s else 0) := by
                simp [Matrix.mul_apply, Matrix.diagonal_apply]
          _ = ∑ i : d, U r i * (star U * τ.mat) i s := by
                apply Finset.sum_congr rfl; intro i _
                split_ifs with hi
                · rfl
                · rw [hτU i hi, mul_zero]
          _ = (U * (star U * τ.mat)) r s := by simp [Matrix.mul_apply]
          _ = τ.mat r s := by rw [← Matrix.mul_assoc, hU_mul, Matrix.one_mul]
      ext r s; exact hcomp r s
    have hτP : τ.mat * (V * Vᴴ) = τ.mat := by
      have h1 := congr_arg Matrix.conjTranspose hPτ
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        τ.posSemidef.isHermitian.eq] at h1
      simpa [Matrix.mul_assoc] using h1
    calc V * (Vᴴ * τ.mat * V) * Vᴴ = (V * Vᴴ) * τ.mat * (V * Vᴴ) := by simp [Matrix.mul_assoc]
      _ = τ.mat := by rw [hPτ, hτP]
  have hρ_comp := hcompress ρ hρ_ker
  have hσ_comp := hcompress σ hσ_ker
  let ρ' : DensityOp d' :=
    { mat := Vᴴ * ρ.mat * V
      posSemidef := ρ.posSemidef.conjTranspose_mul_mul_same V
      trace_one := by
        have htr : (Vᴴ * ρ.mat * V).trace = (V * (Vᴴ * ρ.mat * V) * Vᴴ).trace := by
          rw [Matrix.trace_mul_cycle, hVHV, Matrix.one_mul]
        rw [htr, hρ_comp, ρ.trace_one] }
  let σ' : DensityOp d' :=
    { mat := Vᴴ * σ.mat * V
      posSemidef := σ.posSemidef.conjTranspose_mul_mul_same V
      trace_one := by
        have htr : (Vᴴ * σ.mat * V).trace = (V * (Vᴴ * σ.mat * V) * Vᴴ).trace := by
          rw [Matrix.trace_mul_cycle, hVHV, Matrix.one_mul]
        rw [htr, hσ_comp, σ.trace_one] }
  have hρ'_pd : ρ'.mat.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨ρ'.posSemidef.isHermitian, fun x hx ↦ ?_⟩
    have hρ'_diag : ρ'.mat = Matrix.diagonal (fun k : d' ↦ (ρ.eigvals k.1 : ℂ)) := by
      have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U :=
        ρ.posSemidef.isHermitian.spectral_theorem
      have hVU : Vᴴ * U = Matrix.of fun (a : d') (b : d) ↦ if a.1 = b then 1 else 0 := by
        ext a b
        have h := congr_fun (congr_fun hU_star a.1) b
        simpa [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.star_apply,
          Matrix.one_apply] using h
      have hUV : star U * V = Matrix.of fun (a : d) (b : d') ↦ if a = b.1 then 1 else 0 := by
        ext a b
        have h := congr_fun (congr_fun hU_star a) b.1
        simpa [V, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h
      calc ρ'.mat = Vᴴ * (U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U) * V := by
              rw [← hspec]
        _ = (Vᴴ * U) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * (star U * V) := by
              simp [Matrix.mul_assoc]
        _ = Matrix.diagonal (fun k : d' ↦ (ρ.eigvals k.1 : ℂ)) := by
              rw [hVU, hUV]
              ext j k
              simp [Matrix.mul_apply, Matrix.diagonal_apply, Subtype.ext_iff]
    rw [hρ'_diag]
    have hsum : star x ⬝ᵥ (Matrix.diagonal (fun k : d' ↦ (ρ.eigvals k.1 : ℂ)) *ᵥ x) =
        ((∑ k : d', ρ.eigvals k.1 * ‖x k‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Matrix.mulVec_diagonal, Complex.ofReal_sum, Complex.ofReal_mul]
      apply Finset.sum_congr rfl; intro k _
      have hsq : star (x k) * x k = ((‖x k‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc star (x k) * ((ρ.eigvals k.1 : ℂ) * x k)
          = (ρ.eigvals k.1 : ℂ) * (star (x k) * x k) := by ring
        _ = (ρ.eigvals k.1 : ℂ) * ((‖x k‖ ^ 2 : ℝ) : ℂ) := by rw [hsq]
        _ = _ := by push_cast; ring
    rw [hsum]
    have hpos : (0 : ℝ) < ∑ k : d', ρ.eigvals k.1 * ‖x k‖ ^ 2 := by
      obtain ⟨k₀, hk₀⟩ := Function.ne_iff.mp hx
      apply Finset.sum_pos' (fun k _ ↦ mul_nonneg (ρ.eigvals_nonneg k.1) (sq_nonneg _))
      refine ⟨k₀, Finset.mem_univ k₀, mul_pos ?_ (sq_pos_of_pos (norm_pos_iff.mpr hk₀))⟩
      exact (Finset.mem_filter.mp k₀.2).2
    exact Complex.zero_lt_real.mpr hpos
  have hσ'_pd : σ'.mat.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨σ'.posSemidef.isHermitian, fun x hx ↦ ?_⟩
    have hnn := σ'.posSemidef.dotProduct_mulVec_nonneg x
    by_contra hnot
    have h0 : star x ⬝ᵥ (σ'.mat *ᵥ x) = 0 := by
      have hre0 : (star x ⬝ᵥ (σ'.mat *ᵥ x)).re = 0 := by
        have hle : ¬ (0 < (star x ⬝ᵥ (σ'.mat *ᵥ x)).re) := by
          intro hpos
          apply hnot
          exact (Complex.lt_def.mpr ⟨hpos, (Complex.le_def.mp hnn).2.symm⟩)
        linarith [(Complex.le_def.mp hnn).1]
      exact Complex.ext hre0 (Complex.le_def.mp hnn).2.symm
    have hVx_ne : V *ᵥ x ≠ 0 := by
      intro hVx0
      have : x = 0 := by
        calc x = (Vᴴ * V) *ᵥ x := by rw [hVHV, Matrix.one_mulVec]
          _ = Vᴴ *ᵥ (V *ᵥ x) := by rw [Matrix.mulVec_mulVec]
          _ = 0 := by rw [hVx0, Matrix.mulVec_zero]
      exact hx this
    have hσVx : star (V *ᵥ x) ⬝ᵥ (σ.mat *ᵥ (V *ᵥ x)) = 0 := by
      have hvec : star (V *ᵥ x) ⬝ᵥ (σ.mat *ᵥ (V *ᵥ x)) = star x ⬝ᵥ (σ'.mat *ᵥ x) := by
        simp only [σ', Matrix.mulVec_mulVec]
        rw [← Matrix.vecMul_mulVec]
        have hst : star (V *ᵥ x) = star x ᵥ* Vᴴ := by
          ext j; simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, mul_comm]
        rw [hst, Matrix.vecMul_mulVec]
      rw [hvec, h0]
    have hσ_zero : σ.mat *ᵥ (V *ᵥ x) = 0 :=
      σ.posSemidef.mulVec_eq_zero_of_dotProduct_eq_zero hσVx
    have hρ_zero : ρ.mat *ᵥ (V *ᵥ x) = 0 := suppSubset_ker_aux hsupp.1 hσ_zero
    have hρ'_zero : ρ'.mat *ᵥ x = 0 := by
      calc ρ'.mat *ᵥ x = Vᴴ *ᵥ (ρ.mat *ᵥ (V *ᵥ x)) := by simp [ρ', Matrix.mulVec_mulVec]
        _ = 0 := by rw [hρ_zero, Matrix.mulVec_zero]
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hρ'_pd).2 x hx
    rw [hρ'_zero, dotProduct_zero] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨a, b, μ, ha, hab, hprob, hsuppμ, hhs, hint, hD1, hD2, hqjs⟩ :=
    lemma_3_2_hockeyStick_measure hρ'_pd hσ'_pd
  have hhs_eq : ∀ s : ℝ, hockeyStick s ρ σ = hockeyStick s ρ' σ' := fun s ↦ by
    rw [hockeyStick_eq_posPartTrace, hockeyStick_eq_posPartTrace]
    apply posPartTrace_eq_of_isom (hockeyStick_isHermitian s ρ σ) (hockeyStick_isHermitian s ρ' σ') V hVHV
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hρ_comp, hσ_comp]
  have hiso_ent : ∀ (A B : DensityOp d) (A' B' : DensityOp d'),
      V * A'.mat * Vᴴ = A.mat → V * B'.mat * Vᴴ = B.mat →
      A'.mat.PosDef → B'.mat.PosDef →
      relEntropy A B = relEntropy A' B' ∧ vonNeumannEntropy A = vonNeumannEntropy A' := by
    intro A B A' B' hA hB hA'_pd hB'_pd
    have hS_eq : vonNeumannEntropy A = vonNeumannEntropy A' := by
      have hcomm : ∀ (f : ℝ → ℂ), f 0 = 0 →
          (A.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun i ↦ f (A.eigvals i)) *
            star (A.eigUnitary : Matrix d d ℂ) =
          V * ((A'.eigUnitary : Matrix d' d' ℂ) * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) *
            star (A'.eigUnitary : Matrix d' d' ℂ)) * Vᴴ := by
        intro f hf0
        set M_A := (A.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun i ↦ f (A.eigvals i)) *
          star (A.eigUnitary : Matrix d d ℂ)
        set M_A' := (A'.eigUnitary : Matrix d' d' ℂ) * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) *
          star (A'.eigUnitary : Matrix d' d' ℂ)
        set Q : Matrix d d' ℂ := star (A.eigUnitary : Matrix d d ℂ) * V * (A'.eigUnitary : Matrix d' d' ℂ)
        have hQ_intertwine : ∀ i k, (A.eigvals i : ℂ) * Q i k = Q i k * (A'.eigvals k : ℂ) := by
          intro i k
          have h1 : Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * Q =
              Q * Matrix.diagonal (Complex.ofReal ∘ A'.eigvals) := by
            have hspecA := A.posSemidef.isHermitian.spectral_theorem
            have hspecA' := A'.posSemidef.isHermitian.spectral_theorem
            have hAV : A.mat * V = V * A'.mat := by
              rw [← hA]; calc (V * A'.mat * Vᴴ) * V = V * A'.mat * (Vᴴ * V) := by simp [Matrix.mul_assoc]
                _ = V * A'.mat := by rw [hVHV, Matrix.mul_one]
            calc Matrix.diagonal (Complex.ofReal ∘ A.eigvals) * Q
                = star (A.eigUnitary : Matrix d d ℂ) * (A.mat * V) * (A'.eigUnitary : Matrix d' d' ℂ) := by
                    rw [hspecA]; simp [Q, Matrix.mul_assoc, Unitary.coe_star_mul_self]
              _ = star (A.eigUnitary : Matrix d d ℂ) * (V * A'.mat) * (A'.eigUnitary : Matrix d' d' ℂ) := by
                    rw [hAV]
              _ = Q * Matrix.diagonal (Complex.ofReal ∘ A'.eigvals) := by
                    rw [hspecA']; simp [Q, Matrix.mul_assoc, Unitary.coe_star_mul_self]
          have := congr_fun (congr_fun h1 i) k
          simpa [Matrix.mul_apply, Matrix.diagonal_apply] using this
        have hQ_zero : ∀ i k, A.eigvals i ≠ A'.eigvals k → Q i k = 0 := by
          intro i k hne
          have h := hQ_intertwine i k
          have hsub : ((A.eigvals i - A'.eigvals k : ℝ) : ℂ) * Q i k = 0 := by
            push_cast; linear_combination h
          rcases mul_eq_zero.mp hsub with h0 | h0
          · exact absurd (sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h0)) hne
          · exact h0
        have hQQ : Q * Qᴴ = star (A.eigUnitary : Matrix d d ℂ) * (V * Vᴴ) * (A.eigUnitary : Matrix d d ℂ) := by
          simp only [Q, Matrix.conjTranspose_mul, Matrix.mul_assoc]
          have h1 : (A'.eigUnitary : Matrix d' d' ℂ) * (A'.eigUnitary : Matrix d' d' ℂ)ᴴ = 1 :=
            Unitary.coe_mul_star_self A'.eigUnitary
          calc star (A.eigUnitary : Matrix d d ℂ) *
                (V * ((A'.eigUnitary : Matrix d' d' ℂ) * ((A'.eigUnitary : Matrix d' d' ℂ)ᴴ *
                (Vᴴ * (star (A.eigUnitary : Matrix d d ℂ))ᴴ))))
              = star (A.eigUnitary : Matrix d d ℂ) *
                (V * (((A'.eigUnitary : Matrix d' d' ℂ) * (A'.eigUnitary : Matrix d' d' ℂ)ᴴ) *
                (Vᴴ * (A.eigUnitary : Matrix d d ℂ)))) := by simp [Matrix.mul_assoc]
            _ = _ := by rw [h1, Matrix.one_mul]; simp [Matrix.mul_assoc]
        have hQQ_diag : Matrix.diagonal (fun i ↦ f (A.eigvals i)) * (Q * Qᴴ) =
            Matrix.diagonal (fun i ↦ f (A.eigvals i)) := by
          have hVV_A : (V * Vᴴ) * A.mat = A.mat := by
            rw [← hA]; calc (V * Vᴴ) * (V * A'.mat * Vᴴ) = V * (Vᴴ * V) * A'.mat * Vᴴ := by simp [Matrix.mul_assoc]
              _ = V * A'.mat * Vᴴ := by rw [hVHV, Matrix.mul_one]
          have hQQ_A : (Q * Qᴴ) * Matrix.diagonal (Complex.ofReal ∘ A.eigvals) =
              Matrix.diagonal (Complex.ofReal ∘ A.eigvals) := by
            rw [hQQ]
            have hspecA := A.posSemidef.isHermitian.spectral_theorem
            calc star (A.eigUnitary : Matrix d d ℂ) * (V * Vᴴ) * (A.eigUnitary : Matrix d d ℂ) *
                  Matrix.diagonal (Complex.ofReal ∘ A.eigvals)
                = star (A.eigUnitary : Matrix d d ℂ) * ((V * Vᴴ) * A.mat) * (A.eigUnitary : Matrix d d ℂ) := by
                    rw [hspecA]; simp [Matrix.mul_assoc, Unitary.coe_star_mul_self]
              _ = star (A.eigUnitary : Matrix d d ℂ) * A.mat * (A.eigUnitary : Matrix d d ℂ) := by rw [hVV_A]
              _ = Matrix.diagonal (Complex.ofReal ∘ A.eigvals) := by
                    rw [hspecA]; simp [Matrix.mul_assoc, Unitary.coe_star_mul_self]
          ext i j
          simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul,
            Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
          by_cases hi : A.eigvals i = 0
          · simp [hi, hf0]
          · have h := congr_fun (congr_fun hQQ_A j) i
            simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
              Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Function.comp_apply] at h
            have hji : (Q * Qᴴ) j i = if j = i then 1 else 0 :=
              mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hi) (by simpa [mul_ite] using h)
            have hij : (Q * Qᴴ) i j = if i = j then 1 else 0 := by
              have hherm : (Q * Qᴴ)ᴴ = Q * Qᴴ := by simp [Matrix.conjTranspose_mul]
              have hst := congr_fun (congr_fun hherm i) j
              simp only [Matrix.conjTranspose_apply] at hst
              rw [← hst, hji]; split_ifs with h1 h2 <;> simp_all
            rw [hij]; split_ifs <;> simp
        have hMQ : Matrix.diagonal (fun i ↦ f (A.eigvals i)) * Q =
            Q * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) := by
          ext i k
          simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
            Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          by_cases h : A.eigvals i = A'.eigvals k
          · rw [h, mul_comm]
          · rw [hQ_zero i k h, mul_zero, zero_mul]
        have hcore : Matrix.diagonal (fun i ↦ f (A.eigvals i)) =
            Q * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) * Qᴴ := by
          calc Matrix.diagonal (fun i ↦ f (A.eigvals i))
              = Matrix.diagonal (fun i ↦ f (A.eigvals i)) * (Q * Qᴴ) := hQQ_diag.symm
            _ = (Matrix.diagonal (fun i ↦ f (A.eigvals i)) * Q) * Qᴴ := by rw [Matrix.mul_assoc]
            _ = Q * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) * Qᴴ := by rw [hMQ]
        calc M_A = (A.eigUnitary : Matrix d d ℂ) *
                (Q * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) * Qᴴ) *
                star (A.eigUnitary : Matrix d d ℂ) := by rw [← hcore]
          _ = V * M_A' * Vᴴ := by
                simp only [M_A', Q, Matrix.conjTranspose_mul, Matrix.mul_assoc]
                have h1 : (A.eigUnitary : Matrix d d ℂ) * star (A.eigUnitary : Matrix d d ℂ) = 1 :=
                  Unitary.coe_mul_star_self A.eigUnitary
                calc (A.eigUnitary : Matrix d d ℂ) *
                      (star (A.eigUnitary : Matrix d d ℂ) * (V * ((A'.eigUnitary : Matrix d' d' ℂ) *
                      (Matrix.diagonal (fun k ↦ f (A'.eigvals k)) *
                      ((A'.eigUnitary : Matrix d' d' ℂ)ᴴ * (Vᴴ * ((star (A.eigUnitary : Matrix d d ℂ))ᴴ *
                      star (A.eigUnitary : Matrix d d ℂ))))))))
                    = ((A.eigUnitary : Matrix d d ℂ) * star (A.eigUnitary : Matrix d d ℂ)) *
                      (V * ((A'.eigUnitary : Matrix d' d' ℂ) * (Matrix.diagonal (fun k ↦ f (A'.eigvals k)) *
                      ((A'.eigUnitary : Matrix d' d' ℂ)ᴴ * (Vᴴ * ((A.eigUnitary : Matrix d d ℂ) *
                      star (A.eigUnitary : Matrix d d ℂ))))))) := by simp [Matrix.mul_assoc]
                  _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]; simp [Matrix.mul_assoc]
      let f : ℝ → ℂ := fun t ↦ if t = 0 then 0 else ((t * Real.logb 2 t : ℝ) : ℂ)
      have hf0 : f 0 = 0 := by simp [f]
      have htr := congr_arg Matrix.trace (hcomm f hf0)
      have htrL : ((A.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun i ↦ f (A.eigvals i)) *
          star (A.eigUnitary : Matrix d d ℂ)).trace = ∑ i : d, f (A.eigvals i) := by
        rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
      have htrR : (V * ((A'.eigUnitary : Matrix d' d' ℂ) * Matrix.diagonal (fun k ↦ f (A'.eigvals k)) *
          star (A'.eigUnitary : Matrix d' d' ℂ)) * Vᴴ).trace = ∑ k : d', f (A'.eigvals k) := by
        rw [Matrix.trace_mul_cycle, hVHV, Matrix.one_mul, Matrix.trace_mul_cycle,
          Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
      rw [htrL, htrR] at htr
      have hre := congr_arg Complex.re htr
      simp only [Complex.re_sum, f] at hre
      unfold vonNeumannEntropy
      rw [neg_inj]
      convert hre using 1 <;>
        (apply Finset.sum_congr rfl; intro i _; split_ifs with hi <;> simp [hi])
    have hD_eq : relEntropy A B = relEntropy A' B' := by
      have hsuppAB : suppSubset A B := by
        intro i j hi hj
        have hBi : B.mat *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j) = 0 := by
          have hspec := B.posSemidef.isHermitian.spectral_theorem
          rw [hspec]
          have hvec : star (B.eigUnitary : Matrix d d ℂ) *ᵥ
              (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j) = Pi.single j 1 := by
            ext k
            have h := congr_fun (congr_fun (Unitary.coe_star_mul_self B.eigUnitary) k) j
            simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
              Matrix.one_apply, Pi.single_apply, eq_comm] using h
          calc ((B.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (Complex.ofReal ∘ B.eigvals) *
                star (B.eigUnitary : Matrix d d ℂ)) *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j)
              = (B.eigUnitary : Matrix d d ℂ) *ᵥ (Matrix.diagonal (Complex.ofReal ∘ B.eigvals) *ᵥ
                Pi.single j 1) := by simp [Matrix.mulVec_mulVec, Matrix.mul_assoc, hvec]
            _ = 0 := by
                have h0 : Matrix.diagonal (Complex.ofReal ∘ B.eigvals) *ᵥ Pi.single j 1 = 0 := by
                  ext k; simp [Matrix.mulVec_diagonal, Pi.single_apply, hj]
                rw [h0, Matrix.mulVec_zero]
        have hVHB : Vᴴ *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j) = 0 := by
          by_contra hne
          have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hB'_pd).2 _ hne
          have hzero : B'.mat *ᵥ (Vᴴ *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j)) = 0 := by
            have hBV : Vᴴ * B.mat = B'.mat * Vᴴ := by
              rw [← hB]; simp [Matrix.mul_assoc, hVHV]
            calc B'.mat *ᵥ (Vᴴ *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j))
                = (B'.mat * Vᴴ) *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j) := by
                    rw [Matrix.mulVec_mulVec]
              _ = (Vᴴ * B.mat) *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j) := by rw [← hBV]
              _ = Vᴴ *ᵥ (B.mat *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j)) := by
                    rw [Matrix.mulVec_mulVec]
              _ = 0 := by rw [hBi, Matrix.mulVec_zero]
          rw [hzero, dotProduct_zero] at hpos
          exact lt_irrefl 0 hpos
        have hAi : A.mat *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j) = 0 := by
          rw [← hA]
          calc (V * A'.mat * Vᴴ) *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j)
              = (V * A'.mat) *ᵥ (Vᴴ *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j)) := by
                  simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
            _ = 0 := by rw [hVHB, Matrix.mulVec_zero]
        have hspecA := A.posSemidef.isHermitian.spectral_theorem
        have h0 := congr_fun (congr_arg (fun v ↦ star (A.eigUnitary : Matrix d d ℂ) *ᵥ v) hAi) i
        rw [hspecA] at h0
        simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero, Pi.zero_apply] at h0
        have h1 : (star (A.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) = 1 :=
          Unitary.coe_star_mul_self A.eigUnitary
        have h2 : (Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *ᵥ
            (star (A.eigUnitary : Matrix d d ℂ) *ᵥ (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j))) i = 0 := by
          simpa [Matrix.mul_assoc, h1] using h0
        simp only [Matrix.mulVec_diagonal, Function.comp_apply] at h2
        rcases mul_eq_zero.mp h2 with hλ | hw
        · exact absurd (Complex.ofReal_eq_zero.mp hλ) hi
        · have hst : (star (B.eigUnitary : Matrix d d ℂ) * (A.eigUnitary : Matrix d d ℂ)) j i =
              star ((star (A.eigUnitary : Matrix d d ℂ) *ᵥ
                (fun r ↦ (B.eigUnitary : Matrix d d ℂ) r j)) i) := by
            simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.star_apply, mul_comm]
          rw [hst, hw, star_zero]
      have hsuppA'B' : suppSubset A' B' := fun _ j _ hj ↦
        absurd hj (ne_of_gt (B'.eigvals_pos_of_posDef hB'_pd j))
      rw [relEntropy_eq_trace_log A B hsuppAB, relEntropy_eq_trace_log A' B' hsuppA'B', hS_eq]
      have hcommB :
          (B.eigUnitary : Matrix d d ℂ) *
            Matrix.diagonal (fun j ↦ if B.eigvals j = 0 then (0 : ℂ) else (Real.log (B.eigvals j) : ℂ)) *
            star (B.eigUnitary : Matrix d d ℂ) =
          V * ((B'.eigUnitary : Matrix d' d' ℂ) *
            Matrix.diagonal (fun k ↦ if B'.eigvals k = 0 then (0 : ℂ) else (Real.log (B'.eigvals k) : ℂ)) *
            star (B'.eigUnitary : Matrix d' d' ℂ)) * Vᴴ := by
        let f : ℝ → ℂ := fun t ↦ if t = 0 then 0 else (Real.log t : ℂ)
        set Q : Matrix d d' ℂ := star (B.eigUnitary : Matrix d d ℂ) * V * (B'.eigUnitary : Matrix d' d' ℂ)
        have hQ_intertwine : ∀ i k, (B.eigvals i : ℂ) * Q i k = Q i k * (B'.eigvals k : ℂ) := by
          intro i k
          have h1 : Matrix.diagonal (Complex.ofReal ∘ B.eigvals) * Q =
              Q * Matrix.diagonal (Complex.ofReal ∘ B'.eigvals) := by
            have hspecB := B.posSemidef.isHermitian.spectral_theorem
            have hspecB' := B'.posSemidef.isHermitian.spectral_theorem
            have hBV : B.mat * V = V * B'.mat := by
              rw [← hB]; calc (V * B'.mat * Vᴴ) * V = V * B'.mat * (Vᴴ * V) := by simp [Matrix.mul_assoc]
                _ = V * B'.mat := by rw [hVHV, Matrix.mul_one]
            calc Matrix.diagonal (Complex.ofReal ∘ B.eigvals) * Q
                = star (B.eigUnitary : Matrix d d ℂ) * (B.mat * V) * (B'.eigUnitary : Matrix d' d' ℂ) := by
                    rw [hspecB]; simp [Q, Matrix.mul_assoc, Unitary.coe_star_mul_self]
              _ = star (B.eigUnitary : Matrix d d ℂ) * (V * B'.mat) * (B'.eigUnitary : Matrix d' d' ℂ) := by
                    rw [hBV]
              _ = Q * Matrix.diagonal (Complex.ofReal ∘ B'.eigvals) := by
                    rw [hspecB']; simp [Q, Matrix.mul_assoc, Unitary.coe_star_mul_self]
          have := congr_fun (congr_fun h1 i) k
          simpa [Matrix.mul_apply, Matrix.diagonal_apply] using this
        have hQ_zero : ∀ i k, B.eigvals i ≠ B'.eigvals k → Q i k = 0 := by
          intro i k hne
          have hsub : ((B.eigvals i - B'.eigvals k : ℝ) : ℂ) * Q i k = 0 := by
            push_cast; linear_combination hQ_intertwine i k
          rcases mul_eq_zero.mp hsub with h0 | h0
          · exact absurd (sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h0)) hne
          · exact h0
        have hQQ : Q * Qᴴ = star (B.eigUnitary : Matrix d d ℂ) * (V * Vᴴ) * (B.eigUnitary : Matrix d d ℂ) := by
          simp only [Q, Matrix.conjTranspose_mul, Matrix.mul_assoc]
          have h1 : (B'.eigUnitary : Matrix d' d' ℂ) * (B'.eigUnitary : Matrix d' d' ℂ)ᴴ = 1 :=
            Unitary.coe_mul_star_self B'.eigUnitary
          calc star (B.eigUnitary : Matrix d d ℂ) *
                (V * ((B'.eigUnitary : Matrix d' d' ℂ) * ((B'.eigUnitary : Matrix d' d' ℂ)ᴴ *
                (Vᴴ * (star (B.eigUnitary : Matrix d d ℂ))ᴴ))))
              = star (B.eigUnitary : Matrix d d ℂ) *
                (V * (((B'.eigUnitary : Matrix d' d' ℂ) * (B'.eigUnitary : Matrix d' d' ℂ)ᴴ) *
                (Vᴴ * (B.eigUnitary : Matrix d d ℂ)))) := by simp [Matrix.mul_assoc]
            _ = _ := by rw [h1, Matrix.one_mul]; simp [Matrix.mul_assoc]
        have hQQ_diag : Matrix.diagonal (fun i ↦ f (B.eigvals i)) * (Q * Qᴴ) =
            Matrix.diagonal (fun i ↦ f (B.eigvals i)) := by
          have hVV_B : (V * Vᴴ) * B.mat = B.mat := by
            rw [← hB]; calc (V * Vᴴ) * (V * B'.mat * Vᴴ) = V * (Vᴴ * V) * B'.mat * Vᴴ := by simp [Matrix.mul_assoc]
              _ = V * B'.mat * Vᴴ := by rw [hVHV, Matrix.mul_one]
          have hQQ_B : (Q * Qᴴ) * Matrix.diagonal (Complex.ofReal ∘ B.eigvals) =
              Matrix.diagonal (Complex.ofReal ∘ B.eigvals) := by
            rw [hQQ]
            have hspecB := B.posSemidef.isHermitian.spectral_theorem
            calc star (B.eigUnitary : Matrix d d ℂ) * (V * Vᴴ) * (B.eigUnitary : Matrix d d ℂ) *
                  Matrix.diagonal (Complex.ofReal ∘ B.eigvals)
                = star (B.eigUnitary : Matrix d d ℂ) * ((V * Vᴴ) * B.mat) * (B.eigUnitary : Matrix d d ℂ) := by
                    rw [hspecB]; simp [Matrix.mul_assoc, Unitary.coe_star_mul_self]
              _ = star (B.eigUnitary : Matrix d d ℂ) * B.mat * (B.eigUnitary : Matrix d d ℂ) := by rw [hVV_B]
              _ = Matrix.diagonal (Complex.ofReal ∘ B.eigvals) := by
                    rw [hspecB]; simp [Matrix.mul_assoc, Unitary.coe_star_mul_self]
          ext i j
          simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul,
            Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
          by_cases hi : B.eigvals i = 0
          · simp [f, hi]
          · have h := congr_fun (congr_fun hQQ_B j) i
            simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
              Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Function.comp_apply] at h
            have hji : (Q * Qᴴ) j i = if j = i then 1 else 0 :=
              mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hi) (by simpa [mul_ite] using h)
            have hij : (Q * Qᴴ) i j = if i = j then 1 else 0 := by
              have hherm : (Q * Qᴴ)ᴴ = Q * Qᴴ := by simp [Matrix.conjTranspose_mul]
              have hst := congr_fun (congr_fun hherm i) j
              simp only [Matrix.conjTranspose_apply] at hst
              rw [← hst, hji]; split_ifs with h1 h2 <;> simp_all
            rw [hij]; split_ifs <;> simp
        have hMQ : Matrix.diagonal (fun i ↦ f (B.eigvals i)) * Q =
            Q * Matrix.diagonal (fun k ↦ f (B'.eigvals k)) := by
          ext i k
          simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
            Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          by_cases h : B.eigvals i = B'.eigvals k
          · rw [h, mul_comm]
          · rw [hQ_zero i k h, mul_zero, zero_mul]
        have hcore : Matrix.diagonal (fun i ↦ f (B.eigvals i)) =
            Q * Matrix.diagonal (fun k ↦ f (B'.eigvals k)) * Qᴴ := by
          calc Matrix.diagonal (fun i ↦ f (B.eigvals i))
              = Matrix.diagonal (fun i ↦ f (B.eigvals i)) * (Q * Qᴴ) := hQQ_diag.symm
            _ = (Matrix.diagonal (fun i ↦ f (B.eigvals i)) * Q) * Qᴴ := by rw [Matrix.mul_assoc]
            _ = Q * Matrix.diagonal (fun k ↦ f (B'.eigvals k)) * Qᴴ := by rw [hMQ]
        change (B.eigUnitary : Matrix d d ℂ) * Matrix.diagonal (fun j ↦ f (B.eigvals j)) *
            star (B.eigUnitary : Matrix d d ℂ) =
          V * ((B'.eigUnitary : Matrix d' d' ℂ) * Matrix.diagonal (fun k ↦ f (B'.eigvals k)) *
            star (B'.eigUnitary : Matrix d' d' ℂ)) * Vᴴ
        rw [hcore]
        simp only [Q, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        have h1 : (B.eigUnitary : Matrix d d ℂ) * star (B.eigUnitary : Matrix d d ℂ) = 1 :=
          Unitary.coe_mul_star_self B.eigUnitary
        calc (B.eigUnitary : Matrix d d ℂ) *
              (star (B.eigUnitary : Matrix d d ℂ) * (V * ((B'.eigUnitary : Matrix d' d' ℂ) *
              (Matrix.diagonal (fun k ↦ f (B'.eigvals k)) *
              ((B'.eigUnitary : Matrix d' d' ℂ)ᴴ * (Vᴴ * ((star (B.eigUnitary : Matrix d d ℂ))ᴴ *
              star (B.eigUnitary : Matrix d d ℂ))))))))
            = ((B.eigUnitary : Matrix d d ℂ) * star (B.eigUnitary : Matrix d d ℂ)) *
              (V * ((B'.eigUnitary : Matrix d' d' ℂ) * (Matrix.diagonal (fun k ↦ f (B'.eigvals k)) *
              ((B'.eigUnitary : Matrix d' d' ℂ)ᴴ * (Vᴴ * ((B.eigUnitary : Matrix d d ℂ) *
              star (B.eigUnitary : Matrix d d ℂ))))))) := by simp [Matrix.mul_assoc]
          _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]; simp [Matrix.mul_assoc]
      have htr_eq : (A.mat * ((B.eigUnitary : Matrix d d ℂ) *
            Matrix.diagonal (fun j ↦ if B.eigvals j = 0 then (0 : ℂ) else (Real.log (B.eigvals j) : ℂ)) *
            star (B.eigUnitary : Matrix d d ℂ))).trace =
          (A'.mat * ((B'.eigUnitary : Matrix d' d' ℂ) *
            Matrix.diagonal (fun k ↦ if B'.eigvals k = 0 then (0 : ℂ) else (Real.log (B'.eigvals k) : ℂ)) *
            star (B'.eigUnitary : Matrix d' d' ℂ))).trace := by
        rw [← hA, hcommB]
        set L' := (B'.eigUnitary : Matrix d' d' ℂ) *
          Matrix.diagonal (fun k ↦ if B'.eigvals k = 0 then (0 : ℂ) else (Real.log (B'.eigvals k) : ℂ)) *
          star (B'.eigUnitary : Matrix d' d' ℂ)
        calc (V * A'.mat * Vᴴ * (V * L' * Vᴴ)).trace
            = (V * (A'.mat * (Vᴴ * V) * L') * Vᴴ).trace := by simp [Matrix.mul_assoc]
          _ = (V * (A'.mat * L') * Vᴴ).trace := by rw [hVHV, Matrix.mul_one]
          _ = (Vᴴ * V * (A'.mat * L')).trace := by rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
          _ = (A'.mat * L').trace := by rw [hVHV, Matrix.one_mul]
      rw [htr_eq]
    exact ⟨hD_eq, hS_eq⟩
  have h1 := hiso_ent ρ σ ρ' σ' hρ_comp hσ_comp hρ'_pd hσ'_pd
  have h2 := hiso_ent σ ρ σ' ρ' hσ_comp hρ_comp hσ'_pd hρ'_pd
  have hmid_comp : V * (DensityOp.midpoint ρ' σ').mat * Vᴴ = (DensityOp.midpoint ρ σ).mat := by
    simp only [DensityOp.midpoint, DensityOp.mix, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, hρ_comp, hσ_comp]
  have hmid'_pd : (DensityOp.midpoint ρ' σ').mat.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨(DensityOp.midpoint ρ' σ').posSemidef.isHermitian, fun x hx ↦ ?_⟩
    have h1x := (Matrix.posDef_iff_dotProduct_mulVec.mp hρ'_pd).2 x hx
    have h2x := (Matrix.posDef_iff_dotProduct_mulVec.mp hσ'_pd).2 x hx
    simp only [DensityOp.midpoint, DensityOp.mix, Matrix.add_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hpos1 : (0 : ℂ) < ((1 - 1 / 2 : ℝ) : ℂ) * (star x ⬝ᵥ (ρ'.mat *ᵥ x)) := by
      rw [Complex.lt_def] at h1x ⊢
      refine ⟨by simp [Complex.mul_re]; linarith [h1x.1], by simp [Complex.mul_im, h1x.2.symm]⟩
    have hpos2 : (0 : ℂ) < ((1 / 2 : ℝ) : ℂ) * (star x ⬝ᵥ (σ'.mat *ᵥ x)) := by
      rw [Complex.lt_def] at h2x ⊢
      refine ⟨by simp [Complex.mul_re]; linarith [h2x.1], by simp [Complex.mul_im, h2x.2.symm]⟩
    exact add_pos hpos1 hpos2
  have h3 := hiso_ent (DensityOp.midpoint ρ σ) ρ (DensityOp.midpoint ρ' σ') ρ'
    hmid_comp hρ_comp hmid'_pd hρ'_pd
  have hqjs_eq : qjs ρ σ = qjs ρ' σ' := by
    unfold qjs
    rw [h3.2, h1.2, h2.2]
  refine ⟨a, b, μ, ha, hab, hprob, hsuppμ, fun s ↦ by rw [hhs_eq s]; exact hhs s, hint,
    by rw [h1.1]; exact hD1, by rw [h2.1]; exact hD2, by rw [hqjs_eq]; exact hqjs⟩

end EqualSupportLemma32

/-! ### Part 2: Proposition 3.3 Classical Equality (Gap 5.1) -/

section Prop33Equality

/-- Symmetric classical binary state `diag((1+x)/2, (1-x)/2)` for `x ∈ [0, 1]`. -/
noncomputable def symClassicalPair0 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : DensityOp Bool where
  mat := Matrix.diagonal fun b : Bool ↦ if b = false then (((1 + x) / 2 : ℝ) : ℂ) else (((1 - x) / 2 : ℝ) : ℂ)
  posSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro b; cases b <;> simp only [↓reduceIte, Bool.true_eq_false] <;>
      exact Complex.zero_le_real.mpr (by linarith)
  trace_one := by
    rw [Matrix.trace_diagonal, Fintype.sum_bool]
    simp; push_cast; ring

/-- Symmetric classical binary state `diag((1-x)/2, (1+x)/2)` for `x ∈ [0, 1]`. -/
noncomputable def symClassicalPair1 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : DensityOp Bool where
  mat := Matrix.diagonal fun b : Bool ↦ if b = false then (((1 - x) / 2 : ℝ) : ℂ) else (((1 + x) / 2 : ℝ) : ℂ)
  posSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro b; cases b <;> simp only [↓reduceIte, Bool.true_eq_false] <;>
      exact Complex.zero_le_real.mpr (by linarith)
  trace_one := by
    rw [Matrix.trace_diagonal, Fintype.sum_bool]
    simp; push_cast; ring

/-- **Proposition 3.3 (Classical Equality)**: Every symmetric classical binary pair
`ρ = diag((1+x)/2, (1-x)/2)`, `σ = diag((1-x)/2, (1+x)/2)` attains equality in Proposition 3.3
for all `x ∈ [0, 1]` (including `x = 1`, where both sides equal `⊤ : ℝ≥0∞`). -/
theorem prop_3_3_qjjs_classical_equality {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    phiExt (qjs (symClassicalPair0 x hx0 hx1) (symClassicalPair1 x hx0 hx1)) =
      (1 / 4 : ℝ≥0∞) *
        (relEntropy (symClassicalPair0 x hx0 hx1) (symClassicalPair1 x hx0 hx1) +
         relEntropy (symClassicalPair1 x hx0 hx1) (symClassicalPair0 x hx0 hx1)) := by
  set ρ := symClassicalPair0 x hx0 hx1
  set σ := symClassicalPair1 x hx0 hx1
  set p := (1 - x) / 2
  have hp0 : 0 ≤ p := by linarith
  have hp1 : p ≤ 1 / 2 := by linarith
  have hp1' : p ≤ 1 := by linarith
  have hρ_bsc : ρ.mat = ((bscChannel p hp0 hp1').out false).mat := by
    ext i j; cases i <;> cases j <;> simp [ρ, symClassicalPair0, bscChannel, p] <;>
      (push_cast; ring)
  have hσ_bsc : σ.mat = ((bscChannel p hp0 hp1').out true).mat := by
    ext i j; cases i <;> cases j <;> simp [σ, symClassicalPair1, bscChannel, p] <;>
      (push_cast; ring)
  have hqjs_val : qjs ρ σ = 1 - h2 p := by
    have hcond := condEntropy_bscChannel p hp0 hp1'
    have hqjs_bsc : qjs ((bscChannel p hp0 hp1').out false) ((bscChannel p hp0 hp1').out true) =
        1 - (bscChannel p hp0 hp1').condEntropy := by
      unfold CQChannel.condEntropy; ring
    have hSρ : vonNeumannEntropy ρ = vonNeumannEntropy ((bscChannel p hp0 hp1').out false) := by
      cases ρ; cases ((bscChannel p hp0 hp1').out false); simp_all
    have hSσ : vonNeumannEntropy σ = vonNeumannEntropy ((bscChannel p hp0 hp1').out true) := by
      cases σ; cases ((bscChannel p hp0 hp1').out true); simp_all
    have hSmid : vonNeumannEntropy (DensityOp.midpoint ρ σ) =
        vonNeumannEntropy (DensityOp.midpoint ((bscChannel p hp0 hp1').out false)
          ((bscChannel p hp0 hp1').out true)) := by
      have hmat : (DensityOp.midpoint ρ σ).mat =
          (DensityOp.midpoint ((bscChannel p hp0 hp1').out false)
            ((bscChannel p hp0 hp1').out true)).mat := by
        simp [DensityOp.midpoint, DensityOp.mix, hρ_bsc, hσ_bsc]
      cases DensityOp.midpoint ρ σ
      cases DensityOp.midpoint ((bscChannel p hp0 hp1').out false) ((bscChannel p hp0 hp1').out true)
      simp_all
    unfold qjs at hqjs_bsc ⊢
    rw [hSmid, hSρ, hSσ, hqjs_bsc, hcond]
  by_cases hx_eq1 : x = 1
  · have hp_zero : p = 0 := by simp [p, hx_eq1]
    have hqjs1 : qjs ρ σ = 1 := by rw [hqjs_val, hp_zero, h2_zero]; ring
    have hnsupp : ¬ suppSubset ρ σ := by
      intro hsupp
      have hv : σ.mat *ᵥ (fun b : Bool ↦ if b = false then (1 : ℂ) else 0) = 0 := by
        ext b; cases b <;> simp [σ, symClassicalPair1, hx_eq1, Matrix.mulVec, dotProduct]
      have hρv := suppSubset_ker_aux hsupp hv
      have h0 := congr_fun hρv false
      simp [ρ, symClassicalPair0, hx_eq1, Matrix.mulVec, dotProduct] at h0
    have hDtop : relEntropy ρ σ = ⊤ := by unfold relEntropy; rw [if_neg hnsupp]
    rw [hqjs1, hDtop]
    simp [phiExt]
  · have hx_lt1 : x < 1 := lt_of_le_of_ne hx1 hx_eq1
    have hp_pos : 0 < p := by linarith
    have h1mp_pos : 0 < 1 - p := by linarith
    have hq_lt1 : qjs ρ σ < 1 := by
      rw [hqjs_val]
      have hh2_pos : 0 < h2 p := by
        unfold h2
        have h1 : 0 < -p * Real.logb 2 p := by
          have hl : Real.logb 2 p < 0 := Real.logb_neg (by norm_num) hp_pos (by linarith)
          nlinarith
        have h2' : 0 < -(1 - p) * Real.logb 2 (1 - p) := by
          have hl : Real.logb 2 (1 - p) < 0 := Real.logb_neg (by norm_num) h1mp_pos (by linarith)
          nlinarith
        linarith
      linarith
    have hrel_diag : ∀ (a b : Bool → ℝ) (A B : DensityOp Bool),
        (∀ i, 0 < a i) → (∀ i, 0 < b i) →
        A.mat = Matrix.diagonal (Complex.ofReal ∘ a) →
        B.mat = Matrix.diagonal (Complex.ofReal ∘ b) →
        relEntropy A B = ENNReal.ofReal ((∑ i : Bool, a i * (Real.log (a i) - Real.log (b i))) / Real.log 2) := by
      intro a b A B ha hb hA hB
      have hB_pd : B.mat.PosDef := by
        rw [hB, Matrix.posDef_diagonal_iff]
        intro i; exact Complex.zero_lt_real.mpr (hb i)
      have hsupp : suppSubset A B := fun _ j _ hj ↦
        absurd hj (ne_of_gt (B.eigvals_pos_of_posDef hB_pd j))
      rw [relEntropy_eq_trace_log A B hsupp]
      have hSA : vonNeumannEntropy A = -∑ i : Bool, a i * Real.logb 2 (a i) := by
        have hdiag_S := vonNeumannEntropy_diagonal a (fun i ↦ le_of_lt (ha i)) (by
          have htr := A.trace_one
          rw [hA, Matrix.trace_diagonal] at htr
          have hre := congr_arg Complex.re htr
          simpa using hre)
        have hAeq : A = ⟨Matrix.diagonal (Complex.ofReal ∘ a), by rw [← hA]; exact A.posSemidef,
            by rw [← hA]; exact A.trace_one⟩ := by
          cases A; simp_all
        rw [hAeq]; exact hdiag_S
      have hLB : (B.eigUnitary : Matrix Bool Bool ℂ) *
            Matrix.diagonal (fun j ↦ if B.eigvals j = 0 then (0 : ℂ) else (Real.log (B.eigvals j) : ℂ)) *
            star (B.eigUnitary : Matrix Bool Bool ℂ) =
          Matrix.diagonal (fun i : Bool ↦ (Real.log (b i) : ℂ)) := by
        have hspecB := B.posSemidef.isHermitian.spectral_theorem
        set UB := (B.eigUnitary : Matrix Bool Bool ℂ)
        have hcomm : UB * Matrix.diagonal (Complex.ofReal ∘ B.eigvals) =
            Matrix.diagonal (Complex.ofReal ∘ b) * UB := by
          calc UB * Matrix.diagonal (Complex.ofReal ∘ B.eigvals)
              = (UB * Matrix.diagonal (Complex.ofReal ∘ B.eigvals) * star UB) * UB := by
                  simp [Matrix.mul_assoc, Unitary.coe_star_mul_self]
            _ = B.mat * UB := by rw [← hspecB]
            _ = Matrix.diagonal (Complex.ofReal ∘ b) * UB := by rw [hB]
        have hcomm_log : UB * Matrix.diagonal (fun j ↦ if B.eigvals j = 0 then (0 : ℂ) else (Real.log (B.eigvals j) : ℂ)) =
            Matrix.diagonal (fun i : Bool ↦ (Real.log (b i) : ℂ)) * UB := by
          ext i j
          have hij := congr_fun (congr_fun hcomm i) j
          simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
            Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Function.comp_apply] at hij ⊢
          by_cases hU0 : UB i j = 0
          · simp [hU0]
          · have heq : B.eigvals j = b i := by
              have hsub : ((B.eigvals j - b i : ℝ) : ℂ) * UB i j = 0 := by
                push_cast; linear_combination hij
              rcases mul_eq_zero.mp hsub with h0 | h0
              · exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h0)
              · exact absurd h0 hU0
            rw [heq, if_neg (ne_of_gt (hb i)), mul_comm]
        rw [hcomm_log, Matrix.mul_assoc, Unitary.coe_mul_star_self, Matrix.mul_one]
      rw [hLB, hA, hSA]
      congr 1
      have htr : (Matrix.diagonal (Complex.ofReal ∘ a) *
          Matrix.diagonal (fun i : Bool ↦ (Real.log (b i) : ℂ))).trace.re =
          ∑ i : Bool, a i * Real.log (b i) := by
        rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
        simp only [Complex.re_sum, Function.comp_apply]
        apply Finset.sum_congr rfl; intro i _
        rw [← Complex.ofReal_mul, Complex.ofReal_re]
      rw [htr]
      simp only [Real.logb, Fintype.sum_bool]
      ring
    have hD1 : relEntropy ρ σ = ENNReal.ofReal (x * Real.logb 2 ((1 + x) / (1 - x))) := by
      have h := hrel_diag
        (fun b ↦ if b = false then (1 + x) / 2 else (1 - x) / 2)
        (fun b ↦ if b = false then (1 - x) / 2 else (1 + x) / 2) ρ σ
        (fun b ↦ by cases b <;> simp <;> linarith)
        (fun b ↦ by cases b <;> simp <;> linarith)
        (by ext i j; cases i <;> cases j <;> simp [ρ, symClassicalPair0])
        (by ext i j; cases i <;> cases j <;> simp [σ, symClassicalPair1])
      rw [h]; congr 1
      rw [Fintype.sum_bool]
      simp only [↓reduceIte, Bool.true_eq_false]
      have h1px : 0 < 1 + x := by linarith
      have h1mx : 0 < 1 - x := by linarith
      rw [Real.log_div (ne_of_gt h1px) (by norm_num),
          Real.log_div (ne_of_gt h1mx) (by norm_num),
          Real.logb, Real.log_div (ne_of_gt h1px) (ne_of_gt h1mx)]
      ring
    have hD2 : relEntropy σ ρ = ENNReal.ofReal (x * Real.logb 2 ((1 + x) / (1 - x))) := by
      have h := hrel_diag
        (fun b ↦ if b = false then (1 - x) / 2 else (1 + x) / 2)
        (fun b ↦ if b = false then (1 + x) / 2 else (1 - x) / 2) σ ρ
        (fun b ↦ by cases b <;> simp <;> linarith)
        (fun b ↦ by cases b <;> simp <;> linarith)
        (by ext i j; cases i <;> cases j <;> simp [σ, symClassicalPair1])
        (by ext i j; cases i <;> cases j <;> simp [ρ, symClassicalPair0])
      rw [h]; congr 1
      rw [Fintype.sum_bool]
      simp only [↓reduceIte, Bool.true_eq_false]
      have h1px : 0 < 1 + x := by linarith
      have h1mx : 0 < 1 - x := by linarith
      rw [Real.log_div (ne_of_gt h1px) (by norm_num),
          Real.log_div (ne_of_gt h1mx) (by norm_num),
          Real.logb, Real.log_div (ne_of_gt h1px) (ne_of_gt h1mx)]
      ring
    have hnn : 0 ≤ x * Real.logb 2 ((1 + x) / (1 - x)) := by
      apply mul_nonneg hx0
      exact Real.logb_nonneg (by norm_num) (by rw [one_le_div (by linarith)]; linarith)
    rw [phiExt, if_pos hq_lt1, hD1, hD2, ← ENNReal.ofReal_add hnn hnn]
    have hquarter : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) := by norm_num
    rw [hquarter, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    have hphi_val : phi (qjs ρ σ) = phiParam x := by
      rw [hqjs_val]
      unfold phi
      have hinv : h2Inv (1 - (1 - h2 p)) = p := by
        rw [sub_sub_cancel]
        exact h2Inv_h2 hp0 hp1
      rw [hinv]
      have h1 : 1 - 2 * p = x := by simp [p]; ring
      rw [h1]
    rw [hphi_val]
    unfold phiParam
    ring

end Prop33Equality

/-! ### Part 3: Relative-Entropy Definition of `C(p)` in Theorem 1.3 (Gap 3) -/

section RelEntropyTheorem13

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- For every bipartite state `Ψ ∈ D(ℂ² ⊗ H_B)` and every `p ∈ [0, 1]`,
`supp((Z_p ⊗ id)(Ψ)) ⊆ supp((Z_{1/2} ⊗ id)(Ψ))`. -/
lemma suppSubset_dephaseState_half (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) :
    suppSubset (dephaseState p hp0 hp1 Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) := by
  set A := dephaseState p hp0 hp1 Ψ
  set M := dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ
  set Z := pauliZTensorI d
  have hM_eq : M.mat = (1 / 2 : ℂ) • A.mat + (1 / 2 : ℂ) • (DensityOp.conjUnitary Z A).mat := by
    ext ⟨b₁, i⟩ ⟨b₂, j⟩
    simp only [M, A, Z, dephaseState, DensityOp.mix, DensityOp.conjUnitary, pauliZTensorI,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.star_apply, smul_eq_mul, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring
  intro i j hi hj
  set v : Bool × d → ℂ := fun r ↦ (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) r j
  have hMv : M.mat *ᵥ v = 0 := by
    have hspec := M.posSemidef.isHermitian.spectral_theorem
    rw [hspec]
    have hvec : star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *ᵥ v = Pi.single j 1 := by
      ext k
      have h := congr_fun (congr_fun (Unitary.coe_star_mul_self M.eigUnitary) k) j
      simpa [v, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
        Matrix.one_apply, Pi.single_apply, eq_comm] using h
    calc ((M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
          Matrix.diagonal (Complex.ofReal ∘ M.eigvals) *
          star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)) *ᵥ v
        = (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *ᵥ
          (Matrix.diagonal (Complex.ofReal ∘ M.eigvals) *ᵥ Pi.single j 1) := by
            simp [Matrix.mulVec_mulVec, Matrix.mul_assoc, hvec]
      _ = 0 := by
            have h0 : Matrix.diagonal (Complex.ofReal ∘ M.eigvals) *ᵥ Pi.single j 1 = 0 := by
              ext k; simp [Matrix.mulVec_diagonal, Pi.single_apply, hj]
            rw [h0, Matrix.mulVec_zero]
  have hdot : star v ⬝ᵥ (M.mat *ᵥ v) = 0 := by rw [hMv, dotProduct_zero]
  rw [hM_eq, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hdot
  have hnn1 := A.posSemidef.dotProduct_mulVec_nonneg v
  have hnn2 := (DensityOp.conjUnitary Z A).posSemidef.dotProduct_mulVec_nonneg v
  have hre := congr_arg Complex.re hdot
  simp only [Complex.add_re, Complex.mul_re, Complex.zero_re] at hre
  have h1re : (star v ⬝ᵥ (A.mat *ᵥ v)).re = 0 := by
    have h1 := (Complex.le_def.mp hnn1).1
    have h2 := (Complex.le_def.mp hnn2).1
    norm_num at hre
    linarith
  have hAv0 : star v ⬝ᵥ (A.mat *ᵥ v) = 0 :=
    Complex.ext h1re (Complex.le_def.mp hnn1).2.symm
  have hAv : A.mat *ᵥ v = 0 := A.posSemidef.mulVec_eq_zero_of_dotProduct_eq_zero hAv0
  have hspecA := A.posSemidef.isHermitian.spectral_theorem
  have h0 := congr_fun (congr_arg (fun w ↦ star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *ᵥ w) hAv) i
  rw [hspecA] at h0
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero, Pi.zero_apply] at h0
  have h2 : (Matrix.diagonal (Complex.ofReal ∘ A.eigvals) *ᵥ
      (star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *ᵥ v)) i = 0 := by
    simpa [Matrix.mul_assoc, Unitary.coe_star_mul_self] using h0
  simp only [Matrix.mulVec_diagonal, Function.comp_apply] at h2
  rcases mul_eq_zero.mp h2 with hλ | hw
  · exact absurd (Complex.ofReal_eq_zero.mp hλ) hi
  · have hst : (star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
        (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)) j i =
        star ((star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *ᵥ v) i) := by
      simp [v, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.star_apply, mul_comm]
    rw [hst, hw, star_zero]

/-- **Umegaki Relative-Entropy Identity for Dephasing Coherence**:
`D((Z_p ⊗ id)(Ψ) ‖ (Z_{1/2} ⊗ id)(Ψ)) = S((Z_{1/2} ⊗ id)(Ψ)) - S((Z_p ⊗ id)(Ψ))`. -/
theorem relEntropy_dephaseState_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) :
    relEntropy (dephaseState p hp0 hp1 Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) =
      ENNReal.ofReal
        (vonNeumannEntropy (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) -
         vonNeumannEntropy (dephaseState p hp0 hp1 Ψ)) := by
  set A := dephaseState p hp0 hp1 Ψ
  set M := dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ
  set Z : Matrix (Bool × d) (Bool × d) ℂ := (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)
  have hZZ : Z * Z = 1 := by
    ext ⟨b₁, i⟩ ⟨b₂, j⟩
    simp only [Z, pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    split_ifs with h
    · cases b₁ <;> norm_num
    · rfl
  have hZMZ : Z * M.mat * Z = M.mat := by
    ext ⟨b₁, i⟩ ⟨b₂, j⟩
    simp only [M, Z, dephaseState, DensityOp.mix, DensityOp.conjUnitary, pauliZTensorI,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.star_apply, smul_eq_mul, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring
  have hZM_comm : Z * M.mat = M.mat * Z := by
    calc Z * M.mat = Z * M.mat * (Z * Z) := by rw [hZZ, Matrix.mul_one]
      _ = (Z * M.mat * Z) * Z := by simp [Matrix.mul_assoc]
      _ = M.mat * Z := by rw [hZMZ]
  have hM_avg : M.mat = (1 / 2 : ℂ) • A.mat + (1 / 2 : ℂ) • (Z * A.mat * Z) := by
    ext ⟨b₁, i⟩ ⟨b₂, j⟩
    simp only [M, A, Z, dephaseState, DensityOp.mix, DensityOp.conjUnitary, pauliZTensorI,
      Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.star_apply, smul_eq_mul, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    cases b₁ <;> cases b₂ <;> simp <;> push_cast <;> ring
  set L_M : Matrix (Bool × d) (Bool × d) ℂ :=
    (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
    Matrix.diagonal (fun j ↦ if M.eigvals j = 0 then (0 : ℂ) else (Real.log (M.eigvals j) : ℂ)) *
    star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)
  have hZL_comm : Z * L_M * Z = L_M := by
    set UM := (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)
    set Z' := star UM * Z * UM
    have hZ'_comm : Z' * Matrix.diagonal (Complex.ofReal ∘ M.eigvals) =
        Matrix.diagonal (Complex.ofReal ∘ M.eigvals) * Z' := by
      have hspec := M.posSemidef.isHermitian.spectral_theorem
      calc Z' * Matrix.diagonal (Complex.ofReal ∘ M.eigvals)
          = star UM * (Z * M.mat) * UM := by
              rw [hspec]; simp [Z', UM, Matrix.mul_assoc, Unitary.coe_star_mul_self]
        _ = star UM * (M.mat * Z) * UM := by rw [hZM_comm]
        _ = Matrix.diagonal (Complex.ofReal ∘ M.eigvals) * Z' := by
              rw [hspec]; simp [Z', UM, Matrix.mul_assoc, Unitary.coe_star_mul_self]
    let f : ℝ → ℂ := fun t ↦ if t = 0 then 0 else (Real.log t : ℂ)
    have hZ'_f : Z' * Matrix.diagonal (fun j ↦ f (M.eigvals j)) =
        Matrix.diagonal (fun j ↦ f (M.eigvals j)) * Z' := by
      ext i j
      have hij := congr_fun (congr_fun hZ'_comm i) j
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Function.comp_apply] at hij ⊢
      by_cases h0 : Z' i j = 0
      · simp [h0]
      · have heq : M.eigvals j = M.eigvals i := by
          have hsub : ((M.eigvals j - M.eigvals i : ℝ) : ℂ) * Z' i j = 0 := by
            push_cast; linear_combination hij
          rcases mul_eq_zero.mp hsub with h1 | h1
          · exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h1)
          · exact absurd h1 h0
        rw [heq, mul_comm]
    have hZL : Z * L_M = L_M * Z := by
      calc Z * L_M = UM * (Z' * Matrix.diagonal (fun j ↦ f (M.eigvals j))) * star UM := by
              simp [L_M, Z', UM, f, Matrix.mul_assoc, Unitary.coe_mul_star_self]
        _ = UM * (Matrix.diagonal (fun j ↦ f (M.eigvals j)) * Z') * star UM := by rw [hZ'_f]
        _ = L_M * Z := by
              simp [L_M, Z', UM, f, Matrix.mul_assoc, Unitary.coe_mul_star_self]
    calc Z * L_M * Z = L_M * (Z * Z) := by rw [hZL, Matrix.mul_assoc]
      _ = L_M := by rw [hZZ, Matrix.mul_one]
  have htr_ZA : ((Z * A.mat * Z) * L_M).trace = (A.mat * L_M).trace := by
    calc ((Z * A.mat * Z) * L_M).trace
        = (Z * (A.mat * (Z * L_M))).trace := by simp [Matrix.mul_assoc]
      _ = (A.mat * (Z * L_M) * Z).trace := Matrix.trace_mul_comm _ _
      _ = (A.mat * (Z * L_M * Z)).trace := by simp [Matrix.mul_assoc]
      _ = (A.mat * L_M).trace := by rw [hZL_comm]
  have htr_eq : (A.mat * L_M).trace = (M.mat * L_M).trace := by
    rw [hM_avg, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_add,
        Matrix.trace_smul, Matrix.trace_smul, htr_ZA]
    simp [smul_eq_mul]; ring
  have htr_M : (M.mat * L_M).trace.re / Real.log 2 = -vonNeumannEntropy M := by
    have hspec := M.posSemidef.isHermitian.spectral_theorem
    have htr : (M.mat * L_M).trace =
        ∑ j : Bool × d, (M.eigvals j : ℂ) *
          (if M.eigvals j = 0 then (0 : ℂ) else (Real.log (M.eigvals j) : ℂ)) := by
      rw [hspec]
      have h1 : ((M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
          Matrix.diagonal (Complex.ofReal ∘ M.eigvals) *
          star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)) * L_M =
          (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
          (Matrix.diagonal (Complex.ofReal ∘ M.eigvals) *
           Matrix.diagonal (fun j ↦ if M.eigvals j = 0 then (0 : ℂ) else (Real.log (M.eigvals j) : ℂ))) *
          star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) := by
        simp [L_M, Matrix.mul_assoc, Unitary.coe_star_mul_self]
      rw [h1, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
          Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      rfl
    rw [htr]
    simp only [Complex.re_sum]
    unfold vonNeumannEntropy
    rw [← Finset.sum_div, neg_eq_iff_eq_neg, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro j _
    by_cases hj : M.eigvals j = 0
    · simp [hj]
    · simp only [hj, ↓reduceIte, ← Complex.ofReal_mul, Complex.ofReal_re, Real.logb]; ring
  rw [relEntropy_eq_trace_log A M (suppSubset_dephaseState_half p hp0 hp1 Ψ), htr_eq, htr_M]
  congr 1; ring

/-- `(relEntropy (dephaseState p ...) (dephaseState (1/2) ...)).toReal = dephaseCoherence p ... Ψ`. -/
theorem relEntropy_dephaseState_toReal_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) :
    (relEntropy (dephaseState p hp0 hp1 Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal =
      dephaseCoherence p hp0 hp1 Ψ := by
  rw [relEntropy_dephaseState_eq p hp0 hp1 Ψ]
  have hnn : 0 ≤ vonNeumannEntropy (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) -
      vonNeumannEntropy (dephaseState p hp0 hp1 Ψ) := by
    have hqjs := dephaseCoherence_eq_qjs p hp0 hp1 Ψ
    have hcond := (condEntropy_mem_Icc
      ({ out := fun b ↦ if b = false then dephaseState p hp0 hp1 Ψ
          else DensityOp.conjUnitary (pauliZTensorI d) (dephaseState p hp0 hp1 Ψ) } :
        CQChannel (Bool × d))).2
    unfold CQChannel.condEntropy at hcond
    unfold dephaseCoherence at hqjs
    simp only [↓reduceIte, Bool.true_eq_false] at hcond
    linarith
  exact ENNReal.toReal_ofReal hnn

/-- **Theorem 1.3 (Nonlinear SDPI for Qubit Dephasing, Relative-Entropy Form)**:
With `C(p) := D((Z_p ⊗ id)(Ψ) ‖ (Z_{1/2} ⊗ id)(Ψ))`, for every bipartite density operator
`Ψ ∈ D(ℂ² ⊗ H_B)` and every `p ∈ [0, 1/2]`,
`C(p) ≤ 1 - h₂(h₂⁻¹(1 - C(0)) * p)`. -/
theorem theorem_1_3_dephasing_sdpi_relEntropy (Ψ : DensityOp (Bool × d))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal ≤
      1 - h2 (binConv (h2Inv (1 -
        (relEntropy (dephaseState 0 le_rfl (by norm_num) Ψ)
          (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal)) p) := by
  rw [relEntropy_dephaseState_toReal_eq, relEntropy_dephaseState_toReal_eq]
  exact theorem_1_3_dephasing_sdpi Ψ hp0 hp1

/-- **Theorem 1.3 (Equatorial Equality, Relative-Entropy Form)**:
Every equatorial single-qubit state `½ (I + x X)` (`x ∈ [0, 1]`) attains equality in
Theorem 1.3 (stated via Umegaki relative entropy) for every `p ∈ [0, 1/2]`. -/
theorem theorem_1_3_equatorial_equality_relEntropy {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1))
      (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal =
      1 - h2 (binConv (h2Inv (1 -
        (relEntropy (dephaseState 0 le_rfl (by norm_num) (equatorialState x hx0 hx1))
          (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal)) p) := by
  rw [relEntropy_dephaseState_toReal_eq, relEntropy_dephaseState_toReal_eq]
  exact theorem_1_3_equatorial_equality hx0 hx1 hp0 hp1

end RelEntropyTheorem13

/-! ### Part 4: Channel Equivalence for Proposition 2.2 (D2)–(D3) (Gap 4) -/

section ChannelEquivalence

/-- Output-isometry equivalence between two binary-input c-q channels:
there exists a common finite-dimensional ambient space `γ` and isometries
`V₁ : d₁ → γ`, `V₂ : d₂ → γ` (`V₁ᴴ V₁ = I`, `V₂ᴴ V₂ = I`) such that
`V₁ W₁(b) V₁ᴴ = V₂ W₂(b) V₂ᴴ` for both `b ∈ {false, true}`. -/
def CQChannel.IsoEquiv {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) : Prop :=
  ∃ (γ : Type u) (_ : Fintype γ) (_ : DecidableEq γ)
    (V₁ : Matrix γ d₁ ℂ) (V₂ : Matrix γ d₂ ℂ),
    V₁ᴴ * V₁ = 1 ∧ V₂ᴴ * V₂ = 1 ∧
    ∀ b : Bool, V₁ * (W₁.out b).mat * V₁ᴴ = V₂ * (W₂.out b).mat * V₂ᴴ

/-- Reversible CPTP channel equivalence between two binary-input c-q channels:
there exist CPTP maps `𝒩 : d₁ → d₂` and `ℳ : d₂ → d₁` such that
`𝒩(W₁(b)) = W₂(b)` and `ℳ(W₂(b)) = W₁(b)` for both `b ∈ {false, true}`. -/
def CQChannel.ChannelEquiv {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) : Prop :=
  ∃ (𝒩 : CPTPMap.{u} d₁ d₂) (ℳ : CPTPMap.{u} d₂ d₁),
    (∀ b : Bool, (𝒩.apply (W₁.out b)).mat = (W₂.out b).mat) ∧
    (∀ b : Bool, (ℳ.apply (W₂.out b)).mat = (W₁.out b).mat)

lemma CQChannel.ChannelEquiv.refl {d : Type u} [Fintype d] [DecidableEq d] (W : CQChannel d) :
    W.ChannelEquiv W := by
  refine ⟨CPTPMap.id d, CPTPMap.id d, fun b ↦ ?_, fun b ↦ ?_⟩ <;>
  · ext i j
    change (partialTrace₂Mat ((CPTPMap.id d).isom * (W.out b).mat * (CPTPMap.id d).isomᴴ)) i j =
      (W.out b).mat i j
    dsimp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, CPTPMap.id]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma CQChannel.ChannelEquiv.symm {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.ChannelEquiv W₂) : W₂.ChannelEquiv W₁ := by
  rcases h with ⟨𝒩, ℳ, h1, h2⟩
  exact ⟨ℳ, 𝒩, h2, h1⟩

lemma CQChannel.ChannelEquiv.trans {d₁ d₂ d₃ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃]
    {W₁ : CQChannel d₁} {W₂ : CQChannel d₂} {W₃ : CQChannel d₃}
    (h12 : W₁.ChannelEquiv W₂) (h23 : W₂.ChannelEquiv W₃) : W₁.ChannelEquiv W₃ := by
  rcases h12 with ⟨𝒩₁, ℳ₁, h1, h2⟩
  rcases h23 with ⟨𝒩₂, ℳ₂, h3, h4⟩
  refine ⟨𝒩₂.comp 𝒩₁, ℳ₁.comp ℳ₂, fun b ↦ ?_, fun b ↦ ?_⟩
  · rw [CPTPMap.comp_apply]
    have heq : 𝒩₁.apply (W₁.out b) = W₂.out b := by
      cases hA : 𝒩₁.apply (W₁.out b); cases hB : W₂.out b
      have hm := h1 b; rw [hA, hB] at hm; simp_all
    rw [heq]; exact h3 b
  · rw [CPTPMap.comp_apply]
    have heq : ℳ₂.apply (W₂.out b) = W₁.out b := by
      cases hA : ℳ₂.apply (W₂.out b); cases hB : W₁.out b
      have hm := h4 b; rw [hA, hB] at hm; simp_all
    rw [heq]; exact h2 b

/-- Reversible CPTP channel equivalence immediately implies equality of `condEntropy`,
`symCapacity`, and `qjs`. -/
theorem CQChannel.ChannelEquiv.condEntropy_eq {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.ChannelEquiv W₂) : W₁.condEntropy = W₂.condEntropy := by
  rcases h with ⟨𝒩, ℳ, h1, h2⟩
  have hle1 : W₁.condEntropy ≤ W₂.condEntropy := by
    have hge := condEntropy_cptp_ge 𝒩 W₁
    have heq : (𝒩.compCQ W₁).condEntropy = W₂.condEntropy := by
      have hch : 𝒩.compCQ W₁ = W₂ := by
        cases W₂ with | mk out₂ =>
        congr 1; funext b
        have hb := h1 b
        simp only [CPTPMap.compCQ] at hb ⊢
        cases 𝒩.apply (W₁.out b); cases out₂ b; simp_all
      rw [hch]
    linarith
  have hle2 : W₂.condEntropy ≤ W₁.condEntropy := by
    have hge := condEntropy_cptp_ge ℳ W₂
    have heq : (ℳ.compCQ W₂).condEntropy = W₁.condEntropy := by
      have hch : ℳ.compCQ W₂ = W₁ := by
        cases W₁ with | mk out₁ =>
        congr 1; funext b
        have hb := h2 b
        simp only [CPTPMap.compCQ] at hb ⊢
        cases ℳ.apply (W₂.out b); cases out₁ b; simp_all
      rw [hch]
    linarith
  exact le_antisymm hle1 hle2

/-- Build a CPTP map from any contraction `K : Matrix β α ℂ` (`1 - Kᴴ K ≥ 0`), mapping
`ρ ↦ K ρ Kᴴ + Tr((1 - Kᴴ K) ρ) |b₀⟩⟨b₀|`. -/
noncomputable def CPTPMap.ofContraction {α β : Type u} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (K : Matrix β α ℂ) (hK : (1 - Kᴴ * K).PosSemidef) : CPTPMap.{u} α β := by
  let b₀ : β := Classical.arbitrary β
  let D : Matrix α α ℂ :=
    (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ) *
    Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
    star (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
  have hD_herm : Dᴴ = D := by
    simp only [D, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have hdiag : (Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)))ᴴ =
        Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) := by
      ext i j; simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
      split_ifs with h1 h2
      · rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · rfl
    rw [hdiag]; rfl
  have hDD : D * D = 1 - Kᴴ * K := by
    set U := (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
    have hspec := hK.isHermitian.spectral_theorem
    have hdiag_sq : Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
        Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) =
        Matrix.diagonal (Complex.ofReal ∘ hK.isHermitian.eigenvalues) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      simp only [Function.comp_apply, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hK.eigenvalues_nonneg i)]
    calc D * D = U * (Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
            (star U * U) * Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ))) *
            star U := by simp [D, U, Matrix.mul_assoc]
      _ = U * Matrix.diagonal (Complex.ofReal ∘ hK.isHermitian.eigenvalues) * star U := by
            rw [Unitary.coe_star_mul_self, Matrix.mul_one, hdiag_sq]
      _ = 1 - Kᴴ * K := hspec.symm
  refine ⟨PUnit.{u + 1} ⊕ α, inferInstance, inferInstance,
    Matrix.of fun (p : β × (PUnit.{u + 1} ⊕ α)) (a : α) ↦
      match p.2 with
      | Sum.inl _ => K p.1 a
      | Sum.inr c => if p.1 = b₀ then D c a else 0, ?_⟩
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_unique]
  have h1 : ∑ x : β, star (K x i) * K x j = (Kᴴ * K) i j := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h2 : ∑ x : β, ∑ c : α, star (if x = b₀ then D c i else 0) * (if x = b₀ then D c j else 0) =
      (Dᴴ * D) i j := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
    simp
  rw [Finset.sum_add_distrib, h1, h2, hD_herm, hDD]
  simp

lemma CPTPMap.ofContraction_apply_eq {α β : Type u} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (K : Matrix β α ℂ) (hK : (1 - Kᴴ * K).PosSemidef) (ρ : DensityOp α)
    (hker : (1 - Kᴴ * K) * ρ.mat = 0) :
    ((CPTPMap.ofContraction K hK).apply ρ).mat = K * ρ.mat * Kᴴ := by
  let D : Matrix α α ℂ :=
    (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ) *
    Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
    star (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
  have hD_herm : Dᴴ = D := by
    simp only [D, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have hdiag : (Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)))ᴴ =
        Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) := by
      ext i j; simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
      split_ifs with h1 h2
      · rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · rfl
    rw [hdiag]; rfl
  have hDD : D * D = 1 - Kᴴ * K := by
    set U := (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
    have hspec := hK.isHermitian.spectral_theorem
    have hdiag_sq : Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
        Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) =
        Matrix.diagonal (Complex.ofReal ∘ hK.isHermitian.eigenvalues) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      simp only [Function.comp_apply, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hK.eigenvalues_nonneg i)]
    calc D * D = U * (Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
            (star U * U) * Matrix.diagonal (fun i : α ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ))) *
            star U := by simp [D, U, Matrix.mul_assoc]
      _ = U * Matrix.diagonal (Complex.ofReal ∘ hK.isHermitian.eigenvalues) * star U := by
            rw [Unitary.coe_star_mul_self, Matrix.mul_one, hdiag_sq]
      _ = 1 - Kᴴ * K := hspec.symm
  have hDρD_tr : (D * ρ.mat * Dᴴ).trace = 0 := by
    rw [Matrix.trace_mul_cycle, hD_herm, hDD, hker, Matrix.trace_zero]
  have hDρD : D * ρ.mat * Dᴴ = 0 := by
    have hpsd : (D * ρ.mat * Dᴴ).PosSemidef := ρ.posSemidef.mul_mul_conjTranspose_same D
    have hspec := hpsd.isHermitian.spectral_theorem
    have heig_zero : ∀ i, hpsd.isHermitian.eigenvalues i = 0 := by
      have hsum : ∑ i : α, hpsd.isHermitian.eigenvalues i = 0 := by
        have htr := hpsd.isHermitian.trace_eq_sum_eigenvalues
        rw [hDρD_tr] at htr
        exact_mod_cast htr.symm
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ hpsd.eigenvalues_nonneg k)).mp hsum i
        (Finset.mem_univ i)
    rw [hspec]
    have hdiag0 : Matrix.diagonal (Complex.ofReal ∘ hpsd.isHermitian.eigenvalues) = 0 := by
      ext i j; simp [Matrix.diagonal_apply, heig_zero]
    rw [hdiag0, Matrix.mul_zero, Matrix.zero_mul]
  ext b₁ b₂
  change (partialTrace₂Mat ((CPTPMap.ofContraction K hK).isom * ρ.mat *
    (CPTPMap.ofContraction K hK).isomᴴ)) b₁ b₂ = (K * ρ.mat * Kᴴ) b₁ b₂
  dsimp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, CPTPMap.ofContraction]
  simp only [Matrix.of_apply, Fintype.sum_sum_type, Fintype.sum_unique, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  have hzero : ∑ c : α, ∑ a₂ : α, (∑ a₁ : α, (if b₁ = Classical.arbitrary β then D c a₁ else 0) *
      ρ.mat a₁ a₂) * star (if b₂ = Classical.arbitrary β then D c a₂ else 0) = 0 := by
    by_cases h1 : b₁ = Classical.arbitrary β
    · by_cases h2 : b₂ = Classical.arbitrary β
      · simp only [h1, h2, ↓reduceIte]
        have htr : ∑ c : α, (D * ρ.mat * Dᴴ) c c = 0 := by
          simp [hDρD]
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using htr
      · simp [h2]
    · simp [h1]
  rw [hzero, add_zero]

/-- Output-isometry equivalence implies reversible CPTP channel equivalence. -/
lemma CQChannel.IsoEquiv.toChannelEquiv {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.IsoEquiv W₂) : W₁.ChannelEquiv W₂ := by
  haveI : Nonempty d₁ := by
    by_contra h0; haveI : IsEmpty d₁ := not_nonempty_iff.mp h0
    have htr := (W₁.out false).trace_one; simp [Matrix.trace] at htr
  haveI : Nonempty d₂ := by
    by_contra h0; haveI : IsEmpty d₂ := not_nonempty_iff.mp h0
    have htr := (W₂.out false).trace_one; simp [Matrix.trace] at htr
  rcases h with ⟨γ, _, _, V₁, V₂, hV₁, hV₂, heq⟩
  let K₁ : Matrix d₂ d₁ ℂ := V₂ᴴ * V₁
  let K₂ : Matrix d₁ d₂ ℂ := V₁ᴴ * V₂
  have hK₁_contr : (1 - K₁ᴴ * K₁).PosSemidef := by
    have h1 : 1 - K₁ᴴ * K₁ = V₁ᴴ * (1 - V₂ * V₂ᴴ) * V₁ := by
      simp only [K₁, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV₁, Matrix.mul_assoc]
    have hproj : (1 - V₂ * V₂ᴴ).PosSemidef := by
      have hp : (1 - V₂ * V₂ᴴ) = (1 - V₂ * V₂ᴴ)ᴴ * (1 - V₂ * V₂ᴴ) := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_one, Matrix.one_mul]
        have hsq : V₂ * V₂ᴴ * (V₂ * V₂ᴴ) = V₂ * V₂ᴴ := by
          calc V₂ * V₂ᴴ * (V₂ * V₂ᴴ) = V₂ * (V₂ᴴ * V₂) * V₂ᴴ := by simp [Matrix.mul_assoc]
            _ = V₂ * V₂ᴴ := by rw [hV₂, Matrix.mul_one]
        rw [hsq]; abel
      rw [hp]; exact Matrix.posSemidef_conjTranspose_mul_self _
    rw [h1]; exact hproj.conjTranspose_mul_mul_same V₁
  have hK₂_contr : (1 - K₂ᴴ * K₂).PosSemidef := by
    have h1 : 1 - K₂ᴴ * K₂ = V₂ᴴ * (1 - V₁ * V₁ᴴ) * V₂ := by
      simp only [K₂, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV₂, Matrix.mul_assoc]
    have hproj : (1 - V₁ * V₁ᴴ).PosSemidef := by
      have hp : (1 - V₁ * V₁ᴴ) = (1 - V₁ * V₁ᴴ)ᴴ * (1 - V₁ * V₁ᴴ) := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_one, Matrix.one_mul]
        have hsq : V₁ * V₁ᴴ * (V₁ * V₁ᴴ) = V₁ * V₁ᴴ := by
          calc V₁ * V₁ᴴ * (V₁ * V₁ᴴ) = V₁ * (V₁ᴴ * V₁) * V₁ᴴ := by simp [Matrix.mul_assoc]
            _ = V₁ * V₁ᴴ := by rw [hV₁, Matrix.mul_one]
        rw [hsq]; abel
      rw [hp]; exact Matrix.posSemidef_conjTranspose_mul_self _
    rw [h1]; exact hproj.conjTranspose_mul_mul_same V₂
  refine ⟨CPTPMap.ofContraction K₁ hK₁_contr, CPTPMap.ofContraction K₂ hK₂_contr, ?_, ?_⟩
  · intro b
    have hker : (1 - K₁ᴴ * K₁) * (W₁.out b).mat = 0 := by
      have h1 : K₁ᴴ * K₁ * (W₁.out b).mat = (W₁.out b).mat := by
        calc K₁ᴴ * K₁ * (W₁.out b).mat
            = V₁ᴴ * V₂ * V₂ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₁ := by
                simp only [K₁, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
                  Matrix.mul_assoc]
                have : (W₁.out b).mat * (V₁ᴴ * V₁) = (W₁.out b).mat := by rw [hV₁, Matrix.mul_one]
                simpa [Matrix.mul_assoc] using congr_arg (fun X ↦ V₁ᴴ * V₂ * V₂ᴴ * V₁ * X) this.symm
          _ = V₁ᴴ * V₂ * V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₁ := by rw [heq b]
          _ = V₁ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₁ := by
                calc V₁ᴴ * V₂ * V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₁
                    = V₁ᴴ * (V₂ * (V₂ᴴ * V₂) * (W₂.out b).mat * V₂ᴴ) * V₁ := by simp [Matrix.mul_assoc]
                  _ = _ := by rw [hV₂, Matrix.mul_one]
          _ = V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₁ := by rw [← heq b]
          _ = (W₁.out b).mat := by
                calc V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₁
                    = (V₁ᴴ * V₁) * (W₁.out b).mat * (V₁ᴴ * V₁) := by simp [Matrix.mul_assoc]
                  _ = (W₁.out b).mat := by rw [hV₁, Matrix.one_mul, Matrix.mul_one]
      rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self]
    rw [CPTPMap.ofContraction_apply_eq K₁ hK₁_contr (W₁.out b) hker]
    calc K₁ * (W₁.out b).mat * K₁ᴴ
        = V₂ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₂ := by
            simp [K₁, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₂ := by rw [heq b]
      _ = (W₂.out b).mat := by
            calc V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₂
                = (V₂ᴴ * V₂) * (W₂.out b).mat * (V₂ᴴ * V₂) := by simp [Matrix.mul_assoc]
              _ = (W₂.out b).mat := by rw [hV₂, Matrix.one_mul, Matrix.mul_one]
  · intro b
    have hker : (1 - K₂ᴴ * K₂) * (W₂.out b).mat = 0 := by
      have h1 : K₂ᴴ * K₂ * (W₂.out b).mat = (W₂.out b).mat := by
        calc K₂ᴴ * K₂ * (W₂.out b).mat
            = V₂ᴴ * V₁ * V₁ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₂ := by
                simp only [K₂, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
                  Matrix.mul_assoc]
                have : (W₂.out b).mat * (V₂ᴴ * V₂) = (W₂.out b).mat := by rw [hV₂, Matrix.mul_one]
                simpa [Matrix.mul_assoc] using congr_arg (fun X ↦ V₂ᴴ * V₁ * V₁ᴴ * V₂ * X) this.symm
          _ = V₂ᴴ * V₁ * V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₂ := by rw [← heq b]
          _ = V₂ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₂ := by
                calc V₂ᴴ * V₁ * V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₂
                    = V₂ᴴ * (V₁ * (V₁ᴴ * V₁) * (W₁.out b).mat * V₁ᴴ) * V₂ := by simp [Matrix.mul_assoc]
                  _ = _ := by rw [hV₁, Matrix.mul_one]
          _ = V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₂ := by rw [heq b]
          _ = (W₂.out b).mat := by
                calc V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₂
                    = (V₂ᴴ * V₂) * (W₂.out b).mat * (V₂ᴴ * V₂) := by simp [Matrix.mul_assoc]
                  _ = (W₂.out b).mat := by rw [hV₂, Matrix.one_mul, Matrix.mul_one]
      rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self]
    rw [CPTPMap.ofContraction_apply_eq K₂ hK₂_contr (W₂.out b) hker]
    calc K₂ * (W₂.out b).mat * K₂ᴴ
        = V₁ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₁ := by
            simp [K₂, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₁ := by rw [← heq b]
      _ = (W₁.out b).mat := by
            calc V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₁
                = (V₁ᴴ * V₁) * (W₁.out b).mat * (V₁ᴴ * V₁) := by simp [Matrix.mul_assoc]
              _ = (W₁.out b).mat := by rw [hV₁, Matrix.one_mul, Matrix.mul_one]

lemma CQChannel.IsoEquiv.condEntropy_eq {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.IsoEquiv W₂) : W₁.condEntropy = W₂.condEntropy :=
  h.toChannelEquiv.condEntropy_eq

/-- Appending an independent maximally mixed register `I/|α|` yields a `ChannelEquiv` channel. -/
noncomputable def CQChannel.tensorMaxMixed {d : Type u} [Fintype d] [DecidableEq d]
    (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α] (W : CQChannel d) :
    CQChannel (α × d) where
  out b := DensityOp.tensor (maxMixedState α) (W.out b)

lemma CQChannel.channelEquiv_tensorMaxMixed {d : Type u} [Fintype d] [DecidableEq d]
    (α : Type u) [Fintype α] [DecidableEq α] [Nonempty α] (W : CQChannel d) :
    W.ChannelEquiv (W.tensorMaxMixed α) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let c : ℂ := ((Real.sqrt (Fintype.card α : ℝ) : ℂ)⁻¹)
  have hc_sq : star c * c = ((Fintype.card α : ℂ)⁻¹) := by
    simp only [c, ← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt (le_of_lt hcard_pos)]
    push_cast; rfl
  let 𝒩 : CPTPMap.{u} d (α × d) :=
    ⟨α, inferInstance, inferInstance,
      Matrix.of fun (p : (α × d) × α) (x : d) ↦ if p.1.1 = p.2 ∧ p.1.2 = x then c else 0, by
        ext x y
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Fintype.sum_prod_type, Matrix.one_apply]
        by_cases hxy : x = y
        · subst hxy
          simp only [↓reduceIte]
          calc ∑ a : α, ∑ r : d, ∑ e : α,
                star (if a = e ∧ r = x then c else 0) * (if a = e ∧ r = x then c else 0)
              = ∑ a : α, (star c * c) := by
                  apply Finset.sum_congr rfl; intro a _
                  rw [Finset.sum_eq_single x]
                  · rw [Finset.sum_eq_single a]
                    · simp
                    · intro e _ hne; simp [Ne.symm hne]
                    · intro h; exact absurd (Finset.mem_univ a) h
                  · intro r _ hne; apply Finset.sum_eq_zero; intro e _; simp [hne]
                  · intro h; exact absurd (Finset.mem_univ x) h
            _ = (Fintype.card α : ℂ) * ((Fintype.card α : ℂ)⁻¹) := by
                  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc_sq]
            _ = 1 := mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        · simp only [hxy, ↓reduceIte]
          apply Finset.sum_eq_zero; intro a _
          apply Finset.sum_eq_zero; intro r _
          apply Finset.sum_eq_zero; intro e _
          by_cases hr : r = x
          · subst hr; simp [hxy]
          · simp [hr]⟩
  let ℳ : CPTPMap.{u} (α × d) d :=
    ⟨α, inferInstance, inferInstance,
      Matrix.of fun (p : d × α) (q : α × d) ↦ if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0, by
        ext ⟨a₁, x₁⟩ ⟨a₂, x₂⟩
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Fintype.sum_prod_type, Matrix.one_apply]
        by_cases h : (a₁, x₁) = (a₂, x₂)
        · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
          simp only [↓reduceIte]
          rw [Finset.sum_eq_single x₁]
          · rw [Finset.sum_eq_single a₁]
            · simp
            · intro e _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ a₁) h
          · intro r _ hne; apply Finset.sum_eq_zero; intro e _; simp [hne]
          · intro h; exact absurd (Finset.mem_univ x₁) h
        · simp only [h, ↓reduceIte]
          apply Finset.sum_eq_zero; intro r _
          apply Finset.sum_eq_zero; intro e _
          by_cases h1 : r = x₁ ∧ e = a₁
          · rcases h1 with ⟨rfl, rfl⟩
            have h2 : ¬ (r = x₂ ∧ e = a₂) := fun ⟨hx, ha⟩ ↦ h (by rw [ha, hx])
            simp [h2]
          · simp [h1]⟩
  refine ⟨𝒩, ℳ, ?_, ?_⟩
  · intro b
    ext ⟨a₁, x₁⟩ ⟨a₂, x₂⟩
    change (partialTrace₂Mat (𝒩.isom * (W.out b).mat * 𝒩.isomᴴ)) (a₁, x₁) (a₂, x₂) =
      (DensityOp.tensor (maxMixedState α) (W.out b)).mat (a₁, x₁) (a₂, x₂)
    dsimp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, 𝒩]
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      DensityOp.tensor, maxMixedState, Matrix.kroneckerMap_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    rw [Finset.sum_eq_single a₁]
    · rw [Finset.sum_eq_single x₂]
      · rw [Finset.sum_eq_single x₁]
        · by_cases ha : a₁ = a₂
          · subst ha
            simp only [↓reduceIte, mul_one]
            calc c * (W.out b).mat x₁ x₂ * star c
                = (star c * c) * (W.out b).mat x₁ x₂ := by ring
              _ = _ := by rw [hc_sq]
          · simp [ha, Ne.symm ha]
        · intro y₁ _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ x₁) h
      · intro y₂ _ hne; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ x₂) h
    · intro e _ hne
      apply Finset.sum_eq_zero; intro y₂ _
      apply Finset.sum_eq_zero; intro y₁ _
      simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ a₁) h
  · intro b
    ext x₁ x₂
    change (partialTrace₂Mat (ℳ.isom * (DensityOp.tensor (maxMixedState α) (W.out b)).mat *
      ℳ.isomᴴ)) x₁ x₂ = (W.out b).mat x₁ x₂
    dsimp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, ℳ]
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      DensityOp.tensor, maxMixedState, Matrix.kroneckerMap_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, Fintype.sum_prod_type]
    have hsum : ∑ e : α,
        (∑ a₂ : α, ∑ y₂ : d,
          (∑ a₁ : α, ∑ y₁ : d,
            (if x₁ = y₁ ∧ e = a₁ then (1 : ℂ) else 0) *
            (((Fintype.card α : ℂ)⁻¹ * (if a₁ = a₂ then 1 else 0)) * (W.out b).mat y₁ y₂)) *
          star (if x₂ = y₂ ∧ e = a₂ then (1 : ℂ) else 0)) =
        ∑ _ : α, ((Fintype.card α : ℂ)⁻¹ * (W.out b).mat x₁ x₂) := by
      apply Finset.sum_congr rfl; intro e _
      rw [Finset.sum_eq_single e]
      · rw [Finset.sum_eq_single x₂]
        · rw [Finset.sum_eq_single e]
          · rw [Finset.sum_eq_single x₁]
            · simp
            · intro y₁ _ hne; simp [Ne.symm hne]
            · intro h; exact absurd (Finset.mem_univ x₁) h
          · intro a₁ _ hne; apply Finset.sum_eq_zero; intro y₁ _; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ e) h
        · intro y₂ _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ x₂) h
      · intro a₂ _ hne; apply Finset.sum_eq_zero; intro y₂ _; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ e) h
    rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

/-- Any factorization `A₀ * A₀ᴴ = W(0)`, `A₁ * A₁ᴴ = W(1)` yields a dual channel `W_E` on
`Bool × E` that is `IsoEquiv` to `W.dual`. -/
lemma dual_isoEquiv_of_purification {d E : Type u} [Fintype d] [DecidableEq d]
    [Fintype E] [DecidableEq E] (W : CQChannel d)
    (A₀ A₁ : Matrix d E ℂ)
    (hA₀ : A₀ * A₀ᴴ = (W.out false).mat)
    (hA₁ : A₁ * A₁ᴴ = (W.out true).mat) :
    let M₀ : Matrix (Bool × E) d ℂ :=
      Matrix.of fun p x ↦ ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)
    let M₁ : Matrix (Bool × E) d ℂ :=
      Matrix.of fun p x ↦ ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)
    let W_E : CQChannel (Bool × E) :=
      { out := fun b ↦
          match b with
          | false =>
            { mat := M₀ * M₀ᴴ
              posSemidef := Matrix.posSemidef_mul_conjTranspose_self M₀
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hsq2 : ((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
                  rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal,
                    ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
                  push_cast; ring
                have hMM : M₀ᴴ * M₀ = (1 / 2 : ℂ) • (W.out false).mat + (1 / 2 : ℂ) • (W.out true).mat := by
                  ext x y
                  simp only [M₀, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul']
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
                  rw [Finset.sum_add_distrib]
                  congr 1 <;>
                    (apply Finset.sum_congr rfl; intro e _;
                     calc star (star (A₀ x e)) * star ((Real.sqrt 2 : ℂ)⁻¹) * (((Real.sqrt 2 : ℂ)⁻¹) * star (A₀ y e))
                         = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) * (A₀ x e * star (A₀ y e)) := by simp; ring
                       _ = (1 / 2 : ℂ) * (A₀ x e * star (A₀ y e)) := by rw [hsq2]
                     <|>
                     calc star (star (A₁ x e)) * star ((Real.sqrt 2 : ℂ)⁻¹) * (((Real.sqrt 2 : ℂ)⁻¹) * star (A₁ y e))
                         = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) * (A₁ x e * star (A₁ y e)) := by simp; ring
                       _ = (1 / 2 : ℂ) * (A₁ x e * star (A₁ y e)) := by rw [hsq2])
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    (W.out false).trace_one, (W.out true).trace_one]
                simp [smul_eq_mul]; ring }
          | true =>
            { mat := M₁ * M₁ᴴ
              posSemidef := Matrix.posSemidef_mul_conjTranspose_self M₁
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hsq2 : ((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
                  rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal,
                    ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
                  push_cast; ring
                have hMM : M₁ᴴ * M₁ = (1 / 2 : ℂ) • (W.out false).mat + (1 / 2 : ℂ) • (W.out true).mat := by
                  ext x y
                  simp only [M₁, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul', star_neg]
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
                  rw [Finset.sum_add_distrib]
                  congr 1 <;>
                    (apply Finset.sum_congr rfl; intro e _;
                     calc star (star (A₀ x e)) * star ((Real.sqrt 2 : ℂ)⁻¹) * (((Real.sqrt 2 : ℂ)⁻¹) * star (A₀ y e))
                         = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) * (A₀ x e * star (A₀ y e)) := by simp; ring
                       _ = (1 / 2 : ℂ) * (A₀ x e * star (A₀ y e)) := by rw [hsq2]
                     <|>
                     calc -(star (star (A₁ x e))) * star ((Real.sqrt 2 : ℂ)⁻¹) * (((Real.sqrt 2 : ℂ)⁻¹) * -(star (A₁ y e)))
                         = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) * (A₁ x e * star (A₁ y e)) := by simp; ring
                       _ = (1 / 2 : ℂ) * (A₁ x e * star (A₁ y e)) := by rw [hsq2])
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    (W.out false).trace_one, (W.out true).trace_one]
                simp [smul_eq_mul]; ring } }
    W.dual.IsoEquiv W_E := by
  intro M₀ M₁ W_E
  have hfactor : ∀ (τ : DensityOp d) (A : Matrix d E ℂ), A * Aᴴ = τ.mat →
      ∃ V : Matrix (E ⊕ d) d ℂ, Vᴴ * V = 1 ∧
        ∀ (y : E ⊕ d) (x : d), (V * τ.sqrtMat) y x =
          match y with
          | Sum.inl e => Aᴴ e x
          | Sum.inr _ => 0 := by
    intro τ A hA
    set U := (τ.eigUnitary : Matrix d d ℂ)
    have hU_star : star U * U = 1 := Unitary.coe_star_mul_self τ.eigUnitary
    have hspec : τ.mat = U * Matrix.diagonal (Complex.ofReal ∘ τ.eigvals) * star U :=
      τ.posSemidef.isHermitian.spectral_theorem
    let pinv : Matrix d d ℂ :=
      U * Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) * star U
    let P : Matrix d d ℂ :=
      U * Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) * star U
    let Q : Matrix d d ℂ := 1 - P
    have hP_herm : Pᴴ = P := by
      simp only [P, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      have hd : (Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0))ᴴ =
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) := by
        ext i j; simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
        split_ifs with h1 h2
        · simp
        · exact absurd h1.symm h2
        · exact absurd h2.symm h1
        · rfl
      rw [hd]; rfl
    have hP_idem : P * P = P := by
      have hd : Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) *
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) =
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) := by
        rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> simp
      calc P * P = U * (Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) *
              (star U * U) * Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0)) * star U := by
                simp [P, Matrix.mul_assoc]
        _ = P := by rw [hU_star, Matrix.mul_one, hd]
    have hpinv_herm : pinvᴴ = pinv := by
      simp only [pinv, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      have hd : (Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0))ᴴ =
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) := by
        ext i j; simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
        split_ifs with h1 h2
        · split_ifs <;> simp [← Complex.ofReal_inv]
        · exact absurd h1.symm h2
        · exact absurd h2.symm h1
        · rfl
      rw [hd]; rfl
    have hpinv_mul_mat : pinv * τ.mat * pinv = P := by
      have hd : Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) *
          Matrix.diagonal (Complex.ofReal ∘ τ.eigvals) *
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) =
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) := by
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        congr 1; funext i; simp only [Function.comp_apply]
        split_ifs with hi
        · have hne : (Real.sqrt (τ.eigvals i) : ℂ) ≠ 0 :=
            Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hi))
          have hsq : (Real.sqrt (τ.eigvals i) : ℂ) * (Real.sqrt (τ.eigvals i) : ℂ) = (τ.eigvals i : ℂ) := by
            rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hi)]
          rw [← hsq]; field_simp [hne]
        · simp
      calc pinv * τ.mat * pinv
          = U * (Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) *
            (star U * U) * Matrix.diagonal (Complex.ofReal ∘ τ.eigvals) * (star U * U) *
            Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0)) * star U := by
              rw [hspec]; simp [pinv, Matrix.mul_assoc]
        _ = P := by rw [hU_star, Matrix.mul_one, Matrix.mul_one, hd]
    have hsq_spec : τ.sqrtMat = U * Matrix.diagonal (fun i : d ↦ (Real.sqrt (τ.eigvals i) : ℂ)) * star U := rfl
    have hpinv_sqrt : pinv * τ.sqrtMat = P := by
      have hd : Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) *
          Matrix.diagonal (fun i : d ↦ (Real.sqrt (τ.eigvals i) : ℂ)) =
          Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) := by
        rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i
        split_ifs with hi
        · exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hi)))
        · simp
      calc pinv * τ.sqrtMat
          = U * (Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i) : ℂ)⁻¹) else 0) *
            (star U * U) * Matrix.diagonal (fun i : d ↦ (Real.sqrt (τ.eigvals i) : ℂ))) * star U := by
              rw [hsq_spec]; simp [pinv, Matrix.mul_assoc]
        _ = P := by rw [hU_star, Matrix.mul_one, hd]
    have hQ_sqrt : Q * τ.sqrtMat = 0 := by
      have hP_sqrt : P * τ.sqrtMat = τ.sqrtMat := by
        have hd : Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) *
            Matrix.diagonal (fun i : d ↦ (Real.sqrt (τ.eigvals i) : ℂ)) =
            Matrix.diagonal (fun i : d ↦ (Real.sqrt (τ.eigvals i) : ℂ)) := by
          rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i
          split_ifs with hi
          · simp
          · have h0 : τ.eigvals i = 0 := le_antisymm (not_lt.mp hi) (τ.eigvals_nonneg i)
            simp [h0]
        calc P * τ.sqrtMat
            = U * (Matrix.diagonal (fun i : d ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) *
              (star U * U) * Matrix.diagonal (fun i : d ↦ (Real.sqrt (τ.eigvals i) : ℂ))) * star U := by
                rw [hsq_spec]; simp [P, Matrix.mul_assoc]
          _ = τ.sqrtMat := by rw [hU_star, Matrix.mul_one, hd, ← hsq_spec]
      simp [Q, Matrix.sub_mul, Matrix.one_mul, hP_sqrt]
    have hQ_herm : Qᴴ = Q := by simp [Q, hP_herm]
    have hQ_idem : Q * Q = Q := by
      simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP_idem]; abel
    have hAH_Q : Aᴴ * Q = 0 := by
      have hQ_mat : Q * τ.mat * Qᴴ = 0 := by
        have hsq2 : τ.sqrtMat * τ.sqrtMat = τ.mat := τ.sqrtMat_mul_self
        rw [← hsq2]; calc Q * (τ.sqrtMat * τ.sqrtMat) * Qᴴ = (Q * τ.sqrtMat) * (τ.sqrtMat * Qᴴ) := by simp [Matrix.mul_assoc]
          _ = 0 := by rw [hQ_sqrt, Matrix.zero_mul]
      have hAQ : (Aᴴ * Q)ᴴ * (Aᴴ * Q) = 0 := by
        calc (Aᴴ * Q)ᴴ * (Aᴴ * Q) = Qᴴ * (A * Aᴴ) * Q := by
                simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = Q * τ.mat * Qᴴ := by rw [hA, hQ_herm]
          _ = 0 := hQ_mat
      ext e x
      have hdiag := congr_fun (congr_fun hAQ x) x
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply] at hdiag
      have hre := congr_arg Complex.re hdiag
      simp only [Complex.zero_re, Complex.re_sum] at hre
      have hsum : ∑ e' : E, ‖(Aᴴ * Q) e' x‖ ^ 2 = 0 := by
        rw [← hre]
        apply Finset.sum_congr rfl; intro e' _
        have hsq : star ((Aᴴ * Q) e' x) * (Aᴴ * Q) e' x = ((‖(Aᴴ * Q) e' x‖ ^ 2 : ℝ) : ℂ) := by
          rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [hsq, Complex.ofReal_re]
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun e' _ ↦ sq_nonneg ‖(Aᴴ * Q) e' x‖)).mp
        hsum e (Finset.mem_univ e)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hterm)
    have hAH_P : Aᴴ * P = Aᴴ := by
      have : Aᴴ * (1 - P) = 0 := hAH_Q
      rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
      exact this.symm
    let W_mat : Matrix E d ℂ := Aᴴ * pinv
    let V : Matrix (E ⊕ d) d ℂ := Matrix.of fun y x ↦
      match y with
      | Sum.inl e => W_mat e x
      | Sum.inr r => Q r x
    refine ⟨V, ?_, ?_⟩
    · ext i j
      simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_sum_type, Matrix.one_apply]
      have h1 : ∑ e : E, star (W_mat e i) * W_mat e j = P i j := by
        have hWW : W_matᴴ * W_mat = P := by
          calc W_matᴴ * W_mat = pinvᴴ * (A * Aᴴ) * pinv := by
                  simp [W_mat, Matrix.conjTranspose_mul, Matrix.mul_assoc]
            _ = pinv * τ.mat * pinv := by rw [hpinv_herm, hA]
            _ = P := hpinv_mul_mat
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using congr_fun (congr_fun hWW i) j
      have h2 : ∑ r : d, star (Q r i) * Q r j = Q i j := by
        have hQQ : Qᴴ * Q = Q := by rw [hQ_herm, hQ_idem]
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using congr_fun (congr_fun hQQ i) j
      rw [h1, h2]
      have hPQ : P + Q = 1 := by simp [Q]
      have := congr_fun (congr_fun hPQ i) j
      simpa [Matrix.add_apply, Matrix.one_apply] using this
    · intro y x
      cases y with
      | inl e =>
        have h1 : (V * τ.sqrtMat) (Sum.inl e) x = (W_mat * τ.sqrtMat) e x := by
          simp [V, Matrix.mul_apply]
        rw [h1]
        have hWsq : W_mat * τ.sqrtMat = Aᴴ := by
          calc W_mat * τ.sqrtMat = Aᴴ * (pinv * τ.sqrtMat) := by simp [W_mat, Matrix.mul_assoc]
            _ = Aᴴ * P := by rw [hpinv_sqrt]
            _ = Aᴴ := hAH_P
        rw [hWsq]
      | inr r =>
        have h1 : (V * τ.sqrtMat) (Sum.inr r) x = (Q * τ.sqrtMat) r x := by
          simp [V, Matrix.mul_apply]
        rw [h1, hQ_sqrt]; rfl
  obtain ⟨V₀, hV₀, hV₀_sq⟩ := hfactor (W.out false) A₀ hA₀
  obtain ⟨V₁, hV₁, hV₁_sq⟩ := hfactor (W.out true) A₁ hA₁
  let V : Matrix (Bool × (E ⊕ d)) (Bool × d) ℂ :=
    Matrix.of fun p q ↦ if p.1 = q.1 then (if p.1 = false then V₀ p.2 q.2 else V₁ p.2 q.2) else 0
  let ι : Matrix (Bool × (E ⊕ d)) (Bool × E) ℂ :=
    Matrix.of fun p q ↦ if p.1 = q.1 ∧ p.2 = Sum.inl q.2 then 1 else 0
  have hV_iso : Vᴴ * V = 1 := by
    ext ⟨b₁, x₁⟩ ⟨b₂, x₂⟩
    simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
    by_cases hb : b₁ = b₂
    · subst hb
      rw [Finset.sum_eq_single b₁]
      · cases b₁
        · have h := congr_fun (congr_fun hV₀ x₁) x₂
          simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
        · have h := congr_fun (congr_fun hV₁ x₁) x₂
          simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
      · intro c _ hne; apply Finset.sum_eq_zero; intro y _; simp [hne]
      · intro h; exact absurd (Finset.mem_univ b₁) h
    · simp only [Prod.mk.injEq, hb, false_and, ↓reduceIte]
      apply Finset.sum_eq_zero; intro c _
      apply Finset.sum_eq_zero; intro y _
      by_cases hc : c = b₁
      · subst hc; simp [hb]
      · simp [hc]
  have hι_iso : ιᴴ * ι = 1 := by
    ext ⟨b₁, e₁⟩ ⟨b₂, e₂⟩
    simp only [ι, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.one_apply]
    by_cases h : (b₁, e₁) = (b₂, e₂)
    · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single b₁]
      · have h2 : ∑ a₂ : d, star (if b₁ = b₁ ∧ (Sum.inr a₂ : E ⊕ d) = Sum.inl e₁ then (1 : ℂ) else 0) *
            (if b₁ = b₁ ∧ (Sum.inr a₂ : E ⊕ d) = Sum.inl e₁ then 1 else 0) = 0 := by simp
        rw [h2, add_zero, Finset.sum_eq_single e₁]
        · simp
        · intro a₁ _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ e₁) h
      · intro c _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ b₁) h
    · simp only [h, ↓reduceIte]
      apply Finset.sum_eq_zero; intro c _
      have h2 : ∑ a₂ : d, star (if c = b₁ ∧ (Sum.inr a₂ : E ⊕ d) = Sum.inl e₁ then (1 : ℂ) else 0) *
          (if c = b₂ ∧ (Sum.inr a₂ : E ⊕ d) = Sum.inl e₂ then 1 else 0) = 0 := by simp
      rw [h2, add_zero]
      apply Finset.sum_eq_zero; intro a₁ _
      by_cases h1 : c = b₁ ∧ a₁ = e₁
      · rcases h1 with ⟨rfl, rfl⟩
        have h2' : ¬ (c = b₂ ∧ a₁ = e₂) := fun ⟨hb, he⟩ ↦ h (by rw [hb, he])
        simp [h2']
      · simp [h1]
  have hVM₀ : V * gramFactor (W.out false) (W.out true) = ι * M₀ := by
    ext ⟨b, y⟩ x
    simp only [V, ι, gramFactor, M₀, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single b, Finset.sum_eq_single b]
    · cases b
      · simp only [↓reduceIte]
        have hL : ∑ r : d, V₀ y r * (((Real.sqrt 2 : ℂ)⁻¹) * (W.out false).sqrtMat r x) =
            ((Real.sqrt 2 : ℂ)⁻¹) * (V₀ * (W.out false).sqrtMat) y x := by
          simp only [Matrix.mul_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro r _; ring
        rw [hL, hV₀_sq y x]
        cases y with
        | inl e =>
          rw [Finset.sum_eq_single e]
          · simp
          · intro e' _ hne; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ e) h
        | inr r => simp
      · simp only [↓reduceIte, Bool.true_eq_false]
        have hL : ∑ r : d, V₁ y r * (((Real.sqrt 2 : ℂ)⁻¹) * (W.out true).sqrtMat r x) =
            ((Real.sqrt 2 : ℂ)⁻¹) * (V₁ * (W.out true).sqrtMat) y x := by
          simp only [Matrix.mul_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro r _; ring
        rw [hL, hV₁_sq y x]
        cases y with
        | inl e =>
          rw [Finset.sum_eq_single e]
          · simp
          · intro e' _ hne; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ e) h
        | inr r => simp
    · intro c _ hne; apply Finset.sum_eq_zero; intro e _; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ b) h
    · intro c _ hne; apply Finset.sum_eq_zero; intro r _; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ b) h
  have hVM₁ : V * ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) *
      gramFactor (W.out false) (W.out true)) = ι * M₁ := by
    have hZ_comm : V * (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) =
        (pauliZTensorI (E ⊕ d) : Matrix (Bool × (E ⊕ d)) (Bool × (E ⊕ d)) ℂ) * V := by
      ext ⟨b₁, y⟩ ⟨b₂, x⟩
      simp [V, pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply]
      split_ifs <;> simp_all
    have hZ_ι : (pauliZTensorI (E ⊕ d) : Matrix (Bool × (E ⊕ d)) (Bool × (E ⊕ d)) ℂ) * ι =
        ι * (pauliZTensorI E : Matrix (Bool × E) (Bool × E) ℂ) := by
      ext ⟨b₁, y⟩ ⟨b₂, e⟩
      simp [ι, pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply]
      split_ifs <;> simp_all
    have hZ_M₀ : (pauliZTensorI E : Matrix (Bool × E) (Bool × E) ℂ) * M₀ = M₁ := by
      ext ⟨b, e⟩ x
      simp only [pauliZTensorI, M₀, M₁, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply,
        ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      cases b <;> simp
    calc V * ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) * gramFactor (W.out false) (W.out true))
        = (V * (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)) * gramFactor (W.out false) (W.out true) := by
            rw [Matrix.mul_assoc]
      _ = (pauliZTensorI (E ⊕ d) : Matrix (Bool × (E ⊕ d)) (Bool × (E ⊕ d)) ℂ) * (V * gramFactor (W.out false) (W.out true)) := by
            rw [hZ_comm, Matrix.mul_assoc]
      _ = (pauliZTensorI (E ⊕ d) : Matrix (Bool × (E ⊕ d)) (Bool × (E ⊕ d)) ℂ) * (ι * M₀) := by rw [hVM₀]
      _ = ι * ((pauliZTensorI E : Matrix (Bool × E) (Bool × E) ℂ) * M₀) := by
            rw [← Matrix.mul_assoc, hZ_ι, Matrix.mul_assoc]
      _ = ι * M₁ := by rw [hZ_M₀]
  refine ⟨Bool × (E ⊕ d), inferInstance, inferInstance, V, ι, hV_iso, hι_iso, ?_⟩
  intro b; cases b
  · change V * (gramFactor (W.out false) (W.out true) * (gramFactor (W.out false) (W.out true))ᴴ) * Vᴴ =
      ι * (M₀ * M₀ᴴ) * ιᴴ
    calc V * (gramFactor (W.out false) (W.out true) * (gramFactor (W.out false) (W.out true))ᴴ) * Vᴴ
        = (V * gramFactor (W.out false) (W.out true)) * (V * gramFactor (W.out false) (W.out true))ᴴ := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (ι * M₀) * (ι * M₀)ᴴ := by rw [hVM₀]
      _ = ι * (M₀ * M₀ᴴ) * ιᴴ := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · change V * ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) *
        (gramFactor (W.out false) (W.out true) * (gramFactor (W.out false) (W.out true))ᴴ) *
        star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)) * Vᴴ =
      ι * (M₁ * M₁ᴴ) * ιᴴ
    set G := gramFactor (W.out false) (W.out true)
    set Zd := (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)
    calc V * (Zd * (G * Gᴴ) * star Zd) * Vᴴ
        = (V * (Zd * G)) * (V * (Zd * G))ᴴ := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (ι * M₁) * (ι * M₁)ᴴ := by rw [hVM₁]
      _ = ι * (M₁ * M₁ᴴ) * ιᴴ := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Proposition 2.2 (D3, Exact Output-Isometry Duality for Pure-State Channels)**:
`Pure(1 - 2p)⊥` is literally output-isometry equivalent (`IsoEquiv`) to `BSC(p)` for all `p ∈ [0, 1/2]`. -/
theorem prop_2_2_D3_isoEquiv_pure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (pureChannel (1 - 2 * p) (by linarith) (by linarith)).dual.IsoEquiv
      (bscChannel p hp0 (by linarith)) := by
  set f : ℝ := 1 - 2 * p
  have hf0 : 0 ≤ f := by linarith
  have hf1 : f ≤ 1 := by linarith
  have h1pf : (1 + f) / 2 = 1 - p := by simp [f]; ring
  have h1mf : (1 - f) / 2 = p := by simp [f]; ring
  let A₀ : Matrix Bool PUnit.{1} ℂ :=
    Matrix.of fun b _ ↦ if b = false then (Real.sqrt (1 - p) : ℂ) else (Real.sqrt p : ℂ)
  let A₁ : Matrix Bool PUnit.{1} ℂ :=
    Matrix.of fun b _ ↦ if b = false then (Real.sqrt (1 - p) : ℂ) else -(Real.sqrt p : ℂ)
  have hA₀ : A₀ * A₀ᴴ = ((pureChannel f hf0 hf1).out false).mat := by
    ext i j
    simp only [A₀, pureChannel, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Fintype.sum_unique, h1pf, h1mf]
    cases i <;> cases j <;> simp
  have hA₁ : A₁ * A₁ᴴ = ((pureChannel f hf0 hf1).out true).mat := by
    ext i j
    simp only [A₁, pureChannel, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Fintype.sum_unique, h1pf, h1mf]
    cases i <;> cases j <;> simp
  obtain ⟨γ, _, _, V₁, V₂, h1, h2, heq⟩ :=
    dual_isoEquiv_of_purification (pureChannel f hf0 hf1) A₀ A₁ hA₀ hA₁
  let H : Matrix (Bool × PUnit.{1}) Bool ℂ :=
    Matrix.of fun r c ↦ ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = true ∧ c = true then -1 else 1)
  have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
  have hH_iso : Hᴴ * H = 1 := by
    ext i j
    simp only [H, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool, Matrix.one_apply, star_mul']
    cases i <;> cases j <;> simp [hstar2] <;> linear_combination hmul2 * 2 <|> ring
  have hsp1 : (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) = ((1 - p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hsp2 : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
  have hH_bsc : ∀ b : Bool,
      H * ((bscChannel p hp0 (by linarith)).out b).mat * Hᴴ =
        (match b with
         | false =>
           (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
             ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x)) *
           (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
             ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x))ᴴ
         | true =>
           (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
             ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x)) *
           (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
             ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x))ᴴ) := by
    intro b
    ext ⟨r₁, ⟨⟩⟩ ⟨r₂, ⟨⟩⟩
    cases b <;> cases r₁ <;> cases r₂ <;>
    · simp only [H, A₀, A₁, bscChannel, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.of_apply, Matrix.diagonal_apply, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
        and_self, and_false, false_and, star_mul', star_neg, star_one, hstar2, Complex.star_def,
        Complex.conj_ofReal]
      ring_nf; simp only [sq, hmul2, hsp1, hsp2]; push_cast; ring
  refine ⟨γ, inferInstance, inferInstance, V₁, V₂ * H, h1, ?_, ?_⟩
  · calc (V₂ * H)ᴴ * (V₂ * H) = Hᴴ * (V₂ᴴ * V₂) * H := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hH_iso]
  · intro b
    calc V₁ * ((pureChannel f hf0 hf1).dual.out b).mat * V₁ᴴ
        = V₂ * (match b with
            | false =>
              (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
                ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x)) *
              (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
                ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x))ᴴ
            | true =>
              (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
                ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x)) *
              (Matrix.of fun (r : Bool × PUnit.{1}) (x : Bool) ↦
                ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x))ᴴ) * V₂ᴴ := by
            cases b <;> exact heq _
      _ = V₂ * (H * ((bscChannel p hp0 (by linarith)).out b).mat * Hᴴ) * V₂ᴴ := by rw [hH_bsc b]
      _ = (V₂ * H) * ((bscChannel p hp0 (by linarith)).out b).mat * (V₂ * H)ᴴ := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Proposition 2.2 (D3, Channel-Level Dualities for BSC, Pure-State, and BEC Channels)**:
For every `p ∈ [0, 1/2]` and `ε ∈ [0, 1]`:
1. `BSC(p)⊥ ≃ Pure(1 - 2p)`
2. `Pure(1 - 2p)⊥ ≃ BSC(p)`
3. `BEC(ε)⊥ ≃ BEC(1 - ε)`. -/
theorem prop_2_2_D3_channelEquiv {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (bscChannel p hp0 (by linarith)).dual.ChannelEquiv
      (pureChannel (1 - 2 * p) (by linarith) (by linarith)) ∧
    (pureChannel (1 - 2 * p) (by linarith) (by linarith)).dual.ChannelEquiv
      (bscChannel p hp0 (by linarith)) ∧
    (becChannel ε hε0 hε1).dual.ChannelEquiv
      (becChannel (1 - ε) (by linarith) (by linarith)) := by
  refine ⟨?_, (prop_2_2_D3_isoEquiv_pure hp0 hp1).toChannelEquiv, ?_⟩
  · set f : ℝ := 1 - 2 * p
    have hf0 : 0 ≤ f := by linarith
    have hf1 : f ≤ 1 := by linarith
    have h1pf : (1 + f) / 2 = 1 - p := by simp [f]; ring
    have h1mf : (1 - f) / 2 = p := by simp [f]; ring
    let A₀ : Matrix Bool Bool ℂ :=
      Matrix.diagonal fun k : Bool ↦ if k = false then (Real.sqrt (1 - p) : ℂ) else (Real.sqrt p : ℂ)
    let A₁ : Matrix Bool Bool ℂ :=
      Matrix.diagonal fun k : Bool ↦ if k = false then (Real.sqrt p : ℂ) else (Real.sqrt (1 - p) : ℂ)
    have hsp1 : (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) = ((1 - p : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
    have hsp2 : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
    have hA₀ : A₀ * A₀ᴴ = ((bscChannel p hp0 (by linarith)).out false).mat := by
      ext i j; cases i <;> cases j <;>
        simp [A₀, bscChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, hsp1, hsp2]
    have hA₁ : A₁ * A₁ᴴ = ((bscChannel p hp0 (by linarith)).out true).mat := by
      ext i j; cases i <;> cases j <;>
        simp [A₁, bscChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, hsp1, hsp2]
    have hstep1 := (dual_isoEquiv_of_purification (bscChannel p hp0 (by linarith)) A₀ A₁ hA₀ hA₁).toChannelEquiv
    let U : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
      Matrix.of fun r c ↦
        if r.2 = c.1 ∧ xor r.1 r.2 = c.2 then
          (if c.1 = true ∧ c.2 = true then -1 else 1)
        else 0
    have hU_iso : Uᴴ * U = 1 := by
      ext ⟨c₁, s₁⟩ ⟨c₂, s₂⟩
      simp only [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_prod_type, Fintype.sum_bool, Matrix.one_apply]
      cases c₁ <;> cases s₁ <;> cases c₂ <;> cases s₂ <;> simp
    have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast; ring
    have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
    have hstep2 : CQChannel.IsoEquiv
        ({ out := fun b ↦
            match b with
            | false =>
              { mat :=
                  (Matrix.of fun (r : Bool × Bool) (x : Bool) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x)) *
                  (Matrix.of fun (r : Bool × Bool) (x : Bool) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x))ᴴ
                posSemidef := Matrix.posSemidef_mul_conjTranspose_self _
                trace_one := by
                  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
                    Matrix.of_apply, A₀, A₁, Matrix.diagonal_apply, Fintype.sum_prod_type,
                    Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false, star_mul', hstar2,
                    Complex.star_def, Complex.conj_ofReal]
                  ring_nf; simp only [sq, hmul2, hsp1, hsp2]; ring }
            | true =>
              { mat :=
                  (Matrix.of fun (r : Bool × Bool) (x : Bool) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x)) *
                  (Matrix.of fun (r : Bool × Bool) (x : Bool) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x))ᴴ
                posSemidef := Matrix.posSemidef_mul_conjTranspose_self _
                trace_one := by
                  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
                    Matrix.of_apply, A₀, A₁, Matrix.diagonal_apply, Fintype.sum_prod_type,
                    Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false, star_mul', star_neg, hstar2,
                    Complex.star_def, Complex.conj_ofReal]
                  ring_nf; simp only [sq, hmul2, hsp1, hsp2]; ring } } : CQChannel (Bool × Bool))
        ((pureChannel f hf0 hf1).tensorMaxMixed Bool) := by
      refine ⟨Bool × Bool, inferInstance, inferInstance, 1, U, by simp, hU_iso, ?_⟩
      intro b
      ext ⟨r₁, k₁⟩ ⟨r₂, k₂⟩
      cases b <;> cases r₁ <;> cases k₁ <;> cases r₂ <;> cases k₂ <;>
      · simp only [U, A₀, A₁, CQChannel.tensorMaxMixed, DensityOp.tensor, maxMixedState,
          pureChannel, pureState, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one,
          Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diagonal_apply,
          Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
          Fintype.sum_prod_type, Fintype.sum_bool, h1pf, h1mf, Fintype.card_bool, Nat.cast_ofNat,
          ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, Bool.xor_false, Bool.xor_true,
          and_self, and_false, false_and, star_mul', star_neg, star_one, star_zero, hstar2,
          Complex.star_def, Complex.conj_ofReal, zero_mul, mul_zero, add_zero, zero_add,
          one_mul, mul_one, neg_mul, mul_neg, neg_neg]
        try ring
        try (ring_nf; simp only [sq, hmul2, hsp1, hsp2]; ring)
    exact (hstep1.trans hstep2.toChannelEquiv).trans
      ((pureChannel f hf0 hf1).channelEquiv_tensorMaxMixed Bool).symm
  · let A₀ : Matrix (Fin 3) (Fin 3) ℂ :=
      Matrix.diagonal ![((Real.sqrt (1 - ε) : ℂ)), 0, ((Real.sqrt ε : ℂ))]
    let A₁ : Matrix (Fin 3) (Fin 3) ℂ :=
      Matrix.diagonal ![0, ((Real.sqrt (1 - ε) : ℂ)), ((Real.sqrt ε : ℂ))]
    have hs1 : (Real.sqrt (1 - ε) : ℂ) * (Real.sqrt (1 - ε) : ℂ) = ((1 - ε : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
    have hs2 : (Real.sqrt ε : ℂ) * (Real.sqrt ε : ℂ) = (ε : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hε0]
    have hA₀ : A₀ * A₀ᴴ = ((becChannel ε hε0 hε1).out false).mat := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [A₀, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three, hs1, hs2]
    have hA₁ : A₁ * A₁ᴴ = ((becChannel ε hε0 hε1).out true).mat := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [A₁, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three, hs1, hs2]
    have hstep1 := (dual_isoEquiv_of_purification (becChannel ε hε0 hε1) A₀ A₁ hA₀ hA₁).toChannelEquiv
    have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast; ring
    have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
    let 𝒩 : CPTPMap.{0} (Bool × Fin 3) (Fin 3) :=
      ⟨Bool × Fin 3, inferInstance, inferInstance,
        Matrix.of fun (p : Fin 3 × (Bool × Fin 3)) (q : Bool × Fin 3) ↦
          match q.2 with
          | ⟨0, _⟩ => if p.1 = 2 ∧ p.2 = (q.1, 0) then 1 else 0
          | ⟨1, _⟩ => if p.1 = 2 ∧ p.2 = (q.1, 1) then 1 else 0
          | ⟨2, _⟩ =>
            if p.2 = (false, 2) then
              if p.1 = 0 then ((Real.sqrt 2 : ℂ)⁻¹)
              else if p.1 = 1 then (if q.1 = false then ((Real.sqrt 2 : ℂ)⁻¹) else -((Real.sqrt 2 : ℂ)⁻¹))
              else 0
            else 0, by
        ext ⟨b₁, k₁⟩ ⟨b₂, k₂⟩
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, Matrix.one_apply]
        fin_cases k₁ <;> fin_cases k₂ <;> cases b₁ <;> cases b₂ <;>
          simp [hstar2, hmul2] <;> ring⟩
    let ℳ : CPTPMap.{0} (Fin 3) (Bool × Fin 3) :=
      ⟨Bool, inferInstance, inferInstance,
        Matrix.of fun (p : (Bool × Fin 3) × Bool) (k : Fin 3) ↦
          match k with
          | ⟨0, _⟩ => if p.2 = false ∧ p.1.2 = 2 then ((Real.sqrt 2 : ℂ)⁻¹) else 0
          | ⟨1, _⟩ => if p.2 = false ∧ p.1.2 = 2 then (if p.1.1 = false then ((Real.sqrt 2 : ℂ)⁻¹) else -((Real.sqrt 2 : ℂ)⁻¹)) else 0
          | ⟨2, _⟩ =>
            if (p.2 = false ∧ p.1 = (false, 0)) ∨ (p.2 = true ∧ p.1 = (true, 1)) then ((Real.sqrt 2 : ℂ)⁻¹) else 0, by
        ext k₁ k₂
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, Matrix.one_apply]
        fin_cases k₁ <;> fin_cases k₂ <;>
          simp [hstar2, hmul2] <;> ring⟩
    have hstep2 : CQChannel.ChannelEquiv
        ({ out := fun b ↦
            match b with
            | false =>
              { mat :=
                  (Matrix.of fun (r : Bool × Fin 3) (x : Fin 3) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x)) *
                  (Matrix.of fun (r : Bool × Fin 3) (x : Fin 3) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x))ᴴ
                posSemidef := Matrix.posSemidef_mul_conjTranspose_self _
                trace_one := by
                  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
                    Matrix.of_apply, A₀, A₁, Matrix.diagonal_apply, Fintype.sum_prod_type,
                    Fintype.sum_bool, Fin.sum_univ_three, ↓reduceIte, Bool.true_eq_false,
                    star_mul', hstar2, Complex.star_def, Complex.conj_ofReal]
                  ring_nf; simp only [sq, hmul2, hs1, hs2]; ring }
            | true =>
              { mat :=
                  (Matrix.of fun (r : Bool × Fin 3) (x : Fin 3) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x)) *
                  (Matrix.of fun (r : Bool × Fin 3) (x : Fin 3) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x))ᴴ
                posSemidef := Matrix.posSemidef_mul_conjTranspose_self _
                trace_one := by
                  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
                    Matrix.of_apply, A₀, A₁, Matrix.diagonal_apply, Fintype.sum_prod_type,
                    Fintype.sum_bool, Fin.sum_univ_three, ↓reduceIte, Bool.true_eq_false,
                    star_mul', star_neg, hstar2, Complex.star_def, Complex.conj_ofReal]
                  ring_nf; simp only [sq, hmul2, hs1, hs2]; ring } } : CQChannel (Bool × Fin 3))
        (becChannel (1 - ε) (by linarith) (by linarith)) := by
      refine ⟨𝒩, ℳ, ?_, ?_⟩
      · intro b
        ext i j
        change (partialTrace₂Mat (𝒩.isom * _ * 𝒩.isomᴴ)) i j = ((becChannel (1 - ε) _ _).out b).mat i j
        dsimp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, 𝒩]
        cases b <;> fin_cases i <;> fin_cases j <;>
        · simp only [A₀, A₁, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.of_apply, Matrix.diagonal_apply, Fintype.sum_prod_type, Fintype.sum_bool,
            Fin.sum_univ_three, ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true,
            star_mul', star_neg, star_one, star_zero, hstar2, Complex.star_def, Complex.conj_ofReal,
            zero_mul, mul_zero, add_zero, zero_add, one_mul, mul_one, neg_mul, mul_neg, neg_neg]
          try (push_cast; ring)
          try (ring_nf; simp only [sq, hmul2, hs1, hs2]; push_cast; ring)
      · intro b
        ext ⟨r₁, k₁⟩ ⟨r₂, k₂⟩
        change (partialTrace₂Mat (ℳ.isom * ((becChannel (1 - ε) _ _).out b).mat * ℳ.isomᴴ))
          (r₁, k₁) (r₂, k₂) = _
        dsimp only [partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, ℳ]
        cases b <;> cases r₁ <;> cases r₂ <;> fin_cases k₁ <;> fin_cases k₂ <;>
        · simp only [A₀, A₁, becChannel, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.of_apply, Matrix.diagonal_apply, Fintype.sum_prod_type, Fintype.sum_bool,
            Fin.sum_univ_three, ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true,
            star_mul', star_neg, star_one, star_zero, hstar2, Complex.star_def, Complex.conj_ofReal,
            zero_mul, mul_zero, add_zero, zero_add, one_mul, mul_one, neg_mul, mul_neg, neg_neg]
          try (push_cast; ring)
          try (ring_nf; simp only [sq, hmul2, hs1, hs2]; push_cast; ring)
    exact hstep1.trans hstep2

/-- **Proposition 2.2 (D2, Check-Node Channel-Level Duality)**:
`(W₁ ⊠ W₂)⊥ ≃ W₁⊥ ⊛ W₂⊥` as reversible CPTP-equivalent c-q channels. -/
theorem prop_2_2_D2_check_channelEquiv {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    (W₁.checkCombine W₂).dual.ChannelEquiv (W₁.dual.varCombine W₂.dual) := by
  set ρ₀ := W₁.out false
  set ρ₁ := W₁.out true
  set σ₀ := W₂.out false
  set σ₁ := W₂.out true
  have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
  have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  let A₀ : Matrix (d₁ × d₂) (Bool × d₁ × d₂) ℂ :=
    Matrix.of fun (i₁, i₂) (v, j₁, j₂) ↦
      ((Real.sqrt 2 : ℂ)⁻¹) *
        (if v = false then ρ₀.sqrtMat i₁ j₁ * σ₀.sqrtMat i₂ j₂
         else ρ₁.sqrtMat i₁ j₁ * σ₁.sqrtMat i₂ j₂)
  let A₁ : Matrix (d₁ × d₂) (Bool × d₁ × d₂) ℂ :=
    Matrix.of fun (i₁, i₂) (v, j₁, j₂) ↦
      ((Real.sqrt 2 : ℂ)⁻¹) *
        (if v = false then ρ₁.sqrtMat i₁ j₁ * σ₀.sqrtMat i₂ j₂
         else ρ₀.sqrtMat i₁ j₁ * σ₁.sqrtMat i₂ j₂)
  have hsq_prod : ∀ (τ : DensityOp d₁) (η : DensityOp d₂) (i₁ j₁ : d₁) (i₂ j₂ : d₂),
      ∑ k₁ : d₁, ∑ k₂ : d₂,
        (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * star (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂) =
        τ.mat i₁ j₁ * η.mat i₂ j₂ := by
    intro τ η i₁ j₁ i₂ j₂
    have h1 : ∑ k₁ : d₁, τ.sqrtMat i₁ k₁ * star (τ.sqrtMat j₁ k₁) = τ.mat i₁ j₁ := by
      have hsq := congr_fun (congr_fun τ.sqrtMat_mul_self i₁) j₁
      rw [← hsq]; simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro k _
      have hhk : star (τ.sqrtMat j₁ k) = τ.sqrtMat k j₁ := by
        have := congr_fun (congr_fun τ.sqrtMat_isHermitian.eq k) j₁
        simpa [Matrix.conjTranspose_apply] using this
      rw [hhk]
    have h2 : ∑ k₂ : d₂, η.sqrtMat i₂ k₂ * star (η.sqrtMat j₂ k₂) = η.mat i₂ j₂ := by
      have hsq := congr_fun (congr_fun η.sqrtMat_mul_self i₂) j₂
      rw [← hsq]; simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro k _
      have hhk : star (η.sqrtMat j₂ k) = η.sqrtMat k j₂ := by
        have := congr_fun (congr_fun η.sqrtMat_isHermitian.eq k) j₂
        simpa [Matrix.conjTranspose_apply] using this
      rw [hhk]
    calc ∑ k₁ : d₁, ∑ k₂ : d₂,
          (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * star (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂)
        = (∑ k₁ : d₁, τ.sqrtMat i₁ k₁ * star (τ.sqrtMat j₁ k₁)) *
          (∑ k₂ : d₂, η.sqrtMat i₂ k₂ * star (η.sqrtMat j₂ k₂)) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro k₁ _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k₂ _
            simp only [star_mul']; ring
      _ = τ.mat i₁ j₁ * η.mat i₂ j₂ := by rw [h1, h2]
  have hA₀ : A₀ * A₀ᴴ = ((W₁.checkCombine W₂).out false).mat := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [A₀, CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type,
      Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false, Matrix.add_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, smul_eq_mul, star_mul', hstar2]
    have hl : ∀ (τ : DensityOp d₁) (η : DensityOp d₂),
        ∑ k₁ : d₁, ∑ k₂ : d₂,
          ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
          (star (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂) * (Real.sqrt 2 : ℂ)⁻¹) =
        (1 / 2 : ℂ) * (τ.mat i₁ j₁ * η.mat i₂ j₂) := by
      intro τ η
      rw [← hsq_prod τ η i₁ j₁ i₂ j₂, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k₁ _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k₂ _
      calc ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
            (star (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂) * (Real.sqrt 2 : ℂ)⁻¹)
          = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
            ((τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * star (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂)) := by ring
        _ = _ := by rw [hmul2]
    rw [hl ρ₀ σ₀, hl ρ₁ σ₁]; push_cast; ring
  have hA₁ : A₁ * A₁ᴴ = ((W₁.checkCombine W₂).out true).mat := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [A₁, CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type,
      Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false, Matrix.add_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, smul_eq_mul, star_mul', hstar2]
    have hl : ∀ (τ : DensityOp d₁) (η : DensityOp d₂),
        ∑ k₁ : d₁, ∑ k₂ : d₂,
          ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
          (star (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂) * (Real.sqrt 2 : ℂ)⁻¹) =
        (1 / 2 : ℂ) * (τ.mat i₁ j₁ * η.mat i₂ j₂) := by
      intro τ η
      rw [← hsq_prod τ η i₁ j₁ i₂ j₂, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k₁ _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k₂ _
      calc ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
            (star (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂) * (Real.sqrt 2 : ℂ)⁻¹)
          = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
            ((τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * star (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂)) := by ring
        _ = _ := by rw [hmul2]
    rw [hl ρ₁ σ₀, hl ρ₀ σ₁]; push_cast; ring
  have hstep1 := (dual_isoEquiv_of_purification (W₁.checkCombine W₂) A₀ A₁ hA₀ hA₁).toChannelEquiv
  let W_prod : CQChannel ((Bool × d₁) × (Bool × d₂)) :=
    { out := fun b ↦ DensityOp.tensor (W₁.dual.out b) (W₂.dual.out b) }
  let P : Matrix ((Bool × d₁) × (Bool × d₂)) (Bool × (Bool × d₁ × d₂)) ℂ :=
    Matrix.of fun ((a, r), (c, s)) (u, v, r', s') ↦
      if a = xor u v ∧ c = v ∧ r = r' ∧ s = s' then 1 else 0
  have hP_iso : Pᴴ * P = 1 := by
    ext ⟨u₁, v₁, r₁, s₁⟩ ⟨u₂, v₂, r₂, s₂⟩
    simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
    by_cases h : (u₁, v₁, r₁, s₁) = (u₂, v₂, r₂, s₂)
    · rcases Prod.mk.inj h with ⟨rfl, h'⟩
      rcases Prod.mk.inj h' with ⟨rfl, h''⟩
      rcases Prod.mk.inj h'' with ⟨rfl, rfl⟩
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single (xor u₁ v₁)]
      · rw [Finset.sum_eq_single r₁]
        · rw [Finset.sum_eq_single v₁]
          · rw [Finset.sum_eq_single s₁]
            · simp
            · intro s _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ s₁) h
          · intro c _ hne; apply Finset.sum_eq_zero; intro s _; simp [hne]
          · intro h; exact absurd (Finset.mem_univ v₁) h
        · intro r _ hne; apply Finset.sum_eq_zero; intro c _; apply Finset.sum_eq_zero; intro s _; simp [hne]
        · intro h; exact absurd (Finset.mem_univ r₁) h
      · intro a _ hne; apply Finset.sum_eq_zero; intro r _; apply Finset.sum_eq_zero; intro c _
        apply Finset.sum_eq_zero; intro s _; simp [hne]
      · intro h; exact absurd (Finset.mem_univ (xor u₁ v₁)) h
    · simp only [h, ↓reduceIte]
      apply Finset.sum_eq_zero; intro a _
      apply Finset.sum_eq_zero; intro r _
      apply Finset.sum_eq_zero; intro c _
      apply Finset.sum_eq_zero; intro s _
      by_cases h1 : a = xor u₁ v₁ ∧ c = v₁ ∧ r = r₁ ∧ s = s₁
      · rcases h1 with ⟨rfl, rfl, rfl, rfl⟩
        have h2 : ¬ (xor u₁ c = xor u₂ v₂ ∧ c = v₂ ∧ r = r₂ ∧ s = s₂) := by
          rintro ⟨hxor, rfl, rfl, rfl⟩
          have hu : u₁ = u₂ := by cases u₁ <;> cases u₂ <;> cases c <;> simp_all
          exact h (by rw [hu])
        simp [h2]
      · simp [h1]
  have hstep2a : CQChannel.IsoEquiv
      ({ out := fun b ↦
          match b with
          | false =>
            { mat :=
                (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) *
                (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ
              posSemidef := Matrix.posSemidef_mul_conjTranspose_self _
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hMM : (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ *
                    (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) =
                    (1 / 2 : ℂ) • ((W₁.checkCombine W₂).out false).mat +
                    (1 / 2 : ℂ) • ((W₁.checkCombine W₂).out true).mat := by
                  ext x y
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul', hstar2]
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
                    Finset.mul_sum]
                  rw [Finset.sum_add_distrib]
                  congr 1 <;>
                    (apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro r _;
                     apply Finset.sum_congr rfl; intro s _;
                     simp only [star_star]
                     calc _ = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * _ := by ring
                       _ = _ := by rw [hmul2])
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    ((W₁.checkCombine W₂).out false).trace_one, ((W₁.checkCombine W₂).out true).trace_one]
                simp [smul_eq_mul]; ring }
          | true =>
            { mat :=
                (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) *
                (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ
              posSemidef := Matrix.posSemidef_mul_conjTranspose_self _
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hMM : (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ *
                    (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) =
                    (1 / 2 : ℂ) • ((W₁.checkCombine W₂).out false).mat +
                    (1 / 2 : ℂ) • ((W₁.checkCombine W₂).out true).mat := by
                  ext x y
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, hstar2]
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
                    Finset.mul_sum]
                  rw [Finset.sum_add_distrib]
                  congr 1 <;>
                    (apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro r _;
                     apply Finset.sum_congr rfl; intro s _;
                     simp only [star_star]
                     calc _ = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * _ := by ring
                       _ = _ := by rw [hmul2])
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    ((W₁.checkCombine W₂).out false).trace_one, ((W₁.checkCombine W₂).out true).trace_one]
                simp [smul_eq_mul]; ring } } : CQChannel (Bool × (Bool × d₁ × d₂)))
      W_prod := by
    refine ⟨(Bool × d₁) × (Bool × d₂), inferInstance, inferInstance, P, 1, hP_iso, by simp, ?_⟩
    have hPM : ∀ b : Bool,
        P * (Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x)) =
        Matrix.of fun ((a, r), (c, s)) (i₁, i₂) ↦
          ((if b = false then gramFactor ρ₀ ρ₁ (a, r) i₁
            else ((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) * gramFactor ρ₀ ρ₁) (a, r) i₁) *
           (if b = false then gramFactor σ₀ σ₁ (c, s) i₂
            else ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁) (c, s) i₂)) := by
      intro b
      ext ⟨⟨a, r⟩, ⟨c, s⟩⟩ ⟨i₁, i₂⟩
      simp only [P, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (xor a c)]
      · rw [Finset.sum_eq_single c]
        · rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single s]
            · have hxor : xor (xor a c) c = a := by cases a <;> cases c <;> rfl
              simp only [hxor, and_self, ↓reduceIte, one_mul, A₀, A₁, Matrix.conjTranspose_apply,
                Matrix.of_apply, gramFactor, pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply,
                ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, star_mul', hstar2]
              have hρ₀ : star (ρ₀.sqrtMat i₁ r) = ρ₀.sqrtMat r i₁ := by
                have := congr_fun (congr_fun ρ₀.sqrtMat_isHermitian.eq r) i₁
                simpa [Matrix.conjTranspose_apply] using this
              have hρ₁ : star (ρ₁.sqrtMat i₁ r) = ρ₁.sqrtMat r i₁ := by
                have := congr_fun (congr_fun ρ₁.sqrtMat_isHermitian.eq r) i₁
                simpa [Matrix.conjTranspose_apply] using this
              have hσ₀ : star (σ₀.sqrtMat i₂ s) = σ₀.sqrtMat s i₂ := by
                have := congr_fun (congr_fun σ₀.sqrtMat_isHermitian.eq s) i₂
                simpa [Matrix.conjTranspose_apply] using this
              have hσ₁ : star (σ₁.sqrtMat i₂ s) = σ₁.sqrtMat s i₂ := by
                have := congr_fun (congr_fun σ₁.sqrtMat_isHermitian.eq s) i₂
                simpa [Matrix.conjTranspose_apply] using this
              cases b <;> cases a <;> cases c <;>
                simp [hρ₀, hρ₁, hσ₀, hσ₁] <;> ring
            · intro s' _ hne; simp [Ne.symm hne]
            · intro h; exact absurd (Finset.mem_univ s) h
          · intro r' _ hne; apply Finset.sum_eq_zero; intro s' _; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ r) h
        · intro v _ hne; apply Finset.sum_eq_zero; intro r' _; apply Finset.sum_eq_zero; intro s' _
          simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ c) h
      · intro u _ hne; apply Finset.sum_eq_zero; intro v _; apply Finset.sum_eq_zero; intro r' _
        apply Finset.sum_eq_zero; intro s' _
        by_cases hv : c = v
        · subst hv
          have hne' : ¬ (a = xor u c) := fun h ↦ hne (by rw [h]; cases u <;> cases c <;> rfl)
          simp [hne']
        · simp [hv]
      · intro h; exact absurd (Finset.mem_univ (xor a c)) h
    intro b
    have hfactor_b : (P * Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x)) *
        (P * Matrix.of fun (p : Bool × (Bool × d₁ × d₂)) (x : d₁ × d₂) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ =
        (W_prod.out b).mat := by
      rw [hPM b]
      ext ⟨⟨a₁, r₁⟩, ⟨c₁, s₁⟩⟩ ⟨⟨a₂, r₂⟩, ⟨c₂, s₂⟩⟩
      simp only [W_prod, DensityOp.tensor, CQChannel.dual, gramState, DensityOp.conjUnitary,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.kroneckerMap_apply,
        Fintype.sum_prod_type]
      cases b
      · simp only [↓reduceIte, star_mul']
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i₁ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i₂ _
        ring
      · simp only [Bool.true_eq_false, ↓reduceIte, star_mul']
        have h1 : (((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
            (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) *
            star (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ))) (a₁, r₁) (a₂, r₂) =
            (((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) * gramFactor ρ₀ ρ₁) *
            ((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) * gramFactor ρ₀ ρ₁)ᴴ) (a₁, r₁) (a₂, r₂) := by
          simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        have h2 : (((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) *
            (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) *
            star (pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ))) (c₁, s₁) (c₂, s₂) =
            (((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁) *
            ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁)ᴴ) (c₁, s₁) (c₂, s₂) := by
          simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        rw [h1, h2]
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i₁ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i₂ _
        ring
    cases b <;>
      simpa [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one,
        Matrix.conjTranspose_mul, Matrix.mul_assoc] using hfactor_b
  let U_ctrl : Matrix (Bool × ((Bool × d₁) × (Bool × d₂)))
      (ULift.{u} Bool × ((Bool × d₁) × (Bool × d₂))) ℂ :=
    Matrix.of fun (w, x₁, x₂) (w', y₁, y₂) ↦
      if w = w'.down ∧ x₁ = y₁ ∧ x₂ = y₂ then
        (if w = true ∧ x₁.1 = true then -1 else 1)
      else 0
  have hU_iso : U_ctrlᴴ * U_ctrl = 1 := by
    ext ⟨⟨w₁⟩, x₁, y₁⟩ ⟨⟨w₂⟩, x₂, y₂⟩
    simp only [U_ctrl, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
    by_cases h : (ULift.up w₁, x₁, y₁) = (ULift.up w₂, x₂, y₂)
    · rcases Prod.mk.inj h with ⟨hw, h'⟩
      rcases Prod.mk.inj h' with ⟨rfl, rfl⟩
      have hw' : w₁ = w₂ := congr_arg ULift.down hw
      subst hw'
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single w₁]
      · rw [Finset.sum_eq_single x₁]
        · rw [Finset.sum_eq_single y₁]
          · cases w₁ <;> cases x₁.1 <;> simp
          · intro y _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ y₁) h
        · intro x _ hne; apply Finset.sum_eq_zero; intro y _; simp [hne]
        · intro h; exact absurd (Finset.mem_univ x₁) h
      · intro w _ hne; apply Finset.sum_eq_zero; intro x _; apply Finset.sum_eq_zero; intro y _
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ w₁) h
    · simp only [h, ↓reduceIte]
      apply Finset.sum_eq_zero; intro w _
      apply Finset.sum_eq_zero; intro x _
      apply Finset.sum_eq_zero; intro y _
      by_cases h1 : w = w₁ ∧ x = x₁ ∧ y = y₁
      · rcases h1 with ⟨rfl, rfl, rfl⟩
        have h2 : ¬ (w = w₂ ∧ x = x₂ ∧ y = y₂) := fun ⟨hw, hx, hy⟩ ↦ h (by rw [hw, hx, hy])
        simp [h2]
      · simp [h1]
  have hstep2b : (W_prod.tensorMaxMixed (ULift.{u} Bool)).IsoEquiv (W₁.dual.varCombine W₂.dual) := by
    refine ⟨Bool × ((Bool × d₁) × (Bool × d₂)), inferInstance, inferInstance, U_ctrl, 1, hU_iso, by simp, ?_⟩
    intro b
    ext ⟨w₁, ⟨a₁, r₁⟩, ⟨c₁, s₁⟩⟩ ⟨w₂, ⟨a₂, r₂⟩, ⟨c₂, s₂⟩⟩
    simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, U_ctrl,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (ULift.up w₂)]
    · rw [Finset.sum_eq_single (a₂, r₂)]
      · rw [Finset.sum_eq_single (c₂, s₂)]
        · rw [Finset.sum_eq_single (ULift.up w₁)]
          · rw [Finset.sum_eq_single (a₁, r₁)]
            · rw [Finset.sum_eq_single (c₁, s₁)]
              · simp only [↓reduceIte, and_self, CQChannel.tensorMaxMixed, W_prod,
                  CQChannel.varCombine, DensityOp.tensor, maxMixedState, CQChannel.dual,
                  DensityOp.conjUnitary, pauliZTensorI, Matrix.kroneckerMap_apply,
                  Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul,
                  Fintype.card_ulift, Fintype.card_bool, Nat.cast_ofNat]
                by_cases hw : w₁ = w₂
                · subst hw
                  cases w₁ <;> cases b <;> cases a₁ <;> cases a₂ <;>
                    simp [DensityOp.mix, Matrix.mul_apply, Matrix.diagonal_apply,
                      Matrix.star_apply, ite_mul, zero_mul, mul_ite, mul_zero,
                      Finset.sum_ite_eq, Finset.sum_ite_eq'] <;> ring
                · simp [hw]
                  cases w₁ <;> cases w₂ <;> simp_all [DensityOp.mix, DensityOp.tensor,
                    Matrix.kroneckerMap_apply, Matrix.diagonal_apply]
              · intro z _ hne; simp [Ne.symm hne]
              · intro h; exact absurd (Finset.mem_univ (c₁, s₁)) h
            · intro x _ hne; apply Finset.sum_eq_zero; intro z _; simp [Ne.symm hne]
            · intro h; exact absurd (Finset.mem_univ (a₁, r₁)) h
          · intro w _ hne; apply Finset.sum_eq_zero; intro x _; apply Finset.sum_eq_zero; intro z _
            have hne' : w₁ ≠ w.down := fun h ↦ hne (by cases w; simp_all)
            simp [hne']
          · intro h; exact absurd (Finset.mem_univ (ULift.up w₁)) h
        · intro z _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ (c₂, s₂)) h
      · intro x _ hne; apply Finset.sum_eq_zero; intro z _; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ (a₂, r₂)) h
    · intro w _ hne; apply Finset.sum_eq_zero; intro x _; apply Finset.sum_eq_zero; intro z _
      have hne' : w₂ ≠ w.down := fun h ↦ hne (by cases w; simp_all)
      simp [hne']
    · intro h; exact absurd (Finset.mem_univ (ULift.up w₂)) h
  exact ((hstep1.trans hstep2a.toChannelEquiv).trans
    (W_prod.channelEquiv_tensorMaxMixed (ULift.{u} Bool))).trans hstep2b.toChannelEquiv

/-- **Proposition 2.2 (D2, Variable-Node Channel-Level Duality)**:
`(W₁ ⊛ W₂)⊥ ≃ W₁⊥ ⊠ W₂⊥` as reversible CPTP-equivalent c-q channels. -/
theorem prop_2_2_D2_var_channelEquiv {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    (W₁.varCombine W₂).dual.ChannelEquiv (W₁.dual.checkCombine W₂.dual) := by
  set ρ₀ := W₁.out false
  set ρ₁ := W₁.out true
  set σ₀ := W₂.out false
  set σ₁ := W₂.out true
  have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
  have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  let A₀ : Matrix (Bool × (d₁ × d₂)) (Bool × (d₁ × d₂)) ℂ :=
    Matrix.of fun (v, i₁, i₂) (v', j₁, j₂) ↦
      if v = v' then
        ((Real.sqrt 2 : ℂ)⁻¹) *
          (if v = false then ρ₀.sqrtMat i₁ j₁ * σ₀.sqrtMat i₂ j₂
           else ρ₁.sqrtMat i₁ j₁ * σ₀.sqrtMat i₂ j₂)
      else 0
  let A₁ : Matrix (Bool × (d₁ × d₂)) (Bool × (d₁ × d₂)) ℂ :=
    Matrix.of fun (v, i₁, i₂) (v', j₁, j₂) ↦
      if v = v' then
        ((Real.sqrt 2 : ℂ)⁻¹) *
          (if v = false then ρ₁.sqrtMat i₁ j₁ * σ₁.sqrtMat i₂ j₂
           else ρ₀.sqrtMat i₁ j₁ * σ₁.sqrtMat i₂ j₂)
      else 0
  have hsq_prod : ∀ (τ : DensityOp d₁) (η : DensityOp d₂) (i₁ j₁ : d₁) (i₂ j₂ : d₂),
      ∑ k₁ : d₁, ∑ k₂ : d₂,
        (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * star (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂) =
        τ.mat i₁ j₁ * η.mat i₂ j₂ := by
    intro τ η i₁ j₁ i₂ j₂
    have h1 : ∑ k₁ : d₁, τ.sqrtMat i₁ k₁ * star (τ.sqrtMat j₁ k₁) = τ.mat i₁ j₁ := by
      have hsq := congr_fun (congr_fun τ.sqrtMat_mul_self i₁) j₁
      rw [← hsq]; simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro k _
      have hhk : star (τ.sqrtMat j₁ k) = τ.sqrtMat k j₁ := by
        have := congr_fun (congr_fun τ.sqrtMat_isHermitian.eq k) j₁
        simpa [Matrix.conjTranspose_apply] using this
      rw [hhk]
    have h2 : ∑ k₂ : d₂, η.sqrtMat i₂ k₂ * star (η.sqrtMat j₂ k₂) = η.mat i₂ j₂ := by
      have hsq := congr_fun (congr_fun η.sqrtMat_mul_self i₂) j₂
      rw [← hsq]; simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro k _
      have hhk : star (η.sqrtMat j₂ k) = η.sqrtMat k j₂ := by
        have := congr_fun (congr_fun η.sqrtMat_isHermitian.eq k) j₂
        simpa [Matrix.conjTranspose_apply] using this
      rw [hhk]
    calc ∑ k₁ : d₁, ∑ k₂ : d₂,
          (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * star (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂)
        = (∑ k₁ : d₁, τ.sqrtMat i₁ k₁ * star (τ.sqrtMat j₁ k₁)) *
          (∑ k₂ : d₂, η.sqrtMat i₂ k₂ * star (η.sqrtMat j₂ k₂)) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro k₁ _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k₂ _
            simp only [star_mul']; ring
      _ = τ.mat i₁ j₁ * η.mat i₂ j₂ := by rw [h1, h2]
  have hA₀ : A₀ * A₀ᴴ = ((W₁.varCombine W₂).out false).mat := by
    ext ⟨v₁, i₁, i₂⟩ ⟨v₂, j₁, j₂⟩
    simp only [A₀, CQChannel.varCombine, DensityOp.mix, DensityOp.tensor,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single v₁]
    · by_cases hv : v₁ = v₂
      · subst hv
        have hl : ∀ (τ : DensityOp d₁) (η : DensityOp d₂),
            ∑ k₁ : d₁, ∑ k₂ : d₂,
              ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
              star ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂)) =
            (1 / 2 : ℂ) * (τ.mat i₁ j₁ * η.mat i₂ j₂) := by
          intro τ η
          rw [← hsq_prod τ η i₁ j₁ i₂ j₂, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k₁ _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k₂ _
          simp only [star_mul', hstar2]
          calc _ = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * _ := by ring
            _ = _ := by rw [hmul2]
        cases v₁ <;>
          simp [hl, Matrix.kroneckerMap_apply, Matrix.diagonal_apply] <;> push_cast <;> ring
      · simp [hv, Ne.symm hv, Matrix.kroneckerMap_apply, Matrix.diagonal_apply]
        cases v₁ <;> cases v₂ <;> simp_all
    · intro v _ hne; apply Finset.sum_eq_zero; intro k₁ _; apply Finset.sum_eq_zero; intro k₂ _
      simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ v₁) h
  have hA₁ : A₁ * A₁ᴴ = ((W₁.varCombine W₂).out true).mat := by
    ext ⟨v₁, i₁, i₂⟩ ⟨v₂, j₁, j₂⟩
    simp only [A₁, CQChannel.varCombine, DensityOp.mix, DensityOp.tensor,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single v₁]
    · by_cases hv : v₁ = v₂
      · subst hv
        have hl : ∀ (τ : DensityOp d₁) (η : DensityOp d₂),
            ∑ k₁ : d₁, ∑ k₂ : d₂,
              ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂)) *
              star ((Real.sqrt 2 : ℂ)⁻¹ * (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂)) =
            (1 / 2 : ℂ) * (τ.mat i₁ j₁ * η.mat i₂ j₂) := by
          intro τ η
          rw [← hsq_prod τ η i₁ j₁ i₂ j₂, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k₁ _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k₂ _
          simp only [star_mul', hstar2]
          calc _ = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * _ := by ring
            _ = _ := by rw [hmul2]
        cases v₁ <;>
          simp [hl, Matrix.kroneckerMap_apply, Matrix.diagonal_apply] <;> push_cast <;> ring
      · simp [hv, Ne.symm hv, Matrix.kroneckerMap_apply, Matrix.diagonal_apply]
        cases v₁ <;> cases v₂ <;> simp_all
    · intro v _ hne; apply Finset.sum_eq_zero; intro k₁ _; apply Finset.sum_eq_zero; intro k₂ _
      simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ v₁) h
  have hstep1 := (dual_isoEquiv_of_purification (W₁.varCombine W₂) A₀ A₁ hA₀ hA₁).toChannelEquiv
  let P : Matrix ((Bool × d₁) × (Bool × d₂)) (Bool × (Bool × (d₁ × d₂))) ℂ :=
    Matrix.of fun ((a, r), (c, s)) (u, v, r', s') ↦
      if a = xor u v ∧ c = u ∧ r = r' ∧ s = s' then 1 else 0
  have hP_iso : Pᴴ * P = 1 := by
    ext ⟨u₁, v₁, r₁, s₁⟩ ⟨u₂, v₂, r₂, s₂⟩
    simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.one_apply]
    by_cases h : (u₁, v₁, r₁, s₁) = (u₂, v₂, r₂, s₂)
    · rcases Prod.mk.inj h with ⟨rfl, h'⟩
      rcases Prod.mk.inj h' with ⟨rfl, h''⟩
      rcases Prod.mk.inj h'' with ⟨rfl, rfl⟩
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single (xor u₁ v₁)]
      · rw [Finset.sum_eq_single r₁]
        · rw [Finset.sum_eq_single u₁]
          · rw [Finset.sum_eq_single s₁]
            · simp
            · intro s _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ s₁) h
          · intro c _ hne; apply Finset.sum_eq_zero; intro s _; simp [hne]
          · intro h; exact absurd (Finset.mem_univ u₁) h
        · intro r _ hne; apply Finset.sum_eq_zero; intro c _; apply Finset.sum_eq_zero; intro s _; simp [hne]
        · intro h; exact absurd (Finset.mem_univ r₁) h
      · intro a _ hne; apply Finset.sum_eq_zero; intro r _; apply Finset.sum_eq_zero; intro c _
        apply Finset.sum_eq_zero; intro s _; simp [hne]
      · intro h; exact absurd (Finset.mem_univ (xor u₁ v₁)) h
    · simp only [h, ↓reduceIte]
      apply Finset.sum_eq_zero; intro a _
      apply Finset.sum_eq_zero; intro r _
      apply Finset.sum_eq_zero; intro c _
      apply Finset.sum_eq_zero; intro s _
      by_cases h1 : a = xor u₁ v₁ ∧ c = u₁ ∧ r = r₁ ∧ s = s₁
      · rcases h1 with ⟨rfl, rfl, rfl, rfl⟩
        have h2 : ¬ (xor c v₁ = xor u₂ v₂ ∧ c = u₂ ∧ r = r₂ ∧ s = s₂) := by
          rintro ⟨hxor, rfl, rfl, rfl⟩
          have hv : v₁ = v₂ := by cases c <;> cases v₁ <;> cases v₂ <;> simp_all
          exact h (by rw [hv])
        simp [h2]
      · simp [h1]
  have hstep2 : CQChannel.IsoEquiv
      ({ out := fun b ↦
          match b with
          | false =>
            { mat :=
                (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) *
                (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ
              posSemidef := Matrix.posSemidef_mul_conjTranspose_self _
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hMM : (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ *
                    (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) =
                    (1 / 2 : ℂ) • ((W₁.varCombine W₂).out false).mat +
                    (1 / 2 : ℂ) • ((W₁.varCombine W₂).out true).mat := by
                  ext x y
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul', hstar2]
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
                    Finset.mul_sum]
                  rw [Finset.sum_add_distrib]
                  congr 1 <;>
                    (apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro r _;
                     apply Finset.sum_congr rfl; intro s _;
                     simp only [star_star]
                     calc _ = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * _ := by ring
                       _ = _ := by rw [hmul2])
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    ((W₁.varCombine W₂).out false).trace_one, ((W₁.varCombine W₂).out true).trace_one]
                simp [smul_eq_mul]; ring }
          | true =>
            { mat :=
                (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) *
                (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ
              posSemidef := Matrix.posSemidef_mul_conjTranspose_self _
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hMM : (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ *
                    (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
                    ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) =
                    (1 / 2 : ℂ) • ((W₁.varCombine W₂).out false).mat +
                    (1 / 2 : ℂ) • ((W₁.varCombine W₂).out true).mat := by
                  ext x y
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, hstar2]
                  rw [← hA₀, ← hA₁]
                  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
                    Finset.mul_sum]
                  rw [Finset.sum_add_distrib]
                  congr 1 <;>
                    (apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro r _;
                     apply Finset.sum_congr rfl; intro s _;
                     simp only [star_star]
                     calc _ = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * _ := by ring
                       _ = _ := by rw [hmul2])
                rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    ((W₁.varCombine W₂).out false).trace_one, ((W₁.varCombine W₂).out true).trace_one]
                simp [smul_eq_mul]; ring } } : CQChannel (Bool × (Bool × (d₁ × d₂))))
      (W₁.dual.checkCombine W₂.dual) := by
    refine ⟨(Bool × d₁) × (Bool × d₂), inferInstance, inferInstance, P, 1, hP_iso, by simp, ?_⟩
    have hPM : ∀ b : Bool,
        P * (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x)) =
        Matrix.of fun ((a, r), (c, s)) (v', i₁, i₂) ↦
          if xor a c = v' then
            (if b = false then gramFactor ρ₀ ρ₁ (a, r) i₁ * gramFactor σ₀ σ₁ (c, s) i₂
             else gramFactor ρ₀ ρ₁ (a, r) i₁ *
               ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁) (c, s) i₂)
          else 0 := by
      intro b
      ext ⟨⟨a, r⟩, ⟨c, s⟩⟩ ⟨v', i₁, i₂⟩
      simp only [P, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single c]
      · rw [Finset.sum_eq_single (xor a c)]
        · rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single s]
            · have hxor : xor c (xor a c) = a := by cases a <;> cases c <;> rfl
              simp only [hxor, and_self, ↓reduceIte, one_mul, A₀, A₁, Matrix.conjTranspose_apply,
                Matrix.of_apply, gramFactor, pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply,
                ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
              by_cases hv : xor a c = v'
              · subst hv
                simp only [↓reduceIte, star_mul', hstar2]
                have hρ₀ : star (ρ₀.sqrtMat i₁ r) = ρ₀.sqrtMat r i₁ := by
                  have := congr_fun (congr_fun ρ₀.sqrtMat_isHermitian.eq r) i₁
                  simpa [Matrix.conjTranspose_apply] using this
                have hρ₁ : star (ρ₁.sqrtMat i₁ r) = ρ₁.sqrtMat r i₁ := by
                  have := congr_fun (congr_fun ρ₁.sqrtMat_isHermitian.eq r) i₁
                  simpa [Matrix.conjTranspose_apply] using this
                have hσ₀ : star (σ₀.sqrtMat i₂ s) = σ₀.sqrtMat s i₂ := by
                  have := congr_fun (congr_fun σ₀.sqrtMat_isHermitian.eq s) i₂
                  simpa [Matrix.conjTranspose_apply] using this
                have hσ₁ : star (σ₁.sqrtMat i₂ s) = σ₁.sqrtMat s i₂ := by
                  have := congr_fun (congr_fun σ₁.sqrtMat_isHermitian.eq s) i₂
                  simpa [Matrix.conjTranspose_apply] using this
                cases b <;> cases a <;> cases c <;>
                  simp [hρ₀, hρ₁, hσ₀, hσ₁] <;> ring
              · simp [hv, Ne.symm hv]
                cases c <;> cases b <;> simp [Ne.symm hv]
            · intro s' _ hne; simp [Ne.symm hne]
            · intro h; exact absurd (Finset.mem_univ s) h
          · intro r' _ hne; apply Finset.sum_eq_zero; intro s' _; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ r) h
        · intro v _ hne; apply Finset.sum_eq_zero; intro r' _; apply Finset.sum_eq_zero; intro s' _
          have hne' : ¬ (a = xor c v) := fun h ↦ hne (by rw [h]; cases c <;> cases v <;> rfl)
          simp [hne']
        · intro h; exact absurd (Finset.mem_univ (xor a c)) h
      · intro u _ hne; apply Finset.sum_eq_zero; intro v _; apply Finset.sum_eq_zero; intro r' _
        apply Finset.sum_eq_zero; intro s' _; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ c) h
    intro b
    have hfactor_b : (P * Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x)) *
        (P * Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : Bool × (d₁ × d₂)) ↦
          ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else if b = false then A₁ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ =
        ((W₁.dual.checkCombine W₂.dual).out b).mat := by
      rw [hPM b]
      ext ⟨⟨a₁, r₁⟩, ⟨c₁, s₁⟩⟩ ⟨⟨a₂, r₂⟩, ⟨c₂, s₂⟩⟩
      simp only [CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
        CQChannel.dual, gramState, DensityOp.conjUnitary, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.kroneckerMap_apply, smul_eq_mul, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (xor a₁ c₁)]
      · by_cases hpar : xor a₁ c₁ = xor a₂ c₂
        · simp only [hpar, ↓reduceIte, star_mul']
          have hG1 : ((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
              (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) *
              star (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ)) (a₁, r₁) (a₂, r₂) =
              (if a₁ = a₂ then (1 : ℂ) else -1) * (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) (a₁, r₁) (a₂, r₂) := by
            simp only [pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
              ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
              Finset.mem_univ, ↓reduceIte]
            cases a₁ <;> cases a₂ <;> simp
          have hG2 : ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) *
              (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) *
              star (pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ)) (c₁, s₁) (c₂, s₂) =
              (if c₁ = c₂ then (1 : ℂ) else -1) * (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) (c₁, s₁) (c₂, s₂) := by
            simp only [pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
              ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
              Finset.mem_univ, ↓reduceIte]
            cases c₁ <;> cases c₂ <;> simp
          have hprod : ∑ i₁ : d₁, ∑ i₂ : d₂,
              gramFactor ρ₀ ρ₁ (a₁, r₁) i₁ * gramFactor σ₀ σ₁ (c₁, s₁) i₂ *
              (star (gramFactor σ₀ σ₁ (c₂, s₂) i₂) * star (gramFactor ρ₀ ρ₁ (a₂, r₂) i₁)) =
              (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) (a₁, r₁) (a₂, r₂) *
              (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) (c₁, s₁) (c₂, s₂) := by
            simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
            rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i₁ _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i₂ _; ring
          cases b
          · simp only [↓reduceIte, hG1, hG2]
            rw [hprod]
            cases a₁ <;> cases a₂ <;> cases c₁ <;> cases c₂ <;> simp_all <;> push_cast <;> ring
          · simp only [Bool.true_eq_false, ↓reduceIte, hG1, hG2]
            have hprod' : ∑ i₁ : d₁, ∑ i₂ : d₂,
                gramFactor ρ₀ ρ₁ (a₁, r₁) i₁ *
                ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁) (c₁, s₁) i₂ *
                (star (((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁) (c₂, s₂) i₂) *
                 star (gramFactor ρ₀ ρ₁ (a₂, r₂) i₁)) =
                (if c₁ = c₂ then (1 : ℂ) else -1) *
                ((gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) (a₁, r₁) (a₂, r₂) *
                 (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) (c₁, s₁) (c₂, s₂)) := by
              have hZ2 : ∀ c s i₂, ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) * gramFactor σ₀ σ₁) (c, s) i₂ =
                  (if c = false then (1 : ℂ) else -1) * gramFactor σ₀ σ₁ (c, s) i₂ := by
                intro c s i₂
                simp [pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply]
              simp_rw [hZ2]
              rw [← hprod, Finset.mul_sum]
              apply Finset.sum_congr rfl; intro i₁ _
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i₂ _
              cases c₁ <;> cases c₂ <;> simp <;> ring
            rw [hprod']
            cases a₁ <;> cases a₂ <;> cases c₁ <;> cases c₂ <;> simp_all <;> push_cast <;> ring
        · have hG1 : ((pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ) *
              (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) *
              star (pauliZTensorI d₁ : Matrix (Bool × d₁) (Bool × d₁) ℂ)) (a₁, r₁) (a₂, r₂) =
              (if a₁ = a₂ then (1 : ℂ) else -1) * (gramFactor ρ₀ ρ₁ * (gramFactor ρ₀ ρ₁)ᴴ) (a₁, r₁) (a₂, r₂) := by
            simp only [pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
              ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
              Finset.mem_univ, ↓reduceIte]
            cases a₁ <;> cases a₂ <;> simp
          have hG2 : ((pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ) *
              (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) *
              star (pauliZTensorI d₂ : Matrix (Bool × d₂) (Bool × d₂) ℂ)) (c₁, s₁) (c₂, s₂) =
              (if c₁ = c₂ then (1 : ℂ) else -1) * (gramFactor σ₀ σ₁ * (gramFactor σ₀ σ₁)ᴴ) (c₁, s₁) (c₂, s₂) := by
            simp only [pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
              ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
              Finset.mem_univ, ↓reduceIte]
            cases c₁ <;> cases c₂ <;> simp
          have hne' : ¬ (xor a₂ c₂ = xor a₁ c₁) := fun h ↦ hpar h.symm
          simp only [hne', ↓reduceIte, star_zero, mul_zero, Finset.sum_const_zero]
          cases b <;>
          · simp only [hG1, hG2]
            cases a₁ <;> cases a₂ <;> cases c₁ <;> cases c₂ <;> simp_all <;> push_cast <;> ring
      · intro v _ hne; apply Finset.sum_eq_zero; intro i₁ _; apply Finset.sum_eq_zero; intro i₂ _
        simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ (xor a₁ c₁)) h
    cases b <;>
      simpa [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one,
        Matrix.conjTranspose_mul, Matrix.mul_assoc] using hfactor_b
  exact hstep1.trans hstep2.toChannelEquiv

/-- **Proposition 2.2 (D2, Full Channel-Level Polarization Duality)**:
For all finite-dimensional binary-input c-q channels `W₁, W₂`:
`(W₁ ⊠ W₂)⊥ ≃ W₁⊥ ⊛ W₂⊥` and `(W₁ ⊛ W₂)⊥ ≃ W₁⊥ ⊠ W₂⊥`. -/
theorem prop_2_2_D2_channelEquiv {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    (W₁.checkCombine W₂).dual.ChannelEquiv (W₁.dual.varCombine W₂.dual) ∧
    (W₁.varCombine W₂).dual.ChannelEquiv (W₁.dual.checkCombine W₂.dual) :=
  ⟨prop_2_2_D2_check_channelEquiv W₁ W₂, prop_2_2_D2_var_channelEquiv W₁ W₂⟩

end ChannelEquivalence

end PolarCodes
