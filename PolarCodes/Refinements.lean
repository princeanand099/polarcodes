/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.DephasingSDPI
import PolarCodes.ChannelDuality
import PolarCodes.QuantumChannels

/-!
# Intermediate Refinements: Equal-Support Lemma 3.2, Prop. 3.3 Equality, Relative-Entropy Theorem 1.3, and Channel Equivalence in Prop. 2.2

This module closes the intermediate faithfulness gaps:
1. **Equal-Support Lemma 3.2** (`lemma_3_2_hockeyStick_measure_equalSupport`): factors out the
   support restriction so Lemma 3.2 holds under `suppSubset ρ σ ∧ suppSubset σ ρ`.
2. **Proposition 3.3 Classical Equality** (`prop_3_3_qjjs_classical_equality`): equality in
   Proposition 3.3 for symmetric classical binary pairs `diag((1+x)/2, (1-x)/2)` vs
   `diag((1-x)/2, (1+x)/2)` for all `x ∈ [0, 1]` (including `x = 1` where both sides equal `⊤`).
3. **Relative-Entropy Theorem 1.3** (`suppSubset_dephaseState_half`, `relEntropy_dephaseState_eq`,
   `theorem_1_3_dephasing_sdpi_relEntropy`, `theorem_1_3_equatorial_equality_relEntropy`):
   proves `D(Ψ_p ‖ Ψ_∞) = ENNReal.ofReal (S(Ψ_∞) - S(Ψ_p))` and states Theorem 1.3 directly in
   terms of Umegaki relative entropy.
4. **Channel Equivalence in Proposition 2.2 (D2)–(D3)**: defines `CQChannel.IsoEquiv` (isometric
   equivalence) and `CQChannel.ChannelEquiv` (reversible CPTP equivalence), proving all duality
   identities of Proposition 2.2 (D2)–(D3) at the channel level with entropic equalities as
   immediate corollaries.
-/

open Matrix BigOperators Real Set Filter Topology MeasureTheory
open scoped ComplexOrder ENNReal

namespace PolarCodes

universe u

/-! ### 1. Equal-Support Lemma 3.2 -/

section EqualSupportLemma32

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Isometric conjugation `H = V * H' * Vᴴ` with `Vᴴ * V = 1` preserves `posPartTrace`. -/
private lemma posPartTrace_eq_of_isom {d d' : Type*} [Fintype d] [DecidableEq d]
    [Fintype d'] [DecidableEq d']
    {H : Matrix d d ℂ} {H' : Matrix d' d' ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (V : Matrix d d' ℂ) (hVHV : Vᴴ * V = 1) (hmat : V * H' * Vᴴ = H) :
    posPartTrace hH = posPartTrace hH' := by
  have hle1 : posPartTrace hH ≤ posPartTrace hH' := by
    have hP_psd : (V * posPartMat hH' * Vᴴ).PosSemidef :=
      (posPartMat_posSemidef hH').mul_mul_conjTranspose_same V
    have hdiff_psd : (V * posPartMat hH' * Vᴴ - H).PosSemidef := by
      have heq : V * posPartMat hH' * Vᴴ - H = V * negPartMat hH' * Vᴴ := by
        rw [← hmat, ← Matrix.mul_sub, ← Matrix.sub_mul]
        have hsub := posPartMat_sub_negPartMat hH'
        have : posPartMat hH' - H' = negPartMat hH' := by rw [← hsub]; abel
        rw [this]
      rw [heq]
      exact (negPartMat_posSemidef hH').mul_mul_conjTranspose_same V
    have h1 := posPartTrace_le_trace_of_le hH hP_psd hdiff_psd
    have htr : (V * posPartMat hH' * Vᴴ).trace = (posPartMat hH').trace := by
      rw [Matrix.trace_mul_cycle, hVHV, Matrix.one_mul]
    rw [htr, trace_posPartMat, Complex.ofReal_re] at h1
    exact h1
  have hle2 : posPartTrace hH' ≤ posPartTrace hH := by
    have hH'_eq : Vᴴ * H * V = H' := by
      rw [← hmat]
      calc Vᴴ * (V * H' * Vᴴ) * V = (Vᴴ * V) * H' * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
        _ = H' := by rw [hVHV, Matrix.one_mul, Matrix.mul_one]
    have hP_psd : (Vᴴ * posPartMat hH * V).PosSemidef := by
      simpa [Matrix.conjTranspose_conjTranspose] using
        (posPartMat_posSemidef hH).mul_mul_conjTranspose_same Vᴴ
    have hdiff_psd : (Vᴴ * posPartMat hH * V - H').PosSemidef := by
      have heq : Vᴴ * posPartMat hH * V - H' = Vᴴ * negPartMat hH * V := by
        rw [← hH'_eq, ← Matrix.mul_sub, ← Matrix.sub_mul]
        have hsub := posPartMat_sub_negPartMat hH
        have : posPartMat hH - H = negPartMat hH := by rw [← hsub]; abel
        rw [this]
      rw [heq]
      simpa [Matrix.conjTranspose_conjTranspose] using
        (negPartMat_posSemidef hH).mul_mul_conjTranspose_same Vᴴ
    have h1 := posPartTrace_le_trace_of_le hH' hP_psd hdiff_psd
    set Q : Matrix d d ℂ := 1 - V * Vᴴ
    have hQ_herm : Qᴴ = Q := by
      simp only [Q, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    have hQ_idem : Q * Q = Q := by
      simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      have hVV : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
        calc (V * Vᴴ) * (V * Vᴴ) = V * ((Vᴴ * V) * Vᴴ) := by simp only [Matrix.mul_assoc]
          _ = V * Vᴴ := by rw [hVHV, Matrix.one_mul]
      rw [hVV]; abel
    have hQ_tr_nn : 0 ≤ (Q * posPartMat hH).trace.re := by
      have htr_eq : (Q * posPartMat hH).trace = (Q * posPartMat hH * Qᴴ).trace := by
        rw [hQ_herm, Matrix.trace_mul_cycle, hQ_idem]
      rw [htr_eq]
      have hpsd : (Q * posPartMat hH * Qᴴ).PosSemidef :=
        (posPartMat_posSemidef hH).mul_mul_conjTranspose_same Q
      have hspec : (Q * posPartMat hH * Qᴴ) = (hpsd.isHermitian.eigenvectorUnitary : Matrix d d ℂ) *
          Matrix.diagonal (Complex.ofReal ∘ hpsd.isHermitian.eigenvalues) *
          star (hpsd.isHermitian.eigenvectorUnitary : Matrix d d ℂ) := by
        simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using
          hpsd.isHermitian.spectral_theorem
      conv_rhs => rw [hspec]
      rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self hpsd.isHermitian.eigenvectorUnitary,
        Matrix.one_mul, Matrix.trace_diagonal, Complex.re_sum]
      exact Finset.sum_nonneg fun i _ ↦ by simpa using hpsd.eigenvalues_nonneg i
    have htr_split : (Vᴴ * posPartMat hH * V).trace.re + (Q * posPartMat hH).trace.re =
        posPartTrace hH := by
      have htr1 : (Vᴴ * posPartMat hH * V).trace = ((V * Vᴴ) * posPartMat hH).trace := by
        rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
      rw [htr1, ← Complex.add_re, ← Matrix.trace_add, ← Matrix.add_mul]
      have hsum : V * Vᴴ + Q = 1 := by simp only [Q]; abel
      rw [hsum, Matrix.one_mul, trace_posPartMat, Complex.ofReal_re]
    linarith
  exact le_antisymm hle1 hle2

/-- **Lemma 3.2 (Simultaneous Hockey-Stick Representation under Equal Support)**:
For any finite-dimensional density operators `ρ, σ` with equal support
(`suppSubset ρ σ ∧ suppSubset σ ρ`), there exists a Borel probability measure `μ`
supported on `[a, b] ⊂ (0, ∞)` with `∫ t dμ = 1` simultaneously representing
`E_s(ρ ‖ σ)`, `D(ρ ‖ σ)`, `D(σ ‖ ρ)`, and `QJS(ρ, σ)`. -/
theorem lemma_3_2_hockeyStick_measure_equalSupport {ρ σ : DensityOp d}
    (hsupp : suppSubset ρ σ ∧ suppSubset σ ρ) :
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
  let V : Matrix d d' ℂ := Matrix.of fun r k ↦ U r k.1
  have hVHV : Vᴴ * V = 1 := by
    ext j k
    simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) j.1) k.1
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h
    by_cases hjk : j = k
    · subst hjk; simpa using h
    · have hne : j.1 ≠ k.1 := fun heq ↦ hjk (Subtype.ext heq)
      simpa [hjk, hne] using h
  have hρ_ker : ∀ i : d, i ∉ S_pos → ρ.mat.mulVec (fun r ↦ U r i) = 0 := by
    intro i hi
    have h0 : ρ.eigvals i = 0 := le_antisymm (by simp [S_pos] at hi; exact hi) (ρ.eigvals_nonneg i)
    have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by
      simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
        Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
    have hcol : (star U).mulVec (fun r ↦ U r i) = Pi.single i 1 := by
      ext j; have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) j) i
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
        Pi.single_apply, eq_comm] using h
    conv_lhs => rw [hspec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol]
    have hzero : Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) *ᵥ Pi.single i 1 = 0 := by
      ext j; rw [Matrix.mulVec_diagonal]; by_cases hj : j = i
      · subst hj; simp [h0]
      · simp [Pi.single_eq_of_ne hj]
    rw [hzero, Matrix.mulVec_zero]
  have hσ_ker : ∀ i : d, i ∉ S_pos → σ.mat.mulVec (fun r ↦ U r i) = 0 :=
    fun i hi ↦ suppSubset_ker hsupp.2 (fun r ↦ U r i) (hρ_ker i hi)
  have hρ'_mat : Vᴴ * ρ.mat * V = Matrix.diagonal (fun k : d' ↦ (ρ.eigvals k.1 : ℂ)) := by
    have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by
      simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
        Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
    ext j k
    have hmul : Vᴴ * U = Matrix.of fun (a : d') (b : d) ↦ if a.1 = b then (1 : ℂ) else 0 := by
      ext a b; have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) a.1) b
      simpa [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.star_apply, Matrix.of_apply,
        Matrix.one_apply] using h
    have hmul2 : star U * V = Matrix.of fun (a : d) (b : d') ↦ if a = b.1 then (1 : ℂ) else 0 := by
      ext a b; have h := congr_fun (congr_fun (Unitary.coe_star_mul_self ρ.eigUnitary) a) b.1
      simpa [V, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply] using h
    have hcalc : Vᴴ * ρ.mat * V =
        (Vᴴ * U) * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * (star U * V) := by
      conv_lhs => rw [hspec]; simp only [Matrix.mul_assoc]
    rw [hcalc, hmul, hmul2]
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, Function.comp_apply,
      ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, Finset.sum_ite_eq', Subtype.ext_iff]
    split_ifs <;> simp_all
  let ρ' : DensityOp d' :=
    { mat := Vᴴ * ρ.mat * V
      posSemidef := by
        simpa [Matrix.conjTranspose_conjTranspose] using ρ.posSemidef.mul_mul_conjTranspose_same Vᴴ
      trace_one := by
        rw [hρ'_mat, Matrix.trace_diagonal]
        have htr : ρ.mat.trace = ∑ i : d, (ρ.eigvals i : ℂ) := by
          have hspec : ρ.mat = U * Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star U := by
            simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
              Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
          conv_lhs => rw [hspec]
          rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self ρ.eigUnitary, Matrix.one_mul,
            Matrix.trace_diagonal]; rfl
        rw [← ρ.trace_one, htr, Finset.sum_coe_sort S_pos (fun i ↦ (ρ.eigvals i : ℂ))]
        apply Finset.sum_subset (Finset.subset_univ S_pos)
        intro i _ hi
        simp [le_antisymm (by simp [S_pos] at hi; exact hi) (ρ.eigvals_nonneg i)] }
  have hρ'_pd : ρ'.mat.PosDef := by
    simp only [ρ', hρ'_mat, Matrix.posDef_diagonal_iff]
    intro k; exact_mod_cast (Finset.mem_filter.mp k.2).2
  have hVVH_proj : ∀ (τ : DensityOp d), (∀ i : d, i ∉ S_pos → τ.mat.mulVec (fun r ↦ U r i) = 0) →
      (V * Vᴴ) * τ.mat = τ.mat := by
    intro τ hker
    have hU_eq : ((V * Vᴴ) * τ.mat) * U = τ.mat * U := by
      ext r i
      have hLHS : (((V * Vᴴ) * τ.mat) * U) r i =
          ((V * Vᴴ).mulVec (τ.mat.mulVec (fun x ↦ U x i))) r := by
        change (((V * Vᴴ) * τ.mat) *ᵥ (fun x ↦ U x i)) r = _; rw [← Matrix.mulVec_mulVec]
      have hRHS : (τ.mat * U) r i = (τ.mat.mulVec (fun x ↦ U x i)) r := rfl
      rw [hLHS, hRHS]
      have hVVH_apply : ∀ (v : d → ℂ) (x : d), ((V * Vᴴ).mulVec v) x =
          ∑ k : d', U x k.1 * (∑ y : d, star (U y k.1) * v y) := by
        intro v x
        simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, V, Matrix.conjTranspose_apply,
          Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro y _; ring
      have horth : ∀ j : d, j ∉ S_pos →
          ∑ y : d, star (U y j) * (τ.mat.mulVec (fun x ↦ U x i)) y = 0 := by
        intro j hj
        have hsym : ∑ y : d, star (U y j) * (τ.mat.mulVec (fun x ↦ U x i)) y =
            star (∑ x : d, star (U x i) * (τ.mat.mulVec (fun y ↦ U y j)) x) := by
          simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', star_star, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro y _; apply Finset.sum_congr rfl; intro x _
          have hh := congr_fun (congr_fun τ.isHermitian.eq x) y
          simp only [Matrix.conjTranspose_apply] at hh; rw [hh]; ring
        rw [hsym, hker j hj]; simp
      rw [hVVH_apply]
      have hfull : (τ.mat.mulVec (fun x ↦ U x i)) r =
          ∑ j : d, U r j * (∑ y : d, star (U y j) * (τ.mat.mulVec (fun x ↦ U x i)) y) := by
        set v : d → ℂ := τ.mat.mulVec (fun x ↦ U x i)
        calc v r = ((U * star U).mulVec v) r := by rw [hU_mul, Matrix.one_mulVec]
          _ = _ := by
              simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
                Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro y _; ring
      rw [hfull, Finset.sum_coe_sort S_pos (fun j ↦ U r j * (∑ y : d, star (U y j) * (τ.mat.mulVec (fun x ↦ U x i)) y))]
      apply Finset.sum_subset (Finset.subset_univ S_pos)
      intro j _ hj; rw [horth j hj, mul_zero]
    calc (V * Vᴴ) * τ.mat = ((V * Vᴴ) * τ.mat) * (U * star U) := by rw [hU_mul, Matrix.mul_one]
      _ = ((V * Vᴴ) * τ.mat * U) * star U := by simp only [Matrix.mul_assoc]
      _ = (τ.mat * U) * star U := by rw [hU_eq]
      _ = τ.mat * (U * star U) := by simp only [Matrix.mul_assoc]
      _ = τ.mat := by rw [hU_mul, Matrix.mul_one]
  have hVVH_ρ := hVVH_proj ρ hρ_ker
  have hVVH_σ := hVVH_proj σ hσ_ker
  have hρ_VVH : ρ.mat * (V * Vᴴ) = ρ.mat := by
    have h := congr_arg Matrix.conjTranspose hVVH_ρ
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ρ.isHermitian.eq] using h
  have hσ_VVH : σ.mat * (V * Vᴴ) = σ.mat := by
    have h := congr_arg Matrix.conjTranspose hVVH_σ
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, σ.isHermitian.eq] using h
  let σ' : DensityOp d' :=
    { mat := Vᴴ * σ.mat * V
      posSemidef := by
        simpa [Matrix.conjTranspose_conjTranspose] using σ.posSemidef.mul_mul_conjTranspose_same Vᴴ
      trace_one := by
        calc (Vᴴ * σ.mat * V).trace = ((V * Vᴴ) * σ.mat).trace := by
              rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
          _ = σ.mat.trace := by rw [hVVH_σ]
          _ = 1 := σ.trace_one }
  have hσ'_pd : σ'.mat.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨σ'.isHermitian, fun w hw ↦ ?_⟩
    have hρ_pos : (0 : ℂ) < star (V.mulVec w) ⬝ᵥ ρ.mat.mulVec (V.mulVec w) := by
      have hq : star (V.mulVec w) ⬝ᵥ ρ.mat.mulVec (V.mulVec w) = star w ⬝ᵥ ρ'.mat.mulVec w := by
        calc star (V *ᵥ w) ⬝ᵥ ρ.mat *ᵥ (V *ᵥ w)
            = (star w ᵥ* Vᴴ) ⬝ᵥ (ρ.mat * V) *ᵥ w := by rw [Matrix.star_mulVec, Matrix.mulVec_mulVec]
          _ = star w ⬝ᵥ (Vᴴ * (ρ.mat * V)) *ᵥ w := by
              rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
          _ = star w ⬝ᵥ ρ'.mat *ᵥ w := by simp only [ρ', Matrix.mul_assoc]
      rw [hq]; exact (Matrix.posDef_iff_dotProduct_mulVec.mp hρ'_pd).2 hw
    have hσ_ne : σ.mat.mulVec (V.mulVec w) ≠ 0 := by
      intro h0
      have hρ0 := suppSubset_ker hsupp.1 (V.mulVec w) h0
      rw [hρ0, dotProduct_zero] at hρ_pos; exact lt_irrefl 0 hρ_pos
    have hqσ : star w ⬝ᵥ σ'.mat.mulVec w = star (V.mulVec w) ⬝ᵥ σ.mat.mulVec (V.mulVec w) := by
      symm
      calc star (V *ᵥ w) ⬝ᵥ σ.mat *ᵥ (V *ᵥ w)
          = (star w ᵥ* Vᴴ) ⬝ᵥ (σ.mat * V) *ᵥ w := by rw [Matrix.star_mulVec, Matrix.mulVec_mulVec]
        _ = star w ⬝ᵥ (Vᴴ * (σ.mat * V)) *ᵥ w := by
            rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
        _ = star w ⬝ᵥ σ'.mat *ᵥ w := by simp only [σ', Matrix.mul_assoc]
    rw [hqσ]
    have hnn := (Matrix.posSemidef_iff_dotProduct_mulVec.mp σ.posSemidef).2 (V.mulVec w)
    rcases lt_or_eq_of_le hnn with hlt | heq
    · exact hlt
    · exfalso; apply hσ_ne
      have hre0 := congr_arg Complex.re heq.symm
      rw [re_quadForm_spectral σ.isHermitian (V.mulVec w), Complex.zero_re] at hre0
      have hterm0 : ∀ i : d, σ.isHermitian.eigenvalues i *
          ‖((star (σ.isHermitian.eigenvectorUnitary : Matrix d d ℂ)).mulVec (V.mulVec w)) i‖ ^ 2 = 0 :=
        fun i ↦ (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
          mul_nonneg (σ.posSemidef.eigenvalues_nonneg j) (sq_nonneg _)).mp hre0 i (Finset.mem_univ i)
      have hspec : σ.mat = (σ.isHermitian.eigenvectorUnitary : Matrix d d ℂ) *
          Matrix.diagonal (Complex.ofReal ∘ σ.isHermitian.eigenvalues) *
          star (σ.isHermitian.eigenvectorUnitary : Matrix d d ℂ) := by
        simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using σ.isHermitian.spectral_theorem
      conv_lhs => rw [hspec]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have hzero : Matrix.diagonal (Complex.ofReal ∘ σ.isHermitian.eigenvalues) *ᵥ
          ((star (σ.isHermitian.eigenvectorUnitary : Matrix d d ℂ)).mulVec (V.mulVec w)) = 0 := by
        ext i; rw [Matrix.mulVec_diagonal]
        rcases mul_eq_zero.mp (hterm0 i) with h1 | h2
        · simp [h1]
        · simp [norm_eq_zero.mp (sq_eq_zero_iff.mp h2)]
      rw [hzero, Matrix.mulVec_zero]
  have hVρ'VH : V * ρ'.mat * Vᴴ = ρ.mat := by
    calc V * ρ'.mat * Vᴴ = ((V * Vᴴ) * ρ.mat) * (V * Vᴴ) := by simp only [ρ', Matrix.mul_assoc]
      _ = ρ.mat := by rw [hVVH_ρ, hρ_VVH]
  have hVσ'VH : V * σ'.mat * Vᴴ = σ.mat := by
    calc V * σ'.mat * Vᴴ = ((V * Vᴴ) * σ.mat) * (V * Vᴴ) := by simp only [σ', Matrix.mul_assoc]
      _ = σ.mat := by rw [hVVH_σ, hσ_VVH]
  have hS_iso : ∀ (τ' : DensityOp d') (τ : DensityOp d), V * τ'.mat * Vᴴ = τ.mat →
      vonNeumannEntropy τ = vonNeumannEntropy τ' := by
    intro τ' τ hmat
    unfold vonNeumannEntropy DensityOp.eigvals; congr 1
    let A : Matrix d d' ℂ := V * τ'.sqrtMat
    have hAAH : A * Aᴴ = τ.mat := by
      calc A * Aᴴ = V * (τ'.sqrtMat * τ'.sqrtMat) * Vᴴ := by
            simp only [A, Matrix.conjTranspose_mul, τ'.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
        _ = V * τ'.mat * Vᴴ := by rw [τ'.sqrtMat_mul_self]
        _ = τ.mat := hmat
    have hAHA : Aᴴ * A = τ'.mat := by
      calc Aᴴ * A = τ'.sqrtMat * ((Vᴴ * V) * τ'.sqrtMat) := by
            simp only [A, Matrix.conjTranspose_mul, τ'.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
        _ = τ'.mat := by rw [hVHV, Matrix.one_mul, τ'.sqrtMat_mul_self]
    have hcp := charpoly_mul_conjTranspose_eq A
    rw [hAAH, hAHA] at hcp
    exact spectral_sum_eq_of_charpoly_mul_X_pow τ.isHermitian τ'.isHermitian hcp (by simp [Real.negMulLog])
  have hqjs_eq : qjs ρ σ = qjs ρ' σ' := by
    unfold qjs
    rw [hS_iso ρ' ρ hVρ'VH, hS_iso σ' σ hVσ'VH]
    have hmid : V * (DensityOp.midpoint ρ' σ').mat * Vᴴ = (DensityOp.midpoint ρ σ).mat := by
      simp only [DensityOp.midpoint, DensityOp.mix, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul, hVρ'VH, hVσ'VH]
    rw [hS_iso (DensityOp.midpoint ρ' σ') (DensityOp.midpoint ρ σ) hmid]
  have hD_iso : ∀ (τ₁' τ₂' : DensityOp d') (τ₁ τ₂ : DensityOp d),
      τ₁'.mat.PosDef → τ₂'.mat.PosDef →
      V * τ₁'.mat * Vᴴ = τ₁.mat → V * τ₂'.mat * Vᴴ = τ₂.mat →
      suppSubset τ₁ τ₂ →
      relEntropy τ₁ τ₂ = relEntropy τ₁' τ₂' := by
    intro τ₁' τ₂' τ₁ τ₂ _ h2pd hm1 hm2 hsup
    unfold relEntropy
    have hsup' : suppSubset τ₁' τ₂' := fun _ j _ hj ↦ absurd hj (ne_of_gt (h2pd.eigenvalues_pos j))
    simp only [hsup, hsup', ↓reduceIte]
    congr 1; congr 1
    rw [relEntropy_sum_split τ₁ τ₂, relEntropy_sum_split τ₁' τ₂']
    have hterm1 : (∑ i : d, τ₁.eigvals i * Real.log (τ₁.eigvals i)) =
        ∑ k : d', τ₁'.eigvals k * Real.log (τ₁'.eigvals k) := by
      have hS := hS_iso τ₁' τ₁ hm1
      unfold vonNeumannEntropy Real.negMulLog at hS
      have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
      have hS' : ∑ i : d, -(τ₁.eigvals i * Real.log (τ₁.eigvals i)) =
          ∑ k : d', -(τ₁'.eigvals k * Real.log (τ₁'.eigvals k)) := by
        field_simp [hlog2] at hS; linarith
      simp only [Finset.sum_neg_distrib] at hS'; linarith
    have hterm2 : (∑ i : d, ∑ j : d, τ₁.eigvals i * Real.log (τ₂.eigvals j) *
          ‖((star (τ₂.eigUnitary : Matrix d d ℂ)) * (τ₁.eigUnitary : Matrix d d ℂ)) j i‖ ^ 2) =
        ∑ i : d', ∑ j : d', τ₁'.eigvals i * Real.log (τ₂'.eigvals j) *
          ‖((star (τ₂'.eigUnitary : Matrix d' d' ℂ)) * (τ₁'.eigUnitary : Matrix d' d' ℂ)) j i‖ ^ 2 := by
      let L₂ : Matrix d d ℂ := (τ₂.eigUnitary : Matrix d d ℂ) *
        Matrix.diagonal (fun j ↦ (Real.log (τ₂.eigvals j) : ℂ)) *
        star (τ₂.eigUnitary : Matrix d d ℂ)
      let L₂' : Matrix d' d' ℂ := (τ₂'.eigUnitary : Matrix d' d' ℂ) *
        Matrix.diagonal (fun j ↦ (Real.log (τ₂'.eigvals j) : ℂ)) *
        star (τ₂'.eigUnitary : Matrix d' d' ℂ)
      rw [relEntropy_cross_eq_trace_log τ₁ τ₂, relEntropy_cross_eq_trace_log τ₁' τ₂']
      have hL_eq : V * L₂' * Vᴴ = L₂ := by
        set U₂' : Matrix d' d' ℂ := (τ₂'.eigUnitary : Matrix d' d' ℂ)
        have hU₂'_mul : U₂' * star U₂' = 1 := Unitary.coe_mul_star_self τ₂'.eigUnitary
        have hU₂'_smul : star U₂' * U₂' = 1 := Unitary.coe_star_mul_self τ₂'.eigUnitary
        have hspec2' : τ₂'.mat = U₂' * Matrix.diagonal (Complex.ofReal ∘ τ₂'.eigvals) * star U₂' := by
          simpa [U₂', DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
            Unitary.conjStarAlgAut_apply] using τ₂'.isHermitian.spectral_theorem
        set U₂ : Matrix d d ℂ := (τ₂.eigUnitary : Matrix d d ℂ)
        have hU₂_mul : U₂ * star U₂ = 1 := Unitary.coe_mul_star_self τ₂.eigUnitary
        have hspec2 : τ₂.mat = U₂ * Matrix.diagonal (Complex.ofReal ∘ τ₂.eigvals) * star U₂ := by
          simpa [U₂, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
            Unitary.conjStarAlgAut_apply] using τ₂.isHermitian.spectral_theorem
        have hcol_eq : ∀ j : d, (V * L₂' * Vᴴ).mulVec (fun r ↦ U₂ r j) =
            L₂.mulVec (fun r ↦ U₂ r j) := by
          intro j
          have hcol : (star U₂).mulVec (fun r ↦ U₂ r j) = Pi.single j 1 := by
            ext k; have h := congr_fun (congr_fun (Unitary.coe_star_mul_self τ₂.eigUnitary) k) j
            simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply,
              Matrix.one_apply, Pi.single_apply, eq_comm] using h
          have hR : L₂.mulVec (fun r ↦ U₂ r j) =
              (Real.log (τ₂.eigvals j) : ℂ) • (fun r ↦ U₂ r j) := by
            change (U₂ * Matrix.diagonal (fun j ↦ (Real.log (τ₂.eigvals j) : ℂ)) * star U₂) *ᵥ (fun r ↦ U₂ r j) = _
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol]
            ext r; simp [Matrix.mulVec, dotProduct, Matrix.mulVec_diagonal, Matrix.diagonal_apply, Pi.single_apply, mul_comm]
          rw [hR]
          have hτ2_eig : τ₂.mat.mulVec (fun r ↦ U₂ r j) =
              (τ₂.eigvals j : ℂ) • (fun r ↦ U₂ r j) := by
            conv_lhs => rw [hspec2]
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol]
            ext r; simp [Matrix.mulVec, dotProduct, Matrix.mulVec_diagonal, Matrix.diagonal_apply, Pi.single_apply, mul_comm]
          by_cases hj0 : τ₂.eigvals j = 0
          · rw [hj0, Real.log_zero, Complex.ofReal_zero, zero_smul]
            have hVh0 : Vᴴ.mulVec (fun r ↦ U₂ r j) = 0 := by
              have h0 : (V * τ₂'.mat * Vᴴ).mulVec (fun r ↦ U₂ r j) = 0 := by
                rw [hm2, hτ2_eig, hj0, Complex.ofReal_zero, zero_smul]
              have h1 := congr_arg Vᴴ.mulVec h0
              rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc Vᴴ, ← Matrix.mul_assoc Vᴴ,
                hVHV, Matrix.one_mul, Matrix.mulVec_zero, ← Matrix.mulVec_mulVec] at h1
              by_contra hne
              have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp h2pd).2 hne
              rw [h1, dotProduct_zero] at hp; exact lt_irrefl 0 hp
            rw [← Matrix.mulVec_mulVec, hVh0, Matrix.mulVec_zero]
          · set w : d' → ℂ := Vᴴ.mulVec (fun r ↦ U₂ r j)
            have hVw : V.mulVec w = fun r ↦ U₂ r j := by
              have h1 : (V * Vᴴ).mulVec (τ₂.mat.mulVec (fun r ↦ U₂ r j)) =
                  τ₂.mat.mulVec (fun r ↦ U₂ r j) := by
                rw [Matrix.mulVec_mulVec, ← hm2]
                have hproj : (V * Vᴴ) * (V * τ₂'.mat * Vᴴ) = V * τ₂'.mat * Vᴴ := by
                  calc (V * Vᴴ) * (V * τ₂'.mat * Vᴴ)
                      = V * ((Vᴴ * V) * τ₂'.mat) * Vᴴ := by simp only [Matrix.mul_assoc]
                    _ = V * τ₂'.mat * Vᴴ := by rw [hVHV, Matrix.one_mul]
                rw [hproj]
              rw [hτ2_eig, Matrix.mulVec_smul] at h1
              have hneC : (τ₂.eigvals j : ℂ) ≠ 0 := by exact_mod_cast hj0
              have := congr_arg (fun v : d → ℂ ↦ (τ₂.eigvals j : ℂ)⁻¹ • v) h1
              simp only [smul_smul, inv_mul_cancel₀ hneC, one_smul] at this
              simpa [w, Matrix.mulVec_mulVec] using this
            have hτ2'_w : τ₂'.mat.mulVec w = (τ₂.eigvals j : ℂ) • w := by
              have h1 := congr_arg Vᴴ.mulVec hτ2_eig
              rw [← hm2, Matrix.mulVec_mulVec, ← Matrix.mul_assoc Vᴴ, ← Matrix.mul_assoc Vᴴ,
                hVHV, Matrix.one_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h1
              exact h1
            set y : d' → ℂ := (star U₂').mulVec w
            have hy_coord : ∀ k : d', τ₂'.eigvals k ≠ τ₂.eigvals j → y k = 0 := by
              intro k hk
              have h1 := congr_arg (fun v ↦ ((star U₂').mulVec v) k) hτ2'_w
              have hL : ((star U₂').mulVec (τ₂'.mat.mulVec w)) k = (τ₂'.eigvals k : ℂ) * y k := by
                conv_lhs => rw [hspec2']
                rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc (star U₂'), ← Matrix.mul_assoc (star U₂'),
                  hU₂'_smul, Matrix.one_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]; rfl
              rw [hL, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h1
              have hsub : ((τ₂'.eigvals k : ℂ) - (τ₂.eigvals j : ℂ)) * y k = 0 := by linear_combination h1
              have hneC : (τ₂'.eigvals k : ℂ) - (τ₂.eigvals j : ℂ) ≠ 0 := by
                rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.mpr hk
              exact (mul_eq_zero.mp hsub).resolve_left hneC
            have hL2'_w : L₂'.mulVec w = (Real.log (τ₂.eigvals j) : ℂ) • w := by
              change (U₂' * Matrix.diagonal (fun k ↦ (Real.log (τ₂'.eigvals k) : ℂ)) * star U₂') *ᵥ w = _
              rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
              have hdiag : Matrix.diagonal (fun k ↦ (Real.log (τ₂'.eigvals k) : ℂ)) *ᵥ y =
                  (Real.log (τ₂.eigvals j) : ℂ) • y := by
                ext k; rw [Matrix.mulVec_diagonal]; simp only [Pi.smul_apply, smul_eq_mul]
                by_cases hk : τ₂'.eigvals k = τ₂.eigvals j
                · rw [hk]
                · rw [hy_coord k hk, mul_zero, mul_zero]
              rw [hdiag, Matrix.mulVec_smul, show U₂'.mulVec y = w by
                simp only [y, Matrix.mulVec_mulVec, hU₂'_mul, Matrix.one_mulVec]]
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hL2'_w, Matrix.mulVec_smul, hVw]
        have hmulU : (V * L₂' * Vᴴ) * U₂ = L₂ * U₂ := by ext r j; exact congr_fun (hcol_eq j) r
        calc V * L₂' * Vᴴ = (V * L₂' * Vᴴ) * (U₂ * star U₂) := by rw [hU₂_mul, Matrix.mul_one]
          _ = ((V * L₂' * Vᴴ) * U₂) * star U₂ := by simp only [Matrix.mul_assoc]
          _ = (L₂ * U₂) * star U₂ := by rw [hmulU]
          _ = L₂ * (U₂ * star U₂) := by simp only [Matrix.mul_assoc]
          _ = L₂ := by rw [hU₂_mul, Matrix.mul_one]
      change (τ₁.mat * L₂).trace.re = (τ₁'.mat * L₂').trace.re
      rw [← hL_eq, ← hm1]; congr 1
      calc (V * τ₁'.mat * Vᴴ * (V * L₂' * Vᴴ)).trace
          = (V * τ₁'.mat * ((Vᴴ * V) * L₂') * Vᴴ).trace := by simp only [Matrix.mul_assoc]
        _ = (V * (τ₁'.mat * L₂') * Vᴴ).trace := by rw [hVHV, Matrix.one_mul]; simp only [Matrix.mul_assoc]
        _ = (τ₁'.mat * L₂').trace := by rw [Matrix.trace_mul_cycle, hVHV, Matrix.one_mul]
    linarith
  have hhockey_eq : ∀ s : ℝ, hockeyStick s ρ σ = hockeyStick s ρ' σ' := by
    intro s
    unfold hockeyStick
    refine posPartTrace_eq_of_isom _ _ V hVHV ?_
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hVρ'VH, hVσ'VH]
  obtain ⟨a, b, μ, ha, hab, hprob, hsuppμ, hE, hmean, hD1, hD2, hQJS⟩ :=
    lemma_3_2_hockeyStick_measure hρ'_pd hσ'_pd
  refine ⟨a, b, μ, ha, hab, hprob, hsuppμ, ?_, hmean, ?_, ?_, ?_⟩
  · intro s; rw [hhockey_eq s, hE s]
  · rw [hD_iso ρ' σ' ρ σ hρ'_pd hσ'_pd hVρ'VH hVσ'VH hsupp.1, hD1]
  · rw [hD_iso σ' ρ' σ ρ hσ'_pd hρ'_pd hVσ'VH hVρ'VH hsupp.2, hD2]
  · rw [hqjs_eq, hQJS]

end EqualSupportLemma32

/-! ### 2. Proposition 3.3 Classical Equality Case -/

section Prop33ClassicalEquality

/-- Symmetric classical binary density operator `diag((1+x)/2, (1-x)/2)` for `x ∈ [0, 1]`. -/
def symClassicalPair0 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : DensityOp Bool where
  mat := Matrix.diagonal (fun b : Bool ↦ if b = false then (((1 + x) / 2 : ℝ) : ℂ) else (((1 - x) / 2 : ℝ) : ℂ))
  posSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro b; cases b <;> simp only [↓reduceIte, Bool.true_eq_false] <;> exact_mod_cast (by linarith : (0 : ℝ) ≤ _)
  trace_one := by
    simp only [Matrix.trace_diagonal, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false]
    push_cast; ring

/-- Symmetric classical binary density operator `diag((1-x)/2, (1+x)/2)` for `x ∈ [0, 1]`. -/
def symClassicalPair1 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : DensityOp Bool where
  mat := Matrix.diagonal (fun b : Bool ↦ if b = false then (((1 - x) / 2 : ℝ) : ℂ) else (((1 + x) / 2 : ℝ) : ℂ))
  posSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro b; cases b <;> simp only [↓reduceIte, Bool.true_eq_false] <;> exact_mod_cast (by linarith : (0 : ℝ) ≤ _)
  trace_one := by
    simp only [Matrix.trace_diagonal, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false]
    push_cast; ring

/-- **Proposition 3.3 (Equality Case)**: Every symmetric classical binary pair
`ρ = diag((1+x)/2, (1-x)/2)`, `σ = diag((1-x)/2, (1+x)/2)` (`x ∈ [0, 1]`) attains exact equality
in Proposition 3.3, including at `x = 1` where both sides equal `⊤ : ℝ≥0∞`. -/
theorem prop_3_3_qjjs_classical_equality {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    phiExt (qjs (symClassicalPair0 x hx0 hx1) (symClassicalPair1 x hx0 hx1)) =
      (1 / 4 : ℝ≥0∞) *
        (relEntropy (symClassicalPair0 x hx0 hx1) (symClassicalPair1 x hx0 hx1) +
         relEntropy (symClassicalPair1 x hx0 hx1) (symClassicalPair0 x hx0 hx1)) := by
  set ρ := symClassicalPair0 x hx0 hx1
  set σ := symClassicalPair1 x hx0 hx1
  set p : ℝ := (1 - x) / 2
  have hp0 : 0 ≤ p := by dsimp only [p]; linarith
  have hp1 : p ≤ 1 / 2 := by dsimp only [p]; linarith
  have hρ_bsc : ρ.mat = (bscChannel p hp0 (by linarith)).out false |>.mat := by
    ext i j; simp only [ρ, symClassicalPair0, bscChannel, Matrix.diagonal_apply, p]
    split_ifs <;> try rfl
    push_cast; ring
  have hσ_bsc : σ.mat = (bscChannel p hp0 (by linarith)).out true |>.mat := by
    ext i j; simp only [σ, symClassicalPair1, bscChannel, Matrix.diagonal_apply, p]
    split_ifs <;> try rfl
    push_cast; ring
  have hqjs_val : qjs ρ σ = 1 - h2 p := by
    have hmid : (DensityOp.midpoint ρ σ).mat =
        (DensityOp.midpoint ((bscChannel p hp0 (by linarith)).out false)
          ((bscChannel p hp0 (by linarith)).out true)).mat := by
      simp only [DensityOp.midpoint, DensityOp.mix, hρ_bsc, hσ_bsc]
    have h1 : qjs ρ σ = qjs ((bscChannel p hp0 (by linarith)).out false)
        ((bscChannel p hp0 (by linarith)).out true) := by
      unfold qjs
      rw [vonNeumannEntropy_eq_of_mat_eq hmid, vonNeumannEntropy_eq_of_mat_eq hρ_bsc,
        vonNeumannEntropy_eq_of_mat_eq hσ_bsc]
    rw [h1]
    have hcond := condEntropy_bscChannel p hp0 (by linarith)
    unfold CQChannel.condEntropy at hcond
    linarith
  rcases eq_or_lt_of_le hx1 with rfl | hx_lt1
  · -- Case `x = 1`: `p = 0`, `qjs = 1`, `phiExt 1 = ⊤`, and `¬ suppSubset ρ σ` gives `D(ρ ‖ σ) = ⊤`
    have hp_zero : p = 0 := by simp [p]
    rw [hqjs_val, hp_zero, h2_zero, sub_zero]
    unfold phiExt
    simp only [lt_irrefl, ↓reduceIte]
    have hnsupp : ¬ suppSubset ρ σ := by
      intro hs
      have hker := suppSubset_ker hs (Pi.single false 1) (by
        ext b; cases b <;> simp [σ, symClassicalPair1, Matrix.mulVec_diagonal, Pi.single_apply])
      have h0 := congr_fun hker false
      simp [ρ, symClassicalPair0, Matrix.mulVec_diagonal, Pi.single_apply] at h0
    have htop : relEntropy ρ σ = ⊤ := by unfold relEntropy; rw [if_neg hnsupp]
    rw [htop, top_add, ENNReal.mul_top (by norm_num : (1 / 4 : ℝ≥0∞) ≠ 0)]
  · -- Case `x < 1`: both `ρ, σ` are strictly `PosDef`, compute closed form directly
    have hp_pos : 0 < p := by dsimp only [p]; linarith
    have h1mp_pos : 0 < 1 - p := by linarith
    have hq_lt1 : qjs ρ σ < 1 := by
      rw [hqjs_val]
      have h2pos : 0 < h2 p := by
        rw [h2_eq_negMulLog]
        apply div_pos _ (Real.log_pos (by norm_num))
        have h1 : 0 < Real.negMulLog p := by
          unfold Real.negMulLog; nlinarith [Real.log_neg hp_pos (by linarith : p < 1)]
        have h2' : 0 < Real.negMulLog (1 - p) := by
          unfold Real.negMulLog; nlinarith [Real.log_neg h1mp_pos (by linarith : 1 - p < 1)]
        linarith
      linarith
    have hrel_diag : ∀ (a b : Bool → ℝ) (A B : DensityOp Bool),
        (∀ i, 0 < a i) → (∀ i, 0 < b i) →
        A.mat = Matrix.diagonal (Complex.ofReal ∘ a) →
        B.mat = Matrix.diagonal (Complex.ofReal ∘ b) →
        relEntropy A B = ENNReal.ofReal ((∑ i : Bool, a i * (Real.log (a i) - Real.log (b i))) / Real.log 2) := by
      intro a b A B ha hb hA hB
      have hB_pd : B.mat.PosDef := by
        rw [hB, Matrix.posDef_diagonal_iff]; intro i; exact_mod_cast hb i
      have hsup : suppSubset A B := fun _ j _ hj ↦ absurd hj (ne_of_gt (hB_pd.eigenvalues_pos j))
      unfold relEntropy; rw [if_pos hsup]; congr 1; congr 1
      rw [relEntropy_sum_split A B]
      have h1 : (∑ i : Bool, A.eigvals i * Real.log (A.eigvals i)) = ∑ i : Bool, a i * Real.log (a i) := by
        have hDA : (Matrix.diagonal (Complex.ofReal ∘ a)).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext i; simp
        have hS := spectral_sum_eq_of_charpoly_mul_X_pow A.isHermitian hDA (k := 0) (l := 0)
          (by rw [pow_zero, mul_one, mul_one, hA]) (f := fun t ↦ t * Real.log t) (by simp)
        rw [spectral_sum_diagonal a hDA (f := fun t ↦ t * Real.log t) (by simp)] at hS
        exact hS
      have h2 : (∑ i : Bool, ∑ j : Bool, A.eigvals i * Real.log (B.eigvals j) *
            ‖(star (B.eigUnitary : Matrix Bool Bool ℂ) * (A.eigUnitary : Matrix Bool Bool ℂ)) j i‖ ^ 2) =
          ∑ i : Bool, a i * Real.log (b i) := by
        rw [relEntropy_cross_eq_trace_log A B]
        have hlogB : (B.eigUnitary : Matrix Bool Bool ℂ) *
            Matrix.diagonal (fun j ↦ (Real.log (B.eigvals j) : ℂ)) *
            star (B.eigUnitary : Matrix Bool Bool ℂ) =
            Matrix.diagonal (fun j ↦ (Real.log (b j) : ℂ)) := by
          have h1U : (1 : Matrix.unitaryGroup Bool ℂ) = 1 := rfl
          have hsp : B.mat = ((1 : Matrix.unitaryGroup Bool ℂ) : Matrix Bool Bool ℂ) *
              Matrix.diagonal (Complex.ofReal ∘ b) * star ((1 : Matrix.unitaryGroup Bool ℂ) : Matrix Bool Bool ℂ) := by
            simp [hB]
          have hfn := hermitian_func_eq B.isHermitian (1 : Matrix.unitaryGroup Bool ℂ) b hsp Real.log
          simpa [DensityOp.eigUnitary, DensityOp.eigvals] using hfn
        rw [hlogB, hA]
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
          Function.comp_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, ↓reduceIte, Complex.re_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [← Complex.ofReal_mul, Complex.ofReal_re]
      rw [h1, h2, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    have hD1 : relEntropy ρ σ = ENNReal.ofReal (x * Real.logb 2 ((1 + x) / (1 - x))) := by
      rw [hrel_diag (fun b ↦ if b = false then (1 + x) / 2 else (1 - x) / 2)
        (fun b ↦ if b = false then (1 - x) / 2 else (1 + x) / 2) ρ σ
        (fun b ↦ by cases b <;> simp <;> linarith) (fun b ↦ by cases b <;> simp <;> linarith)
        (by ext i j; simp only [ρ, symClassicalPair0, Matrix.diagonal_apply, Function.comp_apply]; split_ifs <;> rfl)
        (by ext i j; simp only [σ, symClassicalPair1, Matrix.diagonal_apply, Function.comp_apply]; split_ifs <;> rfl)]
      congr 1
      rw [Fintype.sum_bool]
      simp only [Bool.true_eq_false, ↓reduceIte]
      rw [Real.logb, Real.log_div (by linarith) (by linarith),
        Real.log_div (by linarith) (by norm_num : (2 : ℝ) ≠ 0),
        Real.log_div (by linarith) (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    have hD2 : relEntropy σ ρ = ENNReal.ofReal (x * Real.logb 2 ((1 + x) / (1 - x))) := by
      rw [hrel_diag (fun b ↦ if b = false then (1 - x) / 2 else (1 + x) / 2)
        (fun b ↦ if b = false then (1 + x) / 2 else (1 - x) / 2) σ ρ
        (fun b ↦ by cases b <;> simp <;> linarith) (fun b ↦ by cases b <;> simp <;> linarith)
        (by ext i j; simp only [σ, symClassicalPair1, Matrix.diagonal_apply, Function.comp_apply]; split_ifs <;> rfl)
        (by ext i j; simp only [ρ, symClassicalPair0, Matrix.diagonal_apply, Function.comp_apply]; split_ifs <;> rfl)]
      congr 1
      rw [Fintype.sum_bool]
      simp only [Bool.true_eq_false, ↓reduceIte]
      rw [Real.logb, Real.log_div (by linarith) (by linarith),
        Real.log_div (by linarith) (by norm_num : (2 : ℝ) ≠ 0),
        Real.log_div (by linarith) (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    have hnn : 0 ≤ x * Real.logb 2 ((1 + x) / (1 - x)) :=
      mul_nonneg hx0 (Real.logb_nonneg (by norm_num) ((one_le_div (by linarith)).mpr (by linarith)))
    unfold phiExt
    rw [if_pos hq_lt1, hqjs_val, hD1, hD2]
    have hphi_val : phi (1 - h2 p) = (1 / 2) * (x * Real.logb 2 ((1 + x) / (1 - x))) := by
      unfold phi
      rw [sub_sub_cancel, h2Inv_h2 ⟨hp0, hp1⟩]
      have h1 : 1 - 2 * p = x := by dsimp only [p]; ring
      have h2' : (1 - p) / p = (1 + x) / (1 - x) := by
        dsimp only [p]; field_simp; ring
      rw [h1, h2']; ring
    rw [hphi_val, ← ENNReal.ofReal_add hnn hnn,
      show (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) by
        rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
          ENNReal.ofReal_ofNat, one_div],
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring

end Prop33ClassicalEquality

/-! ### 3. Relative-Entropy Definition of `C(p)` in Theorem 1.3 -/

section RelEntropyTheorem13

variable {d : Type u} [Fintype d] [DecidableEq d]

/-- CPTP map associated to unitary conjugation `ρ ↦ U ρ Uᴴ`. -/
def CPTPMap.ofUnitary (U : Matrix.unitaryGroup d ℂ) : CPTPMap d d where
  env := PUnit
  fintypeEnv := inferInstance
  decEqEnv := inferInstance
  isom := Matrix.of fun p j ↦ (U : Matrix d d ℂ) p.1 j
  isom_eq := by
    ext i j
    have h := congr_fun (congr_fun (Unitary.coe_star_mul_self U) i) j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.star_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Fintype.sum_unique] using h

lemma CPTPMap.ofUnitary_apply (U : Matrix.unitaryGroup d ℂ) (ρ : DensityOp d) :
    ((CPTPMap.ofUnitary U).apply ρ).mat = (DensityOp.conjUnitary U ρ).mat := by
  ext i j
  simp only [CPTPMap.apply, CPTPMap.toLinearMap, CPTPMap.ofUnitary, DensityOp.conjUnitary,
    partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.star_apply, Fintype.sum_unique]

/-- Unitary invariance of Umegaki relative entropy: `D(U ρ Uᴴ ‖ U σ Uᴴ) = D(ρ ‖ σ)`. -/
theorem relEntropy_conjUnitary (U : Matrix.unitaryGroup d ℂ) (ρ σ : DensityOp d) :
    relEntropy (DensityOp.conjUnitary U ρ) (DensityOp.conjUnitary U σ) = relEntropy ρ σ := by
  have hext : ∀ (X Y : DensityOp d), X.mat = Y.mat → X = Y := by
    intro ⟨_, _, _⟩ ⟨_, _, _⟩ h; cases h; rfl
  have hle1 : relEntropy (DensityOp.conjUnitary U ρ) (DensityOp.conjUnitary U σ) ≤ relEntropy ρ σ := by
    have h1 := relEntropy_cptp_le (CPTPMap.ofUnitary U) ρ σ
    rwa [hext _ _ (CPTPMap.ofUnitary_apply U ρ), hext _ _ (CPTPMap.ofUnitary_apply U σ)] at h1
  have hle2 : relEntropy ρ σ ≤ relEntropy (DensityOp.conjUnitary U ρ) (DensityOp.conjUnitary U σ) := by
    have h1 := relEntropy_cptp_le (CPTPMap.ofUnitary (star U))
      (DensityOp.conjUnitary U ρ) (DensityOp.conjUnitary U σ)
    have hback : ∀ τ : DensityOp d,
        (CPTPMap.ofUnitary (star U)).apply (DensityOp.conjUnitary U τ) = τ := by
      intro τ; apply hext
      rw [CPTPMap.ofUnitary_apply]
      change star (U : Matrix d d ℂ) * ((U : Matrix d d ℂ) * τ.mat * star (U : Matrix d d ℂ)) *
        star (star (U : Matrix d d ℂ)) = τ.mat
      rw [star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Unitary.coe_star_mul_self U,
        Matrix.one_mul, Matrix.mul_assoc, Unitary.coe_star_mul_self U, Matrix.mul_one]
    rwa [hback ρ, hback σ] at h1
  exact le_antisymm hle1 hle2

/-- Support inclusion `supp((Z_p ⊗ id)(Ψ)) ⊆ supp((Z_{1/2} ⊗ id)(Ψ))` for all `p ∈ [0, 1]`. -/
theorem suppSubset_dephaseState_half (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) :
    suppSubset (dephaseState p hp0 hp1 Ψ) (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) := by
  set A := dephaseState p hp0 hp1 Ψ
  set B := DensityOp.conjUnitary (pauliZTensorI d) A
  set M := dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ
  have hM_mid : M.mat = (DensityOp.midpoint A B).mat := by
    ext ⟨b₁, i⟩ ⟨b₂, j⟩
    have h1 := dephaseState_apply (1 / 2) (by norm_num) (by norm_num) A b₁ b₂ i j
    have h2 := dephaseState_apply (1 / 2) (by norm_num) (by norm_num) Ψ b₁ b₂ i j
    have h3 := dephaseState_apply p hp0 hp1 Ψ b₁ b₂ i j
    change M.mat (b₁, i) (b₂, j) = (dephaseState (1 / 2) (by norm_num) (by norm_num) A).mat (b₁, i) (b₂, j)
    rw [h1, h2, h3]; cases b₁ <;> cases b₂ <;> norm_num
  intro i j hAi hMj
  set v : Bool × d → ℂ := fun r ↦ (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) r j
  have hker : M.mat.mulVec v = 0 := by
    set U := (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)
    have hspec : M.mat = U * Matrix.diagonal (Complex.ofReal ∘ M.eigvals) * star U := by
      simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
        Unitary.conjStarAlgAut_apply] using M.isHermitian.spectral_theorem
    have hcol : (star U).mulVec v = Pi.single j 1 := by
      ext k; have h := congr_fun (congr_fun (Unitary.coe_star_mul_self M.eigUnitary) k) j
      simpa [v, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
        Pi.single_apply, eq_comm] using h
    conv_lhs => rw [hspec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol]
    have hz : Matrix.diagonal (Complex.ofReal ∘ M.eigvals) *ᵥ Pi.single j 1 = 0 := by
      ext k; rw [Matrix.mulVec_diagonal]; by_cases hk : k = j
      · subst hk; simp [hMj]
      · simp [Pi.single_eq_of_ne hk]
    rw [hz, Matrix.mulVec_zero]
  have hquad0 : (star v ⬝ᵥ M.mat.mulVec v).re = 0 := by rw [hker]; simp
  have hmid_quad : (star v ⬝ᵥ M.mat.mulVec v).re =
      ((star v ⬝ᵥ A.mat.mulVec v).re + (star v ⬝ᵥ B.mat.mulVec v).re) / 2 := by
    rw [hM_mid]
    have h1 : (DensityOp.midpoint A B).mat.mulVec v =
        ((1 / 2 : ℝ) : ℂ) • A.mat.mulVec v + ((1 / 2 : ℝ) : ℂ) • B.mat.mulVec v := by
      show (((1 - 1 / 2 : ℝ) : ℂ) • A.mat + ((1 / 2 : ℝ) : ℂ) • B.mat).mulVec v = _
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]; norm_num
    rw [h1, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]; ring
  have hAnn : 0 ≤ (star v ⬝ᵥ A.mat.mulVec v).re :=
    (Complex.le_def.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp A.posSemidef).2 v)).1
  have hBnn : 0 ≤ (star v ⬝ᵥ B.mat.mulVec v).re :=
    (Complex.le_def.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp B.posSemidef).2 v)).1
  have hA0 : (star v ⬝ᵥ A.mat.mulVec v).re = 0 := by linarith
  rw [re_quadForm_spectral A.isHermitian v] at hA0
  have hterm0 : A.eigvals i * ‖((star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v) i‖ ^ 2 = 0 := by
    have hle := Finset.single_le_sum (f := fun k : Bool × d ↦
        A.eigvals k * ‖((star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v) k‖ ^ 2)
      (fun k _ ↦ mul_nonneg (A.eigvals_nonneg k) (sq_nonneg _)) (Finset.mem_univ i)
    have hge : 0 ≤ A.eigvals i * ‖((star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v) i‖ ^ 2 :=
      mul_nonneg (A.eigvals_nonneg i) (sq_nonneg _)
    unfold DensityOp.eigvals DensityOp.eigUnitary at hle hge ⊢
    linarith
  have hnorm0 : ((star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v) i = 0 := by
    rcases mul_eq_zero.mp hterm0 with h | h
    · exact absurd h hAi
    · exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)
  have hconj : (star (M.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ) *
      (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)) j i =
      star (((star (A.eigUnitary : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v) i) := by
    simp only [v, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.star_apply, star_sum,
      star_mul', star_star]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [hconj, hnorm0, star_zero]

/-- **Umegaki Relative-Entropy Identity for Dephasing Coherence**:
`D((Z_p ⊗ id)(Ψ) ‖ (Z_{1/2} ⊗ id)(Ψ)) = ENNReal.ofReal (S((Z_{1/2} ⊗ id)(Ψ)) - S((Z_p ⊗ id)(Ψ)))`. -/
theorem relEntropy_dephaseState_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) :
    relEntropy (dephaseState p hp0 hp1 Ψ) (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) =
      ENNReal.ofReal (vonNeumannEntropy (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ) -
        vonNeumannEntropy (dephaseState p hp0 hp1 Ψ)) := by
  haveI : Nonempty (Bool × d) := by
    by_contra h0; haveI : IsEmpty (Bool × d) := not_nonempty_iff.mp h0
    have htr := Ψ.trace_one; simp [Matrix.trace] at htr
  set A := dephaseState p hp0 hp1 Ψ
  set M := dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ
  have hext : ∀ (X Y : DensityOp (Bool × d)), X.mat = Y.mat → X = Y := by
    intro ⟨_, _, _⟩ ⟨_, _, _⟩ h; cases h; rfl
  have hL := tendsto_relEntropy_mix_maxMixed A M
  have hR : Tendsto (fun δ : ℝ ↦
      if h : 0 < δ ∧ δ < 1 then
        ENNReal.ofReal (vonNeumannEntropy (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) M (maxMixedState (Bool × d))) -
          vonNeumannEntropy (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) A (maxMixedState (Bool × d))))
      else ENNReal.ofReal (vonNeumannEntropy M - vonNeumannEntropy A))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (vonNeumannEntropy M - vonNeumannEntropy A))) := by
    have h1 := tendsto_vonNeumannEntropy_mix_maxMixed M
    have h2 := tendsto_vonNeumannEntropy_mix_maxMixed A
    have hcomb := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (h1.sub h2)
    refine hcomb.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
    have h01 : 0 ≤ δ ∧ δ ≤ 1 := ⟨le_of_lt hδ.1, le_of_lt hδ.2⟩
    have hδ' : 0 < δ ∧ δ < 1 := ⟨hδ.1, hδ.2⟩
    simp only [Function.comp_def, dif_pos h01, dif_pos hδ']
  have hEq : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (if h : 0 < δ ∧ δ < 1 then
        relEntropy (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) A (maxMixedState (Bool × d)))
          (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) M (maxMixedState (Bool × d)))
      else relEntropy A M) =
      (if h : 0 < δ ∧ δ < 1 then
        ENNReal.ofReal (vonNeumannEntropy (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) M (maxMixedState (Bool × d))) -
          vonNeumannEntropy (DensityOp.mix δ (le_of_lt h.1) (le_of_lt h.2) A (maxMixedState (Bool × d))))
      else ENNReal.ofReal (vonNeumannEntropy M - vonNeumannEntropy A)) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
    have hδ' : 0 < δ ∧ δ < 1 := ⟨hδ.1, hδ.2⟩
    rw [dif_pos hδ', dif_pos hδ']
    set Aδ := DensityOp.mix δ (le_of_lt hδ.1) (le_of_lt hδ.2) A (maxMixedState (Bool × d))
    set Mδ := DensityOp.mix δ (le_of_lt hδ.1) (le_of_lt hδ.2) M (maxMixedState (Bool × d))
    set Bδ := DensityOp.conjUnitary (pauliZTensorI d) Aδ
    have hAδ_pd : Aδ.mat.PosDef := by
      have h1 : (((1 - δ : ℝ) : ℂ) • A.mat).PosSemidef := by
        have : (((1 - δ : ℝ) : ℂ) • A.mat) = (1 - δ : ℝ) • A.mat := by ext x y; simp [Complex.real_smul]
        rw [this]; exact A.posSemidef.smul (by linarith [hδ.2])
      have h2 : ((δ : ℂ) • (maxMixedState (Bool × d)).mat).PosDef := by
        have : ((δ : ℂ) • (maxMixedState (Bool × d)).mat) = δ • (maxMixedState (Bool × d)).mat := by
          ext x y; simp [Complex.real_smul]
        rw [this]
        exact ((Matrix.PosDef.one (n := Bool × d) (R := ℂ)).smul
          (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))).smul hδ.1
      change (((1 - δ : ℝ) : ℂ) • A.mat + (δ : ℂ) • (maxMixedState (Bool × d)).mat).PosDef
      rw [add_comm]; exact h2.add_posSemidef h1
    have hBδ_pd : Bδ.mat.PosDef := by
      have h1 := hAδ_pd.mul_mul_conjTranspose_same (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)
      rw [Matrix.posDef_iff_dotProduct_mulVec] at hAδ_pd ⊢
      refine ⟨Bδ.isHermitian, fun v hv ↦ ?_⟩
      set w := (star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)).mulVec v
      have hw : w ≠ 0 := by
        intro h0; apply hv
        have := congr_arg (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ).mulVec h0
        rw [Matrix.mulVec_mulVec, Unitary.coe_mul_star_self (pauliZTensorI d), Matrix.one_mulVec,
          Matrix.mulVec_zero] at this; exact this
      have hq : star v ⬝ᵥ Bδ.mat.mulVec v = star w ⬝ᵥ Aδ.mat.mulVec w := by
        simp only [Bδ, DensityOp.conjUnitary, w]
        rw [Matrix.star_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
          ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
          ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
      rw [hq]; exact hAδ_pd.2 hw
    have hMδ_mid : DensityOp.midpoint Aδ Bδ = Mδ := by
      apply hext
      ext ⟨b₁, i⟩ ⟨b₂, j⟩
      have hZ_max : (DensityOp.conjUnitary (pauliZTensorI d) (maxMixedState (Bool × d))).mat =
          (maxMixedState (Bool × d)).mat := by
        ext ⟨c₁, r₁⟩ ⟨c₂, r₂⟩
        simp only [DensityOp.conjUnitary, pauliZTensorI, maxMixedState, Matrix.mul_apply,
          Matrix.diagonal_apply, Matrix.star_apply, Matrix.smul_apply, Matrix.one_apply]
        rw [Finset.sum_eq_single (c₂, r₂)]
        · rw [Finset.sum_eq_single (c₁, r₁)]
          · by_cases h : (c₁, r₁) = (c₂, r₂)
            · subst h; cases c₁ <;> simp
            · simp [h]
          · intro y _ hy; simp [Ne.symm hy]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro x _ hx; simp [hx, Ne.symm hx]
        · intro h; exact absurd (Finset.mem_univ _) h
      have h1 : (DensityOp.midpoint A (DensityOp.conjUnitary (pauliZTensorI d) A)).mat (b₁, i) (b₂, j) =
          M.mat (b₁, i) (b₂, j) := by
        have ha1 := dephaseState_apply (1 / 2) (by norm_num) (by norm_num) A b₁ b₂ i j
        have ha2 := dephaseState_apply (1 / 2) (by norm_num) (by norm_num) Ψ b₁ b₂ i j
        have ha3 := dephaseState_apply p hp0 hp1 Ψ b₁ b₂ i j
        change (dephaseState (1 / 2) (by norm_num) (by norm_num) A).mat (b₁, i) (b₂, j) = M.mat (b₁, i) (b₂, j)
        rw [ha1, ha2, ha3]; cases b₁ <;> cases b₂ <;> norm_num
      have hB_lin : Bδ.mat = ((1 - δ : ℝ) : ℂ) • (DensityOp.conjUnitary (pauliZTensorI d) A).mat +
          ((δ : ℝ) : ℂ) • (maxMixedState (Bool × d)).mat := by
        calc Bδ.mat = (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) *
              (((1 - δ : ℝ) : ℂ) • A.mat + ((δ : ℝ) : ℂ) • (maxMixedState (Bool × d)).mat) *
              star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) := rfl
          _ = ((1 - δ : ℝ) : ℂ) • (DensityOp.conjUnitary (pauliZTensorI d) A).mat +
              ((δ : ℝ) : ℂ) • (DensityOp.conjUnitary (pauliZTensorI d) (maxMixedState (Bool × d))).mat := by
              rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
                Matrix.mul_smul, Matrix.smul_mul]; rfl
          _ = _ := by rw [hZ_max]
      simp only [DensityOp.midpoint, DensityOp.mix, Aδ, Mδ, hB_lin, Matrix.add_apply,
        Matrix.smul_apply, Complex.real_smul] at h1 ⊢
      linear_combination (1 - δ : ℂ) * h1
    have hZ_Mδ : DensityOp.conjUnitary (pauliZTensorI d) Mδ = Mδ := by
      apply hext
      ext ⟨b₁, i⟩ ⟨b₂, j⟩
      have hM_diag : ∀ x y : Bool × d, x.1 ≠ y.1 → Mδ.mat x y = 0 := by
        intro ⟨c₁, r₁⟩ ⟨c₂, r₂⟩ hne
        simp only [Mδ, M, DensityOp.mix, maxMixedState, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply, Complex.real_smul]
        rw [dephaseState_apply]
        have hne' : (c₁, r₁) ≠ (c₂, r₂) := fun h ↦ hne (congr_arg Prod.fst h)
        simp [hne, hne']
      simp only [DensityOp.conjUnitary, pauliZTensorI, Matrix.mul_apply, Matrix.diagonal_apply,
        Matrix.star_apply]
      rw [Finset.sum_eq_single (b₂, j)]
      · rw [Finset.sum_eq_single (b₁, i)]
        · by_cases hb : b₁ = b₂
          · subst hb; cases b₁ <;> simp
          · rw [hM_diag (b₁, i) (b₂, j) hb]; simp
        · intro y _ hy; simp [Ne.symm hy]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro x _ hx; simp [hx, Ne.symm hx]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hsym : relEntropy Bδ Mδ = relEntropy Aδ Mδ := by
      have h := relEntropy_conjUnitary (pauliZTensorI d) Aδ Mδ
      rwa [hZ_Mδ] at h
    have hq := (qjs_eq_half_relEntropy_midpoint hAδ_pd hBδ_pd).2
    rw [hMδ_mid, hsym] at hq
    have hqjs_S : qjs Aδ Bδ = vonNeumannEntropy Mδ - vonNeumannEntropy Aδ := by
      unfold qjs; rw [hMδ_mid, vonNeumannEntropy_conjUnitary]; ring
    rw [hqjs_S] at hq
    have htwo : (relEntropy Aδ Mδ + relEntropy Aδ Mδ) / 2 = relEntropy Aδ Mδ := by
      rw [← two_mul, ENNReal.mul_div_cancel_left (by norm_num) (by norm_num)]
    rw [htwo] at hq
    exact hq.symm
  exact tendsto_nhds_unique (hL.congr' hEq) hR

/-- `(D((Z_p ⊗ id)(Ψ) ‖ (Z_{1/2} ⊗ id)(Ψ))).toReal = dephaseCoherence p Ψ`. -/
theorem relEntropy_dephaseState_toReal_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ψ : DensityOp (Bool × d)) :
    (relEntropy (dephaseState p hp0 hp1 Ψ)
      (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal =
    dephaseCoherence p hp0 hp1 Ψ := by
  rw [relEntropy_dephaseState_eq]
  have hnn : 0 ≤ dephaseCoherence p hp0 hp1 Ψ := by
    rw [dephaseCoherence_eq_qjs]
    haveI : Nonempty (Bool × d) := by
      by_contra h0; haveI : IsEmpty (Bool × d) := not_nonempty_iff.mp h0
      have htr := Ψ.trace_one; simp [Matrix.trace] at htr
    have h := (relEntropy_dephaseState_eq p hp0 hp1 Ψ).symm
    have hge : 0 ≤ (relEntropy (dephaseState p hp0 hp1 Ψ)
        (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal := ENNReal.toReal_nonneg
    -- `qjs A (Z A Z) ≥ 0` follows from `qjs_nonneg` or `dephaseCoherence = 1 - condEntropy`
    have hcond : (⟨fun b ↦ if b = false then dephaseState p hp0 hp1 Ψ else
        DensityOp.conjUnitary (pauliZTensorI d) (dephaseState p hp0 hp1 Ψ)⟩ : CQChannel (Bool × d)).condEntropy ≤ 1 :=
      (condEntropy_mem_Icc _).2
    unfold CQChannel.condEntropy at hcond
    linarith
  exact ENNReal.toReal_ofReal hnn

/-- **Theorem 1.3 (Relative-Entropy Formulation)**:
For every density operator `Ψ ∈ D(ℂ² ⊗ H)` and every `p ∈ [0, 1/2]`, letting
`C(p) := D((Z_p ⊗ id)(Ψ) ‖ (Z_{1/2} ⊗ id)(Ψ))`,
`C(p) ≤ 1 - h₂(h₂⁻¹(1 - C(0)) * p)`. -/
theorem theorem_1_3_dephasing_sdpi_relEntropy (Ψ : DensityOp (Bool × d))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) Ψ)
        (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal ≤
      1 - h2 (binConv (h2Inv (1 - (relEntropy (dephaseState 0 le_rfl (by norm_num) Ψ)
        (dephaseState (1 / 2) (by norm_num) (by norm_num) Ψ)).toReal)) p) := by
  rw [relEntropy_dephaseState_toReal_eq, relEntropy_dephaseState_toReal_eq]
  exact theorem_1_3_dephasing_sdpi Ψ hp0 hp1

/-- **Theorem 1.3 (Equatorial Equality, Relative-Entropy Formulation)**:
Every equatorial single-qubit state `½ (I + x X)` (`x ∈ [0, 1]`) attains equality in the
relative-entropy formulation of Theorem 1.3 for every `p ∈ [0, 1/2]`. -/
theorem theorem_1_3_equatorial_equality_relEntropy {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (relEntropy (dephaseState p hp0 (le_trans hp1 (by norm_num)) (equatorialState x hx0 hx1))
        (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal =
      1 - h2 (binConv (h2Inv (1 - (relEntropy (dephaseState 0 le_rfl (by norm_num) (equatorialState x hx0 hx1))
        (dephaseState (1 / 2) (by norm_num) (by norm_num) (equatorialState x hx0 hx1))).toReal)) p) := by
  rw [relEntropy_dephaseState_toReal_eq, relEntropy_dephaseState_toReal_eq]
  exact theorem_1_3_equatorial_equality hx0 hx1 hp0 hp1

end RelEntropyTheorem13

/-! ### 4. Channel Equivalence up to Output Isometry / Reversible CPTP (Proposition 2.2 D2–D3) -/

section ChannelEquivalence

variable {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-- Two binary-input c-q channels are equivalent *up to output isometry* if they admit isometric
embeddings `V₁ : d₁ → γ`, `V₂ : d₂ → γ` (`V₁ᴴ V₁ = 1`, `V₂ᴴ V₂ = 1`) into a common output Hilbert
space `γ` such that `V₁ W₁(b) V₁ᴴ = V₂ W₂(b) V₂ᴴ` for both `b ∈ Bool`. -/
def CQChannel.IsoEquiv (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) : Prop :=
  ∃ (γ : Type u) (_ : Fintype γ) (_ : DecidableEq γ)
    (V₁ : Matrix γ d₁ ℂ) (V₂ : Matrix γ d₂ ℂ),
    V₁ᴴ * V₁ = 1 ∧ V₂ᴴ * V₂ = 1 ∧
    ∀ b : Bool, V₁ * (W₁.out b).mat * V₁ᴴ = V₂ * (W₂.out b).mat * V₂ᴴ

/-- Two binary-input c-q channels are *reversibly CPTP equivalent* (channel-isomorphic) if there
exist CPTP maps `Φ : d₁ → d₂` and `Ψ : d₂ → d₁` satisfying `Φ(W₁(b)) = W₂(b)` and
`Ψ(W₂(b)) = W₁(b)` for both `b ∈ Bool`. -/
def CQChannel.ChannelEquiv (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) : Prop :=
  ∃ (Φ : CPTPMap d₁ d₂) (Ψ : CPTPMap d₂ d₁),
    (∀ b : Bool, (Φ.apply (W₁.out b)).mat = (W₂.out b).mat) ∧
    (∀ b : Bool, (Ψ.apply (W₂.out b)).mat = (W₁.out b).mat)

lemma CQChannel.IsoEquiv.refl (W : CQChannel d₁) : W.IsoEquiv W :=
  ⟨d₁, inferInstance, inferInstance, 1, 1, by simp, by simp, fun _ ↦ by simp⟩

lemma CQChannel.IsoEquiv.symm {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.IsoEquiv W₂) : W₂.IsoEquiv W₁ := by
  obtain ⟨γ, _, _, V₁, V₂, h1, h2, heq⟩ := h
  exact ⟨γ, inferInstance, inferInstance, V₂, V₁, h2, h1, fun b ↦ (heq b).symm⟩

lemma CQChannel.ChannelEquiv.refl (W : CQChannel d₁) : W.ChannelEquiv W := by
  refine ⟨CPTPMap.id d₁, CPTPMap.id d₁, ?_, ?_⟩
  all_goals
    intro b; ext i j
    simp [CPTPMap.apply, CPTPMap.toLinearMap, CPTPMap.id, partialTrace₂Mat,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_unique]

lemma CQChannel.ChannelEquiv.symm {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.ChannelEquiv W₂) : W₂.ChannelEquiv W₁ := by
  obtain ⟨Φ, Ψ, h1, h2⟩ := h
  exact ⟨Ψ, Φ, h2, h1⟩

lemma CQChannel.ChannelEquiv.trans {d₃ : Type u} [Fintype d₃] [DecidableEq d₃]
    {W₁ : CQChannel d₁} {W₂ : CQChannel d₂} {W₃ : CQChannel d₃}
    (h12 : W₁.ChannelEquiv W₂) (h23 : W₂.ChannelEquiv W₃) : W₁.ChannelEquiv W₃ := by
  obtain ⟨Φ₁, Ψ₁, hΦ₁, hΨ₁⟩ := h12
  obtain ⟨Φ₂, Ψ₂, hΦ₂, hΨ₂⟩ := h23
  have hext : ∀ {α : Type u} [Fintype α] [DecidableEq α] (X Y : DensityOp α), X.mat = Y.mat → X = Y := by
    intro α _ _ ⟨_, _, _⟩ ⟨_, _, _⟩ h; cases h; rfl
  refine ⟨Φ₂.comp Φ₁, Ψ₁.comp Ψ₂, ?_, ?_⟩
  · intro b; rw [CPTPMap.comp_apply, hext _ _ (hΦ₁ b), hΦ₂ b]
  · intro b; rw [CPTPMap.comp_apply, hext _ _ (hΨ₂ b), hΨ₁ b]

/-- Reversible CPTP equivalence preserves `condEntropy` (immediate from general CPTP DPI). -/
theorem CQChannel.ChannelEquiv.condEntropy_eq {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.ChannelEquiv W₂) : W₁.condEntropy = W₂.condEntropy := by
  obtain ⟨Φ, Ψ, hΦ, hΨ⟩ := h
  have h1 := condEntropy_cptp_ge Φ W₁
  have h2 := condEntropy_cptp_ge Ψ W₂
  have hΦ_eq : (Φ.compCQ W₁).condEntropy = W₂.condEntropy := by
    unfold CQChannel.condEntropy CPTPMap.compCQ qjs
    have hmid : (DensityOp.midpoint (Φ.apply (W₁.out false)) (Φ.apply (W₁.out true))).mat =
        (DensityOp.midpoint (W₂.out false) (W₂.out true)).mat := by
      simp only [DensityOp.midpoint, DensityOp.mix, hΦ false, hΦ true]
    rw [vonNeumannEntropy_eq_of_mat_eq hmid, vonNeumannEntropy_eq_of_mat_eq (hΦ false),
      vonNeumannEntropy_eq_of_mat_eq (hΦ true)]
  have hΨ_eq : (Ψ.compCQ W₂).condEntropy = W₁.condEntropy := by
    unfold CQChannel.condEntropy CPTPMap.compCQ qjs
    have hmid : (DensityOp.midpoint (Ψ.apply (W₂.out false)) (Ψ.apply (W₂.out true))).mat =
        (DensityOp.midpoint (W₁.out false) (W₁.out true)).mat := by
      simp only [DensityOp.midpoint, DensityOp.mix, hΨ false, hΨ true]
    rw [vonNeumannEntropy_eq_of_mat_eq hmid, vonNeumannEntropy_eq_of_mat_eq (hΨ false),
      vonNeumannEntropy_eq_of_mat_eq (hΨ true)]
  linarith

theorem CQChannel.ChannelEquiv.symCapacity_eq {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.ChannelEquiv W₂) : W₁.symCapacity = W₂.symCapacity := by
  unfold CQChannel.symCapacity; rw [h.condEntropy_eq]

/-- Isometric equivalence preserves `condEntropy` and `fidelityParam`. -/
theorem CQChannel.IsoEquiv.condEntropy_eq {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.IsoEquiv W₂) : W₁.condEntropy = W₂.condEntropy := by
  obtain ⟨γ, _, _, V₁, V₂, h1, h2, heq⟩ := h
  have hS : ∀ {α : Type u} [Fintype α] [DecidableEq α] (V : Matrix γ α ℂ),
      Vᴴ * V = 1 → ∀ (τ : DensityOp α) (σ : DensityOp γ), V * τ.mat * Vᴴ = σ.mat →
      vonNeumannEntropy τ = vonNeumannEntropy σ := by
    intro α _ _ V hV τ σ hm
    unfold vonNeumannEntropy DensityOp.eigvals; congr 1
    let A : Matrix γ α ℂ := V * τ.sqrtMat
    have hAAH : A * Aᴴ = σ.mat := by
      calc A * Aᴴ = V * (τ.sqrtMat * τ.sqrtMat) * Vᴴ := by
            simp only [A, Matrix.conjTranspose_mul, τ.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
        _ = V * τ.mat * Vᴴ := by rw [τ.sqrtMat_mul_self]
        _ = σ.mat := hm
    have hAHA : Aᴴ * A = τ.mat := by
      calc Aᴴ * A = τ.sqrtMat * ((Vᴴ * V) * τ.sqrtMat) := by
            simp only [A, Matrix.conjTranspose_mul, τ.sqrtMat_isHermitian.eq, Matrix.mul_assoc]
        _ = τ.mat := by rw [hV, Matrix.one_mul, τ.sqrtMat_mul_self]
    have hcp := (charpoly_mul_conjTranspose_eq A)
    rw [hAAH, hAHA] at hcp
    exact (spectral_sum_eq_of_charpoly_mul_X_pow σ.isHermitian τ.isHermitian hcp (by simp [Real.negMulLog])).symm
  let τ0 : DensityOp γ :=
    { mat := V₁ * (W₁.out false).mat * V₁ᴴ
      posSemidef := (W₁.out false).posSemidef.mul_mul_conjTranspose_same V₁
      trace_one := by rw [Matrix.trace_mul_cycle, h1, Matrix.one_mul, (W₁.out false).trace_one] }
  let τ1 : DensityOp γ :=
    { mat := V₁ * (W₁.out true).mat * V₁ᴴ
      posSemidef := (W₁.out true).posSemidef.mul_mul_conjTranspose_same V₁
      trace_one := by rw [Matrix.trace_mul_cycle, h1, Matrix.one_mul, (W₁.out true).trace_one] }
  have hS0 : vonNeumannEntropy (W₁.out false) = vonNeumannEntropy (W₂.out false) :=
    (hS V₁ h1 (W₁.out false) τ0 rfl).trans (hS V₂ h2 (W₂.out false) τ0 (heq false).symm).symm
  have hS1 : vonNeumannEntropy (W₁.out true) = vonNeumannEntropy (W₂.out true) :=
    (hS V₁ h1 (W₁.out true) τ1 rfl).trans (hS V₂ h2 (W₂.out true) τ1 (heq true).symm).symm
  have hSmid : vonNeumannEntropy (DensityOp.midpoint (W₁.out false) (W₁.out true)) =
      vonNeumannEntropy (DensityOp.midpoint (W₂.out false) (W₂.out true)) := by
    have hm1 : V₁ * (DensityOp.midpoint (W₁.out false) (W₁.out true)).mat * V₁ᴴ =
        (DensityOp.midpoint τ0 τ1).mat := by
      simp only [DensityOp.midpoint, DensityOp.mix, τ0, τ1, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul]
    have hm2 : V₂ * (DensityOp.midpoint (W₂.out false) (W₂.out true)).mat * V₂ᴴ =
        (DensityOp.midpoint τ0 τ1).mat := by
      simp only [DensityOp.midpoint, DensityOp.mix, τ0, τ1, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul, heq false, heq true]
    exact (hS V₁ h1 _ _ hm1).trans (hS V₂ h2 _ _ hm2).symm
  unfold CQChannel.condEntropy qjs; rw [hS0, hS1, hSmid]

/-- Helper: build a CPTP map from a matrix `K : Matrix β α ℂ` whose defect `1 - Kᴴ * K` is
positive semidefinite (in particular, any isometry or contraction `Kᴴ * K ≤ 1`). -/
noncomputable def CPTPMap.ofContraction {α β : Type u} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (K : Matrix β α ℂ) (hK : (1 - Kᴴ * K).PosSemidef) : CPTPMap α β :=
  let b₀ : β := Classical.arbitrary β
  let D : Matrix α α ℂ :=
    (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ) *
      Matrix.diagonal (fun i ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
      star (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
  { env := PUnit ⊕ α
    fintypeEnv := inferInstance
    decEqEnv := inferInstance
    isom := Matrix.of fun p a ↦
      match p.2 with
      | Sum.inl () => K p.1 a
      | Sum.inr c => if p.1 = b₀ then D c a else 0
    isom_eq := by
      have hD_herm : Dᴴ = D := by
        simp only [D, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
        congr 2; ext i j; simp [Matrix.diagonal_apply]; split_ifs <;> simp
      have hDD : Dᴴ * D = 1 - Kᴴ * K := by
        rw [hD_herm]
        set U := (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
        have hspec : 1 - Kᴴ * K = U * Matrix.diagonal (Complex.ofReal ∘ hK.isHermitian.eigenvalues) * star U := by
          simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hK.isHermitian.spectral_theorem
        calc D * D = U * (Matrix.diagonal (fun i ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
              (star U * U) * Matrix.diagonal (fun i ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ))) * star U := by
              simp only [D, U, Matrix.mul_assoc]
          _ = U * Matrix.diagonal (Complex.ofReal ∘ hK.isHermitian.eigenvalues) * star U := by
              rw [Unitary.coe_star_mul_self hK.isHermitian.eigenvectorUnitary, Matrix.mul_one,
                Matrix.diagonal_mul_diagonal]
              congr 2; ext i; simp only [Function.comp_apply, ← Complex.ofReal_mul,
                Real.mul_self_sqrt (hK.eigenvalues_nonneg i)]
          _ = 1 - Kᴴ * K := hspec.symm
      ext i j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_unique]
      have hterm1 : (∑ b : β, star (K b i) * K b j) = (Kᴴ * K) i j := by
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
      have hterm2 : (∑ b : β, ∑ c : α, star (if b = b₀ then D c i else 0) *
          (if b = b₀ then D c j else 0)) = (Dᴴ * D) i j := by
        rw [Finset.sum_eq_single b₀]
        · simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [Finset.sum_add_distrib]
      rw [hterm1, hterm2, hDD, Matrix.sub_apply, add_sub_cancel] }

lemma CPTPMap.ofContraction_apply_of_ker {α β : Type u} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (K : Matrix β α ℂ) (hK : (1 - Kᴴ * K).PosSemidef) (ρ : DensityOp α)
    (hker : (1 - Kᴴ * K) * ρ.mat = 0) :
    ((CPTPMap.ofContraction K hK).apply ρ).mat = K * ρ.mat * Kᴴ := by
  set D : Matrix α α ℂ :=
    (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ) *
      Matrix.diagonal (fun i ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
      star (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
  have hD_herm : Dᴴ = D := by
    simp only [D, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    congr 2; ext i j; simp [Matrix.diagonal_apply]; split_ifs <;> simp
  have hDD : D * D = 1 - Kᴴ * K := by
    set U := (hK.isHermitian.eigenvectorUnitary : Matrix α α ℂ)
    have hspec : 1 - Kᴴ * K = U * Matrix.diagonal (Complex.ofReal ∘ hK.isHermitian.eigenvalues) * star U := by
      simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hK.isHermitian.spectral_theorem
    calc D * D = U * (Matrix.diagonal (fun i ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ)) *
          (star U * U) * Matrix.diagonal (fun i ↦ (Real.sqrt (hK.isHermitian.eigenvalues i) : ℂ))) * star U := by
          simp only [D, U, Matrix.mul_assoc]
      _ = U * Matrix.diagonal (Complex.ofReal ∘ hK.isHermitian.eigenvalues) * star U := by
          rw [Unitary.coe_star_mul_self hK.isHermitian.eigenvectorUnitary, Matrix.mul_one,
            Matrix.diagonal_mul_diagonal]
          congr 2; ext i; simp only [Function.comp_apply, ← Complex.ofReal_mul,
            Real.mul_self_sqrt (hK.eigenvalues_nonneg i)]
      _ = 1 - Kᴴ * K := hspec.symm
  have hDρD : D * ρ.mat * Dᴴ = 0 := by
    have htr0 : (D * ρ.mat * Dᴴ).trace = 0 := by
      rw [Matrix.trace_mul_cycle, hD_herm, hDD, hker, Matrix.trace_zero]
    have hpsd : (D * ρ.mat * Dᴴ).PosSemidef := ρ.posSemidef.mul_mul_conjTranspose_same D
    have heig0 : ∀ i : α, hpsd.isHermitian.eigenvalues i = 0 := by
      have hsum : ∑ i : α, hpsd.isHermitian.eigenvalues i = 0 := by
        have hspec : D * ρ.mat * Dᴴ = (hpsd.isHermitian.eigenvectorUnitary : Matrix α α ℂ) *
            Matrix.diagonal (Complex.ofReal ∘ hpsd.isHermitian.eigenvalues) *
            star (hpsd.isHermitian.eigenvectorUnitary : Matrix α α ℂ) := by
          simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using
            hpsd.isHermitian.spectral_theorem
        have ht : (D * ρ.mat * Dᴴ).trace = ∑ i : α, (hpsd.isHermitian.eigenvalues i : ℂ) := by
          conv_lhs => rw [hspec]
          rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self hpsd.isHermitian.eigenvectorUnitary,
            Matrix.one_mul, Matrix.trace_diagonal]; rfl
        rw [htr0] at ht
        have := congr_arg Complex.re ht
        simpa [Complex.re_sum] using this.symm
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hpsd.eigenvalues_nonneg j).mp hsum i (Finset.mem_univ i)
    have hspec : D * ρ.mat * Dᴴ = (hpsd.isHermitian.eigenvectorUnitary : Matrix α α ℂ) *
        Matrix.diagonal (Complex.ofReal ∘ hpsd.isHermitian.eigenvalues) *
        star (hpsd.isHermitian.eigenvectorUnitary : Matrix α α ℂ) := by
      simpa [Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using
        hpsd.isHermitian.spectral_theorem
    rw [hspec]; simp [heig0]
  ext b₁ b₂
  simp only [CPTPMap.apply, CPTPMap.toLinearMap, CPTPMap.ofContraction, partialTrace₂Mat,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type, Fintype.sum_unique]
  have hzero : (∑ c : α, ∑ a₂ : α, (∑ a₁ : α, (if b₁ = Classical.arbitrary β then D c a₁ else 0) * ρ.mat a₁ a₂) *
      star (if b₂ = Classical.arbitrary β then D c a₂ else 0)) = 0 := by
    by_cases h1 : b₁ = Classical.arbitrary β
    · by_cases h2 : b₂ = Classical.arbitrary β
      · simp only [h1, h2, ↓reduceIte]
        have htr : (∑ c : α, (D * ρ.mat * Dᴴ) c c) = 0 := by simp [hDρD]
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using htr
      · simp [h2]
    · simp [h1]
  rw [hzero, add_zero]

/-- **Isometric equivalence implies reversible CPTP equivalence** (`IsoEquiv → ChannelEquiv`). -/
theorem CQChannel.IsoEquiv.toChannelEquiv {W₁ : CQChannel d₁} {W₂ : CQChannel d₂}
    (h : W₁.IsoEquiv W₂) : W₁.ChannelEquiv W₂ := by
  haveI : Nonempty d₁ := by
    by_contra h0; haveI : IsEmpty d₁ := not_nonempty_iff.mp h0
    have htr := (W₁.out false).trace_one; simp [Matrix.trace] at htr
  haveI : Nonempty d₂ := by
    by_contra h0; haveI : IsEmpty d₂ := not_nonempty_iff.mp h0
    have htr := (W₂.out false).trace_one; simp [Matrix.trace] at htr
  obtain ⟨γ, _, _, V₁, V₂, h1, h2, heq⟩ := h
  set K : Matrix d₂ d₁ ℂ := V₂ᴴ * V₁
  have hK_psd : (1 - Kᴴ * K).PosSemidef := by
    have h1eq : 1 - Kᴴ * K = V₁ᴴ * (1 - V₂ * V₂ᴴ) * V₁ := by
      simp only [K, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, Matrix.mul_assoc]
    rw [h1eq]
    have hQ : (1 - V₂ * V₂ᴴ).PosSemidef := by
      set Q : Matrix γ γ ℂ := 1 - V₂ * V₂ᴴ
      have hQh : Qᴴ = Q := by
        simp [Q, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
      have hQ2 : Qᴴ * Q = Q := by
        rw [hQh]; simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
        have hVV : (V₂ * V₂ᴴ) * (V₂ * V₂ᴴ) = V₂ * V₂ᴴ := by
          calc (V₂ * V₂ᴴ) * (V₂ * V₂ᴴ) = V₂ * ((V₂ᴴ * V₂) * V₂ᴴ) := by simp only [Matrix.mul_assoc]
            _ = V₂ * V₂ᴴ := by rw [h2, Matrix.one_mul]
        rw [hVV]; abel
      rw [← hQ2]; exact Matrix.posSemidef_conjTranspose_mul_self Q
    simpa [Matrix.conjTranspose_conjTranspose] using hQ.mul_mul_conjTranspose_same V₁ᴴ
  have hKH_psd : (1 - (Kᴴ)ᴴ * Kᴴ).PosSemidef := by
    have h1eq : 1 - (Kᴴ)ᴴ * Kᴴ = V₂ᴴ * (1 - V₁ * V₁ᴴ) * V₂ := by
      simp only [K, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2, Matrix.mul_assoc]
    rw [h1eq]
    have hQ : (1 - V₁ * V₁ᴴ).PosSemidef := by
      set Q : Matrix γ γ ℂ := 1 - V₁ * V₁ᴴ
      have hQh : Qᴴ = Q := by simp [Q, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
      have hQ2 : Qᴴ * Q = Q := by
        rw [hQh]; simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
        have hVV : (V₁ * V₁ᴴ) * (V₁ * V₁ᴴ) = V₁ * V₁ᴴ := by
          calc (V₁ * V₁ᴴ) * (V₁ * V₁ᴴ) = V₁ * ((V₁ᴴ * V₁) * V₁ᴴ) := by simp only [Matrix.mul_assoc]
            _ = V₁ * V₁ᴴ := by rw [h1, Matrix.one_mul]
        rw [hVV]; abel
      rw [← hQ2]; exact Matrix.posSemidef_conjTranspose_mul_self Q
    simpa [Matrix.conjTranspose_conjTranspose] using hQ.mul_mul_conjTranspose_same V₂ᴴ
  refine ⟨CPTPMap.ofContraction K hK_psd, CPTPMap.ofContraction Kᴴ hKH_psd, ?_, ?_⟩
  · intro b
    have hker : (1 - Kᴴ * K) * (W₁.out b).mat = 0 := by
      have hV2 : V₂ * V₂ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) = V₁ * (W₁.out b).mat * V₁ᴴ := by
        rw [heq b]
        calc V₂ * V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ)
            = V₂ * ((V₂ᴴ * V₂) * (W₂.out b).mat) * V₂ᴴ := by simp only [Matrix.mul_assoc]
          _ = V₂ * (W₂.out b).mat * V₂ᴴ := by rw [h2, Matrix.one_mul]
      calc (1 - Kᴴ * K) * (W₁.out b).mat
          = (W₁.out b).mat - (V₁ᴴ * (V₂ * V₂ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ)) * V₁) := by
            simp only [K, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
              Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
            congr 1; simp only [← Matrix.mul_assoc V₁ᴴ V₁, h1, Matrix.mul_one]
        _ = (W₁.out b).mat - (V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₁) := by rw [hV2]
        _ = (W₁.out b).mat - (W₁.out b).mat := by
            congr 1
            calc V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₁
                = (V₁ᴴ * V₁) * (W₁.out b).mat * (V₁ᴴ * V₁) := by simp only [Matrix.mul_assoc]
              _ = (W₁.out b).mat := by rw [h1, Matrix.one_mul, Matrix.mul_one]
        _ = 0 := sub_self _
    rw [CPTPMap.ofContraction_apply_of_ker K hK_psd (W₁.out b) hker]
    calc K * (W₁.out b).mat * Kᴴ
        = V₂ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₂ := by
          simp only [K, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₂ := by rw [heq b]
      _ = (V₂ᴴ * V₂) * (W₂.out b).mat * (V₂ᴴ * V₂) := by simp only [Matrix.mul_assoc]
      _ = (W₂.out b).mat := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  · intro b
    have hker : (1 - (Kᴴ)ᴴ * Kᴴ) * (W₂.out b).mat = 0 := by
      have hV1 : V₁ * V₁ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) = V₂ * (W₂.out b).mat * V₂ᴴ := by
        rw [← heq b]
        calc V₁ * V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ)
            = V₁ * ((V₁ᴴ * V₁) * (W₁.out b).mat) * V₁ᴴ := by simp only [Matrix.mul_assoc]
          _ = V₁ * (W₁.out b).mat * V₁ᴴ := by rw [h1, Matrix.one_mul]
      calc (1 - (Kᴴ)ᴴ * Kᴴ) * (W₂.out b).mat
          = (W₂.out b).mat - (V₂ᴴ * (V₁ * V₁ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ)) * V₂) := by
            simp only [K, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
              Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
            congr 1; simp only [← Matrix.mul_assoc V₂ᴴ V₂, h2, Matrix.mul_one]
        _ = (W₂.out b).mat - (V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₂) := by rw [hV1]
        _ = (W₂.out b).mat - (W₂.out b).mat := by
            congr 1
            calc V₂ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₂
                = (V₂ᴴ * V₂) * (W₂.out b).mat * (V₂ᴴ * V₂) := by simp only [Matrix.mul_assoc]
              _ = (W₂.out b).mat := by rw [h2, Matrix.one_mul, Matrix.mul_one]
        _ = 0 := sub_self _
    rw [CPTPMap.ofContraction_apply_of_ker Kᴴ hKH_psd (W₂.out b) hker]
    calc Kᴴ * (W₂.out b).mat * (Kᴴ)ᴴ
        = V₁ᴴ * (V₂ * (W₂.out b).mat * V₂ᴴ) * V₁ := by
          simp only [K, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = V₁ᴴ * (V₁ * (W₁.out b).mat * V₁ᴴ) * V₁ := by rw [← heq b]
      _ = (V₁ᴴ * V₁) * (W₁.out b).mat * (V₁ᴴ * V₁) := by simp only [Matrix.mul_assoc]
      _ = (W₁.out b).mat := by rw [h1, Matrix.one_mul, Matrix.mul_one]

/-- **Universal Purification-Duality Lemma**:
For any binary-input c-q channel `W : CQChannel d` and any purification factors
`A₀, A₁ : Matrix d E ℂ` satisfying `A₀ * A₀ᴴ = (W.out false).mat` and
`A₁ * A₁ᴴ = (W.out true).mat`, the dual channel `W.dual` is equivalent up to output isometry
(`IsoEquiv`) to the channel `b ↦ M_b * M_bᴴ` on `Bool × E` where
`M_false = (1/√2)[A₀ᴴ; A₁ᴴ]` and `M_true = (1/√2)[A₀ᴴ; -A₁ᴴ]`. -/
theorem dual_isoEquiv_of_purification {d E : Type u} [Fintype d] [DecidableEq d]
    [Fintype E] [DecidableEq E]
    (W : CQChannel d) (A₀ A₁ : Matrix d E ℂ)
    (hA₀ : A₀ * A₀ᴴ = (W.out false).mat) (hA₁ : A₁ * A₁ᴴ = (W.out true).mat) :
    let M₀ : Matrix (Bool × E) d ℂ := Matrix.of fun p x ↦
      ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)
    let M₁ : Matrix (Bool × E) d ℂ := Matrix.of fun p x ↦
      ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)
    let W_E : CQChannel (Bool × E) :=
      { out
          | false =>
            { mat := M₀ * M₀ᴴ
              posSemidef := by
                simpa [Matrix.conjTranspose_conjTranspose] using
                  Matrix.posSemidef_conjTranspose_mul_self M₀ᴴ
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hM : M₀ᴴ * M₀ = (DensityOp.midpoint (W.out false) (W.out true)).mat := by
                  have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
                    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
                      ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; push_cast; ring
                  ext x y
                  simp only [M₀, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    DensityOp.midpoint, DensityOp.mix, Matrix.add_apply, Matrix.smul_apply,
                    Complex.real_smul, ← hA₀, ← hA₁]
                  have ht : ∀ (A : Matrix d E ℂ),
                      (∑ e : E, star (((Real.sqrt 2 : ℂ)⁻¹) * star (A x e)) *
                        (((Real.sqrt 2 : ℂ)⁻¹) * star (A y e))) =
                      (1 / 2 : ℂ) * (∑ e : E, A x e * star (A y e)) := by
                    intro A; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _
                    simp only [star_mul', star_star]
                    calc _ = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (A x e * star (A y e)) := by ring
                      _ = _ := by rw [hsq2]
                  rw [ht A₀, ht A₁]; push_cast; ring
                rw [hM, (DensityOp.midpoint (W.out false) (W.out true)).trace_one] }
          | true =>
            { mat := M₁ * M₁ᴴ
              posSemidef := by
                simpa [Matrix.conjTranspose_conjTranspose] using
                  Matrix.posSemidef_conjTranspose_mul_self M₁ᴴ
              trace_one := by
                rw [Matrix.trace_mul_comm]
                have hM : M₁ᴴ * M₁ = (DensityOp.midpoint (W.out false) (W.out true)).mat := by
                  have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
                    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
                      ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; push_cast; ring
                  ext x y
                  simp only [M₁, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                    Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false,
                    DensityOp.midpoint, DensityOp.mix, Matrix.add_apply, Matrix.smul_apply,
                    Complex.real_smul, ← hA₀, ← hA₁]
                  have ht : ∀ (A : Matrix d E ℂ),
                      (∑ e : E, star (((Real.sqrt 2 : ℂ)⁻¹) * star (A x e)) *
                        (((Real.sqrt 2 : ℂ)⁻¹) * star (A y e))) =
                      (1 / 2 : ℂ) * (∑ e : E, A x e * star (A y e)) := by
                    intro A; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _
                    simp only [star_mul', star_star]
                    calc _ = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (A x e * star (A y e)) := by ring
                      _ = _ := by rw [hsq2]
                  have htn : (∑ e : E, star (((Real.sqrt 2 : ℂ)⁻¹) * -star (A₁ x e)) *
                        (((Real.sqrt 2 : ℂ)⁻¹) * -star (A₁ y e))) =
                      (1 / 2 : ℂ) * (∑ e : E, A₁ x e * star (A₁ y e)) := by
                    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _
                    simp only [star_mul', star_neg, star_star]
                    calc _ = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (A₁ x e * star (A₁ y e)) := by ring
                      _ = _ := by rw [hsq2]
                  rw [ht A₀, htn]; push_cast; ring
                rw [hM, (DensityOp.midpoint (W.out false) (W.out true)).trace_one] } }
    W.dual.IsoEquiv W_E := by
  intro M₀ M₁ W_E
  -- For each `τ ∈ {W.out false, W.out true}` with `A * Aᴴ = τ.mat`, construct `V_τ : (E ⊕ d) → d`
  -- with `V_τᴴ V_τ = 1` and `V_τ * √τ = inl ↦ Aᴴ, inr ↦ 0`!
  have hfactor : ∀ (τ : DensityOp d) (A : Matrix d E ℂ), A * Aᴴ = τ.mat →
      ∃ V : Matrix (E ⊕ d) d ℂ, Vᴴ * V = 1 ∧
        ∀ (y : E ⊕ d) (x : d), (V * τ.sqrtMat) y x = match y with | Sum.inl e => Aᴴ e x | Sum.inr _ => 0 := by
    intro τ A hA
    set U : Matrix d d ℂ := (τ.eigUnitary : Matrix d d ℂ)
    have hU_mul : U * star U = 1 := Unitary.coe_mul_star_self τ.eigUnitary
    have hU_star : star U * U = 1 := Unitary.coe_star_mul_self τ.eigUnitary
    have hspec : τ.mat = U * Matrix.diagonal (Complex.ofReal ∘ τ.eigvals) * star U := by
      simpa [U, DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
        Unitary.conjStarAlgAut_apply] using τ.isHermitian.spectral_theorem
    let pinv : Matrix d d ℂ :=
      U * Matrix.diagonal (fun i ↦ if 0 < τ.eigvals i then ((Real.sqrt (τ.eigvals i))⁻¹ : ℂ) else 0) * star U
    let P : Matrix d d ℂ :=
      U * Matrix.diagonal (fun i ↦ if 0 < τ.eigvals i then (1 : ℂ) else 0) * star U
    let Q : Matrix d d ℂ := 1 - P
    have hP_herm : Pᴴ = P := by
      simp only [P, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
      congr 2; ext i j; simp [Matrix.diagonal_apply]; split_ifs <;> simp
    have hP_idem : P * P = P := by
      simp only [P, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hU_star, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _),
        Matrix.diagonal_mul_diagonal]
      congr 2; ext i; split_ifs <;> simp
    have hpinv_herm : pinvᴴ = pinv := by
      simp only [pinv, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
      congr 2; ext i j; simp [Matrix.diagonal_apply]; split_ifs <;> simp
    have hpinv_mul_mat : pinv * τ.mat * pinv = P := by
      conv_lhs => rw [hspec]
      simp only [pinv, P, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hU_star, Matrix.one_mul,
        ← Matrix.mul_assoc (star U) U, hU_star, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i; simp only [Function.comp_apply]
      split_ifs with hi
      · have hsq : (Real.sqrt (τ.eigvals i) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hi)
        have h1 : (τ.eigvals i : ℂ) = (Real.sqrt (τ.eigvals i) : ℂ) * (Real.sqrt (τ.eigvals i) : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hi)]
        rw [h1]; field_simp [hsq]
      · simp
    have hpinv_sqrt : pinv * τ.sqrtMat = P := by
      have hsq_spec : τ.sqrtMat = U * Matrix.diagonal (fun i ↦ (Real.sqrt (τ.eigvals i) : ℂ)) * star U := rfl
      rw [hsq_spec]
      simp only [pinv, P, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hU_star, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i
      split_ifs with hi
      · have hsq : (Real.sqrt (τ.eigvals i) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hi)
        exact inv_mul_cancel₀ hsq
      · simp
    have hQ_sqrt : Q * τ.sqrtMat = 0 := by
      have hsq_spec : τ.sqrtMat = U * Matrix.diagonal (fun i ↦ (Real.sqrt (τ.eigvals i) : ℂ)) * star U := rfl
      have hP_sqrt : P * τ.sqrtMat = τ.sqrtMat := by
        rw [hsq_spec]
        simp only [P, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star U) U, hU_star, Matrix.one_mul,
          ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
        congr 2; ext i
        split_ifs with hi
        · simp
        · have h0 : τ.eigvals i = 0 := le_antisymm (not_lt.mp hi) (τ.eigvals_nonneg i)
          simp [h0]
      simp only [Q, Matrix.sub_mul, Matrix.one_mul, hP_sqrt, sub_self]
    have hAH_P : Aᴴ * P = Aᴴ := by
      have hQ_mat : Q * τ.mat * Qᴴ = 0 := by
        have hQ_herm : Qᴴ = Q := by simp [Q, hP_herm]
        rw [hQ_herm, ← τ.sqrtMat_mul_self, ← Matrix.mul_assoc Q τ.sqrtMat, hQ_sqrt, Matrix.zero_mul,
          Matrix.zero_mul]
      have hAQ : (Aᴴ * Q)ᴴ * (Aᴴ * Q) = 0 := by
        have hQ_herm : Qᴴ = Q := by simp [Q, hP_herm]
        calc (Aᴴ * Q)ᴴ * (Aᴴ * Q) = Q * (A * Aᴴ) * Qᴴ := by
              simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQ_herm, Matrix.mul_assoc]
          _ = Q * τ.mat * Qᴴ := by rw [hA]
          _ = 0 := hQ_mat
      have hAQ0 : Aᴴ * Q = 0 := by
        ext e x
        have hdiag := congr_fun (congr_fun hAQ x) x
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply] at hdiag
        have hsum : ∑ e' : E, ‖(Aᴴ * Q) e' x‖ ^ 2 = 0 := by
          have hre := congr_arg Complex.re hdiag
          rw [Complex.re_sum, Complex.zero_re] at hre
          rw [← hre]; apply Finset.sum_congr rfl; intro e' _
          rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
        have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun e' _ ↦ sq_nonneg ‖(Aᴴ * Q) e' x‖).mp hsum e (Finset.mem_univ e)
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
      have hsub : Aᴴ - Aᴴ * P = 0 := by simpa [Q, Matrix.mul_sub, Matrix.mul_one] using hAQ0
      exact (sub_eq_zero.mp hsub).symm
    let W_mat : Matrix E d ℂ := Aᴴ * pinv
    let V : Matrix (E ⊕ d) d ℂ := Matrix.of fun y x ↦ match y with | Sum.inl e => W_mat e x | Sum.inr r => Q r x
    refine ⟨V, ?_, ?_⟩
    · ext i j
      simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_sum_type]
      have h1 : (∑ e : E, star (W_mat e i) * W_mat e j) = P i j := by
        have hWW : W_matᴴ * W_mat = P := by
          calc W_matᴴ * W_mat = pinv * (A * Aᴴ) * pinv := by
                simp only [W_mat, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
                  hpinv_herm, Matrix.mul_assoc]
            _ = pinv * τ.mat * pinv := by rw [hA]
            _ = P := hpinv_mul_mat
        rw [← hWW]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
      have h2 : (∑ r : d, star (Q r i) * Q r j) = Q i j := by
        have hQQ : Qᴴ * Q = Q := by
          have hQh : Qᴴ = Q := by simp [Q, hP_herm]
          rw [hQh]; simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP_idem]; abel
        rw [← hQQ]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [h1, h2]; simp [Q, Matrix.sub_apply]
    · intro y x
      cases y with
      | inl e =>
        change (W_mat * τ.sqrtMat) e x = Aᴴ e x
        rw [show W_mat * τ.sqrtMat = Aᴴ by
          simp only [W_mat, Matrix.mul_assoc, hpinv_sqrt, hAH_P]]
      | inr r =>
        change (Q * τ.sqrtMat) r x = 0
        rw [hQ_sqrt, Matrix.zero_apply]
  obtain ⟨V₀, hV₀, hV₀_sq⟩ := hfactor (W.out false) A₀ hA₀
  obtain ⟨V₁, hV₁, hV₁_sq⟩ := hfactor (W.out true) A₁ hA₁
  let V : Matrix (Bool × (E ⊕ d)) (Bool × d) ℂ := Matrix.of fun p q ↦
    if p.1 = q.1 then (if p.1 = false then V₀ p.2 q.2 else V₁ p.2 q.2) else 0
  let ι : Matrix (Bool × (E ⊕ d)) (Bool × E) ℂ := Matrix.of fun p q ↦
    if p.1 = q.1 ∧ p.2 = Sum.inl q.2 then (1 : ℂ) else 0
  have hV_iso : Vᴴ * V = 1 := by
    ext ⟨b₁, x₁⟩ ⟨b₂, x₂⟩
    simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fintype.sum_bool]
    cases b₁ <;> cases b₂
    · simp only [↓reduceIte, Bool.true_eq_false, mul_zero, star_zero, Finset.sum_const_zero, add_zero,
        Prod.mk.injEq, true_and]
      have h := congr_fun (congr_fun hV₀ x₁) x₂
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
    · simp
    · simp
    · simp only [↓reduceIte, Bool.false_eq_true, mul_zero, star_zero, Finset.sum_const_zero, zero_add,
        Prod.mk.injEq, true_and]
      have h := congr_fun (congr_fun hV₁ x₁) x₂
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  have hι_iso : ιᴴ * ι = 1 := by
    ext ⟨b₁, e₁⟩ ⟨b₂, e₂⟩
    simp only [ι, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fintype.sum_sum_type]
    by_cases h : (b₁, e₁) = (b₂, e₂)
    · subst h
      rw [Finset.sum_eq_single b₁]
      · simp only [↓reduceIte, true_and, Sum.inl.injEq, reduceCtorEq, and_false, mul_zero,
          star_zero, Finset.sum_const_zero, add_zero]
        rw [Finset.sum_eq_single e₁]
        · simp
        · intro e _ he; simp [he]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro b _ hb; simp [hb]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · simp only [h, ↓reduceIte]
      apply Finset.sum_eq_zero; intro b _
      apply add_eq_zero_iff.mpr
      constructor
      · apply Finset.sum_eq_zero; intro e _
        by_cases h1 : b = b₁ ∧ e = e₁
        · rcases h1 with ⟨rfl, rfl⟩
          have hne : ¬ (b = b₂ ∧ e = e₂) := fun ⟨hb, he⟩ ↦ h (Prod.ext hb he)
          simp [hne]
        · simp [h1]
      · apply Finset.sum_eq_zero; intro r _; simp
  have hVG : V * gramFactor (W.out false) (W.out true) = ι * M₀ := by
    ext ⟨b, y⟩ x
    simp only [V, ι, M₀, gramFactor, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type,
      Fintype.sum_bool]
    cases b
    · simp only [↓reduceIte, Bool.true_eq_false, zero_mul, Finset.sum_const_zero, add_zero]
      have hL : (∑ r : d, V₀ y r * (((Real.sqrt 2 : ℂ)⁻¹) * (W.out false).sqrtMat r x)) =
          ((Real.sqrt 2 : ℂ)⁻¹) * (V₀ * (W.out false).sqrtMat) y x := by
        rw [Matrix.mul_apply, Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
      rw [hL, hV₀_sq y x]
      cases y with
      | inl e =>
        rw [Finset.sum_eq_single e]
        · simp
        · intro e' _ he'; simp [Ne.symm he']
        · intro hm; exact absurd (Finset.mem_univ _) hm
      | inr r => simp
    · simp only [↓reduceIte, Bool.false_eq_true, zero_mul, Finset.sum_const_zero, zero_add]
      have hL : (∑ r : d, V₁ y r * (((Real.sqrt 2 : ℂ)⁻¹) * (W.out true).sqrtMat r x)) =
          ((Real.sqrt 2 : ℂ)⁻¹) * (V₁ * (W.out true).sqrtMat) y x := by
        rw [Matrix.mul_apply, Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
      rw [hL, hV₁_sq y x]
      cases y with
      | inl e =>
        rw [Finset.sum_eq_single e]
        · simp
        · intro e' _ he'; simp [Ne.symm he']
        · intro hm; exact absurd (Finset.mem_univ _) hm
      | inr r => simp
  have hVZG : V * ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) *
      gramFactor (W.out false) (W.out true)) = ι * M₁ := by
    ext ⟨b, y⟩ x
    simp only [V, ι, M₁, pauliZTensorI, gramFactor, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_bool]
    cases b
    · simp only [↓reduceIte, Bool.true_eq_false, zero_mul, Finset.sum_const_zero, add_zero,
        ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ]
      have hL : (∑ r : d, V₀ y r * (((Real.sqrt 2 : ℂ)⁻¹) * (W.out false).sqrtMat r x)) =
          ((Real.sqrt 2 : ℂ)⁻¹) * (V₀ * (W.out false).sqrtMat) y x := by
        rw [Matrix.mul_apply, Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
      have hsimp : ∀ r : d, (∑ z : d, (if (false, r) = (false, z) then (1 : ℂ) else 0) *
          (((Real.sqrt 2 : ℂ)⁻¹) * (W.out false).sqrtMat z x)) +
          (∑ z : d, (if (false, r) = (true, z) then (1 : ℂ) else 0) *
          (((Real.sqrt 2 : ℂ)⁻¹) * (W.out true).sqrtMat z x)) =
          ((Real.sqrt 2 : ℂ)⁻¹) * (W.out false).sqrtMat r x := by
        intro r; simp [Prod.mk.injEq]
      simp_rw [hsimp]; rw [hL, hV₀_sq y x]
      cases y with
      | inl e =>
        rw [Finset.sum_eq_single e]
        · simp
        · intro e' _ he'; simp [Ne.symm he']
        · intro hm; exact absurd (Finset.mem_univ _) hm
      | inr r => simp
    · simp only [↓reduceIte, Bool.false_eq_true, zero_mul, Finset.sum_const_zero, zero_add]
      have hsimp : ∀ r : d, (∑ z : d, (if (true, r) = (false, z) then (-1 : ℂ) else 0) *
          (((Real.sqrt 2 : ℂ)⁻¹) * (W.out false).sqrtMat z x)) +
          (∑ z : d, (if (true, r) = (true, z) then (-1 : ℂ) else 0) *
          (((Real.sqrt 2 : ℂ)⁻¹) * (W.out true).sqrtMat z x)) =
          -(((Real.sqrt 2 : ℂ)⁻¹) * (W.out true).sqrtMat r x) := by
        intro r; simp [Prod.mk.injEq]
      simp_rw [hsimp]
      have hL : (∑ r : d, V₁ y r * -(((Real.sqrt 2 : ℂ)⁻¹) * (W.out true).sqrtMat r x)) =
          -((Real.sqrt 2 : ℂ)⁻¹) * (V₁ * (W.out true).sqrtMat) y x := by
        rw [Matrix.mul_apply, Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
      rw [hL, hV₁_sq y x]
      cases y with
      | inl e =>
        rw [Finset.sum_eq_single e]
        · simp
        · intro e' _ he'; simp [Ne.symm he']
        · intro hm; exact absurd (Finset.mem_univ _) hm
      | inr r => simp
  refine ⟨Bool × (E ⊕ d), inferInstance, inferInstance, V, ι, hV_iso, hι_iso, fun b ↦ ?_⟩
  cases b
  · change V * (gramFactor (W.out false) (W.out true) * (gramFactor (W.out false) (W.out true))ᴴ) * Vᴴ =
      ι * (M₀ * M₀ᴴ) * ιᴴ
    calc V * (gramFactor (W.out false) (W.out true) * (gramFactor (W.out false) (W.out true))ᴴ) * Vᴴ
        = (V * gramFactor (W.out false) (W.out true)) * (V * gramFactor (W.out false) (W.out true))ᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (ι * M₀) * (ι * M₀)ᴴ := by rw [hVG]
      _ = ι * (M₀ * M₀ᴴ) * ιᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · change V * ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) *
        (gramFactor (W.out false) (W.out true) * (gramFactor (W.out false) (W.out true))ᴴ) *
        star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)) * Vᴴ =
      ι * (M₁ * M₁ᴴ) * ιᴴ
    calc V * ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) *
          (gramFactor (W.out false) (W.out true) * (gramFactor (W.out false) (W.out true))ᴴ) *
          star (pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ)) * Vᴴ
        = (V * ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) * gramFactor (W.out false) (W.out true))) *
          (V * ((pauliZTensorI d : Matrix (Bool × d) (Bool × d) ℂ) * gramFactor (W.out false) (W.out true)))ᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
      _ = (ι * M₁) * (ι * M₁)ᴴ := by rw [hVZG]
      _ = ι * (M₁ * M₁ᴴ) * ιᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Proposition 2.2 (D3, Isometric Dual of `Pure(1 - 2p)`)**:
`Pure(1 - 2p)⊥` is equivalent up to output isometry (`IsoEquiv`) to `BSC(p)` for `p ∈ [0, 1/2]`. -/
theorem prop_2_2_D3_isoEquiv_pure (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (pureChannel (1 - 2 * p) (by linarith) (by linarith)).dual.IsoEquiv
      (bscChannel p hp0 (by linarith)) := by
  let f : ℝ := 1 - 2 * p
  let A₀ : Matrix Bool PUnit ℂ := Matrix.of fun b _ ↦
    if b = false then (Real.sqrt ((1 + f) / 2) : ℂ) else (Real.sqrt ((1 - f) / 2) : ℂ)
  let A₁ : Matrix Bool PUnit ℂ := Matrix.of fun b _ ↦
    if b = false then (Real.sqrt ((1 + f) / 2) : ℂ) else -(Real.sqrt ((1 - f) / 2) : ℂ)
  have hA₀ : A₀ * A₀ᴴ = ((pureChannel f (by linarith) (by linarith)).out false).mat := by
    ext i j; simp [A₀, pureChannel, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_unique]
  have hA₁ : A₁ * A₁ᴴ = ((pureChannel f (by linarith) (by linarith)).out true).mat := by
    ext i j; simp [A₁, pureChannel, pureState, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_unique]
  obtain ⟨γ, _, _, V₁, V₂, h1, h2, heq⟩ :=
    dual_isoEquiv_of_purification (pureChannel f (by linarith) (by linarith)) A₀ A₁ hA₀ hA₁
  -- Conjugate `W_E` on `Bool × PUnit` by Hadamard `H : Bool → Bool × PUnit` to get `bscChannel p`!
  let H : Matrix (Bool × PUnit) Bool ℂ := Matrix.of fun r c ↦
    ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = true ∧ c = true then -1 else 1)
  have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; push_cast; ring
  have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
  have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rwa [hstar2] at hsq2
  have hH_iso : Hᴴ * H = 1 := by
    ext i j
    simp only [H, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
    cases i <;> cases j <;> simp [star_mul', hstar2, hmul2] <;> ring
  have hH_mul : H * Hᴴ = 1 := by
    ext ⟨i, ⟨⟩⟩ ⟨j, ⟨⟩⟩
    simp only [H, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_bool]
    cases i <;> cases j <;> simp [star_mul', hstar2, hmul2] <;> ring
  have hM_bsc : ∀ b : Bool,
      H * ((bscChannel p hp0 (by linarith)).out b).mat * Hᴴ =
        (if b = false then
          (Matrix.of fun (r : Bool × PUnit) (x : Bool) ↦ ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x)) *
          (Matrix.of fun (r : Bool × PUnit) (x : Bool) ↦ ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else A₁ᴴ r.2 x))ᴴ
        else
          (Matrix.of fun (r : Bool × PUnit) (x : Bool) ↦ ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x)) *
          (Matrix.of fun (r : Bool × PUnit) (x : Bool) ↦ ((Real.sqrt 2 : ℂ)⁻¹) * (if r.1 = false then A₀ᴴ r.2 x else -A₁ᴴ r.2 x))ᴴ) := by
    have hsp1 : (Real.sqrt ((1 + f) / 2) : ℂ) * (Real.sqrt ((1 + f) / 2) : ℂ) = (((1 - p : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by dsimp only [f]; linarith)]
      congr 1; dsimp only [f]; ring
    have hsp2 : (Real.sqrt ((1 - f) / 2) : ℂ) * (Real.sqrt ((1 - f) / 2) : ℂ) = (p : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by dsimp only [f]; linarith)]
      congr 1; dsimp only [f]; ring
    intro b
    ext ⟨i, ⟨⟩⟩ ⟨j, ⟨⟩⟩
    cases b <;> cases i <;> cases j <;>
      simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, H, bscChannel, A₀, A₁,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diagonal_apply,
        Fintype.sum_bool, star_mul', star_neg, star_one, Complex.star_def, Complex.conj_ofReal,
        hstar2, mul_zero, zero_mul, add_zero, zero_add, mul_one, mul_neg, neg_mul, neg_neg] <;>
      (ring_nf; simp only [show ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) by rw [sq, hmul2],
        show (Real.sqrt ((1 + f) / 2) : ℂ) ^ 2 = ((1 - p : ℝ) : ℂ) by rw [sq, hsp1],
        show (Real.sqrt ((1 - f) / 2) : ℂ) ^ 2 = (p : ℂ) by rw [sq, hsp2]]; push_cast; ring)
  refine ⟨γ, inferInstance, inferInstance, V₁, V₂ * H, h1, ?_, fun b ↦ ?_⟩
  · calc (V₂ * H)ᴴ * (V₂ * H) = Hᴴ * ((V₂ᴴ * V₂) * H) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.one_mul, hH_iso]
  · rw [heq b]
    calc _ = V₂ * (H * ((bscChannel p hp0 (by linarith)).out b).mat * Hᴴ) * V₂ᴴ := by
          cases b <;> simpa using congr_arg (fun X ↦ V₂ * X * V₂ᴴ) (hM_bsc _).symm
      _ = (V₂ * H) * ((bscChannel p hp0 (by linarith)).out b).mat * (V₂ * H)ᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Proposition 2.2 (D3, Channel-Level Duality)**:
`BSC(p)⊥ ≃ Pure(1 - 2p)`, `Pure(1 - 2p)⊥ ≃ BSC(p)`, and `BEC(ε)⊥ ≃ BEC(1 - ε)` under
reversible CPTP channel equivalence (`ChannelEquiv`), implying the entropic equalities of
Proposition 2.2 (D3) as immediate corollaries. -/
theorem prop_2_2_D3_channelEquiv (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (bscChannel p hp0 (by linarith)).dual.ChannelEquiv
      (pureChannel (1 - 2 * p) (by linarith) (by linarith)) ∧
    (pureChannel (1 - 2 * p) (by linarith) (by linarith)).dual.ChannelEquiv
      (bscChannel p hp0 (by linarith)) ∧
    (becChannel ε hε0 hε1).dual.ChannelEquiv
      (becChannel (1 - ε) (by linarith) (by linarith)) := by
  have hpure := (prop_2_2_D3_isoEquiv_pure p hp0 hp1).toChannelEquiv
  refine ⟨?_, hpure, ?_⟩
  · -- Part 1: `BSC(p)⊥ ↔ Pure(1 - 2p)` via controlled-`X` + trace out `y`
    have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; push_cast; ring
    have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
    have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      rwa [hstar2] at hsq2
    -- Note: `BSC(p)(0) = diag(1-p, p)` and `BSC(p)(1) = diag(p, 1-p)`.
    -- In `BSC(p)⊥(b)`, the `y = false` block is `½ |φ_b⟩⟨φ_b|` (in the Hadamard basis) and
    -- the `y = true` block is `½ (X |φ_b⟩)(⟨φ_b| X)`.
    let Φ : CPTPMap (Bool × Bool) Bool :=
      { env := Bool
        fintypeEnv := inferInstance
        decEqEnv := inferInstance
        isom := Matrix.of fun (out_b, env_y) (in_b, in_y) ↦
          if env_y = in_y then
            ((Real.sqrt 2 : ℂ)⁻¹) * (if (if in_y = false then in_b else !in_b) = true ∧ out_b = true then -1 else 1)
          else 0
        isom_eq := by
          ext ⟨b₁, y₁⟩ ⟨b₂, y₂⟩
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
            Fintype.sum_prod_type, Fintype.sum_bool]
          cases y₁ <;> cases y₂ <;> cases b₁ <;> cases b₂ <;>
            simp [star_mul', hstar2, hmul2] <;> ring }
    let Ψ : CPTPMap Bool (Bool × Bool) :=
      { env := PUnit
        fintypeEnv := inferInstance
        decEqEnv := inferInstance
        isom := Matrix.of fun ((out_b, out_y), _) in_b ↦
          (1 / 2 : ℂ) * (if (if out_y = false then out_b else !out_b) = true ∧ in_b = true then -1 else 1)
        isom_eq := by
          ext i j
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
            Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
          cases i <;> cases j <;> simp <;> norm_num }
    have hsqrt_diag : ∀ (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (τ : DensityOp Bool),
        τ.mat = Matrix.diagonal (fun x : Bool ↦ if x = false then (a : ℂ) else (b : ℂ)) →
        τ.sqrtMat = Matrix.diagonal (fun x : Bool ↦ if x = false then (Real.sqrt a : ℂ) else (Real.sqrt b : ℂ)) := by
      intro a b ha hb τ hτ
      have hsp : τ.mat = ((1 : Matrix.unitaryGroup Bool ℂ) : Matrix Bool Bool ℂ) *
          Matrix.diagonal (Complex.ofReal ∘ fun x : Bool ↦ if x = false then a else b) *
          star ((1 : Matrix.unitaryGroup Bool ℂ) : Matrix Bool Bool ℂ) := by
        ext i j; simp only [hτ, Matrix.diagonal_apply, Function.comp_apply, OneMemClass.coe_one,
          Matrix.one_mul, star_one, Matrix.mul_one]; split_ifs <;> rfl
      have hfn := hermitian_func_eq τ.isHermitian (1 : Matrix.unitaryGroup Bool ℂ)
        (fun x : Bool ↦ if x = false then a else b) hsp Real.sqrt
      have h1 : τ.sqrtMat = (τ.isHermitian.eigenvectorUnitary : Matrix Bool Bool ℂ) *
          Matrix.diagonal (fun j ↦ (Real.sqrt (τ.isHermitian.eigenvalues j) : ℂ)) *
          star (τ.isHermitian.eigenvectorUnitary : Matrix Bool Bool ℂ) := rfl
      rw [h1, hfn]
      ext i j; simp only [OneMemClass.coe_one, Matrix.one_mul, star_one, Matrix.mul_one,
        Matrix.diagonal_apply]; split_ifs <;> simp_all
    have hsq0 : ((bscChannel p hp0 (by linarith)).out false).sqrtMat =
        Matrix.diagonal (fun x : Bool ↦ if x = false then (Real.sqrt (1 - p) : ℂ) else (Real.sqrt p : ℂ)) :=
      hsqrt_diag (1 - p) p (by linarith) hp0 _ rfl
    have hsq1 : ((bscChannel p hp0 (by linarith)).out true).sqrtMat =
        Matrix.diagonal (fun x : Bool ↦ if x = false then (Real.sqrt p : ℂ) else (Real.sqrt (1 - p) : ℂ)) :=
      hsqrt_diag p (1 - p) hp0 (by linarith) _ rfl
    have h1pf : (1 + (1 - 2 * p)) / 2 = 1 - p := by ring
    have h1mf : (1 - (1 - 2 * p)) / 2 = p := by ring
    have hmul_sq0 : (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) = ((1 - p : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
    have hmul_sq1 : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
    refine ⟨Φ, Ψ, ?_, ?_⟩
    · intro b
      ext i j
      simp only [Φ, CPTPMap.apply, CPTPMap.toLinearMap, partialTrace₂Mat, LinearMap.coe_mk,
        AddHom.coe_mk, CQChannel.dual, gramState, gramFactor, DensityOp.conjUnitary, pauliZTensorI,
        pureChannel, pureState, h1pf, h1mf, hsq0, hsq1,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diagonal_apply,
        Matrix.star_apply, Fintype.sum_prod_type, Fintype.sum_bool]
      cases b <;> cases i <;> cases j <;>
        (simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, Bool.not_false, Bool.not_true,
          and_self, and_true, and_false, true_and, false_and, mul_zero, zero_mul, add_zero, zero_add,
          mul_one, one_mul, mul_neg, neg_mul, neg_neg, star_mul', star_neg, star_one, star_zero,
          Complex.star_def, Complex.conj_ofReal, hstar2];
         ring_nf;
         simp only [show ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) by rw [sq, hmul2],
           show ((Real.sqrt 2 : ℂ)⁻¹) ^ 4 = (1 / 4 : ℂ) by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq, hmul2]; norm_num,
           show (Real.sqrt (1 - p) : ℂ) ^ 2 = ((1 - p : ℝ) : ℂ) by rw [sq, hmul_sq0],
           show (Real.sqrt p : ℂ) ^ 2 = (p : ℂ) by rw [sq, hmul_sq1]];
         push_cast; ring)
    · intro b
      ext ⟨b₁, y₁⟩ ⟨b₂, y₂⟩
      simp only [Ψ, CPTPMap.apply, CPTPMap.toLinearMap, partialTrace₂Mat, LinearMap.coe_mk,
        AddHom.coe_mk, CQChannel.dual, gramState, gramFactor, DensityOp.conjUnitary, pauliZTensorI,
        pureChannel, pureState, h1pf, h1mf, hsq0, hsq1,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diagonal_apply,
        Matrix.star_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
      cases b <;> cases b₁ <;> cases y₁ <;> cases b₂ <;> cases y₂ <;>
        (simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, Bool.not_false, Bool.not_true,
          and_self, and_true, and_false, true_and, false_and, mul_zero, zero_mul, add_zero, zero_add,
          mul_one, one_mul, mul_neg, neg_mul, neg_neg, star_mul', star_neg, star_one, star_zero,
          Complex.star_def, Complex.conj_ofReal, hstar2];
         ring_nf;
         simp only [show ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) by rw [sq, hmul2],
           show (Real.sqrt (1 - p) : ℂ) ^ 2 = ((1 - p : ℝ) : ℂ) by rw [sq, hmul_sq0],
           show (Real.sqrt p : ℂ) ^ 2 = (p : ℂ) by rw [sq, hmul_sq1]];
         push_cast; ring)
  · -- Part 3: `BEC(ε)⊥ ↔ BEC(1 - ε)`
    have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; push_cast; ring
    have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
      rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
    have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      rwa [hstar2] at hsq2
    -- Forward CPTP `Φ : Bool × Fin 3 → Fin 3`:
    -- `(b, 2)` is mapped via Hadamard to `0` (`|+⟩`) and `1` (`|-⟩`) with `env = 0`;
    -- `(b, 0)` and `(b, 1)` are mapped to erasure `2` with `env = (b, y)`.
    let Φ : CPTPMap (Bool × Fin 3) (Fin 3) :=
      { env := Bool × Fin 3
        fintypeEnv := inferInstance
        decEqEnv := inferInstance
        isom := Matrix.of fun (out_k, (eb, ey)) (in_b, in_y) ↦
          if in_y = 2 then
            if eb = false ∧ ey = 2 then
              match out_k with
              | 0 => ((Real.sqrt 2 : ℂ)⁻¹)
              | 1 => ((Real.sqrt 2 : ℂ)⁻¹) * (if in_b = false then 1 else -1)
              | 2 => 0
            else 0
          else
            if out_k = 2 ∧ eb = in_b ∧ ey = in_y then 1 else 0
        isom_eq := by
          ext ⟨b₁, y₁⟩ ⟨b₂, y₂⟩
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
            Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three]
          fin_cases y₁ <;> fin_cases y₂ <;> cases b₁ <;> cases b₂ <;>
            simp [star_mul', hstar2, hmul2] <;> ring }
    -- Backward CPTP `Ψ : Fin 3 → Bool × Fin 3`:
    -- `0 ↦ |+⟩ ⊗ |2⟩`, `1 ↦ |-⟩ ⊗ |2⟩`, `2 ↦ ½ (|0,0⟩⟨0,0| + |1,1⟩⟨1,1|)` (via `env = Bool`).
    let Ψ : CPTPMap (Fin 3) (Bool × Fin 3) :=
      { env := Bool
        fintypeEnv := inferInstance
        decEqEnv := inferInstance
        isom := Matrix.of fun ((out_b, out_y), e) in_k ↦
          match in_k with
          | 0 => if e = false ∧ out_y = 2 then ((Real.sqrt 2 : ℂ)⁻¹) else 0
          | 1 => if e = false ∧ out_y = 2 then ((Real.sqrt 2 : ℂ)⁻¹) * (if out_b = false then 1 else -1) else 0
          | 2 => if (e = false ∧ out_b = false ∧ out_y = 0) ∨ (e = true ∧ out_b = true ∧ out_y = 1)
                 then ((Real.sqrt 2 : ℂ)⁻¹) else 0
        isom_eq := by
          ext i j
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
            Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three]
          fin_cases i <;> fin_cases j <;> simp [star_mul', hstar2, hmul2] <;> ring }
    have hsqrt_diag3 : ∀ (v : Fin 3 → ℝ) (hv : ∀ i, 0 ≤ v i) (τ : DensityOp (Fin 3)),
        τ.mat = Matrix.diagonal (fun i : Fin 3 ↦ (v i : ℂ)) →
        τ.sqrtMat = Matrix.diagonal (fun i : Fin 3 ↦ (Real.sqrt (v i) : ℂ)) := by
      intro v hv τ hτ
      have hsp : τ.mat = ((1 : Matrix.unitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) *
          Matrix.diagonal (Complex.ofReal ∘ v) *
          star ((1 : Matrix.unitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) := by
        ext i j; simp only [hτ, Matrix.diagonal_apply, Function.comp_apply, OneMemClass.coe_one,
          Matrix.one_mul, star_one, Matrix.mul_one]; split_ifs <;> rfl
      have hfn := hermitian_func_eq τ.isHermitian (1 : Matrix.unitaryGroup (Fin 3) ℂ) v hsp Real.sqrt
      have h1 : τ.sqrtMat = (τ.isHermitian.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ) *
          Matrix.diagonal (fun j ↦ (Real.sqrt (τ.isHermitian.eigenvalues j) : ℂ)) *
          star (τ.isHermitian.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ) := rfl
      rw [h1, hfn]
      ext i j; simp only [OneMemClass.coe_one, Matrix.one_mul, star_one, Matrix.mul_one,
        Matrix.diagonal_apply]; split_ifs <;> simp_all
    have hsq0 : ((becChannel ε hε0 hε1).out false).sqrtMat =
        Matrix.diagonal (fun i : Fin 3 ↦ match i with | 0 => (Real.sqrt (1 - ε) : ℂ) | 1 => 0 | 2 => (Real.sqrt ε : ℂ)) := by
      have h := hsqrt_diag3 ![1 - ε, 0, ε] (fun i ↦ by fin_cases i <;> simp <;> linarith)
        ((becChannel ε hε0 hε1).out false) (by ext i j; fin_cases i <;> fin_cases j <;> simp [becChannel, Matrix.diagonal_apply])
      rw [h]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]
    have hsq1 : ((becChannel ε hε0 hε1).out true).sqrtMat =
        Matrix.diagonal (fun i : Fin 3 ↦ match i with | 0 => 0 | 1 => (Real.sqrt (1 - ε) : ℂ) | 2 => (Real.sqrt ε : ℂ)) := by
      have h := hsqrt_diag3 ![0, 1 - ε, ε] (fun i ↦ by fin_cases i <;> simp <;> linarith)
        ((becChannel ε hε0 hε1).out true) (by ext i j; fin_cases i <;> fin_cases j <;> simp [becChannel, Matrix.diagonal_apply])
      rw [h]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]
    have hmul_e : (Real.sqrt ε : ℂ) * (Real.sqrt ε : ℂ) = (ε : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hε0]
    have hmul_1me : (Real.sqrt (1 - ε) : ℂ) * (Real.sqrt (1 - ε) : ℂ) = ((1 - ε : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
    refine ⟨Φ, Ψ, ?_, ?_⟩
    · intro b
      ext i j
      simp only [Φ, CPTPMap.apply, CPTPMap.toLinearMap, partialTrace₂Mat, LinearMap.coe_mk,
        AddHom.coe_mk, CQChannel.dual, gramState, gramFactor, DensityOp.conjUnitary, pauliZTensorI,
        becChannel, hsq0, hsq1,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diagonal_apply,
        Matrix.star_apply, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three]
      cases b <;> fin_cases i <;> fin_cases j <;>
        (simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, Fin.isValue,
          Fin.reduceEq, and_self, and_true, and_false, true_and, false_and, mul_zero, zero_mul,
          add_zero, zero_add, mul_one, one_mul, mul_neg, neg_mul, neg_neg, star_mul', star_neg,
          star_one, star_zero, Complex.star_def, Complex.conj_ofReal, hstar2];
         ring_nf;
         simp only [show ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) by rw [sq, hmul2],
           show ((Real.sqrt 2 : ℂ)⁻¹) ^ 4 = (1 / 4 : ℂ) by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq, hmul2]; norm_num,
           show (Real.sqrt ε : ℂ) ^ 2 = (ε : ℂ) by rw [sq, hmul_e],
           show (Real.sqrt (1 - ε) : ℂ) ^ 2 = ((1 - ε : ℝ) : ℂ) by rw [sq, hmul_1me]];
         push_cast; ring)
    · intro b
      ext ⟨b₁, y₁⟩ ⟨b₂, y₂⟩
      simp only [Ψ, CPTPMap.apply, CPTPMap.toLinearMap, partialTrace₂Mat, LinearMap.coe_mk,
        AddHom.coe_mk, CQChannel.dual, gramState, gramFactor, DensityOp.conjUnitary, pauliZTensorI,
        becChannel, hsq0, hsq1,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diagonal_apply,
        Matrix.star_apply, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three]
      cases b <;> cases b₁ <;> cases b₂ <;> fin_cases y₁ <;> fin_cases y₂ <;>
        (simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, Fin.isValue,
          Fin.reduceEq, and_self, and_true, and_false, true_and, false_and, or_self, or_true,
          or_false, true_or, false_or, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul,
          mul_neg, neg_mul, neg_neg, star_mul', star_neg, star_one, star_zero, Complex.star_def,
          Complex.conj_ofReal, hstar2];
         ring_nf;
         simp only [show ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) by rw [sq, hmul2],
           show (Real.sqrt ε : ℂ) ^ 2 = (ε : ℂ) by rw [sq, hmul_e],
           show (Real.sqrt (1 - ε) : ℂ) ^ 2 = ((1 - ε : ℝ) : ℂ) by rw [sq, hmul_1me]];
         push_cast; ring)

/-- **Proposition 2.2 (D2, Channel-Level Check/Variable Duality)**:
`(W₁ ⊠ W₂)⊥ ≃ W₁⊥ ⊛ W₂⊥` under reversible CPTP channel equivalence (`ChannelEquiv`),
implying `H((W₁ ⊠ W₂)⊥) = H(W₁⊥ ⊛ W₂⊥)` as an immediate corollary. -/
theorem prop_2_2_D2_check_channelEquiv (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    (CQChannel.checkCombine W₁ W₂).dual.ChannelEquiv
      (CQChannel.varCombine W₁.dual W₂.dual) := by
  let ρ₀ := W₁.out false
  let ρ₁ := W₁.out true
  let σ₀ := W₂.out false
  let σ₁ := W₂.out true
  have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; push_cast; ring
  have hstar2 : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal]
  have hmul2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rwa [hstar2] at hsq2
  -- Purify `(W₁ ⊠ W₂).out false` and `(W₁ ⊠ W₂).out true` with `E = Bool × (d₁ × d₂)`
  let A₀ : Matrix (d₁ × d₂) (Bool × (d₁ × d₂)) ℂ := Matrix.of fun (i₁, i₂) (v, (j₁, j₂)) ↦
    ((Real.sqrt 2 : ℂ)⁻¹) * (if v = false then ρ₀.sqrtMat i₁ j₁ * σ₀.sqrtMat i₂ j₂
      else ρ₁.sqrtMat i₁ j₁ * σ₁.sqrtMat i₂ j₂)
  let A₁ : Matrix (d₁ × d₂) (Bool × (d₁ × d₂)) ℂ := Matrix.of fun (i₁, i₂) (v, (j₁, j₂)) ↦
    ((Real.sqrt 2 : ℂ)⁻¹) * (if v = false then ρ₁.sqrtMat i₁ j₁ * σ₀.sqrtMat i₂ j₂
      else ρ₀.sqrtMat i₁ j₁ * σ₁.sqrtMat i₂ j₂)
  have hsq_prod : ∀ (τ : DensityOp d₁) (η : DensityOp d₂) (i₁ j₁ : d₁) (i₂ j₂ : d₂),
      (∑ k₁ : d₁, ∑ k₂ : d₂, (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) *
        star (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂)) = τ.mat i₁ j₁ * η.mat i₂ j₂ := by
    intro τ η i₁ j₁ i₂ j₂
    have h1 : (∑ k₁ : d₁, τ.sqrtMat i₁ k₁ * star (τ.sqrtMat j₁ k₁)) = τ.mat i₁ j₁ := by
      have hm := congr_fun (congr_fun τ.sqrtMat_mul_self i₁) j₁
      rw [← hm, Matrix.mul_apply]; apply Finset.sum_congr rfl; intro k _; congr 1
      have hh := congr_fun (congr_fun τ.sqrtMat_isHermitian.eq k) j₁
      simpa [Matrix.conjTranspose_apply] using hh.symm
    have h2 : (∑ k₂ : d₂, η.sqrtMat i₂ k₂ * star (η.sqrtMat j₂ k₂)) = η.mat i₂ j₂ := by
      have hm := congr_fun (congr_fun η.sqrtMat_mul_self i₂) j₂
      rw [← hm, Matrix.mul_apply]; apply Finset.sum_congr rfl; intro k _; congr 1
      have hh := congr_fun (congr_fun η.sqrtMat_isHermitian.eq k) j₂
      simpa [Matrix.conjTranspose_apply] using hh.symm
    rw [← h1, ← h2, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k₁ _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k₂ _
    simp only [star_mul']; ring
  have hA₀ : A₀ * A₀ᴴ = ((CQChannel.checkCombine W₁ W₂).out false).mat := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [A₀, CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Bool.not_false, Bool.not_true, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul,
      Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false]
    have hpull : ∀ (τ : DensityOp d₁) (η : DensityOp d₂),
        (∑ k₁ : d₁, ∑ k₂ : d₂, ((Real.sqrt 2 : ℂ)⁻¹) * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) *
          star (((Real.sqrt 2 : ℂ)⁻¹) * (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂))) =
        (1 / 2 : ℂ) * (τ.mat i₁ j₁ * η.mat i₂ j₂) := by
      intro τ η; rw [← hsq_prod τ η i₁ j₁ i₂ j₂, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k₁ _; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k₂ _; simp only [star_mul', hstar2]
      calc _ = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
            ((τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂))) := by ring
        _ = _ := by rw [hmul2]
    rw [hpull ρ₀ σ₀, hpull ρ₁ σ₁]; push_cast; ring
  have hA₁ : A₁ * A₁ᴴ = ((CQChannel.checkCombine W₁ W₂).out true).mat := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [A₁, CQChannel.checkCombine, DensityOp.midpoint, DensityOp.mix, DensityOp.tensor,
      Bool.not_false, Bool.not_true, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul,
      Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false]
    have hpull : ∀ (τ : DensityOp d₁) (η : DensityOp d₂),
        (∑ k₁ : d₁, ∑ k₂ : d₂, ((Real.sqrt 2 : ℂ)⁻¹) * (τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) *
          star (((Real.sqrt 2 : ℂ)⁻¹) * (τ.sqrtMat j₁ k₁ * η.sqrtMat j₂ k₂))) =
        (1 / 2 : ℂ) * (τ.mat i₁ j₁ * η.mat i₂ j₂) := by
      intro τ η; rw [← hsq_prod τ η i₁ j₁ i₂ j₂, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k₁ _; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k₂ _; simp only [star_mul', hstar2]
      calc _ = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
            ((τ.sqrtMat i₁ k₁ * η.sqrtMat i₂ k₂) * (star (τ.sqrtMat j₁ k₁) * star (η.sqrtMat j₂ k₂))) := by ring
        _ = _ := by rw [hmul2]
    rw [hpull ρ₁ σ₀, hpull ρ₀ σ₁]; push_cast; ring
  have hstep1 := (dual_isoEquiv_of_purification (CQChannel.checkCombine W₁ W₂) A₀ A₁ hA₀ hA₁).toChannelEquiv
  -- Now map `W_E` on `Bool × (Bool × (d₁ × d₂))` to `varCombine W₁.dual W₂.dual` on
  -- `Bool × ((Bool × d₁) × (Bool × d₂))` via:
  -- 1. CNOT permutation `(u, v, j₁, j₂) ↦ ((u ⊕ v, j₁), (v, j₂))` giving `W₁⊥(b) ⊗ W₂⊥(b)`,
  -- 2. Tensor with `I/2` + controlled-`(Z₁ ⊗ I₂)` giving `(W₁⊥ ⊛ W₂⊥)(b)`!
  -- Combine both into one explicit CPTP pair `Φ₂, Ψ₂`!
  let Φ₂ : CPTPMap (Bool × (Bool × (d₁ × d₂))) (Bool × ((Bool × d₁) × (Bool × d₂))) :=
    { env := Bool
      fintypeEnv := inferInstance
      decEqEnv := inferInstance
      isom := Matrix.of fun (c, ((w₁, j₁), (w₂, j₂)), e) (u, (v, (r₁, r₂))) ↦
        if e = c ∧ u = xor w₁ w₂ ∧ v = w₂ ∧ r₁ = j₁ ∧ r₂ = j₂ then
          ((Real.sqrt 2 : ℂ)⁻¹) * (if c = true ∧ w₁ = true then -1 else 1)
        else 0
      isom_eq := by
        ext ⟨u₁, v₁, r₁, s₁⟩ ⟨u₂, v₂, r₂, s₂⟩
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
          Fintype.sum_prod_type]
        by_cases h : (u₁, (v₁, (r₁, s₁))) = (u₂, (v₂, (r₂, s₂)))
        · subst h
          simp only [↓reduceIte]
          calc ∑ c : Bool, ∑ w₁ : Bool, ∑ j₁ : d₁, ∑ w₂ : Bool, ∑ j₂ : d₂, ∑ e : Bool,
                star (if e = c ∧ u₁ = xor w₁ w₂ ∧ v₁ = w₂ ∧ r₁ = j₁ ∧ s₁ = j₂ then
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if c = true ∧ w₁ = true then -1 else 1) else 0) *
                (if e = c ∧ u₁ = xor w₁ w₂ ∧ v₁ = w₂ ∧ r₁ = j₁ ∧ s₁ = j₂ then
                  ((Real.sqrt 2 : ℂ)⁻¹) * (if c = true ∧ w₁ = true then -1 else 1) else 0)
              = ∑ c : Bool, (1 / 2 : ℂ) := by
                apply Finset.sum_congr rfl; intro c _
                rw [Finset.sum_eq_single (xor u₁ v₁)]
                · rw [Finset.sum_eq_single r₁]
                  · rw [Finset.sum_eq_single v₁]
                    · rw [Finset.sum_eq_single s₁]
                      · rw [Finset.sum_eq_single c]
                        · have hx : u₁ = xor (xor u₁ v₁) v₁ := by cases u₁ <;> cases v₁ <;> decide
                          simp only [hx, and_self, ↓reduceIte, star_mul', hstar2]
                          cases c <;> cases xor u₁ v₁ <;> simp [hmul2]
                        · intro e _ he; simp [he]
                        · intro hm; exact absurd (Finset.mem_univ _) hm
                      · intro j₂ _ hj₂; simp [Ne.symm hj₂]
                      · intro hm; exact absurd (Finset.mem_univ _) hm
                    · intro w₂ _ hw₂; simp [Ne.symm hw₂]
                    · intro hm; exact absurd (Finset.mem_univ _) hm
                  · intro j₁ _ hj₁; simp [Ne.symm hj₁]
                  · intro hm; exact absurd (Finset.mem_univ _) hm
                · intro w₁ _ hw₁
                  apply Finset.sum_eq_zero; intro j₁ _
                  apply Finset.sum_eq_zero; intro w₂ _
                  apply Finset.sum_eq_zero; intro j₂ _
                  apply Finset.sum_eq_zero; intro e _
                  have hne : ¬ (u₁ = xor w₁ w₂ ∧ v₁ = w₂) := by
                    rintro ⟨hu, hv⟩; subst hv; apply hw₁
                    cases u₁ <;> cases w₁ <;> cases w₂ <;> simp_all
                  by_cases hcond : e = c ∧ u₁ = xor w₁ w₂ ∧ v₁ = w₂ ∧ r₁ = j₁ ∧ s₁ = j₂
                  · exact absurd ⟨hcond.2.1, hcond.2.2.1⟩ hne
                  · simp [hcond]
                · intro hm; exact absurd (Finset.mem_univ _) hm
            _ = 1 := by simp [Fintype.sum_bool]; norm_num
        · simp only [h, ↓reduceIte]
          apply Finset.sum_eq_zero; intro c _
          apply Finset.sum_eq_zero; intro w₁ _
          apply Finset.sum_eq_zero; intro j₁ _
          apply Finset.sum_eq_zero; intro w₂ _
          apply Finset.sum_eq_zero; intro j₂ _
          apply Finset.sum_eq_zero; intro e _
          by_cases h1 : e = c ∧ u₁ = xor w₁ w₂ ∧ v₁ = w₂ ∧ r₁ = j₁ ∧ s₁ = j₂
          · have h2 : ¬ (e = c ∧ u₂ = xor w₁ w₂ ∧ v₂ = w₂ ∧ r₂ = j₁ ∧ s₂ = j₂) := by
              rintro ⟨_, hu, hv, hr, hs⟩
              apply h
              rw [h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2, hu, hv, hr, hs]
            simp [h2]
          · simp [h1] }
  let Ψ₂ : CPTPMap (Bool × ((Bool × d₁) × (Bool × d₂))) (Bool × (Bool × (d₁ × d₂))) :=
    { env := Bool
      fintypeEnv := inferInstance
      decEqEnv := inferInstance
      isom := Matrix.of fun ((u, (v, (r₁, r₂))), e) (c, ((w₁, j₁), (w₂, j₂))) ↦
        if e = c ∧ u = xor w₁ w₂ ∧ v = w₂ ∧ r₁ = j₁ ∧ r₂ = j₂ then
          (if c = true ∧ w₁ = true then -1 else 1)
        else 0
      isom_eq := by
        ext ⟨c₁, ⟨w₁, j₁⟩, ⟨w₂, j₂⟩⟩ ⟨c₂, ⟨w₁', j₁'⟩, ⟨w₂', j₂'⟩⟩
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
          Fintype.sum_prod_type]
        by_cases h : (c₁, ((w₁, j₁), (w₂, j₂))) = (c₂, ((w₁', j₁'), (w₂', j₂')))
        · subst h
          simp only [↓reduceIte]
          rw [Finset.sum_eq_single (xor w₁ w₂)]
          · rw [Finset.sum_eq_single w₂]
            · rw [Finset.sum_eq_single j₁]
              · rw [Finset.sum_eq_single j₂]
                · rw [Finset.sum_eq_single c₁]
                  · cases c₁ <;> cases w₁ <;> simp
                  · intro e _ he; simp [he]
                  · intro hm; exact absurd (Finset.mem_univ _) hm
                · intro r₂ _ hr₂; simp [hr₂]
                · intro hm; exact absurd (Finset.mem_univ _) hm
              · intro r₁ _ hr₁; simp [hr₁]
              · intro hm; exact absurd (Finset.mem_univ _) hm
            · intro v _ hv; simp [hv]
            · intro hm; exact absurd (Finset.mem_univ _) hm
          · intro u _ hu; simp [hu]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        · simp only [h, ↓reduceIte]
          apply Finset.sum_eq_zero; intro u _
          apply Finset.sum_eq_zero; intro v _
          apply Finset.sum_eq_zero; intro r₁ _
          apply Finset.sum_eq_zero; intro r₂ _
          apply Finset.sum_eq_zero; intro e _
          by_cases h1 : e = c₁ ∧ u = xor w₁ w₂ ∧ v = w₂ ∧ r₁ = j₁ ∧ r₂ = j₂
          · have h2 : ¬ (e = c₂ ∧ u = xor w₁' w₂' ∧ v = w₂' ∧ r₁ = j₁' ∧ r₂ = j₂') := by
              rintro ⟨he, hu, hv, hr1, hr2⟩
              apply h
              have hc : c₁ = c₂ := h1.1.symm.trans he
              have hw2 : w₂ = w₂' := h1.2.2.1.symm.trans hv
              have hw1 : w₁ = w₁' := by
                have hx := h1.2.1.symm.trans hu
                rw [hw2] at hx; cases w₁ <;> cases w₁' <;> cases w₂' <;> simp_all
              have hj1 : j₁ = j₁' := h1.2.2.2.1.symm.trans hr1
              have hj2 : j₂ = j₂' := h1.2.2.2.2.symm.trans hr2
              subst hc; subst hw1; subst hw2; subst hj1; subst hj2; rfl
            simp [h2]
          · simp [h1] }
  refine hstep1.trans ⟨Φ₂, Ψ₂, ?_, ?_⟩
  · -- Verify `Φ₂(W_E(b)) = (W₁⊥ ⊛ W₂⊥)(b)`
    intro b
    ext ⟨c₁, ⟨w₁, j₁⟩, ⟨w₂, j₂⟩⟩ ⟨c₂, ⟨w₁', j₁'⟩, ⟨w₂', j₂'⟩⟩
    have hM_entry : ∀ (u₁ u₂ v₁ v₂ : Bool) (r₁ r₁' : d₁) (r₂ r₂' : d₂),
        ((if b = false then
          (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) *
          (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ
        else
          (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) *
          (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ)
          (u₁, (v₁, (r₁, r₂))) (u₂, (v₂, (r₁', r₂')))) =
        (if b = false then (1 : ℂ) else (if u₁ = false then 1 else -1) * (if u₂ = false then 1 else -1)) *
          ((W₁.dual.out false).mat (xor u₁ v₁, r₁) (xor u₂ v₂, r₁') *
           (W₂.dual.out false).mat (v₁, r₂) (v₂, r₂')) := by
      intro u₁ u₂ v₁ v₂ r₁ r₁' r₂ r₂'
      have hA_ent : ∀ (u v : Bool) (x₁ : d₁) (x₂ : d₂) (y₁ : d₁) (y₂ : d₂),
          (if u = false then A₀ᴴ (v, (y₁, y₂)) (x₁, x₂) else A₁ᴴ (v, (y₁, y₂)) (x₁, x₂)) =
          ((Real.sqrt 2 : ℂ)⁻¹) *
            ((if xor u v = false then ρ₀.sqrtMat y₁ x₁ else ρ₁.sqrtMat y₁ x₁) *
             (if v = false then σ₀.sqrtMat y₂ x₂ else σ₁.sqrtMat y₂ x₂)) := by
        intro u v x₁ x₂ y₁ y₂
        simp only [A₀, A₁, Matrix.conjTranspose_apply, Matrix.of_apply]
        cases u <;> cases v <;>
          simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, Bool.xor_false, Bool.xor_true,
            Bool.not_false, Bool.not_true, star_mul', hstar2] <;>
          (have hr0 := congr_fun (congr_fun ρ₀.sqrtMat_isHermitian.eq y₁) x₁;
           have hr1 := congr_fun (congr_fun ρ₁.sqrtMat_isHermitian.eq y₁) x₁;
           have hs0 := congr_fun (congr_fun σ₀.sqrtMat_isHermitian.eq y₂) x₂;
           have hs1 := congr_fun (congr_fun σ₁.sqrtMat_isHermitian.eq y₂) x₂;
           simp only [Matrix.conjTranspose_apply] at hr0 hr1 hs0 hs1;
           try rw [hr0]; try rw [hr1]; try rw [hs0]; try rw [hs1]; ring)
      have hprod : (∑ x₁ : d₁, ∑ x₂ : d₂,
          (((Real.sqrt 2 : ℂ)⁻¹) * (if u₁ = false then A₀ᴴ (v₁, (r₁, r₂)) (x₁, x₂) else A₁ᴴ (v₁, (r₁, r₂)) (x₁, x₂))) *
          star (((Real.sqrt 2 : ℂ)⁻¹) * (if u₂ = false then A₀ᴴ (v₂, (r₁', r₂')) (x₁, x₂) else A₁ᴴ (v₂, (r₁', r₂')) (x₁, x₂)))) =
          (W₁.dual.out false).mat (xor u₁ v₁, r₁) (xor u₂ v₂, r₁') *
          (W₂.dual.out false).mat (v₁, r₂) (v₂, r₂') := by
        simp_rw [hA_ent]
        simp only [CQChannel.dual, gramState, gramFactor, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x₁ _
        apply Finset.sum_congr rfl; intro x₂ _
        simp only [star_mul', hstar2]; ring
      cases b
      · simp only [↓reduceIte, one_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Fintype.sum_prod_type]
        exact hprod
      · simp only [Bool.true_eq_false, ↓reduceIte, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.of_apply, Fintype.sum_prod_type]
        rw [← hprod, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x₁ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x₂ _
        cases u₁ <;> cases u₂ <;> simp [star_mul', star_neg] <;> ring
    simp only [Φ₂, CPTPMap.apply, CPTPMap.toLinearMap, partialTrace₂Mat, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type]
    -- Collapse sums on LHS using the Kronecker deltas in `Φ₂.isom`
    have hLHS : (∑ e : Bool, ∑ u₂ : Bool, ∑ v₂ : Bool, ∑ r₁' : d₁, ∑ r₂' : d₂,
        (∑ u₁ : Bool, ∑ v₁ : Bool, ∑ r₁ : d₁, ∑ r₂ : d₂,
          (if e = c₁ ∧ u₁ = xor w₁ w₂ ∧ v₁ = w₂ ∧ r₁ = j₁ ∧ r₂ = j₂ then
            ((Real.sqrt 2 : ℂ)⁻¹) * (if c₁ = true ∧ w₁ = true then -1 else 1) else 0) *
          (if b = false then
            (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
              ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) *
            (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
              ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ
          else
            (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
              ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) *
            (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
              ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ)
            (u₁, (v₁, (r₁, r₂))) (u₂, (v₂, (r₁', r₂')))) *
        star (if e = c₂ ∧ u₂ = xor w₁' w₂' ∧ v₂ = w₂' ∧ r₁' = j₁' ∧ r₂' = j₂' then
          ((Real.sqrt 2 : ℂ)⁻¹) * (if c₂ = true ∧ w₁' = true then -1 else 1) else 0)) =
      if c₁ = c₂ then
        (1 / 2 : ℂ) * (if c₁ = true ∧ w₁ = true then -1 else 1) *
          (if c₂ = true ∧ w₁' = true then -1 else 1) *
          ((if b = false then (1 : ℂ) else (if xor w₁ w₂ = false then 1 else -1) * (if xor w₁' w₂' = false then 1 else -1)) *
            ((W₁.dual.out false).mat (w₁, j₁) (w₁', j₁') * (W₂.dual.out false).mat (w₂, j₂) (w₂', j₂')))
      else 0 := by
      rw [Finset.sum_eq_single c₁]
      · rw [Finset.sum_eq_single (xor w₁' w₂')]
        · rw [Finset.sum_eq_single w₂']
          · rw [Finset.sum_eq_single j₁']
            · rw [Finset.sum_eq_single j₂']
              · rw [Finset.sum_eq_single (xor w₁ w₂)]
                · rw [Finset.sum_eq_single w₂]
                  · rw [Finset.sum_eq_single j₁]
                    · rw [Finset.sum_eq_single j₂]
                      · rw [hM_entry]
                        have hx1 : xor (xor w₁ w₂) w₂ = w₁ := by cases w₁ <;> cases w₂ <;> decide
                        have hx2 : xor (xor w₁' w₂') w₂' = w₁' := by cases w₁' <;> cases w₂' <;> decide
                        rw [hx1, hx2]
                        by_cases hc : c₁ = c₂
                        · subst hc
                          simp only [↓reduceIte, and_self, star_mul', hstar2]
                          have hs : star (if c₁ = true ∧ w₁' = true then (-1 : ℂ) else 1) =
                              if c₁ = true ∧ w₁' = true then (-1 : ℂ) else 1 := by
                            cases c₁ <;> cases w₁' <;> simp
                          rw [hs]
                          calc _ = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) *
                                ((if c₁ = true ∧ w₁ = true then (-1 : ℂ) else 1) *
                                 (if c₁ = true ∧ w₁' = true then (-1 : ℂ) else 1) *
                                 ((if b = false then (1 : ℂ) else
                                   (if xor w₁ w₂ = false then 1 else -1) * (if xor w₁' w₂' = false then 1 else -1)) *
                                  ((W₁.dual.out false).mat (w₁, j₁) (w₁', j₁') *
                                   (W₂.dual.out false).mat (w₂, j₂) (w₂', j₂')))) := by ring
                            _ = _ := by rw [hmul2]; ring
                        · simp [hc]
                      · intro r₂ _ hr₂; simp [hr₂]
                      · intro hm; exact absurd (Finset.mem_univ _) hm
                    · intro r₁ _ hr₁; simp [hr₁]
                    · intro hm; exact absurd (Finset.mem_univ _) hm
                  · intro v₁ _ hv₁; simp [hv₁]
                  · intro hm; exact absurd (Finset.mem_univ _) hm
                · intro u₁ _ hu₁; simp [hu₁]
                · intro hm; exact absurd (Finset.mem_univ _) hm
              · intro r₂' _ hr₂'; simp [hr₂']
              · intro hm; exact absurd (Finset.mem_univ _) hm
            · intro r₁' _ hr₁'; simp [hr₁']
            · intro hm; exact absurd (Finset.mem_univ _) hm
          · intro v₂ _ hv₂; simp [hv₂]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        · intro u₂ _ hu₂; simp [hu₂]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro e _ he; simp [he]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    -- Match `hLHS` with `(CQChannel.varCombine W₁.dual W₂.dual).out b`
    change _ = ((CQChannel.varCombine W₁.dual W₂.dual).out b).mat (c₁, ((w₁, j₁), (w₂, j₂))) (c₂, ((w₁', j₁'), (w₂', j₂')))
    have hmatch : (∑ e : Bool, ∑ u₂ : Bool, ∑ v₂ : Bool, ∑ r₁' : d₁, ∑ r₂' : d₂,
        (∑ u₁ : Bool, ∑ v₁ : Bool, ∑ r₁ : d₁, ∑ r₂ : d₂,
          (if e = c₁ ∧ u₁ = xor w₁ w₂ ∧ v₁ = w₂ ∧ r₁ = j₁ ∧ r₂ = j₂ then
            ((Real.sqrt 2 : ℂ)⁻¹) * (if c₁ = true ∧ w₁ = true then -1 else 1) else 0) *
          (if b = false then
            (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
              ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) *
            (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
              ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ
          else
            (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
              ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) *
            (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
              ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ)
            (u₁, (v₁, (r₁, r₂))) (u₂, (v₂, (r₁', r₂')))) *
        star (if e = c₂ ∧ u₂ = xor w₁' w₂' ∧ v₂ = w₂' ∧ r₁' = j₁' ∧ r₂' = j₂' then
          ((Real.sqrt 2 : ℂ)⁻¹) * (if c₂ = true ∧ w₁' = true then -1 else 1) else 0)) =
      ((CQChannel.varCombine W₁.dual W₂.dual).out b).mat (c₁, ((w₁, j₁), (w₂, j₂))) (c₂, ((w₁', j₁'), (w₂', j₂'))) := by
      rw [hLHS]
      simp only [CQChannel.varCombine, CQChannel.ketBraBool, DensityOp.midpoint, DensityOp.mix,
        DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
        Matrix.of_apply, Complex.real_smul]
      have hZ1 : ∀ (a a' : Bool) (x x' : d₁),
          (W₁.dual.out true).mat (a, x) (a', x') =
          (if a = false then (1 : ℂ) else -1) * (W₁.dual.out false).mat (a, x) (a', x') *
          (if a' = false then (1 : ℂ) else -1) := by
        intro a a' x x'
        simp only [CQChannel.dual, DensityOp.conjUnitary, pauliZTensorI, Matrix.mul_apply,
          Matrix.diagonal_apply, Matrix.star_apply]
        rw [Finset.sum_eq_single (a', x')]
        · rw [Finset.sum_eq_single (a, x)]
          · cases a <;> cases a' <;> simp
          · intro z _ hz; simp [Ne.symm hz]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        · intro z _ hz; simp [hz, Ne.symm hz]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      have hZ2 : ∀ (a a' : Bool) (x x' : d₂),
          (W₂.dual.out true).mat (a, x) (a', x') =
          (if a = false then (1 : ℂ) else -1) * (W₂.dual.out false).mat (a, x) (a', x') *
          (if a' = false then (1 : ℂ) else -1) := by
        intro a a' x x'
        simp only [CQChannel.dual, DensityOp.conjUnitary, pauliZTensorI, Matrix.mul_apply,
          Matrix.diagonal_apply, Matrix.star_apply]
        rw [Finset.sum_eq_single (a', x')]
        · rw [Finset.sum_eq_single (a, x)]
          · cases a <;> cases a' <;> simp
          · intro z _ hz; simp [Ne.symm hz]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        · intro z _ hz; simp [hz, Ne.symm hz]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      cases b <;> cases c₁ <;> cases c₂ <;> cases w₁ <;> cases w₂ <;> cases w₁' <;> cases w₂' <;>
        simp [hZ1, hZ2] <;> push_cast <;> ring
    cases b <;> exact hmatch
  · -- Verify `Ψ₂((W₁⊥ ⊛ W₂⊥)(b)) = W_E(b)`
    intro b
    ext ⟨u₁, v₁, r₁, r₂⟩ ⟨u₂, v₂, r₁', r₂'⟩
    simp only [Ψ₂, CPTPMap.apply, CPTPMap.toLinearMap, partialTrace₂Mat, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type]
    have hM_entry :
        ((if b = false then
          (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x)) *
          (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else A₁ᴴ p.2 x))ᴴ
        else
          (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x)) *
          (Matrix.of fun (p : Bool × (Bool × (d₁ × d₂))) (x : d₁ × d₂) ↦
            ((Real.sqrt 2 : ℂ)⁻¹) * (if p.1 = false then A₀ᴴ p.2 x else -A₁ᴴ p.2 x))ᴴ)
          (u₁, (v₁, (r₁, r₂))) (u₂, (v₂, (r₁', r₂')))) =
        (if b = false then (1 : ℂ) else (if u₁ = false then 1 else -1) * (if u₂ = false then 1 else -1)) *
          ((W₁.dual.out false).mat (xor u₁ v₁, r₁) (xor u₂ v₂, r₁') *
           (W₂.dual.out false).mat (v₁, r₂) (v₂, r₂')) := by
      have hA_ent : ∀ (u v : Bool) (x₁ : d₁) (x₂ : d₂) (y₁ : d₁) (y₂ : d₂),
          (if u = false then A₀ᴴ (v, (y₁, y₂)) (x₁, x₂) else A₁ᴴ (v, (y₁, y₂)) (x₁, x₂)) =
          ((Real.sqrt 2 : ℂ)⁻¹) *
            ((if xor u v = false then ρ₀.sqrtMat y₁ x₁ else ρ₁.sqrtMat y₁ x₁) *
             (if v = false then σ₀.sqrtMat y₂ x₂ else σ₁.sqrtMat y₂ x₂)) := by
        intro u v x₁ x₂ y₁ y₂
        simp only [A₀, A₁, Matrix.conjTranspose_apply, Matrix.of_apply]
        cases u <;> cases v <;>
          simp only [↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, Bool.xor_false, Bool.xor_true,
            Bool.not_false, Bool.not_true, star_mul', hstar2] <;>
          (have hr0 := congr_fun (congr_fun ρ₀.sqrtMat_isHermitian.eq y₁) x₁;
           have hr1 := congr_fun (congr_fun ρ₁.sqrtMat_isHermitian.eq y₁) x₁;
           have hs0 := congr_fun (congr_fun σ₀.sqrtMat_isHermitian.eq y₂) x₂;
           have hs1 := congr_fun (congr_fun σ₁.sqrtMat_isHermitian.eq y₂) x₂;
           simp only [Matrix.conjTranspose_apply] at hr0 hr1 hs0 hs1;
           try rw [hr0]; try rw [hr1]; try rw [hs0]; try rw [hs1]; ring)
      have hprod : (∑ x₁ : d₁, ∑ x₂ : d₂,
          (((Real.sqrt 2 : ℂ)⁻¹) * (if u₁ = false then A₀ᴴ (v₁, (r₁, r₂)) (x₁, x₂) else A₁ᴴ (v₁, (r₁, r₂)) (x₁, x₂))) *
          star (((Real.sqrt 2 : ℂ)⁻¹) * (if u₂ = false then A₀ᴴ (v₂, (r₁', r₂')) (x₁, x₂) else A₁ᴴ (v₂, (r₁', r₂')) (x₁, x₂)))) =
          (W₁.dual.out false).mat (xor u₁ v₁, r₁) (xor u₂ v₂, r₁') *
          (W₂.dual.out false).mat (v₁, r₂) (v₂, r₂') := by
        simp_rw [hA_ent]
        simp only [CQChannel.dual, gramState, gramFactor, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x₁ _
        apply Finset.sum_congr rfl; intro x₂ _
        simp only [star_mul', hstar2]; ring
      cases b
      · simp only [↓reduceIte, one_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Fintype.sum_prod_type]; exact hprod
      · simp only [Bool.true_eq_false, ↓reduceIte, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.of_apply, Fintype.sum_prod_type]
        rw [← hprod, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x₁ _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x₂ _
        cases u₁ <;> cases u₂ <;> simp [star_mul', star_neg] <;> ring
    have hZ1 : ∀ (a a' : Bool) (x x' : d₁),
        (W₁.dual.out true).mat (a, x) (a', x') =
        (if a = false then (1 : ℂ) else -1) * (W₁.dual.out false).mat (a, x) (a', x') *
        (if a' = false then (1 : ℂ) else -1) := by
      intro a a' x x'
      simp only [CQChannel.dual, DensityOp.conjUnitary, pauliZTensorI, Matrix.mul_apply,
        Matrix.diagonal_apply, Matrix.star_apply]
      rw [Finset.sum_eq_single (a', x')]
      · rw [Finset.sum_eq_single (a, x)]
        · cases a <;> cases a' <;> simp
        · intro z _ hz; simp [Ne.symm hz]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro z _ hz; simp [hz, Ne.symm hz]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    have hZ2 : ∀ (a a' : Bool) (x x' : d₂),
        (W₂.dual.out true).mat (a, x) (a', x') =
        (if a = false then (1 : ℂ) else -1) * (W₂.dual.out false).mat (a, x) (a', x') *
        (if a' = false then (1 : ℂ) else -1) := by
      intro a a' x x'
      simp only [CQChannel.dual, DensityOp.conjUnitary, pauliZTensorI, Matrix.mul_apply,
        Matrix.diagonal_apply, Matrix.star_apply]
      rw [Finset.sum_eq_single (a', x')]
      · rw [Finset.sum_eq_single (a, x)]
        · cases a <;> cases a' <;> simp
        · intro z _ hz; simp [Ne.symm hz]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro z _ hz; simp [hz, Ne.symm hz]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    -- Collapse the sums in `Ψ₂`
    have hLHS : (∑ e : Bool, ∑ c₂ : Bool, ∑ w₁' : Bool, ∑ j₁' : d₁, ∑ w₂' : Bool, ∑ j₂' : d₂,
        (∑ c₁ : Bool, ∑ w₁ : Bool, ∑ j₁ : d₁, ∑ w₂ : Bool, ∑ j₂ : d₂,
          (if e = c₁ ∧ u₁ = xor w₁ w₂ ∧ v₁ = w₂ ∧ r₁ = j₁ ∧ r₂ = j₂ then
            (if c₁ = true ∧ w₁ = true then (-1 : ℂ) else 1) else 0) *
          ((CQChannel.varCombine W₁.dual W₂.dual).out b).mat (c₁, ((w₁, j₁), (w₂, j₂))) (c₂, ((w₁', j₁'), (w₂', j₂')))) *
        star (if e = c₂ ∧ u₂ = xor w₁' w₂' ∧ v₂ = w₂' ∧ r₁' = j₁' ∧ r₂' = j₂' then
          (if c₂ = true ∧ w₁' = true then (-1 : ℂ) else 1) else 0)) =
      ∑ e : Bool, (if e = true ∧ xor u₁ v₁ = true then (-1 : ℂ) else 1) *
        ((CQChannel.varCombine W₁.dual W₂.dual).out b).mat
          (e, ((xor u₁ v₁, r₁), (v₁, r₂))) (e, ((xor u₂ v₂, r₁'), (v₂, r₂'))) *
        (if e = true ∧ xor u₂ v₂ = true then (-1 : ℂ) else 1) := by
      apply Finset.sum_congr rfl; intro e _
      rw [Finset.sum_eq_single e]
      · rw [Finset.sum_eq_single (xor u₂ v₂)]
        · rw [Finset.sum_eq_single r₁']
          · rw [Finset.sum_eq_single v₂]
            · rw [Finset.sum_eq_single r₂']
              · rw [Finset.sum_eq_single e]
                · rw [Finset.sum_eq_single (xor u₁ v₁)]
                  · rw [Finset.sum_eq_single r₁]
                    · rw [Finset.sum_eq_single v₁]
                      · rw [Finset.sum_eq_single r₂]
                        · have hx1 : u₁ = xor (xor u₁ v₁) v₁ := by cases u₁ <;> cases v₁ <;> decide
                          have hx2 : u₂ = xor (xor u₂ v₂) v₂ := by cases u₂ <;> cases v₂ <;> decide
                          simp only [hx1, hx2, and_self, ↓reduceIte]
                          have hs : star (if e = true ∧ xor u₂ v₂ = true then (-1 : ℂ) else 1) =
                              if e = true ∧ xor u₂ v₂ = true then (-1 : ℂ) else 1 := by
                            cases e <;> cases xor u₂ v₂ <;> simp
                          rw [hs]
                        · intro j₂ _ hj₂; simp [Ne.symm hj₂]
                        · intro hm; exact absurd (Finset.mem_univ _) hm
                      · intro w₂ _ hw₂; simp [Ne.symm hw₂]
                      · intro hm; exact absurd (Finset.mem_univ _) hm
                    · intro j₁ _ hj₁; simp [Ne.symm hj₁]
                    · intro hm; exact absurd (Finset.mem_univ _) hm
                  · intro w₁ _ hw₁
                    apply Finset.sum_eq_zero; intro j₁ _
                    apply Finset.sum_eq_zero; intro w₂ _
                    apply Finset.sum_eq_zero; intro j₂ _
                    have hne : ¬ (u₁ = xor w₁ w₂ ∧ v₁ = w₂) := by
                      rintro ⟨hu, hv⟩; subst hv; apply hw₁
                      cases u₁ <;> cases w₁ <;> cases w₂ <;> simp_all
                    by_cases hcond : e = e ∧ u₁ = xor w₁ w₂ ∧ v₁ = w₂ ∧ r₁ = j₁ ∧ r₂ = j₂
                    · exact absurd ⟨hcond.2.1, hcond.2.2.1⟩ hne
                    · simp [hcond]
                  · intro hm; exact absurd (Finset.mem_univ _) hm
                · intro c₁ _ hc₁; simp [Ne.symm hc₁]
                · intro hm; exact absurd (Finset.mem_univ _) hm
              · intro j₂' _ hj₂'; simp [Ne.symm hj₂']
              · intro hm; exact absurd (Finset.mem_univ _) hm
            · intro w₂' _ hw₂'; simp [Ne.symm hw₂']
            · intro hm; exact absurd (Finset.mem_univ _) hm
          · intro j₁' _ hj₁'; simp [Ne.symm hj₁']
          · intro hm; exact absurd (Finset.mem_univ _) hm
        · intro w₁' _ hw₁'
          apply Finset.sum_eq_zero; intro j₁' _
          apply Finset.sum_eq_zero; intro w₂' _
          apply Finset.sum_eq_zero; intro j₂' _
          have hne : ¬ (u₂ = xor w₁' w₂' ∧ v₂ = w₂') := by
            rintro ⟨hu, hv⟩; subst hv; apply hw₁'
            cases u₂ <;> cases w₁' <;> cases w₂' <;> simp_all
          by_cases hcond : e = e ∧ u₂ = xor w₁' w₂' ∧ v₂ = w₂' ∧ r₁' = j₁' ∧ r₂' = j₂'
          · exact absurd ⟨hcond.2.1, hcond.2.2.1⟩ hne
          · simp [hcond]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro c₂ _ hc₂; simp [Ne.symm hc₂]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    have hRHS : (∑ e : Bool, (if e = true ∧ xor u₁ v₁ = true then (-1 : ℂ) else 1) *
        ((CQChannel.varCombine W₁.dual W₂.dual).out b).mat
          (e, ((xor u₁ v₁, r₁), (v₁, r₂))) (e, ((xor u₂ v₂, r₁'), (v₂, r₂'))) *
        (if e = true ∧ xor u₂ v₂ = true then (-1 : ℂ) else 1)) =
      (if b = false then (1 : ℂ) else (if u₁ = false then 1 else -1) * (if u₂ = false then 1 else -1)) *
        ((W₁.dual.out false).mat (xor u₁ v₁, r₁) (xor u₂ v₂, r₁') *
         (W₂.dual.out false).mat (v₁, r₂) (v₂, r₂')) := by
      rw [Fintype.sum_bool]
      simp only [CQChannel.varCombine, CQChannel.ketBraBool, DensityOp.midpoint, DensityOp.mix,
        DensityOp.tensor, Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
        Matrix.of_apply, Complex.real_smul]
      cases b <;> cases u₁ <;> cases v₁ <;> cases u₂ <;> cases v₂ <;>
        simp [hZ1, hZ2] <;> push_cast <;> ring
    cases b
    · simpa [hM_entry] using hLHS.trans hRHS
    · simpa [hM_entry] using hLHS.trans hRHS

end ChannelEquivalence

end PolarCodes
