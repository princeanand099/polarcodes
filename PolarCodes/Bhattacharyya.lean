/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import PolarCodes.GramDephasing

/-!
# Trace Norm, Polar Decomposition, Uhlmann Purifications, and Lemma 5.1(b)

This module establishes:
- The trace norm `traceNorm M = ∑ i, √(λ_i(Mᴴ M))`
- Polar decomposition (`exists_unitary_polar`): every square matrix `M` admits a unitary `U`
  such that `M = U * |M|` and `Re Tr(Uᴴ M) = ‖M‖₁`
- Variational upper bound (`re_trace_unitary_mul_le_traceNorm`): `Re Tr(Uᴴ M) ≤ ‖M‖₁` for all
  unitary `U`
- Trace-norm triangle inequality (`traceNorm_add_le`): `‖A + B‖₁ ≤ ‖A‖₁ + ‖B‖₁`
- Partial trace `partialTrace₂` and Uhlmann's purification theorem (`exists_uhlmann_purification`)
- **Lemma 5.1(b) (minus channel)**: `Z(W⁻) ≤ 2 Z(W)` (`fidelityParam_minusChannel_le`)
-/

open Matrix BigOperators Real
open scoped ComplexOrder InnerProductSpace

namespace PolarCodes

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-! ### Trace Norm and Polar Decomposition -/

/-- The trace norm (Schatten 1-norm) `‖M‖₁ := Tr √(Mᴴ M) = ∑ i, √(λ_i(Mᴴ M))`. -/
noncomputable def traceNorm (M : Matrix d d ℂ) : ℝ :=
  ∑ i : d, Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self M).isHermitian.eigenvalues i)

lemma traceNorm_nonneg (M : Matrix d d ℂ) : 0 ≤ traceNorm M :=
  Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _

/-- For density operators `ρ, σ`, `‖√ρ √σ‖₁ = F(ρ, σ)`. -/
lemma traceNorm_sqrt_mul_sqrt (ρ σ : DensityOp d) :
    traceNorm (ρ.sqrtMat * σ.sqrtMat) = rootFidelity ρ σ := by
  unfold traceNorm rootFidelity
  have h1 : (ρ.sqrtMat * σ.sqrtMat)ᴴ * (ρ.sqrtMat * σ.sqrtMat) = σ.sqrtMat * ρ.mat * σ.sqrtMat := by
    rw [Matrix.conjTranspose_mul, ρ.sqrtMat_isHermitian.eq, σ.sqrtMat_isHermitian.eq,
      ← ρ.sqrtMat_mul_self]
    simp only [Matrix.mul_assoc]
  rw [← rootFidelity_symm]
  unfold rootFidelity
  apply spectral_sum_eq_of_charpoly_mul_X_pow
    (Matrix.posSemidef_conjTranspose_mul_self (ρ.sqrtMat * σ.sqrtMat)).isHermitian
    (posSemidef_sqrt_mul_sqrt σ ρ).isHermitian (k := 0) (l := 0)
  · rw [pow_zero, mul_one, mul_one, h1]
  · exact Real.sqrt_zero

/-- Polar decomposition for square complex matrices: there exists a unitary `U` and a unitary `V`
such that `M = U * V * diag(σ) * Vᴴ`, where `σ i = √(λ_i(Mᴴ M)) ≥ 0` and `∑ i, σ i = ‖M‖₁`. -/
theorem exists_polar_decomp (M : Matrix d d ℂ) :
    ∃ (U : Matrix.unitaryGroup d ℂ),
      let hA := (Matrix.posSemidef_conjTranspose_mul_self M).isHermitian
      let V : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
      let σ : d → ℝ := fun i ↦ Real.sqrt (hA.eigenvalues i)
      M = (U : Matrix d d ℂ) * (V * Matrix.diagonal (Complex.ofReal ∘ σ) * star V) := by
  set hPSD := Matrix.posSemidef_conjTranspose_mul_self M
  set hA := hPSD.isHermitian
  set V : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
  set σ : d → ℝ := fun i ↦ Real.sqrt (hA.eigenvalues i)
  have hσ_nn : ∀ i, 0 ≤ σ i := fun _ ↦ Real.sqrt_nonneg _
  have hσ_sq : ∀ i, σ i ^ 2 = hA.eigenvalues i := fun i ↦ Real.sq_sqrt (hPSD.eigenvalues_nonneg i)
  have hspec : Mᴴ * M = V * Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) * star V := by
    simpa [V, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  have hV_star_mul : star V * V = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hV_mul_star : V * star V = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  set N : Matrix d d ℂ := M * V
  have hNHN : Nᴴ * N = Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) := by
    calc Nᴴ * N = star V * (Mᴴ * M) * V := by
          simp only [N, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
      _ = (star V * V) * Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) * (star V * V) := by
          rw [hspec]; simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) := by
          rw [hV_star_mul, Matrix.one_mul, Matrix.mul_one]
  -- Columns of `N` as vectors in `E := EuclideanSpace ℂ d`
  let E := EuclideanSpace ℂ d
  let colN : d → E := fun j ↦ WithLp.toLp 2 (fun i ↦ N i j)
  have hinner_N : ∀ j₁ j₂ : d, ⟪colN j₁, colN j₂⟫_ℂ =
      if j₁ = j₂ then ((hA.eigenvalues j₁ : ℝ) : ℂ) else 0 := by
    intro j₁ j₂
    have h := congr_fun (congr_fun hNHN j₁) j₂
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Function.comp_apply] at h
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    simpa [colN, mul_comm] using h
  -- Positive singular value indices `S`
  let S : Finset d := Finset.univ.filter (fun j ↦ 0 < σ j)
  let u : {j : d // j ∈ S} → E := fun j ↦ ((σ j.1 : ℂ)⁻¹) • colN j.1
  have hu_ortho : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro j₁ j₂
    have hpos₁ : 0 < σ j₁.1 := (Finset.mem_filter.mp j₁.2).2
    have hpos₂ : 0 < σ j₂.1 := (Finset.mem_filter.mp j₂.2).2
    simp only [u, inner_smul_left, inner_smul_right, hinner_N]
    by_cases heq : j₁ = j₂
    · subst heq
      simp only [↓reduceIte]
      have hne : (σ j₁.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos₁)
      rw [← hσ_sq j₁.1, Complex.ofReal_pow, sq, Complex.star_def, ← Complex.ofReal_inv,
        Complex.conj_ofReal, Complex.ofReal_inv]
      field_simp [hne]
    · have hne : j₁.1 ≠ j₂.1 := fun h ↦ heq (Subtype.ext h)
      simp [heq, hne]
  -- Span `K` of `{u j}` and its orthogonal complement `Kᗮ`
  let K : Submodule ℂ E := Submodule.span ℂ (Set.range u)
  have hlin : LinearIndependent ℂ u := hu_ortho.linearIndependent
  have hcard_K : Module.finrank ℂ K = Fintype.card {j : d // j ∈ S} := by
    rw [show K = Submodule.span ℂ (Set.range u) from rfl,
      finrank_span_eq_card hlin]
  have hcard_E : Module.finrank ℂ E = Fintype.card d := finrank_euclideanSpace
  have hcard_add : Module.finrank ℂ K + Module.finrank ℂ Kᗮ = Module.finrank ℂ E :=
    Submodule.finrank_add_finrank_orthogonal K
  have hcard_compl : Fintype.card {j : d // j ∉ S} = Module.finrank ℂ Kᗮ := by
    have htot : Fintype.card {j : d // j ∈ S} + Fintype.card {j : d // j ∉ S} = Fintype.card d := by
      simp only [Fintype.card_subtype]
      exact Finset.filter_card_add_filter_neg_card_eq_card _
    omega
  let b_perp := stdOrthonormalBasis ℂ Kᗮ
  let e_perp : {j : d // j ∉ S} ≃ Fin (Module.finrank ℂ Kᗮ) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcard_compl])
  let colW : d → E := fun j ↦
    if hj : j ∈ S then u ⟨j, hj⟩ else (b_perp (e_perp ⟨j, hj⟩) : E)
  have hcolW_ortho : Orthonormal ℂ colW := by
    rw [orthonormal_iff_ite]
    intro j₁ j₂
    by_cases h1 : j₁ ∈ S <;> by_cases h2 : j₂ ∈ S
    · simp only [colW, h1, h2, ↓reduceDIte]
      have h := (orthonormal_iff_ite.mp hu_ortho) ⟨j₁, h1⟩ ⟨j₂, h2⟩
      by_cases heq : j₁ = j₂
      · subst heq; simp at h ⊢; exact h
      · have hne : (⟨j₁, h1⟩ : {j // j ∈ S}) ≠ ⟨j₂, h2⟩ := fun h' ↦ heq (congr_arg Subtype.val h')
        simp [heq, hne] at h ⊢; exact h
    · simp only [colW, h1, h2, ↓reduceDIte]
      have hne : j₁ ≠ j₂ := fun h ↦ h2 (h ▸ h1)
      simp only [hne, ↓reduceIte]
      have hmemK : u ⟨j₁, h1⟩ ∈ K := Submodule.subset_span (Set.mem_range_self _)
      have hmemP : (b_perp (e_perp ⟨j₂, h2⟩) : E) ∈ Kᗮ := (b_perp (e_perp ⟨j₂, h2⟩)).2
      exact (Submodule.mem_orthogonal' K _).mp hmemP _ hmemK
    · simp only [colW, h1, h2, ↓reduceDIte]
      have hne : j₁ ≠ j₂ := fun h ↦ h1 (h.symm ▸ h2)
      simp only [hne, ↓reduceIte]
      have hmemK : u ⟨j₂, h2⟩ ∈ K := Submodule.subset_span (Set.mem_range_self _)
      have hmemP : (b_perp (e_perp ⟨j₁, h1⟩) : E) ∈ Kᗮ := (b_perp (e_perp ⟨j₁, h1⟩)).2
      exact Submodule.inner_right_of_mem_orthogonal hmemK hmemP
    · simp only [colW, h1, h2, ↓reduceDIte]
      have h := (orthonormal_iff_ite.mp b_perp.orthonormal) (e_perp ⟨j₁, h1⟩) (e_perp ⟨j₂, h2⟩)
      change ⟪b_perp (e_perp ⟨j₁, h1⟩), b_perp (e_perp ⟨j₂, h2⟩)⟫_ℂ = _
      rw [h]
      by_cases heq : j₁ = j₂
      · subst heq; simp
      · have hne : e_perp ⟨j₁, h1⟩ ≠ e_perp ⟨j₂, h2⟩ := fun h' ↦
          heq (congr_arg Subtype.val (e_perp.injective h'))
        simp [heq, hne]
  let W : Matrix d d ℂ := Matrix.of (fun i j ↦ colW j i)
  have hW_mem : W ∈ Matrix.unitaryGroup d ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext j₁ j₂
    have h := (orthonormal_iff_ite.mp hcolW_ortho) j₁ j₂
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct] at h
    simpa [W, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, mul_comm] using h
  -- Verify `W * diag(σ) = N`
  have hWN : W * Matrix.diagonal (Complex.ofReal ∘ σ) = N := by
    ext i j
    simp only [W, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply, Function.comp_apply,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    by_cases hj : j ∈ S
    · simp only [colW, hj, ↓reduceDIte, u, PiLp.smul_apply, smul_eq_mul, colN]
      have hpos : 0 < σ j := (Finset.mem_filter.mp hj).2
      have hne : (σ j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
      calc (σ j : ℂ)⁻¹ * N i j * (σ j : ℂ) = ((σ j : ℂ)⁻¹ * (σ j : ℂ)) * N i j := by ring
        _ = N i j := by rw [inv_mul_cancel₀ hne, one_mul]
    · have hσ0 : σ j = 0 := by
        have hnot : ¬ 0 < σ j := fun h ↦ hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        linarith [hσ_nn j]
      rw [hσ0, Complex.ofReal_zero, mul_zero]
      -- Since `σ j = 0`, `‖colN j‖² = hA.eigenvalues j = 0`, so `N i j = 0`
      have hlam0 : hA.eigenvalues j = 0 := by rw [← hσ_sq j, hσ0]; ring
      have hnorm0 : ⟪colN j, colN j⟫_ℂ = 0 := by rw [hinner_N j j]; simp [hlam0]
      have hcol0 : colN j = 0 := inner_self_eq_zero.mp hnorm0
      exact (congr_fun (congr_arg WithLp.ofLp hcol0) i).symm
  -- Set `U := W * star V ∈ unitaryGroup d ℂ`
  let U_unit : Matrix.unitaryGroup d ℂ := ⟨W, hW_mem⟩ * star hA.eigenvectorUnitary
  refine ⟨U_unit, ?_⟩
  show M = (W * star V) * (V * Matrix.diagonal (Complex.ofReal ∘ σ) * star V)
  calc M = M * (V * star V) := by rw [hV_mul_star, Matrix.mul_one]
    _ = N * star V := by simp only [N, Matrix.mul_assoc]
    _ = W * Matrix.diagonal (Complex.ofReal ∘ σ) * star V := by rw [hWN]
    _ = W * (star V * V) * Matrix.diagonal (Complex.ofReal ∘ σ) * star V := by
        rw [hV_star_mul, Matrix.mul_one]
    _ = (W * star V) * (V * Matrix.diagonal (Complex.ofReal ∘ σ) * star V) := by
        simp only [Matrix.mul_assoc]

/-- Attainment in the variational characterization of the trace norm:
there exists a unitary `U` such that `(Uᴴ * M).trace = (‖M‖₁ : ℂ)`. -/
theorem exists_unitary_trace_eq_traceNorm (M : Matrix d d ℂ) :
    ∃ U : Matrix.unitaryGroup d ℂ, ((U : Matrix d d ℂ)ᴴ * M).trace = (traceNorm M : ℂ) := by
  obtain ⟨U, hU⟩ := exists_polar_decomp M
  refine ⟨U, ?_⟩
  set hA := (Matrix.posSemidef_conjTranspose_mul_self M).isHermitian
  set V : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
  set σ : d → ℝ := fun i ↦ Real.sqrt (hA.eigenvalues i)
  have h1 : (U : Matrix d d ℂ)ᴴ * M = V * Matrix.diagonal (Complex.ofReal ∘ σ) * star V := by
    rw [hU, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self U,
      Matrix.one_mul]
  rw [h1, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self hA.eigenvectorUnitary,
    Matrix.one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, traceNorm, σ, Complex.ofReal_sum]

/-- Variational upper bound for the trace norm: for every unitary `U'` and matrix `M`,
`Re Tr(U'ᴴ M) ≤ ‖M‖₁`. -/
theorem re_trace_unitary_mul_le_traceNorm (U' : Matrix.unitaryGroup d ℂ) (M : Matrix d d ℂ) :
    (((U' : Matrix d d ℂ)ᴴ * M).trace).re ≤ traceNorm M := by
  obtain ⟨U, hU⟩ := exists_polar_decomp M
  set hA := (Matrix.posSemidef_conjTranspose_mul_self M).isHermitian
  set V : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
  set σ : d → ℝ := fun i ↦ Real.sqrt (hA.eigenvalues i)
  let Q_unit : Matrix.unitaryGroup d ℂ := star hA.eigenvectorUnitary * star U' * U * hA.eigenvectorUnitary
  let Q : Matrix d d ℂ := (Q_unit : Matrix d d ℂ)
  have htr : ((U' : Matrix d d ℂ)ᴴ * M).trace =
      (Q * Matrix.diagonal (Complex.ofReal ∘ σ)).trace := by
    rw [hU]
    have hQ : Q = star V * (U' : Matrix d d ℂ)ᴴ * (U : Matrix d d ℂ) * V := by
      simp [Q, Q_unit, V, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    rw [hQ]
    calc ((U' : Matrix d d ℂ)ᴴ * ((U : Matrix d d ℂ) *
            (V * Matrix.diagonal (Complex.ofReal ∘ σ) * star V))).trace
        = (star V * ((U' : Matrix d d ℂ)ᴴ * (U : Matrix d d ℂ) * V *
            Matrix.diagonal (Complex.ofReal ∘ σ))).trace := by
            rw [Matrix.trace_mul_cycle]
            simp only [Matrix.mul_assoc]
      _ = (star V * (U' : Matrix d d ℂ)ᴴ * (U : Matrix d d ℂ) * V *
            Matrix.diagonal (Complex.ofReal ∘ σ)).trace := by
            simp only [Matrix.mul_assoc]
  rw [htr]
  have htr_sum : (Q * Matrix.diagonal (Complex.ofReal ∘ σ)).trace =
      ∑ j : d, Q j j * (σ j : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
      Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [htr_sum, Complex.re_sum]
  unfold traceNorm
  apply Finset.sum_le_sum
  intro j _
  have hre : (Q j j * (σ j : ℂ)).re = (Q j j).re * σ j := by simp
  rw [hre]
  have hQ_le : (Q j j).re ≤ 1 := by
    have hcol := congr_fun (congr_fun (Unitary.coe_star_mul_self Q_unit) j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hcol
    have hsum_sq : ∑ i : d, ‖Q i j‖ ^ 2 = 1 := by
      have hre_col := congr_arg Complex.re hcol
      have hterm : ∀ i : d, (star (Q i j) * Q i j).re = ‖Q i j‖ ^ 2 := by
        intro i
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      simpa [Complex.re_sum, hterm] using hre_col
    have hdiag_sq : ‖Q j j‖ ^ 2 ≤ 1 := by
      rw [← hsum_sq]
      exact Finset.single_le_sum (fun i _ ↦ sq_nonneg ‖Q i j‖) (Finset.mem_univ j)
    have hnorm_le : ‖Q j j‖ ≤ 1 := by nlinarith [norm_nonneg (Q j j)]
    exact le_trans (Complex.re_le_norm (Q j j)) hnorm_le
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) hQ_le

/-- **Trace-norm triangle inequality**: `‖A + B‖₁ ≤ ‖A‖₁ + ‖B‖₁`. -/
theorem traceNorm_add_le (A B : Matrix d d ℂ) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  obtain ⟨U, hU⟩ := exists_unitary_trace_eq_traceNorm (A + B)
  have hre : traceNorm (A + B) = (((U : Matrix d d ℂ)ᴴ * (A + B)).trace).re := by
    rw [hU, Complex.ofReal_re]
  rw [hre, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  exact add_le_add (re_trace_unitary_mul_le_traceNorm U A) (re_trace_unitary_mul_le_traceNorm U B)

/-! ### Partial Trace and Uhlmann's Purification Theorem -/

/-- Partial trace over the second tensor factor `d₂`: `(Tr₂ ρ)_{i,j} = ∑ k, ρ_{(i,k),(j,k)}`. -/
def partialTrace₂ (ρ : DensityOp (d₁ × d₂)) : DensityOp d₁ where
  mat := Matrix.of fun i j ↦ ∑ k : d₂, ρ.mat (i, k) (j, k)
  posSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_sum]
      apply Finset.sum_congr rfl; intro k _
      have hh := congr_fun (congr_fun ρ.isHermitian.eq (i, k)) (j, k)
      simpa [Matrix.conjTranspose_apply] using hh
    · intro x
      -- Actually prove via `posSemidef` of each term directly
      have hsum' : star x ⬝ᵥ (Matrix.of fun i j ↦ ∑ k : d₂, ρ.mat (i, k) (j, k)).mulVec x =
          ∑ k : d₂, star (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) ⬝ᵥ
            ρ.mat.mulVec (fun p : d₁ × d₂ ↦ if p.2 = k then x p.1 else 0) := by
        trans ∑ k : d₂, ∑ i : d₁, star (x i) * ∑ j : d₁, ρ.mat (i, k) (j, k) * x j
        · simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro j _
          ring
        · apply Finset.sum_congr rfl; intro k _
          simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Fintype.sum_prod_type]
          apply Finset.sum_congr rfl; intro i _
          simp only [star_ite, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
            ↓reduceIte]
          congr 1
          apply Finset.sum_congr rfl; intro j _
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [hsum']
      exact Finset.sum_nonneg fun k _ ↦
        (Matrix.posSemidef_iff_dotProduct_mulVec.mp ρ.posSemidef).2 _
  trace_one := by
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
    have htr := ρ.trace_one
    simpa [Matrix.trace, Matrix.diag, Fintype.sum_prod_type] using htr

/-- **Uhlmann's Purification Theorem**: For any two density operators `ρ, σ ∈ D(ℂ^d)`, there exist
unit vectors `ψ₀, ψ₁ ∈ ℂ^d ⊗ ℂ^d` purifying `ρ` and `σ` respectively (`Tr₂ |ψ₀⟩⟨ψ₀| = ρ`,
`Tr₂ |ψ₁⟩⟨ψ₁| = σ`) with overlap `‖⟨ψ₀|ψ₁⟩‖ = F(ρ, σ)`. -/
theorem exists_uhlmann_purification (ρ σ : DensityOp d) :
    ∃ (ψ₀ ψ₁ : (d × d) → ℂ) (hψ₀ : ∑ p : d × d, ‖ψ₀ p‖ ^ 2 = 1)
      (hψ₁ : ∑ p : d × d, ‖ψ₁ p‖ ^ 2 = 1),
      (partialTrace₂ (pureState ψ₀ hψ₀)).mat = ρ.mat ∧
      (partialTrace₂ (pureState ψ₁ hψ₁)).mat = σ.mat ∧
      ‖∑ p : d × d, star (ψ₀ p) * ψ₁ p‖ = rootFidelity ρ σ := by
  obtain ⟨U, hU⟩ := exists_unitary_trace_eq_traceNorm (ρ.sqrtMat * σ.sqrtMat)
  let ψ₀ : (d × d) → ℂ := fun p ↦ ρ.sqrtMat p.1 p.2
  let ψ₁ : (d × d) → ℂ := fun p ↦ (σ.sqrtMat * (U : Matrix d d ℂ)ᴴ) p.1 p.2
  have htr_pure : ∀ (M : Matrix d d ℂ),
      (∑ p : d × d, ((‖M p.1 p.2‖ ^ 2 : ℝ) : ℂ)) = (M * Mᴴ).trace := by
    intro M
    simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hψ₀ : ∑ p : d × d, ‖ψ₀ p‖ ^ 2 = 1 := by
    have h := htr_pure ρ.sqrtMat
    rw [ρ.sqrtMat_isHermitian.eq, ρ.sqrtMat_mul_self, ρ.trace_one, ← Complex.ofReal_sum] at h
    exact Complex.ofReal_injective h
  have hψ₁ : ∑ p : d × d, ‖ψ₁ p‖ ^ 2 = 1 := by
    have h := htr_pure (σ.sqrtMat * (U : Matrix d d ℂ)ᴴ)
    have hprod : (σ.sqrtMat * (U : Matrix d d ℂ)ᴴ) * (σ.sqrtMat * (U : Matrix d d ℂ)ᴴ)ᴴ = σ.mat := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, σ.sqrtMat_isHermitian.eq,
        Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix d d ℂ)ᴴ, ← Matrix.star_eq_conjTranspose,
        Unitary.coe_star_mul_self U, Matrix.one_mul, σ.sqrtMat_mul_self]
    rw [hprod, σ.trace_one, ← Complex.ofReal_sum] at h
    exact Complex.ofReal_injective h
  refine ⟨ψ₀, ψ₁, hψ₀, hψ₁, ?_, ?_, ?_⟩
  · ext i j
    simp only [partialTrace₂, pureState, Matrix.of_apply, ψ₀]
    have h := congr_fun (congr_fun ρ.sqrtMat_mul_self i) j
    rw [← h, Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro k _
    have hh := congr_fun (congr_fun ρ.sqrtMat_isHermitian.eq k) j
    simp only [Matrix.conjTranspose_apply] at hh; rw [hh]
  · ext i j
    simp only [partialTrace₂, pureState, Matrix.of_apply, ψ₁]
    have hprod : (σ.sqrtMat * (U : Matrix d d ℂ)ᴴ) * (σ.sqrtMat * (U : Matrix d d ℂ)ᴴ)ᴴ = σ.mat := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, σ.sqrtMat_isHermitian.eq,
        Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix d d ℂ)ᴴ, ← Matrix.star_eq_conjTranspose,
        Unitary.coe_star_mul_self U, Matrix.one_mul, σ.sqrtMat_mul_self]
    have h := congr_fun (congr_fun hprod i) j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  · -- Wait: let's compute `hinner` cleanly in 4 lines
    have hinner' : ∑ p : d × d, star (ψ₀ p) * ψ₁ p =
        ((U : Matrix d d ℂ)ᴴ * (ρ.sqrtMat * σ.sqrtMat)).trace := by
      have hcyc : ((U : Matrix d d ℂ)ᴴ * (ρ.sqrtMat * σ.sqrtMat)).trace =
          (ρ.sqrtMatᴴ * (σ.sqrtMat * (U : Matrix d d ℂ)ᴴ)).trace := by
        rw [ρ.sqrtMat_isHermitian.eq, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
      rw [hcyc]
      simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
        Matrix.conjTranspose_apply, ψ₀, ψ₁]
      rw [Finset.sum_comm]
    rw [hinner', hU, traceNorm_sqrt_mul_sqrt, Complex.norm_real,
      Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _)]

/-! ### Lemma 5.1(b) (Minus Channel): `Z(W⁻) ≤ 2 Z(W)` -/

/-- Helper: trace norm of a single-block matrix `E_{ab} ⊗ M` equals `‖M‖₁`. -/
private lemma traceNorm_singleBlock (a b : Bool) (M : Matrix d d ℂ) :
    traceNorm (Matrix.of fun (p q : Bool × d) ↦ if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0) =
      traceNorm M := by
  let B : Matrix (Bool × d) (Bool × d) ℂ :=
    Matrix.of fun p q ↦ if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0
  let R : Matrix d (Bool × d) ℂ :=
    Matrix.of fun i q ↦ if q.1 = b then M i q.2 else 0
  have hBHB : Bᴴ * B = Rᴴ * R := by
    ext ⟨b₁, i₁⟩ ⟨b₂, i₂⟩
    simp only [B, R, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Fintype.sum_bool]
    cases a <;> simp
  have hRRH : R * Rᴴ = M * Mᴴ := by
    ext i j
    simp only [R, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Fintype.sum_bool]
    cases b <;> simp
  have hcp1 : (Bᴴ * B).charpoly * Polynomial.X ^ (Fintype.card d) =
      (M * Mᴴ).charpoly * Polynomial.X ^ (Fintype.card (Bool × d)) := by
    rw [hBHB, ← hRRH]
    exact (charpoly_mul_conjTranspose_eq R).symm
  have hcp2 := charpoly_mul_conjTranspose_eq M
  have hcp_final : (Bᴴ * B).charpoly * Polynomial.X ^ (Fintype.card d) =
      (Mᴴ * M).charpoly * Polynomial.X ^ (Fintype.card (Bool × d)) := by
    rw [hcp1]
    have hcard : Fintype.card (Bool × d) = Fintype.card d + Fintype.card d := by
      simp [Fintype.card_prod]; ring
    -- Since `(M * Mᴴ).charpoly = (Mᴴ * M).charpoly` for square `M`
    have hsq : (M * Mᴴ).charpoly = (Mᴴ * M).charpoly := Matrix.charpoly_mul_comm M Mᴴ
    rw [hsq]
  unfold traceNorm
  exact spectral_sum_eq_of_charpoly_mul_X_pow
    (Matrix.posSemidef_conjTranspose_mul_self B).isHermitian
    (Matrix.posSemidef_conjTranspose_mul_self M).isHermitian hcp_final Real.sqrt_zero

/-- Helper: trace norm of `((1/2 : ℝ) : ℂ) • M` equals `(1/2) * traceNorm M`. -/
private lemma traceNorm_half_smul (M : Matrix d d ℂ) :
    traceNorm (((1 / 2 : ℝ) : ℂ) • M) = (1 / 2 : ℝ) * traceNorm M := by
  set hA := (Matrix.posSemidef_conjTranspose_mul_self M).isHermitian
  have hmul : (((1 / 2 : ℝ) : ℂ) • M)ᴴ * (((1 / 2 : ℝ) : ℂ) • M) =
      ((1 / 4 : ℝ) : ℂ) • (Mᴴ * M) := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1; simp; norm_num
  set U : Matrix d d ℂ := (hA.eigenvectorUnitary : Matrix d d ℂ)
  have hspec : Mᴴ * M = U * Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) * star U := by
    simpa [U, Matrix.star_eq_conjTranspose, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  let lam : d → ℝ := fun i ↦ hA.eigenvalues i / 4
  have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext i; simp
  have hcp : ((((1 / 2 : ℝ) : ℂ) • M)ᴴ * (((1 / 2 : ℝ) : ℂ) • M)).charpoly =
      (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
    rw [hmul]
    conv_lhs => rw [hspec]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self hA.eigenvectorUnitary, Matrix.one_mul]
    congr 1; ext i j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply, smul_eq_mul, lam]
    split_ifs
    · push_cast; ring
    · simp
  unfold traceNorm
  trans ∑ i : d, Real.sqrt (lam i)
  · trans ∑ i : d, Real.sqrt (hD_herm.eigenvalues i)
    · exact spectral_sum_eq_of_charpoly_mul_X_pow
        (Matrix.posSemidef_conjTranspose_mul_self _).isHermitian hD_herm (k := 0) (l := 0)
        (by rw [pow_zero, mul_one, mul_one, hcp]) Real.sqrt_zero
    · exact spectral_sum_diagonal lam hD_herm Real.sqrt_zero
  · have h4 : ∀ x : ℝ, Real.sqrt (x / 4) = (1 / 2 : ℝ) * Real.sqrt x := by
      intro x
      rw [Real.sqrt_div' x (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      ring
    simp_rw [lam, h4, ← Finset.mul_sum]

/-- **Lemma 5.1(b) (minus channel)**: `Z(W⁻) ≤ 2 Z(W)` for every binary-input c-q channel `W`. -/
theorem fidelityParam_minusChannel_le (W : CQChannel d) :
    (CQChannel.minusChannel W).fidelityParam ≤ 2 * W.fidelityParam := by
  set ρ₀ := W.out false
  set ρ₁ := W.out true
  set τ₀ := (CQChannel.minusChannel W).out false
  set τ₁ := (CQChannel.minusChannel W).out true
  -- Factor `τ₀ = P * Pᴴ` and `τ₁ = Q * Qᴴ` via `P, Q : Matrix (d × d) (Bool × (d × d)) ℂ`
  let X0 : DensityOp (d × d) := DensityOp.tensor ρ₀ ρ₀
  let X1 : DensityOp (d × d) := DensityOp.tensor ρ₁ ρ₁
  let Y0 : DensityOp (d × d) := DensityOp.tensor ρ₁ ρ₀
  let Y1 : DensityOp (d × d) := DensityOp.tensor ρ₀ ρ₁
  let P : Matrix (d × d) (Bool × (d × d)) ℂ := Matrix.of fun p q ↦
    ((Real.sqrt 2)⁻¹ : ℂ) * if q.1 = false then X0.sqrtMat p q.2 else X1.sqrtMat p q.2
  let Q : Matrix (d × d) (Bool × (d × d)) ℂ := Matrix.of fun p q ↦
    ((Real.sqrt 2)⁻¹ : ℂ) * if q.1 = false then Y0.sqrtMat p q.2 else Y1.sqrtMat p q.2
  have hsq2' : ((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  have hPPH : P * Pᴴ = τ₀.mat := by
    ext p q
    simp only [P, τ₀, CQChannel.minusChannel, CQChannel.checkCombine, X0, X1,
      DensityOp.midpoint, DensityOp.mix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
      Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false]
    have hblock : ∀ (σ : DensityOp (d × d)),
        (∑ x : d, ∑ y : d, ((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat p (x, y) *
            star (((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat q (x, y))) =
          (1 / 2 : ℂ) * σ.mat p q := by
      intro σ
      have hmul := congr_fun (congr_fun σ.sqrtMat_mul_self p) q
      rw [← hmul, Matrix.mul_apply, Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro y _
      have hh := congr_fun (congr_fun σ.sqrtMat_isHermitian.eq (x, y)) q
      simp only [Matrix.conjTranspose_apply] at hh
      rw [star_mul', ← hh]
      calc ((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat p (x, y) * (σ.sqrtMat (x, y) q * star ((Real.sqrt 2 : ℂ)⁻¹))
          = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) * (σ.sqrtMat p (x, y) * σ.sqrtMat (x, y) q) := by ring
        _ = (1 / 2 : ℂ) * (σ.sqrtMat p (x, y) * σ.sqrtMat (x, y) q) := by rw [hsq2']
    rw [hblock X0, hblock X1]; push_cast; ring
  have hQQH : Q * Qᴴ = τ₁.mat := by
    ext p q
    simp only [Q, τ₁, CQChannel.minusChannel, CQChannel.checkCombine, Y0, Y1,
      Bool.not_false, Bool.not_true,
      DensityOp.midpoint, DensityOp.mix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
      Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false]
    have hblock : ∀ (σ : DensityOp (d × d)),
        (∑ x : d, ∑ y : d, ((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat p (x, y) *
            star (((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat q (x, y))) =
          (1 / 2 : ℂ) * σ.mat p q := by
      intro σ
      have hmul := congr_fun (congr_fun σ.sqrtMat_mul_self p) q
      rw [← hmul, Matrix.mul_apply, Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro y _
      have hh := congr_fun (congr_fun σ.sqrtMat_isHermitian.eq (x, y)) q
      simp only [Matrix.conjTranspose_apply] at hh
      rw [star_mul', ← hh]
      calc ((Real.sqrt 2 : ℂ)⁻¹) * σ.sqrtMat p (x, y) * (σ.sqrtMat (x, y) q * star ((Real.sqrt 2 : ℂ)⁻¹))
          = (((Real.sqrt 2 : ℂ)⁻¹) * star ((Real.sqrt 2 : ℂ)⁻¹)) * (σ.sqrtMat p (x, y) * σ.sqrtMat (x, y) q) := by ring
        _ = (1 / 2 : ℂ) * (σ.sqrtMat p (x, y) * σ.sqrtMat (x, y) q) := by rw [hsq2']
    rw [hblock Y0, hblock Y1]; push_cast; ring
  -- `traceNorm (Pᴴ * Q) = rootFidelity τ₀ τ₁` via Sylvester identity on `R := Qᴴ * τ₀.sqrtMat`
  have htn_eq : traceNorm (Pᴴ * Q) = rootFidelity τ₀ τ₁ := by
    have hprod1 : (Pᴴ * Q)ᴴ * (Pᴴ * Q) = Qᴴ * τ₀.mat * Q := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
        ← Matrix.mul_assoc P, hPPH, Matrix.mul_assoc]
    have hprod2 : Qᴴ * τ₀.mat * Q = (Qᴴ * τ₀.sqrtMat) * (Qᴴ * τ₀.sqrtMat)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, τ₀.sqrtMat_isHermitian.eq,
        ← τ₀.sqrtMat_mul_self]
      simp only [Matrix.mul_assoc]
    have hprod3 : (Qᴴ * τ₀.sqrtMat)ᴴ * (Qᴴ * τ₀.sqrtMat) = τ₀.sqrtMat * τ₁.mat * τ₀.sqrtMat := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, τ₀.sqrtMat_isHermitian.eq,
        Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQQH, Matrix.mul_assoc]
    have hcp := charpoly_mul_conjTranspose_eq (Qᴴ * τ₀.sqrtMat)
    rw [← hprod2, ← hprod1, hprod3] at hcp
    unfold traceNorm rootFidelity
    exact spectral_sum_eq_of_charpoly_mul_X_pow
      (Matrix.posSemidef_conjTranspose_mul_self (Pᴴ * Q)).isHermitian
      (posSemidef_sqrt_mul_sqrt τ₀ τ₁).isHermitian hcp Real.sqrt_zero
  -- Decompose `Pᴴ * Q = B₀₀ + B₀₁ + B₁₀ + B₁₁`
  let mkB : Bool → Bool → Matrix (d × d) (d × d) ℂ → Matrix (Bool × (d × d)) (Bool × (d × d)) ℂ :=
    fun a b M ↦ Matrix.of fun p q ↦ if p.1 = a ∧ q.1 = b then M p.2 q.2 else 0
  let B00 := mkB false false (((1 / 2 : ℝ) : ℂ) • (X0.sqrtMat * Y0.sqrtMat))
  let B01 := mkB false true (((1 / 2 : ℝ) : ℂ) • (X0.sqrtMat * Y1.sqrtMat))
  let B10 := mkB true false (((1 / 2 : ℝ) : ℂ) • (X1.sqrtMat * Y0.sqrtMat))
  let B11 := mkB true true (((1 / 2 : ℝ) : ℂ) • (X1.sqrtMat * Y1.sqrtMat))
  have hsum_B : Pᴴ * Q = B00 + B01 + B10 + B11 := by
    have hsq2 : star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
      rw [mul_comm, hsq2']
    have hEntry : ∀ (σ₁ σ₂ : DensityOp (d × d)) (r s : d × d),
        (∑ p : d × d, star (((Real.sqrt 2 : ℂ)⁻¹) * σ₁.sqrtMat p r) *
            (((Real.sqrt 2 : ℂ)⁻¹) * σ₂.sqrtMat p s)) =
          ((1 / 2 : ℝ) : ℂ) * (σ₁.sqrtMat * σ₂.sqrtMat) r s := by
      intro σ₁ σ₂ r s
      rw [Matrix.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro p _
      have hh := congr_fun (congr_fun σ₁.sqrtMat_isHermitian.eq r) p
      simp only [Matrix.conjTranspose_apply] at hh
      rw [star_mul', hh]
      calc σ₁.sqrtMat r p * star ((Real.sqrt 2 : ℂ)⁻¹) * (((Real.sqrt 2 : ℂ)⁻¹) * σ₂.sqrtMat p s)
          = (star ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * (σ₁.sqrtMat r p * σ₂.sqrtMat p s) := by ring
        _ = ((1 / 2 : ℝ) : ℂ) * (σ₁.sqrtMat r p * σ₂.sqrtMat p s) := by rw [hsq2]; push_cast; rfl
    ext ⟨a, r⟩ ⟨b, s⟩
    simp only [P, Q, B00, B01, B10, B11, mkB, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, Complex.real_smul]
    cases a <;> cases b <;> simp [hEntry]
  -- Each block has trace norm `(1/2) * Z(W)`
  have hF_self : ∀ (ρ : DensityOp d), rootFidelity ρ ρ = 1 := by
    intro ρ
    unfold rootFidelity
    have h1 : ρ.sqrtMat * ρ.mat * ρ.sqrtMat = ρ.mat * ρ.mat := by
      rw [← ρ.sqrtMat_mul_self]
      have hcomm : ρ.sqrtMat * (ρ.sqrtMat * ρ.sqrtMat) * ρ.sqrtMat =
          (ρ.sqrtMat * ρ.sqrtMat) * (ρ.sqrtMat * ρ.sqrtMat) := by
        simp only [Matrix.mul_assoc]
      exact hcomm
    have hspec : ρ.mat = (ρ.eigUnitary : Matrix d d ℂ) *
        Matrix.diagonal (Complex.ofReal ∘ ρ.eigvals) * star (ρ.eigUnitary : Matrix d d ℂ) := by
      simpa [DensityOp.eigUnitary, DensityOp.eigvals, Matrix.star_eq_conjTranspose,
        Unitary.conjStarAlgAut_apply] using ρ.isHermitian.spectral_theorem
    let lam : d → ℝ := fun i ↦ ρ.eigvals i ^ 2
    have hD_herm : (Matrix.diagonal (Complex.ofReal ∘ lam)).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext i; simp
    have hsq : ρ.mat * ρ.mat = (ρ.eigUnitary : Matrix d d ℂ) *
        Matrix.diagonal (Complex.ofReal ∘ lam) * star (ρ.eigUnitary : Matrix d d ℂ) := by
      conv_lhs => rw [hspec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star (ρ.eigUnitary : Matrix d d ℂ)),
        Unitary.coe_star_mul_self ρ.eigUnitary, Matrix.one_mul]
      congr 1; rw [← Matrix.mul_assoc]; congr 1
      ext i j
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, Function.comp_apply, lam,
        mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      split_ifs
      · push_cast; ring
      · rfl
    have hcp : (ρ.sqrtMat * ρ.mat * ρ.sqrtMat).charpoly =
        (Matrix.diagonal (Complex.ofReal ∘ lam)).charpoly := by
      rw [h1, hsq, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
        Unitary.coe_star_mul_self ρ.eigUnitary, Matrix.one_mul]
    trans ∑ i : d, Real.sqrt (lam i)
    · trans ∑ i : d, Real.sqrt (hD_herm.eigenvalues i)
      · exact spectral_sum_eq_of_charpoly_mul_X_pow (posSemidef_sqrt_mul_sqrt ρ ρ).isHermitian
          hD_herm (k := 0) (l := 0) (by rw [pow_zero, mul_one, mul_one, hcp]) Real.sqrt_zero
      · exact spectral_sum_diagonal lam hD_herm Real.sqrt_zero
    · have hnn : ∀ i, 0 ≤ ρ.eigvals i := ρ.posSemidef.eigenvalues_nonneg
      simp_rw [lam, Real.sqrt_sq (hnn _)]
      exact ρ.sum_eigvals
  have hB00 : traceNorm B00 = (1 / 2 : ℝ) * W.fidelityParam := by
    rw [traceNorm_singleBlock, traceNorm_half_smul, traceNorm_sqrt_mul_sqrt,
      rootFidelity_tensor, hF_self ρ₀, mul_one]; rfl
  have hB01 : traceNorm B01 = (1 / 2 : ℝ) * W.fidelityParam := by
    rw [traceNorm_singleBlock, traceNorm_half_smul, traceNorm_sqrt_mul_sqrt,
      rootFidelity_tensor, hF_self ρ₀, one_mul]; rfl
  have hB10 : traceNorm B10 = (1 / 2 : ℝ) * W.fidelityParam := by
    rw [traceNorm_singleBlock, traceNorm_half_smul, traceNorm_sqrt_mul_sqrt,
      rootFidelity_tensor, hF_self ρ₁, one_mul, rootFidelity_symm]; rfl
  have hB11 : traceNorm B11 = (1 / 2 : ℝ) * W.fidelityParam := by
    rw [traceNorm_singleBlock, traceNorm_half_smul, traceNorm_sqrt_mul_sqrt,
      rootFidelity_tensor, hF_self ρ₁, mul_one, rootFidelity_symm]; rfl
  have htri : traceNorm (Pᴴ * Q) ≤ traceNorm B00 + traceNorm B01 + traceNorm B10 + traceNorm B11 := by
    rw [hsum_B]
    have h1 := traceNorm_add_le (B00 + B01 + B10) B11
    have h2 := traceNorm_add_le (B00 + B01) B10
    have h3 := traceNorm_add_le B00 B01
    linarith
  show rootFidelity τ₀ τ₁ ≤ 2 * W.fidelityParam
  rw [← htn_eq]
  linarith [htri, hB00, hB01, hB10, hB11]

end PolarCodes
