/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.MainTheorem
import PolarCodes.QuantumPolarCoding
import PolarCodes.DivergenceCharacterizations

/-!
# Non-Vacuity Sanity Checks for `PolarCodes`

Concrete non-vacuity checks verifying that the core channel types, density operators, and
headline theorems instantiate on nontrivial finite-dimensional quantum channels with strictly
positive capacity (`noiselessChannel`, `symCapacity = 1 > 0`) as well as degradable qubit CPTP
maps (`idQubitChannel`), without vacuous hypotheses.
-/

open scoped ComplexOrder

namespace PolarCodes.SanityChecks

/-- The unique 1-dimensional density operator `|0⟩⟨0|`. -/
noncomputable def trivialState : DensityOp (Fin 1) where
  mat := 1
  posSemidef := Matrix.PosSemidef.one
  trace_one := by simp

/-- The trivial (completely noisy) 1-dimensional binary-input c-q channel. -/
noncomputable def trivialChannel : CQChannel (Fin 1) where
  out _ := trivialState

/-- The noiseless binary classical–quantum channel `0 ↦ |0⟩⟨0|`, `1 ↦ |1⟩⟨1|` on `ℂ²`. -/
noncomputable def noiselessChannel : CQChannel Bool where
  out b := CQChannel.ketBraBool b

/-- The noiseless channel has strictly positive symmetric Holevo capacity `I(W) = 1 > 0`. -/
lemma noiselessChannel_symCapacity : noiselessChannel.symCapacity = 1 := by
  unfold CQChannel.symCapacity noiselessChannel
  rw [qjs_eq_one_iff]
  ext i j
  simp only [CQChannel.ketBraBool, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply,
    Fintype.sum_bool]
  cases i <;> cases j <;> simp

/-- The qubit identity CPTP map `id : B(ℂ²) → B(ℂ²)` with trivial 1-dimensional environment. -/
def idQubitChannel : CPTPMap.{0} Bool Bool where
  env := Unit
  fintypeEnv := inferInstance
  decEqEnv := inferInstance
  isom := Matrix.of fun p a ↦ if p.1 = a then (1 : ℂ) else 0
  isom_eq := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
    cases a <;> cases b <;> simp

/-- `idQubitChannel` is degradable (its complementary channel is the constant trace-out map). -/
lemma idQubitChannel_isDegradable : idQubitChannel.IsDegradable := by
  refine ⟨{ env := Bool
            fintypeEnv := inferInstance
            decEqEnv := inferInstance
            isom := Matrix.of fun p a ↦ if p.2 = a then (1 : ℂ) else 0
            isom_eq := by
              ext a b
              simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
                Matrix.one_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
              cases a <;> cases b <;> simp }, ?_⟩
  intro ρ
  ext ⟨⟩ ⟨⟩
  change ∑ b : Bool, _ = ∑ b : Bool, _
  simp only [idQubitChannel, CPTPMap.apply, CPTPMap.toLinearMap, CPTPMap.complementary,
    partialTrace₂Mat, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_bool, Fintype.sum_unique]
  simp

/-- Non-vacuity witness: Theorem 1.1 fidelity-fraction polarization instantiates on
`noiselessChannel` (with `symCapacity = 1 > 0`). -/
example :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ (n : ℕ), C₀ * (1 / (1 / 2 : ℝ)) ^ μ ≤ (2 : ℝ) ^ n →
        1 - (1 / 2 : ℝ) ≤
          treeProb n (fun b ↦
            polarFidelity noiselessChannel n b ≤
              (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))) := by
  rcases theorem_1_1_quantum_polar_poly_blocklength.{0} with ⟨μ, C₀, hμ, hC₀, h⟩
  refine ⟨μ, C₀, hμ, hC₀, fun n hn ↦ ?_⟩
  have h1 := h noiselessChannel (by norm_num) (by norm_num) n hn
  rwa [noiselessChannel_symCapacity] at h1

/-- Non-vacuity witness: Theorem 1.1 coding-theoretic QSC polar code instantiates on
`noiselessChannel` (with `symCapacity = 1 > 0`). -/
example :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ (n : ℕ), C₀ * (1 / (1 / 2 : ℝ)) ^ μ ≤ (2 : ℝ) ^ n →
        ∃ (infoSet : Finset (Fin (2 ^ n))) (frozen : Fin (2 ^ n) → Bool),
          let C := qscPolarCode noiselessChannel n infoSet frozen
          1 - (1 / 2 : ℝ) ≤ C.rate ∧
          C.avgBlockError ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) := by
  rcases theorem_1_1_coding_poly_blocklength.{0} with ⟨μ, C₀, hμ, hC₀, h⟩
  refine ⟨μ, C₀, hμ, hC₀, fun n hn ↦ ?_⟩
  obtain ⟨infoSet, frozen, hrate, herr⟩ := h noiselessChannel (by norm_num) (by norm_num) n hn
  rw [noiselessChannel_symCapacity] at hrate
  exact ⟨infoSet, frozen, hrate, herr⟩

/-- Non-vacuity witness: Corollary 5.5 instantiates on the degradable qubit identity channel
`idQubitChannel`, yielding vanishing pinned assistance rate `≤ ε / 2`. -/
example :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ (n : ℕ), C₀ * (1 / (1 / 2 : ℝ)) ^ μ ≤ (2 : ℝ) ^ n →
        let thresh : ℝ := (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))
        ∃ C : CSSPrivatePolarCode idQubitChannel n thresh,
          symCoherentInfo idQubitChannel - (1 / 2 : ℝ) / 2 ≤ C.rate ∧
          C.ampPhaseErrorSum ≤ 2 * (2 : ℝ) ^ (-((2 : ℝ) ^ n) ^ (49 / 100 : ℝ)) ∧
          C.assistanceRate ≤ (1 / 2 : ℝ) / 2 := by
  rcases corollary_5_5_quantum_private_polar_coding with ⟨μ, C₀, hμ, hC₀, h⟩
  refine ⟨μ, C₀, hμ, hC₀, fun n hn ↦ ?_⟩
  obtain ⟨C, hrate, _, _, hsum, _, _, hdeg⟩ := h idQubitChannel (by norm_num) (by norm_num) n hn
  exact ⟨C, hrate, hsum, hdeg idQubitChannel_isDegradable⟩

/-- Non-vacuity witness: Theorem 1.2(b) potential contraction instantiates on `noiselessChannel`. -/
example :
    (noiselessChannel.minusChannel.potential + noiselessChannel.plusChannel.potential) / 2 ≤
      Lambda0 * noiselessChannel.potential :=
  theorem_1_2b_potential_contraction noiselessChannel

/-- Non-vacuity witness: Theorem 1.3 nonlinear dephasing SDPI instantiates on `Bool × Fin 1`. -/
example (Ψ : DensityOp (Bool × Fin 1)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    dephaseCoherence p hp0 (le_trans hp1 (by norm_num)) Ψ ≤
      1 - h2 (binConv (h2Inv (1 - dephaseCoherence 0 le_rfl (by norm_num) Ψ)) p) :=
  theorem_1_3_dephasing_sdpi Ψ hp0 hp1

end PolarCodes.SanityChecks
