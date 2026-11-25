/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.MainTheorem

/-!
# Non-Vacuity & Sanity Checks

Concrete non-vacuity checks verifying that the core channel types, density operators, and main
theorems apply to explicit finite-dimensional quantum channels without vacuous hypotheses.
-/

namespace PolarCodes.SanityChecks

/-- The unique 1-dimensional density operator `|0⟩⟨0|`. -/
noncomputable def trivialState : DensityOp (Fin 1) where
  mat := 1
  posSemidef := Matrix.PosSemidef.one
  trace_eq_one := by simp

/-- The trivial (completely noisy) 1-dimensional binary-input c-q channel. -/
noncomputable def trivialChannel : CQChannel (Fin 1) where
  out := fun _ ↦ trivialState

/-- Non-vacuity witness: Theorem 1.1 instantiates concretely on `trivialChannel` at `ε = 1/2`. -/
example :
    ∃ (μ C₀ : ℝ), 0 < μ ∧ 0 < C₀ ∧
      ∀ (n : ℕ), C₀ * (1 / (1 / 2 : ℝ)) ^ μ ≤ (2 : ℝ) ^ n →
        trivialChannel.symCapacity - (1 / 2 : ℝ) ≤
          treeProb n (fun b ↦
            polarFidelity trivialChannel n b ≤
              (2 : ℝ) ^ (-(200 : ℝ) * ((2 : ℝ) ^ n) ^ (49047 / 100000 : ℝ))) := by
  rcases theorem_1_1_quantum_polar_poly_blocklength with ⟨μ, C₀, hμ, hC₀, h⟩
  exact ⟨μ, C₀, hμ, hC₀, fun n hn ↦ h trivialChannel (by norm_num) (by norm_num) n hn⟩

/-- Non-vacuity witness: Theorem 1.2(b) potential contraction instantiates on `trivialChannel`. -/
example :
    (trivialChannel.minusChannel.potential + trivialChannel.plusChannel.potential) / 2 ≤
      (1 - Lambda0) * trivialChannel.potential :=
  theorem_1_2b_potential_contraction trivialChannel

/-- Non-vacuity witness: Theorem 1.3 nonlinear dephasing SDPI instantiates on `Bool × Fin 1`. -/
example (Ψ : DensityOp (Bool × Fin 1)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    qjs (dephaseState η Ψ) (dephaseState η (pauliZTensorI Ψ)) ≤
      gq (qjs Ψ (pauliZTensorI Ψ)) η :=
  theorem_1_3_dephasing_sdpi Ψ η hη0 hη1

end PolarCodes.SanityChecks
