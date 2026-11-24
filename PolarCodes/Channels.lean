/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.QuantumStates

/-!
# Binary-Input Classical–Quantum Channels and Polar Combinations

This module formalizes Section 2.2 of the manuscript:
- Binary-input c-q channels `CQChannel d` (`W : Bool → DensityOp d`)
- Conditional entropy `H(W) = 1 - QJS(ρ₀, ρ₁)`, symmetric capacity `I(W) = QJS(ρ₀, ρ₁)`,
  and fidelity parameter `Z(W) = F(ρ₀, ρ₁)` (Eq. 2.4)
- Standard channel families: `bscChannel`, `becChannel`, `pureChannel`
- **Definition 2.1**: Polar channel combinations `checkCombine` (`W₁ ⊠ W₂`) and
  `varCombine` (`W₁ ⊛ W₂`), and `minusChannel` (`W⁻`), `plusChannel` (`W⁺`)
-/

open Matrix BigOperators Real

namespace PolarCodes

/-- A binary-input classical–quantum (c-q) channel `W : {0, 1} → D(ℂ^d)`. -/
structure CQChannel (d : Type*) [Fintype d] [DecidableEq d] where
  out : Bool → DensityOp d

namespace CQChannel

variable {d d₁ d₂ : Type*} [Fintype d] [DecidableEq d]
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-- Conditional entropy `H(W) := H(X | B) = 1 - QJS(ρ₀, ρ₁)` (Eq. 2.4). -/
noncomputable def condEntropy (W : CQChannel d) : ℝ :=
  1 - qjs (W.out false) (W.out true)

/-- Symmetric Holevo capacity `I(W) := 1 - H(W) = QJS(ρ₀, ρ₁)` (Eq. 2.4). -/
noncomputable def symCapacity (W : CQChannel d) : ℝ :=
  qjs (W.out false) (W.out true)

/-- Fidelity (quantum Bhattacharyya) parameter `Z(W) := F(ρ₀, ρ₁)` (Eq. 2.4). -/
noncomputable def fidelityParam (W : CQChannel d) : ℝ :=
  rootFidelity (W.out false) (W.out true)

/-- Polarization potential `T(W) := √(H(W)(1 - H(W)))` (Eq. 1.9). -/
noncomputable def potential (W : CQChannel d) : ℝ :=
  Real.sqrt (W.condEntropy * (1 - W.condEntropy))

lemma symCapacity_eq_one_sub_condEntropy (W : CQChannel d) :
    W.symCapacity = 1 - W.condEntropy := by
  unfold symCapacity condEntropy; ring

/-- Classical register projection `|b⟩⟨b|` on `ℂ²` (`Bool`). -/
def ketBraBool (b : Bool) : DensityOp Bool where
  mat := Matrix.of (fun i j ↦ if i = b ∧ j = b then (1 : ℂ) else 0)
  posSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_ite, star_one, star_zero]
      split_ifs with h1 h2
      · rfl
      · exact absurd ⟨h1.2, h1.1⟩ h2
      · exact absurd ⟨h2.2, h2.1⟩ h1
      · rfl
    · intro x
      have hmul : ∀ i, (Matrix.of (fun i j ↦ if i = b ∧ j = b then (1 : ℂ) else 0) *ᵥ x) i =
          if i = b then x b else 0 := by
        intro i
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        by_cases hi : i = b
        · subst hi; simp
        · simp [hi]
      simp only [dotProduct, hmul]
      have hsum : ∑ i : Bool, star (x i) * (if i = b then x b else 0) = star (x b) * x b := by
        rw [Finset.sum_eq_single b]
        · simp
        · intro i _ hib; simp [hib]
        · intro hb; exact absurd (Finset.mem_univ b) hb
      rw [hsum]
      exact Complex.mul_conj_nonneg (x b)
  trace_one := by
    simp [Matrix.trace, Matrix.diag]

/-- **Definition 2.1 (Check-node / minus combination)**:
`(W₁ ⊠ W₂)(u₁) := ½ (ρ_{u₁} ⊗ σ₀ + ρ_{u₁ ⊕ 1} ⊗ σ₁)` (Eq. 2.5). -/
noncomputable def checkCombine (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    CQChannel (d₁ × d₂) where
  out u₁ := DensityOp.midpoint
    (DensityOp.tensor (W₁.out u₁) (W₂.out false))
    (DensityOp.tensor (W₁.out (!u₁)) (W₂.out true))

/-- **Definition 2.1 (Variable-node / plus combination)**:
`(W₁ ⊛ W₂)(u₂) := ½ |0⟩⟨0| ⊗ ρ_{u₂} ⊗ σ_{u₂} + ½ |1⟩⟨1| ⊗ ρ_{u₂ ⊕ 1} ⊗ σ_{u₂}` (Eq. 2.6). -/
noncomputable def varCombine (W₁ : CQChannel d₁) (W₂ : CQChannel d₂) :
    CQChannel (Bool × (d₁ × d₂)) where
  out u₂ := DensityOp.midpoint
    (DensityOp.tensor (ketBraBool false) (DensityOp.tensor (W₁.out u₂) (W₂.out u₂)))
    (DensityOp.tensor (ketBraBool true) (DensityOp.tensor (W₁.out (!u₂)) (W₂.out u₂)))

/-- Check-node polarization `W⁻ := W ⊠ W`. -/
noncomputable def minusChannel (W : CQChannel d) : CQChannel (d × d) :=
  checkCombine W W

/-- Variable-node polarization `W⁺ := W ⊛ W`. -/
noncomputable def plusChannel (W : CQChannel d) : CQChannel (Bool × (d × d)) :=
  varCombine W W

/-- A binary-input c-q channel is *pure-state* if both output density operators have rank 1
(`ρ_x = |φ_x⟩⟨φ_x|` for unit vectors `φ₀, φ₁`). -/
def IsPureState (W : CQChannel d) : Prop :=
  ∃ φ₀ φ₁ : d → ℂ,
    (∑ i, ‖φ₀ i‖ ^ 2 = 1) ∧ (∑ i, ‖φ₁ i‖ ^ 2 = 1) ∧
    (W.out false).mat = Matrix.of (fun i j ↦ φ₀ i * star (φ₀ j)) ∧
    (W.out true).mat = Matrix.of (fun i j ↦ φ₁ i * star (φ₁ j))

/-- A binary-input c-q channel is *classical* if its output states commute (`ρ₀ ρ₁ = ρ₁ ρ₀`). -/
def IsClassical (W : CQChannel d) : Prop :=
  (W.out false).mat * (W.out true).mat = (W.out true).mat * (W.out false).mat

end CQChannel

end PolarCodes
