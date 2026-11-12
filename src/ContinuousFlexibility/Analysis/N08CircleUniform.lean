import ContinuousFlexibility.Analysis.N08CircleTailComparison
import ContinuousFlexibility.Analysis.N08ControlHeightLocalization
import ContinuousFlexibility.Analysis.N08PhysicalCellEscape
import ContinuousFlexibility.Analysis.N08DiagonalNeighborhood

/-!
# Uniform invertibility of the actual control diagonal

The same diagonal comes from the genuine N02 control derivative. Its tail
bound uses the actual localized height operators and the physical-cell
comparison forced by N01. The remaining finite labels are controlled by
continuity of that same first jet at the reference state.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

theorem n08CircleDiagonal_tail
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) :
    ∃ b : ℕ, ∃ δ : ℝ, ∃ I : Finset ℕ, base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧
      ∀ z ∈ stateNeighborhood S C b δ, stateSector S z.1 → ∀ m, m ∉ I →
        |n08CircleDiagonal hS hR z m - 1| ≤ (1 / 4 : ℝ) := by
  obtain ⟨physical, F, hH, hdecode, hdecay⟩ := n08_control_height_localizations hT hS hN
  exact n08CircleDiagonal_tail_of_height_localizations hT hS hN hR physical F hdecode hdecay
    (n08_physicalCell_invM_tendsto_zero hT hN physical hH)

/-- One stronger physical state neighborhood makes every coefficient of
the actual control column invertible, with both absolute bounds uniform.
There are no extra placement, variation, or stability assumptions. -/
theorem n08CircleDiagonal_uniform
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) :
    ∃ b : ℕ, ∃ δ : ℝ, base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧
      ∀ z ∈ stateNeighborhood S C b δ, stateSector S z.1 →
        ∀ m, (1 / 2 : ℝ) ≤ |n08CircleDiagonal hS hR z m| ∧
          |n08CircleDiagonal hS hR z m| ≤ 2 :=
  n08CircleDiagonal_uniform_of_tail hT hS hN hR (n08CircleDiagonal_tail hT hS hN hR)

end ContinuousFlexibility.Statements
