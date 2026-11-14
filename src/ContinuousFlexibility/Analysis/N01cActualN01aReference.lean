module

public import ContinuousFlexibility.Analysis.N01cActualReferenceWith
public import ContinuousFlexibility.Analysis.N01cActualPrimitiveGeometry
public import ContinuousFlexibility.Analysis.N01cRetainedComponentEnumeration

/-! # The actual N01a reference with both primitive obligations retained -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Radial

/-- Both obligations concern the reference and cells of the actual R11a construction. -/
theorem exists_n01c_actual_n01a_reference :
    ∃ D : RadialReference, N01RadialPrimitiveGeometry D.val ∧
      ∀ host : N01aNegativeComponent D.val → ℕ,
        (∀ J, J.interval ⊆ D.val.cells (host J)) →
        ∃ e : ℕ ≃ N01aNegativeComponent D.val, ∃ B : ℝ, 0 < B ∧
          ∀ m, |(D.val.cellIndex (host (e m)) : ℝ) - D.val.cellIndex m| ≤ B := by
  obtain ⟨D, hD, hgeometry⟩ := n01c_actual_reference_with
    (fun D => N01RadialPrimitiveGeometry D ∧
      ∀ host : N01aNegativeComponent D → ℕ,
        (∀ J, J.interval ⊆ D.cells (host J)) →
        ∃ e : ℕ ≃ N01aNegativeComponent D, ∃ B : ℝ, 0 < B ∧
          ∀ m, |(D.cellIndex (host (e m)) : ℝ) - D.cellIndex m| ≤ B) (by
      intro S K Cstar requested length metadata P Γ hindex hΓ hw hconstruction hcoordinates
      refine ⟨P.n01c_radialPrimitiveGeometry Γ metadata.selected metadata.first_two
        (by omega) zero_lt_one hΓ hw hconstruction hcoordinates, ?_⟩
      intro host hhost
      exact P.n01c_component_enumeration metadata Γ zero_lt_one hΓ hw hcoordinates host hhost)
  exact ⟨⟨D, hD⟩, hgeometry⟩

end ContinuousFlexibility.Statements
