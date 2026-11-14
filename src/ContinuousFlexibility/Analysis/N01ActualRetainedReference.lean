module

public import ContinuousFlexibility.Analysis.N01cActualReferenceWith

/-!
# Retaining the actual geometric witness through reference completion

The completed inverse and the retained tail geometry belong to the same
reference. This extraction preserves the actual metadata and profile
identity; it does not identify a previously arbitrary Through03 witness
with a newly constructed reference.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

/-- The genuine regional matching construction produces one reference
with its retained-coordinate certificate still available. -/
theorem n01c_exists_actual_retained_reference :
    ∃ S : SelectedTailData, ∃ K : SeedCentralCutoff,
      ∃ Cstar : ℝ, ∃ requested : ℕ, ∃ length : ℝ,
      ∃ metadata : R10aSelectedMetadata Cstar requested S,
      ∃ P : SeedRetainedPair S K 1 length, ∃ Γ : ConnectedReferenceGeometry,
        4096 ≤ S.chain.index ∧ Γ.Realizes ∧
        Γ.reference.w = P.pair.profile ∧
        RadialConstructionGeometry Γ.reference ∧
        R11aRetainedCoordinates P Γ ∧ IsRadialReference Γ.reference := by
  obtain ⟨D, hD, S, K, Cstar, requested, length, metadata, P, Γ,
    hreference, hindex, hΓ, hw, hconstruction, hcoordinates⟩ :=
    n01c_actual_reference_with
      (fun D => ∃ S : SelectedTailData, ∃ K : SeedCentralCutoff,
        ∃ Cstar : ℝ, ∃ requested : ℕ, ∃ length : ℝ,
        ∃ metadata : R10aSelectedMetadata Cstar requested S,
        ∃ P : SeedRetainedPair S K 1 length, ∃ Γ : ConnectedReferenceGeometry,
          Γ.reference = D ∧ 4096 ≤ S.chain.index ∧ Γ.Realizes ∧
          Γ.reference.w = P.pair.profile ∧
          RadialConstructionGeometry Γ.reference ∧ R11aRetainedCoordinates P Γ) (by
        intro S K Cstar requested length metadata P Γ hindex hΓ hw hconstruction hcoordinates
        exact ⟨S, K, Cstar, requested, length, metadata, P, Γ,
          rfl, hindex, hΓ, hw, hconstruction, hcoordinates⟩)
  exact ⟨S, K, Cstar, requested, length, metadata, P, Γ,
    hindex, hΓ, hw, hconstruction, hcoordinates, hreference.symm ▸ hD⟩

end ContinuousFlexibility.Radial
