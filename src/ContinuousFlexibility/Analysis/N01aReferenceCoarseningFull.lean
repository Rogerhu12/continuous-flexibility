import ContinuousFlexibility.Analysis.N01aReferenceCoarseningInverse
import ContinuousFlexibility.Analysis.N01aReferenceCoarseningClosure
import ContinuousFlexibility.Analysis.N01aReferenceSourceMeasurability

/-!
# Transporting the complete reference inverse package

The genuine pure-kernel graph supplies signed source measurability through
Green reciprocity. Thus all five parts of the frozen reference inverse
package pass to the coarse partition, including its actual graph topology.
-/

noncomputable section

namespace ContinuousFlexibility.Statements.N01aReferenceCoarsening

variable {D E : ReferenceData} {σ : ℕ → ℕ} (h : N01aReferenceCoarsening D E σ)

theorem reference_properties_of_phi_graph
    (hGeom : RadialProfileGeometry D) (hNatural : RadialNaturalKernels D)
    (hD : RadialPartition D) (hE : RadialPartition E)
    {γ M₀ M₁ : ℝ} {G : RadialSource → RadialUnknown}
    (hProperties : ReferenceInverseProperties D γ M₀ M₁ G ∧
      ReferenceGraphClosed D γ M₀ M₁ ∧ ReferenceSmoothCoreClosure D γ M₀ M₁ ∧
      ReferenceGreenReciprocity D γ M₀ M₁ ∧ FirstNormalInverseEstimate D γ M₀ M₁ G)
    (hPure : ReferenceGraph D γ M₀ M₁
      ((fun p => D.phi p.1 * Radial.cosineMode 2 p.2), 0)
      ((0 : PolarPoint → ℝ), 1)) :
    ReferenceInverseProperties E γ M₀ M₁ G ∧
      ReferenceGraphClosed E γ M₀ M₁ ∧ ReferenceSmoothCoreClosure E γ M₀ M₁ ∧
      ReferenceGreenReciprocity E γ M₀ M₁ ∧ FirstNormalInverseEstimate E γ M₀ M₁ G := by
  obtain ⟨hG, hClosed, hCore, hRecip, hNormal⟩ := hProperties
  have hab : D.a ≤ D.b := hGeom.2.1.le
  have hMeas := n01a_source_aemeasurable_of_reference_phi_graph
    hGeom hNatural hG hRecip hPure
  exact ⟨h.inverse_properties hD hE hab hG,
    h.graph_closed_of_source_aemeasurable hD hE hab hMeas hClosed,
    h.smooth_core_closure_of_source_aemeasurable hD hE hab hMeas hCore,
    h.green_reciprocity hD hE hab hRecip,
    h.first_normal_estimate hD hE hab hNormal⟩

end ContinuousFlexibility.Statements.N01aReferenceCoarsening
