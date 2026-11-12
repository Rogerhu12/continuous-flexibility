import ContinuousFlexibility.Analysis.CanonicalJetNormalization
import ContinuousFlexibility.Analysis.N04bFieldRegularity

/-!
# Retaining primitive geometry through the final operator normalization

The normalization changes only potential and divided coefficients. Every
field used by the primitive geometry retains its actual value, including
the material cell. The physical coefficient clause is supplied directly
by the controlled field's existing smoothness and periodicity certificate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04Coordinates_primitiveGeometry_normalized
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (h : CanonicalPrimitiveGeometry D T S C L K base ε) :
    CanonicalPrimitiveGeometry D T S C L (normalizedCanonicalData S K) base ε := by
  exact
    { materialJets := h.materialJets
      transport := h.transport
      physicalCoefficients := h.physicalCoefficients }

theorem n04Coordinates_physicalCoefficients_of_fieldRegularity
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {base : ℕ} {ε : ℝ} (h : N04bFieldRegularity D S C L base ε) :
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ContDiffOn ℝ ∞ (L.coefficients z).a (annularOpen D) ∧
      ContDiffOn ℝ ∞ (L.coefficients z).b (annularOpen D) ∧
      ContDiffOn ℝ ∞ (L.coefficients z).c (annularOpen D) ∧
      (∀ r ∈ radialCore D,
        Function.Periodic (fun θ => (L.coefficients z).b (r, θ)) Real.pi) ∧
      (∀ r ∈ radialCore D,
        Function.Periodic (fun θ => (L.coefficients z).c (r, θ)) Real.pi) := by
  intro z hz hs
  obtain ⟨ha, hb, hc⟩ := h.smooth_coefficients z hz hs
  refine ⟨ha, hb, hc, ?_, ?_⟩
  · intro r hr
    exact (h.periodic_coefficients z hz hs r hr).2.1
  · intro r hr
    exact (h.periodic_coefficients z hz hs r hr).2.2

end ContinuousFlexibility.Analysis
