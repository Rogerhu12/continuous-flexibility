import ContinuousFlexibility.Statements.N06PrimitiveGeometryBridge

/-!
# Spatial return-correction regularity already retained by the primitive geometry

The actual coefficient fields in the N04 primitive payload give the raw
smoothness and angular period required by the distributional pairing. This
projection uses the same correction and does not reselect its coefficients.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n06_returnCorrectionSpatial_of_primitive
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ}
    (hG : CanonicalPrimitiveGeometry D T S C L K base ε) :
    ReturnCorrectionSpatialProperties D S C L base ε := by
  intro z hz hs
  obtain ⟨_, hb, hc, hbp, hcp⟩ := hG.physicalCoefficients z hz hs
  refine ⟨hb, hc, ?_⟩
  rintro ⟨r, θ⟩ hp
  have hr : r ∈ radialCore D := hp.1
  constructor
  · simpa only [Prod.mk_add_mk, add_zero] using hbp r hr θ
  · simpa only [Prod.mk_add_mk, add_zero] using hcp r hr θ

end ContinuousFlexibility.Analysis
