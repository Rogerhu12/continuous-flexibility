import ContinuousFlexibility.Blueprint.CanonicalParts
import Mathlib.Analysis.Convex.Topology

/-!
# Connected actual pieces and their reflection-axis points

The current physical domain is the image of the fixed canonical strip
under its genuine continuous inverse. Thus connectedness and an axis
point follow from the existing chart contract even for curved cuts.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem canonicalInverse_image_open
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : Blueprint.N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) :
    K.inverseChart z m '' canonicalOpen S K m = physicalPieceOpen S K z m := by
  have hcharts := hK.charts z hz hsector m
  apply Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    exact hcharts.2.1 hq
  · intro p hp
    exact ⟨K.chart z m p, hcharts.1 hp, hcharts.2.2.1 p hp⟩

theorem canonicalPhysicalPiece_isPreconnected
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : Blueprint.N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) :
    IsPreconnected (physicalPieceOpen S K z m) := by
  have hstrip : IsPreconnected (canonicalOpen S K m) :=
    ((convex_Ioo (K.left m) (K.right m)).prod
      (convex_univ : Convex ℝ (univ : Set ℝ))).isPreconnected
  rw [← canonicalInverse_image_open hK hz hsector m]
  exact hstrip.image (K.inverseChart z m)
    (hK.charts z hz hsector m).2.2.2.2.2.1.continuousOn

theorem canonicalPhysicalPiece_exists_axis_point
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : Blueprint.N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) :
    ∃ p ∈ physicalPieceOpen S K z m, p.2 = 0 := by
  let q : PolarPoint := ((K.left m + K.right m) / 2, 0)
  have hq : q ∈ canonicalOpen S K m := by
    have hab := (hK.referenceBounds m).2.1
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> dsimp only [q] <;> linarith
  have he : (K.inverseChart z m q).2 = -(K.inverseChart z m q).2 := by
    simpa only [q, neg_zero] using
      congrArg Prod.snd (hK.inverseReflection z hz hsector m q hq)
  exact ⟨K.inverseChart z m q, (hK.charts z hz hsector m).2.1 hq, by linarith⟩

/-- The actual N03 odd mixed coefficient vanishes at an actual point of
each canonical piece; no rectangular shape of the physical domain is used. -/
theorem canonicalPhysicalPiece_exists_zero_mixedCoefficient
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : Blueprint.N04PartA D S C K base ε)
    (hN : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) :
    ∃ p ∈ physicalPieceOpen S K z m, (L.coefficients z).b p = 0 := by
  obtain ⟨p, hp, hzero⟩ := canonicalPhysicalPiece_exists_axis_point hK hz hsector m
  have he := (hN.2.2.2.1 z hz hsector p.1 0).2.1
  have hvalue : (L.coefficients z).b (p.1, 0) = 0 := by
    simp only [neg_zero] at he
    linarith only [he]
  refine ⟨p, hp, ?_⟩
  have hpoint : p = (p.1, 0) := Prod.ext rfl hzero
  rw [hpoint]
  exact hvalue

end ContinuousFlexibility.Analysis
