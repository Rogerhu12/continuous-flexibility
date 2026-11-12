import ContinuousFlexibility.Blueprint.CanonicalParts
import ContinuousFlexibility.Analysis.EquivariantOpenDomainStrip

/-!
# The fundamental angular strip of an actual canonical chart

The inverse runs over the fixed canonical rectangle. Its reflection,
translation identity and true inverse fibers identify the fundamental
angular interval, even when the actual physical boundary is curved.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

/-- An actual canonical chart is injective on its whole current piece. -/
theorem canonicalChart_injOn
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : Blueprint.N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) :
    InjOn (K.chart z m) (physicalPieceOpen S K z m) := by
  have hcharts := hK.charts z hz hsector m
  intro p hp q hq heq
  calc
    p = K.inverseChart z m (K.chart z m p) := (hcharts.2.2.1 p hp).symm
    _ = K.inverseChart z m (K.chart z m q) := congrArg (K.inverseChart z m) heq
    _ = q := hcharts.2.2.1 q hq

/-- Forward periodicity and actual domain invariance give inverse
periodicity throughout the fixed canonical strip. -/
theorem canonicalInverse_periodic_on_open
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : Blueprint.N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    K.inverseChart z m (p + (0, Real.pi)) = K.inverseChart z m p + (0, Real.pi) := by
  have hdomains := hK.domains z hz hsector m
  have hcharts := hK.charts z hz hsector m
  exact inverseChart_periodic_on_invariant_domain
    (fun q hq => (hdomains.2.2.2.1 q).mpr hq)
    hcharts.2.1 hcharts.2.2.1 hcharts.2.2.2.1
    (fun q hq => (hcharts.2.2.2.2.2.2.2 q hq).2.2.1) hp

/-- The current physical and canonical fundamental strips have exactly
the same image. No path at a fixed physical radius is required. -/
theorem canonicalChart_image_openStrip
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : Blueprint.N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) :
    K.chart z m '' (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) =
      canonicalOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi) := by
  have hcharts := hK.charts z hz hsector m
  exact equivariantChart_image_openAngularStrip Real.pi_ne_zero
    hcharts.1 hcharts.2.1 hcharts.2.2.1 hcharts.2.2.2.1
    hcharts.2.2.2.2.2.1.continuousOn
    (fun p hp => canonicalInverse_periodic_on_open hK hz hsector m hp)
    (hK.inverseReflection z hz hsector m)

end ContinuousFlexibility.Analysis
