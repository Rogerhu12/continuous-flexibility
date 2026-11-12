import ContinuousFlexibility.Analysis.OpenDomainSourcePairing
import ContinuousFlexibility.Analysis.CanonicalStripGeometry

/-!
# Canonical source conversion on the actual physical domain

The state-dependent open domain and the true inverse on the fixed
canonical strip supply the planar change of variables. Intersecting an
arbitrary physical set with an angular boundary line is still null.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

/-- The actual source conversion preserves the unknown-source pairing,
including the totalized integral convention, on the current open domain. -/
theorem canonicalSource_pairing_of_partA
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (u f : PolarPoint → ℝ) :
    (∫ p in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi), u p * f p) =
      ∫ p in canonicalOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        canonicalHeight S K z m u p * canonicalSource S K z m f p := by
  have hdomains := hK.domains z hz hsector m
  have hcharts := hK.charts z hz hsector m
  have hdiff : ∀ p ∈ physicalPieceOpen S K z m,
      DifferentiableAt ℝ (K.chart z m) p := by
    intro p hp
    exact ((hcharts.2.2.2.2.1 p hp).contDiffAt
      (hdomains.1.mem_nhds hp)).differentiableAt (by simp)
  have hconv := integral_source_pairing_on_openDomain hdomains.1 Real.pi_ne_zero
    hcharts.1 hcharts.2.1 hcharts.2.2.1 hcharts.2.2.2.1
    hcharts.2.2.2.2.2.1.continuousOn
    (fun p hp => canonicalInverse_periodic_on_open hK hz hsector m hp)
    (hK.inverseReflection z hz hsector m) hdiff
    (fun p hp => (hcharts.2.2.2.2.2.2.2 p hp).1.ne')
    (fun p hp => (hcharts.2.2.2.2.2.2.2 p hp).2.1) u f
  simpa only [canonicalHeight, canonicalSource] using hconv

end ContinuousFlexibility.Analysis
