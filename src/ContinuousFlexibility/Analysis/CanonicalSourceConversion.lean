import ContinuousFlexibility.Analysis.CanonicalAngularStripMeasure
import ContinuousFlexibility.Analysis.CanonicalStripGeometry

/-!
# Canonical source conversion on one angular period

The chart geometry in `N04PartA` already suffices for the source-pairing
identity.  Reflection and periodicity identify the image of the open
angular strip; null boundary lines then give the half-open period used
by the physical and canonical integrals.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

/-- The actual source conversion preserves the unknown-source pairing.
No smoothness or integrability conditions on the paired functions are
needed beyond the chart geometry, because change of variables preserves
the totalized Bochner-integral convention as well. -/
theorem canonicalSource_pairing_of_partA
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (u f : PolarPoint → ℝ) :
    (∫ p in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi), u p * f p) =
      ∫ p in canonicalOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        canonicalHeight S K z m u p * canonicalSource S K z m f p := by
  have hphysicalOpen : IsOpen (physicalPieceOpen S K z m) :=
    (hK.domains z hz hsector m).1
  have hphys_ae :
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) =ᵐ[volume]
        (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) := by
    exact polarDomain_Ioc_ae_eq_Ioo (physicalPieceOpen S K z m) 0 Real.pi
  have hcanon_ae :
      (canonicalOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) =ᵐ[volume]
        (canonicalOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) := by
    simpa only [canonicalOpen, prod_inter_prod, inter_univ, univ_inter] using
      polarStrip_Ioc_ae_eq_Ioo (K.left m) (K.right m) 0 Real.pi
  have himage := canonicalChart_image_openStrip hK hz hsector m
  obtain ⟨_, _, hinv, _, hsmooth, _, _, hnonzero⟩ := hK.charts z hz hsector m
  have hmeas : MeasurableSet
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) :=
    (hphysicalOpen.inter (isOpen_univ.prod isOpen_Ioo)).measurableSet
  have hdiff : ∀ p ∈ physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi),
      DifferentiableAt ℝ (K.chart z m) p := by
    intro p hp
    exact ((hsmooth p hp.1).contDiffAt (hphysicalOpen.mem_nhds hp.1)).differentiableAt
      (by simp)
  have hconv := integral_pairing_eq_canonical_of_image hmeas hdiff
    (fun p hp => hinv p hp.1) himage
    (fun p hp => (hnonzero p hp.1).1.ne')
    (fun p hp => (hnonzero p hp.1).2.1) u f
  calc
    _ = ∫ p in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi), u p * f p :=
      setIntegral_congr_set hphys_ae
    _ = ∫ p in canonicalOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi),
        canonicalHeight S K z m u p * canonicalSource S K z m f p := by
      simpa only [canonicalHeight, canonicalSource] using hconv
    _ = _ := setIntegral_congr_set hcanon_ae.symm

end ContinuousFlexibility.Analysis
