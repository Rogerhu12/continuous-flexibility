import ContinuousFlexibility.Analysis.N07aCurrentPhysicalGeometry
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Rough pairing through the actual canonical chart

The reflected periodic chart preserves the actual half-period cell. The
ordinary plane change-of-variables theorem therefore extends the original
smooth pairing identity to arbitrary representatives, with an exact
integrability equivalence. No regularity of the unknown is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory Module
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n07a_planeJacobian_eq_det (F : PolarPoint → PolarPoint) (p : PolarPoint) :
    planeJacobian F p = (fderiv ℝ F p).det :=
  planeJacobian_eq_fderiv_det F p

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

private theorem n07a_canonical_pairing_cancel (m : ℕ) (u f : PolarPoint → ℝ)
    {p : PolarPoint} (hinv : K.inverseChart z m (K.chart z m p) = p)
    (hh : K.height z m p ≠ 0) (hj : planeJacobian (K.chart z m) p ≠ 0) :
    |(fderiv ℝ (K.chart z m) p).det| •
      (canonicalHeight S K z m u (K.chart z m p) *
        canonicalSource S K z m f (K.chart z m p)) = u p * f p := by
  rw [← n07a_planeJacobian_eq_det]
  simp only [canonicalHeight, canonicalSource, hinv, smul_eq_mul]
  field_simp [hh, abs_ne_zero.mpr hj]

/-- The geometric pairing is valid for arbitrary actual functions, including
the rough representatives in the reference and perturbed graph relations. -/
theorem n07a_canonical_pairing_all
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (u f : PolarPoint → ℝ) :
    (∫ p in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
      u p * f p) =
    ∫ p, canonicalHeight S K z m u p * canonicalSource S K z m f p
      ∂canonicalMeasure S K m := by
  simpa only [canonicalMeasure, canonicalOpen, prod_inter_prod,
    inter_univ, univ_inter] using
    canonicalSource_pairing_of_partA h04.1 hz hs m u f

/-- The same actual chart equivalence preserves integrability of the paired
functions; this permits Fubini for weak equations without a smooth unknown. -/
theorem n07a_canonical_pairing_integrable_iff
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (u f : PolarPoint → ℝ) :
    Integrable (fun p => canonicalHeight S K z m u p * canonicalSource S K z m f p)
      (canonicalMeasure S K m) ↔
    IntegrableOn (fun p => u p * f p)
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) := by
  obtain ⟨himage, hinj, hderiv, hpoint⟩ := n07a_physicalHalfGeometry h04 hz hs m
  have hQ := ((h04.1.domains z hz hs m).1.inter
    (isOpen_univ.prod isOpen_Ioo)).measurableSet
  have hcov := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    hQ hderiv hinj
    (fun p => canonicalHeight S K z m u p * canonicalSource S K z m f p)
  rw [himage] at hcov
  change Integrable _ (canonicalMeasure S K m) ↔
    Integrable _ (n07aPhysicalMeasure S K z m)
  rw [n07a_canonicalMeasure_eq_openAngularStrip,
    n07aPhysicalMeasure_eq_openAngularStrip]
  apply hcov.trans
  apply integrable_congr
  filter_upwards [ae_restrict_mem hQ] with p hp
  have h := hpoint p hp
  exact n07a_canonical_pairing_cancel m u f h.1 h.2.1 h.2.2

end ContinuousFlexibility.Analysis
