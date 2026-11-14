module

public import ContinuousFlexibility.Analysis.CanonicalSourceConversion
public import ContinuousFlexibility.Analysis.SpacesLpCurveDerivative

/-!
# Actual chart change of variables for the source energy

These formulas apply to arbitrary canonical functions, including every
actual angular source jet. Integrability is transported by its own
equivalence, independently of the totalized integral identity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hK : N04PartA D S C K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1)

include hK hz hs

/-- Actual integrability is preserved by the Jacobian-weighted pullback
from one canonical period to its prescribed physical piece. -/
theorem n07b_sourceBound_integrable_chart_iff (m : ℕ) (g : PolarPoint → ℝ) :
    Integrable g (canonicalMeasure S K m) ↔
      IntegrableOn (fun p => |planeJacobian (K.chart z m) p| * g (K.chart z m p))
        (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) := by
  let : (volume : Measure PolarPoint).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hphysicalOpen : IsOpen (physicalPieceOpen S K z m) :=
    (hK.domains z hz hs m).1
  have hphys : volume.restrict
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) =
      volume.restrict (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) := by
    apply Measure.restrict_congr_set
    exact polarDomain_Ioc_ae_eq_Ioo (physicalPieceOpen S K z m) 0 Real.pi
  have hcan : canonicalMeasure S K m = volume.restrict
      (canonicalOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) := by
    apply Measure.restrict_congr_set
    simpa only [canonicalOpen, prod_inter_prod, inter_univ, univ_inter] using
      polarStrip_Ioc_ae_eq_Ioo (K.left m) (K.right m) 0 Real.pi
  change Integrable g (canonicalMeasure S K m) ↔
    Integrable (fun p => |planeJacobian (K.chart z m) p| * g (K.chart z m p))
      (volume.restrict (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)))
  rw [hcan, hphys]
  have hcharts := hK.charts z hz hs m
  have hU : MeasurableSet
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) :=
    hphysicalOpen.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioo)
  have hd : ∀ p ∈ physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi),
      HasFDerivWithinAt (K.chart z m) (fderiv ℝ (K.chart z m) p)
        (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) p := by
    intro p hp
    exact ((hcharts.2.2.2.2.1.contDiffAt
      (hphysicalOpen.mem_nhds hp.1)).differentiableAt
        (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn (K.chart z m)
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) :=
    (canonicalChart_injOn hK hz hs m).mono inter_subset_left
  have hc := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (volume : Measure PolarPoint) hU hd hinj g
  rw [canonicalChart_image_openStrip hK hz hs m] at hc
  simpa only [IntegrableOn, ← planeJacobian_eq_fderiv_det, smul_eq_mul] using hc

/-- The corresponding raw integral identity uses the same actual chart
and the same half-open angular period on both sides. -/
theorem n07b_sourceBound_integral_chart (m : ℕ) (g : PolarPoint → ℝ) :
    (∫ p, g p ∂canonicalMeasure S K m) =
      ∫ p in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        |planeJacobian (K.chart z m) p| * g (K.chart z m p) := by
  let : (volume : Measure PolarPoint).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hphysicalOpen : IsOpen (physicalPieceOpen S K z m) :=
    (hK.domains z hz hs m).1
  have hphys : volume.restrict
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) =
      volume.restrict (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) := by
    apply Measure.restrict_congr_set
    exact polarDomain_Ioc_ae_eq_Ioo (physicalPieceOpen S K z m) 0 Real.pi
  have hcan : canonicalMeasure S K m = volume.restrict
      (canonicalOpen S K m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) := by
    apply Measure.restrict_congr_set
    simpa only [canonicalOpen, prod_inter_prod, inter_univ, univ_inter] using
      polarStrip_Ioc_ae_eq_Ioo (K.left m) (K.right m) 0 Real.pi
  rw [hcan, hphys]
  have hcharts := hK.charts z hz hs m
  have hU : MeasurableSet
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) :=
    hphysicalOpen.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioo)
  have hd : ∀ p ∈ physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi),
      HasFDerivWithinAt (K.chart z m) (fderiv ℝ (K.chart z m) p)
        (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) p := by
    intro p hp
    exact ((hcharts.2.2.2.2.1.contDiffAt
      (hphysicalOpen.mem_nhds hp.1)).differentiableAt
        (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn (K.chart z m)
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioo (0 : ℝ) Real.pi)) :=
    (canonicalChart_injOn hK hz hs m).mono inter_subset_left
  have hc := integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure PolarPoint) hU hd hinj g
  rw [canonicalChart_image_openStrip hK hz hs m] at hc
  simpa only [← planeJacobian_eq_fderiv_det, smul_eq_mul] using hc

theorem n07b_sourceBound_square_integrable (m : ℕ) {g : PolarPoint → ℝ}
    (hg : MemLp g 2 (canonicalMeasure S K m)) :
    IntegrableOn (fun p => |planeJacobian (K.chart z m) p| * (g (K.chart z m p)) ^ 2)
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) :=
  (n07b_sourceBound_integrable_chart_iff hK hz hs m (fun p => g p ^ 2)).mp hg.integrable_sq

/-- The square of the genuine canonical `L²` norm is its physical
Jacobian-weighted square integral. -/
theorem n07b_sourceBound_eLpNorm_sq (m : ℕ) {g : PolarPoint → ℝ}
    (hg : MemLp g 2 (canonicalMeasure S K m)) :
    (eLpNorm g 2 (canonicalMeasure S K m)).toReal ^ 2 =
      ∫ p in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        |planeJacobian (K.chart z m) p| * (g (K.chart z m p)) ^ 2 := by
  calc
    _ = ‖hg.toLp g‖ ^ 2 := by rw [Lp.norm_toLp]
    _ = ∫ p, g p ^ 2 ∂canonicalMeasure S K m := spaces_lp_norm_sq_toLp hg
    _ = _ := n07b_sourceBound_integral_chart hK hz hs m (fun p => g p ^ 2)

end ContinuousFlexibility.Analysis
