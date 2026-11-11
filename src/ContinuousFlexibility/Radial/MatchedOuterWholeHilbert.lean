import ContinuousFlexibility.Radial.OuterWholeMeasure
import ContinuousFlexibility.Analysis.L2RestrictionSplit

/-!
# The actual whole-tail restriction and physical extension

The existing coordinate isometry reflects the restricted physical measure
and its L² classes together. Restriction is contractive and extension is
isometric. Their representative identities hold for every L² source.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

def matchedOuterWholeEquiv (D : ReferenceData) (right : Bool) (entry : ℝ) :
    OuterWholeL2 D right entry ≃ₗᵢ[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right entry)) :=
  coordinateL2Equiv _ (outerOutwardRadius right) (outerOutwardRadius right)
    (measurableEmbedding_outerOutwardRadius right) (outerOutwardRadius_twice right)

theorem matchedOuterWholeEquiv_ae (D : ReferenceData) (right : Bool) (entry : ℝ)
    (f : OuterWholeL2 D right entry) :
    (matchedOuterWholeEquiv D right entry f : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (radialTailInterval D right entry)]
      fun r => f (outerOutwardRadius right r) :=
  coordinateL2Equiv_ae _ (outerOutwardRadius right) (outerOutwardRadius right)
    (measurableEmbedding_outerOutwardRadius right) (outerOutwardRadius_twice right) f

def matchedOuterWholeRestrict (D : ReferenceData) (right : Bool) (entry : ℝ) :
    RadialModeL2 D →L[ℝ] OuterWholeL2 D right entry :=
  (matchedOuterWholeEquiv D right entry).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (l2Restrict (radialHilbertMeasure D) (radialTailInterval D right entry))

theorem matchedOuterWholeRestrict_apply (D : ReferenceData) (right : Bool) (entry : ℝ)
    (f : RadialModeL2 D) :
    matchedOuterWholeRestrict D right entry f =
      (matchedOuterWholeEquiv D right entry).symm
        (l2Restrict (radialHilbertMeasure D) (radialTailInterval D right entry) f) := by
  simp only [matchedOuterWholeRestrict, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]

theorem matchedOuterWholeRestrict_ae (D : ReferenceData) (right : Bool) (entry : ℝ)
    (f : RadialModeL2 D) :
    (f : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (radialTailInterval D right entry)]
      fun r => matchedOuterWholeRestrict D right entry f (outerOutwardRadius right r) := by
  have h := matchedOuterWholeEquiv_ae D right entry (matchedOuterWholeRestrict D right entry f)
  rw [matchedOuterWholeRestrict_apply,
    (matchedOuterWholeEquiv D right entry).apply_symm_apply] at h
  exact (l2Restrict_coeFn (radialHilbertMeasure D) (radialTailInterval D right entry) f).symm.trans h

theorem norm_matchedOuterWholeRestrict_apply_le
    (D : ReferenceData) (right : Bool) (entry : ℝ) (f : RadialModeL2 D) :
    ‖matchedOuterWholeRestrict D right entry f‖ ≤ ‖f‖ := by
  rw [matchedOuterWholeRestrict_apply, LinearIsometryEquiv.norm_map]
  exact ((l2Restrict (radialHilbertMeasure D)
    (radialTailInterval D right entry)).le_opNorm f).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (norm_l2Restrict_le (radialHilbertMeasure D) (radialTailInterval D right entry))
        (norm_nonneg f))

theorem matchedOuterWholeRestrict_representative {D : ReferenceData}
    {right : Bool} {entry : ℝ} (f : RadialModeL2 D) {u : ℝ → ℝ}
    (hu : (f : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (radialTailInterval D right entry)] u) :
    (matchedOuterWholeRestrict D right entry f : ℝ → ℝ) =ᵐ[
      outerWholeMeasure D right entry] fun x => u (outerOutwardRadius right x) := by
  apply (measurableEmbedding_outerOutwardRadius right).ae_map_iff.mpr
  simpa only [outerOutwardRadius_twice] using
    (matchedOuterWholeRestrict_ae D right entry f).symm.trans hu

def matchedOuterWholeExtend (D : ReferenceData) (right : Bool) (entry : ℝ) :
    OuterWholeL2 D right entry →L[ℝ] RadialModeL2 D :=
  (l2ZeroExtend (radialHilbertMeasure D) (radialTailInterval D right entry)
    (by cases right <;> exact measurableSet_Ioo)).comp
    (matchedOuterWholeEquiv D right entry).toContinuousLinearEquiv.toContinuousLinearMap

theorem matchedOuterWholeExtend_apply (D : ReferenceData) (right : Bool) (entry : ℝ)
    (f : OuterWholeL2 D right entry) :
    matchedOuterWholeExtend D right entry f =
      l2ZeroExtend (radialHilbertMeasure D) (radialTailInterval D right entry)
        (by cases right <;> exact measurableSet_Ioo) (matchedOuterWholeEquiv D right entry f) := by
  simp only [matchedOuterWholeExtend, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]

theorem matchedOuterWholeExtend_ae (D : ReferenceData) (right : Bool) (entry : ℝ)
    (f : OuterWholeL2 D right entry) :
    (matchedOuterWholeExtend D right entry f : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (radialTailInterval D right entry).indicator
        (fun r => f (outerOutwardRadius right r)) := by
  rw [matchedOuterWholeExtend_apply]
  filter_upwards [l2ZeroExtend_coeFn (radialHilbertMeasure D)
      (radialTailInterval D right entry) (by cases right <;> exact measurableSet_Ioo)
      (matchedOuterWholeEquiv D right entry f),
    ae_imp_of_ae_restrict (matchedOuterWholeEquiv_ae D right entry f)] with r hE hF
  rw [hE]
  by_cases hr : r ∈ radialTailInterval D right entry
  · rw [indicator_of_mem hr, indicator_of_mem hr, hF hr]
  · rw [indicator_of_notMem hr, indicator_of_notMem hr]

theorem norm_matchedOuterWholeExtend_apply
    (D : ReferenceData) (right : Bool) (entry : ℝ) (f : OuterWholeL2 D right entry) :
    ‖matchedOuterWholeExtend D right entry f‖ = ‖f‖ := by
  rw [matchedOuterWholeExtend_apply, norm_l2ZeroExtend_apply, LinearIsometryEquiv.norm_map]

theorem matchedOuterWholeExtend_representative {D : ReferenceData} {right : Bool} {entry : ℝ}
    (f : OuterWholeL2 D right entry) {u : ℝ → ℝ}
    (hu : (f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry] u) :
    (matchedOuterWholeExtend D right entry f : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (radialTailInterval D right entry).indicator
        (fun r => u (outerOutwardRadius right r)) := by
  have hp := ae_eq_comp (measurableEmbedding_outerOutwardRadius right).measurable.aemeasurable hu
  filter_upwards [matchedOuterWholeExtend_ae D right entry f,
    ae_imp_of_ae_restrict hp] with r hr hp
  rw [hr]
  by_cases hs : r ∈ radialTailInterval D right entry
  · rw [indicator_of_mem hs, indicator_of_mem hs, hp hs]
  · rw [indicator_of_notMem hs, indicator_of_notMem hs]

end ContinuousFlexibility.Radial
