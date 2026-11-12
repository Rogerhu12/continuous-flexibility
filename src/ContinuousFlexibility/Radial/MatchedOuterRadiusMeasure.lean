import ContinuousFlexibility.Radial.MatchedRadiusGreenKernel
import ContinuousFlexibility.Radial.OuterWholeMeasure

/-!
# The same whole-tail Green inverse on the scaled physical profile

The whole outward measure is derived from the existing exact radial
measure law.  The already constructed radius isometry therefore applies
to the actual whole-tail spaces on both ends, including the left end.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements

/-- Reflection commutes with the positive physical radius change, so
the same height factor is the Jacobian of the whole outward measure. -/
theorem outerWholeMeasure_radiusScale
    {D E : ReferenceData} {κ β entry : ℝ} {right : Bool}
    (hκ : 0 < κ) (hβ : 0 < β)
    (hD : entry ∈ radialCore D) (hE : κ * entry ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right entry,
      E.w (κ * r) = (β * κ) * D.w r) :
    outerWholeMeasure E right (κ * entry) =
      ENNReal.ofReal β • (outerWholeMeasure D right entry).map (fun x => κ * x) := by
  have hmul : Measurable (fun r : ℝ => κ * r) :=
    measurable_const.mul measurable_id
  have hout := (measurableEmbedding_outerOutwardRadius right).measurable
  have hcomm : outerOutwardRadius right ∘ (fun r : ℝ => κ * r) =
      (fun r : ℝ => κ * r) ∘ outerOutwardRadius right := by
    funext r
    cases right <;> simp only [Function.comp_def, outerOutwardRadius,
      Bool.false_eq_true, ite_false, ite_true]
    ring
  rw [outerWholeMeasure,
    radialHilbertMeasure_restrict_tail_radiusScale hκ hβ right hD hE hend hprofile,
    Measure.map_smul _ hout.aemeasurable, Measure.map_map hout hmul]
  change ENNReal.ofReal β •
      ((radialHilbertMeasure D).restrict (radialTailInterval D right entry)).map
        (outerOutwardRadius right ∘ (fun r : ℝ => κ * r)) =
    ENNReal.ofReal β •
      ((((radialHilbertMeasure D).restrict (radialTailInterval D right entry)).map
        (outerOutwardRadius right)).map (fun r : ℝ => κ * r))
  rw [Measure.map_map hmul hout, hcomm]

/-- The actual natural function of the original whole problem remains
an L² function after the physical dilation. -/
theorem outerWhole_memLp_radiusScale
    {D E : ReferenceData} {κ β entry : ℝ} {right : Bool}
    (hκ : 0 < κ) (hβ : 0 < β)
    (hD : entry ∈ radialCore D) (hE : κ * entry ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right entry,
      E.w (κ * r) = (β * κ) * D.w r)
    {V : ℝ → ℝ} (hV : MemLp V 2 (outerWholeMeasure D right entry)) :
    MemLp (fun x => V (x / κ)) 2 (outerWholeMeasure E right (κ * entry)) :=
  memLp_inverseRadiusPullback hκ.ne'
    (outerWholeMeasure_radiusScale hκ hβ hD hE hend hprofile) hV

/-- The supplied whole inverse, transported by the actual measure
isometry, retains the Green kernel of the same homogeneous pair. -/
theorem outerWhole_inverseRadiusOperator_kernel
    {D E : ReferenceData} {κ β entry : ℝ} {right : Bool}
    (hκ : 0 < κ) (hβ : 0 < β)
    (hD : entry ∈ radialCore D) (hE : κ * entry ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right entry,
      E.w (κ * r) = (β * κ) * D.w r)
    (R : OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry)
    (lam : ℝ) (U V : ℝ → ℝ)
    (hR : ∀ f : OuterWholeL2 D right entry,
      (R f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry]
        fun x => ∫ y, outerGreenKernel lam U V x y * f y
          ∂outerWholeMeasure D right entry)
    (f : OuterWholeL2 E right (κ * entry)) :
    (inverseRadiusOperator hκ.ne' hβ
      (outerWholeMeasure_radiusScale hκ hβ hD hE hend hprofile) R f : ℝ → ℝ)
      =ᵐ[outerWholeMeasure E right (κ * entry)]
        fun x => ∫ y, outerGreenKernel (β * lam) (fun r => U (r / κ))
          (fun r => V (r / κ)) x y * f y ∂outerWholeMeasure E right (κ * entry) :=
  inverseRadiusOperator_outerGreenKernel hκ hβ
    (outerWholeMeasure_radiusScale hκ hβ hD hE hend hprofile) R lam U V hR f

end ContinuousFlexibility.Radial
