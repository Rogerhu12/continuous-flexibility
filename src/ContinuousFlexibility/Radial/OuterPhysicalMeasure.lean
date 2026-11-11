import ContinuousFlexibility.Radial.DeepTailPhysicalLift
import ContinuousFlexibility.Radial.DeepTailPhysicalBounds
import ContinuousFlexibility.Statements.RadialTargets
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The actual logarithmic measure of a physical deep tail

Both orientations use the same absolute Jacobian. The resulting measure is
the restriction of the original radial Hilbert measure, and its pullback is
the physical density 12 w(R)/R. Finiteness of the actual tail measure is
derived from the already proved physical coefficient bound.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency false

theorem measurableEmbedding_tailPhysicalRadius (right : Bool) :
    MeasurableEmbedding (tailPhysicalRadius right) := by
  have he : MeasurableEmbedding Real.exp :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi).comp
      Real.expOrderIso.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  cases right
  · exact he.comp (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding
  · exact he

private theorem hasDerivAt_tailPhysicalRadius (right : Bool) (x : ℝ) :
    HasDerivAt (tailPhysicalRadius right)
      (if right then tailPhysicalRadius right x else -tailPhysicalRadius right x) x := by
  cases right
  · change HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x
    simpa only [mul_neg_one] using (hasDerivAt_neg x).exp
  · exact Real.hasDerivAt_exp x

private theorem tailPhysicalRadius_abs_coefficient (right : Bool) (x : ℝ) :
    |if right then tailPhysicalRadius right x else -tailPhysicalRadius right x| =
      tailPhysicalRadius right x := by
  cases right <;> simp [tailPhysicalRadius, abs_of_pos (Real.exp_pos _)]

theorem tailPhysicalRadius_lintegral_change (right : Bool) {s : Set ℝ}
    (hs : MeasurableSet s) (f : ℝ → ℝ≥0∞) :
    (∫⁻ r in tailPhysicalRadius right '' s, f r) =
      ∫⁻ x in s, ENNReal.ofReal (tailPhysicalRadius right x) *
        f (tailPhysicalRadius right x) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul hs
    (fun x _ => (hasDerivAt_tailPhysicalRadius right x).hasDerivWithinAt)
    (measurableEmbedding_tailPhysicalRadius right).injective.injOn f
  simpa only [tailPhysicalRadius_abs_coefficient] using h

def outerPhysicalPullbackMeasure (D : ReferenceData) (T : DeepTailData)
    (right : Bool) : Measure ℝ :=
  (volume.restrict (Ioo T.entrance T.endpoint)).withDensity
    (fun x => ENNReal.ofReal (12 * D.w (tailPhysicalRadius right x) /
      tailPhysicalRadius right x))

def outerRadialIntervalMeasure (D : ReferenceData) (s : Set ℝ) : Measure ℝ :=
  (volume.restrict s).withDensity (fun r => ENNReal.ofReal (12 * D.w r / r ^ 2))

/-- The Jacobian identity retains the factor 12 exactly. -/
theorem outerPhysicalPullbackMeasure_map (D : ReferenceData) (T : DeepTailData)
    (right : Bool) :
    Measure.map (tailPhysicalRadius right) (outerPhysicalPullbackMeasure D T right) =
      outerRadialIntervalMeasure D
        (tailPhysicalRadius right '' Ioo T.entrance T.endpoint) := by
  ext s hs
  have hR := (measurableEmbedding_tailPhysicalRadius right).measurable
  have hpre := hR hs
  rw [Measure.map_apply hR hs, outerPhysicalPullbackMeasure, withDensity_apply _ hpre]
  calc
    _ = ∫⁻ x in Ioo T.entrance T.endpoint,
        (tailPhysicalRadius right ⁻¹' s).indicator
          (fun x => ENNReal.ofReal (12 * D.w (tailPhysicalRadius right x) /
            tailPhysicalRadius right x)) x := (lintegral_indicator hpre _).symm
    _ = ∫⁻ x in Ioo T.entrance T.endpoint,
        ENNReal.ofReal (tailPhysicalRadius right x) *
          s.indicator (fun r => ENNReal.ofReal (12 * D.w r / r ^ 2))
            (tailPhysicalRadius right x) := by
      apply lintegral_congr
      intro x
      by_cases hx : tailPhysicalRadius right x ∈ s
      · simp only [mem_preimage, hx, indicator_of_mem]
        rw [← ENNReal.ofReal_mul (tailPhysicalRadius_pos right x).le]
        congr 1
        field_simp [(tailPhysicalRadius_pos right x).ne'] <;> ring
      · simp [hx]
    _ = ∫⁻ r in tailPhysicalRadius right '' Ioo T.entrance T.endpoint,
        s.indicator (fun r => ENNReal.ofReal (12 * D.w r / r ^ 2)) r :=
      (tailPhysicalRadius_lintegral_change right measurableSet_Ioo _).symm
    _ = outerRadialIntervalMeasure D
        (tailPhysicalRadius right '' Ioo T.entrance T.endpoint) s := by
      rw [lintegral_indicator hs, outerRadialIntervalMeasure, withDensity_apply _ hs]

/-- The physical interval is exactly the selected oriented radial tail. -/
theorem tailPhysicalRadius_image {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} (hD : IsAccumulatingProfile D)
    (hphysical : TailPhysicalRelation D T right j start) :
    tailPhysicalRadius right '' Ioo T.entrance T.endpoint =
      radialTailInterval D right (tailPhysicalRadius right T.entrance) := by
  obtain ⟨C, hC⟩ := hD
  have ha : 0 < D.a := hC.1.1
  have hb : 0 < D.b := ha.trans hC.1.2.1
  cases right
  · have he : T.endpoint = -Real.log D.a := hphysical.2.1
    have hn : Neg.neg '' Ioo T.entrance T.endpoint =
        Ioo (-T.endpoint) (-T.entrance) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        constructor <;> linarith [hy.1, hy.2]
      · intro hx
        refine ⟨-x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, neg_neg x⟩
    change (Real.exp ∘ Neg.neg) '' Ioo T.entrance T.endpoint =
      Ioo D.a (Real.exp (-T.entrance))
    calc
      _ = Real.exp '' (Neg.neg '' Ioo T.entrance T.endpoint) := by rw [Set.image_image]; rfl
      _ = _ := by rw [hn, Real.image_exp_Ioo, he, neg_neg, Real.exp_log ha]
  · have he : T.endpoint = Real.log D.b := hphysical.2.1
    change Real.exp '' Ioo T.entrance T.endpoint = Ioo (Real.exp T.entrance) D.b
    rw [Real.image_exp_Ioo, he, Real.exp_log hb]

theorem outerPhysicalPullbackMeasure_map_radial {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} (hD : IsAccumulatingProfile D)
    (hphysical : TailPhysicalRelation D T right j start) :
    Measure.map (tailPhysicalRadius right) (outerPhysicalPullbackMeasure D T right) =
      (radialHilbertMeasure D).restrict
        (radialTailInterval D right (tailPhysicalRadius right T.entrance)) := by
  have hs : MeasurableSet (tailPhysicalRadius right '' Ioo T.entrance T.endpoint) :=
    (measurableEmbedding_tailPhysicalRadius right).measurableSet_image.mpr measurableSet_Ioo
  have hsub : tailPhysicalRadius right '' Ioo T.entrance T.endpoint ⊆ radialCore D := by
    rintro r ⟨x, hx, rfl⟩
    exact (hphysical.2.2.1 x hx).1
  rw [outerPhysicalPullbackMeasure_map, ← tailPhysicalRadius_image hD hphysical,
    radialHilbertMeasure, restrict_withDensity hs, Measure.restrict_restrict hs,
    inter_eq_left.mpr hsub]
  rfl

/-- Finiteness used by the full-source Green extension follows from the
actual physical profile, with no finite-mass assumption on abstract tails. -/
theorem isFiniteMeasure_deepTailMeasure_of_physical {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} (hD : IsAccumulatingProfile D)
    (hT : DeepTailHypotheses T) (hphysical : TailPhysicalRelation D T right j start) :
    IsFiniteMeasure (deepTailMeasure T) := by
  obtain ⟨P, _, hP⟩ := tailPhysical_density_bounded hD hT hphysical
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  calc
    (∫⁻ x in Ioo T.entrance T.endpoint, ENNReal.ofReal (T.p x)) ≤
        ∫⁻ _ in Ioo T.entrance T.endpoint, ENNReal.ofReal P := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact ENNReal.ofReal_le_ofReal (hP x (Ioo_subset_Ico_self hx))
    _ < ∞ := by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
        Real.volume_Ioo]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end ContinuousFlexibility.Radial
