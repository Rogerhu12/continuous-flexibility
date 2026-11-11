import ContinuousFlexibility.Radial.OuterPhysicalInverseGauge
import ContinuousFlexibility.Radial.ModeTestIntegrability
import ContinuousFlexibility.Analysis.L2MeasureCongr

/-!
# The actual exterior measure in the increasing outward coordinate

The coordinate reflection preserves the full weighted Hilbert measure.
Its finite-core complement is exactly the physical deep-tail measure.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

def selectedOutwardDensity (D : ReferenceData) (right : Bool) (x : ℝ) : ℝ :=
  12 * D.w (outerOutwardRadius right x) / x ^ 2

theorem contDiff_outerOutwardRadius (right : Bool) :
    ContDiff ℝ ∞ (outerOutwardRadius right) := by
  cases right
  · exact contDiff_id.neg
  · exact contDiff_id

theorem selectedOutwardDensity_reflect (D : ReferenceData) (right : Bool) (r : ℝ) :
    selectedOutwardDensity D right (outerOutwardRadius right r) = matchingDensity D r := by
  unfold selectedOutwardDensity matchingDensity
  rw [outerOutwardRadius_twice]
  cases right <;> simp [outerOutwardRadius]

theorem selectedOutwardDensity_measurable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (right : Bool) :
    Measurable (selectedOutwardDensity D right) := by
  have hw : Measurable D.w := (matchingProfileGeometry hD).2.2.1.1.continuous.measurable
  have hr := (measurableEmbedding_outerOutwardRadius right).measurable
  exact (measurable_const.mul (hw.comp hr)).div (measurable_id.pow_const 2)

theorem outerOutwardRegionMeasure_eq_density (D : ReferenceData) (right : Bool) (cut : ℝ) :
    outerOutwardIntervalMeasure D right (radialTailInterval D right cut) =
      (volume.restrict (Ioo (outerOutwardRadius right cut)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)))).withDensity
          (fun x => ENNReal.ofReal (selectedOutwardDensity D right x)) := by
  rw [outerOutwardIntervalMeasure, outerOutward_tail_image]
  rfl

/-- Either selected open tail lies in the same radial core. -/
theorem selectedTailInterval_subset_core {D : ReferenceData} {cut : ℝ}
    (hcut : cut ∈ radialCore D) (right : Bool) :
    radialTailInterval D right cut ⊆ radialCore D := by
  cases right
  · intro r hr
    exact ⟨hr.1, hr.2.trans hcut.2⟩
  · intro r hr
    exact ⟨hcut.1.trans hr.1, hr.2⟩

theorem outerOutwardRegionMeasure_eq_map {D : ReferenceData} {right : Bool} {cut : ℝ}
    (hcut : cut ∈ radialCore D) :
    outerOutwardIntervalMeasure D right (radialTailInterval D right cut) =
      Measure.map (outerOutwardRadius right)
        ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) := by
  have hs : MeasurableSet (radialTailInterval D right cut) := by
    cases right <;> exact measurableSet_Ioo
  have hsub : radialTailInterval D right cut ⊆ radialCore D :=
    selectedTailInterval_subset_core hcut right
  rw [← outerOutwardIntervalMeasure_map D right hs, radialHilbertMeasure,
    restrict_withDensity hs, Measure.restrict_restrict hs, inter_eq_left.mpr hsub]
  rfl

def outerRegionEquiv {D : ReferenceData} {right : Bool} {cut : ℝ}
    (hcut : cut ∈ radialCore D) :
    Lp ℝ 2 (outerOutwardIntervalMeasure D right (radialTailInterval D right cut)) ≃ₗᵢ[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) :=
  l2EquivCompose (l2MeasureCongr (outerOutwardRegionMeasure_eq_map hcut))
    (coordinateL2Equiv _ (outerOutwardRadius right) (outerOutwardRadius right)
      (measurableEmbedding_outerOutwardRadius right) (outerOutwardRadius_twice right))

theorem outerRegionEquiv_ae {D : ReferenceData} {right : Bool} {cut : ℝ}
    (hcut : cut ∈ radialCore D)
    (f : Lp ℝ 2 (outerOutwardIntervalMeasure D right (radialTailInterval D right cut))) :
    (outerRegionEquiv hcut f : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (radialTailInterval D right cut)]
        fun r => f (outerOutwardRadius right r) := by
  rw [outerRegionEquiv, l2EquivCompose_apply]
  exact (coordinateL2Equiv_ae _ _ _ (measurableEmbedding_outerOutwardRadius right)
    (outerOutwardRadius_twice right) _).trans
      (ae_eq_comp (measurableEmbedding_outerOutwardRadius right).measurable.aemeasurable
        (l2MeasureCongr_ae (outerOutwardRegionMeasure_eq_map hcut) f))

theorem outerOutwardRadius_mem_core {D : ReferenceData} {right : Bool} {cut x : ℝ}
    (hcut : cut ∈ radialCore D)
    (hx : x ∈ Ico (outerOutwardRadius right cut)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    outerOutwardRadius right x ∈ radialCore D := by
  cases right
  · change -cut ≤ x ∧ x < -D.a at hx
    change D.a < -x ∧ -x < D.b
    constructor <;> linarith [hcut.2]
  · change cut ≤ x ∧ x < D.b at hx
    exact ⟨hcut.1.trans_le hx.1, hx.2⟩

theorem selectedOutwardDensity_pos {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {right : Bool} {cut : ℝ} (hcut : cut ∈ radialCore D) (x : ℝ)
    (hx : x ∈ Ico (outerOutwardRadius right cut)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    0 < selectedOutwardDensity D right x := by
  have hp := matchingDensity_pos hD (outerOutwardRadius_mem_core hcut hx)
  simpa only [← selectedOutwardDensity_reflect D right, outerOutwardRadius_twice] using hp

theorem isFiniteMeasure_outerOutwardRegion {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {right : Bool} {cut : ℝ}
    (hcut : cut ∈ radialCore D) :
    IsFiniteMeasure (outerOutwardIntervalMeasure D right (radialTailInterval D right cut)) := by
  letI : IsFiniteMeasure (radialHilbertMeasure D) := radialHilbertMeasure_isFinite hD
  rw [outerOutwardRegionMeasure_eq_map hcut]
  infer_instance

theorem outerOutwardRegion_ae_iff {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {right : Bool} {cut : ℝ} (hcut : cut ∈ radialCore D) {p : ℝ → Prop} :
    (∀ᵐ x ∂outerOutwardIntervalMeasure D right (radialTailInterval D right cut), p x) ↔
      ∀ᵐ x ∂volume.restrict (Ioo (outerOutwardRadius right cut)
        (outerOutwardRadius right (tailPhysicalEndpoint D right))), p x := by
  rw [outerOutwardRegionMeasure_eq_density,
    ae_withDensity_iff (selectedOutwardDensity_measurable hD right).ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with x hx hxi
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr
      (selectedOutwardDensity_pos hD hcut x (Ioo_subset_Ico_self hxi))))
  · intro h
    exact h.mono (fun _ hp _ => hp)

theorem outerOutwardRegion_restrict_deep {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} {cut : ℝ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (horder : outerOutwardRadius right cut ≤
      outerOutwardRadius right (tailPhysicalRadius right T.entrance)) :
    (outerOutwardIntervalMeasure D right (radialTailInterval D right cut)).restrict
      (Icc (outerOutwardRadius right cut)
        (outerOutwardRadius right (tailPhysicalRadius right T.entrance)))ᶜ =
      outerOutwardTailMeasure D T right := by
  have hs : MeasurableSet
      (Icc (outerOutwardRadius right cut)
        (outerOutwardRadius right (tailPhysicalRadius right T.entrance)))ᶜ :=
    measurableSet_Icc.compl
  have hi :
      (Icc (outerOutwardRadius right cut)
        (outerOutwardRadius right (tailPhysicalRadius right T.entrance)))ᶜ ∩
      Ioo (outerOutwardRadius right cut)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)) =
      Ioo (outerOutwardRadius right (tailPhysicalRadius right T.entrance))
        (outerOutwardRadius right (tailPhysicalEndpoint D right)) := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_Icc, mem_Ioo]
    constructor
    · rintro ⟨hn, hl, hr⟩
      exact ⟨lt_of_not_ge (fun h => hn ⟨hl.le, h⟩), hr⟩
    · rintro ⟨hl, hr⟩
      exact ⟨fun h => not_le_of_gt hl h.2, horder.trans_lt hl, hr⟩
  rw [outerOutwardRegionMeasure_eq_density, restrict_withDensity hs,
    Measure.restrict_restrict hs, hi, outerOutwardTailMeasure_eq_density hD hphysical]
  rfl

end ContinuousFlexibility.Radial
