import ContinuousFlexibility.Radial.OuterTotalMass
import ContinuousFlexibility.Radial.OuterOutwardHilbert

/-!
# The physical measure on one entire outer interval

The core and deep tail use the same restricted radial Hilbert measure,
reflected together when the chosen end is the left end.  Cutting off the
closed core gives exactly the already constructed deep-tail measure.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements

def outerWholeMeasure (D : ReferenceData) (right : Bool) (entry : ℝ) : Measure ℝ :=
  Measure.map (outerOutwardRadius right)
    ((radialHilbertMeasure D).restrict (radialTailInterval D right entry))

abbrev OuterWholeL2 (D : ReferenceData) (right : Bool) (entry : ℝ) :=
  Lp ℝ 2 (outerWholeMeasure D right entry)

theorem outerWholeMeasure_tail (D : ReferenceData) (T : DeepTailData) (right : Bool) :
    outerWholeMeasure D right (tailPhysicalRadius right T.entrance) =
      outerOutwardTailMeasure D T right := rfl

theorem outerWhole_interval {D : ReferenceData} {right : Bool} {entry : ℝ}
    (hentry : entry ∈ radialCore D) :
    outerOutwardRadius right entry <
      outerOutwardRadius right (tailPhysicalEndpoint D right) := by
  cases right
  · exact neg_lt_neg hentry.1
  · exact hentry.2

/-- Every outward point, including the regular entrance, is an actual
interior physical point. -/
theorem outerWhole_coordinate_core {D : ReferenceData} {right : Bool} {entry x : ℝ}
    (hentry : entry ∈ radialCore D)
    (hx : x ∈ Ico (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    outerOutwardRadius right x ∈ radialCore D := by
  cases right
  · change -entry ≤ x ∧ x < -D.a at hx
    change D.a < -x ∧ -x < D.b
    constructor <;> linarith [hx.1, hx.2, hentry.1, hentry.2]
  · change entry ≤ x ∧ x < D.b at hx
    exact ⟨hentry.1.trans_le hx.1, hx.2⟩

theorem outerWholeMeasure_isFinite {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (right : Bool) (entry : ℝ) : IsFiniteMeasure (outerWholeMeasure D right entry) := by
  letI := radialHilbertMeasure_isFinite hD
  unfold outerWholeMeasure
  infer_instance

theorem outerWholeMeasure_real_univ (D : ReferenceData) (right : Bool) (entry : ℝ) :
    (outerWholeMeasure D right entry).real univ =
      (radialHilbertMeasure D).real (radialTailInterval D right entry) := by
  rw [outerWholeMeasure, map_measureReal_apply
    (measurableEmbedding_outerOutwardRadius right).measurable measurableSet_univ,
    preimage_univ, measureReal_restrict_apply_univ]

/-- The same common profile mass controls all outer cuts and frequencies. -/
theorem outerWholeMeasure_mass_bound {D : ReferenceData} {C : ℕ → ℝ}
    (hC : AccumulatingProfileBounds D C) (right : Bool) (entry : ℝ) :
    (outerWholeMeasure D right entry).real univ ≤
      12 * C 0 * Real.exp ((C 0) ^ 5) * (D.b - D.a) / D.a ^ 2 := by
  letI := radialHilbertMeasure_isFinite (show IsAccumulatingProfile D from ⟨C, hC⟩)
  rw [outerWholeMeasure_real_univ]
  exact (measureReal_mono (subset_univ (radialTailInterval D right entry))).trans
    (outer_radialHilbertMeasure_mass_bound hC)

/-- The pushforward is exactly the manuscript's positive outward density. -/
theorem outerWholeMeasure_eq_density {D : ReferenceData} {right : Bool} {entry : ℝ}
    (hentry : entry ∈ radialCore D) :
    outerWholeMeasure D right entry =
      (volume.restrict (Ioo (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)))).withDensity
          (fun x => ENNReal.ofReal (12 * D.w (outerOutwardRadius right x) / x ^ 2)) := by
  have hs : MeasurableSet (radialTailInterval D right entry) := by
    cases right <;> exact measurableSet_Ioo
  have hsub : radialTailInterval D right entry ⊆ radialCore D := by
    cases right
    · intro r hr
      exact ⟨hr.1, hr.2.trans hentry.2⟩
    · intro r hr
      exact ⟨hentry.1.trans hr.1, hr.2⟩
  have hm : (radialHilbertMeasure D).restrict (radialTailInterval D right entry) =
      outerRadialIntervalMeasure D (radialTailInterval D right entry) := by
    rw [radialHilbertMeasure, restrict_withDensity hs, Measure.restrict_restrict hs,
      inter_eq_left.mpr hsub]
    rfl
  rw [outerWholeMeasure, hm, outerOutwardIntervalMeasure_map D right hs,
    outerOutwardIntervalMeasure, outerOutward_tail_image]

theorem outerWholeMeasure_ae_mem {D : ReferenceData} {right : Bool} {entry : ℝ}
    (hentry : entry ∈ radialCore D) :
    ∀ᵐ x ∂outerWholeMeasure D right entry,
      x ∈ Ioo (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)) := by
  rw [outerWholeMeasure_eq_density hentry]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

/-- Removing the closed core from a weighted interval leaves exactly the
open deep interval; no endpoint atom is discarded by an approximation. -/
theorem outer_weighted_interval_restrict_core_compl {a c b : ℝ} (hac : a ≤ c)
    (ρ : ℝ → ℝ≥0∞) :
    (((volume.restrict (Ioo a b)).withDensity ρ).restrict (Icc a c)ᶜ) =
      (volume.restrict (Ioo c b)).withDensity ρ := by
  have hs : (Icc a c)ᶜ ∩ Ioo a b = Ioo c b := by
    ext x
    constructor
    · rintro ⟨hn, hx⟩
      exact ⟨lt_of_not_ge (fun hxc => hn ⟨hx.1.le, hxc⟩), hx.2⟩
    · intro hx
      exact ⟨fun hc => (not_lt_of_ge hc.2) hx.1, ⟨hac.trans_lt hx.1, hx.2⟩⟩
  rw [restrict_withDensity measurableSet_Icc.compl,
    Measure.restrict_restrict measurableSet_Icc.compl, hs]

/-- This exact identity is the measure bridge for the full Green blocks. -/
theorem outerWholeMeasure_restrict_deep {D : ReferenceData} {right : Bool}
    {entry cut : ℝ} (hentry : entry ∈ radialCore D) (hcut : cut ∈ radialCore D)
    (horder : outerOutwardRadius right entry ≤ outerOutwardRadius right cut) :
    (outerWholeMeasure D right entry).restrict
        (Icc (outerOutwardRadius right entry) (outerOutwardRadius right cut))ᶜ =
      outerWholeMeasure D right cut := by
  rw [outerWholeMeasure_eq_density hentry, outerWholeMeasure_eq_density hcut]
  exact outer_weighted_interval_restrict_core_compl horder _

end ContinuousFlexibility.Radial
