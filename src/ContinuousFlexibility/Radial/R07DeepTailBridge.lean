import ContinuousFlexibility.Statements.RadialTargets
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# From the physical deep-tail output to the natural radial line

The natural line used in `R07` lives in the physical radial coordinate.  The
`R06` physical conclusion supplies a globally smooth physical representative,
but states its differential equation in the outward logarithmic coordinate.
This module proves the change of interval and the finite-measure integrability
needed to turn that output into `RadialNaturalTail`.  It treats both ends with
one Boolean-oriented logarithmic coordinate.

The construction and estimates of a `DeepTailData` satisfying the hypotheses
of `R06` are not assumed to follow merely from this conversion.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- The inverse of the outward physical-radius coordinate, on positive radii. -/
def r07OutwardLog (right : Bool) (r : ℝ) : ℝ :=
  if right then log r else -log r

theorem r07_radius_outwardLog (right : Bool) {r : ℝ} (hr : 0 < r) :
    tailPhysicalRadius right (r07OutwardLog right r) = r := by
  cases right <;> simp only [tailPhysicalRadius, r07OutwardLog, Bool.false_eq_true,
    if_false, if_true, neg_neg, exp_log hr]

theorem r07_outwardLog_radius (right : Bool) (x : ℝ) :
    r07OutwardLog right (tailPhysicalRadius right x) = x := by
  cases right <;> simp only [tailPhysicalRadius, r07OutwardLog, Bool.false_eq_true,
    if_false, if_true, log_exp, neg_neg]

theorem r07_radius_pos (right : Bool) (x : ℝ) :
    0 < tailPhysicalRadius right x :=
  exp_pos _

/-- The two outward coordinates carry the same open tail to an ordinary
increasing open interval. -/
theorem r07_radius_mem_tail_iff {D : ReferenceData} (ha : 0 < D.a) (hb : 0 < D.b)
    (right : Bool) (entrance x : ℝ) :
    tailPhysicalRadius right x ∈ radialTailInterval D right
      (tailPhysicalRadius right entrance) ↔
      x ∈ Ioo entrance (r07OutwardLog right (if right then D.b else D.a)) := by
  cases right
  · simp only [tailPhysicalRadius, radialTailInterval, r07OutwardLog,
      Bool.false_eq_true, if_false, mem_Ioo]
    rw [← log_lt_iff_lt_exp ha, exp_lt_exp]
    constructor
    · rintro ⟨h₁, h₂⟩
      constructor <;> linarith
    · rintro ⟨h₁, h₂⟩
      constructor <;> linarith
  · simp only [tailPhysicalRadius, radialTailInterval, r07OutwardLog, if_true, mem_Ioo]
    rw [exp_lt_exp, ← lt_log_iff_exp_lt hb]

/-- The density defining the radial Hilbert space is integrable on the
bounded core; the positive inner radius removes its apparent denominator
singularity. -/
theorem r07_isFinite_radialHilbertMeasure {D : ReferenceData}
    (ha : 0 < D.a) (hw : Continuous D.w) :
    IsFiniteMeasure (radialHilbertMeasure D) := by
  have hc : ContinuousOn (fun r : ℝ => 12 * D.w r / r ^ 2) (Icc D.a D.b) :=
    (continuous_const.mul hw).continuousOn.div (continuous_id.pow 2).continuousOn
      (fun r hr => pow_ne_zero 2 (ha.trans_le hr.1).ne')
  have hi : Integrable (fun r : ℝ => 12 * D.w r / r ^ 2)
      (volume.restrict (radialCore D)) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  exact isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral

/-- Global continuity is enough for square integrability in the radial
Hilbert measure, whose support is contained in the bounded radial core. -/
theorem r07_memLp_radialHilbertMeasure {D : ReferenceData}
    (ha : 0 < D.a) (hw : Continuous D.w) {v : ℝ → ℝ} (hv : Continuous v) :
    MemLp v 2 (radialHilbertMeasure D) := by
  letI : IsFiniteMeasure (radialHilbertMeasure D) := r07_isFinite_radialHilbertMeasure ha hw
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc D.a D.b)).bddAbove_image
    hv.norm.continuousOn
  refine MemLp.of_bound hv.aestronglyMeasurable C ?_
  have haecore : ∀ᵐ r ∂radialHilbertMeasure D, r ∈ radialCore D :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [haecore] with r hr
  exact hC ⟨r, ⟨hr.1.le, hr.2.le⟩, rfl⟩

/-- The smooth physical representative supplied by `R06` is a genuine natural
radial solution at the physical deep-tail entrance.  The equation, nonzero
witness and Hilbert-space membership all refer to that same representative. -/
theorem r07_naturalTail_of_physicalFlat {D : ReferenceData} {T : DeepTailData}
    {right : Bool} {j start : ℕ} (hD : IsAccumulatingProfile D)
    (hend : T.endpoint = r07OutwardLog right (if right then D.b else D.a))
    (hflat : TailPhysicalFlatConclusion D T right j start) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
      RadialNaturalTail D right j (tailPhysicalRadius right T.entrance) v := by
  obtain ⟨C, hC⟩ := hD
  have ha : 0 < D.a := hC.1.1
  have hb : 0 < D.b := ha.trans hC.1.2.1
  have hw : Continuous D.w := hC.1.2.2.1.1.continuous
  rcases hflat with ⟨u, v, hu, hune, hv, hrel, hode, hrest⟩
  refine ⟨v, hv, hv.contDiffAt, ⟨hv.contDiffOn, ?_⟩,
    (r07_memLp_radialHilbertMeasure ha hw hv.continuous).restrict _, ?_⟩
  · intro r hr
    have hrpos : 0 < r := by
      cases right
      · exact ha.trans hr.1
      · exact (r07_radius_pos true T.entrance).trans hr.1
    have hx : r07OutwardLog right r ∈ Ioo T.entrance T.endpoint := by
      rw [hend]
      apply (r07_radius_mem_tail_iff ha hb right T.entrance _).mp
      simpa only [r07_radius_outwardLog right hrpos] using hr
    simpa only [r07_radius_outwardLog right hrpos] using hode _ hx
  · rcases hune with ⟨x, hx, hux⟩
    have hrmem : tailPhysicalRadius right x ∈ radialTailInterval D right
        (tailPhysicalRadius right T.entrance) :=
      (r07_radius_mem_tail_iff ha hb right T.entrance x).mpr (by simpa only [hend] using hx)
    refine ⟨tailPhysicalRadius right x, hrmem, ?_⟩
    rw [hrel x hx]
    have hep : 0 < (if right then D.b else D.a) := by
      cases right <;> assumption
    exact mul_ne_zero (rpow_pos_of_pos (div_pos (r07_radius_pos right x) hep) _).ne' hux

end ContinuousFlexibility.Radial
