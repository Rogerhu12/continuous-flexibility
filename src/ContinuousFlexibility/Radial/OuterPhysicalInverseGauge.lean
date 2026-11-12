import ContinuousFlexibility.Radial.OuterPhysicalTailBasis
import ContinuousFlexibility.Radial.OuterOutwardHilbert

/-!
# The inverse physical gauge on the actual L2 spaces

The pullback and the square density transport all L2 functions. This is
used below for classification of the natural line, without assuming a
bound for multiplication by the reciprocal gauge.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

def outerPhysicalInverseGauge (D : ReferenceData) (right : Bool) (j : ℕ)
    (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (tailPhysicalRadius right x) / outerLogGauge D right j x

theorem morsePhysicalDeepTail_squareDensity_measure
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    (right : Bool) (j start : ℕ) (entrance η K : ℝ) :
    outerPhysicalPullbackMeasure D (morsePhysicalDeepTail M D right j start entrance η K) right =
      squareDensityMeasure (deepTailMeasure (morsePhysicalDeepTail M D right j start entrance η K))
        (outerPhysicalAmplitude D right j) := by
  have hend : 0 < tailPhysicalEndpoint D right := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  apply outerPhysicalPullbackMeasure_eq_squareDensity_of_density hD.2.2.1.1.continuous hend
  intro x _
  change (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ (2 * j ^ 2) *
      D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x =
    ((tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ (j ^ 2)) ^ 2 *
      D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x
  rw [← pow_mul, Nat.mul_comm (j ^ 2) 2]

/-- Every actual physical L2 function has a logarithmic inverse gauge
in the actual deep-tail L2 space. -/
theorem morsePhysicalDeepTail_inverseGauge_memLp
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ} (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {f : ℝ → ℝ}
    (hf : MemLp f 2
      ((radialHilbertMeasure D).restrict (radialTailInterval D right entrance))) :
    MemLp (outerPhysicalInverseGauge D right j f) 2
      (deepTailMeasure (morsePhysicalDeepTail M D right j start entrance η K)) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  have hend : 0 < tailPhysicalEndpoint D right := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hfmap : MemLp f 2
      (Measure.map (tailPhysicalRadius right) (outerPhysicalPullbackMeasure D T right)) := by
    rw [outerPhysicalPullbackMeasure_map, morsePhysicalDeepTail_interval_measure_eq hD hentry hT]
    exact hf
  have hpull := (measurableEmbedding_tailPhysicalRadius right).memLp_map_measure_iff.mp hfmap
  rw [morsePhysicalDeepTail_squareDensity_measure hD right j start entrance η K] at hpull
  have hh := (squareDensity_memLp_iff (deepTailMeasure T)
    (continuous_outerPhysicalAmplitude hend j).measurable
    (outerPhysicalAmplitude_pos hend j) (f ∘ tailPhysicalRadius right)).mp hpull
  have hc := hh.const_mul (sqrt 12)⁻¹
  convert hc using 1
  funext x
  dsimp only [outerPhysicalInverseGauge, outerPhysicalAmplitude, Function.comp_apply]
  field_simp [(sqrt_pos.mpr (by norm_num : (0 : ℝ) < 12)).ne',
    (outerLogGauge_pos hend j x).ne'] <;> ring

@[simp] theorem outerOutwardRadius_eq_sign (right : Bool) (r : ℝ) :
    outerOutwardRadius right r = outerTailSign right * r := by
  cases right <;> simp [outerOutwardRadius, outerTailSign]

@[simp] theorem outerTailOutwardLift_reflect (D : ReferenceData) (right : Bool)
    (j : ℕ) (u : ℝ → ℝ) (r : ℝ) :
    outerTailOutwardLift D right j u (outerOutwardRadius right r) =
      tailPhysicalLift D right j u r := by
  rw [outerOutwardRadius_eq_sign, outerTailOutwardLift,
    ← mul_assoc, outerTailSign_mul_self, one_mul]

/-- The normalized natural basis belongs to the true outward L2 space,
whose density and orientation are transported together. -/
theorem morsePhysicalDeepTail_outward_lift_memLp
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ} (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {u : ℝ → ℝ}
    (hu : TailNaturalEquation (morsePhysicalDeepTail M D right j start entrance η K) u) :
    MemLp (outerTailOutwardLift D right j u) 2
      (outerOutwardTailMeasure D (morsePhysicalDeepTail M D right j start entrance η K) right) := by
  unfold outerOutwardTailMeasure
  change MemLp _ 2 (Measure.map (outerOutwardRadius right)
    ((radialHilbertMeasure D).restrict
      (radialTailInterval D right (tailPhysicalRadius right (tailPhysicalLog right entrance)))))
  rw [tailPhysicalRadius_log right hentry]
  apply (measurableEmbedding_outerOutwardRadius right).memLp_map_measure_iff.mpr
  simpa only [Function.comp_def, outerTailOutwardLift_reflect] using
    morsePhysicalDeepTail_lift_memLp_radial hD hentry hT hu

/-- Both orientations send the logarithmic half-open interval to the
increasing outward half-open physical interval. -/
theorem outerTailRadius_mem_outwardIco {D : ReferenceData} (hD : RadialProfileGeometry D)
    (right : Bool) {entrance x : ℝ} (hentry : 0 < entrance)
    (hx : x ∈ Ico (tailPhysicalLog right entrance)
      (tailPhysicalLog right (tailPhysicalEndpoint D right))) :
    outerOutwardRadius right (tailPhysicalRadius right x) ∈
      Ico (outerTailSign right * entrance)
        (outerTailSign right * tailPhysicalEndpoint D right) := by
  cases right with
  | true =>
      have hx' : x ∈ Ico (log entrance) (log D.b) := hx
      have hl := exp_le_exp.mpr hx'.1
      have hr := exp_lt_exp.mpr hx'.2
      rw [exp_log hentry] at hl
      rw [exp_log (hD.1.trans hD.2.1)] at hr
      simpa [outerOutwardRadius, outerTailSign, tailPhysicalRadius, tailPhysicalEndpoint]
        using And.intro hl hr
  | false =>
      have hx' : x ∈ Ico (-log entrance) (-log D.a) := hx
      have hl : -x ≤ log entrance := by linarith only [hx'.1]
      have hr : log D.a < -x := by linarith only [hx'.2]
      have hl' := exp_le_exp.mpr hl
      have hr' := exp_lt_exp.mpr hr
      rw [exp_log hentry] at hl'
      rw [exp_log hD.1] at hr'
      have hh : -exp (-x) ∈ Ico (-entrance) (-D.a) :=
        ⟨neg_le_neg hl', neg_lt_neg hr'⟩
      simpa [outerOutwardRadius, outerTailSign, tailPhysicalRadius, tailPhysicalEndpoint] using hh

end ContinuousFlexibility.Radial
