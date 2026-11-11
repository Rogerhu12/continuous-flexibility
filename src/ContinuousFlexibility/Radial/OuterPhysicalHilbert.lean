import ContinuousFlexibility.Radial.OuterPhysicalMeasure
import ContinuousFlexibility.Analysis.L2MeasureCongr

/-!
# The physical deep-tail Hilbert space

The logarithmic coordinate and the exact gauge give a surjective linear
isometry from the original radial Hilbert measure to the actual deep-tail
measure. The amplitude is sqrt(12)/g; it need not have a bounded reciprocal
at the singular endpoint.
-/

noncomputable section



namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency false

def outerLogGauge (D : ReferenceData) (right : Bool) (j : ℕ) (x : ℝ) : ℝ :=
  (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ (j ^ 2)

theorem outerLogGauge_eq_rpow (D : ReferenceData) (right : Bool) (j : ℕ) (x : ℝ) :
    outerLogGauge D right j x =
      (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2) := by
  rw [show (j : ℝ) ^ 2 = ((j ^ 2 : ℕ) : ℝ) by simp, rpow_natCast]
  rfl

theorem continuous_outerLogGauge (D : ReferenceData) (right : Bool) (j : ℕ) :
    Continuous (outerLogGauge D right j) :=
  ((continuous_tailPhysicalRadius right).div_const _).pow _

theorem outerLogGauge_pos {D : ReferenceData} {right : Bool}
    (hend : 0 < tailPhysicalEndpoint D right) (j : ℕ) (x : ℝ) :
    0 < outerLogGauge D right j x :=
  pow_pos (div_pos (tailPhysicalRadius_pos right x) hend) _

def outerPhysicalAmplitude (D : ReferenceData) (right : Bool) (j : ℕ) (x : ℝ) : ℝ :=
  sqrt 12 / outerLogGauge D right j x

theorem continuous_outerPhysicalAmplitude {D : ReferenceData} {right : Bool}
    (hend : 0 < tailPhysicalEndpoint D right) (j : ℕ) :
    Continuous (outerPhysicalAmplitude D right j) :=
  continuous_const.div (continuous_outerLogGauge D right j)
    (fun x => (outerLogGauge_pos hend j x).ne')

theorem outerPhysicalAmplitude_pos {D : ReferenceData} {right : Bool}
    (hend : 0 < tailPhysicalEndpoint D right) (j : ℕ) (x : ℝ) :
    0 < outerPhysicalAmplitude D right j x :=
  div_pos (sqrt_pos.2 (by norm_num)) (outerLogGauge_pos hend j x)

/-- Only the actual local density identity is needed for this measure
calculation; no tail decay or inverse estimate is an input. -/
theorem outerPhysicalPullbackMeasure_eq_squareDensity_of_density
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j : ℕ}
    (hw : Continuous D.w) (hend : 0 < tailPhysicalEndpoint D right)
    (hp : ∀ x ∈ Ioo T.entrance T.endpoint,
      T.p x = outerLogGauge D right j x ^ 2 *
        D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x) :
    outerPhysicalPullbackMeasure D T right =
      squareDensityMeasure (deepTailMeasure T) (outerPhysicalAmplitude D right j) := by
  let μ := volume.restrict (Ioo T.entrance T.endpoint)
  let q : ℝ → ℝ := fun x => outerLogGauge D right j x ^ 2 *
    D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x
  have hq : Continuous q :=
    (((continuous_outerLogGauge D right j).pow 2).mul
      (hw.comp (continuous_tailPhysicalRadius right))).div
      (continuous_tailPhysicalRadius right) (fun x => (tailPhysicalRadius_pos right x).ne')
  have hpq : (fun x => ENNReal.ofReal (T.p x)) =ᵐ[μ] fun x => ENNReal.ofReal (q x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hp x hx]
  have hpm : AEMeasurable (fun x => ENNReal.ofReal (T.p x)) μ :=
    hq.measurable.ennreal_ofReal.aemeasurable.congr hpq.symm
  have ham := ((continuous_outerPhysicalAmplitude hend j).pow 2).measurable.ennreal_ofReal
  change Measurable (fun x => ENNReal.ofReal (outerPhysicalAmplitude D right j x ^ 2)) at ham
  change μ.withDensity (fun x => ENNReal.ofReal (12 * D.w (tailPhysicalRadius right x) /
      tailPhysicalRadius right x)) =
    (μ.withDensity (fun x => ENNReal.ofReal (T.p x))).withDensity
      (fun x => ENNReal.ofReal (outerPhysicalAmplitude D right j x ^ 2))
  rw [← withDensity_mul₀ hpm ham.aemeasurable]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  change ENNReal.ofReal (12 * D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x) =
    ENNReal.ofReal (T.p x) * ENNReal.ofReal (outerPhysicalAmplitude D right j x ^ 2)
  rw [mul_comm (ENNReal.ofReal (T.p x)), ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [hp x hx, outerPhysicalAmplitude, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
  field_simp [(outerLogGauge_pos hend j x).ne', (tailPhysicalRadius_pos right x).ne']
  <;> ring

theorem outerPhysicalPullbackMeasure_eq_squareDensity
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start) :
    outerPhysicalPullbackMeasure D T right =
      squareDensityMeasure (deepTailMeasure T) (outerPhysicalAmplitude D right j) := by
  obtain ⟨C, hC⟩ := hD
  apply outerPhysicalPullbackMeasure_eq_squareDensity_of_density
    hC.1.2.2.1.1.continuous (tailPhysicalEndpoint_pos ⟨C, hC⟩ right)
  intro x hx
  rw [(hphysical.2.2.1 x hx).2, outerLogGauge_eq_rpow]
  change (tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ (2 * (j : ℝ) ^ 2) *
    D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x = _
  rw [mul_comm 2 ((j : ℝ) ^ 2),
    rpow_mul (div_pos (tailPhysicalRadius_pos right x)
      (tailPhysicalEndpoint_pos ⟨C, hC⟩ right)).le, rpow_two]

abbrev OuterPhysicalTailL2 (D : ReferenceData) (T : DeepTailData) (right : Bool) :=
  Lp ℝ 2 ((radialHilbertMeasure D).restrict
    (radialTailInterval D right (tailPhysicalRadius right T.entrance)))

/-- Pullback by the actual signed logarithmic radius. -/
def outerPhysicalCoordinateEquiv
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start) :
    OuterPhysicalTailL2 D T right ≃ₗᵢ[ℝ] Lp ℝ 2 (outerPhysicalPullbackMeasure D T right) :=
  (l2MeasureCongr (outerPhysicalPullbackMeasure_map_radial hD hphysical).symm).trans
    (coordinateL2Equiv (outerPhysicalPullbackMeasure D T right)
      (tailPhysicalRadius right) (tailPhysicalLog right)
      (measurableEmbedding_tailPhysicalRadius right) (tailPhysicalLog_radius right))

theorem outerPhysicalCoordinateEquiv_ae
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (f : OuterPhysicalTailL2 D T right) :
    outerPhysicalCoordinateEquiv hD hphysical f =ᵐ[outerPhysicalPullbackMeasure D T right]
      fun x => f (tailPhysicalRadius right x) := by
  have hc := l2MeasureCongr_ae (outerPhysicalPullbackMeasure_map_radial hD hphysical).symm f
  have hp := coordinateL2Equiv_ae (outerPhysicalPullbackMeasure D T right)
    (tailPhysicalRadius right) (tailPhysicalLog right)
    (measurableEmbedding_tailPhysicalRadius right) (tailPhysicalLog_radius right)
    (l2MeasureCongr (outerPhysicalPullbackMeasure_map_radial hD hphysical).symm f)
  exact hp.trans (ae_eq_comp
    (measurableEmbedding_tailPhysicalRadius right).measurable.aemeasurable hc)

/-- Exact gauge isometry on logarithmic coordinates. -/
def outerPhysicalGaugeEquiv
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start) :
    Lp ℝ 2 (outerPhysicalPullbackMeasure D T right) ≃ₗᵢ[ℝ] DeepTailL2 T :=
  squareDensityMeasureEquiv (outerPhysicalPullbackMeasure_eq_squareDensity hD hphysical)
    (continuous_outerPhysicalAmplitude (tailPhysicalEndpoint_pos hD right) j).measurable
    (outerPhysicalAmplitude_pos (tailPhysicalEndpoint_pos hD right) j)

theorem outerPhysicalPullback_ae_eq
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    {f g : ℝ → ℝ} (hfg : f =ᵐ[outerPhysicalPullbackMeasure D T right] g) :
    f =ᵐ[deepTailMeasure T] g :=
  squareDensity_ae_eq (deepTailMeasure T)
    (continuous_outerPhysicalAmplitude (tailPhysicalEndpoint_pos hD right) j).measurable
    (outerPhysicalAmplitude_pos (tailPhysicalEndpoint_pos hD right) j)
    (ae_eq_of_measure_eq (outerPhysicalPullbackMeasure_eq_squareDensity hD hphysical) hfg)

theorem outerPhysicalGaugeEquiv_ae
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (f : Lp ℝ 2 (outerPhysicalPullbackMeasure D T right)) :
    outerPhysicalGaugeEquiv hD hphysical f =ᵐ[deepTailMeasure T]
      fun x => outerPhysicalAmplitude D right j x * f x :=
  squareDensityMeasureEquiv_ae (outerPhysicalPullbackMeasure_eq_squareDensity hD hphysical)
    (continuous_outerPhysicalAmplitude (tailPhysicalEndpoint_pos hD right) j).measurable
    (outerPhysicalAmplitude_pos (tailPhysicalEndpoint_pos hD right) j) f

/-- The exact physical logarithmic-gauge isometry. -/
def outerPhysicalTailEquiv
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start) :
    OuterPhysicalTailL2 D T right ≃ₗᵢ[ℝ] DeepTailL2 T :=
  Classical.choose (exists_l2EquivCompose_apply (outerPhysicalCoordinateEquiv hD hphysical)
    (outerPhysicalGaugeEquiv hD hphysical))

theorem outerPhysicalTailEquiv_apply
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (f : OuterPhysicalTailL2 D T right) :
    outerPhysicalTailEquiv hD hphysical f =
      outerPhysicalGaugeEquiv hD hphysical (outerPhysicalCoordinateEquiv hD hphysical f) :=
  Classical.choose_spec (exists_l2EquivCompose_apply (outerPhysicalCoordinateEquiv hD hphysical)
    (outerPhysicalGaugeEquiv hD hphysical)) f

/-- The exact representative is sqrt(12) times inverse gauge and pullback. -/
theorem outerPhysicalTailEquiv_ae
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (f : OuterPhysicalTailL2 D T right) :
    outerPhysicalTailEquiv hD hphysical f =ᵐ[deepTailMeasure T] fun x =>
      outerPhysicalAmplitude D right j x * f (tailPhysicalRadius right x) := by
  rw [outerPhysicalTailEquiv_apply]
  have hc := outerPhysicalPullback_ae_eq hD hphysical (outerPhysicalCoordinateEquiv_ae hD hphysical f)
  have hg := outerPhysicalGaugeEquiv_ae hD hphysical (outerPhysicalCoordinateEquiv hD hphysical f)
  filter_upwards [hc, hg] with x hx hy
  exact hy.trans (congrArg (fun t => outerPhysicalAmplitude D right j x * t) hx)

end ContinuousFlexibility.Radial
