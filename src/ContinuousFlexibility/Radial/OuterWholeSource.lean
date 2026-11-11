import ContinuousFlexibility.Radial.OuterPhysicalFundamentalPair
import ContinuousFlexibility.Radial.OuterEntranceVariation

/-!
# Ordinary source integrals on the physical outer interval

The density conversion uses the actual outward pushforward measure.  Every
weighted L² source is an ordinary integrable Jacobi source.  Multiplication
by a homogeneous solution is integrable on each initial compact segment,
even when the source has no continuous representative at the entrance.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements

def outerWholeDensity (D : ReferenceData) (right : Bool) (x : ℝ) : ℝ :=
  12 * D.w (outerOutwardRadius right x) / x ^ 2

theorem outerWholeMeasure_eq_outerDensity {D : ReferenceData} {right : Bool} {entry : ℝ}
    (hentry : entry ∈ radialCore D) :
    outerWholeMeasure D right entry =
      (volume.restrict (Ioo (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)))).withDensity
          (fun x => ENNReal.ofReal (outerWholeDensity D right x)) :=
  outerWholeMeasure_eq_density hentry

variable {D : ReferenceData} (hD : IsAccumulatingProfile D)
  {right : Bool} {entry : ℝ} (hentry : entry ∈ radialCore D)

include hD

theorem outerWholeDensity_measurable : Measurable (outerWholeDensity D right) := by
  have hw := (matchingProfileGeometry hD).2.2.1.1.continuous.measurable
  have hs := (measurableEmbedding_outerOutwardRadius right).measurable
  exact (measurable_const.mul (hw.comp hs)).div (measurable_id.pow_const 2)

include hentry

theorem outerWholeDensity_pos {x : ℝ}
    (hx : x ∈ Ico (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    0 < outerWholeDensity D right x := by
  have hw := (matchingProfileGeometry hD).2.2.2.2.1 _
    (outerWhole_coordinate_core hentry hx)
  have hx0 := outerWhole_coordinate_ne_zero (matchingProfileGeometry hD) hentry hx
  exact div_pos (mul_pos (by norm_num) hw) (sq_pos_of_ne_zero hx0)

theorem outerWholeMeasure_ae_iff {p : ℝ → Prop} :
    (∀ᵐ x ∂outerWholeMeasure D right entry, p x) ↔
      ∀ᵐ x ∂volume.restrict (Ioo (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right))), p x := by
  rw [outerWholeMeasure_eq_outerDensity hentry,
    ae_withDensity_iff (outerWholeDensity_measurable (right := right) hD).ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with x hx hxi
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr
      (outerWholeDensity_pos hD hentry (Ioo_subset_Ico_self hxi))))
  · intro h
    exact h.mono (fun _ hp _ => hp)

theorem outerWholeDensity_integrable_iff (f : ℝ → ℝ) :
    Integrable f (outerWholeMeasure D right entry) ↔
      IntegrableOn (fun x => outerWholeDensity D right x * f x)
        (Ioo (outerOutwardRadius right entry)
          (outerOutwardRadius right (tailPhysicalEndpoint D right))) := by
  rw [outerWholeMeasure_eq_outerDensity hentry,
    integrable_withDensity_iff_integrable_smul'
      (outerWholeDensity_measurable (right := right) hD).ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simp only [ENNReal.toReal_ofReal
    (outerWholeDensity_pos hD hentry (Ioo_subset_Ico_self hx)).le, smul_eq_mul]

theorem outerWholeDensity_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂outerWholeMeasure D right entry) =
      ∫ x in (outerOutwardRadius right entry)..
        (outerOutwardRadius right (tailPhysicalEndpoint D right)),
          outerWholeDensity D right x * f x := by
  rw [outerWholeMeasure_eq_outerDensity hentry,
    integral_withDensity_eq_integral_toReal_smul
      (outerWholeDensity_measurable (right := right) hD).ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    intervalIntegral.integral_of_le (outerWhole_interval hentry).le,
    integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simp only [ENNReal.toReal_ofReal
    (outerWholeDensity_pos hD hentry (Ioo_subset_Ico_self hx)).le, smul_eq_mul]

/-- The initial integral has its exact ordinary-coordinate expression,
including when its upper limit is the regular entrance itself. -/
theorem outerWholeDensity_initial_integral (f : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Ico (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    (∫ y in Iic x, f y ∂outerWholeMeasure D right entry) =
      ∫ y in (outerOutwardRadius right entry)..x,
        outerWholeDensity D right y * f y := by
  have hs : Iic x ∩ Ioo (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) =
        Ioc (outerOutwardRadius right entry) x := by
    ext y
    constructor
    · rintro ⟨hyx, hy⟩
      exact ⟨hy.1, hyx⟩
    · intro hy
      exact ⟨hy.2, hy.1, hy.2.trans_lt hx.2⟩
  rw [outerWholeMeasure_eq_outerDensity hentry, restrict_withDensity measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, hs,
    integral_withDensity_eq_integral_toReal_smul
      (outerWholeDensity_measurable (right := right) hD).ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    intervalIntegral.integral_of_le hx.1]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  simp only [ENNReal.toReal_ofReal
    (outerWholeDensity_pos hD hentry ⟨hy.1.le, hy.2.trans_lt hx.2⟩).le,
    smul_eq_mul]

/-- Integrability on an initial weighted interval has the same exact
density conversion as its integral. -/
theorem outerWholeDensity_initial_integrable_iff (f : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Ico (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    IntegrableOn f (Iic x) (outerWholeMeasure D right entry) ↔
      IntervalIntegrable (fun y => outerWholeDensity D right y * f y)
        volume (outerOutwardRadius right entry) x := by
  have hs : Iic x ∩ Ioo (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) =
        Ioc (outerOutwardRadius right entry) x := by
    ext y
    constructor
    · rintro ⟨hyx, hy⟩
      exact ⟨hy.1, hyx⟩
    · intro hy
      exact ⟨hy.2, hy.1, hy.2.trans_lt hx.2⟩
  rw [IntegrableOn, outerWholeMeasure_eq_outerDensity hentry,
    restrict_withDensity measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic, hs,
    integrable_withDensity_iff_integrable_smul'
      (outerWholeDensity_measurable (right := right) hD).ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  simp only [ENNReal.toReal_ofReal
    (outerWholeDensity_pos hD hentry ⟨hy.1.le, hy.2.trans_lt hx.2⟩).le,
    smul_eq_mul]

/-- A weighted L² right-hand side is an ordinary integrable Jacobi source. -/
theorem outerWholeSource_integrable (f : OuterWholeL2 D right entry) :
    IntegrableOn (fun x => -(outerWholeDensity D right x * f x))
      (Ioo (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right))) := by
  letI := outerWholeMeasure_isFinite hD right entry
  exact ((outerWholeDensity_integrable_iff hD hentry (f : ℝ → ℝ)).mp
    (MemLp.integrable (by norm_num) (Lp.memLp f))).neg

/-- The initial primitives used in variation of parameters exist for
every actual L² source and every continuous homogeneous coefficient. -/
theorem outerWholeSource_initial_integrable (f : OuterWholeL2 D right entry)
    {U : ℝ → ℝ}
    (hU : ContinuousOn U (Ico (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))) :
    ∀ x ∈ Ioo (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)),
      IntervalIntegrable (fun y => U y * (-(outerWholeDensity D right y * f y)))
        volume (outerOutwardRadius right entry) x := by
  intro x hx
  have hi : IntervalIntegrable (fun y => -(outerWholeDensity D right y * f y))
      volume (outerOutwardRadius right entry) x :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.1.le).mpr
      ((outerWholeSource_integrable hD hentry f).mono_set
        (fun _ hy => ⟨hy.1, hy.2.trans hx.2⟩))
  apply hi.continuousOn_mul
  rw [uIcc_of_le hx.1.le]
  exact hU.mono (fun _ hy => ⟨hy.1, hy.2.trans_lt hx.2⟩)

end ContinuousFlexibility.Radial
