import ContinuousFlexibility.Radial.AngularMeanL2

/-! # The normalized angular interval has total mass one -/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory

theorem angularMeanMeasure_univ : angularMeanMeasure Set.univ = 1 := by
  simp only [angularMeanMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, smul_eq_mul]
  have hcancel : (1 / (2 * Real.pi)) * (2 * Real.pi) = 1 :=
    div_mul_cancel₀ 1 (by positivity)
  rw [← ENNReal.ofReal_mul (by positivity), hcancel]
  simp

instance angularMeanMeasure_isProbabilityMeasure : IsProbabilityMeasure angularMeanMeasure where
  measure_univ := angularMeanMeasure_univ

end

end ContinuousFlexibility.Radial
