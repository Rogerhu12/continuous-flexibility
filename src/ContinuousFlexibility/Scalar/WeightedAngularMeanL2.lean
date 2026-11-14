module

public import ContinuousFlexibility.Scalar.WeightedAngularMeanJets
public import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveL2

/-!
# Angular averaging contracts the actual cylinder L² norm

Cauchy--Schwarz on the prescribed angular interval bounds the squared
normalized mean. The angular interval has mass pi, which cancels its
normalization after Fubini. The output is therefore an actual L² member
with operator norm at most one.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

theorem scalarAngularMeanField_sq_le {f : PolarPoint → ℝ} (hf : Continuous f)
    (p : PolarPoint) :
    scalarAngularMeanField f p ^ 2 ≤
      (1 / Real.pi) * ∫ t, f (p.1, t) ^ 2 ∂angleMeasure := by
  have hb := scalarAngularPrimitive_sq_le hf p.1
    (θ := Real.pi) ⟨Real.pi_pos.le, le_rfl⟩
  have he : scalarAngularMeanField f p =
      (1 / Real.pi) * scalarAngularPrimitive f (p.1, Real.pi) := rfl
  rw [he, mul_pow]
  calc
    _ ≤ (1 / Real.pi) ^ 2 * (Real.pi * ∫ t, f (p.1, t) ^ 2 ∂angleMeasure) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by field_simp [Real.pi_ne_zero] <;> ring

theorem scalarAngularMeanField_memLp_and_norm_le {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hmem : MemLp f 2 materialCylinderMeasure) :
    MemLp (scalarAngularMeanField f) 2 materialCylinderMeasure ∧
      (eLpNorm (scalarAngularMeanField f) 2 materialCylinderMeasure).toReal ≤
        (eLpNorm f 2 materialCylinderMeasure).toReal := by
  let : IsFiniteMeasure angleMeasure :=
    ⟨by rw [scalar_angleMeasure_mass]; exact ENNReal.ofReal_lt_top⟩
  let G : ℝ → ℝ := fun r => (1 / Real.pi) * ∫ t, f (r, t) ^ 2 ∂angleMeasure
  have hsq : Integrable (fun p : PolarPoint => f p ^ 2)
      ((volume : Measure ℝ).prod angleMeasure) := by
    rw [← materialCylinderMeasure_eq_prod]
    exact hmem.integrable_sq
  have hG : Integrable G volume := hsq.integral_prod_left.const_mul (1 / Real.pi)
  have hGp : Integrable (fun p : PolarPoint => G p.1) materialCylinderMeasure := by
    rw [materialCylinderMeasure_eq_prod]
    exact hG.comp_fst angleMeasure
  have hbound : ∀ᵐ p ∂materialCylinderMeasure, scalarAngularMeanField f p ^ 2 ≤ G p.1 :=
    Eventually.of_forall (scalarAngularMeanField_sq_le hf.continuous)
  have hFint : Integrable (fun p => scalarAngularMeanField f p ^ 2)
      materialCylinderMeasure := by
    apply hGp.mono' ((scalarAngularMeanField_contDiff hf).pow 2).continuous.aestronglyMeasurable
    filter_upwards [hbound] with p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (scalarAngularMeanField f p))] using hp
  have hF : MemLp (scalarAngularMeanField f) 2 materialCylinderMeasure :=
    (memLp_two_iff_integrable_sq
      (scalarAngularMeanField_contDiff hf).continuous.aestronglyMeasurable).mpr hFint
  have hGint : (∫ p, G p.1 ∂materialCylinderMeasure) =
      ∫ p, f p ^ 2 ∂materialCylinderMeasure := by
    simp only [materialCylinderMeasure_eq_prod]
    rw [integral_prod (fun p : PolarPoint => G p.1) (hG.comp_fst angleMeasure)]
    simp only [scalar_integral_angle_const, G, one_div, ← mul_assoc,
      mul_inv_cancel₀ Real.pi_ne_zero, one_mul]
    exact (integral_prod (fun p : PolarPoint => f p ^ 2) hsq).symm
  have hint : (eLpNorm (scalarAngularMeanField f) 2 materialCylinderMeasure).toReal ^ 2 ≤
      (eLpNorm f 2 materialCylinderMeasure).toReal ^ 2 := by
    rw [scalar_eLpNorm_two_sq hF, scalar_eLpNorm_two_sq hmem, ← hGint]
    exact integral_mono_ae hFint hGp hbound
  exact ⟨hF, (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mp hint⟩

end ContinuousFlexibility.Statements
