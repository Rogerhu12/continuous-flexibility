module

public import ContinuousFlexibility.Analysis.SpacesLpOverlap

/-!
# Isometric normalization of a real `L²` measure

Canonical pieces have different areas. Dividing the measure by an area
and multiplying the representative by its square root gives an exact
linear isometry. This file keeps that normalization explicit, so the
later direct sum over pieces has the prescribed physical norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (a : ℝ) (ha : 0 < a)

def n07aAngularNormalizedMeasure : Measure α := ENNReal.ofReal a⁻¹ • μ

include ha in
theorem n07aAngularNormalizedMeasure_restore :
    ENNReal.ofReal a • n07aAngularNormalizedMeasure μ a = μ := by
  rw [n07aAngularNormalizedMeasure, smul_smul, ← ENNReal.ofReal_mul ha.le,
    mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one, one_smul]

include ha in
theorem n07aAngularNormalizedMeasure_ae_iff (p : α → Prop) :
    (∀ᵐ x ∂n07aAngularNormalizedMeasure μ a, p x) ↔ ∀ᵐ x ∂μ, p x := by
  exact Measure.ae_ennreal_smul_measure_iff
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr ha)).ne'

/-- Keep the representative while normalizing the underlying measure. -/
def n07aAngularLpNormalize :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (n07aAngularNormalizedMeasure μ a) :=
  Lp.LpToLpOfMeasureLeSMul (c := ENNReal.ofReal a⁻¹) ENNReal.ofReal_ne_top le_rfl

theorem n07aAngularLpNormalize_ae (u : Lp ℝ 2 μ) :
    (n07aAngularLpNormalize μ a u : α → ℝ) =ᵐ[n07aAngularNormalizedMeasure μ a] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

/-- Restore the original measure without changing the representative. -/
def n07aAngularLpRestore :
    Lp ℝ 2 (n07aAngularNormalizedMeasure μ a) →L[ℝ] Lp ℝ 2 μ :=
  Lp.LpToLpOfMeasureLeSMul (c := ENNReal.ofReal a) ENNReal.ofReal_ne_top
    (le_of_eq (n07aAngularNormalizedMeasure_restore μ a ha).symm)

theorem n07aAngularLpRestore_ae (u : Lp ℝ 2 (n07aAngularNormalizedMeasure μ a)) :
    (n07aAngularLpRestore μ a ha u : α → ℝ) =ᵐ[μ] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

theorem n07aAngularLpRestore_normalize (u : Lp ℝ 2 μ) :
    n07aAngularLpRestore μ a ha (n07aAngularLpNormalize μ a u) = u := by
  apply Lp.ext
  have hu := (n07aAngularNormalizedMeasure_ae_iff μ a ha _).mp
    (n07aAngularLpNormalize_ae μ a u)
  exact (n07aAngularLpRestore_ae μ a ha (n07aAngularLpNormalize μ a u)).trans hu

theorem n07aAngularLpNormalize_restore (u : Lp ℝ 2 (n07aAngularNormalizedMeasure μ a)) :
    n07aAngularLpNormalize μ a (n07aAngularLpRestore μ a ha u) = u := by
  apply Lp.ext
  have hu := (n07aAngularNormalizedMeasure_ae_iff μ a ha _).mpr
    (n07aAngularLpRestore_ae μ a ha u)
  exact (n07aAngularLpNormalize_ae μ a (n07aAngularLpRestore μ a ha u)).trans hu

include ha in
theorem n07aAngularLpNormalize_norm_sq (u : Lp ℝ 2 μ) :
    ‖n07aAngularLpNormalize μ a u‖ ^ 2 = a⁻¹ * ‖u‖ ^ 2 := by
  rw [spacesLpReal_norm_sq]
  calc
    (∫ x, (n07aAngularLpNormalize μ a u x) ^ 2 ∂n07aAngularNormalizedMeasure μ a) =
        ∫ x, u x ^ 2 ∂n07aAngularNormalizedMeasure μ a :=
      integral_congr_ae ((n07aAngularLpNormalize_ae μ a u).fun_comp (fun x : ℝ => x ^ 2))
    _ = a⁻¹ * ∫ x, u x ^ 2 ∂μ := by
      rw [n07aAngularNormalizedMeasure, integral_smul_measure,
        ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le), smul_eq_mul]
    _ = a⁻¹ * ‖u‖ ^ 2 := by rw [← spacesLpReal_norm_sq]

include ha in
private theorem n07aAngularLpScale_norm (u : Lp ℝ 2 μ) :
    ‖Real.sqrt a • n07aAngularLpNormalize μ a u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt ha.le, n07aAngularLpNormalize_norm_sq μ a ha, ← mul_assoc,
    mul_inv_cancel₀ ha.ne', one_mul]

/-- Exact isometry from the actual measure to its normalization, including the
square-root factor in the actual function. -/
def n07aAngularLpScaleEquiv :
    Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 (n07aAngularNormalizedMeasure μ a) where
  toFun u := Real.sqrt a • n07aAngularLpNormalize μ a u
  map_add' := by
    intro u v
    rw [map_add, smul_add]
  map_smul' := by
    intro c u
    rw [map_smul, smul_comm, RingHom.id_apply]
  norm_map' := n07aAngularLpScale_norm μ a ha
  invFun v := (Real.sqrt a)⁻¹ • n07aAngularLpRestore μ a ha v
  left_inv := by
    intro u
    dsimp only
    rw [map_smul, n07aAngularLpRestore_normalize μ a ha, smul_smul,
      inv_mul_cancel₀ (Real.sqrt_pos.mpr ha).ne', one_smul]
  right_inv := by
    intro v
    dsimp only
    rw [map_smul, n07aAngularLpNormalize_restore μ a ha, smul_smul,
      mul_inv_cancel₀ (Real.sqrt_pos.mpr ha).ne', one_smul]

@[simp] theorem n07aAngularLpScaleEquiv_apply (u : Lp ℝ 2 μ) :
    n07aAngularLpScaleEquiv μ a ha u = Real.sqrt a • n07aAngularLpNormalize μ a u := rfl

@[simp] theorem n07aAngularLpScaleEquiv_symm_apply
    (u : Lp ℝ 2 (n07aAngularNormalizedMeasure μ a)) :
    (n07aAngularLpScaleEquiv μ a ha).symm u =
      (Real.sqrt a)⁻¹ • n07aAngularLpRestore μ a ha u := rfl

theorem n07aAngularLpScaleEquiv_ae (u : Lp ℝ 2 μ) :
    (n07aAngularLpScaleEquiv μ a ha u : α → ℝ) =ᵐ[n07aAngularNormalizedMeasure μ a]
      fun x => Real.sqrt a * u x := by
  rw [n07aAngularLpScaleEquiv_apply]
  filter_upwards [Lp.coeFn_smul (Real.sqrt a) (n07aAngularLpNormalize μ a u),
    n07aAngularLpNormalize_ae μ a u] with x hx hu
  simpa only [Pi.smul_apply, smul_eq_mul, hu] using hx

theorem n07aAngularLpScaleEquiv_symm_ae
    (u : Lp ℝ 2 (n07aAngularNormalizedMeasure μ a)) :
    ((n07aAngularLpScaleEquiv μ a ha).symm u : α → ℝ) =ᵐ[μ]
      fun x => (Real.sqrt a)⁻¹ * u x := by
  rw [n07aAngularLpScaleEquiv_symm_apply]
  filter_upwards [Lp.coeFn_smul ((Real.sqrt a)⁻¹) (n07aAngularLpRestore μ a ha u),
    n07aAngularLpRestore_ae μ a ha u] with x hx hu
  simpa only [Pi.smul_apply, smul_eq_mul, hu] using hx

end ContinuousFlexibility.Analysis
