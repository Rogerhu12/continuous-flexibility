module

public import ContinuousFlexibility.Geometry.CoframeCurvature
public import ContinuousFlexibility.Scalar.FormPullback

/-!
# Actual coordinate change for Cartan curvature

This combines genuine pullback differentiation with independence of the oriented
metric coframe. In particular, curvature closedness can be checked in a polar
chart without constructing a global polar angle.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set
open scoped ContDiff

theorem cartan_equations_pullback
    {F : PolarPoint → PolarPoint} {η₁ η₂ α : PlaneOneForm} {x : PolarPoint}
    (hF : ContDiffAt ℝ 2 F x)
    (h1r : DifferentiableAt ℝ η₁.radial (F x))
    (h1θ : DifferentiableAt ℝ η₁.angular (F x))
    (h2r : DifferentiableAt ℝ η₂.radial (F x))
    (h2θ : DifferentiableAt ℝ η₂.angular (F x))
    (hc1 : exteriorCoefficient η₁ (F x) = wedgeCoefficient α η₂ (F x))
    (hc2 : exteriorCoefficient η₂ (F x) = -wedgeCoefficient α η₁ (F x)) :
    exteriorCoefficient (pullbackPlaneOneForm F η₁) x =
        wedgeCoefficient (pullbackPlaneOneForm F α) (pullbackPlaneOneForm F η₂) x ∧
      exteriorCoefficient (pullbackPlaneOneForm F η₂) x =
        -wedgeCoefficient (pullbackPlaneOneForm F α) (pullbackPlaneOneForm F η₁) x := by
  rw [exteriorCoefficient_pullbackPlaneOneForm hF h1r h1θ,
    exteriorCoefficient_pullbackPlaneOneForm hF h2r h2θ,
    wedgeCoefficient_pullbackPlaneOneForm, wedgeCoefficient_pullbackPlaneOneForm,
    hc1, hc2]
  constructor
  · rfl
  · ring

/-- The curvature of a target Cartan coframe, pulled back through an actual smooth map,
equals the curvature of any equally oriented smooth coframe for its pullback metric. -/
theorem cartan_curvature_pullback_eq_of_same_metric
    {U : Set PolarPoint} (hU : IsOpen U) {x : PolarPoint} (hx : x ∈ U)
    {F : PolarPoint → PolarPoint} {η₁ η₂ ζ₁ ζ₂ α β : PlaneOneForm}
    (hF : ∀ y ∈ U, ContDiffAt ℝ ∞ F y)
    (hη : ∀ y ∈ U, ContDiffAt ℝ ∞ η₁.radial y ∧ ContDiffAt ℝ ∞ η₁.angular y ∧
      ContDiffAt ℝ ∞ η₂.radial y ∧ ContDiffAt ℝ ∞ η₂.angular y)
    (hζ : ∀ y ∈ U, ContDiffAt ℝ ∞ ζ₁.radial (F y) ∧ ContDiffAt ℝ ∞ ζ₁.angular (F y) ∧
      ContDiffAt ℝ ∞ ζ₂.radial (F y) ∧ ContDiffAt ℝ ∞ ζ₂.angular (F y))
    (hαr : DifferentiableAt ℝ α.radial x) (hαθ : DifferentiableAt ℝ α.angular x)
    (hβr : DifferentiableAt ℝ β.radial (F x))
    (hβθ : DifferentiableAt ℝ β.angular (F x))
    (hcartη : ∀ y ∈ U,
      exteriorCoefficient η₁ y = wedgeCoefficient α η₂ y ∧
      exteriorCoefficient η₂ y = -wedgeCoefficient α η₁ y)
    (hcartζ : ∀ y ∈ U,
      exteriorCoefficient ζ₁ (F y) = wedgeCoefficient β ζ₂ (F y) ∧
      exteriorCoefficient ζ₂ (F y) = -wedgeCoefficient β ζ₁ (F y))
    (hmetric : ∀ y ∈ U, ∀ v : PolarPoint,
      formValue ζ₁ (F y) (fderiv ℝ F y v) ^ 2 +
        formValue ζ₂ (F y) (fderiv ℝ F y v) ^ 2 =
          formValue η₁ y v ^ 2 + formValue η₂ y v ^ 2)
    (hor : ∀ y ∈ U, 0 < wedgeCoefficient η₁ η₂ y *
      (wedgeCoefficient ζ₁ ζ₂ (F y) * planeJacobian F y)) :
    exteriorCoefficient β (F x) * planeJacobian F x = exteriorCoefficient α x := by
  have hpreg : ∀ y ∈ U,
      ContDiffAt ℝ ∞ (pullbackPlaneOneForm F ζ₁).radial y ∧
      ContDiffAt ℝ ∞ (pullbackPlaneOneForm F ζ₁).angular y ∧
      ContDiffAt ℝ ∞ (pullbackPlaneOneForm F ζ₂).radial y ∧
      ContDiffAt ℝ ∞ (pullbackPlaneOneForm F ζ₂).angular y := by
    intro y hy
    obtain ⟨h1r, h1θ, h2r, h2θ⟩ := hζ y hy
    exact ⟨(contDiffAt_pullbackPlaneOneForm (hF y hy) h1r h1θ).1,
      (contDiffAt_pullbackPlaneOneForm (hF y hy) h1r h1θ).2,
      (contDiffAt_pullbackPlaneOneForm (hF y hy) h2r h2θ).1,
      (contDiffAt_pullbackPlaneOneForm (hF y hy) h2r h2θ).2⟩
  have hpcartan : ∀ y ∈ U,
      exteriorCoefficient (pullbackPlaneOneForm F ζ₁) y =
        wedgeCoefficient (pullbackPlaneOneForm F β) (pullbackPlaneOneForm F ζ₂) y ∧
      exteriorCoefficient (pullbackPlaneOneForm F ζ₂) y =
        -wedgeCoefficient (pullbackPlaneOneForm F β) (pullbackPlaneOneForm F ζ₁) y := by
    intro y hy
    obtain ⟨h1r, h1θ, h2r, h2θ⟩ := hζ y hy
    exact cartan_equations_pullback ((hF y hy).of_le (by simp))
      (h1r.differentiableAt (by simp)) (h1θ.differentiableAt (by simp))
      (h2r.differentiableAt (by simp)) (h2θ.differentiableAt (by simp))
      (hcartζ y hy).1 (hcartζ y hy).2
  have hpmetric : ∀ y ∈ U, ∀ v : PolarPoint,
      formValue (pullbackPlaneOneForm F ζ₁) y v ^ 2 +
        formValue (pullbackPlaneOneForm F ζ₂) y v ^ 2 =
          formValue η₁ y v ^ 2 + formValue η₂ y v ^ 2 := by
    intro y hy v
    rw [formValue_pullbackPlaneOneForm, formValue_pullbackPlaneOneForm]
    exact hmetric y hy v
  have hpor : ∀ y ∈ U, 0 < wedgeCoefficient η₁ η₂ y *
      wedgeCoefficient (pullbackPlaneOneForm F ζ₁) (pullbackPlaneOneForm F ζ₂) y := by
    intro y hy
    rw [wedgeCoefficient_pullbackPlaneOneForm]
    exact hor y hy
  have hc := coframe_curvature_eq_of_same_metric hU hx hη hpreg hαr hαθ
    hcartη hpcartan hpmetric hpor
  rw [exteriorCoefficient_pullbackPlaneOneForm ((hF x hx).of_le (by simp)) hβr hβθ] at hc
  exact hc

end ContinuousFlexibility
