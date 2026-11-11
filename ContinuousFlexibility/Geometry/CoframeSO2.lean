import ContinuousFlexibility.Geometry.CoframeRotationAlgebra
import ContinuousFlexibility.Geometry.GaugeConnection

/-!
# Angle-free SO(2) connection calculus

The Maurer--Cartan form `C dS - S dC` is constructed with actual partial
derivatives. Its exterior derivative vanishes when `C²+S²=1` locally.
No single-valued angle or primitive on an annulus is used.
-/

noncomputable section

namespace ContinuousFlexibility

open Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def so2CoframeOne (C S : PolarPoint → ℝ) (η₁ η₂ : PlaneOneForm) : PlaneOneForm :=
  ⟨fun x => C x * η₁.radial x - S x * η₂.radial x,
   fun x => C x * η₁.angular x - S x * η₂.angular x⟩

def so2CoframeTwo (C S : PolarPoint → ℝ) (η₁ η₂ : PlaneOneForm) : PlaneOneForm :=
  ⟨fun x => S x * η₁.radial x + C x * η₂.radial x,
   fun x => S x * η₁.angular x + C x * η₂.angular x⟩

def so2Connection (C S : PolarPoint → ℝ) : PlaneOneForm :=
  ⟨fun x => C x * radialPartial S x - S x * radialPartial C x,
   fun x => C x * angularPartial S x - S x * angularPartial C x⟩

theorem so2_tangent_identity {C S Cr Sr : ℝ}
    (hu : C ^ 2 + S ^ 2 = 1) (ht : C * Cr + S * Sr = 0) :
    Cr = -S * (C * Sr - S * Cr) ∧ Sr = C * (C * Sr - S * Cr) := by
  constructor
  · linear_combination C * ht - Cr * hu
  · linear_combination S * ht - Sr * hu

theorem so2_unit_tangent {C S : PolarPoint → ℝ} {x : PolarPoint}
    (hC : DifferentiableAt ℝ C x) (hS : DifferentiableAt ℝ S x)
    (hu : (fun y => C y ^ 2 + S y ^ 2) =ᶠ[𝓝 x] fun _ => 1) :
    C x ^ 2 + S x ^ 2 = 1 ∧
      C x * radialPartial C x + S x * radialPartial S x = 0 ∧
      C x * angularPartial C x + S x * angularPartial S x = 0 := by
  have hr : radialPartial (fun y => C y ^ 2 + S y ^ 2) x = 0 := by
    unfold radialPartial
    rw [hu.fderiv_eq]
    simp
  have hθ : angularPartial (fun y => C y ^ 2 + S y ^ 2) x = 0 := by
    unfold angularPartial
    rw [hu.fderiv_eq]
    simp
  rw [radialPartial_add (f := fun y => C y ^ 2) (g := fun y => S y ^ 2)
    (hC.pow 2) (hS.pow 2), radialPartial_sq hC, radialPartial_sq hS] at hr
  rw [angularPartial_add (f := fun y => C y ^ 2) (g := fun y => S y ^ 2)
    (hC.pow 2) (hS.pow 2), angularPartial_sq hC, angularPartial_sq hS] at hθ
  exact ⟨hu.eq_of_nhds, by linarith, by linarith⟩

theorem exteriorCoefficient_so2Connection {C S : PolarPoint → ℝ} {x : PolarPoint}
    (hC : ContDiffAt ℝ 2 C x) (hS : ContDiffAt ℝ 2 S x) :
    exteriorCoefficient (so2Connection C S) x =
      2 * (radialPartial C x * angularPartial S x -
        angularPartial C x * radialPartial S x) := by
  have hC0 := hC.differentiableAt two_ne_zero
  have hS0 := hS.differentiableAt two_ne_zero
  have hCr := (contDiffAt_radialPartial hC (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hCθ := (contDiffAt_angularPartial hC (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hSr := (contDiffAt_radialPartial hS (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hSθ := (contDiffAt_angularPartial hS (m := 1) (by norm_num)).differentiableAt one_ne_zero
  change radialPartial (fun y => C y * angularPartial S y - S y * angularPartial C y) x -
    angularPartial (fun y => C y * radialPartial S y - S y * radialPartial C y) x = _
  rw [radialPartial_sub (f := fun y => C y * angularPartial S y)
      (g := fun y => S y * angularPartial C y) (hC0.mul hSθ) (hS0.mul hCθ),
    angularPartial_sub (f := fun y => C y * radialPartial S y)
      (g := fun y => S y * radialPartial C y) (hC0.mul hSr) (hS0.mul hCr),
    radialPartial_mul hC0 hSθ, radialPartial_mul hS0 hCθ,
    angularPartial_mul hC0 hSr, angularPartial_mul hS0 hCr,
    radial_angular_commute hC, radial_angular_commute hS]
  ring

theorem so2Connection_closed {C S : PolarPoint → ℝ} {x : PolarPoint}
    (hC : ContDiffAt ℝ 2 C x) (hS : ContDiffAt ℝ 2 S x)
    (hu : (fun y => C y ^ 2 + S y ^ 2) =ᶠ[𝓝 x] fun _ => 1) :
    exteriorCoefficient (so2Connection C S) x = 0 := by
  obtain ⟨hu0, hr, hθ⟩ := so2_unit_tangent
    (hC.differentiableAt two_ne_zero) (hS.differentiableAt two_ne_zero) hu
  rw [exteriorCoefficient_so2Connection hC hS]
  have hd : radialPartial C x * angularPartial S x -
      angularPartial C x * radialPartial S x = 0 := by
    by_cases hc : C x = 0
    · have hs : S x ≠ 0 := by intro hz; simp [hc, hz] at hu0
      have hsr : radialPartial S x = 0 := (mul_eq_zero.mp (by simpa [hc] using hr)).resolve_left hs
      have hsθ : angularPartial S x = 0 := (mul_eq_zero.mp (by simpa [hc] using hθ)).resolve_left hs
      rw [hsr, hsθ]
      ring
    · have hz : C x * (radialPartial C x * angularPartial S x -
          angularPartial C x * radialPartial S x) = 0 := by
        linear_combination angularPartial S x * hr - radialPartial S x * hθ
      exact (mul_eq_zero.mp hz).resolve_left hc
  rw [hd, mul_zero]

theorem exteriorCoefficient_so2CoframeOne
    {C S : PolarPoint → ℝ} {η₁ η₂ : PlaneOneForm} {x : PolarPoint}
    (hC : DifferentiableAt ℝ C x) (hS : DifferentiableAt ℝ S x)
    (h1r : DifferentiableAt ℝ η₁.radial x) (h1θ : DifferentiableAt ℝ η₁.angular x)
    (h2r : DifferentiableAt ℝ η₂.radial x) (h2θ : DifferentiableAt ℝ η₂.angular x) :
    exteriorCoefficient (so2CoframeOne C S η₁ η₂) x =
      C x * exteriorCoefficient η₁ x - S x * exteriorCoefficient η₂ x +
        wedgeCoefficient (coordinateDifferential C) η₁ x -
        wedgeCoefficient (coordinateDifferential S) η₂ x := by
  have hr := (hC.hasFDerivAt.mul h1r.hasFDerivAt).sub (hS.hasFDerivAt.mul h2r.hasFDerivAt)
  have hθ := (hC.hasFDerivAt.mul h1θ.hasFDerivAt).sub (hS.hasFDerivAt.mul h2θ.hasFDerivAt)
  change HasFDerivAt (so2CoframeOne C S η₁ η₂).radial _ x at hr
  change HasFDerivAt (so2CoframeOne C S η₁ η₂).angular _ x at hθ
  simp only [exteriorCoefficient, radialPartial, angularPartial]
  rw [hθ.fderiv, hr.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, wedgeCoefficient,
    coordinateDifferential, radialPartial, angularPartial]
  ring

theorem exteriorCoefficient_so2CoframeTwo
    {C S : PolarPoint → ℝ} {η₁ η₂ : PlaneOneForm} {x : PolarPoint}
    (hC : DifferentiableAt ℝ C x) (hS : DifferentiableAt ℝ S x)
    (h1r : DifferentiableAt ℝ η₁.radial x) (h1θ : DifferentiableAt ℝ η₁.angular x)
    (h2r : DifferentiableAt ℝ η₂.radial x) (h2θ : DifferentiableAt ℝ η₂.angular x) :
    exteriorCoefficient (so2CoframeTwo C S η₁ η₂) x =
      S x * exteriorCoefficient η₁ x + C x * exteriorCoefficient η₂ x +
        wedgeCoefficient (coordinateDifferential S) η₁ x +
        wedgeCoefficient (coordinateDifferential C) η₂ x := by
  have hr := (hS.hasFDerivAt.mul h1r.hasFDerivAt).add (hC.hasFDerivAt.mul h2r.hasFDerivAt)
  have hθ := (hS.hasFDerivAt.mul h1θ.hasFDerivAt).add (hC.hasFDerivAt.mul h2θ.hasFDerivAt)
  change HasFDerivAt (so2CoframeTwo C S η₁ η₂).radial _ x at hr
  change HasFDerivAt (so2CoframeTwo C S η₁ η₂).angular _ x at hθ
  simp only [exteriorCoefficient, radialPartial, angularPartial]
  rw [hθ.fderiv, hr.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, wedgeCoefficient,
    coordinateDifferential, radialPartial, angularPartial]
  ring

theorem contDiffAt_so2Connection {C S : PolarPoint → ℝ} {x : PolarPoint}
    (hC : ContDiffAt ℝ ∞ C x) (hS : ContDiffAt ℝ ∞ S x) :
    ContDiffAt ℝ ∞ (so2Connection C S).radial x ∧
      ContDiffAt ℝ ∞ (so2Connection C S).angular x := by
  exact ⟨(hC.mul (contDiffAt_radialPartial hS (by simp))).sub
      (hS.mul (contDiffAt_radialPartial hC (by simp))),
    (hC.mul (contDiffAt_angularPartial hS (by simp))).sub
      (hS.mul (contDiffAt_angularPartial hC (by simp)))⟩

theorem so2Coframe_cartan
    {C S : PolarPoint → ℝ} {η₁ η₂ α : PlaneOneForm} {x : PolarPoint}
    (hC : DifferentiableAt ℝ C x) (hS : DifferentiableAt ℝ S x)
    (h1r : DifferentiableAt ℝ η₁.radial x) (h1θ : DifferentiableAt ℝ η₁.angular x)
    (h2r : DifferentiableAt ℝ η₂.radial x) (h2θ : DifferentiableAt ℝ η₂.angular x)
    (hu : (fun y => C y ^ 2 + S y ^ 2) =ᶠ[𝓝 x] fun _ => 1)
    (hc1 : exteriorCoefficient η₁ x = wedgeCoefficient α η₂ x)
    (hc2 : exteriorCoefficient η₂ x = -wedgeCoefficient α η₁ x) :
    exteriorCoefficient (so2CoframeOne C S η₁ η₂) x =
        wedgeCoefficient (subtractPlaneOneForm α (so2Connection C S))
          (so2CoframeTwo C S η₁ η₂) x ∧
      exteriorCoefficient (so2CoframeTwo C S η₁ η₂) x =
        -wedgeCoefficient (subtractPlaneOneForm α (so2Connection C S))
          (so2CoframeOne C S η₁ η₂) x := by
  obtain ⟨hu0, hr, hθ⟩ := so2_unit_tangent hC hS hu
  constructor
  · rw [exteriorCoefficient_so2CoframeOne hC hS h1r h1θ h2r h2θ, hc1, hc2]
    simp only [wedgeCoefficient, coordinateDifferential, subtractPlaneOneForm,
      so2Connection, so2CoframeTwo]
    linear_combination (C x * η₁.angular x - S x * η₂.angular x) * hr +
      (S x * η₂.radial x - C x * η₁.radial x) * hθ +
      (-radialPartial C x * η₁.angular x + angularPartial C x * η₁.radial x +
        radialPartial S x * η₂.angular x - angularPartial S x * η₂.radial x) * hu0
  · rw [exteriorCoefficient_so2CoframeTwo hC hS h1r h1θ h2r h2θ, hc1, hc2]
    simp only [wedgeCoefficient, coordinateDifferential, subtractPlaneOneForm,
      so2Connection, so2CoframeOne]
    linear_combination (S x * η₁.angular x + C x * η₂.angular x) * hr -
      (S x * η₁.radial x + C x * η₂.radial x) * hθ +
      (-radialPartial S x * η₁.angular x + angularPartial S x * η₁.radial x -
        radialPartial C x * η₂.angular x + angularPartial C x * η₂.radial x) * hu0

end ContinuousFlexibility
