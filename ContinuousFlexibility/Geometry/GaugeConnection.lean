import ContinuousFlexibility.Geometry.RotatedCoframe

/-!
# The connection of a rotated coframe

For the convention `dη₁ = α ∧ η₂`, `dη₂ = -α ∧ η₁`, rotation by
`exp(i ψ)` changes the connection to `α - dψ`. All exterior coefficients
below use actual Frechet partial derivatives. This does not assert that an
arbitrary closed connection on an annulus has a single-valued primitive.
-/

noncomputable section

namespace ContinuousFlexibility

set_option backward.isDefEq.respectTransparency false

/-- Difference of two coordinate one-forms, without introducing global
algebraic instances for the one-form structure. -/
def subtractPlaneOneForm (α β : PlaneOneForm) : PlaneOneForm :=
  ⟨fun x => α.radial x - β.radial x, fun x => α.angular x - β.angular x⟩

/-- The connection of the coframe rotated by `exp(i ψ)`. -/
def gaugeConnection (α : PlaneOneForm) (ψ : PolarPoint → ℝ) : PlaneOneForm :=
  subtractPlaneOneForm α (coordinateDifferential ψ)

theorem exteriorCoefficient_subtractPlaneOneForm
    {α β : PlaneOneForm} {x : PolarPoint}
    (hαr : DifferentiableAt ℝ α.radial x) (hαθ : DifferentiableAt ℝ α.angular x)
    (hβr : DifferentiableAt ℝ β.radial x) (hβθ : DifferentiableAt ℝ β.angular x) :
    exteriorCoefficient (subtractPlaneOneForm α β) x =
      exteriorCoefficient α x - exteriorCoefficient β x := by
  change radialPartial (fun y => α.angular y - β.angular y) x -
      angularPartial (fun y => α.radial y - β.radial y) x = _
  rw [radialPartial_sub hαθ hβθ, angularPartial_sub hαr hβr]
  unfold exteriorCoefficient
  ring

/-- The first Cartan equation with the transformed connection. -/
theorem rotatedCoframeOne_cartan_gauge
    {α η₁ η₂ : PlaneOneForm} {ψ : PolarPoint → ℝ} {x : PolarPoint}
    (hψ : DifferentiableAt ℝ ψ x)
    (h1r : DifferentiableAt ℝ η₁.radial x) (h1θ : DifferentiableAt ℝ η₁.angular x)
    (h2r : DifferentiableAt ℝ η₂.radial x) (h2θ : DifferentiableAt ℝ η₂.angular x)
    (hcartan1 : exteriorCoefficient η₁ x = wedgeCoefficient α η₂ x)
    (hcartan2 : exteriorCoefficient η₂ x = -wedgeCoefficient α η₁ x) :
    exteriorCoefficient (rotatedCoframeOne ψ η₁ η₂) x =
      wedgeCoefficient (gaugeConnection α ψ) (rotatedCoframeTwo ψ η₁ η₂) x := by
  rw [exteriorCoefficient_rotatedCoframeOne hψ h1r h1θ h2r h2θ, hcartan1, hcartan2]
  dsimp [gaugeConnection, subtractPlaneOneForm, wedgeCoefficient,
    coordinateDifferential, rotatedCoframeTwo]
  ring

/-- The second Cartan equation with the same transformed connection. -/
theorem rotatedCoframeTwo_cartan_gauge
    {α η₁ η₂ : PlaneOneForm} {ψ : PolarPoint → ℝ} {x : PolarPoint}
    (hψ : DifferentiableAt ℝ ψ x)
    (h1r : DifferentiableAt ℝ η₁.radial x) (h1θ : DifferentiableAt ℝ η₁.angular x)
    (h2r : DifferentiableAt ℝ η₂.radial x) (h2θ : DifferentiableAt ℝ η₂.angular x)
    (hcartan1 : exteriorCoefficient η₁ x = wedgeCoefficient α η₂ x)
    (hcartan2 : exteriorCoefficient η₂ x = -wedgeCoefficient α η₁ x) :
    exteriorCoefficient (rotatedCoframeTwo ψ η₁ η₂) x =
      -wedgeCoefficient (gaugeConnection α ψ) (rotatedCoframeOne ψ η₁ η₂) x := by
  rw [exteriorCoefficient_rotatedCoframeTwo hψ h1r h1θ h2r h2θ, hcartan1, hcartan2]
  dsimp [gaugeConnection, subtractPlaneOneForm, wedgeCoefficient,
    coordinateDifferential, rotatedCoframeOne]
  ring

/-- Actual curvature-coefficient invariance under a smooth gauge change:
`d(α - dψ) = dα`, by actual mixed-partial symmetry. -/
theorem exteriorCoefficient_gaugeConnection
    {α : PlaneOneForm} {ψ : PolarPoint → ℝ} {x : PolarPoint}
    (hαr : DifferentiableAt ℝ α.radial x) (hαθ : DifferentiableAt ℝ α.angular x)
    (hψ : ContDiffAt ℝ 2 ψ x) :
    exteriorCoefficient (gaugeConnection α ψ) x = exteriorCoefficient α x := by
  have hpr := (contDiffAt_radialPartial hψ (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hpt := (contDiffAt_angularPartial hψ (m := 1) (by norm_num)).differentiableAt one_ne_zero
  change exteriorCoefficient (subtractPlaneOneForm α (coordinateDifferential ψ)) x = _
  rw [exteriorCoefficient_subtractPlaneOneForm hαr hαθ hpr hpt,
    exteriorCoefficient_coordinateDifferential hψ, sub_zero]

theorem gaugeConnection_closed_iff
    {α : PlaneOneForm} {ψ : PolarPoint → ℝ} {x : PolarPoint}
    (hαr : DifferentiableAt ℝ α.radial x) (hαθ : DifferentiableAt ℝ α.angular x)
    (hψ : ContDiffAt ℝ 2 ψ x) :
    exteriorCoefficient (gaugeConnection α ψ) x = 0 ↔ exteriorCoefficient α x = 0 := by
  rw [exteriorCoefficient_gaugeConnection hαr hαθ hψ]

/-- Removing the polar angle does not change the radial connection field. -/
@[simp] theorem gaugeConnection_angle_radial (α : PlaneOneForm) (x : PolarPoint) :
    (gaugeConnection α Prod.snd).radial x = α.radial x := by
  simp [gaugeConnection, subtractPlaneOneForm, coordinateDifferential]

/-- The angular connection field changes by exactly one under `ψ = θ`. -/
@[simp] theorem gaugeConnection_angle_angular (α : PlaneOneForm) (x : PolarPoint) :
    (gaugeConnection α Prod.snd).angular x = α.angular x - 1 := by
  simp [gaugeConnection, subtractPlaneOneForm, coordinateDifferential]

/-- Specialization of gauge invariance to the polar-to-Cartesian rotation. -/
theorem exteriorCoefficient_gaugeConnection_angle
    {α : PlaneOneForm} {x : PolarPoint}
    (hαr : DifferentiableAt ℝ α.radial x) (hαθ : DifferentiableAt ℝ α.angular x) :
    exteriorCoefficient (gaugeConnection α Prod.snd) x = exteriorCoefficient α x := by
  exact exteriorCoefficient_gaugeConnection hαr hαθ contDiffAt_snd

end ContinuousFlexibility
