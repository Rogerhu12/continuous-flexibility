import ContinuousFlexibility.Analysis.PositiveReferenceInterpolation
import ContinuousFlexibility.Analysis.TravelStripGlobalInverse
import ContinuousFlexibility.Analysis.PrincipalDensityGerms

/-!
# The actual cylindrical reference interpolation

A scalar coordinate produced by the endpoint interpolation gives a
genuine smooth cylinder coordinate and a genuine smooth inverse.
Its planar Jacobian is exactly the actual scalar derivative. Scalar
endpoint coordinate and height germs lift to density germs on the plane.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def positiveReferenceCylinderChart (Y : ℝ → ℝ) (p : PolarPoint) : PolarPoint :=
  (Y p.1, p.2)

def positiveReferenceCylinderInverse (Y : ℝ → ℝ) (p : PolarPoint) : PolarPoint :=
  (Function.invFun Y p.1, p.2)

theorem contDiff_positiveReferenceCylinderChart
    {Y : ℝ → ℝ} (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (positiveReferenceCylinderChart Y) :=
  (hY.comp contDiff_fst).prodMk contDiff_snd

theorem contDiff_positiveReferenceCylinderInverse
    {Y : ℝ → ℝ} (hY : ContDiff ℝ ∞ (Function.invFun Y)) :
    ContDiff ℝ ∞ (positiveReferenceCylinderInverse Y) :=
  (hY.comp contDiff_fst).prodMk contDiff_snd

theorem positiveReferenceCylinder_leftInverse
    {Y : ℝ → ℝ} (hY : Function.Injective Y) :
    Function.LeftInverse (positiveReferenceCylinderInverse Y)
      (positiveReferenceCylinderChart Y) := by
  intro p
  apply Prod.ext
  · exact Function.leftInverse_invFun hY p.1
  · rfl

theorem positiveReferenceCylinder_rightInverse
    {Y : ℝ → ℝ} (hY : Function.Surjective Y) :
    Function.RightInverse (positiveReferenceCylinderInverse Y)
      (positiveReferenceCylinderChart Y) := by
  intro p
  apply Prod.ext
  · exact Function.rightInverse_invFun hY p.1
  · rfl

/-- This uses the actual scalar derivative, not a prescribed slope jet. -/
theorem planeJacobian_positiveReferenceCylinderChart
    {Y : ℝ → ℝ} {p : PolarPoint} (hY : DifferentiableAt ℝ Y p.1) :
    planeJacobian (positiveReferenceCylinderChart Y) p = deriv Y p.1 := by
  have hd : HasFDerivAt (fun q : PolarPoint => Y q.1)
      (deriv Y p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hY.hasDerivAt.comp_hasFDerivAt p hasFDerivAt_fst
  change planeJacobian (fun q : PolarPoint => (Y q.1, q.2)) p = deriv Y p.1
  rw [planeJacobian_preserve_second hd.differentiableAt]
  unfold radialPartial
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
    smul_eq_mul, mul_one]

/-- The scalar factory's verified outputs give global open smoothness,
strictly positive ordinary Jacobian, and the actual smooth inverse. -/
theorem positiveReferenceCylinder_geometry
    {Y H : ℝ → ℝ} (hY : ContDiff ℝ ∞ Y)
    (hYpos : ∀ r, 0 < deriv Y r) (hYbij : Function.Bijective Y)
    (hYinv : ContDiff ℝ ∞ (Function.invFun Y))
    (hH : ContDiff ℝ ∞ H) (hHpos : ∀ r, 0 < H r) :
    ContDiff ℝ ∞ (positiveReferenceCylinderChart Y) ∧
      (∀ p, 0 < planeJacobian (positiveReferenceCylinderChart Y) p) ∧
      ContDiff ℝ ∞ (positiveReferenceCylinderInverse Y) ∧
      Function.LeftInverse (positiveReferenceCylinderInverse Y)
        (positiveReferenceCylinderChart Y) ∧
      Function.RightInverse (positiveReferenceCylinderInverse Y)
        (positiveReferenceCylinderChart Y) ∧
      ContDiff ℝ ∞ (fun p : PolarPoint => H p.1) ∧
      (∀ p : PolarPoint, 0 < H p.1) := by
  refine ⟨contDiff_positiveReferenceCylinderChart hY, ?_,
    contDiff_positiveReferenceCylinderInverse hYinv,
    positiveReferenceCylinder_leftInverse hYbij.1,
    positiveReferenceCylinder_rightInverse hYbij.2, hH.comp contDiff_fst,
    fun p => hHpos p.1⟩
  intro p
  rw [planeJacobian_positiveReferenceCylinderChart
    (hY.differentiable (by simp) p.1)]
  exact hYpos p.1

theorem positiveReferenceCylinderChart_eventuallyEq
    {Y y : ℝ → ℝ} {c : ℝ} (hY : Y =ᶠ[𝓝 c] y) (θ : ℝ) :
    positiveReferenceCylinderChart Y =ᶠ[𝓝 (c, θ)]
      positiveReferenceCylinderChart y := by
  have hf : Tendsto (fun p : PolarPoint => p.1) (𝓝 (c, θ)) (𝓝 c) :=
    continuous_fst.tendsto (c, θ)
  filter_upwards [hY.comp_tendsto hf] with p hp
  apply Prod.ext
  · exact hp
  · rfl

/-- Full endpoint germs supplied by the scalar interpolation identify
the actual density remainder germ, with the same physical operator. -/
theorem positiveReferencePrincipalRemainder_endpoint_germ
    {A : SymmetricCoefficients} {Y y H h : ℝ → ℝ} {c : ℝ}
    (hY : Y =ᶠ[𝓝 c] y) (hH : H =ᶠ[𝓝 c] h)
    (N : ℝ → ℝ) (i : Fin 3) (θ : ℝ) :
    (fun p => canonicalCoefficientComponent i
        (coordinatePrincipalDensity A (positiveReferenceCylinderChart Y)
          (fun q => H q.1)) p - N (Y p.1)) =ᶠ[𝓝 (c, θ)]
    (fun p => canonicalCoefficientComponent i
        (coordinatePrincipalDensity A (positiveReferenceCylinderChart y)
          (fun q => h q.1)) p - N (y p.1)) := by
  have hh : (fun p : PolarPoint => H p.1) =ᶠ[𝓝 (c, θ)]
      (fun p : PolarPoint => h p.1) :=
    hH.comp_tendsto (continuous_fst.tendsto (c, θ))
  exact coordinatePrincipalRemainder_eventuallyEq
    (positiveReferenceCylinderChart_eventuallyEq hY θ) hh N i

end ContinuousFlexibility.Analysis

