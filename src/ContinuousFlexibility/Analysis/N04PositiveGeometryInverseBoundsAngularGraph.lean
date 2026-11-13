import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsBoundaryData
import ContinuousFlexibility.Analysis.AngularInverseFirstDerivative

/-!
# Actual triangular angular inverse data at a positive endpoint

The first inverse differential is a polynomial in the forward root-label
derivative and the radial derivative of the supplied source angle. The
finite inverse recurrence can therefore use these original boundary
data, without introducing a new inverse-Jacobian regularity premise.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff

def n04PositiveGeometry_angularGraph (φ : PolarPoint → ℝ) (p : PolarPoint) :
    PolarPoint := (p.1, φ p)

def n04PositiveGeometry_angularGraphInverse (φ : PolarPoint → ℝ)
    (p : PolarPoint) : PolarPoint := (p.1, parameterizedCircleInverse φ p)

def n04PositiveGeometry_angularInverseLinear (a b : ℝ) : PolarPoint →L[ℝ] PolarPoint :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (b • (ContinuousLinearMap.snd ℝ ℝ ℝ - a • ContinuousLinearMap.fst ℝ ℝ ℝ))

theorem n04PositiveGeometry_angularInverseLinear_apply (a b : ℝ) (v : PolarPoint) :
    n04PositiveGeometry_angularInverseLinear a b v =
      (v.1, b * (v.2 - a * v.1)) := by
  simp only [n04PositiveGeometry_angularInverseLinear,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]

section Angular

variable {φ : PolarPoint → ℝ} {T : ℝ}
  (hT : T ≠ 0) (hφ : ContDiff ℝ ∞ φ)
  (hpositive : ∀ p : PolarPoint, 0 < deriv (fun θ => φ (p.1, θ)) p.2)
  (hperiod : ∀ r θ, φ (r, θ + T) = φ (r, θ) + T)

include hφ in
theorem n04PositiveGeometry_angularGraph_contDiff :
    ContDiff ℝ ∞ (n04PositiveGeometry_angularGraph φ) :=
  contDiff_fst.prodMk hφ

include hT hφ hpositive hperiod in
theorem n04PositiveGeometry_angularGraphInverse_contDiff :
    ContDiff ℝ ∞ (n04PositiveGeometry_angularGraphInverse φ) :=
  contDiff_fst.prodMk (contDiff_parameterizedCircleInverse hT hφ hpositive hperiod)

include hT hφ hperiod in
theorem n04PositiveGeometry_angularGraph_right_inverse (p : PolarPoint) :
    n04PositiveGeometry_angularGraph φ (n04PositiveGeometry_angularGraphInverse φ p) = p :=
  Prod.ext rfl (parameterizedCircleInverse_right_inverse hT hφ hperiod p)

include hpositive in
theorem n04PositiveGeometry_angularGraph_left_inverse (p : PolarPoint) :
    n04PositiveGeometry_angularGraphInverse φ (n04PositiveGeometry_angularGraph φ p) = p :=
  Prod.ext rfl (parameterizedCircleInverse_left_inverse hpositive p)

include hT hφ hpositive hperiod

/-- An exact inverse angular boundary value identifies its actual first
angular derivative with the reciprocal forward angular derivative. -/
theorem n04PositiveGeometry_angularInverse_boundary_reciprocal
    (c : ℝ) (β : ℝ → ℝ)
    (hβ : ∀ θ, parameterizedCircleInverse φ (c, θ) = β θ) (θ : ℝ) :
    (angularPartial φ (c, β θ))⁻¹ = deriv β θ := by
  have hd := (hasDerivAt_parameterizedCircleInverse hT hφ hpositive hperiod c θ).deriv
  have he : (fun η => parameterizedCircleInverse φ (c, η)) = β := funext hβ
  rw [he, hβ θ,
    deriv_cylinder_angular_slice (hφ.differentiable (by simp))] at hd
  exact hd.symm

theorem n04PositiveGeometry_angularGraphInverse_fderiv_boundary
    (c : ℝ) (β : ℝ → ℝ)
    (hβ : ∀ θ, parameterizedCircleInverse φ (c, θ) = β θ) (θ : ℝ) :
    fderiv ℝ (n04PositiveGeometry_angularGraphInverse φ) (c, θ) =
      n04PositiveGeometry_angularInverseLinear
        (radialPartial φ (c, β θ)) (deriv β θ) := by
  have hA := contDiff_parameterizedCircleInverse hT hφ hpositive hperiod
  have hd := (hasFDerivAt_fst.prodMk
    (hA.differentiable (by simp) (c, θ)).hasFDerivAt).fderiv
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ (fun p : PolarPoint =>
    (p.1, parameterizedCircleInverse φ p)) (c, θ) v = _
  rw [hd, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    fderiv_parameterizedCircleInverse_apply hT hφ hpositive hperiod,
    hβ θ, n04PositiveGeometry_angularInverseLinear_apply, div_eq_mul_inv,
    n04PositiveGeometry_angularInverse_boundary_reciprocal hT hφ hpositive hperiod c β hβ]
  congr 1
  ring

/-- The displayed differential really is a left inverse of the forward
angular-graph differential at the same inverse point. -/
theorem n04PositiveGeometry_angularGraphInverse_fderiv_left (p : PolarPoint) :
    (fderiv ℝ (n04PositiveGeometry_angularGraphInverse φ) p).comp
      (fderiv ℝ (n04PositiveGeometry_angularGraph φ)
        (n04PositiveGeometry_angularGraphInverse φ p)) =
      ContinuousLinearMap.id ℝ PolarPoint := by
  let F := n04PositiveGeometry_angularGraph φ
  let G := n04PositiveGeometry_angularGraphInverse φ
  have hF : ContDiff ℝ ∞ F := n04PositiveGeometry_angularGraph_contDiff hφ
  have hG : ContDiff ℝ ∞ G :=
    n04PositiveGeometry_angularGraphInverse_contDiff hT hφ hpositive hperiod
  have hc := (hG.differentiable (by simp) (F (G p))).hasFDerivAt.comp (G p)
    (hF.differentiable (by simp) (G p)).hasFDerivAt
  have he : G ∘ F = id := funext
    (n04PositiveGeometry_angularGraph_left_inverse hpositive)
  rw [he] at hc
  have hd := hc.unique (hasFDerivAt_id (G p))
  have hr : F (G p) = p :=
    n04PositiveGeometry_angularGraph_right_inverse hT hφ hperiod p
  rw [hr] at hd
  exact hd

end Angular

variable {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}

/-- In the chosen family the differential uses the original source's
radial trace, evaluated at the actual forward root label. -/
theorem n04PositiveGeometry_controlled_angle_inverse_differential
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (side : Bool) (m : ℕ) (hsource : (X.src i side).val = some m) (θ : ℝ) :
    fderiv ℝ (n04PositiveGeometry_angularGraphInverse
        (G.toN04PositiveGeometryControlData.angle z i))
        (if side then n04PositiveRight i else n04PositiveLeft i, θ) =
      n04PositiveGeometry_angularInverseLinear
        (radialPartial (fun p =>
          (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).2)
          (if side then n04PositiveRight i else n04PositiveLeft i,
            n01RootLabel W.S W.C z m (!side) θ))
        (deriv (n01RootLabel W.S W.C z m (!side)) θ) := by
  let φ := G.toN04PositiveGeometryControlData.angle z i
  let c := if side then n04PositiveRight i else n04PositiveLeft i
  let β := n01RootLabel W.S W.C z m (!side)
  have hφ := n04PositiveGeometry_controlled_angle_contDiff G hz hs i
  have hp (p : PolarPoint) : 0 < deriv (fun η => φ (p.1, η)) p.2 :=
    n04PositiveGeometry_controlled_angle_positive G hz hs i p.1 p.2
  have hperiod (r θ : ℝ) : φ (r, θ + Real.pi) = φ (r, θ) + Real.pi :=
    n04PositiveGeometry_controlled_angle_period G hz hs i r θ
  have hβ (η : ℝ) : parameterizedCircleInverse φ (c, η) = β η :=
    n04PositiveGeometry_controlled_angle_inverse_boundary G hz hs i side m hsource η
  have hradial : radialPartial φ (c, β θ) =
      radialPartial (fun p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).2)
        (c, β θ) := by
    have hj := congrArg (fun A : PolarPoint [×1]→L[ℝ] ℝ => A (fun _ => (1, 0)))
      (n04PositiveGeometry_controlled_angle_boundary_jets G hz hs i side 1 (by omega) (β θ))
    simpa only [iteratedFDeriv_one_apply, radialPartial] using hj
  have hd := n04PositiveGeometry_angularGraphInverse_fderiv_boundary
    Real.pi_ne_zero hφ hp hperiod c β hβ θ
  rw [hradial] at hd
  exact hd

end ContinuousFlexibility.Analysis
