import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsRadial
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledOneSidedTransport
import ContinuousFlexibility.Analysis.N04RealizationOneSidedTransportDirections

/-!
# Both actual positive transports from the original endpoint towers

The forward endpoint data produce the angular lift and its genuine
inverse in the existing circle model. Their actual pulled-back radial
traces feed the finite scalar inverse kernel. Thus the inverse transport
has a joint tower on the original state space, using exactly the same
stored widths as the forward map and with no inverse tower as input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
  {U : Set E}

/-- The only coefficient assumptions are the finite forward margins
retained by the controlled transport factory. The fixed circle label zero
is an implementation of the same angular functions, uniformly over all
physical components. -/
def n04PositiveGeometry_oneSidedTransportFactorDirections
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation S.grading)
    (hU : IsOpen U) (hc : Convex ℝ U) (n : ℕ)
    {l r c d κφ κX M Mσ : ℝ} (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκX : 0 < κX) (hMσ : 0 ≤ Mσ)
    (ψ X : E → Bool → PolarPoint → ℝ)
    (hψ : ∀ x ∈ U, ∀ side (j : Fin (n + 2)), ContDiff ℝ ∞
      (fun θ => radialBoundaryJet (ψ x side) (if side then r else l) j θ -
        if (j : ℕ) = 0 then θ else 0))
    (hperiod : ∀ x ∈ U, ∀ side (j : Fin (n + 2)), Function.Periodic
      (fun θ => radialBoundaryJet (ψ x side) (if side then r else l) j θ -
        if (j : ℕ) = 0 then θ else 0) Real.pi)
    (Jψ : ∀ side (j : Fin (n + 2)) b θ, SmoothDirections U
      (fun x => iteratedDeriv b (fun η =>
        radialBoundaryJet (ψ x side) (if side then r else l) j η -
          if (j : ℕ) = 0 then η else 0) θ))
    (hbound : ∀ side j b, UniformScalarJetSeminormBounds (Jψ side j b))
    (JX : ∀ side (j : Fin (n + 2)), SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => radialBoundaryJet (X p.1 side)
        (if side then r else l) j p.2))
    (hXvalue : ∀ x ∈ U, ∀ side θ,
      X x side (if side then r else l, θ) = if side then r else l)
    (hpositive : ∀ x ∈ U, ∀ t θ, 0 < deriv (fun η =>
      wholeComponentEndpointAngle n
        (oneSidedEndpointRepresentative (n + 2) l r (ψ x))
        l r c d κφ M (t, η)) θ)
    (hfirst : ∀ x ∈ U, ∀ side θ, κX <
      n04PositiveGeometry_oneSidedFiberData n (ψ x) (X x) l r c d κφ M side 1 θ)
    (hcoeff : ∀ x ∈ U, ∀ side (j : Fin (n + 1)) θ,
      |n04PositiveGeometry_oneSidedFiberData n (ψ x) (X x)
        l r c d κφ M side (j + 1) θ| < Mσ) :
    let φ : E → PolarPoint → ℝ := fun x => wholeComponentEndpointAngle n
      (oneSidedEndpointRepresentative (n + 2) l r (ψ x)) l r c d κφ M
    let X₀ : E → Bool → PolarPoint → ℝ := fun x =>
      oneSidedEndpointRepresentative (n + 1) l r (X x)
    let Y : E → PolarPoint → ℝ := fun x =>
      endpointFiberPullbackCoordinate n (φ x) (X₀ x) l r c d κX Mσ
    SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => φ p.1 p.2) ×
    SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint =>
      parameterizedCircleInverse (φ p.1) p.2) ×
    SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => Y p.1 p.2) ×
    SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint =>
      positiveFiberRadialInverse (Y p.1) p.2) ×
    (∀ side (j : Fin (n + 1)), SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => n04PositiveGeometry_oneSidedFiberData n
        (ψ p.1) (X p.1) l r c d κφ M side (j + 1) p.2)) ×
    SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint =>
      oneSidedWholeComponentTransport n (ψ p.1) (X p.1) l r c d κφ κX M Mσ p.2) ×
    SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint =>
      oneSidedWholeComponentTransportInverse n (ψ p.1) (X p.1) l r c d κφ κX M Mσ p.2) := by
  let Ψ : E → Bool → PolarPoint → ℝ := fun x =>
    oneSidedEndpointRepresentative (n + 2) l r (ψ x)
  let A : E → Bool → ℕ → ℝ → ℝ := fun x => rawEndpointAngularData l r (Ψ x)
  have hangular (x : E) (side : Bool) (j : Fin (n + 2)) :
      (fun θ => A x side j θ - if (j : ℕ) = 0 then θ else 0) =
        (fun θ => radialBoundaryJet (ψ x side) (if side then r else l) j θ -
          if (j : ℕ) = 0 then θ else 0) := by
    funext θ
    change radialBoundaryJet (oneSidedBoundaryTaylorRepresentative (n + 2)
      (if side then r else l) (ψ x side)) (if side then r else l) j θ - _ = _
    rw [radialBoundaryJet_oneSidedBoundaryTaylorRepresentative _ _ _ (by omega)]
  let JA : ∀ side (j : Fin (n + 2)) b θ, SmoothDirections U
      (fun x => iteratedDeriv b (fun η =>
        A x side j η - if (j : ℕ) = 0 then η else 0) θ) :=
    fun side j b θ => (Jψ side j b θ).congrOn
      (fun x _ => by rw [hangular x side j])
  let φ : E → PolarPoint → ℝ := fun x =>
    wholeComponentEndpointAngle n (Ψ x) l r c d κφ M
  let pair := n04Realization_positiveAngularTaylor_jointDirections hS hT hD hγ hi
    hU hc (n + 1) 0 l r (endpointAngularWidth (n + 1) l r c d κφ M) A
    (fun x hx side j => by rw [hangular x side j]; exact hψ x hx side j)
    (fun x hx side j => by rw [hangular x side j]; exact hperiod x hx side j)
    JA (fun side j b => hbound side j b) hpositive
  let X₀ : E → Bool → PolarPoint → ℝ := fun x =>
    oneSidedEndpointRepresentative (n + 1) l r (X x)
  let KX : ∀ side, SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => X₀ p.1 side p.2) := fun side =>
    n04Realization_oneSidedRepresentative_jointDirections hU (n + 1)
      (if side then r else l) (fun x => X x side) (JX side)
  let F : Bool → E → PolarPoint → ℝ := fun side x => angularFiberPullback (φ x) (X₀ x side)
  let JF : ∀ side, SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => F side p.1 p.2) := fun side =>
    n04Realization_angularFiberPullback_jointDirections hU φ (fun x => X₀ x side)
      pair.2 (KX side)
  let B : E → Bool → ℕ → ℝ → ℝ := fun x side =>
    radialBoundaryJet (F side x) (if side then r else l)
  have hB (x : E) (hx : x ∈ U) (side : Bool) (j : ℕ) (_hj : j ≤ n + 1) :
      ContDiff ℝ ∞ (B x side j) :=
    contDiff_radialBoundaryJet
      (contDiffOn_univ.mp ((JF side).spatial_value_contDiffOn isOpen_univ x hx))
      (if side then r else l) j
  let JB : ∀ side (j : Fin (n + 1)), SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => B p.1 side (j + 1) p.2) := fun side j =>
    n04Realization_radialBoundaryJointDirections hU hc (F side) (JF side)
      (if side then r else l) (j + 1)
  have hzero (x : E) (hx : x ∈ U) (side : Bool) (θ : ℝ) :
      B x side 0 θ = if side then r else l := by
    have hv (α : ℝ) : X₀ x side (if side then r else l, α) = if side then r else l := by
      have he := radialBoundaryJet_oneSidedBoundaryTaylorRepresentative (X x side) (n + 1)
        (if side then r else l) (k := 0) (Nat.zero_le _) α
      have he' : X₀ x side (if side then r else l, α) =
          X x side (if side then r else l, α) := he
      exact he'.trans (hXvalue x hx side α)
    exact angularFiberPullback_boundary (φ := φ x) hv θ
  let Y : E → PolarPoint → ℝ := fun x =>
    endpointFiberPullbackCoordinate n (φ x) (X₀ x) l r c d κX Mσ
  let KY := n04Realization_endpointFiberPullback_jointDirections hU hc n
    hlc hcd hdr hκX hMσ φ X₀ pair.2 KX
  let KI : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint =>
      positiveFiberRadialInverse (Y p.1) p.2) :=
    n04PositiveGeometry_endpointRadialInverseDirections hU n hlc hcd hdr hκX hMσ
      B hB hzero JB hfirst hcoeff
  exact ⟨pair.1, pair.2, KY, KI, JB,
    n04Realization_positiveFiberChart_jointDirections hU φ Y pair.1 KY,
    n04PositiveGeometry_fiberChartInverseDirections (φ := φ) (Y := Y) KI pair.2⟩

/-- The two transport towers are projections of the same retained
angular, radial and coefficient towers. -/
def n04PositiveGeometry_oneSidedTransportPairDirections
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation S.grading)
    (hU : IsOpen U) (hc : Convex ℝ U) (n : ℕ)
    {l r c d κφ κX M Mσ : ℝ} (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκX : 0 < κX) (hMσ : 0 ≤ Mσ)
    (ψ X : E → Bool → PolarPoint → ℝ)
    (hψ : ∀ x ∈ U, ∀ side (j : Fin (n + 2)), ContDiff ℝ ∞
      (fun θ => radialBoundaryJet (ψ x side) (if side then r else l) j θ -
        if (j : ℕ) = 0 then θ else 0))
    (hperiod : ∀ x ∈ U, ∀ side (j : Fin (n + 2)), Function.Periodic
      (fun θ => radialBoundaryJet (ψ x side) (if side then r else l) j θ -
        if (j : ℕ) = 0 then θ else 0) Real.pi)
    (Jψ : ∀ side (j : Fin (n + 2)) b θ, SmoothDirections U
      (fun x => iteratedDeriv b (fun η =>
        radialBoundaryJet (ψ x side) (if side then r else l) j η -
          if (j : ℕ) = 0 then η else 0) θ))
    (hbound : ∀ side j b, UniformScalarJetSeminormBounds (Jψ side j b))
    (JX : ∀ side (j : Fin (n + 2)), SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => radialBoundaryJet (X p.1 side)
        (if side then r else l) j p.2))
    (hXvalue : ∀ x ∈ U, ∀ side θ,
      X x side (if side then r else l, θ) = if side then r else l)
    (hpositive : ∀ x ∈ U, ∀ t θ, 0 < deriv (fun η =>
      wholeComponentEndpointAngle n
        (oneSidedEndpointRepresentative (n + 2) l r (ψ x))
        l r c d κφ M (t, η)) θ)
    (hfirst : ∀ x ∈ U, ∀ side θ, κX <
      n04PositiveGeometry_oneSidedFiberData n (ψ x) (X x) l r c d κφ M side 1 θ)
    (hcoeff : ∀ x ∈ U, ∀ side (j : Fin (n + 1)) θ,
      |n04PositiveGeometry_oneSidedFiberData n (ψ x) (X x)
        l r c d κφ M side (j + 1) θ| < Mσ) :
    SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint =>
      oneSidedWholeComponentTransport n (ψ p.1) (X p.1) l r c d κφ κX M Mσ p.2) ×
    SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint =>
      oneSidedWholeComponentTransportInverse n (ψ p.1) (X p.1) l r c d κφ κX M Mσ p.2) :=
  (n04PositiveGeometry_oneSidedTransportFactorDirections hS hT hD hγ hi
    hU hc n hlc hcd hdr hκX hMσ ψ X hψ hperiod Jψ hbound JX
    hXvalue hpositive hfirst hcoeff).2.2.2.2.2

end ContinuousFlexibility.Analysis
