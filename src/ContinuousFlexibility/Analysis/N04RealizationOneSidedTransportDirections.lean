import ContinuousFlexibility.Analysis.N04RealizationPositiveAngularInverse
import ContinuousFlexibility.Analysis.N04RealizationBoundaryTaylorDirections
import ContinuousFlexibility.Analysis.N04RealizationEndpointPullbackDirections
import ContinuousFlexibility.Analysis.OneSidedWholeComponentTransport

/-!
# The literal positive transport from its raw endpoint towers

All state dependence enters through the actual endpoint traces of the
two original source fields. Their finite representatives, the angular
inverse, the radial integral collars and the fixed-exit glues are built
on one unchanged state domain. The only positivity input is the spatial
angular positivity already certified by the finite collar construction.
There is no inverse tower or completed current-jet hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
  {U : Set E}

def n04Realization_oneSidedTransport_jointDirections
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation S.grading)
    (hU : IsOpen U) (hc : Convex ℝ U) (n m : ℕ)
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
    (hpositive : ∀ x ∈ U, ∀ t θ, 0 < deriv (fun η =>
      wholeComponentEndpointAngle n
        (oneSidedEndpointRepresentative (n + 2) l r (ψ x))
        l r c d κφ M (t, η)) θ) :
    SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint =>
      oneSidedWholeComponentTransport n (ψ p.1) (X p.1)
        l r c d κφ κX M Mσ p.2) := by
  let Ψ : E → Bool → PolarPoint → ℝ := fun x =>
    oneSidedEndpointRepresentative (n + 2) l r (ψ x)
  let A : E → Bool → ℕ → ℝ → ℝ := fun x => rawEndpointAngularData l r (Ψ x)
  have hcoeff (x : E) (side : Bool) (j : Fin (n + 2)) :
      (fun θ => A x side j θ - if (j : ℕ) = 0 then θ else 0) =
        (fun θ => radialBoundaryJet (ψ x side) (if side then r else l) j θ -
          if (j : ℕ) = 0 then θ else 0) := by
    funext θ
    change radialBoundaryJet
      (oneSidedBoundaryTaylorRepresentative (n + 2)
        (if side then r else l) (ψ x side)) (if side then r else l) j θ - _ = _
    rw [radialBoundaryJet_oneSidedBoundaryTaylorRepresentative _ _ _ (by omega)]
  let JA : ∀ side (j : Fin (n + 2)) b θ, SmoothDirections U
      (fun x => iteratedDeriv b
        (fun η => A x side j η - if (j : ℕ) = 0 then η else 0) θ) :=
    fun side j b θ => (Jψ side j b θ).congrOn (fun x _ => by rw [hcoeff x side j])
  let φ : E → PolarPoint → ℝ := fun x =>
    wholeComponentEndpointAngle n (Ψ x) l r c d κφ M
  let pair := n04Realization_positiveAngularTaylor_jointDirections hS hT hD hγ hi
    hU hc (n + 1) m l r (endpointAngularWidth (n + 1) l r c d κφ M) A
    (fun x hx side j => by rw [hcoeff x side j]; exact hψ x hx side j)
    (fun x hx side j => by rw [hcoeff x side j]; exact hperiod x hx side j)
    JA (fun side j b => hbound side j b) hpositive
  let X₀ : E → Bool → PolarPoint → ℝ := fun x =>
    oneSidedEndpointRepresentative (n + 1) l r (X x)
  let KX : ∀ side, SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => X₀ p.1 side p.2) := fun side =>
    n04Realization_oneSidedRepresentative_jointDirections hU (n + 1)
      (if side then r else l) (fun x => X x side) (JX side)
  let Y : E → PolarPoint → ℝ := fun x =>
    endpointFiberPullbackCoordinate n (φ x) (X₀ x) l r c d κX Mσ
  let KY : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => Y p.1 p.2) :=
    n04Realization_endpointFiberPullback_jointDirections hU hc n hlc hcd hdr
      hκX hMσ φ X₀ pair.2 KX
  exact n04Realization_positiveFiberChart_jointDirections hU φ Y pair.1 KY

end ContinuousFlexibility.Analysis
