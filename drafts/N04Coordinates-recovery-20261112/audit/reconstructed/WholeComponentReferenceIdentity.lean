import ContinuousFlexibility.Analysis.OneSidedWholeComponentTransport
import ContinuousFlexibility.Analysis.TaylorReferenceIdentity
import ContinuousFlexibility.Analysis.PositiveReferenceIdentity

/-!
# Exact reference identity of the displayed whole-component transport

The reference germs determine the actual finite Taylor representatives.
Their radial integral has unit physical slope and its prescribed mass
is the interval width. Both pointwise inverses are consequently the
identity as well. No estimate on an unspecified transport is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveReferenceCollarCoordinate_reference_identity
    (n : ℕ) {a b δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < b - a) (root : Bool) :
    positiveReferenceCollarCoordinate n a b δ a (b - a) root
      (radialBoundaryJet (Prod.fst : PolarPoint → ℝ) (if root then b else a))
      Prod.fst = (Prod.fst : PolarPoint → ℝ) := by
  have hfield : positiveReferenceCollarField n a b root
      (radialBoundaryJet (Prod.fst : PolarPoint → ℝ) (if root then b else a))
      Prod.fst = (fun _ => (Prod.fst : PolarPoint → ℝ)) := by
    funext side
    by_cases he : side = root
    · subst side
      simp only [positiveReferenceCollarField, if_pos rfl, boundaryTaylorPolynomial_fst]
    · simp only [positiveReferenceCollarField, if_neg he]
  have hslope : (fun side => radialPartial (positiveReferenceCollarField n a b root
      (radialBoundaryJet (Prod.fst : PolarPoint → ℝ) (if root then b else a))
      Prod.fst side)) = (fun _ _ => (1 : ℝ)) := by
    rw [hfield]
    funext side p
    exact radialPartial_fst
  rw [positiveReferenceCollarCoordinate, hslope]
  exact parameterizedPositiveReferenceCoordinate_one_eq_fst hδ hgap

theorem endpointFiberInterpolation_reference_identity
    (n : ℕ) {l r c d : ℝ} {η : Bool → ℝ}
    (hη : ∀ side, 0 < η side)
    (hgap : ∀ side, 2 * η side <
      (if side then r else c) - (if side then d else l)) :
    endpointFiberInterpolation n l r c d η
      (fun side => radialBoundaryJet (Prod.fst : PolarPoint → ℝ)
        (if side then r else l)) = (Prod.fst : PolarPoint → ℝ) := by
  have hcollar (side : Bool) : endpointFiberCollar n l r c d η
      (fun t => radialBoundaryJet (Prod.fst : PolarPoint → ℝ)
        (if t then r else l)) side = (Prod.fst : PolarPoint → ℝ) := by
    cases side with
    | false => exact positiveReferenceCollarCoordinate_reference_identity n
        (hη false) (hgap false) false
    | true => exact positiveReferenceCollarCoordinate_reference_identity n
        (hη true) (hgap true) true
  funext p
  simp only [endpointFiberInterpolation, twoEndpointFiberCoordinate, hcollar,
    radialGermGlue, ite_self]

theorem positiveFiberChartInverse_projections :
    positiveFiberChartInverse (Prod.snd : PolarPoint → ℝ) Prod.fst =
      (id : PolarPoint → PolarPoint) := by
  funext p
  apply Prod.ext
  · change Function.invFun (id : ℝ → ℝ) p.1 = p.1
    exact Function.leftInverse_invFun Function.injective_id p.1
  · change Function.invFun (id : ℝ → ℝ) p.2 = p.2
    exact Function.leftInverse_invFun Function.injective_id p.2

theorem wholeComponentEndpointTransport_reference_identity
    (n : ℕ) {l r c d κφ κX M Mσ : ℝ}
    (hη : ∀ side, 0 < endpointFiberWidths n l r c d κX Mσ side)
    (hgap : ∀ side, 2 * endpointFiberWidths n l r c d κX Mσ side <
      (if side then r else c) - (if side then d else l)) :
    wholeComponentEndpointTransport n (fun _ => Prod.snd) (fun _ => Prod.fst)
      l r c d κφ κX M Mσ = id ∧
    wholeComponentEndpointTransportInverse n (fun _ => Prod.snd) (fun _ => Prod.fst)
      l r c d κφ κX M Mσ = id := by
  have hangle : wholeComponentEndpointAngle n (fun _ => Prod.snd)
      l r c d κφ M = (Prod.snd : PolarPoint → ℝ) := by
    funext p
    simp only [wholeComponentEndpointAngle, rawEndpointAngularData,
      positiveAngularTaylorInterpolation, positiveAngularTaylorPatch,
      Bool.false_eq_true, ite_false, ite_true, boundaryTaylorPolynomial_snd]
    ring
  have hY : endpointFiberPullbackCoordinate n (Prod.snd : PolarPoint → ℝ)
      (fun _ => Prod.fst) l r c d κX Mσ = (Prod.fst : PolarPoint → ℝ) := by
    change endpointFiberInterpolation n l r c d (endpointFiberWidths n l r c d κX Mσ)
      (fun side => radialBoundaryJet (Prod.fst : PolarPoint → ℝ)
        (if side then r else l)) = (Prod.fst : PolarPoint → ℝ)
    exact endpointFiberInterpolation_reference_identity n hη hgap
  simp only [wholeComponentEndpointTransport, wholeComponentEndpointTransportInverse,
    hangle, hY]
  exact ⟨funext (fun p => Prod.eta p), positiveFiberChartInverse_projections⟩

theorem oneSidedWholeComponentTransport_reference_identity
    (n : ℕ) {ψ X : Bool → PolarPoint → ℝ} {l r c d κφ κX M Mσ : ℝ}
    (hψ : ∀ side θ, ψ side =ᶠ[𝓝 (if side then r else l, θ)]
      (Prod.snd : PolarPoint → ℝ))
    (hX : ∀ side θ, X side =ᶠ[𝓝 (if side then r else l, θ)]
      (Prod.fst : PolarPoint → ℝ))
    (hη : ∀ side, 0 < endpointFiberWidths n l r c d κX Mσ side)
    (hgap : ∀ side, 2 * endpointFiberWidths n l r c d κX Mσ side <
      (if side then r else c) - (if side then d else l)) :
    oneSidedWholeComponentTransport n ψ X l r c d κφ κX M Mσ = id ∧
    oneSidedWholeComponentTransportInverse n ψ X l r c d κφ κX M Mσ = id := by
  have hψrep : oneSidedEndpointRepresentative (n + 2) l r ψ =
      (fun _ => (Prod.snd : PolarPoint → ℝ)) := by
    funext side
    exact oneSidedBoundaryTaylorRepresentative_eq_snd (hψ side) (n + 2)
  have hXrep : oneSidedEndpointRepresentative (n + 1) l r X =
      (fun _ => (Prod.fst : PolarPoint → ℝ)) := by
    funext side
    exact oneSidedBoundaryTaylorRepresentative_eq_fst (hX side) n
  simpa only [oneSidedWholeComponentTransport, oneSidedWholeComponentTransportInverse,
    hψrep, hXrep] using
    (wholeComponentEndpointTransport_reference_identity
      (κφ := κφ) (M := M) n hη hgap)

end ContinuousFlexibility.Analysis

