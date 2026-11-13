import ContinuousFlexibility.Analysis.N04PositiveGeometryActualHeightDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryGaugeDirections

/-!
# Genuine towers of the physical reference height

The numerator and denominator are evaluated at the actual inverse
transport. The subsequent unit pullback uses the physical endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

def n04PositiveGeometry_controlledPhysicalHeight
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    (H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (z : AnnularState W.S × ℝ) (q : PolarPoint) : ℝ :=
  wholePositiveReferenceGaugeHeight (fun p => H₀ i p.1)
    (G.toN04PositiveGeometryControlData.σ z i) (G.toN04PositiveGeometryControlData.Q z i) q

def n04PositiveGeometry_controlledUnitHeight
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    (H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (z : AnnularState W.S × ℝ) (q : PolarPoint) : ℝ :=
  n04PositiveGeometry_controlledPhysicalHeight G H₀ i z
    (n04PositiveLeft i + (n04PositiveRight i - n04PositiveLeft i) * q.1, q.2)

def n04PositiveGeometry_actualControlledPhysicalHeight_joint
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) (hn : n ≤ 3)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H₀)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1) (hGb : G.base ≤ base) (hGε : ε ≤ G.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (hctx : ∀ m side,
      N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (JS : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y : (StateDirections W.S × ℝ) × PolarPoint =>
        G.toN04PositiveGeometryControlData.σ (liftSectorParameter W.S W.C y.1) i y.2)) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y : (StateDirections W.S × ℝ) × PolarPoint =>
        n04PositiveGeometry_controlledPhysicalHeight G H₀ i (liftSectorParameter W.S W.C y.1) y.2) := by
  letI : LocallyConvexSpace ℝ (StateDirections W.S × ℝ) :=
    (sectorPairGrading_withSeminorms W.S).toLocallyConvexSpace
  let JQ := n04PositiveGeometry_actualControlledHeight_joint G hn hb hε hεW hεone
    hGb hGε hflow hctx i true
  let Jden := n04PositiveGeometry_movingPointDirections JQ JS
  let Jnum := JS.comp_contDiff isOpen_univ (href i).1.height_smooth.contDiffOn
    (fun _ _ => mem_univ _)
  apply (Jnum.mul Jden).congrOn
  intro y _
  exact (div_eq_mul_inv _ _).symm.trans
    (wholePositiveReferenceGaugeHeight_eq _ _ _ _).symm

def n04PositiveGeometry_actualControlledUnitHeight_joint
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    (H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    {base : ℕ} {ε : ℝ} (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (J : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y : (StateDirections W.S × ℝ) × PolarPoint =>
        n04PositiveGeometry_controlledPhysicalHeight G H₀ i (liftSectorParameter W.S W.C y.1) y.2)) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ unitStrip)
      (fun y : (StateDirections W.S × ℝ) × PolarPoint =>
        n04PositiveGeometry_controlledUnitHeight G H₀ i (liftSectorParameter W.S W.C y.1) y.2) :=
  n04PositiveGeometry_unitPullbackDirections J (sectorNeighborhood_isOpen W.S base ε ε)
    (n04PositiveLeft i) (n04PositiveRight i)

end ContinuousFlexibility.Analysis
