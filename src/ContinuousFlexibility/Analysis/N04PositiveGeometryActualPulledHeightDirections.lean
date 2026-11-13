import ContinuousFlexibility.Analysis.N04PositiveGeometryActualHeightDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryGaugeDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledPulledHeight
import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity

/-!
# The actual pulled height from the fixed reference inverse

The relative inverse cancels the relative transport at every point.
Only the genuine reciprocal of `Q` is composed with the fixed reference
inverse; no joint transport tower is needed for the pulled height.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

def n04PositiveGeometry_controlledPulledHeight
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (z : AnnularState W.S × ℝ) (q : PolarPoint) : ℝ :=
  wholePositiveReferenceGaugeHeight (fun p => H₀ i p.1)
    (G.toN04PositiveGeometryControlData.σ z i) (G.toN04PositiveGeometryControlData.Q z i)
    (wholePositiveReferenceGaugeInverse (G.toN04PositiveGeometryControlData.τ z i)
      (positiveReferenceCylinderInverse (Y i)) q)

theorem n04PositiveGeometry_controlledPulledHeight_eq
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1) (q : PolarPoint) :
    n04PositiveGeometry_controlledPulledHeight G Y H₀ i z q =
      H₀ i (Function.invFun (Y i) q.1) *
        (G.toN04PositiveGeometryControlData.Q z i (positiveReferenceCylinderInverse (Y i) q))⁻¹ := by
  rw [n04PositiveGeometry_controlledPulledHeight, wholePositiveReferenceGaugeHeight_eq]
  change H₀ i (G.toN04PositiveGeometryControlData.σ z i
      (G.toN04PositiveGeometryControlData.τ z i (positiveReferenceCylinderInverse (Y i) q))).1 /
      G.toN04PositiveGeometryControlData.Q z i (G.toN04PositiveGeometryControlData.σ z i
        (G.toN04PositiveGeometryControlData.τ z i (positiveReferenceCylinderInverse (Y i) q))) = _
  rw [(G.matching z hz hs i).geometry.left_inverse]
  exact div_eq_mul_inv _ _

def n04PositiveGeometry_actualControlledPulledHeight_joint
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) (hn : n ≤ 3)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H₀)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1) (hGb : G.base ≤ base) (hGε : ε ≤ G.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (hctx : ∀ m side,
      N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y : (StateDirections W.S × ℝ) × PolarPoint =>
        n04PositiveGeometry_controlledPulledHeight G Y H₀ i (liftSectorParameter W.S W.C y.1) y.2) := by
  letI : LocallyConvexSpace ℝ (StateDirections W.S × ℝ) :=
    (sectorPairGrading_withSeminorms W.S).toLocallyConvexSpace
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  have hU := sectorNeighborhood_isOpen W.S base ε ε
  let JQ := n04PositiveGeometry_actualControlledHeight_joint G hn hb hε hεW hεone
    hGb hGε hflow hctx i true
  let P : ((StateDirections W.S × ℝ) × PolarPoint) →L[ℝ] PolarPoint :=
    ContinuousLinearMap.snd ℝ (StateDirections W.S × ℝ) PolarPoint
  let JP := (smoothDirectionsLinear P).restrict (hU.prod isOpen_univ) (subset_univ _)
  let Jχ := JP.comp_contDiff isOpen_univ (href i).1.inverse_smooth.contDiffOn
    (fun _ _ => mem_univ _)
  let Jnum := Jχ.comp_contDiff isOpen_univ (href i).1.height_smooth.contDiffOn
    (fun _ _ => mem_univ _)
  let Jden := n04PositiveGeometry_movingPointDirections JQ Jχ
  apply (Jnum.mul Jden).congr
  intro y hy
  exact (n04PositiveGeometry_controlledPulledHeight_eq G Y H₀ i
    (stateNeighborhood_mono W.S W.C hGb hGε
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) hy.1 le_rfl))
    (hN.2.2.1.liftSectorParameter_sector y.1) y.2).symm

def n04PositiveGeometry_actualControlledPulledHeight_mixedJetRegularity
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) (hn : n ≤ 3)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H₀)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1) (hGb : G.base ≤ base) (hGε : ε ≤ G.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (hctx : ∀ m side,
      N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
    MixedJetRegularity (sectorNeighborhood W.S base ε ε) univ
      (fun x p => n04PositiveGeometry_controlledPulledHeight G Y H₀ i
        (liftSectorParameter W.S W.C x) p) :=
  n04Realization_jointMixedRegularity
    (n04PositiveGeometry_actualControlledPulledHeight_joint G hn Y H₀ href
      hb hε hεW hεone hGb hGε hflow hctx i)
    (sectorNeighborhood_isOpen W.S base ε ε) isOpen_univ
    ((sectorNeighborhood_convex W.S base ε ε).prod convex_univ)

end ContinuousFlexibility.Analysis
