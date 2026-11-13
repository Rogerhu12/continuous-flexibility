import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceHeightJets
import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceJets
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledHeightJoint
import ContinuousFlexibility.Analysis.N04PositiveGeometryRightSource

/-!
# Actual source and interpolation height towers

Every source-map derivative is now produced from the retained atlas.
The finite source-height ratio and its reciprocal therefore have genuine
joint radial traces without any assumed endpoint tower. These traces
feed the original controlled interpolation and its existing mixed jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

def n04PositiveGeometry_sourceHeightChoice_joint
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (hctx : ∀ m side,
      N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (n : ℕ) (hn : n ≤ 3) (inv : Bool) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y : (StateDirections W.S × ℝ) × ℝ => radialBoundaryJet (fun p => if inv then
        (n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1) p)⁻¹
        else n04PositiveSourceHeight (X.src i side) (W.A X.e₀)
          (liftSectorParameter W.S W.C y.1) p) (n04PositiveEndpoint i side) n y.2) := by
  let sourceData := n04PositiveGeometry_source_some W X i side
  let m := sourceData.choose
  have hm : (X.src i side).val = some m := sourceData.choose_spec
  exact n04PositiveGeometry_sourceHeight_joint_of_sourceJets W X hb hε hεW hεone hflow
    i side m hm (hctx m (!side)) n hn
    (fun j hj hjn v => n04PositiveGeometry_sourceJet_eval_joint W X hb hε hεW hεone hflow
      i side m hm (hctx m (!side)) j hj (by omega) v) inv

def n04PositiveGeometry_sourceHeight_joint
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (hctx : ∀ m side,
      N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (n : ℕ) (hn : n ≤ 3) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y : (StateDirections W.S × ℝ) × ℝ => radialBoundaryJet
        (n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1))
        (n04PositiveEndpoint i side) n y.2) :=
  (n04PositiveGeometry_sourceHeightChoice_joint W X hb hε hεW hεone hflow hctx
    i side n hn false).congr (fun _ _ => rfl)

def n04PositiveGeometry_actualControlledHeight_joint
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) (hn : n ≤ 3)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1) (hGb : G.base ≤ base) (hGε : ε ≤ G.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (hctx : ∀ m side,
      N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (inv : Bool) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y : (StateDirections W.S × ℝ) × PolarPoint => if inv then
        (G.toN04PositiveGeometryControlData.Q (liftSectorParameter W.S W.C y.1) i y.2)⁻¹
        else G.toN04PositiveGeometryControlData.Q (liftSectorParameter W.S W.C y.1) i y.2) := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  exact n04PositiveGeometry_controlledHeight_jointDirections G
    (sectorNeighborhood_isOpen W.S base ε ε) (liftSectorParameter W.S W.C)
    (fun x hx => stateNeighborhood_mono W.S W.C hGb hGε
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) hx le_rfl))
    (fun x _ => hN.2.2.1.liftSectorParameter_sector x) i
    (fun side j hj => n04PositiveGeometry_sourceHeight_joint W X hb hε hεW hεone hflow hctx
      i side j (hj.trans hn)) inv

/-- The independently established mixed and quantitative construction
uses precisely the same actual raw height traces. -/
def n04PositiveGeometry_actualControlledHeight_mixedJetRegularity
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) (hn : n ≤ 3)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1) (hGb : G.base ≤ base) (hGε : ε ≤ G.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (hctx : ∀ m side,
      N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (inv : Bool) :
    MixedJetRegularity (sectorNeighborhood W.S base ε ε) univ
      (fun x q => if inv then
        (G.toN04PositiveGeometryControlData.Q (liftSectorParameter W.S W.C x) i q)⁻¹
        else G.toN04PositiveGeometryControlData.Q (liftSectorParameter W.S W.C x) i q) := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  exact n04PositiveGeometry_controlledHeight_jointRaw_mixedJetRegularity G
    (sectorNeighborhood_isOpen W.S base ε ε) (liftSectorParameter W.S W.C)
    (fun x hx => stateNeighborhood_mono W.S W.C hGb hGε
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) hx le_rfl))
    (fun x _ => hN.2.2.1.liftSectorParameter_sector x) i
    (fun side j hj => n04PositiveGeometry_sourceHeight_joint W X hb hε hεW hεone hflow hctx
      i side j (hj.trans hn)) inv

end ContinuousFlexibility.Analysis
