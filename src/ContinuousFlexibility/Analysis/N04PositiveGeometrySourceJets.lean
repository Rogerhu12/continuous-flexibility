import ContinuousFlexibility.Analysis.N04PositiveGeometryStoredInverseJets
import ContinuousFlexibility.Analysis.N04PositiveGeometryReferenceForwardJets
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryComposition
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryTraceOperations

/-!
# Full finite jets of the retained positive endpoint source

The source is the original current inverse composed with the original
reference chart. Its genuine positive spatial jets use the already
constructed full inverse jets and fixed reference jets. The actual
unwrapped value is never an input to this construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04SourceJetsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

def n04PositiveGeometry_sourceJet
    {D : ReferenceData} (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (src : N04PositiveEndpointSource C i side) (K : CanonicalData S)
    (n : ℕ) (y : (StateDirections S × ℝ) × ℝ) : PolarPoint [×n]→L[ℝ] PolarPoint :=
  iteratedFDeriv ℝ n (n04PositiveSourceMap src K (liftSectorParameter S C y.1))
    (n04PositiveEndpoint i side, y.2)

theorem n04PositiveGeometry_sourceEndpoint_eq_root
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (src : N04PositiveEndpointSource C i side) {m : ℕ} (hm : src.val = some m) :
    n01ComponentRoot C m (!side) = n04PositiveEndpoint i side := by
  have he : n04PositiveEndpoint i side = (if side then C.left m else C.right m) := by
    simpa only [hm] using src.property
  cases side <;> exact he.symm

theorem n04PositiveGeometry_sourceMap_eq_rootComposite
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (src : N04PositiveEndpointSource C i side) (K : CanonicalData S)
    {m : ℕ} (hm : src.val = some m) (z : AnnularState S × ℝ) :
    n04PositiveSourceMap src K z =
      K.inverseChart z (if !side then (K.cutPair m).2 else (K.cutPair m).1) ∘
        K.chart (C.referenceState, 0)
          (if !side then (K.cutPair m).2 else (K.cutPair m).1) := by
  funext p
  cases side <;> simp only [n04PositiveSourceMap, hm, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, if_false, if_true, canonicalCurrentPoint, Function.comp_apply]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {Kcur : CanonicalData S}
  {base loss m : ℕ} {ε : ℝ}
  {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}

theorem n04PositiveGeometry_sourceComposite_regularities
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hA : CanonicalGeometry D S C Kcur base ε)
    (src : N04PositiveEndpointSource C i side) (hm : src.val = some m)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m (!side))
    {y : (StateDirections S × ℝ) × ℝ} (hy : y ∈ sectorNeighborhood S base ε ε ×ˢ univ) :
    let k := if !side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1
    let f := Kcur.inverseChart (liftSectorParameter S C y.1) k
    let g := Kcur.chart (C.referenceState, 0) k
    let q : PolarPoint := (n04PositiveEndpoint i side, y.2)
    g q = (0, y.2) ∧ ContDiffAt ℝ ∞ f (g q) ∧ ContDiffAt ℝ ∞ g q := by
  have hrad := n04PositiveGeometry_sourceEndpoint_eq_root src hm
  have he := n04PositiveGeometry_referenceRoot_chart_eq hT hS hN hflow hctx y.2
  rw [hrad] at he
  have hreg := n04PositiveGeometry_storedInverse_regularities hT hS hN hflow hA hctx hy
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  have hmodel := (hc.2.2.2.2 (C.referenceState, 0)
    hN.reference_mem_stateNeighborhood hN.2.2.1.stateSector).2.choose_spec.2
  have href := hA.boundary (C.referenceState, 0) hN.reference_mem_stateNeighborhood
    hN.2.2.1.stateSector (if !side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1)
  refine ⟨he, ?_, ?_⟩
  · rw [he]
    exact hreg.2.1
  · simpa only [hrad] using (href.2.2.2.2.1 _ (hmodel y.2).1).1

def n04PositiveGeometry_sourceJet_directions
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hA : CanonicalGeometry D S C Kcur base ε)
    (src : N04PositiveEndpointSource C i side) (hm : src.val = some m)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m (!side))
    (hr : n04PositiveEndpoint i side ∈ radialCore D)
    (hroot : deriv D.w (n04PositiveEndpoint i side) = 0)
    (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_sourceJet S C src Kcur n) := by
  have hrad := n04PositiveGeometry_sourceEndpoint_eq_root src hm
  have hr' : n01ComponentRoot C m (!side) ∈ radialCore D := hrad.symm ▸ hr
  have hroot' : deriv D.w (n01ComponentRoot C m (!side)) = 0 := hrad.symm ▸ hroot
  let F := fun y : (StateDirections S × ℝ) × ℝ =>
    Kcur.inverseChart (liftSectorParameter S C y.1)
      (if !side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1)
  let G := fun _y : (StateDirections S × ℝ) × ℝ =>
    Kcur.chart (C.referenceState, 0)
      (if !side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1)
  let q := fun y : (StateDirections S × ℝ) × ℝ => (n04PositiveEndpoint i side, y.2)
  have hreg := fun y hy => n04PositiveGeometry_sourceComposite_regularities
    hT hS hN hflow hA src hm hctx (y := y) hy
  let JF : ∀ j, 1 ≤ j → j ≤ n → SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ univ)
        (fun y => iteratedFDeriv ℝ j (F y) (G y (q y))) := fun j hj hjn =>
    (n04PositiveGeometry_storedInverseJet_joint hT hS hN hεone hflow hA hctx
      hr' hroot' j hj (hjn.trans hn4)).congr (fun y hy =>
        congrArg (iteratedFDeriv ℝ j (F y)) (hreg y hy).1.symm)
  let JG : ∀ j, 1 ≤ j → j ≤ n → ∀ v : Fin j → PolarPoint, SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ univ)
        (fun y => iteratedFDeriv ℝ j (G y) (q y) v) := fun j hj hjn v =>
    (n04PositiveGeometry_boundaryFixedEvaluation_directions
      (n04PositiveGeometry_referenceForwardJet_joint hT hS hN hε hεone hflow hctx
        hr' hroot' j hj (hjn.trans hn4)) v).congr
      (fun _ _ => by rw [n04PositiveGeometry_referenceForwardJet, hrad])
  apply n04PositiveGeometry_planeBasis_directions n
    (n04PositiveGeometry_sourceJet S C src Kcur n)
  intro w
  exact (n04PositiveGeometry_boundaryComposition_directions n (by omega)
    (sectorNeighborhood_isOpen S base ε ε) F G q
    (fun y hy => (hreg y hy).2.1) (fun y hy => (hreg y hy).2.2) JF JG
    (fun a => cylinderBasisVector (w a))).congr (fun y _ => by
      unfold n04PositiveGeometry_sourceJet
      rw [n04PositiveGeometry_sourceMap_eq_rootComposite src Kcur hm])

/-- The sampled atlas supplies every geometric input; this is a producer
for the actual stored source, with no assumed source jet tower. -/
def n04PositiveGeometry_sourceJet_joint
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (m : ℕ) (hm : (X.src i side).val = some m)
    (hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side))
    (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (n04PositiveGeometry_sourceJet W.S W.C (X.src i side) (W.A X.e₀) n) := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  have hA : CanonicalGeometry W.D W.S W.C (W.A X.e₀) base ε :=
    n04PartA_restrict (n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field X.e₀) hb hεW
  exact n04PositiveGeometry_sourceJet_directions W.hT W.hS hN hε hεone hflow hA
    (X.src i side) hm hctx (W.roots i side).1 (W.roots i side).2.1 n hn hn4

def n04PositiveGeometry_sourceJet_eval_joint
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (m : ℕ) (hm : (X.src i side).val = some m)
    (hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side))
    (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) (v : Fin n → PolarPoint) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y : (StateDirections W.S × ℝ) × ℝ => iteratedFDeriv ℝ n
        (n04PositiveSourceMap (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1))
        (n04PositiveEndpoint i side, y.2) v) :=
  n04PositiveGeometry_boundaryFixedEvaluation_directions
    (n04PositiveGeometry_sourceJet_joint W X hb hε hεW hεone hflow i side m hm hctx n hn hn4) v

end ContinuousFlexibility.Analysis
