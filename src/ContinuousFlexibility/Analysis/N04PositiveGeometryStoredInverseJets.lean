import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInverseDifferentialDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryStoredForwardJets
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryInversePlanePrefix

/-!
# Genuine finite jets of the original canonical inverse

The original chart and inverse satisfy genuine inverse germs at the
canonical zero edge. The actual triangular differential and forward
jets at the inverse root label construct its full jets through order four.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

local instance n04StoredInverseJetsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

def n04PositiveGeometry_storedInverseDifferential
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (m : ℕ) (side : Bool) (y : (StateDirections S × ℝ) × ℝ) : PolarPoint →L[ℝ] PolarPoint :=
  fderiv ℝ (K.inverseChart (liftSectorParameter S C y.1)
    (if side then (K.cutPair m).2 else (K.cutPair m).1)) (0, y.2)

def n04PositiveGeometry_storedInverseJet
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (m : ℕ) (side : Bool) (n : ℕ) (y : (StateDirections S × ℝ) × ℝ) :
    PolarPoint [×n]→L[ℝ] PolarPoint :=
  iteratedFDeriv ℝ n (K.inverseChart (liftSectorParameter S C y.1)
    (if side then (K.cutPair m).2 else (K.cutPair m).1)) (0, y.2)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {Kcur : CanonicalData S}
  {base loss m : ℕ} {ε : ℝ} {side : Bool}

theorem n04PositiveGeometry_storedInverseBoundary_data
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hA : CanonicalGeometry D S C Kcur base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    {y : (StateDirections S × ℝ) × ℝ} (hy : y ∈ sectorNeighborhood S base ε ε ×ˢ univ) :
    let z := liftSectorParameter S C y.1
    let i := if side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1
    let η := Function.invFun (n01RootLabel S C z m side) y.2
    Kcur.inverseChart z i (0, y.2) = (n01ComponentRoot C m side, η) ∧
      ((0, y.2) : PolarPoint) ∈ canonicalClosed S Kcur i ∧
      n04PositiveGeometry_storedInverseDifferential S C Kcur m side y =
        n04PositiveGeometry_rootInverseDifferential D S C hctx.choose m side y := by
  let z := liftSectorParameter S C y.1
  let r := n01ComponentRoot C m side
  let i := if side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1
  let β := n01RootLabel S C z m side
  let η := Function.invFun β y.2
  have hz := liftSectorParameter_mem_stateNeighborhood (C := C) hy.1 le_rfl
  have hs := hN.2.2.1.liftSectorParameter_sector y.1
  let g := hctx.choose
  let hR := hctx.choose_spec.choose_spec.choose
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  let data := hc.2.2.2.2 z hz hs
  let Θ := data.2.choose
  have hΘ := data.2.choose_spec.1
  have hmodel := data.2.choose_spec.2
  have hβ : β η = y.2 := rightInverse_invFun_of_deriv_lower_bound
    (by norm_num : (0 : ℝ) < 1 / 4)
    (fun ν => (n01RootLabel_deriv_mem_quarter_four hN hflow hz hs m side ν).1) y.2
  have hcols := n04PositiveGeometry_actual_root_firstColumns hT hS hN hflow hy.1
    m side g hc.1 hR data.1 hc.2.2.2.1.ne' Θ hΘ hmodel η
  have hv : Kcur.chart z i (r, η) = (0, y.2) := by
    have h : Kcur.chart z i (r, η) = (0, β η) := hcols.1
    simpa only [hβ] using h
  have hr : (r, η) ∈ physicalPieceClosed S Kcur z i := (hmodel η).1
  have hclosed := hA.boundary z hz hs i
  refine ⟨?_, ?_, ?_⟩
  · exact (congrArg (Kcur.inverseChart z i) hv.symm).trans
      (hclosed.2.2.1 _ hr)
  · exact (congrArg (fun q : PolarPoint => q ∈ canonicalClosed S Kcur i) hv).mp
      (hclosed.1 hr)
  · exact n04PositiveGeometry_actual_rootInverse_fderiv_eq hT hS hN hflow hA hy.1
      m side g hc.1 hR data.1 hc.2.2.2.1.ne' Θ hΘ hmodel y.2

theorem n04PositiveGeometry_storedInverse_regularities
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hA : CanonicalGeometry D S C Kcur base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    {y : (StateDirections S × ℝ) × ℝ} (hy : y ∈ sectorNeighborhood S base ε ε ×ˢ univ) :
    let z := liftSectorParameter S C y.1
    let i := if side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1
    let f := Kcur.chart z i
    let g := Kcur.inverseChart z i
    let q : PolarPoint := (0, y.2)
    ContDiffAt ℝ ∞ f (g q) ∧ ContDiffAt ℝ ∞ g q ∧
      f ∘ g =ᶠ[𝓝 q] (id : PolarPoint → PolarPoint) ∧
      (n04PositiveGeometry_storedInverseDifferential S C Kcur m side y).comp
        (fderiv ℝ f (g q)) = ContinuousLinearMap.id ℝ PolarPoint := by
  have hz := liftSectorParameter_mem_stateNeighborhood (C := C) hy.1 le_rfl
  have hs := hN.2.2.1.liftSectorParameter_sector y.1
  have hq := (n04PositiveGeometry_storedInverseBoundary_data hT hS hN hflow hA hctx hy).2.1
  let i := if side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1
  have hclosed := hA.boundary (liftSectorParameter S C y.1) hz hs i
  exact ⟨(hclosed.2.2.2.2.1 _ (hclosed.2.1 hq)).1,
    n04b_inverseChart_contDiffAt_closed hA hz hs i hq,
    (canonicalClosed_inverse_germs hA hz hs i hq).2,
    (canonicalClosed_inverse_fderiv hA hz hs i hq).1⟩

def n04PositiveGeometry_storedInverseDifferential_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hA : CanonicalGeometry D S C Kcur base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_storedInverseDifferential S C Kcur m side) := by
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  let J := n04PositiveGeometry_rootInverseDifferential_joint hT hS hN hε hflow
    hctx.choose hc.1 hc.2.1 m side hr hroot hctx.choose_spec.choose_spec.choose
    (fun y hy => (hc.2.2.2.2 (liftSectorParameter S C y)
      (liftSectorParameter_mem_stateNeighborhood (C := C) hy le_rfl)
      (hN.2.2.1.liftSectorParameter_sector y)).1)
  exact J.congr (fun y hy =>
    (n04PositiveGeometry_storedInverseBoundary_data hT hS hN hflow hA hctx hy).2.2.symm)

def n04PositiveGeometry_storedForward_atInverse_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hA : CanonicalGeometry D S C Kcur base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun y : (StateDirections S × ℝ) × ℝ =>
        let z := liftSectorParameter S C y.1
        let i := if side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1
        iteratedFDeriv ℝ n (Kcur.chart z i) (Kcur.inverseChart z i (0, y.2))) := by
  letI : LocallyConvexSpace ℝ (StateDirections S × ℝ) :=
    (sectorPairGrading_withSeminorms S).toLocallyConvexSpace
  let JF := n04PositiveGeometry_storedForwardJet_joint hT hS hN hε hflow hctx hr hroot n hn hn4
  let Jα := n04Realization_rootLabel_inverseJointDirections hT hS hN m side
  apply (n04PositiveGeometry_boundaryMoving_directions JF Jα).congr
  intro y hy
  exact congrArg (iteratedFDeriv ℝ n (Kcur.chart (liftSectorParameter S C y.1)
    (if side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1)))
    (n04PositiveGeometry_storedInverseBoundary_data hT hS hN hflow hA hctx hy).1.symm

/-- No parameter smoothness of the inverse is an input. The finite
formula constructs the genuine tower of its original multilinear jet. -/
def n04PositiveGeometry_storedInverseJet_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hA : CanonicalGeometry D S C Kcur base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_storedInverseJet S C Kcur m side n) := by
  let F := fun y : (StateDirections S × ℝ) × ℝ => Kcur.chart (liftSectorParameter S C y.1)
    (if side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1)
  let G := fun y : (StateDirections S × ℝ) × ℝ => Kcur.inverseChart (liftSectorParameter S C y.1)
    (if side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1)
  let q := fun y : (StateDirections S × ℝ) × ℝ => ((0, y.2) : PolarPoint)
  let L := n04PositiveGeometry_storedInverseDifferential S C Kcur m side
  have hreg := fun y hy => n04PositiveGeometry_storedInverse_regularities hT hS hN hflow hA hctx
    (y := y) hy
  let JL := n04PositiveGeometry_storedInverseDifferential_joint hT hS hN hε hflow hA hctx hr hroot
  let JF : ∀ j, 2 ≤ j → j ≤ 4 →
      SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
        (fun y => iteratedFDeriv ℝ j (F y) (G y (q y))) :=
    fun j hj hj4 => n04PositiveGeometry_storedForward_atInverse_joint hT hS hN hε hflow
      hA hctx hr hroot j (by omega) hj4
  apply n04PositiveGeometry_planeBasis_directions n
    (n04PositiveGeometry_storedInverseJet S C Kcur m side n)
  intro w
  exact n04Realization_inverse_finiteJet_directions
    (f := F) (g := G) (x := q) (L := L)
    ((sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ)
    (fun y hy => (hreg y hy).1) (fun y hy => (hreg y hy).2.1)
    (fun y hy => (hreg y hy).2.2.1) (fun y hy => (hreg y hy).2.2.2) JL
    4 JF n hn hn4 (fun i => cylinderBasisVector (w i))

end ContinuousFlexibility.Analysis
