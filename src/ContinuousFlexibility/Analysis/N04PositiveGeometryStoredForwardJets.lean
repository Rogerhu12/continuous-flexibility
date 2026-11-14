module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsForwardModel
public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledHeightTrace

/-!
# Genuine full jets of the original root chart

One model at each state identifies every angle and every spatial order.
Its finite trace formulas construct the actual chart's parameter tower.
The fixed inverse radial linear map restores the original physical
coordinate and preserves the complete ordered-word budget.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private theorem forwardBasis_congr
    {O O' : ℕ → ℝ → ℝ} {E E' : Fin 8 → ℝ → ℝ} {B B' : ℝ → ℝ}
    (κ : ℝ) (a b : ℕ) (ha : a ≤ 4)
    (hO : ∀ j, j ≤ 3 → O j = O' j) (hE : ∀ j, E j = E' j) (hB : B = B') :
    n04PositiveGeometry_forwardBasisValue κ O E B a b =
      n04PositiveGeometry_forwardBasisValue κ O' E' B' a b := by
  by_cases ha0 : a = 0
  · simp only [n04PositiveGeometry_forwardBasisValue, if_pos ha0, hB]
  · have hj : a - 1 ≤ 3 := by omega
    simp only [n04PositiveGeometry_forwardBasisValue, if_neg ha0, dif_pos ha,
      hO (a - 1) hj, hE]

private theorem boundaryInputSlope (d c : PolarPoint → ℝ) (β : ℝ → ℝ) :
    n06RootBoundaryInputs d c β 8 = deriv β := rfl

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {Kcur : CanonicalData S}
  {base loss m : ℕ} {ε : ℝ} {side : Bool}

def n04PositiveGeometry_storedForwardJet
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (m : ℕ) (side : Bool) (n : ℕ) (y : (StateDirections S × ℝ) × ℝ) :
    PolarPoint [×n]→L[ℝ] PolarPoint :=
  iteratedFDeriv ℝ n (K.chart (liftSectorParameter S C y.1)
    (if side then (K.cutPair m).2 else (K.cutPair m).1))
    (n01ComponentRoot C m side, y.2)

def n04PositiveGeometry_shiftedForwardJet
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (m : ℕ) (side : Bool) (n : ℕ) (y : (StateDirections S × ℝ) × ℝ) :
    PolarPoint [×n]→L[ℝ] PolarPoint :=
  iteratedFDeriv ℝ n (fun p => K.chart (liftSectorParameter S C y.1)
    (if side then (K.cutPair m).2 else (K.cutPair m).1)
    (rootProfileShift (n01ComponentRoot C m side) (n01ComponentRootOrientation side) p))
    (0, y.2)

theorem n04PositiveGeometry_shiftedForwardJet_basis
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) (w : Fin n → Fin 2)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) (θ : ℝ) :
    n04PositiveGeometry_shiftedForwardJet S C Kcur m side n (z, θ)
      (fun j => cylinderBasisVector (w j)) =
      n04PositiveGeometry_forwardBasisValue ((3 / 2 : ℝ) ^ (2 / 3 : ℝ))
        (fun j η => n04PositiveGeometry_rootOddPowerTrace D S C hctx.choose
          m side (2 / 3 : ℝ) j (z, η))
        (fun j η => n04PositiveGeometry_rootBoundaryFormula D S C hctx.choose m side j (z, η))
        (fun η => n04PositiveGeometry_rootBoundaryInput D S C hctx.choose m side 8 (z, η))
        (n04PositiveGeometry_planeWordRadial w) (n04PositiveGeometry_planeWordAngular w) θ := by
  let g : ℝ → ℝ := hctx.choose
  let R : ℝ := hctx.choose_spec.choose
  let hR : 0 < R := hctx.choose_spec.choose_spec.choose
  let δ : ℝ := hctx.choose_spec.choose_spec.choose_spec.choose
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
  have hs := hN.2.2.1.liftSectorParameter_sector z
  let data := hc.2.2.2.2 (liftSectorParameter S C z) hz' hs
  let Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ := data.2.choose
  have hΘ := data.2.choose_spec.1
  have hmodel := data.2.choose_spec.2
  have P := n04PositiveGeometry_actual_unitRootCoordinate_properties hT hS hN hflow
    hz' hs m side g hc.1 hR data.1 hc.2.2.2.1.ne' Θ hΘ
  have ha : n04PositiveGeometry_planeWordRadial w ≤ 4 := by
    have hw := n04PositiveGeometry_planeWord_orders w
    omega
  have hB := congrArg (fun v : N06RootBoundaryInputs => v 8)
    (n04PositiveGeometry_rootBoundaryInput_eq D S C g m side z)
  have hword := P.n04PositiveGeometry_chartBasis_eq hn hn4 w θ
  have he := forwardBasis_congr ((3 / 2 : ℝ) ^ (2 / 3 : ℝ))
    (n04PositiveGeometry_planeWordRadial w) (n04PositiveGeometry_planeWordAngular w) ha
    (fun j hj => n04PositiveGeometry_actual_oddPowerTrace_eq hT hS hN hflow hz
      m side g hc.1 hR data.1 hc.2.2.2.1.ne' Θ hΘ (2 / 3 : ℝ) j hj)
    (fun j => n04PositiveGeometry_actual_unitRootTrace_eq hT hS hN hflow hz
      m side g hc.1 hR data.1 hc.2.2.2.1.ne' Θ hΘ j)
    (hB.trans (boundaryInputSlope _ _ _)).symm
  exact (congrArg (fun A : PolarPoint [×n]→L[ℝ] PolarPoint =>
    A (fun j => cylinderBasisVector (w j))) ((hmodel θ).2.2.2.2.1 n)).trans
      (hword.trans (congrFun he θ))

private def forwardOddDirections
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    (j : ℕ) (hj : j ≤ 3) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootOddPowerTrace D S C hctx.choose m side (2 / 3 : ℝ) j) := by
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  exact n04PositiveGeometry_rootOddPowerTrace_joint hT hS hN hε hflow
    hctx.choose hc.1 hc.2.1 m side hr hroot hctx.choose_spec.choose_spec.choose
    (fun z hz => (hc.2.2.2.2 (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
      (hN.2.2.1.liftSectorParameter_sector z)).1) (2 / 3 : ℝ) j hj

def n04PositiveGeometry_shiftedForwardJet_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_shiftedForwardJet S C Kcur m side n) := by
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  exact n04PositiveGeometry_forwardJet_directions
    (forwardOddDirections hT hS hN hε hflow hctx hr hroot)
    (n04PositiveGeometry_rootBoundaryFormula_joint hT hS hN hε
      hctx.choose hc.1 hc.2.1 m side hr hroot)
    (n04PositiveGeometry_rootBoundaryInput_joint hT hS hN hε
      hctx.choose hc.1 hc.2.1 m side hr hroot 8)
    ((3 / 2 : ℝ) ^ (2 / 3 : ℝ)) hn4 _
    (fun w y hy => n04PositiveGeometry_shiftedForwardJet_basis
      hT hS hN hflow hctx n hn hn4 w y.1 hy.1 y.2)

theorem n04PositiveGeometry_storedForwardJet_unscale
    (hN : N01Properties D T S C base loss ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (n : ℕ) {y : (StateDirections S × ℝ) × ℝ}
    (hy : y ∈ sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ)) :
    n04PositiveGeometry_storedForwardJet S C Kcur m side n y =
      (n04PositiveGeometry_shiftedForwardJet S C Kcur m side n y).compContinuousLinearMap
        (fun _ => rootProfileInverseLinear (n01ComponentRootOrientation side)) := by
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  let data := hc.2.2.2.2 (liftSectorParameter S C y.1)
    (liftSectorParameter_mem_stateNeighborhood (C := C) hy.1 le_rfl)
    (hN.2.2.1.liftSectorParameter_sector y.1)
  have hm := data.2.choose_spec.2 y.2
  exact n04PositiveGeometry_rootProfileJet_unscale _ _ _
    (by cases side <;> norm_num [n01ComponentRootOrientation]) _ n hm.2.1

def n04PositiveGeometry_storedForwardJet_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_storedForwardJet S C Kcur m side n) :=
  (n04PositiveGeometry_planePrecomp_directions n _
    (n04PositiveGeometry_shiftedForwardJet_joint hT hS hN hε hflow hctx hr hroot n hn hn4)
    (rootProfileInverseLinear (n01ComponentRootOrientation side))).congr
    (fun y hy => (n04PositiveGeometry_storedForwardJet_unscale hN hctx n hy).symm)

theorem n04PositiveGeometry_storedForwardJet_word_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4)
    (Q : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_storedForwardJet S C Kcur m side n))
    {K s : ℕ} {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    {θ : ℝ} {P : (StateDirections S × ℝ) → Prop} (hP : P 0)
    {M H t : ℝ} {shift : ℕ} (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 1 ≤ t)
    (hO : ∀ j, j ≤ 3 → ∀ J : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootOddPowerTrace D S C hctx.choose m side (2 / 3 : ℝ) j),
      N04BoundaryWordBounds J K s 5 z θ P M H t shift)
    (hE : ∀ j, ∀ J : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootBoundaryFormula D S C hctx.choose m side j),
      N04BoundaryWordBounds J K s 5 z θ P M H t shift)
    (hB : ∀ J : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootBoundaryInput D S C hctx.choose m side 8),
      N04BoundaryWordBounds J K s 5 z θ P M H t shift) :
    N04BoundaryWordBounds Q K s 1 z θ P
      ((2 : ℝ) ^ n * ((1 + 4 * |(3 / 2 : ℝ) ^ (2 / 3 : ℝ)|) * M)) H t shift := by
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  let JO := forwardOddDirections hT hS hN hε hflow hctx hr hroot
  let JE := n04PositiveGeometry_rootBoundaryFormula_joint hT hS hN hε
    hctx.choose hc.1 hc.2.1 m side hr hroot
  let JB := n04PositiveGeometry_rootBoundaryInput_joint hT hS hN hε
    hctx.choose hc.1 hc.2.1 m side hr hroot 8
  let JA := n04PositiveGeometry_shiftedForwardJet_joint
    hT hS hN hε hflow hctx hr hroot n hn hn4
  have hA := N04BoundaryWordBounds.of_forwardBasis JO JE JB
    ((3 / 2 : ℝ) ^ (2 / 3 : ℝ)) hn4 JA
    (fun w y hy => n04PositiveGeometry_shiftedForwardJet_basis
      hT hS hN hflow hctx n hn hn4 w y.1 hy.1 y.2)
    hz (sectorNeighborhood_convex S base ε ε) hP hM hH ht
    (fun j hj => hO j hj (JO j hj)) (fun j => hE j (JE j)) (hB JB)
  let JP := n04PositiveGeometry_planePrecomp_directions n _ JA
    (rootProfileInverseLinear (n01ComponentRootOrientation side))
  have hp := hA.planeUnscale hz (n01ComponentRootOrientation_eq side) JP
  exact hp.congr (Q := Q) hz
    (fun y hy => (n04PositiveGeometry_storedForwardJet_unscale hN hctx n hy).symm)

end ContinuousFlexibility.Analysis
