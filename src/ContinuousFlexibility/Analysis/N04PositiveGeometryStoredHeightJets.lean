module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledHeightTrace
public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsAxisJets

/-!
# The original stored height has genuine full spatial jet towers

The common context fixes a division before any exponent or jet order.
At each state its single unit model identifies every basis word of the
stored height. The fixed inverse radial linear map returns the original
physical jet without a parameter-dependent choice of extension.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {Kcur : CanonicalData S}
  {base loss m : ℕ} {ε : ℝ} {side : Bool}

def n04PositiveGeometry_storedHeightPowerJet
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (m : ℕ) (side : Bool) (γ : ℝ) (n : ℕ) (y : (StateDirections S × ℝ) × ℝ) :
    PolarPoint [×n]→L[ℝ] ℝ :=
  iteratedFDeriv ℝ n (fun p => K.height (liftSectorParameter S C y.1)
    (if side then (K.cutPair m).2 else (K.cutPair m).1) p ^ γ)
    (n01ComponentRoot C m side, y.2)

def n04PositiveGeometry_shiftedHeightPowerJet
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (m : ℕ) (side : Bool) (γ : ℝ) (n : ℕ) (y : (StateDirections S × ℝ) × ℝ) :
    PolarPoint [×n]→L[ℝ] ℝ :=
  iteratedFDeriv ℝ n (fun p => K.height (liftSectorParameter S C y.1)
    (if side then (K.cutPair m).2 else (K.cutPair m).1)
    (rootProfileShift (n01ComponentRoot C m side) (n01ComponentRootOrientation side) p) ^ γ)
    (0, y.2)

theorem n04PositiveGeometry_shiftedHeightPowerJet_basis
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (γ : ℝ) (n : ℕ) (hn : n ≤ 3) (w : Fin n → Fin 2)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) (θ : ℝ) :
    n04PositiveGeometry_shiftedHeightPowerJet S C Kcur m side γ n (z, θ)
      (fun j => cylinderBasisVector (w j)) =
      iteratedDeriv (n04PositiveGeometry_planeWordAngular w)
        (fun η => n04PositiveGeometry_rootHeightPowerTrace D S C hctx.choose m side γ
          (n04PositiveGeometry_planeWordRadial w) (z, η)) θ := by
  let g := hctx.choose
  let R := hctx.choose_spec.choose
  let hR := hctx.choose_spec.choose_spec.choose
  let δ := hctx.choose_spec.choose_spec.choose_spec.choose
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
  have hs := hN.2.2.1.liftSectorParameter_sector z
  let stateData := hc.2.2.2.2 (liftSectorParameter S C z) hz' hs
  let Θ := stateData.2.choose
  have hΘ := stateData.2.choose_spec.1
  have hmodel := stateData.2.choose_spec.2
  have P := n04PositiveGeometry_actual_unitRootCoordinate_properties hT hS hN hflow
    hz' hs m side g hc.1 hR stateData.1 hc.2.2.2.1.ne' Θ hΘ
  have hχ (η : ℝ) : 0 < extendedRootOddCoefficient
      (rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
        (n01RootLabel S C (liftSectorParameter S C z) m side)) (0, η) := by
    rw [extendedRootOddCoefficient_of_nonneg _ (le_refl (0 : ℝ))]
    exact P.odd_positive η
  have hΩ := n04PositiveGeometry_rootHeightPowerDomain_isOpen P.n06_extendedOdd_smooth R
  have hreg := n04PositiveGeometry_rootDividedHeight_rpow_contDiffOn
    hN.1.1.choose_spec.1.2.2.1.1 hc.1
    (contDiff_stateProfile_of_n01 hS hT hN _) (contDiff_stateHeight_of_n01 hS hT hN _)
    stateData.1 P.n06_extendedOdd_smooth γ
  have haxis := n04PositiveGeometry_rootHeightPowerDomain_axis hR hχ
  have hword := n04PositiveGeometry_axisBasis_eq_radialTrace hΩ hreg 0 haxis n w θ
  have ha : n04PositiveGeometry_planeWordRadial w ≤ 3 := by
    have ho := n04PositiveGeometry_planeWord_orders w
    omega
  have htrace := n04PositiveGeometry_actual_unitHeightPowerTrace_eq hT hS hN hflow
    hz m side g hc.1 hR stateData.1 hc.2.2.2.1.ne' Θ hΘ γ _ ha
  exact (congrArg (fun A : PolarPoint [×n]→L[ℝ] ℝ =>
    A (fun j => cylinderBasisVector (w j))) ((hmodel θ).2.2.2.2.2 γ n)).trans
      (hword.trans (congrArg (fun f : ℝ → ℝ =>
        iteratedDeriv (n04PositiveGeometry_planeWordAngular w) f θ) htrace))

def n04PositiveGeometry_rootHeightPowerTrace_context_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    (γ : ℝ) (n : ℕ) (hn : n ≤ 3) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootHeightPowerTrace D S C hctx.choose m side γ n) := by
  let hR := hctx.choose_spec.choose_spec.choose
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  exact n04PositiveGeometry_rootHeightPowerTrace_joint hT hS hN hε hflow
    hctx.choose hc.1 hc.2.1 m side hr hroot hR
    (fun z hz => (hc.2.2.2.2 (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
      (hN.2.2.1.liftSectorParameter_sector z)).1) γ n hn

def n04PositiveGeometry_shiftedHeightPowerJet_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    (γ : ℝ) (n : ℕ) (hn : n ≤ 3) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_shiftedHeightPowerJet S C Kcur m side γ n) :=
  n04PositiveGeometry_axisJet_directions
    (fun a ha => n04PositiveGeometry_rootHeightPowerTrace_context_joint
      hT hS hN hε hflow hctx hr hroot γ a (ha.trans hn))
    (fun w y hy => n04PositiveGeometry_shiftedHeightPowerJet_basis
      hT hS hN hflow hctx γ n hn w y.1 hy.1 y.2)

theorem n04PositiveGeometry_storedHeightPowerJet_unscale
    (hN : N01Properties D T S C base loss ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (γ : ℝ) (n : ℕ) {y : (StateDirections S × ℝ) × ℝ}
    (hy : y ∈ sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ)) :
    n04PositiveGeometry_storedHeightPowerJet S C Kcur m side γ n y =
      (n04PositiveGeometry_shiftedHeightPowerJet S C Kcur m side γ n y).compContinuousLinearMap
        (fun _ => rootProfileInverseLinear (n01ComponentRootOrientation side)) := by
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  let data := hc.2.2.2.2 (liftSectorParameter S C y.1)
    (liftSectorParameter_mem_stateNeighborhood (C := C) hy.1 le_rfl)
    (hN.2.2.1.liftSectorParameter_sector y.1)
  have hm := data.2.choose_spec.2 y.2
  have hpos : 0 < Kcur.height (liftSectorParameter S C y.1)
      (if side then (Kcur.cutPair m).2 else (Kcur.cutPair m).1)
      (rootProfileShift (n01ComponentRoot C m side) (n01ComponentRootOrientation side) (0, y.2)) := by
    simpa only [rootProfileShift, mul_zero, add_zero] using hm.2.2.2.1
  exact n04PositiveGeometry_rootProfileJet_unscale _ _ _
    (by cases side <;> norm_num [n01ComponentRootOrientation]) _ n
    (hm.2.2.1.rpow_const_of_ne hpos.ne')

def n04PositiveGeometry_storedHeightPowerJet_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    (γ : ℝ) (n : ℕ) (hn : n ≤ 3) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_storedHeightPowerJet S C Kcur m side γ n) :=
  (n04PositiveGeometry_planePrecomp_directions n _
    (n04PositiveGeometry_shiftedHeightPowerJet_joint hT hS hN hε hflow hctx hr hroot γ n hn)
    (rootProfileInverseLinear (n01ComponentRootOrientation side))).congr
    (fun y hy => (n04PositiveGeometry_storedHeightPowerJet_unscale hN hctx γ n hy).symm)

theorem n04PositiveGeometry_storedHeightPowerJet_word_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hctx : N04PositiveGeometryRootContext D S C Kcur base ε m side)
    (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0)
    (γ : ℝ) (n : ℕ) (hn : n ≤ 3)
    (Q : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_storedHeightPowerJet S C Kcur m side γ n))
    {K s : ℕ} {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    {θ : ℝ} {P : (StateDirections S × ℝ) → Prop} (hP : P 0)
    {M H t : ℝ} {shift : ℕ} (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 1 ≤ t)
    (hb : ∀ a, a ≤ n → ∀ J : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootHeightPowerTrace D S C hctx.choose m side γ a),
      N04BoundaryWordBounds J K s 5 z θ P M H t shift) :
    N04BoundaryWordBounds Q K s 1 z θ P ((2 : ℝ) ^ n * M) H t shift := by
  let JT (a : ℕ) (ha : a ≤ n) := n04PositiveGeometry_rootHeightPowerTrace_context_joint
    hT hS hN hε hflow hctx hr hroot γ a (ha.trans hn)
  let JA := n04PositiveGeometry_shiftedHeightPowerJet_joint
    hT hS hN hε hflow hctx hr hroot γ n hn
  have hA := N04BoundaryWordBounds.of_axisRadialTraces JT JA
    (fun w y hy => n04PositiveGeometry_shiftedHeightPowerJet_basis
      hT hS hN hflow hctx γ n hn w y.1 hy.1 y.2)
    hz (sectorNeighborhood_convex S base ε ε) hP hM hH ht
    (fun a ha => (hb a ha (JT a ha)).reserve hM hH ht (by omega : 1 + n ≤ 5))
  let JP := n04PositiveGeometry_planePrecomp_directions n _ JA
    (rootProfileInverseLinear (n01ComponentRootOrientation side))
  have hp := hA.planeUnscale hz (show n01ComponentRootOrientation side = 1 ∨
      n01ComponentRootOrientation side = -1 from by cases side <;> simp [n01ComponentRootOrientation]) JP
  exact hp.congr (Q := Q) hz
    (fun y hy => (n04PositiveGeometry_storedHeightPowerJet_unscale hN hctx γ n hy).symm)

end ContinuousFlexibility.Analysis
