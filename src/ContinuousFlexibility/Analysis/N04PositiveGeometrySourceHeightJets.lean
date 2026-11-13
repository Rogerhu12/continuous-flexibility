import ContinuousFlexibility.Analysis.N04PositiveGeometryReferenceHeightJets
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryRadialComposition
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryMoving
import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundary
import ContinuousFlexibility.Analysis.N04RealizationRootBoundaryDirections

/-!
# Genuine radial traces of the original source height ratio

The actual source height is the reference height divided by the current
height at the original source map. Its reciprocal uses the opposite
powers. Current height jets move only in the genuine inverse root label;
positive source jets enter through the finite spatial composition rule.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04SourceHeightStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem n04PositiveGeometry_source_root_eq
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (m : ℕ) (hm : (X.src i side).val = some m) :
    n01ComponentRoot W.C m (!side) = n04PositiveEndpoint i side := by
  have he : n04PositiveEndpoint i side = (if side then W.C.left m else W.C.right m) := by
    simpa only [hm] using (X.src i side).property
  cases side <;> exact he.symm

theorem n04PositiveGeometry_actualHeightPower_root_smooth
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C W.base W.ε)
    (hs : stateSector W.S z.1) (m : ℕ) (side : Bool) (γ θ : ℝ) :
    ContDiffAt ℝ ∞ (fun p => (W.A X.e₀).height z
      (if side then ((W.A X.e₀).cutPair m).2 else ((W.A X.e₀).cutPair m).1) p ^ γ)
      (n01ComponentRoot W.C m side, θ) := by
  let K := W.A X.e₀
  let k := if side then (K.cutPair m).2 else (K.cutPair m).1
  have hA : CanonicalGeometry W.D W.S W.C K W.base W.ε :=
    n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field X.e₀
  have hcut : CanonicalCutGeometry W.S W.C K W.base W.ε :=
    n04bActualTypedAtlas_cutGeometry W.hT W.hS W.through03 W.field X.e₀
  have hp := (canonicalCutRoot_mem_closed_and_zero hA hcut hz hs m side θ).1
  have hreg := (hA.boundary z hz hs k).2.2.2.2.1 _ hp
  exact hreg.2.1.rpow_const_of_ne hreg.2.2.2.ne'

theorem n04PositiveGeometry_sourceHeight_factorization
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (m : ℕ) (hm : (X.src i side).val = some m)
    (z : AnnularState W.S × ℝ) (inv : Bool) (p : PolarPoint) :
    (if inv then (n04PositiveSourceHeight (X.src i side) (W.A X.e₀) z p)⁻¹
      else n04PositiveSourceHeight (X.src i side) (W.A X.e₀) z p) =
      (W.A X.e₀).height (W.C.referenceState, 0)
        (if side then ((W.A X.e₀).cutPair m).1 else ((W.A X.e₀).cutPair m).2) p ^
          (if inv then (-1 : ℝ) else 1) *
        (W.A X.e₀).height z
          (if side then ((W.A X.e₀).cutPair m).1 else ((W.A X.e₀).cutPair m).2)
          (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p) ^
            (if inv then (1 : ℝ) else -1) := by
  cases inv <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    n04PositiveSourceHeight, n04PositiveSourceMap, hm,
    n04CoordinatesCurrentHeightRatio, Real.rpow_one, Real.rpow_neg_one,
    inv_div, div_eq_mul_inv] <;> ring

def n04PositiveGeometry_sourceHeightCurrentJet
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (side : Bool) (m : ℕ) (γ : ℝ) (n : ℕ) (y : (StateDirections W.S × ℝ) × ℝ) :
    PolarPoint [×n]→L[ℝ] ℝ :=
  iteratedFDeriv ℝ n (fun p => (W.A X.e₀).height (liftSectorParameter W.S W.C y.1)
    (if side then ((W.A X.e₀).cutPair m).1 else ((W.A X.e₀).cutPair m).2) p ^ γ)
    (n04PositiveSourceMap (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1)
      (n04PositiveEndpoint i side, y.2))

def n04PositiveGeometry_sourceHeightCurrentJet_joint
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (m : ℕ) (hm : (X.src i side).val = some m)
    (hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side))
    (γ : ℝ) (n : ℕ) (hn : n ≤ 3) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (n04PositiveGeometry_sourceHeightCurrentJet W X i side m γ n) := by
  letI : LocallyConvexSpace ℝ (StateDirections W.S × ℝ) :=
    (sectorPairGrading_withSeminorms W.S).toLocallyConvexSpace
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  have hrad := n04PositiveGeometry_source_root_eq W X i side m hm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D :=
    hrad.symm ▸ (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 :=
    hrad.symm ▸ (W.roots i side).2.1
  have hidx : (if !side then ((W.A X.e₀).cutPair m).2 else ((W.A X.e₀).cutPair m).1) =
      (if side then ((W.A X.e₀).cutPair m).1 else ((W.A X.e₀).cutPair m).2) := by
    cases side <;> rfl
  let JH := n04PositiveGeometry_storedHeightPowerJet_joint W.hT W.hS hN hεone hflow
    hctx hr hroot γ n hn
  let Jα := n04Realization_rootLabel_inverseJointDirections W.hT W.hS hN m (!side)
  apply (n04PositiveGeometry_boundaryMoving_directions JH Jα).congr
  intro y hy
  have hz := stateNeighborhood_mono W.S W.C hb hεW
    (liftSectorParameter_mem_stateNeighborhood (C := W.C) hy.1 le_rfl)
  have hs := hN.2.2.1.liftSectorParameter_sector y.1
  have hp := n04PositiveGeometry_source_endpoint_value W X i side m hm hz hs y.2
  simpa only [n04PositiveGeometry_sourceHeightCurrentJet,
    n04PositiveGeometry_storedHeightPowerJet, hidx, hrad] using
    congrArg (fun p => iteratedFDeriv ℝ n
      (fun q => (W.A X.e₀).height (liftSectorParameter W.S W.C y.1)
        (if side then ((W.A X.e₀).cutPair m).1 else ((W.A X.e₀).cutPair m).2) q ^ γ) p) hp.symm

/-- These are the original source-height radial traces. Only genuine
positive source-map jets remain as input; inverse jets will supply them. -/
def n04PositiveGeometry_sourceHeight_joint_of_sourceJets
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (m : ℕ) (hm : (X.src i side).val = some m)
    (hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side))
    (n : ℕ) (hn : n ≤ 3)
    (JG : ∀ j, 1 ≤ j → j ≤ n → ∀ v : Fin j → PolarPoint,
      SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y => iteratedFDeriv ℝ j
          (n04PositiveSourceMap (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1))
          (n04PositiveEndpoint i side, y.2) v)) (inv : Bool) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y : (StateDirections W.S × ℝ) × ℝ => radialBoundaryJet (fun p => if inv then
        (n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1) p)⁻¹
        else n04PositiveSourceHeight (X.src i side) (W.A X.e₀)
          (liftSectorParameter W.S W.C y.1) p) (n04PositiveEndpoint i side) n y.2) := by
  let U := sectorNeighborhood W.S base ε ε
  have hU : IsOpen U := sectorNeighborhood_isOpen W.S base ε ε
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  let k := if side then ((W.A X.e₀).cutPair m).1 else ((W.A X.e₀).cutPair m).2
  let r := n04PositiveEndpoint i side
  let a : ℝ := if inv then -1 else 1
  let b : ℝ := if inv then 1 else -1
  let f : ((StateDirections W.S × ℝ) × ℝ) → PolarPoint → ℝ :=
    fun _ p => (W.A X.e₀).height (W.C.referenceState, 0) k p ^ a
  let h : ((StateDirections W.S × ℝ) × ℝ) → PolarPoint → ℝ :=
    fun y p => (W.A X.e₀).height (liftSectorParameter W.S W.C y.1) k p ^ b
  let g : ((StateDirections W.S × ℝ) × ℝ) → PolarPoint → PolarPoint :=
    fun y => n04PositiveSourceMap (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1)
  have hrad := n04PositiveGeometry_source_root_eq W X i side m hm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D :=
    hrad.symm ▸ (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 :=
    hrad.symm ▸ (W.roots i side).2.1
  have hidx : (if !side then ((W.A X.e₀).cutPair m).2 else ((W.A X.e₀).cutPair m).1) = k := by
    cases side <;> rfl
  have hz (y : (StateDirections W.S × ℝ) × ℝ) (hy : y ∈ U ×ˢ (univ : Set ℝ)) :=
    stateNeighborhood_mono W.S W.C hb hεW
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) hy.1 le_rfl)
  have hs (y : (StateDirections W.S × ℝ) × ℝ) := hN.2.2.1.liftSectorParameter_sector y.1
  have hf (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) : ContDiffAt ℝ ∞ (f y) (r, y.2) := by
    simpa only [hrad, hidx] using n04PositiveGeometry_actualHeightPower_root_smooth W X
      W.through03.1.1.reference_mem_stateNeighborhood W.through03.1.1.2.2.1.stateSector
      m (!side) a y.2
  have hg (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) : ContDiffAt ℝ ∞ (g y) (r, y.2) :=
    (n04Coordinates_actualAtlas_positiveEndpoint_of_source W.hT W.hS W.through03 W.field
      X.e₀ (X.src i side) (hz y hy) (hs y)).root_smooth y.2
  have hh (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) : ContDiffAt ℝ ∞ (h y) (g y (r, y.2)) := by
    have hp := n04PositiveGeometry_source_endpoint_value W X i side m hm (hz y hy) (hs y) y.2
    have ht := n04PositiveGeometry_actualHeightPower_root_smooth W X (hz y hy) (hs y)
      m (!side) b (Function.invFun
        (n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side)) y.2)
    simpa only [hrad, hidx, ← hp] using ht
  let JF (j : ℕ) (hj : j ≤ n) : SmoothDirections (U ×ˢ univ)
      (fun y => radialBoundaryJet (f y) r j y.2) := by
    let Q := n04PositiveGeometry_referenceHeightPowerJet_joint W.hT W.hS hN hε hεone hflow
      hctx hr hroot a j (hj.trans hn)
    apply (n04PositiveGeometry_boundaryFixedEvaluation_directions Q (fun _ => (1, 0))).congr
    intro y hy
    simpa only [n04PositiveGeometry_referenceHeightPowerJet, hidx, hrad] using
      (n06_radialBoundaryJet_eq_frechet j (hf y hy)).symm
  let JH (j : ℕ) (hj : j ≤ n) : SmoothDirections (U ×ˢ univ)
      (fun y => iteratedFDeriv ℝ j (h y) (g y (r, y.2))) :=
    n04PositiveGeometry_sourceHeightCurrentJet_joint W X hb hε hεW hεone hflow
      i side m hm hctx b j (hj.trans hn)
  let JC (j : ℕ) (hj : j ≤ n) :=
    n04PositiveGeometry_boundaryRadialComposition_directions hU r j h g hh hg
      (fun l hl => JH l (hl.trans hj)) (fun l hl hlj => JG l hl (hlj.trans hj))
  apply (n04PositiveGeometry_radialProduct_directions hU r n f (fun y => h y ∘ g y)
    hf (fun y hy => (hh y hy).comp _ (hg y hy)) JF JC).congr
  intro y _
  apply congrArg (fun F : PolarPoint → ℝ => radialBoundaryJet F r n y.2)
  funext p
  exact (n04PositiveGeometry_sourceHeight_factorization W X i side m hm
    (liftSectorParameter W.S W.C y.1) inv p).symm

end ContinuousFlexibility.Analysis
