module

public import ContinuousFlexibility.Analysis.N01ReturnVelocitySpatialTower
public import ContinuousFlexibility.Analysis.ReturnCorrectionTransportEquations
public import ContinuousFlexibility.Analysis.SmoothDirectionsNormedComposition

/-!
# Actual joint towers of the transported correction factors

These are the three scalar fields in the radial transport equations:
the inverse-flow slope, the independently pulled displacement, and the
same displacement at the actual return residual.  Their joint towers
use the existing circle realizations and the same cutoff as the final
correction.  No radial or parameter regularity is added as a premise.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped Topology

/-- Add an independent parameter while preserving the actual spatial
coordinate and the original genuine jets. -/
def _root_.ContinuousFlexibility.Statements.SmoothDirections.fstParameter
    {E F P G : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [TopologicalSpace P] [AddCommGroup P] [Module ℝ P]
    [IsTopologicalAddGroup P] [ContinuousSMul ℝ P]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    {U : Set E} {V : Set P} {f : E × P → G}
    (J : SmoothDirections (U ×ˢ V) f) (hU : IsOpen U) (hV : IsOpen V) :
    SmoothDirections ((U ×ˢ (univ : Set F)) ×ˢ V)
      (fun x : (E × F) × P => f (x.1.1, x.2)) := by
  let L : (E × F) × P →L[ℝ] E × P :=
    ((ContinuousLinearMap.fst ℝ E F).comp
      (ContinuousLinearMap.fst ℝ (E × F) P)).prod
        (ContinuousLinearMap.snd ℝ (E × F) P)
  exact J.compLinear L ((hU.prod isOpen_univ).prod hV) (fun x hx => ⟨hx.1.1, hx.2⟩)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology ContDiff

local instance n01ReturnTransportSpatialTowersStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (m : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m)
  (hdisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ p : PolarPoint,
    p.1 ∈ Ioo l h →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)

def N01Properties.singleComponentInverseSlopeCircleTower :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ Ioo l h)
      (hN.singleComponentInverseSlopeCircle hS hT m) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hi : HasInterpolation H.grading := (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  let J := hN.singleComponentFlowTower hS hT m l h hl hh hdisc
  have hpos : MapsTo (hN.singleComponentFlowCircle hS hT m)
      (sectorNeighborhood S base ε ε ×ˢ Ioo l h) (circlePositiveLiftDomain H) := by
    intro x hx
    exact hN.singleComponentFlowCircle_positive hS hT m x hx.1
      ⟨hl.trans hx.2.1, hx.2.2.trans hh⟩
  exact circleInverseComposeDirections hH hT hN.1.1 (by norm_num) hi (fun _ => 0)
    J (circleDerivativeDirections hH J) hpos

private theorem returnTransport_one_add_sub_one (a : ℝ) : 1 + (a - 1) = a := by
  ring

include hN hS hT hl hh hdisc in
private theorem returnFlowInverseSlope_parameterSpatialTower_nonempty :
    Nonempty (SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        returnFlowInverseSlope S C (liftSectorParameter S C x.1) m x.2)) := by
  let H := S.circle (3 / 4 : ℝ)
  let f : ((StateDirections S × ℝ) × ℝ) → H.Space :=
    hN.singleComponentInverseSlopeCircle hS hT m
  let J : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ Ioo l h) f :=
    hN.singleComponentInverseSlopeCircleTower hS hT m l h hl hh hdisc
  have hH (i : ℕ) : 0 < T.H (T.sample i) :=
    (material_circle_sample_weights_pos hT hN.1.1).2 i
  let K : SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ Ioo l h) ×ˢ univ)
      (fun x : ((StateDirections S × ℝ) × ℝ) × ℝ => H.decode (f x.1) m x.2) :=
    circleDecodedJointDirections (hS.2.1 (3 / 4 : ℝ)) hH J m
  let L : SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ Ioo l h) ×ˢ univ)
      (fun x : ((StateDirections S × ℝ) × ℝ) × ℝ => 1 + H.decode (f x.1) m x.2) :=
    K.comp_contDiff (g := fun y : ℝ => 1 + y) (V := univ) isOpen_univ
      ((contDiff_const.add contDiff_id : ContDiff ℝ ∞ (fun y : ℝ => 1 + y)).contDiffOn)
        (fun _ _ => mem_univ _)
  let M : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        1 + H.decode (f (x.1, x.2.1)) m x.2.2) :=
    L.compLinear (parameterSpatialAssociation (StateDirections S × ℝ))
      ((sectorNeighborhood_isOpen S base ε ε).prod (isOpen_Ioo.prod isOpen_univ))
      (fun x hx => ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩)
  refine ⟨M.congrOn ?_⟩
  intro x hx
  have hd : H.decode (f (x.1, x.2.1)) m x.2.2 =
      returnFlowInverseSlope S C (liftSectorParameter S C x.1) m x.2 - 1 :=
    hN.singleComponentInverseSlopeCircle_decode hS hT m (x.1, x.2.1) hx.1
      ⟨hl.trans hx.2.1.1, hx.2.1.2.trans hh⟩ x.2.2
  exact (congrArg (fun y : ℝ => 1 + y) hd).trans
    (returnTransport_one_add_sub_one (returnFlowInverseSlope S C (liftSectorParameter S C x.1) m x.2))

def N01Properties.returnFlowInverseSlope_parameterSpatialTower :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        returnFlowInverseSlope S C (liftSectorParameter S C x.1) m x.2) :=
  Classical.choice (returnFlowInverseSlope_parameterSpatialTower_nonempty
    (hN := hN) (hS := hS) (hT := hT) (m := m) (l := l) (h := h)
    (hl := hl) (hh := hh) (hdisc := hdisc))

variable (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)

def N01Properties.singleComponentPulledDisplacementCircleTower :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ Ioo l h)
      (hN.singleComponentPulledDisplacementCircle hS hT χ m) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hi : HasInterpolation H.grading := (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  have hU := ((sectorNeighborhood_isOpen S base ε ε).prod
    (isOpen_univ : IsOpen (univ : Set (CircleSpace S)))).prod
      (isOpen_Ioo : IsOpen (Ioo l h))
  let L := correctionStateRadiusProjection S
  let P : (((StateDirections S × ℝ) × CircleSpace S) × ℝ) →L[ℝ]
      (StateDirections S × ℝ) × CircleSpace S :=
    ContinuousLinearMap.fst ℝ ((StateDirections S × ℝ) × CircleSpace S) ℝ
  have hL : MapsTo L ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ Ioo l h)
      (sectorNeighborhood S base ε ε ×ˢ Ioo l h) :=
    fun x hx => ⟨hx.1.1, hx.2⟩
  let Jflow := (hN.singleComponentFlowTower hS hT m l h hl hh hdisc).compLinear L hU hL
  let Jint := (hN.singleComponentInterpolationTower hS hT χ hχ m l h).compLinear L hU hL
  let Jdisp := (hN.smoothTameOn_returnCorrectionDisplacementCircleLinear hS hT).choose.compLinear
    P hU (fun x hx => hx.1)
  have hflowpos : MapsTo
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × ℝ =>
        hN.singleComponentFlowCircle hS hT m (L x))
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ Ioo l h) (circlePositiveLiftDomain H) := by
    intro x hx
    exact hN.singleComponentFlowCircle_positive hS hT m (x.1.1, x.2) hx.1.1
      ⟨hl.trans hx.2.1, hx.2.2.trans hh⟩
  have hintpos : MapsTo
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × ℝ =>
        hN.singleComponentInterpolationCircle hS hT χ m (L x))
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ Ioo l h) (circlePositiveLiftDomain H) := by
    intro x hx
    exact hN.singleComponentInterpolationCircle_positive hS hT χ hχrange m
      (x.1.1, x.2) hx.1.1 ⟨(hl.trans hx.2.1).le, (hx.2.2.trans hh).le⟩
  let Jfirst := circleInverseComposeDirections hH hT hN.1.1 (by norm_num)
    hi (fun _ => 0) Jint Jdisp hintpos
  exact circleInverseComposeDirections hH hT hN.1.1 (by norm_num)
    hi (fun _ => 0) Jflow Jfirst hflowpos

def N01Properties.returnCorrectionPulledDisplacement_parameterSpatialTower :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1.1)
          m x.2 x.1.2) := by
  let J := hN.singleComponentPulledDisplacementCircleTower
    hS hT m l h hl hh hdisc χ hχ hχrange
  have hH (i : ℕ) : 0 < T.H (T.sample i) :=
    (material_circle_sample_weights_pos hT hN.1.1).2 i
  let K := (circleDecodedJointDirections (hS.2.1 (3 / 4 : ℝ)) hH J m).compLinear
    (parameterSpatialAssociation ((StateDirections S × ℝ) × CircleSpace S))
    (((sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ).prod
      (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩)
  apply K.congrOn
  intro x hx
  exact hN.singleComponentPulledDisplacementCircle_decode hS hT χ hχrange m
    (x.1, x.2.1) hx.1.1 ⟨hl.trans hx.2.1.1, hx.2.1.2.trans hh⟩ x.2.2

def N01Properties.singleComponentPulledResidualCircleTower
    {R : ReturnEquationData S} (hR : N02Properties D T S C R base ε) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ Ioo l h)
      (fun x : (StateDirections S × ℝ) × ℝ =>
        hN.singleComponentPulledDisplacementCircle hS hT χ m
          ((x.1, R.residual (liftSectorParameter S C x.1)), x.2)) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  letI : LocallyConvexSpace ℝ (((StateDirections S × ℝ) × H.Space) × ℝ) :=
    velocitySpatial_pair_locallyConvex (E := StateDirections S × ℝ) (F := H.Space)
      (sectorPairGrading_withSeminorms S)
      (withSeminorms_graded (fun n => H.level n) H.bond)
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_Ioo : IsOpen (Ioo l h))
  let F : ((StateDirections S × ℝ) × ℝ) →L[ℝ] StateDirections S × ℝ :=
    ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) ℝ
  let G : ((StateDirections S × ℝ) × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) ℝ
  have hres : SmoothTameOn (pairGrading (sectorGrading S) realGrading) H.grading
      (sectorNeighborhood S base ε ε)
      (fun z => R.residual (liftSectorParameter S C z)) := by
    rcases hR with ⟨_, _, _, _, _, _, _, _, _, _, hr⟩
    exact hr
  let JR := hres.choose.compLinear F hU (fun x hx => hx.1)
  let J := smoothDirectionsProd
    (smoothDirectionsProd (smoothDirectionsLinearOn F hU) JR)
    (smoothDirectionsLinearOn G hU)
  exact J.compCircle hH
    (hN.singleComponentPulledDisplacementCircleTower
      hS hT m l h hl hh hdisc χ hχ hχrange)
    (fun x hx => ⟨⟨hx.1, mem_univ _⟩, hx.2⟩)

def N01Properties.returnCorrectionPulledResidual_parameterSpatialTower
    {R : ReturnEquationData S} (hR : N02Properties D T S C R base ε) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1)
          m x.2 (R.residual (liftSectorParameter S C x.1))) := by
  let J := hN.singleComponentPulledResidualCircleTower
    hS hT m l h hl hh hdisc χ hχ hχrange hR
  have hH (i : ℕ) : 0 < T.H (T.sample i) :=
    (material_circle_sample_weights_pos hT hN.1.1).2 i
  let K := (circleDecodedJointDirections (hS.2.1 (3 / 4 : ℝ)) hH J m).compLinear
    (parameterSpatialAssociation (StateDirections S × ℝ))
    ((sectorNeighborhood_isOpen S base ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩)
  apply K.congrOn
  intro x hx
  exact hN.singleComponentPulledDisplacementCircle_decode hS hT χ hχrange m
    ((x.1, R.residual (liftSectorParameter S C x.1)), x.2.1) hx.1
      ⟨hl.trans hx.2.1.1, hx.2.1.2.trans hh⟩ x.2.2

end ContinuousFlexibility.Statements
