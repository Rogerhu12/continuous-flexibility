module

public import ContinuousFlexibility.Analysis.N01FlowSpatialJets
public import ContinuousFlexibility.Analysis.CircleSingleComponentJets
public import ContinuousFlexibility.Analysis.N01SelectorInverse
public import ContinuousFlexibility.Analysis.NormedSmoothDirections

/-!
# A varying radius in one component of the actual flow

The single-component field is realized in the original circle model.
Its affine lift has zero fixed travel: the reference translation is
included in that one component. This gives a genuine joint state and
radius tower for the actual inverse flow on an interior positive
discriminant strip, without postulating any inverse parameter regularity.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01SingleComponentFlowStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology

private theorem singleComponent_increment_add_reference
    (m : ℕ) (r travel : ℝ) (F G : PolarPoint → ℝ)
    (hG : ∀ θ, G (r, θ) = θ - travel) :
    circleSingleComponentField m
        (fun θ => mixedDerivative 0 0 (fun p => F p - G p) (r, θ)) +
      circleSingletonField m (G (r, 0)) =
      circleSingleComponentField m (fun θ => F (r, θ) - θ) := by
  funext i θ
  by_cases hi : i = m
  · subst i
    simp only [Pi.add_apply, circleSingleComponentField, circleSingletonField,
      eq_self_iff_true, ite_true, mixedDerivative, iteratedDeriv_zero]
    rw [hG θ, hG 0]
    ring
  · simp only [Pi.add_apply, circleSingleComponentField, circleSingletonField,
      if_neg hi, add_zero]

private theorem singleComponent_displacement_affineLift (m : ℕ) (f : ℝ → ℝ) :
    circleAffineLift (fun _ => 0)
      (circleSingleComponentField m (fun θ => f θ - θ)) 1 m = f := by
  funext θ
  simp only [circleAffineLift, circleSingleComponentField, if_pos rfl, one_mul, add_zero]
  exact (add_comm θ (f θ - θ)).trans (sub_add_cancel (f θ) θ)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)

include hN in
theorem N01Properties.singleComponentFlowIncrement_periodic
    (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    Function.Periodic (fun θ =>
      ordinaryFlowFamily S C m 0 0 (r, θ) (liftSectorParameter S C z)) Real.pi := by
  intro θ
  change C.minusFlow (liftSectorParameter S C z) m r (θ + Real.pi) -
      C.minusFlow (C.referenceState, 0) m r (θ + Real.pi) =
    C.minusFlow (liftSectorParameter S C z) m r θ - C.minusFlow (C.referenceState, 0) m r θ
  rw [hN.minusFlow_add_period (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    m ⟨hr.1.le, hr.2.le⟩ θ,
    hN.minusFlow_add_period hN.reference_mem_stateNeighborhood m ⟨hr.1.le, hr.2.le⟩ θ]
  ring

include hN hS hT in
theorem N01Properties.singleComponentFlowIncrement_member
    (m : ℕ) (r : ℝ) (hr : r ∈ Ioo (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    CircleMember T (3 / 4 : ℝ) (circleSingleComponentField m
      (fun θ => ordinaryFlowFamily S C m 0 0 (r, θ) (liftSectorParameter S C z))) := by
  apply circleSingleComponentField_member
  · have hf := hN.minusFlow_angular_contDiff hS hT
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hN.2.2.1.liftSectorParameter_sector z) m ⟨hr.1.le, hr.2.le⟩
    have hg := hN.minusFlow_angular_contDiff hS hT hN.reference_mem_stateNeighborhood
      hN.2.2.1.stateSector m ⟨hr.1.le, hr.2.le⟩
    exact hf.sub hg
  · exact hN.singleComponentFlowIncrement_periodic m r hr z hz

def N01Properties.singleComponentFlowIncrementCircle
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ) : CircleSpace S := by
  classical
  exact if hx : x.1 ∈ sectorNeighborhood S base ε ε ∧
      x.2 ∈ Ioo (C.left m) (C.right m) then
    circleRealize (hS.2.1 (3 / 4 : ℝ))
      (circleSingleComponentField m
        (fun θ => ordinaryFlowFamily S C m 0 0 (x.2, θ) (liftSectorParameter S C x.1)))
      (hN.singleComponentFlowIncrement_member hS hT m x.2 hx.2 x.1 hx.1)
  else 0

theorem N01Properties.singleComponentFlowIncrementCircle_decode
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) :
    (S.circle (3 / 4 : ℝ)).decode (hN.singleComponentFlowIncrementCircle hS hT m x) =
      circleSingleComponentField m
        (fun θ => ordinaryFlowFamily S C m 0 0 (x.2, θ) (liftSectorParameter S C x.1)) := by
  simp only [singleComponentFlowIncrementCircle, dif_pos (And.intro hx hr)]
  exact circleRealize_decode _ _ _

def N01Properties.singleComponentFlowCircle
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ) : CircleSpace S :=
  hN.singleComponentFlowIncrementCircle hS hT m x +
    circleSingletonLinear (hS.2.1 (3 / 4 : ℝ)) m
      (C.minusFlow (C.referenceState, 0) m x.2 0)

theorem N01Properties.singleComponentFlowCircle_decode
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) :
    (S.circle (3 / 4 : ℝ)).decode (hN.singleComponentFlowCircle hS hT m x) =
      circleSingleComponentField m
        (fun θ => C.minusFlow (liftSectorParameter S C x.1) m x.2 θ - θ) := by
  have hadd :
      (S.circle (3 / 4 : ℝ)).decode (hN.singleComponentFlowCircle hS hT m x) =
        (S.circle (3 / 4 : ℝ)).decode
          (hN.singleComponentFlowIncrementCircle hS hT m x) +
        (S.circle (3 / 4 : ℝ)).decode
          (circleSingletonLinear (hS.2.1 (3 / 4 : ℝ)) m
            (C.minusFlow (C.referenceState, 0) m x.2 0)) :=
    (S.circle (3 / 4 : ℝ)).decode.map_add
      (hN.singleComponentFlowIncrementCircle hS hT m x)
      (circleSingletonLinear (hS.2.1 (3 / 4 : ℝ)) m
        (C.minusFlow (C.referenceState, 0) m x.2 0))
  have hfields := congrArg₂ (fun u v : ℕ → ℝ → ℝ => u + v)
    (hN.singleComponentFlowIncrementCircle_decode hS hT m x hx hr)
    (circleSingletonLinear_decode (hS.2.1 (3 / 4 : ℝ)) m
      (C.minusFlow (C.referenceState, 0) m x.2 0))
  exact hadd.trans (hfields.trans
    (singleComponent_increment_add_reference m x.2 (opticalTravel D.w (C.left m) x.2)
      (fun p => C.minusFlow (liftSectorParameter S C x.1) m p.1 p.2)
      (fun p => C.minusFlow (C.referenceState, 0) m p.1 p.2)
      (hN.minusFlow_reference_eq hS hT m ⟨hr.1.le, hr.2.le⟩)))

theorem N01Properties.singleComponentFlowCircle_affineLift
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) :
    circleAffineLift (fun _ => 0)
        ((S.circle (3 / 4 : ℝ)).decode (hN.singleComponentFlowCircle hS hT m x)) 1 m =
      C.minusFlow (liftSectorParameter S C x.1) m x.2 := by
  exact (congrArg (fun e : ℕ → ℝ → ℝ => circleAffineLift (fun _ => 0) e 1 m)
    (hN.singleComponentFlowCircle_decode hS hT m x hx hr)).trans
      (singleComponent_displacement_affineLift m
        (C.minusFlow (liftSectorParameter S C x.1) m x.2))

theorem N01Properties.singleComponentFlowCircle_positive
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) :
    hN.singleComponentFlowCircle hS hT m x ∈ circlePositiveLiftDomain (S.circle (3 / 4 : ℝ)) := by
  apply (circlePositiveLiftDomain_iff (hS.2.1 (3 / 4 : ℝ)) (fun _ => 0) _).mpr
  intro i θ
  by_cases hi : i = m
  · subst i
    rw [hN.singleComponentFlowCircle_affineLift hS hT m x hx hr]
    have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
      hN.2.2.2.2.2.2.1
    exact ((hflow _ (liftSectorParameter_mem_stateNeighborhood hx le_rfl) m θ).2.2.2
      x.2 ⟨hr.1.le, hr.2.le⟩).1
  · have heq : circleAffineLift (fun _ => 0)
        ((S.circle (3 / 4 : ℝ)).decode (hN.singleComponentFlowCircle hS hT m x)) 1 i =
          (fun t : ℝ => t) := by
      funext t
      rw [hN.singleComponentFlowCircle_decode hS hT m x hx hr]
      simp only [circleAffineLift, circleSingleComponentField, if_neg hi,
        one_mul, add_zero]
    rw [heq, deriv_id'']
    exact zero_lt_one

def N01Properties.singleComponentFlowInverseCircle
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ) : CircleSpace S :=
  circlePositiveInversePerturbation (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun _ => 0) (hN.singleComponentFlowCircle hS hT m x)

theorem N01Properties.singleComponentFlowInverseCircle_decode
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (hN.singleComponentFlowInverseCircle hS hT m x) m θ =
      Function.invFun (C.minusFlow (liftSectorParameter S C x.1) m x.2) θ - θ := by
  have hd : (S.circle (3 / 4 : ℝ)).decode
      (hN.singleComponentFlowInverseCircle hS hT m x) m θ =
        circleAffineInverse (fun _ => 0) (hN.singleComponentFlowCircle hS hT m x) m θ -
          (θ - 0) :=
    congrArg (fun e : ℕ → ℝ → ℝ => e m θ)
      (circlePositiveInversePerturbation_decode
        (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) (fun _ => 0)
        (hN.singleComponentFlowCircle hS hT m x)
        (hN.singleComponentFlowCircle_positive hS hT m x hx hr))
  have heq : circleAffineInverse (fun _ => 0) (hN.singleComponentFlowCircle hS hT m x) m θ =
      Function.invFun (C.minusFlow (liftSectorParameter S C x.1) m x.2) θ :=
    congrArg (fun f : ℝ → ℝ => Function.invFun f θ)
      (hN.singleComponentFlowCircle_affineLift hS hT m x hx hr)
  exact hd.trans (congrArg₂ (fun a b : ℝ => a - b) heq (sub_zero θ))

section RadialTower

variable (m : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m)
  (hdisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ p : PolarPoint,
    p.1 ∈ Ioo l h →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)

def N01Properties.singleComponentFlowIncrementTower :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ Ioo l h)
      (hN.singleComponentFlowIncrementCircle hS hT m) := by
  let J := hN.sectorFlow_radialJointTower hS hT m l h hl hh hdisc
  have hM (i : ℕ) : 0 ≤ T.M (T.sample i) :=
    ((material_circle_sample_weights_pos hT hN.1.1).1 i).le
  have hH (i : ℕ) : 0 ≤ T.H (T.sample i) :=
    ((material_circle_sample_weights_pos hT hN.1.1).2 i).le
  apply (exists_singleComponent_circle_smoothDirections J
    ((sectorNeighborhood_isOpen S base ε ε).prod isOpen_Ioo)
    ((sectorNeighborhood_convex S base ε ε).prod (convex_Ioo l h))
    (hN.sectorFlow_radialJointTower_uniform hS hT m l h hl hh hdisc)
    (fun b θ x hx => hN.sectorFlowStrip_hasDerivAt_angular hS hT m l h hl hh hdisc
      0 b (x.2, θ) ⟨hx.2, mem_univ θ⟩ x.1 hx.1)
    (fun x hx => hN.singleComponentFlowIncrement_periodic m x.2
      ⟨hl.trans hx.2.1, hx.2.2.trans hh⟩ x.1 hx.1) m
    (hS.2.1 (3 / 4 : ℝ)) hM hH
    (hN.singleComponentFlowIncrementCircle hS hT m)
    (fun x hx => hN.singleComponentFlowIncrementCircle_decode hS hT m x hx.1
      ⟨hl.trans hx.2.1, hx.2.2.trans hh⟩)).choose

def N01Properties.singleComponentFlowTower :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ Ioo l h)
      (hN.singleComponentFlowCircle hS hT m) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  let J := hN.singleComponentFlowIncrementTower hS hT m l h hl hh hdisc
  have href : ContDiffOn ℝ ∞ (fun r => C.minusFlow (C.referenceState, 0) m r 0) (Ioo l h) := by
    intro r hr
    exact ((hN.minusFlow_reference_contDiffAt hS hT m (r, 0)
      ⟨hl.trans hr.1, hr.2.trans hh⟩).comp r
        (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  let Kref := smoothDirectionsOfContDiffOn isOpen_Ioo href
  let L : ((StateDirections S × ℝ) × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) ℝ
  let K := Kref.compAffine L 0
    ((sectorNeighborhood_isOpen S base ε ε).prod isOpen_Ioo)
    (fun x hx => by simpa only [zero_add, L, ContinuousLinearMap.coe_snd'] using hx.2)
  let M : ℝ →L[ℝ] H.Space :=
    ContinuousLinearMap.toSpanSingleton ℝ (circleSingletonLinear hH m 1)
  apply (smoothDirectionsAdd J (solveSmoothDirectionsPostcomp K M)).congrOn
  intro x hx
  change hN.singleComponentFlowIncrementCircle hS hT m x +
    (C.minusFlow (C.referenceState, 0) m (0 + L x) 0) • circleSingletonLinear hH m 1 = _
  simp only [L, ContinuousLinearMap.coe_snd', zero_add]
  have heq (c : ℝ) : c • circleSingletonLinear hH m 1 = circleSingletonLinear hH m c := by
    simpa only [smul_eq_mul, mul_one] using ((circleSingletonLinear hH m).map_smul c (1 : ℝ)).symm
  rw [heq]
  rfl

def N01Properties.singleComponentFlowInverseTower :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ Ioo l h)
      (hN.singleComponentFlowInverseCircle hS hT m) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace (H.level n) := fun n => (hH.2.1 n).isComplete.completeSpace_coe
  let J := hN.singleComponentFlowTower hS hT m l h hl hh hdisc
  let K := (smoothTameOn_circlePositiveInversePerturbation hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ => 0)).choose
  exact smoothDirectionsOfJets J.open_domain
    (projectiveCompositionJets (hN.singleComponentFlowCircle hS hT m) J.D K.D)
    (HasProjectiveJetsOn.comp_topological J.open_domain K.open_domain
      J.hasProjectiveJetsOn K.hasProjectiveJetsOn
      (fun x hx => hN.singleComponentFlowCircle_positive hS hT m x hx.1
        ⟨hl.trans hx.2.1, hx.2.2.trans hh⟩))

def N01Properties.minusFlow_inverse_radial_angularJointTower :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ Ioo l h) ×ˢ univ)
      (fun x : ((StateDirections S × ℝ) × ℝ) × ℝ =>
        Function.invFun (C.minusFlow (liftSectorParameter S C x.1.1) m x.1.2) x.2) := by
  let J : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ Ioo l h)
      (hN.singleComponentFlowInverseCircle hS hT m) :=
    hN.singleComponentFlowInverseTower hS hT m l h hl hh hdisc
  have hH (i : ℕ) : 0 < T.H (T.sample i) :=
    (material_circle_sample_weights_pos hT hN.1.1).2 i
  let K : SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ Ioo l h) ×ˢ univ)
      (fun x : ((StateDirections S × ℝ) × ℝ) × ℝ => x.2 + 0 +
        (S.circle (3 / 4 : ℝ)).decode
          (hN.singleComponentFlowInverseCircle hS hT m x.1) m x.2) :=
    circleAffineLiftJointDirections (hS.2.1 (3 / 4 : ℝ)) hH J (fun _ => 0) m
  apply K.congr
  intro x hx
  let a : ℝ := x.2
  let b : ℝ := Function.invFun (C.minusFlow (liftSectorParameter S C x.1.1) m x.1.2) x.2
  have hd : (S.circle (3 / 4 : ℝ)).decode
      (hN.singleComponentFlowInverseCircle hS hT m x.1) m x.2 = b - a :=
    hN.singleComponentFlowInverseCircle_decode hS hT m x.1 hx.1.1
      ⟨hl.trans hx.1.2.1, hx.1.2.2.trans hh⟩ x.2
  exact (congrArg (fun y : ℝ => a + 0 + y) hd).trans
    ((congrArg (fun y : ℝ => y + (b - a)) (add_zero a)).trans
      ((add_comm a (b - a)).trans (sub_add_cancel b a)))

end RadialTower

end ContinuousFlexibility.Statements
