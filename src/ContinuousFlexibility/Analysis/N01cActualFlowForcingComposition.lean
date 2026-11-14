module

public import ContinuousFlexibility.Analysis.N01cActualFlowForcingBounds
public import ContinuousFlexibility.Analysis.N01cActualFlowSpeedOuterBounds
public import ContinuousFlexibility.Analysis.OneHighCircleFourierComposition

/-!
# Composing the actual forcing speed with the actual ordinary flow

The selected head is the genuine outer speed jet composed with the
supplied trajectory. The circle composition theorem therefore separates
its high norm into the high outer norm and a low outer norm times the
actual flow derivative defect. The linear coefficient is the one-angle
instance of the same head.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- The all-angle singleton choice represents the linear flow coefficient. -/
def flowAngleForcingChoice : FlowForcingChoice 1 :=
  ⟨_root_.OrderedFinpartition.atomic 1, ∅⟩

section CanonicalAccess

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {G Θ : E × PolarPoint → ℝ}
  {P : ℝ} [Fact (0 < P)]
  (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set E) G)
  (hΘ : ContDiff ℝ ∞ Θ)
  (hGp : ∀ q t, Function.Periodic (fun α => G (q, (t, α))) P)
  (hΘp : ∀ q t α, Θ (q, (t, α + P)) = Θ (q, (t, α)) + P)

private theorem n01c_canonicalForcingHead_eq_comp {N : ℕ}
    (q : E) (v : Fin N → E) (t : ℝ) (choice : FlowForcingChoice N) (b : ℕ) :
    let slots : Fin choice.1.length → E × ℝ := fun i => if i ∈ choice.2 then
      ((flowParameterIdentityJet (choice.1.partSize i) (v ∘ choice.1.emb i)).1, 0)
      else (0, 1)
    canonicalFlowForcingFactorJet hG J hΘ hGp hΘp q v t choice 0 b =
      periodicCircleJet
        ((fun η => flowSpeedJointField J choice.1.length q slots (t, η)) ∘
          (fun η => Θ (q, (t, η))))
        (periodic_comp_circleLift
          (flowSpeedJointField_periodic J hGp choice.1.length q slots t) (hΘp q t))
        (((contDiff_flowSpeedJointField J hG choice.1.length q slots).comp
          (contDiff_const.prodMk contDiff_id)).comp
          (hΘ.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)))) b := by
  dsimp only
  ext θ
  induction θ using QuotientAddGroup.induction_on
  simp only [canonicalFlowForcingFactorJet, periodicCircleJet_coe_apply,
    canonicalFlowForcingFactors, flowForcingFactors, Fin.cons_zero,
    flowSelectedSpeedCoefficient, flowSpeedJointField, flowTrajectoryGraph,
    flowInitialSlice, Function.comp_def]

private theorem n01c_flowCircleCoefficient_eq_head
    (hinit : ∀ q α, Θ (q, (0, α)) = α)
    (hflow : ∀ q t α, HasDerivAt (fun r => Θ (q, (r, α)))
      (G (q, (t, Θ (q, (t, α))))) t)
    (stop : ℝ) (n : ℕ) (q : E) (v : Fin (n + 1) → E) (t : ℝ) :
    (flowParameterCircleVariationData hG J hΘ.continuous hinit hflow hGp hΘp
      stop n q v).coefficient t 0 =
      canonicalFlowForcingFactorJet hG J hΘ hGp hΘp q
        (fun _ : Fin 1 => (0 : E)) t flowAngleForcingChoice 0 0 := by
  ext θ
  induction θ using QuotientAddGroup.induction_on
  rename_i α
  let hs : ContDiff ℝ ∞ Θ :=
    contDiff_globalCircleVectorFlow hG hΘ.continuous hinit hflow
  change circleFlowSpeedJet (flowVariationCoefficient G Θ q)
    (contDiff_flowVariationCoefficient hG hs q)
    (flowVariationCoefficient_periodic hG hGp hΘp q) t 0
      (α : AddCircle P) = _
  simp only [circleFlowSpeedJet_coe_apply, canonicalFlowForcingFactorJet,
    periodicCircleJet_coe_apply, iteratedDeriv_zero]
  exact (speedAlongFlowAngularJet_eq_coefficient (Θ := Θ) hG J q (t, α)).symm

end CanonicalAccess

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped Topology ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
  (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
    r ∈ Icc (C.left i) (C.right i) →
      0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
  (m : ℕ)
  (J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
    (componentCosineSpeed D S C m))
  {d : ℕ} (x : AnnularState S × ℝ) (hx : x ∈ stateNeighborhood S C base ε)
  (L : (Fin d → ℝ) →L[ℝ] (AnnularState S × ℝ))

def ordinaryFlowFiniteAngle (t : ℝ) (θ : ℝ) : ℝ :=
  ordinaryFlowFiniteTrajectory x hx L m (0, (t, θ))

include hS hT hA hB hpos J in
theorem contDiff_ordinaryFlowFiniteAngle (t : ℝ) :
    ContDiff ℝ ∞ (ordinaryFlowFiniteAngle m x hx L t) :=
  (contDiff_ordinaryFlowFiniteTrajectory hS hT hA hB hpos m J x hx L).comp
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))

include hS hT hA hB hpos in
theorem ordinaryFlowFiniteAngle_lift (t θ : ℝ) :
    ordinaryFlowFiniteAngle m x hx L t (θ + Real.pi) =
      ordinaryFlowFiniteAngle m x hx L t θ + Real.pi :=
  ordinaryFlowFiniteTrajectory_periodic_lift hS hT hA hB hpos m x hx L 0 t θ

def ordinaryFlowFiniteDefectJet (t : ℝ) (b : ℕ) : C(AddCircle Real.pi, ℝ) :=
  circleLiftDefectJet (ordinaryFlowFiniteAngle m x hx L t)
    (contDiff_ordinaryFlowFiniteAngle hS hT hA hB hpos m J x hx L t)
    (ordinaryFlowFiniteAngle_lift hS hT hA hB hpos m x hx L t) b

/-- Exact composition before any estimate is used. -/
theorem ordinaryFlowForcingFactorJet_head_eq_comp {N : ℕ}
    (v : Fin N → (Fin d → ℝ)) (t : ℝ) (choice : FlowForcingChoice N) (b : ℕ) :
    ordinaryFlowForcingFactorJet hS hT hA hB hpos m J x hx L v t choice 0 b =
      periodicCircleJet
        (ordinaryFlowSpeedOuterField hS hT hA hB hpos m x hx L v t choice ∘
          ordinaryFlowFiniteAngle m x hx L t)
        (periodic_comp_circleLift
          (ordinaryFlowSpeedOuterField_periodic hS hT hA hB hpos m x hx L v t choice)
          (ordinaryFlowFiniteAngle_lift hS hT hA hB hpos m x hx L t))
        ((contDiff_ordinaryFlowSpeedOuterField hS hT hA hB hpos m x hx L v t choice).comp
          (contDiff_ordinaryFlowFiniteAngle hS hT hA hB hpos m J x hx L t)) b := by
  exact n01c_canonicalForcingHead_eq_comp
    (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L)
    (continuousTimeSpeedTowerOfContDiff
      (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L))
    (contDiff_ordinaryFlowFiniteTrajectory hS hT hA hB hpos m J x hx L)
    (ordinaryFlowFiniteSpeed_periodic hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteTrajectory_periodic_lift hS hT hA hB hpos m x hx L)
    0 v t choice b

/-- The only high flow factor in tame composition is its actual
derivative defect at order s-1. The low geometry is fixed separately. -/
theorem ordinaryFlowForcingFactorJet_head_sobolev_le {N : ℕ}
    (v : Fin N → (Fin d → ℝ)) (t : ℝ) (choice : FlowForcingChoice N)
    (s : ℕ) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : ∀ θ, c ≤ deriv (ordinaryFlowFiniteAngle m x hx L t) θ)
    (hlow : circleRealSobolevNorm 3
      (ordinaryFlowFiniteDefectJet hS hT hA hB hpos m J x hx L t 0) ≤ M) :
    circleRealSobolevNorm (s : ℝ)
        (ordinaryFlowForcingFactorJet hS hT hA hB hpos m J x hx L v t choice 0 0) ≤
      circleLiftCompositionConstant Real.pi c M s *
        (circleRealSobolevNorm (s : ℝ)
          (ordinaryFlowSpeedOuterJet hS hT hA hB hpos m x hx L v t choice 0) +
          circleRealSobolevNorm 3
            (ordinaryFlowSpeedOuterJet hS hT hA hB hpos m x hx L v t choice 0) *
              circleRealSobolevNorm ((s - 1 : ℕ) : ℝ)
                (ordinaryFlowFiniteDefectJet hS hT hA hB hpos m J x hx L t 0)) := by
  rw [ordinaryFlowForcingFactorJet_head_eq_comp]
  exact circleLift_sobolev_comp_le s hc hM
    (ordinaryFlowSpeedOuterField hS hT hA hB hpos m x hx L v t choice)
    (ordinaryFlowSpeedOuterField_periodic hS hT hA hB hpos m x hx L v t choice)
    (contDiff_ordinaryFlowSpeedOuterField hS hT hA hB hpos m x hx L v t choice)
    (ordinaryFlowFiniteAngle m x hx L t)
    (contDiff_ordinaryFlowFiniteAngle hS hT hA hB hpos m J x hx L t)
    (ordinaryFlowFiniteAngle_lift hS hT hA hB hpos m x hx L t)
    hlower hlow

/-- The actual linear coefficient is exactly the all-angle singleton
head, independently of the variation order and its parameter directions. -/
theorem ordinaryFlowCircleVariationData_coefficient_eq_head
    (n : ℕ) (v : Fin (n + 1) → (Fin d → ℝ)) (t : ℝ) :
    (ordinaryFlowCircleVariationData hS hT hA hB hpos m J x hx L n v).coefficient t 0 =
      ordinaryFlowForcingFactorJet hS hT hA hB hpos m J x hx L
        (fun _ : Fin 1 => (0 : Fin d → ℝ)) t flowAngleForcingChoice 0 0 := by
  exact n01c_flowCircleCoefficient_eq_head
    (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L)
    (continuousTimeSpeedTowerOfContDiff
      (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L))
    (contDiff_ordinaryFlowFiniteTrajectory hS hT hA hB hpos m J x hx L)
    (ordinaryFlowFiniteSpeed_periodic hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteTrajectory_periodic_lift hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteTrajectory_initial hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteTrajectory_hasDerivAt hS hT hA hB hpos m x hx L)
    1 n 0 v t

end ContinuousFlexibility.Statements
