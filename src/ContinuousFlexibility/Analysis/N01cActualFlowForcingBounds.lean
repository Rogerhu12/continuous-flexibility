module

public import ContinuousFlexibility.Analysis.N01cActualFlowCircleData
public import ContinuousFlexibility.Analysis.N01cFlowVariationForcingBounds

/-!
# Actual ordinary-flow forcing factors and their Sobolev estimate

The factors below come from the compressed finite affine plot of the
supplied ordinary trajectories. Their speed factor is the original
cosine speed tower times the fixed time derivative. Every nonconstant
lower factor is an actual lower state derivative of the same flow.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open scoped ContDiff

section CanonicalFactorEvaluation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {G Θ : E × PolarPoint → ℝ} {P : ℝ} [Fact (0 < P)]

private theorem n01c_canonicalForcingFactor_head_eq
    (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set E) G)
    (hΘ : ContDiff ℝ ∞ Θ)
    (hGp : ∀ q t, Function.Periodic (fun α => G (q, (t, α))) P)
    (hΘp : ∀ q t α, Θ (q, (t, α + P)) = Θ (q, (t, α)) + P)
    {N : ℕ} (q : E) (v : Fin N → E) (t : ℝ) (choice : FlowForcingChoice N)
    (A Ψ : ℝ → ℝ)
    (hspeed : ∀ α, J.D choice.1.length (q, (t, α))
      (fun i => if i ∈ choice.2 then
        ((flowParameterIdentityJet (choice.1.partSize i) (v ∘ choice.1.emb i)).1, 0)
        else (0, 1)) = A α)
    (htrajectory : ∀ α, Θ (q, (t, α)) = Ψ α)
    (b : ℕ) (θ : ℝ) :
    canonicalFlowForcingFactorJet hG J hΘ hGp hΘp q v t choice 0 b
        (θ : AddCircle P) =
      iteratedDeriv b (fun α => A (Ψ α)) θ := by
  classical
  rw [canonicalFlowForcingFactorJet, periodicCircleJet_coe_apply]
  apply congrArg (fun f : ℝ → ℝ => iteratedDeriv b f θ)
  funext α
  change J.D choice.1.length (q, (t, Θ (q, (t, α)))) _ = A (Ψ α)
  rw [hspeed, htrajectory]

private theorem n01c_canonicalForcingFactor_lower_eq
    (hG : ContDiff ℝ ∞ G) (J : ContinuousTimeSpeedTower (univ : Set E) G)
    (hΘ : ContDiff ℝ ∞ Θ)
    (hGp : ∀ q t, Function.Periodic (fun α => G (q, (t, α))) P)
    (hΘp : ∀ q t α, Θ (q, (t, α + P)) = Θ (q, (t, α)) + P)
    {N : ℕ} (q : E) (v : Fin N → E) (t : ℝ) (choice : FlowForcingChoice N)
    (i : Fin choice.1.length) (hi : i ∉ choice.2) (hk : choice.1.partSize i < N)
    (b : ℕ) (θ : ℝ) {value : ℝ}
    (hvalue : iteratedDeriv b (fun α =>
      flowParameterField Θ (choice.1.partSize i) q (v ∘ choice.1.emb i) (t, α)) θ =
        value) :
    canonicalFlowForcingFactorJet hG J hΘ hGp hΘp q v t choice i.succ b
      (θ : AddCircle P) = value := by
  classical
  rw [canonicalFlowForcingFactorJet, periodicCircleJet_coe_apply]
  simp only [canonicalFlowForcingFactors, flowForcingFactors, Fin.cons_succ,
    flowSelectedLowerFactor, if_neg hi, lowerStateVariation, dif_pos hk]
  exact hvalue

end CanonicalFactorEvaluation

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

/-- Canonical circle jets of the actual factors, at the centre of the
finite affine plot. These use no order-dependent state compression. -/
def ordinaryFlowForcingFactorJet {N : ℕ} (v : Fin N → (Fin d → ℝ))
    (t : ℝ) (choice : FlowForcingChoice N) (i : Fin (choice.1.length + 1))
    (b : ℕ) : C(AddCircle Real.pi, ℝ) :=
  canonicalFlowForcingFactorJet
    (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L)
    (continuousTimeSpeedTowerOfContDiff
      (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L))
    (contDiff_ordinaryFlowFiniteTrajectory hS hT hA hB hpos m J x hx L)
    (ordinaryFlowFiniteSpeed_periodic hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteTrajectory_periodic_lift hS hT hA hB hpos m x hx L)
    0 v t choice i b

/-- The first factor is exactly the original actual speed jet, evaluated
along the supplied trajectory. The only time multiplier is the one
derivative of the fixed compact time map. -/
theorem ordinaryFlowForcingFactorJet_head {N : ℕ}
    (v : Fin N → (Fin d → ℝ)) (t : ℝ) (choice : FlowForcingChoice N)
    (b : ℕ) (θ : ℝ) :
    ordinaryFlowForcingFactorJet hS hT hA hB hpos m J x hx L v t choice 0 b
        (θ : AddCircle Real.pi) =
      iteratedDeriv b (fun η =>
        deriv (circleFlowCompactTime 0 Real.pi) t *
          J.D choice.1.length
            (x, (circleFlowCompactTime 0 Real.pi t,
              ordinaryFlowInCosineTime C m (x, (circleFlowCompactTime 0 Real.pi t, η))))
            (fun i => flowStateAngleMap L
              (if i ∈ choice.2 then
                ((flowParameterIdentityJet (choice.1.partSize i)
                  (v ∘ choice.1.emb i)).1, 0) else (0, 1)))) θ := by
  exact n01c_canonicalForcingFactor_head_eq
    (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L)
    (continuousTimeSpeedTowerOfContDiff
      (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L))
    (contDiff_ordinaryFlowFiniteTrajectory hS hT hA hB hpos m J x hx L)
    (ordinaryFlowFiniteSpeed_periodic hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteTrajectory_periodic_lift hS hT hA hB hpos m x hx L)
    (0 : Fin d → ℝ) v t choice
    (fun α => deriv (circleFlowCompactTime 0 Real.pi) t *
      J.D choice.1.length (x, (circleFlowCompactTime 0 Real.pi t, α))
        (fun i => flowStateAngleMap L (if i ∈ choice.2 then
          ((flowParameterIdentityJet (choice.1.partSize i) (v ∘ choice.1.emb i)).1, 0)
          else (0, 1))))
    (fun α => ordinaryFlowInCosineTime C m (x, (circleFlowCompactTime 0 Real.pi t, α)))
    (fun α => ordinaryFlowFiniteSpeedTower_D_apply hS hT hA hB hpos m J x hx L
      choice.1.length t α (fun i => if i ∈ choice.2 then
        ((flowParameterIdentityJet (choice.1.partSize i) (v ∘ choice.1.emb i)).1, 0)
        else (0, 1)))
    (fun α => ordinaryFlowFiniteTrajectory_zero x hx L m (t, α)) b θ

/-- Every surviving lower factor is a strict lower-order actual state
jet; all its angular derivatives identify with the same canonical tower. -/
theorem ordinaryFlowForcingFactorJet_lower {N : ℕ}
    (v : Fin N → (Fin d → ℝ)) (t : ℝ) (choice : FlowForcingChoice N)
    (i : Fin choice.1.length) (hi : i ∉ choice.2) (hk : choice.1.partSize i < N)
    (b : ℕ) (θ : ℝ) :
    ordinaryFlowForcingFactorJet hS hT hA hB hpos m J x hx L v t choice i.succ b
        (θ : AddCircle Real.pi) =
      (ordinaryFlowAngularStateSmoothDirections hS hT hA hB hpos m J
        (rootCosinePath_mem_Icc (hA.2.2.1.1 m).2.1.le
          (circleFlowCompactTime 0 Real.pi t)) b θ).D (choice.1.partSize i) x (fun j => L (v (choice.1.emb i j))) := by
  exact n01c_canonicalForcingFactor_lower_eq
    (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L)
    (continuousTimeSpeedTowerOfContDiff
      (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L))
    (contDiff_ordinaryFlowFiniteTrajectory hS hT hA hB hpos m J x hx L)
    (ordinaryFlowFiniteSpeed_periodic hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteTrajectory_periodic_lift hS hT hA hB hpos m x hx L)
    (0 : Fin d → ℝ) v t choice i hi hk b θ
    (ordinaryFlowFiniteTrajectory_parameterAngularJet
      hS hT hA hB hpos m J x hx L (choice.1.partSize i) b t θ (v ∘ choice.1.emb i))

theorem ordinaryFlowForcingFactorJet_selected {N : ℕ}
    (v : Fin N → (Fin d → ℝ)) (t : ℝ) (choice : FlowForcingChoice N)
    (i : Fin choice.1.length) (hi : i ∈ choice.2) (b : ℕ) (θ : ℝ) :
    ordinaryFlowForcingFactorJet hS hT hA hB hpos m J x hx L v t choice i.succ b
        (θ : AddCircle Real.pi) = iteratedDeriv b (fun _ : ℝ => (1 : ℝ)) θ := by
  rw [ordinaryFlowForcingFactorJet, canonicalFlowForcingFactorJet,
    periodicCircleJet_coe_apply]
  simp only [canonicalFlowForcingFactors, flowForcingFactors, Fin.cons_succ,
    flowSelectedLowerFactor, if_pos hi]

theorem ordinaryFlowForcingFactorJet_large {N : ℕ}
    (v : Fin N → (Fin d → ℝ)) (t : ℝ) (choice : FlowForcingChoice N)
    (i : Fin choice.1.length) (hi : i ∉ choice.2) (hk : N ≤ choice.1.partSize i)
    (b : ℕ) (θ : ℝ) :
    ordinaryFlowForcingFactorJet hS hT hA hB hpos m J x hx L v t choice i.succ b
        (θ : AddCircle Real.pi) = 0 := by
  classical
  rw [ordinaryFlowForcingFactorJet, canonicalFlowForcingFactorJet,
    periodicCircleJet_coe_apply]
  simp only [canonicalFlowForcingFactors, flowForcingFactors, Fin.cons_succ,
    flowSelectedLowerFactor, if_neg hi, lowerStateVariation,
    dif_neg (Nat.not_lt.mpr hk), zeroStateVariation, ContinuousMultilinearMap.zero_apply,
    iteratedDeriv_const, ite_self]

/-- The actual forcing of the actual positive ordinary-flow variation
has one high factor in every explicitly indexed product. -/
theorem ordinaryFlowCircleVariationData_forcingNorm_le
    (n : ℕ) (v : Fin (n + 1) → (Fin d → ℝ)) (t : ℝ) (s : ℕ) :
    (ordinaryFlowCircleVariationData hS hT hA hB hpos m J x hx L n v).forcingNorm s t ≤
      (2 : ℝ) ^ (s + 1) *
        ∑ choice : FlowForcingChoice (n + 1),
          circleProductSobolevConstant Real.pi choice.1.length s *
            ∑ j : Fin (choice.1.length + 1),
              circleRealSobolevNorm (s : ℝ)
                (ordinaryFlowForcingFactorJet hS hT hA hB hpos m J x hx L v t choice j 0) *
              ∏ i ∈ Finset.univ.erase j,
                circleRealSobolevNorm 1
                  (ordinaryFlowForcingFactorJet hS hT hA hB hpos m J x hx L v t choice i 0) := by
  exact flowParameterCircleVariationData_forcingNorm_le
    (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L)
    (continuousTimeSpeedTowerOfContDiff
      (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L))
    (continuous_ordinaryFlowFiniteTrajectory hS hT hA hB hpos m J x hx L)
    (ordinaryFlowFiniteTrajectory_initial hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteTrajectory_hasDerivAt hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteSpeed_periodic hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteTrajectory_periodic_lift hS hT hA hB hpos m x hx L)
    1 n 0 v t s

end ContinuousFlexibility.Statements
