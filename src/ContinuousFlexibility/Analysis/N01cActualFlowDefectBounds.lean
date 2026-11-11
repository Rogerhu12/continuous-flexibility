import ContinuousFlexibility.Analysis.N01cActualFlowForcingComposition
import ContinuousFlexibility.Analysis.N01cOrdinaryFlowZeroAngularBounds

/-!
# The actual derivative defect after the fixed compact time map

The finite parameter plot has centre equal to the original state.
Consequently its angle defect is the original ordinary-flow defect at
the compact time, even when the two constructions use different
neighbourhood witnesses. The zero-parameter growth estimate therefore
restricts to every smaller neighbourhood without changing its loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- Transport whole families without specializing their large index types. -/
theorem n01c_transfer_positiveConstants {I : Type*}
    (P Q : I → ℝ → Prop)
    (hP : ∀ i, ∃ K : ℝ, 0 < K ∧ P i K)
    (hstep : ∀ i K, 0 < K → P i K → Q i K) :
    ∀ i, ∃ K : ℝ, 0 < K ∧ Q i K := by
  intro i
  obtain ⟨K, hK, hPK⟩ := hP i
  exact ⟨K, hK, hstep i K hK hPK⟩

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base base₀ : ℕ} {ε ε₀ : ℝ}
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

/-- Equality of actual circle functions; the neighbourhood certificates
and the finite parameter chart do not affect the value. -/
theorem ordinaryFlowFiniteDefectJet_eq_component
    (hB₀ : N01PartB D S C base₀ ε₀)
    (hx₀ : x ∈ stateNeighborhood S C base₀ ε₀)
    (hGx : ContDiff ℝ ∞
      (fun p : PolarPoint => componentCosineSpeed D S C m (x, p)))
    (t : ℝ) (b : ℕ) :
    ordinaryFlowFiniteDefectJet hS hT hA hB hpos m J x hx L t b =
      componentCosineFlowDefectJet hS hT hA hB₀ hx₀ m hGx
        (circleFlowCompactTime 0 Real.pi t) b := by
  ext θ
  induction θ using QuotientAddGroup.induction_on
  rename_i θ
  change circleLiftDefectJet _ _ _ b (θ : AddCircle Real.pi) =
    circleFlowDefectJet _ _ _ _ _ _ b (θ : AddCircle Real.pi)
  rw [circleLiftDefectJet_coe_apply_eq,
    circleFlowDefectJet_coe_apply _ _ _ _ _
      (circleFlowCompactTime_mem Real.pi_pos.le t)]
  apply congrArg (fun f : ℝ → ℝ =>
    iteratedDeriv (b + 1) f θ - if b = 0 then 1 else 0)
  funext η
  exact ordinaryFlowFiniteTrajectory_zero x hx L m (t, η)

/-- The proved zero-parameter estimate on one neighbourhood controls all
finite plots on a smaller neighbourhood, with the same uniform constants. -/
theorem ordinaryFlowFiniteDefectJet_sobolev_growth
    (hB₀ : N01PartB D S C base₀ ε₀)
    (hGs : ∀ z ∈ stateNeighborhood S C base₀ ε₀, ∀ i,
      ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C i (z, p)))
    (loss d₀ : ℕ)
    (hQ : OrdinaryFlowZeroAngularGrowth hS hT hA hB₀ hGs loss d₀)
    (hsub : stateNeighborhood S C base ε ⊆ stateNeighborhood S C base₀ ε₀) :
    ∀ s : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ m, ∀ J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
        (componentCosineSpeed D S C m),
      ∀ d : ℕ, ∀ x : AnnularState S × ℝ, ∀ hx : x ∈ stateNeighborhood S C base ε,
      ∀ L : (Fin d → ℝ) →L[ℝ] (AnnularState S × ℝ),
      ∀ t : ℝ, circleRealSobolevNorm (s : ℝ)
        (ordinaryFlowFiniteDefectJet hS hT hA hB hpos m J x hx L t 0) ≤
          K * (1 + pairGrading (stateGrading S) realGrading
            (s + 1 + loss + d₀) (x - (C.referenceState, 0))) := by
  refine n01c_transfer_positiveConstants _ _ hQ.1 ?_
  intro s K hK hbound m J d x hx L t
  rw [ordinaryFlowFiniteDefectJet_eq_component hS hT hA hB hpos m J x hx L
    hB₀ (hsub hx) (hGs x (hsub hx) m)]
  exact hbound x (hsub hx) m (circleFlowCompactTime 0 Real.pi t)
    (circleFlowCompactTime_mem Real.pi_pos.le t)

end ContinuousFlexibility.Statements
