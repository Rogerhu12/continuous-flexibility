import ContinuousFlexibility.Analysis.N01cPhysicalHeightBounds
import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
import ContinuousFlexibility.Scalar.WeightedTowerCalculus

/-!
# Physical mixed jets of one genuine height-valued tower

The existing physical jet functionals evaluate the actual decoded
height. Applying those fixed continuous linear functionals to the
supplied tower retains its genuine parameter derivatives and its exact
material height power. No spatial or parameter neighborhood is changed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
  {U : Set X} {f : X → M.Space}

/-- Spatial regularity and genuine parameter towers of every decoded
physical jet, all on the supplied parameter domain. -/
def n04Realization_heightMixedJetRegularity
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (J : SmoothDirections U f) :
    MixedJetRegularity U (annularOpen D) (fun x => M.decode (f x)) where
  spatial x _ := (hM.2.2.2.1 (f x)).1
  parameter a b p hp :=
    (smoothDirectionsScalarPostcompose J (heightPhysicalJetCLM hT hM a b p hp)).congr
      (fun x _ => heightPhysicalJetCLM_apply hT hM a b p hp (f x))

/-- Evaluation commutes with the whole retained tower, at every order. -/
theorem n04Realization_heightMixedJetRegularity_D
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (J : SmoothDirections U f) (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D)
    (k : ℕ) (x : X) (v : Fin k → X) :
    ((n04Realization_heightMixedJetRegularity hT hM J).parameter a b p hp).D k x v =
      mixedDerivative a b (M.decode (J.D k x v)) p := by
  unfold n04Realization_heightMixedJetRegularity SmoothDirections.congr
  rw [smoothDirectionsScalarPostcompose_apply, heightPhysicalJetCLM_apply]

/-- The exact physical `H^γ` gain survives at every parameter order.
The fixed loss is only enlarged by the original base and the two spatial
derivatives in the existing point-evaluation estimate. -/
theorem n04Realization_heightTower_physicalJets_bound
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    {p : ℕ → Seminorm ℝ X} {base loss : ℕ}
    (J : SmoothDirections U f)
    (hJ : UniformScalarTowerEstimate p M.grading U base loss f J)
    (k s : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ x ∈ U, ∀ v : Fin k → X, ∀ a b : ℕ, a + b ≤ s →
      ∀ q (hq : q ∈ annularOpen D),
        |((n04Realization_heightMixedJetRegularity hT hM J).parameter a b q hq).D k x v| ≤
          C * T.E0 q.1 ^ A * T.H q.1 ^ γ *
            oneHighVariationWeight p base (s + (base + 2 + loss)) x v := by
  obtain ⟨C₀, A, hC₀, hA, hpoint⟩ :=
    sobolevModel_physicalMixedJets_le_E0_grading hT hM s
  obtain ⟨C₁, hC₁, hbound⟩ := hJ k (s + base + 2) (by omega)
  refine ⟨C₀ * C₁, A, mul_nonneg hC₀ hC₁, hA, ?_⟩
  intro x hx v a b hab q hq
  have hgrade : M.grading (s + 2) (J.D k x v) ≤
      M.grading (s + base + 2) (J.D k x v) :=
    gradedSeminorm_monotone _ _ (by omega) _
  have hg : M.grading (s + 2) (J.D k x v) ≤
      C₁ * oneHighVariationWeight p base (s + (base + 2 + loss)) x v := by
    simpa only [tameJetSize, oneHighVariationWeight, Nat.add_assoc] using
      hgrade.trans (hbound x hx v)
  have hfactor : 0 ≤ C₀ * T.E0 q.1 ^ A * T.H q.1 ^ γ :=
    mul_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.2.1.le _))
      (Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _)
  rw [n04Realization_heightMixedJetRegularity_D]
  calc
    _ ≤ C₀ * T.E0 q.1 ^ A * T.H q.1 ^ γ * M.grading (s + 2) (J.D k x v) :=
      hpoint (J.D k x v) a b hab q hq
    _ ≤ C₀ * T.E0 q.1 ^ A * T.H q.1 ^ γ *
        (C₁ * oneHighVariationWeight p base (s + (base + 2 + loss)) x v) :=
      mul_le_mul_of_nonneg_left hg hfactor
    _ = _ := by ring

end ContinuousFlexibility.Analysis
