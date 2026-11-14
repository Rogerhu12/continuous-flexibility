import ContinuousFlexibility.Analysis.N04RealizationHeightTowerJets

/-!
# Genuine mixed jets of the actual decoded physical field

The equality is an equality of the complete physical functions on the
same parameter neighborhood. It therefore identifies every spatial jet
before the retained height tower is evaluated. The material exponent and
the fixed loss are preserved without a new neighborhood choice.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
  {U : Set X} {f : X → M.Space} {g : X → PolarPoint → ℝ}

/-- Transport the decoded height tower to its actual physical field.
The parameter derivatives are unchanged, since the entire spatial
function is identified before differentiation. -/
def n04Realization_heightFieldMixedJets
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (J : SmoothDirections U f)
    (heq : ∀ x ∈ U, M.decode (f x) = g x) :
    MixedJetRegularity U (annularOpen D) g where
  spatial x hx := by
    rw [← heq x hx]
    exact (hM.2.2.2.1 (f x)).1
  parameter a b q hq :=
    ((n04Realization_heightMixedJetRegularity hT hM J).parameter a b q hq).congr
      (fun x hx => congrArg (fun F => mixedDerivative a b F q) (heq x hx))

/-- The actual physical field inherits the exact all-order physical
height bound of its supplied decoded tower. -/
theorem n04Realization_heightFieldMixedJets_bound
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    {p : ℕ → Seminorm ℝ X} {base loss : ℕ}
    (J : SmoothDirections U f)
    (hJ : UniformScalarTowerEstimate p M.grading U base loss f J)
    (heq : ∀ x ∈ U, M.decode (f x) = g x) (k s : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ x ∈ U, ∀ v : Fin k → X, ∀ a b : ℕ, a + b ≤ s →
      ∀ q (hq : q ∈ annularOpen D),
        |((n04Realization_heightFieldMixedJets hT hM J heq).parameter a b q hq).D
            k x v| ≤ C * T.E0 q.1 ^ A * T.H q.1 ^ γ *
              oneHighVariationWeight p base (s + (base + 2 + loss)) x v := by
  exact n04Realization_heightTower_physicalJets_bound hT hM J hJ k s

end ContinuousFlexibility.Analysis
