module

public import ContinuousFlexibility.Analysis.N04RealizationHeightFieldJets
public import ContinuousFlexibility.Analysis.N04RealizationHeightPowerBounds

/-!
# One interpolation choice for actual decoded fields

The input and output orders are selected before the parameter domain,
the retained height field, and its actual physical formula. This permits
several actual fields with the same original uniform tower bounds to use
one interpolation choice and one subsequently restricted neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- All actual fields decoded from a uniform height tower share the
same interpolation indices. The full height gain remains at order zero. -/
theorem n04Realization_heightField_spatialPower_choices
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hIp : HasInterpolation p)
    (oldBase oldLoss : ℕ) (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ B L : ℕ, oldBase ≤ B ∧
      ∀ U : Set X, ∀ f : X → M.Space, ∀ g : X → PolarPoint → ℝ,
      ∀ J : SmoothDirections U f,
      UniformScalarTowerEstimate p M.grading U oldBase oldLoss f J →
      (∀ x ∈ U, M.decode (f x) = g x) →
      ∃ RF : MixedJetRegularity U (annularOpen D) g,
      ∀ K s : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
        ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
        ∀ q ∈ annularOpen D,
        ∀ Jq : SmoothDirections U (fun x => mixedDerivative a b (g x) q),
        ∀ x ∈ U, p B x ≤ 1 →
        ∀ v : Fin k → X, (∀ i, p B (v i) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p (s + L) x ≤ R →
          (∀ i, p (s + L) (v i) ≤ R) →
          ‖Jq.D k x v‖ ≤ C * T.E0 q.1 ^ A * T.H q.1 ^ γ *
            R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  apply exists_base_ge_of_spatialPower_continuation p hp hIp
    oldBase (oldBase + 2 + oldLoss)
  intro B L hB hI U f g J hJ heq
  let RF : MixedJetRegularity U (annularOpen D) g :=
    n04Realization_heightFieldMixedJets hT hM J heq
  refine ⟨RF, ?_⟩
  have hraw := n04Realization_oneHigh_spatialPower_prefix hp (0 : X) hB RF
    (fun q hq => Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le γ)
    (fun q hq => hE q.1 hq.1) hI (by
      intro k n
      obtain ⟨C, A, hC, hA, hb⟩ :=
        n04Realization_heightFieldMixedJets_bound hT hM J hJ heq k n
      refine ⟨C, A, hC, hA, fun a b hab q hq x hx v => ?_⟩
      simpa only [sub_zero] using hb x hx v a b hab q hq)
  simpa only [sub_zero] using hraw

end ContinuousFlexibility.Analysis
