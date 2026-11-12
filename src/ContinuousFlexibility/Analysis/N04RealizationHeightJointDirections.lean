import ContinuousFlexibility.Analysis.N04RealizationHeightFieldJets
import ContinuousFlexibility.Analysis.N01cMaterialAbsorption
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine
import ContinuousFlexibility.Analysis.SmoothDirectionsSpatialJoint
import ContinuousFlexibility.Analysis.MixedDerivativeHierarchy
import ContinuousFlexibility.Analysis.N01ReturnVelocitySpatialTower

/-!
# Actual height fields jointly in state and physical position

The exact positive material height factor bounds every fixed physical
jet uniformly on the annulus. It is used here only to obtain the
qualitative uniform seminorm bounds required by the existing joint
calculus. The sharper weighted estimate remains available separately.
Both physical coordinates are then joined to the original parameter
tower on its unchanged convex neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
  {U : Set X} {f : X → M.Space} {g : X → PolarPoint → ℝ}

/-- The genuine physical tower has one continuous seminorm bound for
each parameter order, uniform in the whole physical point. This weaker
bound is used for joint regularity only. -/
theorem n04Realization_heightField_uniformSeminormBounds
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M) (hγ : 0 < γ)
    {p : ℕ → Seminorm ℝ X} (hp : Monotone p) (hcp : ∀ n, Continuous (p n))
    {base loss : ℕ} (J : SmoothDirections U f)
    (hJ : UniformScalarTowerEstimate p M.grading U base loss f J)
    (heq : ∀ x ∈ U, M.decode (f x) = g x) (a b : ℕ) :
    UniformScalarJetSeminormBounds
      (fun q : annularOpen D =>
        (n04Realization_heightFieldMixedJets hT hM J heq).parameter a b q q.property) := by
  intro k
  obtain ⟨C, A, hC, _hA, hb⟩ :=
    n04Realization_heightFieldMixedJets_bound hT hM J hJ heq k (a + b)
  obtain ⟨B, hB, hweight⟩ := materialHeight_E0_weight_bounded hT hγ A
  let high : ℕ := a + b + (base + 2 + loss)
  let q : Seminorm ℝ X := p high
  have hbase : p base ≤ q := hp (by dsimp only [high]; omega)
  refine ⟨q, C * B * ((k : ℝ) + 1), hcp high, by positivity, ?_⟩
  intro y x hx v
  have hCB : 0 ≤ C * B := mul_nonneg hC hB.le
  have hw := oneHighVariationWeight_le_seminorm_product p q base high
    hbase le_rfl x v
  calc
    _ ≤ C * T.E0 y.val.1 ^ A * T.H y.val.1 ^ γ *
        oneHighVariationWeight p base high x v :=
      hb x hx v a b le_rfl y.val y.property
    _ = C * (T.H y.val.1 ^ γ * T.E0 y.val.1 ^ A) *
        oneHighVariationWeight p base high x v := by ring
    _ ≤ C * B * oneHighVariationWeight p base high x v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hweight y.val.1 y.property.1) hC)
        (oneHighVariationWeight_nonneg p base high x v)
    _ ≤ C * B * (((k : ℝ) + 1) * (1 + q x) * ∏ i, q (v i)) :=
      mul_le_mul_of_nonneg_left hw hCB
    _ = _ := by ring

/-- The joint physical tower uses the caller's unchanged state domain.
The existing local spatial calculus supplies both coordinate joins. -/
def n04Realization_heightFieldJointDirections
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M) (hγ : 0 < γ)
    {p : ℕ → Seminorm ℝ X} (hp : Monotone p) (hcp : ∀ n, Continuous (p n))
    {base loss : ℕ} (J : SmoothDirections U f)
    (hJ : UniformScalarTowerEstimate p M.grading U base loss f J)
    (heq : ∀ x ∈ U, M.decode (f x) = g x) (hconv : Convex ℝ U) :
    SmoothDirections (U ×ˢ annularOpen D) (fun x : X × PolarPoint => g x.1 x.2) := by
  let RF : MixedJetRegularity U (annularOpen D) g :=
    n04Realization_heightFieldMixedJets hT hM J heq
  have hΩ : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  let K := mixedScalarSpatialJointDirections RF.parameter J.open_domain hconv isOpen_Ioo
    (fun a b x hx => (contDiffOn_mixedDerivative hΩ (RF.spatial x hx) a b).continuousOn)
    (n04Realization_heightField_uniformSeminormBounds hT hM hγ hp hcp J hJ heq)
    (fun a b q hq x hx => mixedDerivative_hasDerivAt_radial hΩ (RF.spatial x hx) a b hq)
    (fun a b q hq x hx => mixedDerivative_hasDerivAt_angular hΩ (RF.spatial x hx) a b hq)
    (convex_Ioo D.a D.b)
  let L := K.compLinear (parameterSpatialAssociation X) (J.open_domain.prod hΩ)
    (fun x hx => ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩)
  exact L.congrOn (fun x _ => by
    simp only [mixedDerivative, iteratedDeriv_zero, Prod.eta])

end ContinuousFlexibility.Analysis
