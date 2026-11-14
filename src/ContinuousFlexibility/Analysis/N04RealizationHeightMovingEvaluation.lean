module

public import ContinuousFlexibility.Analysis.N04RealizationHeightJointDirections
public import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph

/-!
# Actual physical fields evaluated at a moving inverse point

The original state is paired with the genuine moving point. Composition
with the previously constructed joint physical tower uses the existing
projective chain rule on that same domain. Multiplication by the actual
source factor then yields the literal canonical source.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {U : Set X}

/-- Evaluate the same decoded physical field at the supplied genuine
moving point, retaining the original parameter neighborhood. -/
def n04Realization_heightFieldMovingDirections
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M) (hγ : 0 < γ)
    {p : ℕ → Seminorm ℝ X} (hp : Monotone p) (ht : WithSeminorms p)
    {base loss : ℕ} {f : X → M.Space} {g : X → PolarPoint → ℝ}
    (J : SmoothDirections U f)
    (hJ : UniformScalarTowerEstimate p M.grading U base loss f J)
    (heq : ∀ x ∈ U, M.decode (f x) = g x) (hconv : Convex ℝ U)
    {φ : X → PolarPoint} (Jφ : SmoothDirections U φ)
    (hφ : MapsTo φ U (annularOpen D)) :
    SmoothDirections U (fun x => g x (φ x)) := by
  letI : LocallyConvexSpace ℝ X := ht.toLocallyConvexSpace
  let K := n04Realization_heightFieldJointDirections hT hM hγ hp
    ht.continuous_seminorm J hJ heq hconv
  let Jid := (smoothDirectionsLinear (ContinuousLinearMap.id ℝ X)).restrict
    J.open_domain (subset_univ U)
  let G := smoothDirectionsUniformProd Jid Jφ
  have hmap : MapsTo (fun x => (x, φ x)) U (U ×ˢ annularOpen D) :=
    fun x hx => ⟨hx, hφ hx⟩
  exact smoothDirections_realCompTVS G K hmap

/-- The actual canonical source is the actual pullback times the same
source factor. No chart, height, or sample is reselected. -/
def n04Realization_canonicalSourceDirections
    {S : PhysicalSpacesData} (K : CanonicalData S)
    (z : X → AnnularState S × ℝ) (m : ℕ) (y : PolarPoint)
    (g : X → PolarPoint → ℝ)
    (Jg : SmoothDirections U (fun x => g x (K.inverseChart (z x) m y)))
    (JF : SmoothDirections U
      (fun x => canonicalSource S K (z x) m (fun _ => 1) y)) :
    SmoothDirections U (fun x => canonicalSource S K (z x) m (g x) y) := by
  apply (smoothDirections_realMul JF Jg).congr
  intro x _
  simp only [canonicalSource, mul_one, div_eq_mul_inv]
  ring

end ContinuousFlexibility.Analysis
