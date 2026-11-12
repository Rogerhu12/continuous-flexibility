import ContinuousFlexibility.Analysis.N04RealizationFullWeightProductOneHigh
import ContinuousFlexibility.Analysis.N04RealizationHeightMovingEvaluation

/-!
# The literal canonical source as the same two raw factors

The fixed unit map is applied to the same inverse chart and source
factor. The whole-function identity holds on the actual open domain
and therefore transports every spatial and parameter derivative.
No chart, height, field, sample or neighborhood is selected again.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_canonicalSource_eq_product
    {S : PhysicalSpacesData} (K : CanonicalData S)
    (z : X → AnnularState S × ℝ) (m : ℕ) (ψ : PolarPoint → PolarPoint)
    (g : X → PolarPoint → ℝ) :
    (fun x q => canonicalSource S K (z x) m (g x) (ψ q)) =
      (fun x q => canonicalSource S K (z x) m (fun _ => 1) (ψ q) *
        g x (K.inverseChart (z x) m (ψ q))) := by
  funext x q
  simp only [canonicalSource, mul_one, div_eq_mul_inv]
  ring

/-- The actual canonical field has the product tower on the same open
unit domain, so the full-weight raw product estimate applies to it. -/
def n04Realization_canonicalSource_mixedRegularity
    {S : PhysicalSpacesData} (K : CanonicalData S)
    (z : X → AnnularState S × ℝ) (m : ℕ) (ψ : PolarPoint → PolarPoint)
    (g : X → PolarPoint → ℝ)
    {U : Set X} {Ω : Set PolarPoint} (hU : IsOpen U) (hΩ : IsOpen Ω)
    (RF : MixedJetRegularity U Ω
      (fun x q => canonicalSource S K (z x) m (fun _ => 1) (ψ q)))
    (RG : MixedJetRegularity U Ω
      (fun x q => g x (K.inverseChart (z x) m (ψ q)))) :
    MixedJetRegularity U Ω
      (fun x q => canonicalSource S K (z x) m (g x) (ψ q)) := by
  rw [n04Realization_canonicalSource_eq_product K z m ψ g]
  exact RF.mul RG hU hΩ

end ContinuousFlexibility.Analysis
