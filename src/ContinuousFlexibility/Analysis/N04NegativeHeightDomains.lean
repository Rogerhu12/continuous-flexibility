import ContinuousFlexibility.Analysis.N04NegativeHeightCurrentData

/-! Domain restrictions shared by scalar compositions and products. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- Restrict the actual mixed towers without choosing new derivatives. -/
def MixedJetRegularity.height_restrict
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U U' : Set X} {Ω : Set PolarPoint} {F : X → PolarPoint → ℝ}
    (R : MixedJetRegularity U Ω F) (hU' : IsOpen U') (hsub : U' ⊆ U) :
    MixedJetRegularity U' Ω F where
  spatial x hx := R.spatial x (hsub hx)
  parameter a b q hq := (R.parameter a b q hq).restrict hU' hsub

/-- The two defining sector bounds control the sum parameter grading. -/
theorem n04NegativeHeight_parameterGrading_le_one
    {S : PhysicalSpacesData} {b : ℕ} {e : ℝ} (he : e ≤ 1 / 2) {z : Parameter S}
    (hz : z ∈ sectorNeighborhood S b e e) : parameterGrading S b z ≤ 1 := by
  change sectorGrading S b z.1 + ‖z.2‖ ≤ 1
  have hscalar : ‖z.2‖ ≤ e := (Real.norm_eq_abs z.2).trans_le hz.2.le
  have he₂ : e + e ≤ 1 := by linarith
  exact (add_le_add hz.1.le hscalar).trans he₂

end ContinuousFlexibility.Analysis
