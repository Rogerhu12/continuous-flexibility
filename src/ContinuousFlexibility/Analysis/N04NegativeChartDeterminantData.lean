import ContinuousFlexibility.Analysis.N04NegativeChartJacobianIdentities
import ContinuousFlexibility.Analysis.N04SourceColumnsDerivative
import ContinuousFlexibility.Analysis.N04SourceColumnsMultiplication
import ContinuousFlexibility.Analysis.N04SourceColumnsScalarLinear

/-!
# Current data for the forward first-jet determinant polynomial

Spatial differentiation adds only a fixed loss. The two products choose
one common low order and neighborhood before every later derivative order.
The width ratio is a fixed coefficient at the original material sample.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {cell : ℕ → ℕ} {base : ℕ} {ε : ℝ}
  {R A : Parameter S → ℕ → PolarPoint → ℝ} {R₀ A₀ : ℕ → PolarPoint → ℝ}

theorem n04NegativeChart_referenceDeterminant_data
    (hR : N04SourceReferenceData T cell R₀) (hA : N04SourceReferenceData T cell A₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (c : ℕ → ℝ) (hc : ∃ B : ℝ, 0 < B ∧ ∀ m,
      |c m| ≤ B * T.E0 (T.sample (cell m)) ^ B) :
    N04SourceReferenceData T cell (n04NegativeChartDeterminant c R₀ A₀) := by
  have h1 := n04SourceColumns_reference_one hE
  have hB := h1.sourceColumns_add (hA.sourceColumns_mixedDerivative 0 1) hE
  have hleft := (hR.sourceColumns_mixedDerivative 1 0).sourceColumns_mul hB hE
  have hright := (hA.sourceColumns_mixedDerivative 1 0).sourceColumns_mul
    (hR.sourceColumns_mixedDerivative 0 1) hE
  exact (hleft.sourceColumns_sub hright hE).sourceColumns_constMul hE c hc

/-- Genuine coordinate data imply genuine determinant data, with no
determinant derivative estimate among the hypotheses. -/
theorem n04NegativeChart_currentDeterminant_data
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hI : HasInterpolation (parameterGrading S))
    (hR : CurrentJetDataOn S T cell (fun _ => True) base ε R R₀)
    (hA : CurrentJetDataOn S T cell (fun _ => True) base ε A A₀)
    (hR₀ : N04SourceReferenceData T cell R₀) (hA₀ : N04SourceReferenceData T cell A₀)
    (c : ℕ → ℝ) (hc : ∃ B : ℝ, 0 < B ∧ ∀ m,
      |c m| ≤ B * T.E0 (T.sample (cell m)) ^ B) :
    ∃ b : ℕ, ∃ δ : ℝ, base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧
      CurrentJetDataOn S T cell (fun _ => True) b δ
        (fun z => n04NegativeChartDeterminant c (R z) (A z))
        (n04NegativeChartDeterminant c R₀ A₀) := by
  have hE₀ (m : ℕ) : 0 ≤ T.E0 (T.sample (cell m)) := zero_le_one.trans (hE m)
  have hH (m : ℕ) : 0 ≤ T.H (T.sample (cell m)) :=
    (hT.2.1 _ (materialSample_mem_interval hD hT (cell m))).2.1.le
  have h1₀ := n04SourceColumns_reference_one hE
  have hAr := hR₀.sourceColumns_mixedDerivative 1 0
  have hBr := h1₀.sourceColumns_add (hA₀.sourceColumns_mixedDerivative 0 1) hE
  have hCr := hA₀.sourceColumns_mixedDerivative 1 0
  have hDr := hR₀.sourceColumns_mixedDerivative 0 1
  have h1 := h1₀.sourceColumns_static (S := S) (base := base) (ε := ε) hE₀ hH
  have hAt := hR.sourceColumns_mixedDerivative hR₀ 1 0
  have hBt := h1.sourceColumns_add (hA.sourceColumns_mixedDerivative hA₀ 0 1)
    h1₀ (hA₀.sourceColumns_mixedDerivative 0 1) hE hH
  have hCt := hA.sourceColumns_mixedDerivative hA₀ 1 0
  have hDt := hR.sourceColumns_mixedDerivative hR₀ 0 1
  have hAB := hAt.sourceColumns_mul hD hT hε hE hI hBt hAr hBr
  let b₁ : ℕ := hAB.choose
  let ε₁ : ℝ := hAB.choose_spec.choose
  have hb₁ : base ≤ b₁ := hAB.choose_spec.choose_spec.1
  have hε₁ : 0 < ε₁ := hAB.choose_spec.choose_spec.2.1
  have hε₁ε : ε₁ ≤ ε := hAB.choose_spec.choose_spec.2.2.1
  have hC₁ := hCt.mono (fun _ h => h) hb₁ hε₁ε hE₀ hH
  have hD₁ := hDt.mono (fun _ h => h) hb₁ hε₁ε hE₀ hH
  have hCD := hC₁.sourceColumns_mul hD hT hε₁ hE hI hD₁ hCr hDr
  let b₂ : ℕ := hCD.choose
  let ε₂ : ℝ := hCD.choose_spec.choose
  have hb₂ : b₁ ≤ b₂ := hCD.choose_spec.choose_spec.1
  have hε₂ : 0 < ε₂ := hCD.choose_spec.choose_spec.2.1
  have hε₂ε₁ : ε₂ ≤ ε₁ := hCD.choose_spec.choose_spec.2.2.1
  have hAB₂ := hAB.choose_spec.choose_spec.2.2.2.mono
    (fun _ h => h) hb₂ hε₂ε₁ hE₀ hH
  have hsub := hAB₂.sourceColumns_sub hCD.choose_spec.choose_spec.2.2.2
    (hAr.sourceColumns_mul hBr hE) (hCr.sourceColumns_mul hDr hE) hE hH
  exact ⟨b₂, ε₂, hb₁.trans hb₂, hε₂, hε₂ε₁.trans hε₁ε,
    hsub.sourceColumns_constMul hE hH c hc⟩

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_currentDeterminant_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_currentDeterminant_data
