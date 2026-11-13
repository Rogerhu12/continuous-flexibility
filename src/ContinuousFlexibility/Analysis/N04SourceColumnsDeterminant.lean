import ContinuousFlexibility.Analysis.N04SourceColumnsWidth
import ContinuousFlexibility.Analysis.N04SourceColumnsDerivative
import ContinuousFlexibility.Analysis.N04SourceColumnsMultiplication
import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-!
# Current data for the actual inverse determinant

The determinant is the first-jet polynomial of the two inverse-coordinate
atoms. The two product operations each choose one fixed neighborhood, and
all remaining operations retain the final neighborhood. The stored width
ratio contributes only its reference coefficient envelope.
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

namespace N04RealizationGauge

variable (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)

/-- Replacing the auxiliary field retains the sector grading and its
smoothing operators, hence its interpolation estimates. -/
theorem sourceColumns_interpolation :
    HasInterpolation (parameterGrading (G.S η)) := by
  have hsector : HasSmoothing (sectorGrading G.W.S) :=
    solve_sector_hasSmoothing (S := G.W.S) G.W.hS
  have hparameter : HasSmoothing (parameterGrading G.W.S) :=
    hasSmoothing_pairGrading hsector hasSmoothing_realGrading
  have hI : HasInterpolation (parameterGrading G.W.S) :=
    hasInterpolation_of_hasSmoothing (n07aParameterGrading_monotone G.W.S) hparameter
  exact hI

/-- Reference jets control the determinant polynomial at the same sample. -/
theorem sourceColumns_inverseDeterminantRef_data
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    N04SourceReferenceData G.W.U (G.V η).cell
      (G.sourceColumnsInverseDeterminantRef η) := by
  have hE := (G.cost_nonneg η).2.2
  have hX : N04SourceReferenceData G.W.U (G.V η).cell (G.atomRef η .inverseRadial) :=
    n04SourceReferenceData_of_referenceJets href .inverseRadial
  have hY : N04SourceReferenceData G.W.U (G.V η).cell (G.atomRef η .inverseAngleDefect) :=
    n04SourceReferenceData_of_referenceJets href .inverseAngleDefect
  have h1 := n04SourceColumns_reference_one hE
  have hA := hX.sourceColumns_mixedDerivative 1 0
  have hB := h1.sourceColumns_add (hY.sourceColumns_mixedDerivative 0 1) hE
  have hC := hY.sourceColumns_mixedDerivative 1 0
  have hD := hX.sourceColumns_mixedDerivative 0 1
  exact ((hA.sourceColumns_mul hB hE).sourceColumns_sub
    (hC.sourceColumns_mul hD hE) hE).sourceColumns_constMul hE
      (G.sourceColumnsWidthRatio η) (G.sourceColumns_widthRatio_bound η href)

/-- The current determinant inherits the true vanishing difference and
all parameter jets on a single, derivative-independent neighborhood. -/
theorem sourceColumns_inverseDeterminant_data {b : ℕ} {ε : ℝ}
    (hA : G.Admissible b ε) (hG : G.GeometryData η (fun _ => True) b ε)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      G.Data η (fun _ => True) b' ε'
        (G.sourceColumnsInverseDeterminant η) (G.sourceColumnsInverseDeterminantRef η) := by
  have hD : IsAccumulatingProfile G.W.D := G.W.radial.1
  have hT : IsMaterialData G.W.D G.W.U :=
    isMaterialData_enlargedMaterialData hD G.W.hT
  have hE := (G.cost_nonneg η).2.2
  have hE₀ := (G.cost_nonneg η).1
  have hH := (G.cost_nonneg η).2.1
  have hI := G.sourceColumns_interpolation η
  have hX₀ : N04SourceReferenceData G.W.U (G.V η).cell (G.atomRef η .inverseRadial) :=
    n04SourceReferenceData_of_referenceJets href .inverseRadial
  have hY₀ : N04SourceReferenceData G.W.U (G.V η).cell
      (G.atomRef η .inverseAngleDefect) :=
    n04SourceReferenceData_of_referenceJets href .inverseAngleDefect
  have h1₀ := n04SourceColumns_reference_one hE
  have hAr := hX₀.sourceColumns_mixedDerivative 1 0
  have hBr := h1₀.sourceColumns_add (hY₀.sourceColumns_mixedDerivative 0 1) hE
  have hCr := hY₀.sourceColumns_mixedDerivative 1 0
  have hDr := hX₀.sourceColumns_mixedDerivative 0 1
  have hX := hG.1 .inverseRadial trivial
  have hY := hG.1 .inverseAngleDefect trivial
  have h1 := h1₀.sourceColumns_static (S := G.S η) (base := b) (ε := ε) hE₀ hH
  have hAt := hX.sourceColumns_mixedDerivative hX₀ 1 0
  have hBt := h1.sourceColumns_add (hY.sourceColumns_mixedDerivative hY₀ 0 1)
    h1₀ (hY₀.sourceColumns_mixedDerivative 0 1) hE hH
  have hCt := hY.sourceColumns_mixedDerivative hY₀ 1 0
  have hDt := hX.sourceColumns_mixedDerivative hX₀ 0 1
  have hAB := hAt.sourceColumns_mul hD hT hA.2.1 hE hI hBt hAr hBr
  let b₁ : ℕ := hAB.choose
  let ε₁ : ℝ := hAB.choose_spec.choose
  have hb₁ : b ≤ b₁ := hAB.choose_spec.choose_spec.1
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
  have hdet := hsub.sourceColumns_constMul hE hH (G.sourceColumnsWidthRatio η)
    (G.sourceColumns_widthRatio_bound η href)
  exact ⟨b₂, ε₂, hb₁.trans hb₂, hε₂, hε₂ε₁.trans hε₁ε, hdet⟩

end N04RealizationGauge

end ContinuousFlexibility.Analysis
