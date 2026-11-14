module

public import ContinuousFlexibility.Radial.ReferenceSourceCosine

/-!
# The exact energy of each actual source mode

These identities use the coefficients of the physical source and its
frozen cell norm. The separate scalar source is included once in the
full energy and is available for the frequency-two bordered equation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped ENNReal

theorem referenceCosineCoefficient_zero_eq_mean (f : PolarPoint → ℝ) :
    referenceCosineCoefficient f 0 =
      (fun r => radialAngularMean (fun θ => f (r, θ))) := by
  funext r
  exact referenceCosineCoeff_zero (fun θ => f (r, θ))

theorem referenceSourceCosineAnalysis_summable {D : ReferenceData}
    (hab : D.a ≤ D.b) (hP : RadialPartition D)
    {γ M : ℝ} {F : RadialSource} (hF : SourceMember D γ M F) :
    Summable (fun n : ℕ => ‖referenceSourceCosineAnalysis hab hP hF n‖ ^ 2) :=
  (referenceCosineAnalysisCoeff_hasSum_norm_sq
    (hF.memLp_radial_angular hab hP)
    (referenceSource_angular_periodic hF) hF.2.2.2.1).summable

theorem referenceSourceCosineAnalysis_energy {D : ReferenceData}
    (hab : D.a ≤ D.b) (hP : RadialPartition D)
    {γ M : ℝ} {F : RadialSource} (hF : SourceMember D γ M F) (n : ℕ) :
    ‖referenceSourceCosineAnalysis hab hP hF n‖ ^ 2 =
      ∫ r, referenceCosineCoefficient F.1 n r ^ 2
        ∂referenceRadialWeightedMeasure D γ M :=
  referenceCosineAnalysisCoeff_norm_sq (hF.memLp_radial_angular hab hP)
    (referenceSource_angular_periodic hF) hF.2.2.2.1 n

theorem referenceSourceCosineAnalysis_coordinate_scalar_le {D : ReferenceData}
    (hab : D.a ≤ D.b) (hP : RadialPartition D)
    {γ M : ℝ} {F : RadialSource} (hF : SourceMember D γ M F) (n : ℕ) :
    ‖referenceSourceCosineAnalysis hab hP hF n‖ ^ 2 + F.2 ^ 2 ≤
      sourceNormSquare D γ M F := by
  have hle := (referenceSourceCosineAnalysis_summable hab hP hF).le_tsum n
    (fun k _ => sq_nonneg ‖referenceSourceCosineAnalysis hab hP hF k‖)
  calc
    _ ≤ (∑' k : ℕ, ‖referenceSourceCosineAnalysis hab hP hF k‖ ^ 2) + F.2 ^ 2 :=
      add_le_add hle le_rfl
    _ = sourceNormSquare D γ M F := by
      rw [add_comm]
      exact referenceSourceCosineAnalysis_norm_sq hab hP hF

theorem referenceSourceCosineAnalysis_coordinate_le {D : ReferenceData}
    (hab : D.a ≤ D.b) (hP : RadialPartition D)
    {γ M : ℝ} {F : RadialSource} (hF : SourceMember D γ M F) (n : ℕ) :
    ‖referenceSourceCosineAnalysis hab hP hF n‖ ^ 2 ≤
      sourceNormSquare D γ M F := by
  have h := referenceSourceCosineAnalysis_coordinate_scalar_le hab hP hF n
  linarith only [h, sq_nonneg F.2]

end ContinuousFlexibility.Statements
