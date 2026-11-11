import ContinuousFlexibility.Analysis.SpacesSequenceRetraction

/-!
# Smoothing and interpolation after the concrete retractions

The exponential model grading equals its projective grading because the
weighted level norms are monotone. The stated H01 calculus therefore
transfers smoothing to each actual retract and supplies interpolation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

theorem spaces_modelGrading_eq_projective :
    modelGrading = gradedSeminorm (fun _ : ℕ => ExponentialSequenceLevel PhysicalModelBanach)
      (exponentialSequenceBond PhysicalModelBanach) := by
  funext n
  apply Seminorm.ext
  intro u
  apply le_antisymm
  · exact norm_coordinate_le_graded _ _ le_rfl u
  · apply (gradedSeminorm_le_iff _ _ n u (apply_nonneg _ _)).mpr
    intro i hi
    exact exponentialSequenceSeminorm_monotone PhysicalModelBanach hi u

theorem spaces_tameStructure_of_retraction (hH01 : H01Statement)
    (E : ℕ → Type) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
    [∀ n, CompleteSpace (E n)] (bond : ∀ n, E (n + 1) →L[ℝ] E n)
    (hR : TameRetraction (gradedSeminorm E bond) modelGrading) :
    HasSmoothing (gradedSeminorm E bond) ∧ HasInterpolation (gradedSeminorm E bond) := by
  let F : ℕ → Type := fun _ => ExponentialSequenceLevel PhysicalModelBanach
  have hcalc := hH01.2 E F E bond (exponentialSequenceBond PhysicalModelBanach) bond
  have hR' : TameRetraction (gradedSeminorm E bond)
      (gradedSeminorm F (exponentialSequenceBond PhysicalModelBanach)) := by
    rw [← spaces_modelGrading_eq_projective]
    exact hR
  have hSm : HasSmoothing (gradedSeminorm F (exponentialSequenceBond PhysicalModelBanach)) := by
    rw [← spaces_modelGrading_eq_projective]
    exact hasSmoothing_modelGrading
  have hS := hcalc.2.2.2.2.1 hR' hSm
  exact ⟨hS, hcalc.2.2.2.1 hS⟩

end ContinuousFlexibility.Statements
