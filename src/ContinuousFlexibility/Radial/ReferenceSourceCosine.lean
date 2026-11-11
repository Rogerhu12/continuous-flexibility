import ContinuousFlexibility.Radial.ReferenceCosineReconstruction

/-!
# Fourier realization of the frozen reference source space

These wrappers connect the actual coefficient analysis to SourceMember,
the frozen source norm, and almost-everywhere equality in the physical
annulus. No reconstruction or norm-comparison hypothesis is added.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory Filter
open scoped ENNReal

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem referenceCosineCoeff_const_mul (c : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    referenceCosineCoeff (fun θ => c * f θ) n = c * referenceCosineCoeff f n := by
  unfold referenceCosineCoeff
  simp_rw [mul_assoc]
  rw [integral_const_mul]

theorem referenceCosineCoefficient_radial_mul {α : Type*}
    (a : α → ℝ) (f : α × ℝ → ℝ) (n : ℕ) (r : α) :
    referenceCosineCoefficient (fun x => a x.1 * f x) n r =
      a r * referenceCosineCoefficient f n r :=
  referenceCosineCoeff_const_mul (a r) (fun θ => f (r, θ)) n

theorem referenceCosineCoefficient_succ_eq_referenceMode
    (f : PolarPoint → ℝ) (n : ℕ) :
    referenceCosineCoefficient f (n + 1) = referenceMode f (2 * (n + 1)) := by
  funext r
  exact referenceCosineCoeff_succ (fun θ => f (r, θ)) n

theorem referenceSource_angular_periodic {D : ReferenceData} {γ M : ℝ}
    {F : RadialSource} (hF : SourceMember D γ M F) (r : ℝ) :
    Function.Periodic (fun θ => F.1 (r, θ)) Real.pi := by
  intro θ
  change F.1 (r, θ + Real.pi) = F.1 (r, θ)
  have h := hF.2.2.1 (r, θ)
  change F.1 (r + 0, θ + Real.pi) = F.1 (r, θ) at h
  simpa only [add_zero] using h

theorem SourceMember.memLp_radial_angular {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) :
    MemLp F.1 2 ((referenceRadialWeightedMeasure D γ M).prod referenceAngularMeasure) := by
  simpa only [referenceWeightedMeasure_eq_prod hD γ M] using hF.memLp_weighted hab hD

theorem SourceMember.cosineCoefficient_memLp {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) (n : ℕ) :
    MemLp (referenceCosineCoefficient F.1 n) 2 (referenceRadialWeightedMeasure D γ M) :=
  referenceCosineCoefficient_memLp (hF.memLp_radial_angular hab hD)
    (referenceSource_angular_periodic hF) hF.2.2.2.1 n

theorem SourceMember.referenceMode_even_memLp {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) (n : ℕ) :
    MemLp (referenceMode F.1 (2 * (n + 1))) 2 (referenceRadialWeightedMeasure D γ M) := by
  rw [← referenceCosineCoefficient_succ_eq_referenceMode]
  exact hF.cosineCoefficient_memLp hab hD (n + 1)

/-- The actual radial L² mode sequence of a member of the frozen source space. -/
def referenceSourceCosineAnalysis {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) :
    lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ M)) 2 :=
  referenceCosineAnalysis (hF.memLp_radial_angular hab hD)
    (referenceSource_angular_periodic hF) hF.2.2.2.1

/-- Exact equality with the frozen norm, including the separate scalar source coordinate. -/
theorem referenceSourceCosineAnalysis_norm_sq {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) :
    F.2 ^ 2 + (∑' n : ℕ, ‖referenceSourceCosineAnalysis hab hD hF n‖ ^ 2) =
      sourceNormSquare D γ M F := by
  unfold sourceNormSquare
  congr 1
  change (∑' n : ℕ, ‖referenceCosineAnalysis (hF.memLp_radial_angular hab hD)
    (referenceSource_angular_periodic hF) hF.2.2.2.1 n‖ ^ 2) = _
  rw [referenceCosineAnalysis_tsum_norm_sq, referenceL2_toLp_norm_sq,
    ← referenceWeightedMeasure_eq_prod hD γ M]
  exact integral_sq_referenceWeightedMeasure_eq hab hD hF.1 hF.2.1

/-- Fourier reconstruction gives equality in the actual physical annulus measure. -/
theorem referenceSourceCosineAnalysis_reconstruct_ae {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) :
    referenceCosineRepresentative (referenceSourceCosineAnalysis hab hD hF)
      =ᵐ[radialPhysicalMeasure D] F.1 := by
  have hh := referenceCosineRepresentative_analysis_ae (hF.memLp_radial_angular hab hD)
    (referenceSource_angular_periodic hF) hF.2.2.2.1
  apply (referenceWeightedMeasure_ae_iff hD γ M).mp
  simpa only [referenceWeightedMeasure_eq_prod hD γ M, referenceSourceCosineAnalysis] using hh

theorem referenceCosineRepresentative_periodic_polar {μ : Measure ℝ} [SFinite μ]
    (a : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) :
    Function.Periodic (referenceCosineRepresentative a) (0, Real.pi) := by
  rintro ⟨r, θ⟩
  change referenceCosineRepresentative a (r + 0, θ + Real.pi) =
    referenceCosineRepresentative a (r, θ)
  rw [add_zero]
  exact referenceCosineRepresentative_periodic a r θ

end ContinuousFlexibility.Statements
