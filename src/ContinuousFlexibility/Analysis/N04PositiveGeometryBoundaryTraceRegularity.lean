module

public import ContinuousFlexibility.Analysis.OneSidedBoundaryTaylorRepresentative

/-! # Smoothness and periodicity of radial angular defects

These scalar boundary identities are proved before specializing to an
actual atlas, keeping the angular shift calculation independent of its
geometric certificates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04PositiveGeometry_radialAngleDefect_contDiff
    {F : PolarPoint → ℝ} (c : ℝ)
    (hF : ∀ θ : ℝ, ContDiffAt ℝ ∞ F (c, θ)) (j : ℕ) :
    ContDiff ℝ ∞ (fun θ => radialBoundaryJet F c j θ - if j = 0 then θ else 0) := by
  have hlinear : ContDiff ℝ ∞ (fun θ : ℝ => if j = 0 then θ else 0) := by
    split_ifs
    · exact contDiff_id
    · exact contDiff_const
  exact (contDiff_radialBoundaryJet_of_contDiffAt c hF j).sub hlinear

theorem n04PositiveGeometry_radialAngleDefect_period
    {F : PolarPoint → ℝ} {a b c : ℝ} (hab : a < b) (hc : c ∈ Icc a b)
    (hF : ∀ θ : ℝ, ContDiffAt ℝ ∞ F (c, θ))
    (hperiod : ∀ r ∈ Ioo a b, ∀ θ, F (r, θ + Real.pi) = F (r, θ) + Real.pi)
    (j : ℕ) :
    Function.Periodic
      (fun θ => radialBoundaryJet F c j θ - if j = 0 then θ else 0) Real.pi := by
  intro θ
  have he := radialBoundaryJet_angleAffine_on_closedStrip (F := F)
    (α := 1) (β := Real.pi) (τ := fun t : ℝ => t + Real.pi) hab hc hF
    (contDiff_id.add contDiff_const)
    (fun r hr η => by simpa only [one_mul, add_comm] using hperiod r hr η) j θ
  change radialBoundaryJet F c j (θ + Real.pi) - (if j = 0 then θ + Real.pi else 0) =
    radialBoundaryJet F c j θ - (if j = 0 then θ else 0)
  rw [he]
  by_cases hj : j = 0
  · simp only [if_pos hj, one_mul]
    ring
  · simp only [if_neg hj, zero_add, one_mul, sub_zero]

end ContinuousFlexibility.Analysis
