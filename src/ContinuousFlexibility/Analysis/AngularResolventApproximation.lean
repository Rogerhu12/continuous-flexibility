import ContinuousFlexibility.Analysis.AngularResolventSpectrum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Approximation of a discrete-spectrum resolvent

The finite spectral sums converge to the bounded resolvent in operator
norm. This is valid with infinite-dimensional eigenspaces: no finite-rank
or compact-operator approximation is claimed or used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

theorem angularReciprocalBump_eigenvalue (n m : ℕ) :
    angularReciprocalBump n (angularResolventEigenvalue m) = if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst m
    simp only [angularReciprocalBump_self, if_pos rfl]
  · simp only [angularReciprocalBump_other hmn, if_neg hmn]

/-- The scalar finite spectral sum. -/
def angularResolventPartialFunction (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, angularResolventEigenvalue n * angularReciprocalBump n x

theorem continuous_angularResolventPartialFunction (N : ℕ) :
    Continuous (angularResolventPartialFunction N) := by
  unfold angularResolventPartialFunction
  exact continuous_finsetSum _ (fun n _ =>
    continuous_const.mul (continuous_angularReciprocalBump n))

@[simp] theorem angularResolventPartialFunction_zero (N : ℕ) :
    angularResolventPartialFunction N 0 = 0 := by
  simp only [angularResolventPartialFunction, angularReciprocalBump_zero, mul_zero,
    Finset.sum_const_zero]

theorem angularResolventPartialFunction_eigenvalue (N m : ℕ) :
    angularResolventPartialFunction N (angularResolventEigenvalue m) =
      if m < N then angularResolventEigenvalue m else 0 := by
  simp [angularResolventPartialFunction, angularReciprocalBump_eigenvalue, mul_ite]

theorem angularResolventPartialFunction_error (N : ℕ) {x : ℝ}
    (hx : x ∈ angularReciprocalSpectrum) :
    ‖x - angularResolventPartialFunction N x‖ ≤ angularResolventEigenvalue N := by
  rcases hx with rfl | ⟨m, rfl⟩
  · simp only [angularResolventPartialFunction_zero, sub_self, norm_zero]
    exact (angularResolventEigenvalue_pos N).le
  · rw [angularResolventPartialFunction_eigenvalue]
    by_cases hm : m < N
    · rw [if_pos hm, sub_self, norm_zero]
      exact (angularResolventEigenvalue_pos N).le
    · rw [if_neg hm, sub_zero, Real.norm_eq_abs,
        abs_of_pos (angularResolventEigenvalue_pos m)]
      exact angularResolventEigenvalue_strictAnti.antitone (Nat.le_of_not_gt hm)

theorem angularResolventEigenvalue_tendsto :
    Tendsto angularResolventEigenvalue atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A finite sum of reciprocal eigenvalues times their spectral projections. -/
def angularResolventPartial (B : H →L[ℂ] H) (N : ℕ) : H →L[ℂ] H :=
  ∑ n ∈ Finset.range N, angularResolventEigenvalue n • angularResolventProjection B n

theorem angularResolventPartial_eq_cfc (B : H →L[ℂ] H) (N : ℕ) :
    angularResolventPartial B N = cfc (angularResolventPartialFunction N) B := by
  have h := cfc_sum (fun n => fun x : ℝ =>
    angularResolventEigenvalue n * angularReciprocalBump n x) B (Finset.range N)
    (fun n _ => (continuous_const.mul (continuous_angularReciprocalBump n)).continuousOn)
  have hfun : (∑ n ∈ Finset.range N, fun x : ℝ =>
      angularResolventEigenvalue n * angularReciprocalBump n x) =
      angularResolventPartialFunction N := by
    funext x
    simp only [Finset.sum_apply, angularResolventPartialFunction]
  rw [hfun] at h
  simpa only [cfc_const_mul _ _ _ (continuous_angularReciprocalBump _).continuousOn,
    angularResolventPartial, angularResolventProjection] using h.symm

/-- Uniform approximation with an explicit tail bound. The spectral
projections may have infinite rank. -/
theorem angularResolventPartial_error {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (hSpectrum : spectrum ℝ B ⊆ angularReciprocalSpectrum) (N : ℕ) :
    ‖B - angularResolventPartial B N‖ ≤ angularResolventEigenvalue N := by
  rw [angularResolventPartial_eq_cfc]
  have heq : B - cfc (angularResolventPartialFunction N) B =
      cfc (fun x : ℝ => x - angularResolventPartialFunction N x) B := by
    rw [cfc_sub (fun x : ℝ => x) _ _ continuous_id.continuousOn
      (continuous_angularResolventPartialFunction N).continuousOn, cfc_id' ℝ B hB]
  rw [heq]
  apply norm_cfc_le (angularResolventEigenvalue_pos N).le
  intro x hx
  exact angularResolventPartialFunction_error N (hSpectrum hx)

theorem angularResolventPartial_tendsto {B : H →L[ℂ] H} (hB : IsSelfAdjoint B)
    (hSpectrum : spectrum ℝ B ⊆ angularReciprocalSpectrum) :
    Tendsto (angularResolventPartial B) atTop (𝓝 B) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun N => norm_nonneg _)
    (fun N => ?_) angularResolventEigenvalue_tendsto
  rw [norm_sub_rev]
  exact angularResolventPartial_error hB hSpectrum N

end ContinuousFlexibility.Analysis
