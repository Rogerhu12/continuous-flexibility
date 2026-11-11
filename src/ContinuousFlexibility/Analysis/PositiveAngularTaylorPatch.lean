import ContinuousFlexibility.Analysis.AngularTaylorPolynomial
import ContinuousFlexibility.Analysis.PositiveEndpointCutoff

/-!
# A positive angular Taylor patch at one endpoint

The zeroth angular datum is interpolated convexly with the identity.
The positive radial orders are small after the fixed collar is chosen.
This separates angular positivity from potentially large radial
derivatives of the cutoff.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def positiveAngularTaylorPatch (n : ℕ) (c δ : ℝ)
    (A : ℕ → ℝ → ℝ) (p : PolarPoint) : ℝ :=
  p.2 + positiveEndpointCutoff c δ p.1 *
    (boundaryTaylorPolynomial n c A p - p.2)

theorem contDiff_positiveAngularTaylorPatch
    {n : ℕ} {A : ℕ → ℝ → ℝ}
    (hA : ∀ j ≤ n, ContDiff ℝ ∞ (A j)) (c δ : ℝ) :
    ContDiff ℝ ∞ (positiveAngularTaylorPatch n c δ A) :=
  contDiff_snd.add (((contDiff_positiveEndpointCutoff c δ).comp contDiff_fst).mul
    ((contDiff_boundaryTaylorPolynomial hA c).sub contDiff_snd))

theorem hasDerivAt_positiveAngularTaylorPatch_angle
    {n : ℕ} {A : ℕ → ℝ → ℝ}
    (hA : ∀ j ≤ n, ContDiff ℝ ∞ (A j)) (c δ r θ : ℝ) :
    HasDerivAt (fun η => positiveAngularTaylorPatch n c δ A (r, η))
      (1 + positiveEndpointCutoff c δ r *
        (boundaryTaylorPolynomial n c (fun j => deriv (A j)) (r, θ) - 1)) θ := by
  have hid : HasDerivAt (fun η : ℝ => η) 1 θ := hasDerivAt_id θ
  change HasDerivAt
    (fun η : ℝ => η + positiveEndpointCutoff c δ r *
      (boundaryTaylorPolynomial n c A (r, η) - η))
    (1 + positiveEndpointCutoff c δ r *
      (boundaryTaylorPolynomial n c (fun j => deriv (A j)) (r, θ) - 1)) θ
  exact hid.fun_add
    (((hasDerivAt_boundaryTaylorPolynomial_angle hA c r θ).fun_sub hid).const_mul
      (positiveEndpointCutoff c δ r))

/-- The data bound concerns actual angular derivatives of positive
radial coefficients. The leading angle may have large displacement. -/
theorem deriv_positiveAngularTaylorPatch_lower
    {n : ℕ} {A : ℕ → ℝ → ℝ} {c δ κ M : ℝ}
    (hA : ∀ j ≤ n, ContDiff ℝ ∞ (A j))
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hκone : κ ≤ 1) (hM : 0 ≤ M)
    (hzero : ∀ θ, κ ≤ deriv (A 0) θ)
    (hbound : ∀ j, 0 < j → j ≤ n → ∀ θ, |deriv (A j) θ| ≤ M)
    (hsmall : ((n + 1 : ℕ) : ℝ) * M * δ ≤ κ / 2)
    (r θ : ℝ) :
    κ / 2 ≤ deriv (fun η => positiveAngularTaylorPatch n c δ A (r, η)) θ := by
  rw [(hasDerivAt_positiveAngularTaylorPatch_angle hA c δ r θ).deriv]
  by_cases hr : r ∈ Metric.ball c δ
  · have hr' : |r - c| ≤ δ :=
      (show |r - c| < δ by simpa only [Metric.mem_ball, Real.dist_eq] using hr).le
    have hb := abs_boundaryTaylorPolynomial_sub_zero_le
      (A := fun j => deriv (A j)) hδ.le hδone hM hr'
      (fun j hj hjn => hbound j hj hjn θ)
    have hP : κ / 2 ≤
        boundaryTaylorPolynomial n c (fun j => deriv (A j)) (r, θ) := by
      have hl := (abs_le.mp hb).1
      linarith [hzero θ]
    have hfirst := mul_nonneg (positiveEndpointCutoff_nonneg c δ r)
      (sub_nonneg.mpr hP)
    have hsecond := mul_nonneg
      (sub_nonneg.mpr (positiveEndpointCutoff_le_one c δ r))
      (show 0 ≤ 1 - κ / 2 by linarith)
    nlinarith
  · rw [positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hr, zero_mul, add_zero]
    linarith

theorem positiveAngularTaylorPatch_radial_germ
    (n : ℕ) (c δ : ℝ) (A : ℕ → ℝ → ℝ) (θ : ℝ) :
    (fun r => positiveAngularTaylorPatch n c δ A (r, θ)) =ᶠ[𝓝 c]
      (fun r => boundaryTaylorPolynomial n c A (r, θ)) := by
  filter_upwards [positiveEndpointCutoff_one_germ c δ] with r hr
  simp only [positiveAngularTaylorPatch, hr, Pi.one_apply, one_mul]
  ring

theorem iteratedDeriv_positiveAngularTaylorPatch
    (n : ℕ) (c δ : ℝ) (A : ℕ → ℝ → ℝ) {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedDeriv k (fun r => positiveAngularTaylorPatch n c δ A (r, θ)) c = A k θ :=
  ((positiveAngularTaylorPatch_radial_germ n c δ A θ).iteratedDeriv k).eq_of_nhds.trans
    (iteratedDeriv_boundaryTaylorPolynomial n c A hk θ)

theorem positiveAngularTaylorPatch_eq_angle_of_not_mem_ball
    (n : ℕ) {c δ r : ℝ} (hδ : 0 < δ) (A : ℕ → ℝ → ℝ)
    (hr : r ∉ Metric.ball c δ) (θ : ℝ) :
    positiveAngularTaylorPatch n c δ A (r, θ) = θ := by
  simp only [positiveAngularTaylorPatch,
    positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hr, zero_mul, add_zero]

theorem positiveAngularTaylorPatch_period_add
    {n : ℕ} {A : ℕ → ℝ → ℝ} {T : ℝ}
    (hzero : ∀ θ, A 0 (θ + T) = A 0 θ + T)
    (hperiod : ∀ j, 0 < j → j ≤ n → Function.Periodic (A j) T)
    (c δ r θ : ℝ) :
    positiveAngularTaylorPatch n c δ A (r, θ + T) =
      positiveAngularTaylorPatch n c δ A (r, θ) + T := by
  simp only [positiveAngularTaylorPatch,
    boundaryTaylorPolynomial_period_add hzero hperiod]
  ring

theorem positiveAngularTaylorPatch_reflect
    {n : ℕ} {A : ℕ → ℝ → ℝ}
    (hodd : ∀ j ≤ n, ∀ θ, A j (-θ) = -A j θ) (c δ r θ : ℝ) :
    positiveAngularTaylorPatch n c δ A (r, -θ) =
      -positiveAngularTaylorPatch n c δ A (r, θ) := by
  simp only [positiveAngularTaylorPatch, boundaryTaylorPolynomial_reflect hodd]
  ring

end ContinuousFlexibility.Analysis

