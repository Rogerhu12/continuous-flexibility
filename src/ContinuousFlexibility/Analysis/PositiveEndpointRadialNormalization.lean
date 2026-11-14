import ContinuousFlexibility.Analysis.RadialAffineDensity
import ContinuousFlexibility.Analysis.CylinderSobolev
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# One radial normalization for the two positive endpoints

The left endpoint uses `v + ξ`, and the right endpoint uses `v - ξ`.
In particular the normalized positive interval uses ξ on the left and
1 - ξ on the right. Translation and unit reflection preserve every
positive-order actual Fréchet jet norm.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def positiveEndpointRadialNormalization (root : Bool) (v : ℝ)
    (ξ : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  if root then v - ξ p else v + ξ p

theorem contDiffAt_positiveEndpointRadialNormalization
    (root : Bool) (v : ℝ) {ξ : PolarPoint → ℝ} {p : PolarPoint}
    (hξ : ContDiffAt ℝ ∞ ξ p) :
    ContDiffAt ℝ ∞ (positiveEndpointRadialNormalization root v ξ) p := by
  cases root with
  | false => exact contDiffAt_const.add hξ
  | true => exact contDiffAt_const.sub hξ

theorem positiveEndpointRadialNormalization_boundary
    (root : Bool) (v : ℝ) {ξ : PolarPoint → ℝ} {c : ℝ}
    (hξ : ∀ θ, ξ (c, θ) = 0) (θ : ℝ) :
    positiveEndpointRadialNormalization root v ξ (c, θ) = v := by
  cases root <;> simp only [positiveEndpointRadialNormalization, Bool.false_eq_true,
    if_false, if_true, hξ θ, add_zero, sub_zero]

theorem radialPartial_positiveEndpointRadialNormalization
    (root : Bool) (v : ℝ) {ξ : PolarPoint → ℝ} {p : PolarPoint}
    (hξ : DifferentiableAt ℝ ξ p) :
    radialPartial (positiveEndpointRadialNormalization root v ξ) p =
      if root then -radialPartial ξ p else radialPartial ξ p := by
  cases root with
  | false =>
    change radialPartial (fun q => v + ξ q) p = radialPartial ξ p
    rw [radialPartial_add (differentiableAt_const v) hξ, radialPartial_const, zero_add]
  | true =>
    change radialPartial (fun q => v - ξ q) p = -radialPartial ξ p
    rw [radialPartial_sub (differentiableAt_const v) hξ, radialPartial_const, zero_sub]

/-- No cutoff radius or higher derivative enters this identity. -/
theorem norm_iteratedFDeriv_positiveEndpointRadialNormalization
    (root : Bool) (v : ℝ) {ξ : PolarPoint → ℝ} {p : PolarPoint}
    (hξ : ContDiffAt ℝ ∞ ξ p) {k : ℕ} (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (positiveEndpointRadialNormalization root v ξ) p‖ =
      ‖iteratedFDeriv ℝ k ξ p‖ := by
  cases k with
  | zero => omega
  | succ j =>
    have hξj : ContDiffAt ℝ (j + 1) ξ p := hξ.of_le (by simp)
    cases root with
    | false =>
      change ‖iteratedFDeriv ℝ (j + 1) ((fun _ : PolarPoint => v) + ξ) p‖ = _
      rw [iteratedFDeriv_add_apply contDiffAt_const hξj, iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply, zero_add]
    | true =>
      change ‖iteratedFDeriv ℝ (j + 1) ((fun _ : PolarPoint => v) - ξ) p‖ = _
      rw [iteratedFDeriv_sub_apply contDiffAt_const hξj, iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply, zero_sub, norm_neg]

/-- The same normalization is the already defined affine chart operation,
so its principal-density identities apply with the actual orientation. -/
theorem positiveEndpointRadialNormalization_chart
    (root : Bool) (v : ℝ) (ξ φ : PolarPoint → ℝ) :
    (fun p => (positiveEndpointRadialNormalization root v ξ p, φ p)) =
      radialAffineChart v (if root then -1 else 1) (fun p => (ξ p, φ p)) := by
  funext p
  cases root <;> apply Prod.ext <;>
    simp only [positiveEndpointRadialNormalization, radialAffineChart,
      Bool.false_eq_true, if_false, if_true, neg_one_mul, one_mul] <;> ring

end ContinuousFlexibility.Analysis
