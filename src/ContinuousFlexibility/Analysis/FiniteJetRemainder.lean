import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Uniform bounds for a function with a vanishing finite jet

On a convex set of radius `R` about a point, a bound for the derivative of
order `n` controls every lower derivative of a function whose lower jet
vanishes at that point. Downward induction and the mean value inequality
give the bound `M * R ^ (n - j)`. This deliberately non-sharp version has
constant one and is convenient when normalizing Taylor remainders.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite vanishing jet and a bound for the top derivative give a
simultaneous radius-weighted bound for all lower derivatives. -/
theorem norm_iteratedFDeriv_le_pow_of_zero_jet
    {f : E → F} (hf : ContDiff ℝ ∞ f) {K : Set E} (hK : Convex ℝ K)
    {x : E} (hx : x ∈ K) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hradius : ∀ y ∈ K, ‖y - x‖ ≤ R) (n : ℕ)
    (hzero : ∀ k : ℕ, k < n → iteratedFDeriv ℝ k f x = 0)
    (htop : ∀ y ∈ K, ‖iteratedFDeriv ℝ n f y‖ ≤ M)
    (j : ℕ) (hj : j ≤ n) :
    ∀ y ∈ K, ‖iteratedFDeriv ℝ j f y‖ ≤ M * R ^ (n - j) := by
  refine Nat.decreasingInduction
    (motive := fun k _ => ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k f y‖ ≤ M * R ^ (n - k)) ?_ ?_ hj
  · intro k hk ih y hy
    have hdiff (z : E) : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) z :=
      hf.contDiffAt.differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)
    have hderiv : ∀ z ∈ K,
        ‖fderiv ℝ (iteratedFDeriv ℝ k f) z‖ ≤ M * R ^ (n - (k + 1)) := by
      intro z hz
      simpa only [norm_fderiv_iteratedFDeriv] using ih z hz
    have hmean := hK.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hdiff z) hderiv hx hy
    rw [hzero k hk, sub_zero] at hmean
    calc
      ‖iteratedFDeriv ℝ k f y‖ ≤
          (M * R ^ (n - (k + 1))) * ‖y - x‖ := hmean
      _ ≤ (M * R ^ (n - (k + 1))) * R :=
        mul_le_mul_of_nonneg_left (hradius y hy) (mul_nonneg hM (pow_nonneg hR _))
      _ = M * R ^ (n - k) := by
        rw [show n - k = (n - (k + 1)) + 1 by omega, pow_succ]
        ring
  · intro y hy
    simpa only [Nat.sub_self, pow_zero, mul_one] using htop y hy

end ContinuousFlexibility.Analysis
