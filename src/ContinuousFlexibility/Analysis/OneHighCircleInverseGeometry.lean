module

public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Actual inverse-lift derivative identities

The two real functions are genuine smooth inverses. Their lift law and
derivatives below are derived from those inverse identities and the ordinary
chain rule, with no supplied inverse-derivative or norm estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem circleInverse_lift {P : ℝ} {h ι : ℝ → ℝ}
    (hι : ∀ x, h (ι x) = x) (ιh : ∀ x, ι (h x) = x)
    (hlift : ∀ x, h (x + P) = h x + P) (x : ℝ) :
    ι (x + P) = ι x + P := by
  apply (show Function.Injective h from (show LeftInverse ι h from ιh).injective)
  rw [hι, hlift, hι]

theorem circleInverse_deriv {h ι : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hi : ContDiff ℝ ∞ ι)
    (hι : ∀ x, h (ι x) = x) (x : ℝ) (hne : deriv h (ι x) ≠ 0) :
    deriv ι x = (deriv h (ι x))⁻¹ := by
  have hd : HasDerivAt (h ∘ ι) (deriv h (ι x) * deriv ι x) x :=
    ((hh.differentiable (by simp) (ι x)).hasDerivAt).comp x
      (hi.differentiable (by simp) x).hasDerivAt
  have he : h ∘ ι = id := funext hι
  rw [he] at hd
  have hmul : deriv h (ι x) * deriv ι x = 1 := hd.unique (hasDerivAt_id x)
  have hcancel := congrArg (fun y : ℝ => (deriv h (ι x))⁻¹ * y) hmul
  simpa only [← mul_assoc, inv_mul_cancel₀ hne, one_mul, mul_one] using hcancel

theorem circleInverse_iteratedDeriv_two {h ι : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hi : ContDiff ℝ ∞ ι)
    (hι : ∀ x, h (ι x) = x) (x : ℝ) (hne : deriv h (ι x) ≠ 0) :
    iteratedDeriv 2 ι x =
      -iteratedDeriv 2 h (ι x) * ((deriv h (ι x))⁻¹) ^ 3 := by
  have he : h ∘ ι = id := funext hι
  have hd := iteratedDeriv_comp_two (g := h) (f := ι) (x := x)
    (hh.contDiffAt.of_le (by simp : (2 : ℕ∞ω) ≤ ∞))
    (hi.contDiffAt.of_le (by simp : (2 : ℕ∞ω) ≤ ∞))
  have hfirst := circleInverse_deriv hh hi hι x hne
  have hzero : (0 : ℝ) = iteratedDeriv 2 h (ι x) * ((deriv h (ι x))⁻¹) ^ 2 +
      deriv h (ι x) * iteratedDeriv 2 ι x := by
    simpa [he, iteratedDeriv_id, hfirst] using hd
  apply mul_left_cancel₀ hne
  calc
    deriv h (ι x) * iteratedDeriv 2 ι x =
        -iteratedDeriv 2 h (ι x) * ((deriv h (ι x))⁻¹) ^ 2 := by linarith
    _ = deriv h (ι x) *
        (-iteratedDeriv 2 h (ι x) * ((deriv h (ι x))⁻¹) ^ 3) := by
      field_simp [hne] <;> ring

theorem circleInverse_iteratedDeriv_three {h ι : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hi : ContDiff ℝ ∞ ι)
    (hι : ∀ x, h (ι x) = x) (x : ℝ) (hne : deriv h (ι x) ≠ 0) :
    iteratedDeriv 3 ι x =
      3 * (iteratedDeriv 2 h (ι x)) ^ 2 * ((deriv h (ι x))⁻¹) ^ 5 -
        iteratedDeriv 3 h (ι x) * ((deriv h (ι x))⁻¹) ^ 4 := by
  have he : h ∘ ι = id := funext hι
  have hd := iteratedDeriv_comp_three (g := h) (f := ι) (x := x)
    (hh.contDiffAt.of_le (by simp : (3 : ℕ∞ω) ≤ ∞))
    (hi.contDiffAt.of_le (by simp : (3 : ℕ∞ω) ≤ ∞))
  have hfirst := circleInverse_deriv hh hi hι x hne
  have hsecond := circleInverse_iteratedDeriv_two hh hi hι x hne
  have hzero : (0 : ℝ) =
      iteratedDeriv 3 h (ι x) * ((deriv h (ι x))⁻¹) ^ 3 +
        3 * iteratedDeriv 2 h (ι x) * iteratedDeriv 2 ι x * (deriv h (ι x))⁻¹ +
        deriv h (ι x) * iteratedDeriv 3 ι x := by
    simpa [he, iteratedDeriv_id, hfirst] using hd
  apply mul_left_cancel₀ hne
  calc
    deriv h (ι x) * iteratedDeriv 3 ι x =
        -(iteratedDeriv 3 h (ι x) * ((deriv h (ι x))⁻¹) ^ 3 +
          3 * iteratedDeriv 2 h (ι x) * iteratedDeriv 2 ι x * (deriv h (ι x))⁻¹) := by
      linarith
    _ = deriv h (ι x) *
        (3 * (iteratedDeriv 2 h (ι x)) ^ 2 * ((deriv h (ι x))⁻¹) ^ 5 -
          iteratedDeriv 3 h (ι x) * ((deriv h (ι x))⁻¹) ^ 4) := by
      rw [hsecond]
      field_simp [hne] <;> ring

end ContinuousFlexibility.Analysis
