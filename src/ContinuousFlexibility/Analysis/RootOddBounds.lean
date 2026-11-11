import ContinuousFlexibility.Analysis.RootCompositionIntegral
import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A smooth integral model for the odd root quotient

The odd divided difference is the average of the middle partial derivative
over a symmetric interval.  This realizes it as the even root substitution
of a globally smooth function.  Compact-parameter integral estimates and
the ordinary composition bounds control its jets with one input derivative
more than the output order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology Interval

/-- The middle directional derivative in the source coordinates. -/
def rootMiddleDerivative (G : ℝ × ℝ × ℝ → ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  fderiv ℝ G q (0, 1, 0)

/-- A global smooth model of the odd divided difference. -/
def rootOddIntegral (G : ℝ × ℝ × ℝ → ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1,
    rootMiddleDerivative G (q.1, t * q.2.1, q.2.2)

theorem contDiff_rootMiddleDerivative {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (rootMiddleDerivative G) :=
  (contDiff_infty_iff_fderiv.mp hG).2.clm_apply contDiff_const

theorem hasDerivAt_rootMiddleDerivative {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (x z θ : ℝ) :
    HasDerivAt (fun t : ℝ => G (x, t, θ)) (rootMiddleDerivative G (x, z, θ)) z := by
  have hc : HasDerivAt (fun t : ℝ => (x, t, θ)) (0, 1, 0) z :=
    (hasDerivAt_const z x).prodMk ((hasDerivAt_id' z).prodMk (hasDerivAt_const z θ))
  simpa only [Function.comp_def] using
    ((hG.differentiable (by simp)) (x, z, θ)).hasFDerivAt.comp_hasDerivAt z hc

theorem contDiff_rootOddIntegral {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (rootOddIntegral G) := by
  have hIntegrand : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × ℝ =>
      rootMiddleDerivative G (q.1.1, q.2 * q.1.2.1, q.1.2.2)) :=
    (contDiff_rootMiddleDerivative hG).comp
      (contDiff_fst.fst.prodMk
        ((contDiff_snd.mul contDiff_fst.snd.fst).prodMk contDiff_fst.snd.snd))
  have hI := contDiff_intervalIntegral_of_contDiff hIntegrand (-1) 1
  exact contDiff_const.mul hI

theorem rootOddIntegral_factor {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (q : ℝ × ℝ × ℝ) :
    (2 * q.2.1) * rootOddIntegral G q = G q - G (q.1, -q.2.1, q.2.2) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => G (q.1, t * q.2.1, q.2.2))
      (q.2.1 * rootMiddleDerivative G (q.1, t * q.2.1, q.2.2)) t := by
    simpa only [Function.comp_def, smul_eq_mul] using
      (hasDerivAt_rootMiddleDerivative hG q.1 (t * q.2.1) q.2.2).scomp t
        (hasDerivAt_mul_const q.2.1)
  have hc : Continuous (fun t : ℝ =>
      q.2.1 * rootMiddleDerivative G (q.1, t * q.2.1, q.2.2)) :=
    continuous_const.mul ((contDiff_rootMiddleDerivative hG).continuous.comp
      (continuous_const.prodMk ((continuous_id.mul continuous_const).prodMk continuous_const)))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-1 : ℝ)) (b := 1) (fun t _ => hd t) (hc.intervalIntegrable (-1) 1)
  calc
    (2 * q.2.1) * rootOddIntegral G q = q.2.1 *
        ∫ t in (-1 : ℝ)..1, rootMiddleDerivative G (q.1, t * q.2.1, q.2.2) := by
      dsimp only [rootOddIntegral]
      ring
    _ = G q - G (q.1, -q.2.1, q.2.2) := by
      simpa only [intervalIntegral.integral_const_mul, one_mul, neg_one_mul, Prod.mk.eta] using h

theorem rootOddIntegral_zero (G : ℝ × ℝ × ℝ → ℝ) (x θ : ℝ) :
    rootOddIntegral G (x, 0, θ) = rootMiddleDerivative G (x, 0, θ) := by
  simp only [rootOddIntegral, mul_zero, intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem rootOddIntegral_even {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (x z θ : ℝ) :
    rootOddIntegral G (x, -z, θ) = rootOddIntegral G (x, z, θ) := by
  by_cases hz : z = 0
  · simp only [hz, neg_zero]
  have hp := rootOddIntegral_factor hG (x, z, θ)
  have hm := rootOddIntegral_factor hG (x, -z, θ)
  simp only [neg_neg] at hm
  have heq : (2 * z) * rootOddIntegral G (x, -z, θ) =
      (2 * z) * rootOddIntegral G (x, z, θ) := by
    nlinarith only [hp, hm]
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hz) heq

/-- On the nonnegative halfspace, applying the even construction to the
integral model reproduces the prescribed odd quotient exactly. -/
theorem rootEven_rootOddIntegral_eqOn {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) :
    EqOn (rootEven (rootOddIntegral G)) (rootOdd G) (Ici (0 : ℝ) ×ˢ univ) := by
  intro p hp
  have he : rootEven (rootOddIntegral G) p =
      rootOddIntegral G (p.1, p.1 ^ (3 / 2 : ℝ), p.2) := by
    rw [rootEven, rootOddIntegral_even hG]
    ring
  rw [he]
  by_cases hx : p.1 = 0
  · rw [rootOdd, if_pos hx, hx, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0),
      rootOddIntegral_zero]
    exact (hasDerivAt_rootMiddleDerivative hG 0 0 p.2).deriv.symm
  · have hxpos : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hx)
    have hrne : p.1 ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hxpos _).ne'
    rw [rootOdd, if_neg hx]
    apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hrne)).mpr
    calc
      rootOddIntegral G (p.1, p.1 ^ (3 / 2 : ℝ), p.2) * (2 * p.1 ^ (3 / 2 : ℝ)) =
          (2 * p.1 ^ (3 / 2 : ℝ)) *
            rootOddIntegral G (p.1, p.1 ^ (3 / 2 : ℝ), p.2) := mul_comm _ _
      _ = _ := rootOddIntegral_factor hG _

end ContinuousFlexibility.Statements
