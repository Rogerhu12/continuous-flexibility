import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Smoothness of integrals along a scaled interval

For a continuous weight and a smooth function, integration over the fixed
compact interval preserves smooth dependence on the scale.  The derivative
tower is obtained by inserting one additional factor of the integration
variable at each differentiation.  Domination is local in the scale and
comes from continuity on a compact rectangle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

/-- A fixed continuous weight can be integrated against a smoothly scaled
function without losing smoothness in the scaling parameter. -/
theorem contDiff_scaled_intervalIntegral {w g : ℝ → ℝ}
    (hw : Continuous w) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun y : ℝ => ∫ t in (0 : ℝ)..1, w t * g (t * y)) := by
  let J : ℕ → ℝ → ℝ := fun n y =>
    ∫ t in (0 : ℝ)..1, w t * t ^ n * iteratedDeriv n g (t * y)
  have hjet_cont (n : ℕ) : Continuous (iteratedDeriv n g) :=
    hg.continuous_iteratedDeriv n (by simp)
  have hjet_deriv (n : ℕ) (x : ℝ) :
      HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g x) x := by
    have hn : Differentiable ℝ (iteratedDeriv n g) :=
      hg.differentiable_iteratedDeriv n
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
    simpa only [iteratedDeriv_succ] using (hn x).hasDerivAt
  have hsection (n : ℕ) (x : ℝ) :
      Continuous (fun t : ℝ => w t * t ^ n * iteratedDeriv n g (t * x)) :=
    (hw.mul (continuous_id.pow n)).mul
      ((hjet_cont n).comp (continuous_id.mul continuous_const))
  have hJ (n : ℕ) (y : ℝ) : HasDerivAt (J n) (J (n + 1) y) y := by
    have hcompact : IsCompact
        (Icc (y - 1) (y + 1) ×ˢ Icc (0 : ℝ) 1) :=
      isCompact_Icc.prod isCompact_Icc
    have hcont : Continuous (fun p : ℝ × ℝ =>
        w p.2 * p.2 ^ (n + 1) * iteratedDeriv (n + 1) g (p.2 * p.1)) :=
      ((hw.comp continuous_snd).mul (continuous_snd.pow (n + 1))).mul
        ((hjet_cont (n + 1)).comp (continuous_snd.mul continuous_fst))
    obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
    have hs : Ioo (y - 1) (y + 1) ∈ 𝓝 y :=
      Ioo_mem_nhds (by linarith) (by linarith)
    have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x t : ℝ => w t * t ^ n * iteratedDeriv n g (t * x))
      (F' := fun x t : ℝ => w t * t ^ (n + 1) * iteratedDeriv (n + 1) g (t * x))
      (μ := volume) (a := 0) (b := 1) (s := Ioo (y - 1) (y + 1))
      (bound := fun _ : ℝ => B) hs
      (Filter.Eventually.of_forall (fun x => (hsection n x).aestronglyMeasurable))
      ((hsection n y).intervalIntegrable 0 1)
      ((hsection (n + 1) y).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun t ht x hx => by
        have ht' : t ∈ Icc (0 : ℝ) 1 :=
          Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht)
        exact hB (x, t) ⟨⟨hx.1.le, hx.2.le⟩, ht'⟩))
      intervalIntegrable_const
      (Filter.Eventually.of_forall (fun t _ x _ => by
        have hchain := (hjet_deriv n (t * x)).comp x (hasDerivAt_const_mul t)
        have hprod := hchain.const_mul (w t * t ^ n)
        have hcoef : w t * t ^ (n + 1) * iteratedDeriv (n + 1) g (t * x) =
            (w t * t ^ n) * (iteratedDeriv (n + 1) g (t * x) * t) := by
          rw [pow_succ]
          ring
        rw [hcoef]
        exact hprod))
    exact h.2
  have hiter (n : ℕ) : iteratedDeriv n (J 0) = J n := by
    induction n with
    | zero => exact iteratedDeriv_zero
    | succ n ih =>
        rw [iteratedDeriv_succ, ih]
        exact funext (fun y => (hJ n y).deriv)
  have hsmooth : ContDiff ℝ ∞ (J 0) := by
    apply contDiff_of_differentiable_iteratedDeriv (n := ⊤)
    intro n _
    rw [hiter n]
    exact fun y => (hJ n y).differentiableAt
  simpa only [J, pow_zero, mul_one, iteratedDeriv_zero] using hsmooth

end ContinuousFlexibility.Analysis
