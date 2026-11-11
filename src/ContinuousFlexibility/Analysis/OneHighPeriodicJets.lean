import ContinuousFlexibility.Analysis.OneHighCircleFourierDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Ring.Periodic

/-!
# Genuine derivative towers of smooth periodic functions

The circle Fourier estimates use continuous circle functions and identities
for their successive actual derivatives. Here that entire tower is constructed
from an ordinary smooth periodic lift. Thus the applications do not assume a
separate family of jets, nor any derivative identity or frequency estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : ℝ} [Fact (0 < P)]

/-- Translation invariance of actual iterated derivatives preserves the
given period, including when the lift is not differentiable. -/
theorem periodic_iteratedDeriv {v : ℝ → E} (hp : Periodic v P) (n : ℕ) :
    Periodic (iteratedDeriv n v) P := by
  have he : (fun x : ℝ => v (x + P)) = v := funext hp
  have h := congrArg (fun f : ℝ → E => iteratedDeriv n f) he
  rw [iteratedDeriv_comp_add_const] at h
  exact fun x => congrFun h x

private theorem continuous_periodic_lift {v : ℝ → E}
    (hp : Periodic v P) (hv : Continuous v) : Continuous hp.lift := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples P)).continuous_iff.mpr
  have he : (hp.lift ∘ (QuotientAddGroup.mk : ℝ → AddCircle P)) = v := by
    funext x
    exact hp.lift_coe x
  rw [he]
  exact hv

/-- The actual nth derivative, descended to the circle. -/
def periodicCircleJet (v : ℝ → E) (hp : Periodic v P) (hv : ContDiff ℝ ∞ v)
    (n : ℕ) : C(AddCircle P, E) :=
  ⟨(periodic_iteratedDeriv hp n).lift,
    continuous_periodic_lift (periodic_iteratedDeriv hp n)
      (hv.continuous_iteratedDeriv n (by simp))⟩

@[simp] theorem periodicCircleJet_coe_apply (v : ℝ → E) (hp : Periodic v P)
    (hv : ContDiff ℝ ∞ v) (n : ℕ) (x : ℝ) :
    periodicCircleJet v hp hv n (x : AddCircle P) = iteratedDeriv n v x :=
  (periodic_iteratedDeriv hp n).lift_coe x

/-- All derivative identities in the continuous circle tower follow from
smoothness of the original periodic lift. -/
theorem periodicCircleJet_hasDerivAt (v : ℝ → E) (hp : Periodic v P)
    (hv : ContDiff ℝ ∞ v) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => periodicCircleJet v hp hv n (y : AddCircle P))
      (periodicCircleJet v hp hv (n + 1) (x : AddCircle P)) x := by
  simp only [periodicCircleJet_coe_apply, iteratedDeriv_succ]
  have hn : (n : ℕ∞ω) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)
  exact (hv.differentiable_iteratedDeriv n hn x).hasDerivAt

/-- Every mode of every actual derivative has the physical multiplier
of the original smooth periodic function. -/
theorem periodicCircleJet_fourierCoeff (v : ℝ → ℂ) (hp : Periodic v P)
    (hv : ContDiff ℝ ∞ v) (k : ℕ) (n : ℤ) :
    fourierCoeff (periodicCircleJet v hp hv k) n =
      (Complex.I * (circlePhysicalFrequency P n : ℂ)) ^ k *
        fourierCoeff (periodicCircleJet v hp hv 0) n :=
  circle_fourierCoeff_iterated_derivatives (periodicCircleJet v hp hv)
    (periodicCircleJet_hasDerivAt v hp hv) k n

end ContinuousFlexibility.Analysis
