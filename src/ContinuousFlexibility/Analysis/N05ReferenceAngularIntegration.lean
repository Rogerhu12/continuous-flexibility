import ContinuousFlexibility.Analysis.SpacesCircleFourierJets
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Angular integration by parts on an arbitrary period

The reference graph uses a full period of length `2π`. This form of the
ordinary periodic integration identity keeps the period explicit and
works for every derivative order.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem n05_periodic_iteratedDeriv {f : ℝ → ℝ} {T : ℝ}
    (hp : Function.Periodic f T) (b : ℕ) :
    Function.Periodic (iteratedDeriv b f) T := by
  intro x
  have hshift : (fun t : ℝ => f (t + T)) = f := funext hp
  have h := congrFun (iteratedDeriv_comp_add_const b f T) x
  rw [hshift] at h
  exact h.symm

theorem n05_integral_periodic_deriv_mul {f φ : ℝ → ℝ} {T : ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ)
    (hfp : Function.Periodic f T) (hφp : Function.Periodic φ T) :
    (∫ x in (0 : ℝ)..T, deriv f x * φ x) =
      -(∫ x in (0 : ℝ)..T, f x * deriv φ x) := by
  have hfend : f T = f 0 := by simpa only [zero_add] using hfp 0
  have hφend : φ T = φ 0 := by simpa only [zero_add] using hφp 0
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := T)
    (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
    (fun x _ => (hφ.differentiable (by simp) x).hasDerivAt)
    ((contDiff_infty_iff_deriv.mp hf).2.continuous.intervalIntegrable 0 T)
    ((contDiff_infty_iff_deriv.mp hφ).2.continuous.intervalIntegrable 0 T)
  rw [hfend, hφend, sub_self, zero_sub] at hIBP
  linarith

theorem n05_integral_periodic_iteratedDeriv_mul {f φ : ℝ → ℝ} {T : ℝ}
    (hf : ContDiff ℝ ∞ f) (hfp : Function.Periodic f T) (b : ℕ)
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ T) :
    (∫ x in (0 : ℝ)..T, iteratedDeriv b f x * φ x) =
      (-1 : ℝ) ^ b * ∫ x in (0 : ℝ)..T, f x * iteratedDeriv b φ x := by
  induction b generalizing φ with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ b ih =>
    have hφder : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    have hφderp : Function.Periodic (deriv φ) T := by
      simpa only [iteratedDeriv_one] using n05_periodic_iteratedDeriv hφp 1
    calc
      (∫ x in (0 : ℝ)..T, iteratedDeriv (b + 1) f x * φ x) =
          -(∫ x in (0 : ℝ)..T, iteratedDeriv b f x * deriv φ x) := by
        rw [iteratedDeriv_succ]
        exact n05_integral_periodic_deriv_mul
          (circleFourier_contDiff_iteratedDeriv hf b) hφ
          (n05_periodic_iteratedDeriv hfp b) hφp
      _ = -((-1 : ℝ) ^ b * ∫ x in (0 : ℝ)..T,
          f x * iteratedDeriv b (deriv φ) x) :=
        congrArg Neg.neg (ih hφder hφderp)
      _ = _ := by
        rw [iteratedDeriv_succ', pow_succ]
        ring

end ContinuousFlexibility.Radial
