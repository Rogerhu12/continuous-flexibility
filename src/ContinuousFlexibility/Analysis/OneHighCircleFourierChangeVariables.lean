import ContinuousFlexibility.Analysis.OneHighCircleFourierParseval
import ContinuousFlexibility.Analysis.OneHighPeriodicJets

/-!
# The genuine circle `L²` change-of-variables estimate

A lift satisfying `h (x + P) = h x + P` maps one period to one period.
Substitution with its actual derivative, followed by periodicity, proves the
estimate. No inverse map or pre-assumed composition estimate is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Function
open scoped ENNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Substitution and the lower derivative bound control the actual square
integral over one period. -/
theorem circleLift_integral_comp_sq_le {P c : ℝ} (hP : 0 < P)
    (v : ℝ → E) (hv : Continuous v) (hp : Periodic v P)
    (h dh : ℝ → ℝ) (hderiv : ∀ x, HasDerivAt h (dh x) x)
    (hdh : Continuous dh) (hlift : ∀ x, h (x + P) = h x + P)
    (hlower : ∀ x, c ≤ dh x) :
    c * (∫ x in (0 : ℝ)..P, ‖v (h x)‖ ^ 2) ≤
      ∫ x in (0 : ℝ)..P, ‖v x‖ ^ 2 := by
  have hh : Continuous h := continuous_iff_continuousAt.mpr fun x => (hderiv x).continuousAt
  have hv2 : Continuous (fun x => ‖v x‖ ^ 2) := hv.norm.pow 2
  have hp2 : Periodic (fun x => ‖v x‖ ^ 2) P := by
    intro x
    rw [hp x]
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := P) (fun x _ => hderiv x) hdh.continuousOn hv2
  have hend : h P = h 0 + P := by simpa only [zero_add] using hlift 0
  rw [hend, hp2.intervalIntegral_add_eq (h 0) 0, zero_add] at hsub
  calc
    c * (∫ x in (0 : ℝ)..P, ‖v (h x)‖ ^ 2) =
        ∫ x in (0 : ℝ)..P, c * ‖v (h x)‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ x in (0 : ℝ)..P, ‖v (h x)‖ ^ 2 * dh x := by
      apply intervalIntegral.integral_mono_on hP.le
        ((continuous_const.mul (hv2.comp hh)).intervalIntegrable 0 P)
        (((hv2.comp hh).mul hdh).intervalIntegrable 0 P)
      intro x _
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hlower x) (sq_nonneg ‖v (h x)‖)
    _ = ∫ x in (0 : ℝ)..P, ‖v x‖ ^ 2 := hsub

private theorem sqrt_le_inv_sqrt_mul_of_mul_le {c A B : ℝ} (hc : 0 < c)
    (h : c * A ≤ B) : Real.sqrt A ≤ (Real.sqrt c)⁻¹ * Real.sqrt B := by
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul hc.le] at hs
  rw [inv_mul_eq_div, le_div_iff₀ (Real.sqrt_pos.mpr hc)]
  simpa only [mul_comm] using hs

variable {P : ℝ} [hP : Fact (0 < P)]

/-- The actual normalized-Haar `L²` norm expressed by one physical period. -/
theorem circle_l2_toReal_eq_sqrt_interval (f : C(AddCircle P, E)) :
    (eLpNorm f 2 AddCircle.haarAddCircle).toReal =
      Real.sqrt (P⁻¹ * ∫ x in (0 : ℝ)..P, ‖f (x : AddCircle P)‖ ^ 2) := by
  rw [toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top
      (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℝ f).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [Real.sqrt_eq_rpow, one_div]
  congr 1
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage P 0 (fun θ => ‖f θ‖ ^ 2)]
  simp only [zero_add, smul_eq_mul]

/-- The actual circle `L²` change-of-variables bound. The equality premise
identifies the composed continuous function pointwise on the quotient. -/
theorem circle_l2_comp_le (f g : C(AddCircle P, E)) {c : ℝ} (hc : 0 < c)
    (h dh : ℝ → ℝ) (hderiv : ∀ x, HasDerivAt h (dh x) x)
    (hdh : Continuous dh) (hlift : ∀ x, h (x + P) = h x + P)
    (hlower : ∀ x, c ≤ dh x)
    (hcomp : ∀ x : ℝ, g (x : AddCircle P) = f (h x : AddCircle P)) :
    (eLpNorm g 2 AddCircle.haarAddCircle).toReal ≤
      (Real.sqrt c)⁻¹ * (eLpNorm f 2 AddCircle.haarAddCircle).toReal := by
  have hv : Continuous (fun x : ℝ => f (x : AddCircle P)) :=
    f.continuous.comp (AddCircle.continuous_mk' P)
  have hp : Periodic (fun x : ℝ => f (x : AddCircle P)) P := by
    intro x
    rw [AddCircle.coe_add_period]
  have hraw := circleLift_integral_comp_sq_le hP.out
    (fun x : ℝ => f (x : AddCircle P)) hv hp h dh hderiv hdh hlift hlower
  have hg : (∫ x in (0 : ℝ)..P, ‖g (x : AddCircle P)‖ ^ 2) =
      ∫ x in (0 : ℝ)..P, ‖f (h x : AddCircle P)‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _
    rw [hcomp x]
  rw [circle_l2_toReal_eq_sqrt_interval, circle_l2_toReal_eq_sqrt_interval]
  apply sqrt_le_inv_sqrt_mul_of_mul_le hc
  rw [hg]
  calc
    c * (P⁻¹ * ∫ x in (0 : ℝ)..P, ‖f (h x : AddCircle P)‖ ^ 2) =
        P⁻¹ * (c * ∫ x in (0 : ℝ)..P, ‖f (h x : AddCircle P)‖ ^ 2) := by ring
    _ ≤ P⁻¹ * ∫ x in (0 : ℝ)..P, ‖f (x : AddCircle P)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hP.out.le)

/-- A periodic function remains periodic after a degree-one circle lift. -/
theorem periodic_comp_circleLift {E : Type*} {v : ℝ → E} (hp : Periodic v P)
    {h : ℝ → ℝ} (hlift : ∀ x, h (x + P) = h x + P) : Periodic (v ∘ h) P := by
  intro x
  simp only [Function.comp_apply, hlift, hp]

/-- The base composition estimate for genuine smooth periodic lifts.
All circle representatives and derivatives are constructed from the input. -/
theorem periodicCircleJet_l2_comp_le (v : ℝ → E) (hp : Periodic v P)
    (hv : ContDiff ℝ ∞ v) (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x, c ≤ deriv h x) :
    (eLpNorm (periodicCircleJet (v ∘ h) (periodic_comp_circleLift hp hlift)
      (hv.comp hh) 0) 2 AddCircle.haarAddCircle).toReal ≤
      (Real.sqrt c)⁻¹ *
        (eLpNorm (periodicCircleJet v hp hv 0) 2 AddCircle.haarAddCircle).toReal := by
  refine circle_l2_comp_le (periodicCircleJet v hp hv 0)
    (periodicCircleJet (v ∘ h) (periodic_comp_circleLift hp hlift) (hv.comp hh) 0)
    hc h (deriv h) (fun x => (hh.differentiable (by simp) x).hasDerivAt)
    ?_ hlift hlower ?_
  · simpa only [iteratedDeriv_one] using hh.continuous_iteratedDeriv 1 (by simp)
  · intro x
    simp only [periodicCircleJet_coe_apply, iteratedDeriv_zero, Function.comp_apply]

end ContinuousFlexibility.Analysis
