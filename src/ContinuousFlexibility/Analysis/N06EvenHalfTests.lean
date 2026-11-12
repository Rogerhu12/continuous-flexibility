import ContinuousFlexibility.Analysis.N06AveragedWeakTests

/-!
# Even projection of the actual half-period physical tests

Reflection averaging preserves smoothness, the angular period and the
same compact radial support. Its integral over a complete period is the
original integral. These facts also apply to integrable operator values,
so no smoothness of a corrected coefficient is needed in the averaging
step of the physical left-column pairing.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

def n06EvenPart (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  (f p + f (p.1, -p.2)) / 2

theorem n06EvenPart_contDiff {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (n06EvenPart f) :=
  (hf.add (hf.comp (contDiff_fst.prodMk contDiff_snd.neg))).div_const 2

theorem n06EvenPart_even (f : PolarPoint → ℝ) (r θ : ℝ) :
    n06EvenPart f (r, -θ) = n06EvenPart f (r, θ) := by
  simp only [n06EvenPart, neg_neg]
  ring

theorem n06EvenPart_periodic {f : PolarPoint → ℝ} {t : ℝ}
    (hf : Function.Periodic f (0, t)) :
    Function.Periodic (n06EvenPart f) (0, t) := by
  intro p
  have hminus : f (p.1, -(p.2 + t)) = f (p.1, -p.2) := by
    have h := hf (p.1, -(p.2 + t))
    have he : (p.1, -(p.2 + t)) + (0, t) = (p.1, -p.2) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add, add_zero] <;> ring
    rw [he] at h
    exact h.symm
  simp only [n06EvenPart, hf p, Prod.fst_add, Prod.snd_add, add_zero, hminus]

theorem n06EvenPart_support {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : HasCompactRadialSupport D f) : HasCompactRadialSupport D (n06EvenPart f) := by
  obtain ⟨J, hJ, hJD, hzero⟩ := hf
  refine ⟨J, hJ, hJD, fun r hr θ => ?_⟩
  simp only [n06EvenPart, hzero r hr, zero_add, zero_div]

theorem n06EvenPart_test {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : RadialTest D f) : RadialTest D (n06EvenPart f) :=
  ⟨n06EvenPart_contDiff hf.1, n06EvenPart_periodic hf.2.1, n06EvenPart_support hf.2.2⟩

/-- Reflection preserves the integral over a full period, including
the totalized integral of a function not yet known to be integrable. -/
theorem n06_angularMean_reflection {f : ℝ → ℝ}
    (hf : Function.Periodic f Real.pi) :
    angularMean (fun θ => f (-θ)) = angularMean f := by
  have hshift : (∫ θ in -Real.pi..(0 : ℝ), f θ) =
      ∫ θ in (0 : ℝ)..Real.pi, f θ := by
    simpa only [neg_add_cancel, zero_add] using hf.intervalIntegral_add_eq (-Real.pi) 0
  unfold angularMean
  rw [intervalIntegral.integral_comp_neg, neg_zero, hshift]

/-- Actual integrability allows the two summands of the even projection
to be split. Only one original period is required. -/
theorem n06_angularMean_reflectionAverage {f : ℝ → ℝ}
    (hf : Function.Periodic f Real.pi)
    (hint : IntervalIntegrable f volume 0 Real.pi) :
    angularMean (fun θ => (f θ + f (-θ)) / 2) = angularMean f := by
  have hneg : IntervalIntegrable (fun θ => f (-θ)) volume 0 Real.pi := by
    simpa only [neg_zero, neg_neg] using
      (IntervalIntegrable.iff_comp_neg (f := f) (a := (0 : ℝ)) (b := -Real.pi)).mp
        (hf.intervalIntegrable₀ Real.pi_ne_zero hint (-Real.pi) 0).symm
  have he := n06_angularMean_reflection hf
  unfold angularMean at he ⊢
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hint hneg]
  linarith only [he]

/-- Equality almost everywhere suffices for the original angular mean. -/
theorem n06_angularMean_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    angularMean f = angularMean g := by
  unfold angularMean
  exact congrArg (fun x : ℝ => (1 / Real.pi) * x)
    (intervalIntegral.integral_congr_ae (h.mono (fun _ hx _ => hx)))

/-- An almost-everywhere period suffices for the reflection average.
This is the period furnished by a genuine planar atlas cover. -/
theorem n06_angularMean_reflectionAverage_ae {f : ℝ → ℝ}
    (hf : (fun θ => f (θ + Real.pi)) =ᵐ[volume] f)
    (hint : IntervalIntegrable f volume 0 Real.pi) :
    angularMean (fun θ => (f θ + f (-θ)) / 2) = angularMean f := by
  have hshift : (∫ θ in -Real.pi..(0 : ℝ), f θ) =
      ∫ θ in (0 : ℝ)..Real.pi, f θ := by
    calc
      _ = ∫ θ in -Real.pi..(0 : ℝ), f (θ + Real.pi) :=
        intervalIntegral.integral_congr_ae (hf.symm.mono (fun _ hx _ => hx))
      _ = _ := by
        rw [intervalIntegral.integral_comp_add_right]
        simp only [neg_add_cancel, zero_add]
  have hshiftI : IntervalIntegrable (fun θ => f (θ + Real.pi))
      volume (-Real.pi) 0 :=
    (IntervalIntegrable.comp_add_right_iff
      (f := f) (a := -Real.pi) (b := 0) (c := Real.pi)).mpr
      (by simpa only [neg_add_cancel, zero_add] using hint)
  have hminus : IntervalIntegrable f volume (-Real.pi) 0 :=
    hshiftI.congr_ae (ae_restrict_of_ae hf)
  have hneg : IntervalIntegrable (fun θ => f (-θ)) volume 0 Real.pi := by
    simpa only [neg_zero, neg_neg] using
      (IntervalIntegrable.iff_comp_neg (f := f) (a := (0 : ℝ)) (b := -Real.pi)).mp
        hminus.symm
  have he : angularMean (fun θ => f (-θ)) = angularMean f := by
    unfold angularMean
    rw [intervalIntegral.integral_comp_neg, neg_zero, hshift]
  unfold angularMean at he ⊢
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hint hneg]
  linarith only [he]

/-- An even periodic coefficient may be paired with the even part of
the test without changing the original half-period mean. -/
theorem n06_angularMean_evenPart_pairing
    {u f : ℝ → ℝ} (hu : Function.Periodic u Real.pi)
    (hf : Function.Periodic f Real.pi) (he : ∀ θ, u (-θ) = u θ)
    (hint : IntervalIntegrable (fun θ => u θ * f θ) volume 0 Real.pi) :
    angularMean (fun θ => u θ * ((f θ + f (-θ)) / 2)) =
      angularMean (fun θ => u θ * f θ) := by
  have heq : (fun θ => u θ * ((f θ + f (-θ)) / 2)) =
      fun θ => (u θ * f θ + u (-θ) * f (-θ)) / 2 := by
    funext θ
    rw [he]
    ring
  rw [heq]
  exact n06_angularMean_reflectionAverage (hu.mul hf) hint

/-- This pairing keeps the literal physical source mean. -/
theorem n06_sourceIntegral_evenPart_pairing
    (D : ReferenceData) {u f : PolarPoint → ℝ}
    (hu : Continuous u) (hf : Continuous f)
    (hup : Function.Periodic u (0, Real.pi))
    (hfp : Function.Periodic f (0, Real.pi))
    (hue : ∀ r θ, u (r, -θ) = u (r, θ)) :
    physicalSourceIntegral D (fun p => u p * n06EvenPart f p) =
      physicalSourceIntegral D (fun p => u p * f p) := by
  unfold physicalSourceIntegral
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only [n06EvenPart]
  apply n06_angularMean_evenPart_pairing
  · intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hup (r, θ)
  · intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hfp (r, θ)
  · exact hue r
  · exact ((hu.mul hf).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

end ContinuousFlexibility.Statements
