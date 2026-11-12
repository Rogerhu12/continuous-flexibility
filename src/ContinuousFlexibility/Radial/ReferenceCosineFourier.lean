import ContinuousFlexibility.Radial.ReferenceFourierL2

/-!
# The real, even, pi-periodic Fourier sector

Using the circle of period `π` makes its integer frequency `n` the physical
frequency `2*n`. The exact normalization agrees with the reference angular
mean, and even real fields have real coefficients invariant under `n ↦ -n`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal ComplexConjugate

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem radialAngularMean_eq_pi_mean {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi)
    (hf : IntervalIntegrable f volume 0 Real.pi) :
    radialAngularMean f = Real.pi⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, f θ := by
  have hi := hp.intervalIntegral_add_zsmul_eq (2 : ℤ) (0 : ℝ)
    (hp.intervalIntegrable₀ Real.pi_ne_zero hf)
  have hi' : (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) =
      2 * ∫ θ in (0 : ℝ)..Real.pi, f θ := by
    simpa [zsmul_eq_mul] using hi
  unfold radialAngularMean
  rw [hi']
  field_simp [Real.pi_ne_zero] <;> ring

/-- Fourier coefficients on the circle of period `π`. -/
def referencePiFourierCoeff (f : ℝ → ℝ) (n : ℤ) : ℂ :=
  fourierCoeffOn Real.pi_pos (fun θ => (f θ : ℂ)) n

theorem hasSum_sq_referencePiFourierCoeff {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) Real.pi))) :
    HasSum (fun n : ℤ => ‖referencePiFourierCoeff f n‖ ^ 2)
      (radialAngularMean (fun θ => f θ ^ 2)) := by
  have hsq : IntervalIntegrable (fun θ => f θ ^ 2) volume 0 Real.pi :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).2 hf.integrable_sq
  have hsp : Function.Periodic (fun θ => f θ ^ 2) Real.pi :=
    hp.comp (fun x : ℝ => x ^ 2)
  rw [radialAngularMean_eq_pi_mean hsp hsq]
  have hc : MemLp (fun θ => (f θ : ℂ)) 2
      (volume.restrict (Ioc (0 : ℝ) Real.pi)) := hf.ofReal
  simpa only [referencePiFourierCoeff, sub_zero, smul_eq_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      hasSum_sq_fourierCoeffOn Real.pi_pos hc

theorem referenceFourier_neg_argument {T : ℝ} (n : ℤ) (z : AddCircle T) :
    fourier n (-z) = fourier (-n) z := by
  simp only [fourier_apply, smul_neg, neg_smul]

theorem referenceFourierCoeff_neg_of_even {T : ℝ} [Fact (0 < T)]
    {f : AddCircle T → ℂ} (he : ∀ z, f (-z) = f z) (n : ℤ) :
    fourierCoeff f (-n) = fourierCoeff f n := by
  simpa only [fourierCoeff, smul_eq_mul,
    referenceFourier_neg_argument, he] using
      (integral_neg_eq_self
        (fun z : AddCircle T => fourier (-n) z * f z)
        AddCircle.haarAddCircle)

theorem referenceFourierCoeff_conj_of_real {T : ℝ} [Fact (0 < T)]
    (f : AddCircle T → ℝ) (n : ℤ) :
    conj (fourierCoeff (fun z => (f z : ℂ)) n) =
      fourierCoeff (fun z => (f z : ℂ)) (-n) := by
  unfold fourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with z
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, ← fourier_neg]

theorem periodic_lift_even {T : ℝ} {f : ℝ → ℝ}
    (hp : Function.Periodic f T) (he : ∀ θ, f (-θ) = f θ) :
    ∀ z : AddCircle T, hp.lift (-z) = hp.lift z := by
  intro z
  induction z using QuotientAddGroup.induction_on
  rename_i θ
  change f (-θ) = f θ
  exact he θ

theorem referencePiFourierCoeff_eq_lift (f : ℝ → ℝ)
    (hp : Function.Periodic f Real.pi) (n : ℤ) :
    referencePiFourierCoeff f n =
      fourierCoeff (fun z : AddCircle Real.pi => (hp.lift z : ℂ)) n := by
  have hlift : AddCircle.liftIoc Real.pi 0 (fun θ => (f θ : ℂ)) =
      fun z : AddCircle Real.pi => (hp.lift z : ℂ) := by
    apply AddCircle.Ioc_ext (p := Real.pi) 0
    intro θ hθ
    rw [AddCircle.liftIoc_coe_apply hθ, Function.Periodic.lift_coe]
  have hc := fourierCoeff_liftIoc_eq
    (T := Real.pi) (a := 0) (fun θ => (f θ : ℂ)) n
  rw [hlift] at hc
  simpa only [referencePiFourierCoeff, zero_add] using hc.symm

theorem referencePiFourierCoeff_neg {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (he : ∀ θ, f (-θ) = f θ) (n : ℤ) :
    referencePiFourierCoeff f (-n) = referencePiFourierCoeff f n := by
  rw [referencePiFourierCoeff_eq_lift f hp (-n),
    referencePiFourierCoeff_eq_lift f hp n]
  apply referenceFourierCoeff_neg_of_even
  intro z
  exact congrArg (fun x : ℝ => (x : ℂ)) (periodic_lift_even hp he z)

theorem referencePiFourierCoeff_im_eq_zero {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (he : ∀ θ, f (-θ) = f θ) (n : ℤ) :
    (referencePiFourierCoeff f n).im = 0 := by
  have hc : conj (referencePiFourierCoeff f n) = referencePiFourierCoeff f n := by
    rw [referencePiFourierCoeff_eq_lift f hp n]
    refine (referenceFourierCoeff_conj_of_real hp.lift n).trans ?_
    apply referenceFourierCoeff_neg_of_even
    intro z
    exact congrArg (fun x : ℝ => (x : ℂ)) (periodic_lift_even hp he z)
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

end ContinuousFlexibility.Statements
