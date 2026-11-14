module

public import ContinuousFlexibility.Radial.InnerLiouvillePhysicalOperators

/-!
# A buffer-supported leading field pays only the buffer velocity

The same actual field lift is used for the leading cutoff and the
remainder. This refinement uses the smaller velocity bound only where
the leading Lp vector is nonzero; no bound on the opposite cap is charged.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)

theorem innerLiouvilleFieldLift_norm_le_velocity (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ‖innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f‖ ≤
      Real.sqrt 12 * ‖innerLiouvilleVelocityMultiplier R a b hR U hU hv f‖ := by
  rw [innerLiouvilleFieldLift_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 12), innerL2ZeroExtension_norm _ _ measurableSet_Ioo,
    LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_left
    (innerL2Restriction_norm_apply_le volume (Ioo a b) _)
    (Real.sqrt_nonneg 12)

theorem innerLiouvilleFieldLift_norm_le_on_support (f : Lp ℝ 2 (volume : Measure ℝ))
    {Ucap : ℝ} (hcap : 0 ≤ Ucap)
    (hf : ∀ᵐ x ∂volume, x ∈ Ioo a b → f x ≠ 0 → |deriv R x / R x| ≤ Ucap) :
    ‖innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f‖ ≤
      Real.sqrt 12 * Ucap * ‖f‖ := by
  have hV : ‖innerLiouvilleVelocityMultiplier R a b hR U hU hv f‖ ≤ Ucap * ‖f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [innerLiouvilleVelocityMultiplier_ae R a b hR U hU hv f, hf] with
      x hx hf'
    rw [hx, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    by_cases hi : x ∈ Ioo a b
    · rw [innerLiouvilleModelVelocity, indicator_of_mem hi]
      by_cases hz : f x = 0
      · simp only [hz, abs_zero, mul_zero, le_refl]
      · exact mul_le_mul_of_nonneg_right (hf' hi hz) (abs_nonneg (f x))
    · rw [innerLiouvilleModelVelocity, indicator_of_notMem hi, abs_zero, zero_mul]
      exact mul_nonneg hcap (abs_nonneg (f x))
  calc
    _ ≤ Real.sqrt 12 * ‖innerLiouvilleVelocityMultiplier R a b hR U hU hv f‖ :=
      innerLiouvilleFieldLift_norm_le_velocity D hab hlam hR hs hp hcore hw U hU hv f
    _ ≤ Real.sqrt 12 * (Ucap * ‖f‖) :=
      mul_le_mul_of_nonneg_left hV (Real.sqrt_nonneg 12)
    _ = _ := (mul_assoc _ _ _).symm

/-- A genuine cutoff support and a geometric velocity estimate imply
the local leading estimate for the same field lift. -/
theorem innerLiouvilleFieldLift_norm_le_of_buffer (f : Lp ℝ 2 (volume : Measure ℝ))
    (buffer : Set ℝ) {Ucap : ℝ} (hcap : 0 ≤ Ucap)
    (hsupport : ∀ᵐ x ∂volume, f x ≠ 0 → x ∈ buffer)
    (hbuffer : ∀ x ∈ buffer, |deriv R x / R x| ≤ Ucap) :
    ‖innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f‖ ≤
      Real.sqrt 12 * Ucap * ‖f‖ := by
  apply innerLiouvilleFieldLift_norm_le_on_support D hab hlam hR hs hp hcore hw U hU hv f hcap
  filter_upwards [hsupport] with x hx
  intro _hi hne
  exact hbuffer x (hx hne)

end ContinuousFlexibility.Radial
