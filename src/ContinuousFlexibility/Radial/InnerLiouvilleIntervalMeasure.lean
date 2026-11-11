import ContinuousFlexibility.Radial.InnerSquareDensity
import ContinuousFlexibility.Radial.MorseCellLiouville

/-!
# The physical measure under a retained Liouville coordinate

Only positivity on the retained closed interval is required. The map
identity is for the restriction of the actual radialHilbertMeasure D.
The inverse coordinate is the existing invFunOn coordinate of that
same radius and interval.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff ENNReal

def innerLiouvilleIntervalAmplitude (R s : ℝ → ℝ) (lam x : ℝ) : ℝ :=
  sqrt (12 * lam) * s x * (deriv R x / R x)

theorem innerLiouvilleIntervalAmplitude_measurable {R s : ℝ → ℝ}
    (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s) (lam : ℝ) :
    Measurable (innerLiouvilleIntervalAmplitude R s lam) :=
  (measurable_const.mul hs.continuous.measurable).mul
    ((contDiff_infty_iff_deriv.mp hR).2.continuous.measurable.div hR.continuous.measurable)

theorem innerLiouvilleIntervalAmplitude_pos {R s : ℝ → ℝ} {lam x : ℝ}
    (hlam : 0 < lam) (hR : 0 < R x) (hv : 0 < deriv R x) (hs : 0 < s x) :
    0 < innerLiouvilleIntervalAmplitude R s lam x := by
  unfold innerLiouvilleIntervalAmplitude
  exact mul_pos (mul_pos (sqrt_pos.mpr (by positivity)) hs) (div_pos hv hR)

theorem innerLiouvilleIntervalAmplitude_sq {R s w : ℝ → ℝ} {lam x : ℝ}
    (hlam : 0 ≤ lam) (hR : R x ≠ 0)
    (hw : w (R x) = lam * s x ^ 2 * deriv R x) :
    innerLiouvilleIntervalAmplitude R s lam x ^ 2 =
      deriv R x * (12 * w (R x) / R x ^ 2) := by
  unfold innerLiouvilleIntervalAmplitude
  rw [mul_pow, mul_pow, sq_sqrt (mul_nonneg (by norm_num) hlam), hw]
  field_simp [hR] <;> ring

theorem innerLiouvilleIntervalCoordinate_continuousOn {R : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hR : ContDiff ℝ ∞ R)
    (hv : ∀ x ∈ Icc a b, 0 < deriv R x) :
    ContinuousOn (morseCellModelCoordinate R a b) (Ioo (R a) (R b)) := by
  rw [← hR.continuous.continuousOn.image_Ioo_of_strictMonoOn hab
    (morseCell_strictMonoOn hR hv)]
  rintro _ ⟨x, hx, rfl⟩
  exact (morseCellModelCoordinate_contDiffAt hR hv hx).continuousAt.continuousWithinAt

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)

/-- The exact Jacobian map into the same physical measure used by the
global radial problem. No global monotonicity of R is imposed. -/
theorem innerLiouvilleInterval_map_measure :
    Measure.map R ((volume.restrict (Ioo a b)).withDensity
      (fun x => ENNReal.ofReal (innerLiouvilleIntervalAmplitude R s lam x ^ 2))) =
      (radialHilbertMeasure D).restrict (Ioo (R a) (R b)) := by
  have hv : ∀ x ∈ Icc a b, 0 < deriv R x := fun x hx => (hp x hx).2.1
  have hmono := morseCell_strictMonoOn hR hv
  have him := hR.continuous.continuousOn.image_Ioo_of_strictMonoOn hab hmono
  have hJac (g : ℝ → ℝ≥0∞) :
      (∫⁻ r in Ioo (R a) (R b), g r) =
        ∫⁻ x in Ioo a b, ENNReal.ofReal (deriv R x) * g (R x) := by
    have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (fun x _ => (hR.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
      (hmono.injOn.mono Ioo_subset_Icc_self) g
    rw [him] at h
    refine h.trans ?_
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [abs_of_pos (hv x (Ioo_subset_Icc_self hx))]
  ext t ht
  rw [Measure.map_apply hR.continuous.measurable ht,
    withDensity_apply _ (hR.continuous.measurable ht),
    innerRadialHilbertMeasure_restrict D measurableSet_Ioo hcore,
    withDensity_apply _ ht,
    ← lintegral_indicator (hR.continuous.measurable ht),
    ← lintegral_indicator ht, hJac]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hx' := Ioo_subset_Icc_self hx
  by_cases hxt : R x ∈ t
  · simp only [mem_preimage, hxt, indicator_of_mem]
    rw [← ENNReal.ofReal_mul (hv x hx').le,
      ← innerLiouvilleIntervalAmplitude_sq hlam.le (hp x hx').1.ne' (hw x hx')]
  · simp only [mem_preimage, hxt, not_false_eq_true, indicator_of_notMem, mul_zero]

theorem innerLiouvilleInterval_measurePreserving :
    MeasurePreserving R
      ((volume.restrict (Ioo a b)).withDensity
        (fun x => ENNReal.ofReal (innerLiouvilleIntervalAmplitude R s lam x ^ 2)))
      ((radialHilbertMeasure D).restrict (Ioo (R a) (R b))) :=
  ⟨hR.continuous.measurable, innerLiouvilleInterval_map_measure D hab hlam hR hp hcore hw⟩

theorem innerLiouvilleIntervalAmplitude_ne_ae :
    ∀ᵐ x ∂volume.restrict (Ioo a b), innerLiouvilleIntervalAmplitude R s lam x ≠ 0 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have h := hp x (Ioo_subset_Icc_self hx)
  exact (innerLiouvilleIntervalAmplitude_pos hlam h.1 h.2.1 h.2.2).ne'

/-- A physical L² representative may be pulled back through the actual
radius without changing its almost everywhere class. -/
theorem innerLiouvilleInterval_pullback_ae {f g : ℝ → ℝ}
    (hfg : f =ᵐ[(radialHilbertMeasure D).restrict (Ioo (R a) (R b))] g) :
    (fun x => f (R x)) =ᵐ[volume.restrict (Ioo a b)] (fun x => g (R x)) := by
  have hmap := innerLiouvilleInterval_map_measure D hab hlam hR hp hcore hw
  have hh : f =ᵐ[Measure.map R ((volume.restrict (Ioo a b)).withDensity
      (fun x => ENNReal.ofReal (innerLiouvilleIntervalAmplitude R s lam x ^ 2)))] g := by
    rw [hmap]
    exact hfg
  exact (innerSquareDensity_base_ac (volume.restrict (Ioo a b))
    (innerLiouvilleIntervalAmplitude R s lam)
    (innerLiouvilleIntervalAmplitude_measurable hR hs lam)
    (innerLiouvilleIntervalAmplitude_ne_ae hlam hp)).ae_eq
      (ae_eq_comp hR.continuous.measurable.aemeasurable hh)

theorem innerLiouvilleInterval_memLp_iff (u : ℝ → ℝ)
    (hu : AEStronglyMeasurable u
      ((radialHilbertMeasure D).restrict (Ioo (R a) (R b)))) :
    MemLp u 2 ((radialHilbertMeasure D).restrict (Ioo (R a) (R b))) ↔
      MemLp (fun x => innerLiouvilleIntervalAmplitude R s lam x * u (R x))
        2 (volume.restrict (Ioo a b)) := by
  have hmap := innerLiouvilleInterval_map_measure D hab hlam hR hp hcore hw
  rw [← hmap] at hu ⊢
  rw [memLp_map_measure_iff hu hR.continuous.measurable.aemeasurable]
  simpa only [Function.comp_apply] using
    innerSquareDensity_memLp_iff (volume.restrict (Ioo a b))
      (innerLiouvilleIntervalAmplitude R s lam)
      (innerLiouvilleIntervalAmplitude_measurable hR hs lam)
      (innerLiouvilleIntervalAmplitude_ne_ae hlam hp) (u ∘ R)

end ContinuousFlexibility.Radial
