import ContinuousFlexibility.Analysis.IntervalWeakPrimitive
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integral primitives of integrable functions

The weak fundamental theorem below is proved by Fubini on a triangle. It
does not replace an integrable function by a pointwise differentiable one.
The final lemma gives an actual derivative when the integrand has a
continuous representative on the open interval.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Analysis

noncomputable section

/-- Integration by parts for the genuine Lebesgue primitive of an integrable
function, against a smooth test supported strictly inside the interval. -/
theorem integral_intervalPrimitive_mul_deriv_eq_neg {a b : ℝ} (hab : a < b)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Ioc a b)) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo a b) :
    (∫ x, (∫ y in a..x, g y) * deriv φ x) = -(∫ x, g x * φ x) := by
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  let W : Set (ℝ × ℝ) := {p | p.2 ≤ p.1}
  let K (x y : ℝ) : ℝ := W.indicator (fun p => deriv φ p.1 * g p.2) (x, y)
  have hW : MeasurableSet W := measurableSet_le measurable_snd measurable_fst
  have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hφdi : Integrable (deriv φ) μ := (hφd.continuous.intervalIntegrable a b).1
  have hK : Integrable (Function.uncurry K) (μ.prod μ) :=
    (hφdi.mul_prod hg).indicator hW
  have hmem : ∀ᵐ x ∂μ, x ∈ Ioc a b := ae_restrict_mem measurableSet_Ioc
  have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport
    (fun hh => (lt_irrefl b) (hφs hh).2)
  have hleft (x : ℝ) (hx : x ∈ Ioc a b) :
      (∫ y, K x y ∂μ) = (∫ y in a..x, g y) * deriv φ x := by
    have hfun : K x = (Iic x).indicator (fun y => deriv φ x * g y) := by
      funext y
      by_cases hy : y ≤ x <;> simp [K, W, hy]
    rw [hfun, integral_indicator measurableSet_Iic, integral_const_mul]
    have hr : μ.restrict (Iic x) = volume.restrict (Ioc a x) := by
      dsimp only [μ]
      rw [Measure.restrict_restrict measurableSet_Iic]
      congr 1
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      exact ⟨fun h => ⟨h.2.1, h.1⟩,
        fun h => ⟨h.2, h.1, h.2.trans hx.2⟩⟩
    rw [hr, ← intervalIntegral.integral_of_le hx.1.le, mul_comm]
  have hright (y : ℝ) (hy : y ∈ Ioc a b) :
      (∫ x, K x y ∂μ) = -(g y * φ y) := by
    have hfun : (fun x => K x y) = (Ici y).indicator (fun x => g y * deriv φ x) := by
      funext x
      by_cases hx : y ≤ x <;> simp [K, W, hx, mul_comm]
    rw [hfun, integral_indicator measurableSet_Ici, integral_const_mul]
    have hr : μ.restrict (Ici y) = volume.restrict (Ioc y b) := by
      dsimp only [μ]
      rw [Measure.restrict_restrict measurableSet_Ici]
      have hs : Ici y ∩ Ioc a b = Icc y b := by
        ext x
        simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
        exact ⟨fun h => ⟨h.1, h.2.2⟩,
          fun h => ⟨h.1, hy.1.trans_le h.1, h.2⟩⟩
      rw [hs, ← restrict_Ioc_eq_restrict_Icc]
    rw [hr, ← intervalIntegral.integral_of_le hy.2,
      intervalIntegral.integral_deriv_eq_sub
        (fun x _ => hφ.differentiable (by simp) x)
        (hφd.continuous.intervalIntegrable _ _), hφb]
    ring
  have hleft_full :
      (∫ x, (∫ y in a..x, g y) * deriv φ x) =
        ∫ x, (∫ y in a..x, g y) * deriv φ x ∂μ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxφ : x ∉ tsupport φ :=
      fun hh => hx ⟨(hφs hh).1, (hφs hh).2.le⟩
    have hxd : deriv φ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hxφ (tsupport_deriv_subset hh))
    rw [hxd, mul_zero]
  have hright_full : (∫ x, g x * φ x ∂μ) = ∫ x, g x * φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hh => hx ⟨(hφs hh).1, (hφs hh).2.le⟩)
    rw [hz, mul_zero]
  calc
    (∫ x, (∫ y in a..x, g y) * deriv φ x) =
        ∫ x, (∫ y, K x y ∂μ) ∂μ :=
      hleft_full.trans (integral_congr_ae (hmem.mono fun x hx => (hleft x hx).symm))
    _ = ∫ y, (∫ x, K x y ∂μ) ∂μ := integral_integral_swap hK
    _ = ∫ y, -(g y * φ y) ∂μ := integral_congr_ae (hmem.mono hright)
    _ = _ := by rw [integral_neg, hright_full]

/-- A globally continuous primitive obtained by extending an interval
integrand by zero. -/
def intervalL1Primitive (a b : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in a..x, (Ioo a b).indicator g y

theorem continuous_intervalL1Primitive {a b : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo a b)) : Continuous (intervalL1Primitive a b g) := by
  have hi : Integrable ((Ioo a b).indicator g) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hg
  exact hi.continuous_primitive a

/-- The zero extension in the primitive has no effect on interior tests. -/
theorem integral_intervalL1Primitive_mul_deriv_eq_neg {a b : ℝ} (hab : a < b)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Ioo a b)) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo a b) :
    (∫ x, intervalL1Primitive a b g x * deriv φ x) = -(∫ x, g x * φ x) := by
  have hi : Integrable ((Ioo a b).indicator g) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hg
  have he : (fun x => (Ioo a b).indicator g x * φ x) = fun x => g x * φ x := by
    funext x
    by_cases hx : x ∈ Ioo a b
    · rw [indicator_of_mem hx]
    · have hz : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hh => hx (hφs hh))
      rw [hz, mul_zero, mul_zero]
  simpa only [intervalL1Primitive, he] using
    integral_intervalPrimitive_mul_deriv_eq_neg hab hi.integrableOn hφ hφc hφs

/-- If an integrable function agrees almost everywhere with a continuous
function, its primitive has the latter as its actual interior derivative. -/
theorem hasDerivAt_intervalL1Primitive_of_ae_eq {a b : ℝ} {g h : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo a b))
    (he : g =ᵐ[volume.restrict (Ioo a b)] h)
    (hh : ContinuousOn h (Ioo a b)) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (intervalL1Primitive a b g) (h x) x := by
  have hae : (Ioo a b).indicator g =ᵐ[volume] (Ioo a b).indicator h := by
    have hi := (ae_restrict_iff' measurableSet_Ioo).mp he
    filter_upwards [hi] with y hy
    by_cases hyI : y ∈ Ioo a b
    · simp only [indicator_of_mem hyI, hy hyI]
    · simp only [indicator_of_notMem hyI]
  have hgi : Integrable ((Ioo a b).indicator g) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hg
  have hhi : Integrable ((Ioo a b).indicator h) := hgi.congr hae
  have hprim : intervalL1Primitive a b g =
      (fun t => ∫ y in a..t, (Ioo a b).indicator h y) := by
    funext t
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with y hy _hyI
    exact hy
  have hnear : (Ioo a b).indicator h =ᶠ[𝓝 x] h := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact indicator_of_mem hy h
  have hcont : ContinuousAt ((Ioo a b).indicator h) x :=
    (hh.continuousAt (isOpen_Ioo.mem_nhds hx)).congr_of_eventuallyEq hnear
  rw [hprim]
  simpa only [indicator_of_mem hx] using
    intervalIntegral.integral_hasDerivAt_right (hhi.intervalIntegrable (a := a) (b := x))
      hhi.aestronglyMeasurable.stronglyMeasurableAtFilter hcont

end

end ContinuousFlexibility.Analysis
