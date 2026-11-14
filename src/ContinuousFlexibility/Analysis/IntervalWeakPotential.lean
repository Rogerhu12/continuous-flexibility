module

public import ContinuousFlexibility.Analysis.IntervalWeakTestExtension
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Extending the weak equation with a continuous potential and border

The potential and the border are moved to the forcing before compressing the
tests. All integrals remain ordinary integrals on the finite interval. The
L² hypotheses supply the L¹ pairings with continuous coefficients, including
the product with any smooth test.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem interval_memLp_of_continuous {a b : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) : MemLp f 2 (volume.restrict (Ioo a b)) := by
  letI : IsFiniteMeasure (volume.restrict (Ioo a b)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top⟩
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable K
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hK ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩

theorem interval_integrable_mul_continuous {a b : ℝ} {u p : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a b))) (hp : Continuous p) :
    IntegrableOn (fun x => u x * p x) (Ioo a b) volume :=
  hu.integrable_mul (interval_memLp_of_continuous hp)

theorem intervalIntegrable_mul_continuous {a b : ℝ} (hab : a ≤ b)
    {u p : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hp : Continuous p) :
    IntervalIntegrable (fun x => u x * p x) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr
    (interval_integrable_mul_continuous hu hp)

theorem interval_memLp_integrable {a b : ℝ} {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a b))) :
    IntegrableOn u (Ioo a b) volume := by
  simpa only [mul_one] using interval_integrable_mul_continuous hu
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))

/-- Rewriting the potential term is justified by actual integrability. -/
theorem interval_weak_potential_expand {a b : ℝ} (hab : a ≤ b)
    {u w V φ : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hw : ContDiff ℝ ∞ w) (hV : Continuous V) (hφ : ContDiff ℝ ∞ φ) :
    (∫ x in a..b, u x *
      (deriv (fun y => w y * deriv φ y) x - V x * φ x)) =
      (∫ x in a..b, u x * deriv (fun y => w y * deriv φ y) x) -
        ∫ x in a..b, u x * (V x * φ x) := by
  have hφd := (contDiff_infty_iff_deriv.mp hφ).2
  have hflux := (contDiff_infty_iff_deriv.mp (hw.mul hφd)).2.continuous
  have hi₁ := intervalIntegrable_mul_continuous hab hu hflux
  have hi₂ := intervalIntegrable_mul_continuous hab hu (hV.mul hφ.continuous)
  simp_rw [mul_sub]
  exact intervalIntegral.integral_sub hi₁ hi₂

theorem interval_weak_forcing_expand {a b : ℝ} (hab : a ≤ b)
    {u f V g φ : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hV : Continuous V) (hg : Continuous g) (hφ : Continuous φ) (κ : ℝ) :
    (∫ x in a..b, (f x + u x * V x - κ * g x) * φ x) =
      (∫ x in a..b, f x * φ x) +
        (∫ x in a..b, u x * (V x * φ x)) -
          κ * (∫ x in a..b, g x * φ x) := by
  have hfφ := intervalIntegrable_mul_continuous hab hf hφ
  have huVφ : IntervalIntegrable (fun x => u x * (V x * φ x)) volume a b :=
    intervalIntegrable_mul_continuous hab hu (hV.mul hφ)
  have hgφ : IntervalIntegrable (fun x => g x * φ x) volume a b :=
    (hg.mul hφ).intervalIntegrable _ _
  have heq : (fun x => (f x + u x * V x - κ * g x) * φ x) =
      (fun x => (f x * φ x + u x * (V x * φ x)) - κ * (g x * φ x)) := by
    funext x
    ring
  rw [heq, intervalIntegral.integral_sub (hfφ.add huVφ) (hgφ.const_mul κ),
    intervalIntegral.integral_add hfφ huVφ, intervalIntegral.integral_const_mul]

/-- A bounded potential does not change the test compression argument. -/
theorem extend_weak_potential_tests_interval {a b : ℝ} (hab : a < b)
    {u f w V g : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hw : ContDiff ℝ ∞ w) (hV : Continuous V) (hg : Continuous g) (κ : ℝ)
    (hstrict : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x in a..b, u x *
          (deriv (fun y => w y * deriv φ y) x - V x * φ x)) +
            κ * (∫ x in a..b, g x * φ x) = ∫ x in a..b, f x * φ x)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : Function.support ψ ⊆ Ioo a b) :
    (∫ x in a..b, u x *
      (deriv (fun y => w y * deriv ψ y) x - V x * ψ x)) +
        κ * (∫ x in a..b, g x * ψ x) = ∫ x in a..b, f x * ψ x := by
  let H : ℝ → ℝ := fun x => f x + u x * V x - κ * g x
  have hH : IntegrableOn H (Ioo a b) volume :=
    ((interval_memLp_integrable hf).add
      (interval_integrable_mul_continuous hu hV)).sub
        ((interval_memLp_integrable (interval_memLp_of_continuous hg)).const_mul κ)
  have hstrict' : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x in a..b, u x * deriv (fun y => w y * deriv φ y) x) =
          ∫ x in a..b, H x * φ x := by
    intro φ hφ hφc hφs
    have h := hstrict φ hφ hφc hφs
    rw [interval_weak_potential_expand hab.le hu hw hV hφ] at h
    change _ = ∫ x in a..b, (f x + u x * V x - κ * g x) * φ x
    rw [interval_weak_forcing_expand hab.le hu hf hV hg hφ.continuous κ]
    linarith
  have heq := extend_weak_divergence_tests_interval hab
    (interval_memLp_integrable hu) hH hw hstrict' hψ hψc hψs
  change (∫ x in a..b, u x * deriv (fun y => w y * deriv ψ y) x) =
    ∫ x in a..b, (f x + u x * V x - κ * g x) * ψ x at heq
  rw [interval_weak_forcing_expand hab.le hu hf hV hg hψ.continuous κ] at heq
  rw [interval_weak_potential_expand hab.le hu hw hV hψ]
  linarith

end ContinuousFlexibility.Analysis
