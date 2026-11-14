module

public import ContinuousFlexibility.Analysis.CylinderTestPairing
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration by parts for actual cylinder tests

Compact radial support removes the two radial boundary terms. Angular
periodicity removes the boundary term between `0` and `π`. Iterating
these two ordinary one-variable identities proves the exact weak mixed
derivative relation used by the physical graph.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

@[simp] theorem spaces_mixedDerivative_zero (f : PolarPoint → ℝ) :
    mixedDerivative 0 0 f = f := by
  funext p
  simp only [mixedDerivative, iteratedDeriv_zero, Prod.eta]

/-- Compact radial support and continuity suffice for cylinder integrability. -/
theorem spaces_integrable_cylinder_of_radial_support {f : PolarPoint → ℝ}
    (hf : Continuous f) {R : ℝ} (hR : ∀ p : PolarPoint, R ≤ |p.1| → f p = 0) :
    Integrable f materialCylinderMeasure := by
  let K : Set PolarPoint := Icc (-R) R ×ˢ Icc 0 Real.pi
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  let : IsFiniteMeasureOnCompacts materialCylinderMeasure := by
    unfold materialCylinderMeasure
    infer_instance
  have hi : Integrable (K.indicator f) materialCylinderMeasure :=
    (hf.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have hstrip : ∀ᵐ p ∂materialCylinderMeasure, p.2 ∈ Ioc (0 : ℝ) Real.pi :=
    (ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioc)).mono (fun p hp => hp.2)
  apply hi.congr
  filter_upwards [hstrip] with p hp
  by_cases hpK : p ∈ K
  · exact indicator_of_mem hpK f
  · have hlarge : R ≤ |p.1| := (lt_of_not_ge (fun hsmall =>
      hpK ⟨abs_le.mp hsmall, Ioc_subset_Icc_self hp⟩)).le
    rw [indicator_of_notMem hpK, hR p hlarge]

theorem IsCylinderTest.spaces_integrable {φ : PolarPoint → ℝ} (hφ : IsCylinderTest φ) :
    Integrable φ materialCylinderMeasure := by
  obtain ⟨R, _, hR⟩ := hφ.2.2
  exact spaces_integrable_cylinder_of_radial_support hφ.1.continuous hR

theorem spaces_integrable_mul_cylinderTest {f φ : PolarPoint → ℝ}
    (hf : Continuous f) (hφ : IsCylinderTest φ) :
    Integrable (fun p => f p * φ p) materialCylinderMeasure := by
  obtain ⟨R, _, hR⟩ := hφ.2.2
  apply spaces_integrable_cylinder_of_radial_support (R := R) (hf.mul hφ.1.continuous)
  intro p hp
  simp only [Pi.mul_apply, hR p hp, mul_zero]

theorem IsCylinderTest.spaces_radialPartial {φ : PolarPoint → ℝ} (hφ : IsCylinderTest φ) :
    IsCylinderTest (radialPartial φ) := by
  have he := radialPartial_mixedDerivative hφ.1 0 0
  rw [spaces_mixedDerivative_zero] at he
  rw [he]
  exact hφ.mixedDerivative 1 0

theorem IsCylinderTest.spaces_angularPartial {φ : PolarPoint → ℝ} (hφ : IsCylinderTest φ) :
    IsCylinderTest (angularPartial φ) := by
  have he := angularPartial_mixedDerivative hφ.1 0 0
  rw [spaces_mixedDerivative_zero] at he
  rw [he]
  exact hφ.mixedDerivative 0 1

theorem IsCylinderTest.spaces_mul_left {f φ : PolarPoint → ℝ}
    (hφ : IsCylinderTest φ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (0, Real.pi)) :
    IsCylinderTest (fun p => f p * φ p) := by
  obtain ⟨R, hR, hz⟩ := hφ.2.2
  refine ⟨hf.mul hφ.1, hp.mul hφ.2.1, R, hR, ?_⟩
  intro p hpR
  dsimp only
  rw [hz p hpR, mul_zero]

private theorem spaces_integrable_radial_slice {φ : PolarPoint → ℝ}
    (hφ : IsCylinderTest φ) (θ : ℝ) : Integrable (fun x => φ (x, θ)) volume := by
  obtain ⟨R, _, hR⟩ := hφ.2.2
  have hc : HasCompactSupport (fun x : ℝ => φ (x, θ)) := by
    apply HasCompactSupport.intro' isCompact_Icc isClosed_Icc
    intro x hx
    exact hR (x, θ) ((lt_of_not_ge (fun h => hx (abs_le.mp h))).le)
  exact (hφ.1.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport hc

/-- The integral of a radial derivative of a cylinder test is zero. -/
theorem spaces_integral_radialPartial_cylinderTest {φ : PolarPoint → ℝ}
    (hφ : IsCylinderTest φ) : (∫ p, radialPartial φ p ∂materialCylinderMeasure) = 0 := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  have hi := hφ.spaces_radialPartial.spaces_integrable
  rw [materialCylinderMeasure_eq_prod] at hi ⊢
  rw [integral_prod_symm _ hi]
  have hz (θ : ℝ) : (∫ x : ℝ, radialPartial φ (x, θ)) = 0 := by
    apply integral_eq_zero_of_hasDerivAt_of_integrable
    · intro x
      exact ((hφ.1.differentiable (by simp) (x, θ)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x θ)))
    · exact spaces_integrable_radial_slice hφ.spaces_radialPartial θ
    · exact spaces_integrable_radial_slice hφ θ
  simp only [hz, integral_zero]

/-- The integral of an angular derivative of a cylinder test is zero. -/
theorem spaces_integral_angularPartial_cylinderTest {φ : PolarPoint → ℝ}
    (hφ : IsCylinderTest φ) : (∫ p, angularPartial φ p ∂materialCylinderMeasure) = 0 := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  have hi := hφ.spaces_angularPartial.spaces_integrable
  rw [materialCylinderMeasure_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  have hz (x : ℝ) : (∫ θ, angularPartial φ (x, θ) ∂angleMeasure) = 0 := by
    have hd (θ : ℝ) : HasDerivAt (fun t : ℝ => φ (x, t)) (angularPartial φ (x, θ)) θ :=
      (hφ.1.differentiable (by simp) (x, θ)).hasFDerivAt.comp_hasDerivAt θ
        ((hasDerivAt_const θ x).prodMk (hasDerivAt_id θ))
    have hint : IntervalIntegrable (fun θ => angularPartial φ (x, θ)) volume 0 Real.pi :=
      ((contDiff_cylinder_angularPartial hφ.1).continuous.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ) hint
    rw [intervalIntegral.integral_of_le Real.pi_pos.le] at h
    have he : φ (x, Real.pi) = φ (x, 0) := by
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using hφ.2.1 (x, 0)
    simpa only [angleMeasure, he, sub_self] using h
  simp only [hz, integral_zero]

/-- Radial integration by parts against a genuine cylinder test. -/
theorem spaces_integral_radialPartial_mul {f φ : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (0, Real.pi)) (hφ : IsCylinderTest φ) :
    (∫ p, radialPartial f p * φ p ∂materialCylinderMeasure) =
      -(∫ p, f p * radialPartial φ p ∂materialCylinderMeasure) := by
  have hz := spaces_integral_radialPartial_cylinderTest (hφ.spaces_mul_left hf hp)
  have he : radialPartial (fun p => f p * φ p) =
      fun p => radialPartial f p * φ p + f p * radialPartial φ p :=
    funext (fun p => radialPartial_mul (hf.differentiable (by simp) p)
      (hφ.1.differentiable (by simp) p))
  rw [he, integral_add
    (spaces_integrable_mul_cylinderTest (contDiff_cylinder_radialPartial hf).continuous hφ)
    (spaces_integrable_mul_cylinderTest hf.continuous hφ.spaces_radialPartial)] at hz
  linarith

/-- Angular integration by parts against a genuine cylinder test. -/
theorem spaces_integral_angularPartial_mul {f φ : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (0, Real.pi)) (hφ : IsCylinderTest φ) :
    (∫ p, angularPartial f p * φ p ∂materialCylinderMeasure) =
      -(∫ p, f p * angularPartial φ p ∂materialCylinderMeasure) := by
  have hz := spaces_integral_angularPartial_cylinderTest (hφ.spaces_mul_left hf hp)
  have he : angularPartial (fun p => f p * φ p) =
      fun p => angularPartial f p * φ p + f p * angularPartial φ p :=
    funext (fun p => angularPartial_mul (hf.differentiable (by simp) p)
      (hφ.1.differentiable (by simp) p))
  rw [he, integral_add
    (spaces_integrable_mul_cylinderTest (contDiff_cylinder_angularPartial hf).continuous hφ)
    (spaces_integrable_mul_cylinderTest hf.continuous hφ.spaces_angularPartial)] at hz
  linarith

/-- The full mixed integration-by-parts identity for smooth periodic functions. -/
theorem spaces_integral_mixedDerivative_mul {f φ : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (0, Real.pi)) (hφ : IsCylinderTest φ)
    (a b : ℕ) :
    (∫ p, mixedDerivative a b f p * φ p ∂materialCylinderMeasure) =
      (-1 : ℝ) ^ (a + b) * ∫ p, f p * mixedDerivative a b φ p ∂materialCylinderMeasure := by
  have hpcoord (x : ℝ) : Function.Periodic (fun θ => f (x, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hp (x, θ)
  have hjp (i j : ℕ) : Function.Periodic (mixedDerivative i j f) (0, Real.pi) := by
    rintro ⟨x, θ⟩
    simpa only [Prod.mk_add_mk, add_zero] using mixedDerivative_angular_periodic hpcoord i j x θ
  induction a generalizing φ with
  | zero =>
    induction b generalizing φ with
    | zero => simp only [spaces_mixedDerivative_zero, Nat.add_zero, pow_zero, one_mul]
    | succ b ih =>
      rw [← angularPartial_mixedDerivative hf 0 b,
        spaces_integral_angularPartial_mul (contDiff_mixedDerivative hf 0 b) (hjp 0 b) hφ,
        ih hφ.spaces_angularPartial]
      have he : mixedDerivative 0 b (angularPartial φ) = mixedDerivative 0 (b + 1) φ :=
        funext (fun p => mixedDerivative_angularPartial isOpen_univ hφ.1.contDiffOn 0 b (mem_univ p))
      rw [he]
      simp only [Nat.zero_add, pow_succ, mul_neg_one, neg_mul]
  | succ a ih =>
    rw [← radialPartial_mixedDerivative hf a b,
      spaces_integral_radialPartial_mul (contDiff_mixedDerivative hf a b) (hjp a b) hφ,
      ih hφ.spaces_radialPartial]
    have he : mixedDerivative a b (radialPartial φ) = mixedDerivative (a + 1) b φ :=
      funext (fun p => mixedDerivative_radialPartial isOpen_univ hφ.1.contDiffOn a b (mem_univ p))
    rw [he]
    simp only [Nat.add_right_comm a 1 b, pow_succ, mul_neg_one, neg_mul]

/-- The actual smooth derivative class satisfies the weak graph identity. -/
theorem spaces_hasWeakMixedDerivative_of_smooth {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (0, Real.pi))
    (a b : ℕ) (hfLp : MemLp f 2 materialCylinderMeasure)
    (hdLp : MemLp (mixedDerivative a b f) 2 materialCylinderMeasure) :
    HasWeakMixedDerivative (hfLp.toLp f) (hdLp.toLp (mixedDerivative a b f)) a b := by
  intro φ hφ
  have hfint : (∫ p, hfLp.toLp f p * mixedDerivative a b φ p ∂materialCylinderMeasure) =
      ∫ p, f p * mixedDerivative a b φ p ∂materialCylinderMeasure := by
    apply integral_congr_ae
    filter_upwards [hfLp.coeFn_toLp] with p hp
    rw [hp]
  have hdint : (∫ p, hdLp.toLp (mixedDerivative a b f) p * φ p ∂materialCylinderMeasure) =
      ∫ p, mixedDerivative a b f p * φ p ∂materialCylinderMeasure := by
    apply integral_congr_ae
    filter_upwards [hdLp.coeFn_toLp] with p hp
    rw [hp]
  rw [hfint, hdint]
  exact spaces_integral_mixedDerivative_mul hf hp hφ a b

end ContinuousFlexibility.Statements
