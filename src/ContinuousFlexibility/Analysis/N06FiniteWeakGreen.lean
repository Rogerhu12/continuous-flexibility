module

public import ContinuousFlexibility.Analysis.N06PhysicalWeakIntegration
public import ContinuousFlexibility.Analysis.N06WeakDivergencePairing
public import ContinuousFlexibility.Scalar.GreenIdentity

/-!
# Physical Green identity for finite C1/H2 Fourier fields

The two mixed divergence channels are kept separately. The radial
integration identities have their true endpoint pairings, while angular
periodicity removes only the seam. The finite-field constructor below
obtains all six identities from AC modal representatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def N06PhysicalRadialPairing (D : ReferenceData) (u ur : PolarPoint → ℝ) : Prop :=
  ∀ φ : PolarPoint → ℝ, ContDiff ℝ ∞ φ → Function.Periodic φ (0, 2 * Real.pi) →
    (∫ p, ur p * φ p ∂radialPhysicalMeasure D) +
      (∫ p, u p * radialPartial φ p ∂radialPhysicalMeasure D) = n06PhysicalBoundary D u φ

def N06PhysicalAngularPairing (D : ReferenceData) (u ut : PolarPoint → ℝ) : Prop :=
  ∀ φ : PolarPoint → ℝ, ContDiff ℝ ∞ φ → Function.Periodic φ (0, 2 * Real.pi) →
    (∫ p, ut p * φ p ∂radialPhysicalMeasure D) +
      (∫ p, u p * angularPartial φ p ∂radialPhysicalMeasure D) = 0

/-- These are genuine first-order identities, including true boundary
values. The concrete finite Fourier constructor supplies every field. -/
structure N06PhysicalWeakH2Row (D : ReferenceData)
    (U Ur Ut Urr Urt Utt : PolarPoint → ℝ) : Prop where
  value_memLp : MemLp U 2 (radialPhysicalMeasure D)
  radial_memLp : MemLp Ur 2 (radialPhysicalMeasure D)
  angular_memLp : MemLp Ut 2 (radialPhysicalMeasure D)
  radial_radial_memLp : MemLp Urr 2 (radialPhysicalMeasure D)
  radial_angular_memLp : MemLp Urt 2 (radialPhysicalMeasure D)
  angular_angular_memLp : MemLp Utt 2 (radialPhysicalMeasure D)
  value_continuous : Continuous U
  radial_continuous : Continuous Ur
  angular_continuous : Continuous Ut
  radial_value : radialPartial U = Ur
  angular_value : angularPartial U = Ut
  radial : N06PhysicalRadialPairing D U Ur
  angular : N06PhysicalAngularPairing D U Ut
  radial_radial : N06PhysicalRadialPairing D Ur Urr
  radial_angular : N06PhysicalAngularPairing D Ur Urt
  angular_radial : N06PhysicalRadialPairing D Ut Urt
  angular_angular : N06PhysicalAngularPairing D Ut Utt

private theorem physical_weighted_test_integrable {D : ReferenceData}
    {f a φ : PolarPoint → ℝ} (hf : MemLp f 2 (radialPhysicalMeasure D))
    (ha : Continuous a) (hφ : Continuous φ) :
    Integrable (fun p => (a p * f p) * φ p) (radialPhysicalMeasure D) := by
  apply (hf.integrable_mul (r11b_continuous_memLp (ha.mul hφ))).congr
  filter_upwards with p
  simp only [Pi.mul_apply]
  ring

private theorem physical_product_test_integrable {D : ReferenceData}
    {f g a da φ : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D))
    (hg : MemLp g 2 (radialPhysicalMeasure D))
    (ha : Continuous a) (hda : Continuous da) (hφ : Continuous φ) :
    Integrable (fun p => (a p * g p + da p * f p) * φ p) (radialPhysicalMeasure D) := by
  apply ((physical_weighted_test_integrable hg ha hφ).add
    (physical_weighted_test_integrable hf hda hφ)).congr
  filter_upwards with p
  simp only [Pi.add_apply]
  ring

private theorem physical_product_radial_green {D : ReferenceData}
    {f g a φ : PolarPoint → ℝ}
    (hfg : N06PhysicalRadialPairing D f g)
    (hf : MemLp f 2 (radialPhysicalMeasure D))
    (hg : MemLp g 2 (radialPhysicalMeasure D))
    (ha : ContDiff ℝ ∞ a) (hap : Function.Periodic a (0, 2 * Real.pi))
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, 2 * Real.pi)) :
    (∫ p, (a p * g p + radialPartial a p * f p) * φ p ∂radialPhysicalMeasure D) +
      (∫ p, (a p * f p) * radialPartial φ p ∂radialPhysicalMeasure D) =
      n06PhysicalBoundary D (fun p => a p * f p) φ := by
  have h := hfg (fun p => a p * φ p) (ha.mul hφ) (hap.mul hφp)
  have har : ContDiff ℝ ∞ (radialPartial a) := r11b_contDiff_directionalPartial ha (1, 0)
  have hφr : ContDiff ℝ ∞ (radialPartial φ) := r11b_contDiff_directionalPartial hφ (1, 0)
  have hA : Integrable (fun p => (a p * g p) * φ p) (radialPhysicalMeasure D) :=
    physical_weighted_test_integrable hg ha.continuous hφ.continuous
  have hB : Integrable (fun p => (radialPartial a p * f p) * φ p) (radialPhysicalMeasure D) :=
    physical_weighted_test_integrable hf har.continuous hφ.continuous
  have hC : Integrable (fun p => (a p * f p) * radialPartial φ p) (radialPhysicalMeasure D) :=
    physical_weighted_test_integrable hf ha.continuous hφr.continuous
  have hfirst : (∫ p, g p * (a p * φ p) ∂radialPhysicalMeasure D) =
      ∫ p, (a p * g p) * φ p ∂radialPhysicalMeasure D := by
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hsecond : (∫ p, f p * radialPartial (fun q => a q * φ q) p
      ∂radialPhysicalMeasure D) =
      (∫ p, (radialPartial a p * f p) * φ p ∂radialPhysicalMeasure D) +
        ∫ p, (a p * f p) * radialPartial φ p ∂radialPhysicalMeasure D := by
    rw [← integral_add hB hC]
    apply integral_congr_ae
    filter_upwards with p
    rw [radialPartial_mul (ha.differentiable (by simp) p) (hφ.differentiable (by simp) p)]
    ring
  have hboundary : n06PhysicalBoundary D f (fun p => a p * φ p) =
      n06PhysicalBoundary D (fun p => a p * f p) φ := by
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  have hsum : (∫ p, (a p * g p + radialPartial a p * f p) * φ p
      ∂radialPhysicalMeasure D) =
      (∫ p, (a p * g p) * φ p ∂radialPhysicalMeasure D) +
        ∫ p, (radialPartial a p * f p) * φ p ∂radialPhysicalMeasure D := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    filter_upwards with p
    ring
  rw [hfirst, hsecond, hboundary] at h
  rw [hsum]
  linarith only [h]

private theorem physical_product_angular_green {D : ReferenceData}
    {f g a φ : PolarPoint → ℝ}
    (hfg : N06PhysicalAngularPairing D f g)
    (hf : MemLp f 2 (radialPhysicalMeasure D))
    (hg : MemLp g 2 (radialPhysicalMeasure D))
    (ha : ContDiff ℝ ∞ a) (hap : Function.Periodic a (0, 2 * Real.pi))
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, 2 * Real.pi)) :
    (∫ p, (a p * g p + angularPartial a p * f p) * φ p ∂radialPhysicalMeasure D) +
      (∫ p, (a p * f p) * angularPartial φ p ∂radialPhysicalMeasure D) = 0 := by
  have h := hfg (fun p => a p * φ p) (ha.mul hφ) (hap.mul hφp)
  have hat : ContDiff ℝ ∞ (angularPartial a) := r11b_contDiff_directionalPartial ha (0, 1)
  have hφt : ContDiff ℝ ∞ (angularPartial φ) := r11b_contDiff_directionalPartial hφ (0, 1)
  have hA : Integrable (fun p => (a p * g p) * φ p) (radialPhysicalMeasure D) :=
    physical_weighted_test_integrable hg ha.continuous hφ.continuous
  have hB : Integrable (fun p => (angularPartial a p * f p) * φ p) (radialPhysicalMeasure D) :=
    physical_weighted_test_integrable hf hat.continuous hφ.continuous
  have hC : Integrable (fun p => (a p * f p) * angularPartial φ p) (radialPhysicalMeasure D) :=
    physical_weighted_test_integrable hf ha.continuous hφt.continuous
  have hfirst : (∫ p, g p * (a p * φ p) ∂radialPhysicalMeasure D) =
      ∫ p, (a p * g p) * φ p ∂radialPhysicalMeasure D := by
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hsecond : (∫ p, f p * angularPartial (fun q => a q * φ q) p
      ∂radialPhysicalMeasure D) =
      (∫ p, (angularPartial a p * f p) * φ p ∂radialPhysicalMeasure D) +
        ∫ p, (a p * f p) * angularPartial φ p ∂radialPhysicalMeasure D := by
    rw [← integral_add hB hC]
    apply integral_congr_ae
    filter_upwards with p
    rw [angularPartial_mul (ha.differentiable (by simp) p) (hφ.differentiable (by simp) p)]
    ring
  have hsum : (∫ p, (a p * g p + angularPartial a p * f p) * φ p
      ∂radialPhysicalMeasure D) =
      (∫ p, (a p * g p) * φ p ∂radialPhysicalMeasure D) +
        ∫ p, (angularPartial a p * f p) * φ p ∂radialPhysicalMeasure D := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    filter_upwards with p
    ring
  rw [hfirst, hsecond] at h
  rw [hsum]
  linarith only [h]

private theorem physical_integral_four {μ : Measure PolarPoint}
    {f g h j : PolarPoint → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) (hj : Integrable j μ) :
    (∫ p, f p + g p + h p + j p ∂μ) =
      (∫ p, f p ∂μ) + (∫ p, g p ∂μ) + (∫ p, h p ∂μ) + ∫ p, j p ∂μ := by
  have hfg : Integrable (fun p => f p + g p) μ := hf.add hg
  have hfgh : Integrable (fun p => f p + g p + h p) μ := hfg.add hh
  rw [integral_add hfgh hj, integral_add hfg hh, integral_add hf hg]

private theorem physical_boundary_integrable (D : ReferenceData)
    {u φ : PolarPoint → ℝ} (hu : Continuous u) (hφ : Continuous φ) :
    IntervalIntegrable
      (fun θ => u (D.b, θ) * φ (D.b, θ) - u (D.a, θ) * φ (D.a, θ))
      volume 0 (2 * Real.pi) :=
  (((hu.comp (continuous_const.prodMk continuous_id)).mul
      (hφ.comp (continuous_const.prodMk continuous_id))).sub
    ((hu.comp (continuous_const.prodMk continuous_id)).mul
      (hφ.comp (continuous_const.prodMk continuous_id)))).intervalIntegrable _ _

private theorem physical_green_boundary_four (D : ReferenceData)
    {U Ur Ut A B φ : PolarPoint → ℝ}
    (hU : Continuous U) (hUr : Continuous Ur) (hUt : Continuous Ut)
    (hA : Continuous A) (hB : Continuous B) (hφ : ContDiff ℝ ∞ φ)
    (hr : radialPartial U = Ur) (ht : angularPartial U = Ut) :
    n06PhysicalBoundary D (fun p => A p * Ur p) φ +
      n06PhysicalBoundary D (fun p => B p * Ut p) φ -
        n06PhysicalBoundary D U (fun p => A p * radialPartial φ p) -
        n06PhysicalBoundary D U (fun p => B p * angularPartial φ p) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        greenNormalFlux A B φ U (D.b, θ) - greenNormalFlux A B φ U (D.a, θ) := by
  have hI : IntervalIntegrable (fun θ =>
      (A (D.b, θ) * Ur (D.b, θ)) * φ (D.b, θ) -
        (A (D.a, θ) * Ur (D.a, θ)) * φ (D.a, θ)) volume 0 (2 * Real.pi) :=
    physical_boundary_integrable D (hA.mul hUr) hφ.continuous
  have hJ : IntervalIntegrable (fun θ =>
      (B (D.b, θ) * Ut (D.b, θ)) * φ (D.b, θ) -
        (B (D.a, θ) * Ut (D.a, θ)) * φ (D.a, θ)) volume 0 (2 * Real.pi) :=
    physical_boundary_integrable D (hB.mul hUt) hφ.continuous
  have hK : IntervalIntegrable (fun θ =>
      U (D.b, θ) * (A (D.b, θ) * radialPartial φ (D.b, θ)) -
        U (D.a, θ) * (A (D.a, θ) * radialPartial φ (D.a, θ))) volume 0 (2 * Real.pi) :=
    physical_boundary_integrable D hU
      (hA.mul (r11b_contDiff_directionalPartial hφ (1, 0)).continuous)
  have hM : IntervalIntegrable (fun θ =>
      U (D.b, θ) * (B (D.b, θ) * angularPartial φ (D.b, θ)) -
        U (D.a, θ) * (B (D.a, θ) * angularPartial φ (D.a, θ))) volume 0 (2 * Real.pi) :=
    physical_boundary_integrable D hU
      (hB.mul (r11b_contDiff_directionalPartial hφ (0, 1)).continuous)
  have hadd := intervalIntegral.integral_add hI hJ
  have hsub₁ := intervalIntegral.integral_sub (hI.add hJ) hK
  have hsub₂ := intervalIntegral.integral_sub ((hI.add hJ).sub hK) hM
  unfold n06PhysicalBoundary
  rw [← hadd, ← hsub₁, ← hsub₂]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [greenNormalFlux, symmetricNormalFlux, hr, ht]
  ring

/-- Green's formula for a genuine physical weak H2 row. The boundary
uses the actual polar conormal, including the mixed coefficient. -/
theorem n06_physical_weak_divergence_green {D : ReferenceData}
    {U Ur Ut Urr Urt Utt φ : PolarPoint → ℝ}
    (hrow : N06PhysicalWeakH2Row D U Ur Ut Urr Urt Utt)
    (L : SymmetricCoefficients)
    (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b) (hc : ContDiff ℝ ∞ L.c)
    (hpa : Function.Periodic L.a (0, 2 * Real.pi))
    (hpb : Function.Periodic L.b (0, 2 * Real.pi))
    (hpc : Function.Periodic L.c (0, 2 * Real.pi))
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, 2 * Real.pi)) :
    (∫ p, n06WeakDivergenceExpression L Ur Ut Urr Urt Utt p * φ p
      ∂radialPhysicalMeasure D) -
      (∫ p, U p * divergenceOperator L φ p ∂radialPhysicalMeasure D) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        greenNormalFlux L.a L.b φ U (D.b, θ) -
          greenNormalFlux L.a L.b φ U (D.a, θ) := by
  let F₁ := radialPartial (fun p => L.a p * radialPartial φ p)
  let F₂ := radialPartial (fun p => L.b p * angularPartial φ p)
  let F₃ := angularPartial (fun p => L.b p * radialPartial φ p)
  let F₄ := angularPartial (fun p => L.c p * angularPartial φ p)
  let Q₁ : PolarPoint → ℝ := fun p => L.a p * Urr p + radialPartial L.a p * Ur p
  let Q₂ : PolarPoint → ℝ := fun p => L.b p * Urt p + angularPartial L.b p * Ur p
  let Q₃ : PolarPoint → ℝ := fun p => L.b p * Urt p + radialPartial L.b p * Ut p
  let Q₄ : PolarPoint → ℝ := fun p => L.c p * Utt p + angularPartial L.c p * Ut p
  have hφr : ContDiff ℝ ∞ (radialPartial φ) := r11b_contDiff_directionalPartial hφ (1, 0)
  have hφt : ContDiff ℝ ∞ (angularPartial φ) := r11b_contDiff_directionalPartial hφ (0, 1)
  have hT₁ : ContDiff ℝ ∞ (fun p => L.a p * radialPartial φ p) := ha.mul hφr
  have hT₂ : ContDiff ℝ ∞ (fun p => L.b p * angularPartial φ p) := hb.mul hφt
  have hT₃ : ContDiff ℝ ∞ (fun p => L.b p * radialPartial φ p) := hb.mul hφr
  have hT₄ : ContDiff ℝ ∞ (fun p => L.c p * angularPartial φ p) := hc.mul hφt
  have hP₁ := hpa.mul (periodic_radialPartial hφp)
  have hP₂ := hpb.mul (periodic_angularPartial hφp)
  have hP₃ := hpb.mul (periodic_radialPartial hφp)
  have hP₄ := hpc.mul (periodic_angularPartial hφp)
  have hF₁ : Integrable (fun p => U p * F₁ p) (radialPhysicalMeasure D) :=
    hrow.value_memLp.integrable_mul (r11b_continuous_memLp
      (r11b_contDiff_directionalPartial hT₁ (1, 0)).continuous)
  have hF₂ : Integrable (fun p => U p * F₂ p) (radialPhysicalMeasure D) :=
    hrow.value_memLp.integrable_mul (r11b_continuous_memLp
      (r11b_contDiff_directionalPartial hT₂ (1, 0)).continuous)
  have hF₃ : Integrable (fun p => U p * F₃ p) (radialPhysicalMeasure D) :=
    hrow.value_memLp.integrable_mul (r11b_continuous_memLp
      (r11b_contDiff_directionalPartial hT₃ (0, 1)).continuous)
  have hF₄ : Integrable (fun p => U p * F₄ p) (radialPhysicalMeasure D) :=
    hrow.value_memLp.integrable_mul (r11b_continuous_memLp
      (r11b_contDiff_directionalPartial hT₄ (0, 1)).continuous)
  have hQ₁ : Integrable (fun p => Q₁ p * φ p) (radialPhysicalMeasure D) :=
    physical_product_test_integrable hrow.radial_memLp hrow.radial_radial_memLp
      ha.continuous (r11b_contDiff_directionalPartial ha (1, 0)).continuous hφ.continuous
  have hQ₂ : Integrable (fun p => Q₂ p * φ p) (radialPhysicalMeasure D) :=
    physical_product_test_integrable hrow.radial_memLp hrow.radial_angular_memLp
      hb.continuous (r11b_contDiff_directionalPartial hb (0, 1)).continuous hφ.continuous
  have hQ₃ : Integrable (fun p => Q₃ p * φ p) (radialPhysicalMeasure D) :=
    physical_product_test_integrable hrow.angular_memLp hrow.radial_angular_memLp
      hb.continuous (r11b_contDiff_directionalPartial hb (1, 0)).continuous hφ.continuous
  have hQ₄ : Integrable (fun p => Q₄ p * φ p) (radialPhysicalMeasure D) :=
    physical_product_test_integrable hrow.angular_memLp hrow.angular_angular_memLp
      hc.continuous (r11b_contDiff_directionalPartial hc (0, 1)).continuous hφ.continuous
  have hswap (f a ψ : PolarPoint → ℝ) :
      (∫ p, f p * (a p * ψ p) ∂radialPhysicalMeasure D) =
        ∫ p, (a p * f p) * ψ p ∂radialPhysicalMeasure D := by
    apply integral_congr_ae
    filter_upwards with p
    ring
  have h₁ : (∫ p, U p * F₁ p ∂radialPhysicalMeasure D) =
      (∫ p, Q₁ p * φ p ∂radialPhysicalMeasure D) +
        n06PhysicalBoundary D U (fun p => L.a p * radialPartial φ p) -
        n06PhysicalBoundary D (fun p => L.a p * Ur p) φ := by
    have hfirst := hrow.radial _ hT₁ hP₁
    rw [hswap Ur L.a (radialPartial φ)] at hfirst
    have hsecond := physical_product_radial_green hrow.radial_radial
      hrow.radial_memLp hrow.radial_radial_memLp ha hpa hφ hφp
    change (∫ p, Q₁ p * φ p ∂radialPhysicalMeasure D) + _ = _ at hsecond
    change (∫ p, (L.a p * Ur p) * radialPartial φ p ∂radialPhysicalMeasure D) +
      (∫ p, U p * F₁ p ∂radialPhysicalMeasure D) = _ at hfirst
    linarith only [hfirst, hsecond]
  have h₂ : (∫ p, U p * F₂ p ∂radialPhysicalMeasure D) =
      (∫ p, Q₂ p * φ p ∂radialPhysicalMeasure D) +
        n06PhysicalBoundary D U (fun p => L.b p * angularPartial φ p) := by
    have hfirst := hrow.radial _ hT₂ hP₂
    rw [hswap Ur L.b (angularPartial φ)] at hfirst
    have hsecond := physical_product_angular_green hrow.radial_angular
      hrow.radial_memLp hrow.radial_angular_memLp hb hpb hφ hφp
    change (∫ p, Q₂ p * φ p ∂radialPhysicalMeasure D) + _ = 0 at hsecond
    change (∫ p, (L.b p * Ur p) * angularPartial φ p ∂radialPhysicalMeasure D) +
      (∫ p, U p * F₂ p ∂radialPhysicalMeasure D) = _ at hfirst
    linarith only [hfirst, hsecond]
  have h₃ : (∫ p, U p * F₃ p ∂radialPhysicalMeasure D) =
      (∫ p, Q₃ p * φ p ∂radialPhysicalMeasure D) -
        n06PhysicalBoundary D (fun p => L.b p * Ut p) φ := by
    have hfirst := hrow.angular _ hT₃ hP₃
    rw [hswap Ut L.b (radialPartial φ)] at hfirst
    have hsecond := physical_product_radial_green hrow.angular_radial
      hrow.angular_memLp hrow.radial_angular_memLp hb hpb hφ hφp
    change (∫ p, Q₃ p * φ p ∂radialPhysicalMeasure D) + _ = _ at hsecond
    change (∫ p, (L.b p * Ut p) * radialPartial φ p ∂radialPhysicalMeasure D) +
      (∫ p, U p * F₃ p ∂radialPhysicalMeasure D) = 0 at hfirst
    linarith only [hfirst, hsecond]
  have h₄ : (∫ p, U p * F₄ p ∂radialPhysicalMeasure D) =
      ∫ p, Q₄ p * φ p ∂radialPhysicalMeasure D := by
    have hfirst := hrow.angular _ hT₄ hP₄
    rw [hswap Ut L.c (angularPartial φ)] at hfirst
    have hsecond := physical_product_angular_green hrow.angular_angular
      hrow.angular_memLp hrow.angular_angular_memLp hc hpc hφ hφp
    change (∫ p, Q₄ p * φ p ∂radialPhysicalMeasure D) + _ = 0 at hsecond
    change (∫ p, (L.c p * Ut p) * angularPartial φ p ∂radialPhysicalMeasure D) +
      (∫ p, U p * F₄ p ∂radialPhysicalMeasure D) = 0 at hfirst
    linarith only [hfirst, hsecond]
  have hoperator : divergenceOperator L φ = fun p => F₁ p + F₂ p + F₃ p + F₄ p := by
    funext p
    change radialPartial (fun q => L.a q * radialPartial φ q + L.b q * angularPartial φ q) p +
      angularPartial (fun q => L.b q * radialPartial φ q + L.c q * angularPartial φ q) p = _
    rw [radialPartial_add (hT₁.differentiable (by simp) p)
      (hT₂.differentiable (by simp) p),
      angularPartial_add (hT₃.differentiable (by simp) p) (hT₄.differentiable (by simp) p)]
    dsimp only [F₁, F₂, F₃, F₄]
    ring
  have hleft : (∫ p, U p * divergenceOperator L φ p ∂radialPhysicalMeasure D) =
      (∫ p, U p * F₁ p ∂radialPhysicalMeasure D) +
      (∫ p, U p * F₂ p ∂radialPhysicalMeasure D) +
      (∫ p, U p * F₃ p ∂radialPhysicalMeasure D) +
      ∫ p, U p * F₄ p ∂radialPhysicalMeasure D := by
    rw [← physical_integral_four hF₁ hF₂ hF₃ hF₄]
    apply integral_congr_ae
    filter_upwards with p
    rw [hoperator]
    ring
  have hright : (∫ p, n06WeakDivergenceExpression L Ur Ut Urr Urt Utt p * φ p
      ∂radialPhysicalMeasure D) =
      (∫ p, Q₁ p * φ p ∂radialPhysicalMeasure D) +
      (∫ p, Q₂ p * φ p ∂radialPhysicalMeasure D) +
      (∫ p, Q₃ p * φ p ∂radialPhysicalMeasure D) +
      ∫ p, Q₄ p * φ p ∂radialPhysicalMeasure D := by
    rw [← physical_integral_four hQ₁ hQ₂ hQ₃ hQ₄]
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [n06WeakDivergenceExpression, Q₁, Q₂, Q₃, Q₄]
    ring
  rw [hleft, hright,
    ← physical_green_boundary_four D hrow.value_continuous hrow.radial_continuous
      hrow.angular_continuous ha.continuous hb.continuous hφ hrow.radial_value hrow.angular_value]
  linarith only [h₁, h₂, h₃, h₄]

private theorem finiteSynthesis_contDiff_one {ι : Type*}
    (s : Finset ι) (v e : ι → ℝ → ℝ)
    (hv : ∀ i ∈ s, ContDiff ℝ 1 (v i)) (he : ∀ i ∈ s, ContDiff ℝ 1 (e i)) :
    ContDiff ℝ 1 (r11bFiniteSynthesis s v e) := by
  apply ContDiff.sum
  intro i hi
  exact ((hv i hi).comp contDiff_fst).mul ((he i hi).comp contDiff_snd)

private theorem finiteSynthesis_first_partials {ι : Type*}
    (s : Finset ι) (v e : ι → ℝ → ℝ)
    (hv : ∀ i ∈ s, ContDiff ℝ 1 (v i)) (he : ∀ i ∈ s, ContDiff ℝ 1 (e i)) :
    radialPartial (r11bFiniteSynthesis s v e) =
        r11bFiniteSynthesis s (fun i => deriv (v i)) e ∧
      angularPartial (r11bFiniteSynthesis s v e) =
        r11bFiniteSynthesis s v (fun i => deriv (e i)) := by
  have hU := (finiteSynthesis_contDiff_one s v e hv he).differentiable (by norm_num)
  constructor
  · funext p
    have hd : HasDerivAt (fun r => r11bFiniteSynthesis s v e (r, p.2))
        (r11bFiniteSynthesis s (fun i => deriv (v i)) e p) p.1 :=
      HasDerivAt.fun_sum (fun i hi =>
        ((hv i hi).differentiable (by norm_num) p.1).hasDerivAt.mul_const (e i p.2))
    exact (deriv_cylinder_radial_slice hU p.1 p.2).symm.trans hd.deriv
  · funext p
    have hd : HasDerivAt (fun θ => r11bFiniteSynthesis s v e (p.1, θ))
        (r11bFiniteSynthesis s v (fun i => deriv (e i)) p) p.2 :=
      HasDerivAt.fun_sum (fun i hi =>
        ((he i hi).differentiable (by norm_num) p.2).hasDerivAt.const_mul (v i p.1))
    exact (deriv_cylinder_angular_slice hU p.1 p.2).symm.trans hd.deriv

private theorem finiteMixed_memLp {D : ReferenceData}
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (a b : ℕ)
    (hv : ∀ i ∈ s, MemLp (iteratedDeriv a (v i)) 2 (volume.restrict (radialCore D))) :
    MemLp (n06FiniteMixedField s v a b) 2 (radialPhysicalMeasure D) :=
  r11b_finiteSynthesis_memLp s _ _ hv (fun i _ =>
    memLp_referenceAngular_interval_of_continuous
      (circleFourier_contDiff_iteratedDeriv (contDiff_referenceAngularBasis i) b).continuous)

private theorem finiteMixed_continuous (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (a b : ℕ)
    (hv : ∀ i ∈ s, Continuous (iteratedDeriv a (v i))) :
    Continuous (n06FiniteMixedField s v a b) :=
  continuous_finsetSum s (fun i hi => ((hv i hi).comp continuous_fst).mul
    ((circleFourier_contDiff_iteratedDeriv
      (contDiff_referenceAngularBasis i) b).continuous.comp continuous_snd))

private theorem finiteMixed_radial_pairing {D : ReferenceData} (hab : D.a ≤ D.b)
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (a b : ℕ)
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (iteratedDeriv a (v i)) D.a D.b)
    (hv : ∀ i ∈ s, MemLp (iteratedDeriv a (v i)) 2 (volume.restrict (radialCore D)))
    (hvd : ∀ i ∈ s,
      MemLp (iteratedDeriv (a + 1) (v i)) 2 (volume.restrict (radialCore D))) :
    N06PhysicalRadialPairing D (n06FiniteMixedField s v a b)
      (n06FiniteMixedField s v (a + 1) b) := by
  intro φ hφ _
  simpa only [n06FiniteMixedField, iteratedDeriv_succ] using
    n06_finiteSynthesis_physical_radial_green hab s (fun i => iteratedDeriv a (v i))
      (fun i => iteratedDeriv b (referenceAngularBasis i)) hAC hv
      (fun i hi => by simpa only [iteratedDeriv_succ] using hvd i hi)
      (fun i _ => (circleFourier_contDiff_iteratedDeriv
        (contDiff_referenceAngularBasis i) b).continuous) hφ

private theorem finiteMixed_angular_pairing {D : ReferenceData}
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (a b : ℕ)
    (hv : ∀ i ∈ s, MemLp (iteratedDeriv a (v i)) 2 (volume.restrict (radialCore D))) :
    N06PhysicalAngularPairing D (n06FiniteMixedField s v a b)
      (n06FiniteMixedField s v a (b + 1)) := by
  intro φ hφ hp
  simpa only [n06FiniteMixedField, iteratedDeriv_succ] using
    n06_finiteSynthesis_physical_angular_green s (fun i => iteratedDeriv a (v i))
      (fun i => iteratedDeriv b (referenceAngularBasis i)) hv
      (fun i _ => circleFourier_contDiff_iteratedDeriv (contDiff_referenceAngularBasis i) b)
      (fun i _ => by
        have hpπ := circleFourier_periodic_iteratedDeriv (referenceAngularBasis_periodic i) b
        intro θ
        rw [show θ + 2 * Real.pi = (θ + Real.pi) + Real.pi by ring, hpπ, hpπ])
      hφ hp

/-- All six identities, including the true radial traces, follow from
the same actual finite C1/H2 modal representatives. -/
theorem n06_finiteMixedField_physical_weakH2 {D : ReferenceData} (hab : D.a ≤ D.b)
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (hC : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (deriv (v i)) D.a D.b)
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (radialCore D)))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (radialCore D)))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2 (volume.restrict (radialCore D))) :
    N06PhysicalWeakH2Row D (n06FiniteMixedField s v 0 0)
      (n06FiniteMixedField s v 1 0) (n06FiniteMixedField s v 0 1)
      (n06FiniteMixedField s v 2 0) (n06FiniteMixedField s v 1 1)
      (n06FiniteMixedField s v 0 2) := by
  have h₀ : ∀ i ∈ s, MemLp (iteratedDeriv 0 (v i)) 2 (volume.restrict (radialCore D)) := by
    simpa only [iteratedDeriv_zero] using hv
  have h₁ : ∀ i ∈ s, MemLp (iteratedDeriv 1 (v i)) 2 (volume.restrict (radialCore D)) := by
    simpa only [iteratedDeriv_one] using hv₁
  have h₂ : ∀ i ∈ s, MemLp (iteratedDeriv 2 (v i)) 2 (volume.restrict (radialCore D)) := by
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one, iteratedDeriv_zero] using hv₂
  have hAC₀ : ∀ i ∈ s,
      AbsolutelyContinuousOnInterval (iteratedDeriv 0 (v i)) D.a D.b :=
    fun i hi => (hC i hi).contDiffOn.absolutelyContinuousOnInterval
  have hAC₁ : ∀ i ∈ s,
      AbsolutelyContinuousOnInterval (iteratedDeriv 1 (v i)) D.a D.b := by
    simpa only [iteratedDeriv_one] using hAC
  have hc₀ : ∀ i ∈ s, Continuous (iteratedDeriv 0 (v i)) := fun i hi => (hC i hi).continuous
  have hc₁ : ∀ i ∈ s, Continuous (iteratedDeriv 1 (v i)) := by
    intro i hi
    simpa only [iteratedDeriv_one] using (hC i hi).continuous_deriv le_rfl
  have hpartials := finiteSynthesis_first_partials s v referenceAngularBasis hC
    (fun i _ => (contDiff_referenceAngularBasis i).of_le (by simp))
  refine ⟨finiteMixed_memLp s v 0 0 h₀, finiteMixed_memLp s v 1 0 h₁,
    finiteMixed_memLp s v 0 1 h₀, finiteMixed_memLp s v 2 0 h₂,
    finiteMixed_memLp s v 1 1 h₁, finiteMixed_memLp s v 0 2 h₀,
    finiteMixed_continuous s v 0 0 hc₀, finiteMixed_continuous s v 1 0 hc₁,
    finiteMixed_continuous s v 0 1 hc₀, ?_, ?_,
    finiteMixed_radial_pairing hab s v 0 0 hAC₀ h₀ h₁,
    finiteMixed_angular_pairing s v 0 0 h₀,
    finiteMixed_radial_pairing hab s v 1 0 hAC₁ h₁ h₂,
    finiteMixed_angular_pairing s v 1 0 h₁,
    finiteMixed_radial_pairing hab s v 0 1 hAC₀ h₀ h₁,
    finiteMixed_angular_pairing s v 0 1 h₀⟩
  · simpa only [n06FiniteMixedField, iteratedDeriv_zero, iteratedDeriv_one] using hpartials.1
  · simpa only [n06FiniteMixedField, iteratedDeriv_zero, iteratedDeriv_one] using hpartials.2

/-- The single-piece physical Green bridge for finite weak modes. The
test need not vanish at either endpoint, and the source is the exact
six-field divergence expression, with both mixed terms present. -/
theorem n06_finite_weak_physical_green {D : ReferenceData} (hab : D.a ≤ D.b)
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (hC : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (deriv (v i)) D.a D.b)
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (radialCore D)))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (radialCore D)))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2 (volume.restrict (radialCore D)))
    (L : SymmetricCoefficients)
    (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b) (hc : ContDiff ℝ ∞ L.c)
    (hpa : Function.Periodic L.a (0, 2 * Real.pi))
    (hpb : Function.Periodic L.b (0, 2 * Real.pi))
    (hpc : Function.Periodic L.c (0, 2 * Real.pi))
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφp : Function.Periodic φ (0, 2 * Real.pi)) :
    (∫ p, n06WeakDivergenceExpression L
      (n06FiniteMixedField s v 1 0) (n06FiniteMixedField s v 0 1)
      (n06FiniteMixedField s v 2 0) (n06FiniteMixedField s v 1 1)
      (n06FiniteMixedField s v 0 2) p * φ p ∂radialPhysicalMeasure D) -
      (∫ p, r11bFiniteSynthesis s v referenceAngularBasis p * divergenceOperator L φ p
        ∂radialPhysicalMeasure D) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        greenNormalFlux L.a L.b φ (r11bFiniteSynthesis s v referenceAngularBasis) (D.b, θ) -
          greenNormalFlux L.a L.b φ (r11bFiniteSynthesis s v referenceAngularBasis) (D.a, θ) := by
  simpa only [n06FiniteMixedField, iteratedDeriv_zero] using
    n06_physical_weak_divergence_green
      (n06_finiteMixedField_physical_weakH2 hab s v hC hAC hv hv₁ hv₂)
      L ha hb hc hpa hpb hpc hφ hφp

end ContinuousFlexibility.Analysis
