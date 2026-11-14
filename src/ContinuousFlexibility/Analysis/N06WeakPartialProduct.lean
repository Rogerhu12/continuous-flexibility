module

public import ContinuousFlexibility.Analysis.N06WeakTensorCalculus

/-!
# Weak partial products against the original unit-cylinder tests

Only the coefficient on the open strip is differentiated. Products with
the compact radial test are globally smooth and square integrable, so
these distributional product identities need no endpoint extension or
global bound on the coefficient itself.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def N06UnitWeakRadialDerivative (f g : PolarPoint → ℝ) : Prop :=
  ∀ φ, n06UnitCanonicalTest φ →
    (∫ p, g p * φ p ∂cylinderWindowMeasure 0) =
      -(∫ p, f p * radialPartial φ p ∂cylinderWindowMeasure 0)

def N06UnitWeakAngularDerivative (f g : PolarPoint → ℝ) : Prop :=
  ∀ φ, n06UnitCanonicalTest φ →
    (∫ p, g p * φ p ∂cylinderWindowMeasure 0) =
      -(∫ p, f p * angularPartial φ p ∂cylinderWindowMeasure 0)

theorem n06_unitOpen_ae :
    ∀ᵐ p ∂cylinderWindowMeasure 0, p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
  rw [← n06_unitCanonicalMeasure_eq_window]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  exact ⟨hp.1, mem_univ _⟩

theorem n06_unit_integrable_mul_local_test {f a φ : PolarPoint → ℝ}
    (hf : MemLp f 2 (cylinderWindowMeasure 0)) (hφ : n06UnitCanonicalTest φ)
    (ha : ContDiffOn ℝ ∞ a (Ioo (0 : ℝ) 1 ×ˢ univ)) :
    Integrable (fun p => f p * (a p * φ p)) (cylinderWindowMeasure 0) :=
  hf.integrable_mul (continuous_memLp_cylinderWindow
    (hφ.n06_contDiff_mul_left ha).continuous 0)

private theorem n06_weak_product_integral
    {μ : Measure PolarPoint} {f g a da φ dφ dtest : PolarPoint → ℝ}
    (htest : (∫ p, g p * (a p * φ p) ∂μ) = -(∫ p, f p * dtest p ∂μ))
    (hder : dtest =ᵐ[μ] (fun p => da p * φ p + a p * dφ p))
    (hI₁ : Integrable (fun p => g p * (a p * φ p)) μ)
    (hI₂ : Integrable (fun p => f p * (da p * φ p)) μ)
    (hI₃ : Integrable (fun p => f p * (a p * dφ p)) μ) :
    (∫ p, (a p * g p + da p * f p) * φ p ∂μ) =
      -(∫ p, (a p * f p) * dφ p ∂μ) := by
  have hout : (∫ p, (a p * g p + da p * f p) * φ p ∂μ) =
      (∫ p, g p * (a p * φ p) ∂μ) + ∫ p, f p * (da p * φ p) ∂μ := by
    calc
      _ = ∫ p, g p * (a p * φ p) + f p * (da p * φ p) ∂μ := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = _ := integral_add hI₁ hI₂
  have hin : (∫ p, f p * dtest p ∂μ) =
      (∫ p, f p * (da p * φ p) ∂μ) + ∫ p, f p * (a p * dφ p) ∂μ := by
    calc
      _ = ∫ p, f p * (da p * φ p) + f p * (a p * dφ p) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hder] with p hp
        rw [hp]
        ring
      _ = _ := integral_add hI₂ hI₃
  have hright : (∫ p, (a p * f p) * dφ p ∂μ) =
      ∫ p, f p * (a p * dφ p) ∂μ := by
    apply integral_congr_ae
    filter_upwards with p
    ring
  rw [hout, hright]
  linarith only [htest, hin]

/-- The radial product rule is a true distributional identity on all
original tests, with a coefficient smooth only in the open strip. -/
theorem n06_unit_weak_radial_product_pairing
    {f g a φ : PolarPoint → ℝ}
    (hfg : N06UnitWeakRadialDerivative f g)
    (hf : MemLp f 2 (cylinderWindowMeasure 0))
    (hg : MemLp g 2 (cylinderWindowMeasure 0))
    (ha : ContDiffOn ℝ ∞ a (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hp : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), a (p + (0, Real.pi)) = a p)
    (hφ : n06UnitCanonicalTest φ) :
    (∫ p, (a p * g p + radialPartial a p * f p) * φ p ∂cylinderWindowMeasure 0) =
      -(∫ p, (a p * f p) * radialPartial φ p ∂cylinderWindowMeasure 0) := by
  have har : ContDiffOn ℝ ∞ (radialPartial a) (Ioo (0 : ℝ) 1 ×ˢ univ) :=
    scalar_contDiffOn_radialPartial (isOpen_Ioo.prod isOpen_univ) ha
  have hder : radialPartial (fun p => a p * φ p) =ᵐ[cylinderWindowMeasure 0]
      (fun p => radialPartial a p * φ p + a p * radialPartial φ p) := by
    filter_upwards [n06_unitOpen_ae] with p hpU
    exact radialPartial_mul
      ((ha.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpU)).differentiableAt (by simp))
      (hφ.1.differentiable (by simp) p)
  exact n06_weak_product_integral
    (hfg _ (hφ.n06_mul_left_of_contDiffOn ha hp)) hder
    (n06_unit_integrable_mul_local_test hg hφ ha)
    (n06_unit_integrable_mul_local_test hf hφ har)
    (n06_unit_integrable_mul_local_test hf hφ.n06_radialPartial ha)

theorem n06_unit_weak_angular_product_pairing
    {f g a φ : PolarPoint → ℝ}
    (hfg : N06UnitWeakAngularDerivative f g)
    (hf : MemLp f 2 (cylinderWindowMeasure 0))
    (hg : MemLp g 2 (cylinderWindowMeasure 0))
    (ha : ContDiffOn ℝ ∞ a (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hp : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), a (p + (0, Real.pi)) = a p)
    (hφ : n06UnitCanonicalTest φ) :
    (∫ p, (a p * g p + angularPartial a p * f p) * φ p ∂cylinderWindowMeasure 0) =
      -(∫ p, (a p * f p) * angularPartial φ p ∂cylinderWindowMeasure 0) := by
  have hat : ContDiffOn ℝ ∞ (angularPartial a) (Ioo (0 : ℝ) 1 ×ˢ univ) :=
    scalar_contDiffOn_angularPartial (isOpen_Ioo.prod isOpen_univ) ha
  have hder : angularPartial (fun p => a p * φ p) =ᵐ[cylinderWindowMeasure 0]
      (fun p => angularPartial a p * φ p + a p * angularPartial φ p) := by
    filter_upwards [n06_unitOpen_ae] with p hpU
    exact angularPartial_mul
      ((ha.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpU)).differentiableAt (by simp))
      (hφ.1.differentiable (by simp) p)
  exact n06_weak_product_integral
    (hfg _ (hφ.n06_mul_left_of_contDiffOn ha hp)) hder
    (n06_unit_integrable_mul_local_test hg hφ ha)
    (n06_unit_integrable_mul_local_test hf hφ hat)
    (n06_unit_integrable_mul_local_test hf hφ.n06_angularPartial ha)

end ContinuousFlexibility.Analysis
