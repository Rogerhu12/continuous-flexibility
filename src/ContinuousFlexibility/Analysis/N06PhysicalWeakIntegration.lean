import ContinuousFlexibility.Analysis.N06WeakTensorCalculus
import ContinuousFlexibility.Radial.R11bFiniteSynthesis
import ContinuousFlexibility.Radial.R11bPhysicalPairing

/-!
# Physical first-order integration by parts with true boundary values

The radial interval and the full angular period are the original physical
ones. Tests may be nonzero at both radial endpoints. Absolute continuity
of each radial coefficient is sufficient; no smooth radial approximation
or prescribed trace is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The unnormalized physical endpoint pairing. -/
def n06PhysicalBoundary (D : ReferenceData) (u φ : PolarPoint → ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    u (D.b, θ) * φ (D.b, θ) - u (D.a, θ) * φ (D.a, θ)

theorem n06_physical_tensor_memLp {D : ReferenceData} {v e : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (radialCore D))) (he : Continuous e) :
    MemLp (fun p : PolarPoint => v p.1 * e p.2) 2 (radialPhysicalMeasure D) := by
  rw [r11b_radialPhysicalMeasure_eq_prod]
  exact r11b_memLp_tensor hv (memLp_referenceAngular_interval_of_continuous he)

/-- Radial AC integration by parts keeps both true endpoint values. -/
theorem n06_tensor_physical_radial_green {D : ReferenceData} (hab : D.a ≤ D.b)
    {v e : ℝ → ℝ} (hAC : AbsolutelyContinuousOnInterval v D.a D.b)
    (hv : MemLp v 2 (volume.restrict (radialCore D)))
    (hvd : MemLp (deriv v) 2 (volume.restrict (radialCore D)))
    (he : Continuous e) {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    (∫ p, (deriv v p.1 * e p.2) * φ p ∂radialPhysicalMeasure D) +
      (∫ p, (v p.1 * e p.2) * radialPartial φ p ∂radialPhysicalMeasure D) =
      n06PhysicalBoundary D (fun p => v p.1 * e p.2) φ := by
  have hφr : ContDiff ℝ ∞ (radialPartial φ) :=
    r11b_contDiff_directionalPartial hφ (1, 0)
  have hI : Integrable (fun p : PolarPoint => (deriv v p.1 * e p.2) * φ p)
      (radialPhysicalMeasure D) := (n06_physical_tensor_memLp hvd he).integrable_mul
    (r11b_continuous_memLp hφ.continuous)
  have hJ : Integrable (fun p : PolarPoint => (v p.1 * e p.2) * radialPartial φ p)
      (radialPhysicalMeasure D) := (n06_physical_tensor_memLp hv he).integrable_mul
    (r11b_continuous_memLp hφr.continuous)
  rw [← integral_add hI hJ]
  have hIJ : Integrable (fun p : PolarPoint =>
      (deriv v p.1 * e p.2) * φ p + (v p.1 * e p.2) * radialPartial φ p)
      (radialPhysicalMeasure D) := hI.add hJ
  rw [r11b_radialPhysicalMeasure_eq_prod] at hIJ ⊢
  rw [integral_prod_symm _ hIJ]
  unfold n06PhysicalBoundary
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  apply integral_congr_ae
  filter_upwards with θ
  have hψ : ContDiff ℝ 1 (fun r : ℝ => φ (r, θ)) :=
    (hφ.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  have hderiv : deriv (fun r : ℝ => φ (r, θ)) =
      fun r => radialPartial φ (r, θ) :=
    funext (fun r => deriv_cylinder_radial_slice (hφ.differentiable (by simp)) r θ)
  have hibp := hAC.integral_deriv_mul_eq_sub
    hψ.contDiffOn.absolutelyContinuousOnInterval
  rw [hderiv] at hibp
  change (∫ r in radialCore D,
      (deriv v r * e θ) * φ (r, θ) + (v r * e θ) * radialPartial φ (r, θ)) = _
  rw [show radialCore D = Ioo D.a D.b from rfl, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab]
  calc
    _ = e θ * (∫ r in D.a..D.b,
        deriv v r * φ (r, θ) + v r * radialPartial φ (r, θ)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      ring
    _ = _ := by rw [hibp]; ring

/-- Angular periodicity removes the seam, independently of radial regularity. -/
theorem n06_tensor_physical_angular_green {D : ReferenceData}
    {v e : ℝ → ℝ} (hv : MemLp v 2 (volume.restrict (radialCore D)))
    (he : ContDiff ℝ ∞ e) (hep : Function.Periodic e (2 * Real.pi))
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφp : Function.Periodic φ (0, 2 * Real.pi)) :
    (∫ p, (v p.1 * deriv e p.2) * φ p ∂radialPhysicalMeasure D) +
      (∫ p, (v p.1 * e p.2) * angularPartial φ p ∂radialPhysicalMeasure D) = 0 := by
  have hφt : ContDiff ℝ ∞ (angularPartial φ) :=
    r11b_contDiff_directionalPartial hφ (0, 1)
  have hI : Integrable (fun p : PolarPoint => (v p.1 * deriv e p.2) * φ p)
      (radialPhysicalMeasure D) :=
    (n06_physical_tensor_memLp hv (he.continuous_deriv (by simp))).integrable_mul
    (r11b_continuous_memLp hφ.continuous)
  have hJ : Integrable (fun p : PolarPoint => (v p.1 * e p.2) * angularPartial φ p)
      (radialPhysicalMeasure D) := (n06_physical_tensor_memLp hv he.continuous).integrable_mul
    (r11b_continuous_memLp hφt.continuous)
  rw [← integral_add hI hJ]
  have hIJ : Integrable (fun p : PolarPoint =>
      (v p.1 * deriv e p.2) * φ p + (v p.1 * e p.2) * angularPartial φ p)
      (radialPhysicalMeasure D) := hI.add hJ
  rw [r11b_radialPhysicalMeasure_eq_prod] at hIJ ⊢
  rw [integral_prod _ hIJ]
  apply integral_eq_zero_of_ae
  filter_upwards with r
  have hψ : ContDiff ℝ 1 (fun θ : ℝ => φ (r, θ)) :=
    (hφ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have heAC : AbsolutelyContinuousOnInterval e 0 (2 * Real.pi) :=
    (show ContDiff ℝ 1 e from he.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hderiv : deriv (fun θ : ℝ => φ (r, θ)) =
      fun θ => angularPartial φ (r, θ) :=
    funext (fun θ => deriv_cylinder_angular_slice (hφ.differentiable (by simp)) r θ)
  have hibp := heAC.integral_deriv_mul_eq_sub
    hψ.contDiffOn.absolutelyContinuousOnInterval
  have hψp : φ (r, 2 * Real.pi) = φ (r, 0) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using hφp (r, 0)
  have heπ : e (2 * Real.pi) = e 0 := by simpa only [zero_add] using hep 0
  simp only [hderiv, heπ, hψp, sub_self] at hibp
  change (∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
    (v r * deriv e θ) * φ (r, θ) + (v r * e θ) * angularPartial φ (r, θ)) = 0
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  calc
    _ = v r * (∫ θ in (0 : ℝ)..2 * Real.pi,
        deriv e θ * φ (r, θ) + e θ * angularPartial φ (r, θ)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      ring
    _ = 0 := by rw [hibp, mul_zero]

theorem n06_physicalBoundary_finiteSynthesis {D : ReferenceData} {ι : Type*}
    (s : Finset ι) (v e : ι → ℝ → ℝ) (he : ∀ i ∈ s, Continuous (e i))
    {φ : PolarPoint → ℝ} (hφ : Continuous φ) :
    n06PhysicalBoundary D (r11bFiniteSynthesis s v e) φ =
      ∑ i ∈ s, n06PhysicalBoundary D (fun p => v i p.1 * e i p.2) φ := by
  unfold n06PhysicalBoundary r11bFiniteSynthesis
  simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply intervalIntegral.integral_finsetSum
  intro i hi
  exact (((continuous_const.mul (he i hi)).mul
    (hφ.comp (continuous_const.prodMk continuous_id))).sub
      ((continuous_const.mul (he i hi)).mul
        (hφ.comp (continuous_const.prodMk continuous_id)))).intervalIntegrable _ _

theorem n06_finiteSynthesis_physical_radial_green {D : ReferenceData}
    (hab : D.a ≤ D.b) {ι : Type*} (s : Finset ι) (v e : ι → ℝ → ℝ)
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (v i) D.a D.b)
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (radialCore D)))
    (hvd : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (radialCore D)))
    (he : ∀ i ∈ s, Continuous (e i))
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    (∫ p, r11bFiniteSynthesis s (fun i => deriv (v i)) e p * φ p
      ∂radialPhysicalMeasure D) +
      (∫ p, r11bFiniteSynthesis s v e p * radialPartial φ p ∂radialPhysicalMeasure D) =
      n06PhysicalBoundary D (r11bFiniteSynthesis s v e) φ := by
  have hI (i : ι) (hi : i ∈ s) : Integrable
      (fun p : PolarPoint => (deriv (v i) p.1 * e i p.2) * φ p) (radialPhysicalMeasure D) :=
    (n06_physical_tensor_memLp (hvd i hi) (he i hi)).integrable_mul
      (r11b_continuous_memLp hφ.continuous)
  have hJ (i : ι) (hi : i ∈ s) : Integrable
      (fun p : PolarPoint => (v i p.1 * e i p.2) * radialPartial φ p)
        (radialPhysicalMeasure D) :=
    (n06_physical_tensor_memLp (hv i hi) (he i hi)).integrable_mul
      (r11b_continuous_memLp (r11b_contDiff_directionalPartial hφ (1, 0)).continuous)
  rw [n06_physicalBoundary_finiteSynthesis s v e he hφ.continuous]
  simp only [r11bFiniteSynthesis, Finset.sum_mul]
  rw [integral_finsetSum s hI, integral_finsetSum s hJ, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i hi =>
    n06_tensor_physical_radial_green hab (hAC i hi) (hv i hi) (hvd i hi) (he i hi) hφ)

theorem n06_finiteSynthesis_physical_angular_green {D : ReferenceData}
    {ι : Type*} (s : Finset ι) (v e : ι → ℝ → ℝ)
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (radialCore D)))
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i))
    (hep : ∀ i ∈ s, Function.Periodic (e i) (2 * Real.pi))
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφp : Function.Periodic φ (0, 2 * Real.pi)) :
    (∫ p, r11bFiniteSynthesis s v (fun i => deriv (e i)) p * φ p
      ∂radialPhysicalMeasure D) +
      (∫ p, r11bFiniteSynthesis s v e p * angularPartial φ p ∂radialPhysicalMeasure D) = 0 := by
  have hI (i : ι) (hi : i ∈ s) : Integrable
      (fun p : PolarPoint => (v i p.1 * deriv (e i) p.2) * φ p) (radialPhysicalMeasure D) :=
    (n06_physical_tensor_memLp (hv i hi) ((he i hi).continuous_deriv (by simp))).integrable_mul
      (r11b_continuous_memLp hφ.continuous)
  have hJ (i : ι) (hi : i ∈ s) : Integrable
      (fun p : PolarPoint => (v i p.1 * e i p.2) * angularPartial φ p)
        (radialPhysicalMeasure D) :=
    (n06_physical_tensor_memLp (hv i hi) (he i hi).continuous).integrable_mul
      (r11b_continuous_memLp (r11b_contDiff_directionalPartial hφ (0, 1)).continuous)
  simp only [r11bFiniteSynthesis, Finset.sum_mul]
  rw [integral_finsetSum s hI, integral_finsetSum s hJ, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero (fun i hi =>
    n06_tensor_physical_angular_green (hv i hi) (he i hi) (hep i hi) hφ hφp)

end ContinuousFlexibility.Analysis
