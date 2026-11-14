module

public import ContinuousFlexibility.Analysis.N06UnitTestCalculus

/-!
# Actual weak differentiation of finite radial/angular tensors

Radial integration by parts uses absolute continuity on the closed unit
interval. Angular integration by parts only requires a smooth periodic
angular factor; its radial coefficient remains an arbitrary L2 function.
Fubini places both identities in the original cylinder window measure.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n06_unit_tensor_memLp {v e : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioo (0 : ℝ) 1))) (he : Continuous e) :
    MemLp (fun p : PolarPoint => v p.1 * e p.2) 2 (cylinderWindowMeasure 0) := by
  rw [n06_weak_unitWindow_eq_prod]
  exact r11b_memLp_tensor hv (n06_weak_halfPeriod_memLp_of_continuous he)

/-- This applies both to v and to its absolutely continuous first derivative. -/
theorem n06_tensor_weak_radial {v e : ℝ → ℝ}
    (hvAC : AbsolutelyContinuousOnInterval v 0 1)
    (hv : MemLp v 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hvd : MemLp (deriv v) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (he : Continuous e) {φ : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ) :
    (∫ p, (deriv v p.1 * e p.2) * φ p ∂cylinderWindowMeasure 0) =
      -(∫ p, (v p.1 * e p.2) * radialPartial φ p ∂cylinderWindowMeasure 0) := by
  have hI : Integrable (fun p : PolarPoint => (deriv v p.1 * e p.2) * φ p)
      (cylinderWindowMeasure 0) :=
    (n06_unit_tensor_memLp hvd he).integrable_mul hφ.n06_memLp
  have hJ : Integrable (fun p : PolarPoint => (v p.1 * e p.2) * radialPartial φ p)
      (cylinderWindowMeasure 0) :=
    (n06_unit_tensor_memLp hv he).integrable_mul hφ.n06_radialPartial.n06_memLp
  rw [n06_weak_unitWindow_eq_prod] at hI hJ ⊢
  rw [integral_prod_symm _ hI, integral_prod_symm _ hJ, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with θ
  rw [← n06_unit_intervalIntegral_eq, ← n06_unit_intervalIntegral_eq]
  have hψ : ContDiff ℝ 1 (fun r : ℝ => φ (r, θ)) :=
    (hφ.1.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  have hψAC : AbsolutelyContinuousOnInterval (fun r : ℝ => φ (r, θ)) 0 1 :=
    hψ.contDiffOn.absolutelyContinuousOnInterval
  have hψ0 : φ (0, θ) = 0 := hφ.n06_zero_of_not_mem (by simp)
  have hψ1 : φ (1, θ) = 0 := hφ.n06_zero_of_not_mem (by simp)
  have hderiv : deriv (fun r : ℝ => φ (r, θ)) =
      fun r => radialPartial φ (r, θ) :=
    funext (fun r => deriv_cylinder_radial_slice (hφ.1.differentiable (by simp)) r θ)
  have hibp := hvAC.integral_mul_deriv_eq_deriv_mul hψAC
  simp only [hψ0, hψ1, mul_zero, sub_zero, zero_sub, hderiv] at hibp
  have hbase : (∫ r in (0 : ℝ)..1, deriv v r * φ (r, θ)) =
      -(∫ r in (0 : ℝ)..1, v r * radialPartial φ (r, θ)) := by
    linarith only [hibp]
  calc
    _ = e θ * (∫ r in (0 : ℝ)..1, deriv v r * φ (r, θ)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      ring
    _ = -(e θ * (∫ r in (0 : ℝ)..1, v r * radialPartial φ (r, θ))) := by
      rw [hbase, mul_neg]
    _ = _ := by
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      ring

/-- No radial smoothness is needed for the genuine angular weak identity. -/
theorem n06_tensor_weak_angular {v e : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (he : ContDiff ℝ ∞ e) (hep : Function.Periodic e Real.pi)
    {φ : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ) :
    (∫ p, (v p.1 * deriv e p.2) * φ p ∂cylinderWindowMeasure 0) =
      -(∫ p, (v p.1 * e p.2) * angularPartial φ p ∂cylinderWindowMeasure 0) := by
  have hed : Continuous (deriv e) := he.continuous_deriv (by simp)
  have hI : Integrable (fun p : PolarPoint => (v p.1 * deriv e p.2) * φ p)
      (cylinderWindowMeasure 0) :=
    (n06_unit_tensor_memLp hv hed).integrable_mul hφ.n06_memLp
  have hJ : Integrable (fun p : PolarPoint => (v p.1 * e p.2) * angularPartial φ p)
      (cylinderWindowMeasure 0) :=
    (n06_unit_tensor_memLp hv he.continuous).integrable_mul hφ.n06_angularPartial.n06_memLp
  rw [n06_weak_unitWindow_eq_prod] at hI hJ ⊢
  rw [integral_prod _ hI, integral_prod _ hJ, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with r
  have hψ : ContDiff ℝ 1 (fun θ : ℝ => φ (r, θ)) :=
    (hφ.1.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hψAC : AbsolutelyContinuousOnInterval (fun θ : ℝ => φ (r, θ)) 0 Real.pi :=
    hψ.contDiffOn.absolutelyContinuousOnInterval
  have heAC : AbsolutelyContinuousOnInterval e 0 Real.pi :=
    (show ContDiff ℝ 1 e from he.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hψp : φ (r, Real.pi) = φ (r, 0) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using hφ.2.1 (r, 0)
  have heπ : e Real.pi = e 0 := by simpa only [zero_add] using hep 0
  have hderiv : deriv (fun θ : ℝ => φ (r, θ)) =
      fun θ => angularPartial φ (r, θ) :=
    funext (fun θ => deriv_cylinder_angular_slice (hφ.1.differentiable (by simp)) r θ)
  have hibp := heAC.integral_mul_deriv_eq_deriv_mul hψAC
  simp only [hψp, heπ, sub_self, zero_sub, hderiv] at hibp
  have hbase : (∫ θ in (0 : ℝ)..Real.pi, deriv e θ * φ (r, θ)) =
      -(∫ θ in (0 : ℝ)..Real.pi, e θ * angularPartial φ (r, θ)) := by
    linarith only [hibp]
  have hscaled : (∫ θ in (0 : ℝ)..Real.pi, (v r * deriv e θ) * φ (r, θ)) =
      -(∫ θ in (0 : ℝ)..Real.pi, (v r * e θ) * angularPartial φ (r, θ)) := by
    simp only [mul_assoc, intervalIntegral.integral_const_mul]
    rw [hbase, mul_neg]
  simpa only [intervalIntegral.integral_of_le Real.pi_pos.le] using hscaled

theorem n06_finiteSynthesis_weak_radial {ι : Type*} (s : Finset ι)
    (v e : ι → ℝ → ℝ)
    (hvAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (v i) 0 1)
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hvd : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (he : ∀ i ∈ s, Continuous (e i))
    {φ : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ) :
    (∫ p, r11bFiniteSynthesis s (fun i => deriv (v i)) e p * φ p
      ∂cylinderWindowMeasure 0) =
      -(∫ p, r11bFiniteSynthesis s v e p * radialPartial φ p ∂cylinderWindowMeasure 0) := by
  have hI (i : ι) (hi : i ∈ s) :
      Integrable (fun p : PolarPoint => (deriv (v i) p.1 * e i p.2) * φ p)
        (cylinderWindowMeasure 0) :=
    (n06_unit_tensor_memLp (hvd i hi) (he i hi)).integrable_mul hφ.n06_memLp
  have hJ (i : ι) (hi : i ∈ s) :
      Integrable (fun p : PolarPoint => (v i p.1 * e i p.2) * radialPartial φ p)
        (cylinderWindowMeasure 0) :=
    (n06_unit_tensor_memLp (hv i hi) (he i hi)).integrable_mul hφ.n06_radialPartial.n06_memLp
  simp only [r11bFiniteSynthesis, Finset.sum_mul]
  rw [integral_finsetSum s hI, integral_finsetSum s hJ, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i hi =>
    n06_tensor_weak_radial (hvAC i hi) (hv i hi) (hvd i hi) (he i hi) hφ)

theorem n06_finiteSynthesis_weak_angular {ι : Type*} (s : Finset ι)
    (v e : ι → ℝ → ℝ)
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i))
    (hep : ∀ i ∈ s, Function.Periodic (e i) Real.pi)
    {φ : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ) :
    (∫ p, r11bFiniteSynthesis s v (fun i => deriv (e i)) p * φ p
      ∂cylinderWindowMeasure 0) =
      -(∫ p, r11bFiniteSynthesis s v e p * angularPartial φ p ∂cylinderWindowMeasure 0) := by
  have hI (i : ι) (hi : i ∈ s) :
      Integrable (fun p : PolarPoint => (v i p.1 * deriv (e i) p.2) * φ p)
        (cylinderWindowMeasure 0) :=
    (n06_unit_tensor_memLp (hv i hi)
      ((he i hi).continuous_deriv (by simp))).integrable_mul hφ.n06_memLp
  have hJ (i : ι) (hi : i ∈ s) :
      Integrable (fun p : PolarPoint => (v i p.1 * e i p.2) * angularPartial φ p)
        (cylinderWindowMeasure 0) :=
    (n06_unit_tensor_memLp (hv i hi) (he i hi).continuous).integrable_mul
      hφ.n06_angularPartial.n06_memLp
  simp only [r11bFiniteSynthesis, Finset.sum_mul]
  rw [integral_finsetSum s hI, integral_finsetSum s hJ, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i hi =>
    n06_tensor_weak_angular (hv i hi) (he i hi) (hep i hi) hφ)

end ContinuousFlexibility.Analysis
