module

public import ContinuousFlexibility.Analysis.N06HalfPhysicalPairing
public import ContinuousFlexibility.Analysis.PhysicalTransmissionOperator

/-!
# Returning from half-period tests to the original physical test class

The actual symmetric divergence operator commutes with half-period
averaging when its three coefficients have period `pi`. A fourth,
periodic potential coefficient is retained explicitly. Fubini then
connects the existing angular pairing identity to the original radial
weak pairing for every `RadialTest`, including tests which are not even
and have period only `2 * pi`. The existing averaging construction
preserves the original compact radial support.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n06_radialTestAverage_apply (φ : PolarPoint → ℝ) (p : PolarPoint) :
    n06_radialTestAverage φ p = (φ p + φ (p + (0, Real.pi))) / 2 := by
  simp only [n06_radialTestAverage, n06_halfPeriodAverage, Prod.add_def,
    add_zero, Prod.mk.eta]

private theorem average_add (f g : PolarPoint → ℝ) :
    n06_radialTestAverage (fun p => f p + g p) =
      fun p => n06_radialTestAverage f p + n06_radialTestAverage g p := by
  funext p
  simp only [n06_radialTestAverage_apply]
  ring

private theorem average_mul {a : PolarPoint → ℝ}
    (ha : Function.Periodic a (0, Real.pi)) (f : PolarPoint → ℝ) :
    n06_radialTestAverage (fun p => a p * f p) =
      fun p => a p * n06_radialTestAverage f p := by
  funext p
  simp only [n06_radialTestAverage_apply, ha p]
  ring

/-- Averaging commutes with every genuine first coordinate derivative. -/
theorem n06_fderiv_radialTestAverage {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (p v : PolarPoint) :
    fderiv ℝ (n06_radialTestAverage φ) p v =
      n06_radialTestAverage (fun q => fderiv ℝ φ q v) p := by
  have hshift : ContDiff ℝ ∞ (fun q : PolarPoint => φ (q + (0, Real.pi))) :=
    hφ.comp (contDiff_id.add contDiff_const)
  have heq : n06_radialTestAverage φ =
      fun q : PolarPoint => (1 / 2 : ℝ) * (φ q + φ (q + (0, Real.pi))) := by
    funext q
    rw [n06_radialTestAverage_apply]
    ring
  rw [heq, fderiv_const_mul ((hφ.add hshift).differentiable (by simp) p) (1 / 2),
    fderiv_fun_add (hφ.differentiable (by simp) p)
      (hshift.differentiable (by simp) p), fderiv_comp_add_right]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    smul_eq_mul, n06_radialTestAverage_apply]
  ring

theorem n06_radialPartial_radialTestAverage {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    radialPartial (n06_radialTestAverage φ) = n06_radialTestAverage (radialPartial φ) := by
  funext p
  exact n06_fderiv_radialTestAverage hφ p (1, 0)

theorem n06_angularPartial_radialTestAverage {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) :
    angularPartial (n06_radialTestAverage φ) = n06_radialTestAverage (angularPartial φ) := by
  funext p
  exact n06_fderiv_radialTestAverage hφ p (0, 1)

/-- The actual two mixed channels are retained: the radial flux uses
`a,b` and the angular flux uses `b,c`. No parity of the test is required. -/
theorem n06_divergenceOperator_radialTestAverage
    {L : SymmetricCoefficients} {φ : PolarPoint → ℝ}
    (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b) (hc : ContDiff ℝ ∞ L.c)
    (hpa : Function.Periodic L.a (0, Real.pi))
    (hpb : Function.Periodic L.b (0, Real.pi))
    (hpc : Function.Periodic L.c (0, Real.pi)) (hφ : ContDiff ℝ ∞ φ) :
    divergenceOperator L (n06_radialTestAverage φ) =
      n06_radialTestAverage (divergenceOperator L φ) := by
  have hR : (fun q => L.a q * radialPartial (n06_radialTestAverage φ) q +
      L.b q * angularPartial (n06_radialTestAverage φ) q) =
      n06_radialTestAverage (fun q => L.a q * radialPartial φ q +
        L.b q * angularPartial φ q) := by
    rw [n06_radialPartial_radialTestAverage hφ, n06_angularPartial_radialTestAverage hφ,
      average_add, average_mul hpa, average_mul hpb]
  have hT : (fun q => L.b q * radialPartial (n06_radialTestAverage φ) q +
      L.c q * angularPartial (n06_radialTestAverage φ) q) =
      n06_radialTestAverage (fun q => L.b q * radialPartial φ q +
        L.c q * angularPartial φ q) := by
    rw [n06_radialPartial_radialTestAverage hφ, n06_angularPartial_radialTestAverage hφ,
      average_add, average_mul hpb, average_mul hpc]
  have hRc : ContDiff ℝ ∞ (fun q => L.a q * radialPartial φ q +
      L.b q * angularPartial φ q) :=
    (ha.mul (contDiff_cylinder_radialPartial hφ)).add
      (hb.mul (contDiff_cylinder_angularPartial hφ))
  have hTc : ContDiff ℝ ∞ (fun q => L.b q * radialPartial φ q +
      L.c q * angularPartial φ q) :=
    (hb.mul (contDiff_cylinder_radialPartial hφ)).add
      (hc.mul (contDiff_cylinder_angularPartial hφ))
  funext p
  change radialPartial (fun q => L.a q * radialPartial (n06_radialTestAverage φ) q +
      L.b q * angularPartial (n06_radialTestAverage φ) q) p +
    angularPartial (fun q => L.b q * radialPartial (n06_radialTestAverage φ) q +
      L.c q * angularPartial (n06_radialTestAverage φ) q) p = _
  rw [hR, hT, n06_radialPartial_radialTestAverage hRc,
    n06_angularPartial_radialTestAverage hTc]
  exact (congrFun (average_add
    (radialPartial (fun q => L.a q * radialPartial φ q + L.b q * angularPartial φ q))
    (angularPartial (fun q => L.b q * radialPartial φ q + L.c q * angularPartial φ q))) p).symm

/-- The same identity includes the genuine zeroth coefficient and either
canonical sign of the divergence part. -/
theorem n06_fourCoefficientOperator_radialTestAverage
    (σ : ℝ) {L : SymmetricCoefficients} {V φ : PolarPoint → ℝ}
    (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b) (hc : ContDiff ℝ ∞ L.c)
    (hpa : Function.Periodic L.a (0, Real.pi))
    (hpb : Function.Periodic L.b (0, Real.pi))
    (hpc : Function.Periodic L.c (0, Real.pi))
    (hpV : Function.Periodic V (0, Real.pi)) (hφ : ContDiff ℝ ∞ φ) :
    (fun p => σ * divergenceOperator L (n06_radialTestAverage φ) p +
      V p * n06_radialTestAverage φ p) =
      n06_radialTestAverage (fun p => σ * divergenceOperator L φ p + V p * φ p) := by
  rw [n06_divergenceOperator_radialTestAverage ha hb hc hpa hpb hpc hφ]
  funext p
  simp only [n06_radialTestAverage_apply, hpV p]
  ring

/-- Fubini promotes the existing angular averaging identity to the actual
radial pairing. Only actual integrability is used; the field may be L2. -/
theorem n06_integrated_radialTestAverage_pairing
    {D : ReferenceData} (hab : D.a ≤ D.b) {u φ : PolarPoint → ℝ}
    (hup : Function.Periodic u (0, Real.pi))
    (hint : Integrable (fun p => u p * φ p) (radialPhysicalMeasure D)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, angularMean
        (fun θ => u (r, θ) * n06_radialTestAverage φ (r, θ)) := by
  have hprod : Integrable (fun p => u p * φ p)
      ((volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    rwa [r11b_radialPhysicalMeasure_eq_prod] at hint
  have hae : (fun r => radialAngularMean (fun θ => u (r, θ) * φ (r, θ))) =ᵐ[
      volume.restrict (radialCore D)]
      (fun r => angularMean (fun θ => u (r, θ) * n06_radialTestAverage φ (r, θ))) := by
    filter_upwards [hprod.prod_right_ae] with r hr
    apply n06_radialAngularMean_pairing
    · intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hup (r, θ)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
        (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).mpr hr
  have hrad : (volume : Measure ℝ).restrict (radialCore D) =
      volume.restrict (Ioc D.a D.b) := Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  rw [hrad] at hae
  exact integral_congr_ae hae

/-- A half-period weak equation on the genuine compact physical tests
implies the full original equation on every `RadialTest`. The four
coefficients are unchanged and the same test support is retained by
`n06_radialTestAverage_test`. -/
theorem n06_full_radialWeakEquation_of_half_tests
    {D : ReferenceData} (hab : D.a ≤ D.b) (σ : ℝ)
    {L : SymmetricCoefficients} {V u f : PolarPoint → ℝ}
    (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b) (hc : ContDiff ℝ ∞ L.c)
    (hpa : Function.Periodic L.a (0, Real.pi))
    (hpb : Function.Periodic L.b (0, Real.pi))
    (hpc : Function.Periodic L.c (0, Real.pi))
    (hV : Continuous V) (hpV : Function.Periodic V (0, Real.pi))
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hf : MemLp f 2 (radialPhysicalMeasure D))
    (hup : Function.Periodic u (0, Real.pi))
    (hfp : Function.Periodic f (0, Real.pi))
    (hhalf : ∀ ψ, RadialTest D ψ → Function.Periodic ψ (0, Real.pi) →
      (∫ r in D.a..D.b, angularMean (fun θ => u (r, θ) *
        (σ * divergenceOperator L ψ (r, θ) + V (r, θ) * ψ (r, θ)))) =
        ∫ r in D.a..D.b, angularMean (fun θ => f (r, θ) * ψ (r, θ))) :
    ∀ φ, RadialTest D φ →
      (∫ r in D.a..D.b, radialAngularMean (fun θ => u (r, θ) *
        (σ * divergenceOperator L φ (r, θ) + V (r, θ) * φ (r, θ)))) =
        ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ)) := by
  intro φ hφ
  let Q (ψ : PolarPoint → ℝ) : PolarPoint → ℝ :=
    fun p => σ * divergenceOperator L ψ p + V p * ψ p
  have hQ : Continuous (Q φ) :=
    (continuous_const.mul (contDiff_divergenceOperator ha hb hc hφ.1).continuous).add
      (hV.mul hφ.1.continuous)
  have hIu : Integrable (fun p => u p * Q φ p) (radialPhysicalMeasure D) :=
    hu.integrable_mul (r11b_continuous_memLp hQ)
  have hIf : Integrable (fun p => f p * φ p) (radialPhysicalMeasure D) :=
    hf.integrable_mul (r11b_continuous_memLp hφ.1.continuous)
  have hcomm : Q (n06_radialTestAverage φ) = n06_radialTestAverage (Q φ) :=
    n06_fourCoefficientOperator_radialTestAverage σ ha hb hc hpa hpb hpc hpV hφ.1
  calc
    _ = ∫ r in D.a..D.b, angularMean
        (fun θ => u (r, θ) * n06_radialTestAverage (Q φ) (r, θ)) :=
      n06_integrated_radialTestAverage_pairing hab hup hIu
    _ = ∫ r in D.a..D.b, angularMean
        (fun θ => u (r, θ) * Q (n06_radialTestAverage φ) (r, θ)) := by rw [← hcomm]
    _ = ∫ r in D.a..D.b, angularMean
        (fun θ => f (r, θ) * n06_radialTestAverage φ (r, θ)) :=
      hhalf (n06_radialTestAverage φ) (n06_radialTestAverage_test hφ)
        (n06_radialTestAverage_periodic hφ.2.1)
    _ = _ := (n06_integrated_radialTestAverage_pairing hab hfp hIf).symm

end ContinuousFlexibility.Analysis
