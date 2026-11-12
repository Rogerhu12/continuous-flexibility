import ContinuousFlexibility.Analysis.N05ReferenceNormalUniqueness
import ContinuousFlexibility.Radial.ReferenceGraphProjection
import ContinuousFlexibility.Radial.R11bWeakNormalLimit

/-!
# Angular projections of the actual physical normal derivative

Differentiation under the genuine angular integral gives commutation on
smooth tests. Self-adjointness then projects the physical weak derivative,
and L² representatives preserve that same weak relation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem n05_referenceBasisProjection_radialPartial {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (I : Finset ℕ) :
    radialPartial (referenceBasisProjection I φ) =
      referenceBasisProjection I (radialPartial φ) := by
  funext p
  have hp := referenceBasisProjection_contDiff hφ I
  apply (hasDerivAt_radial_slice (hp.differentiable (by simp) p)).unique
  change HasDerivAt
    (fun r => ∑ n ∈ I, referenceRadialCoefficient φ n r * referenceAngularBasis n p.2)
    (∑ n ∈ I, referenceRadialCoefficient (radialPartial φ) n p.1 *
      referenceAngularBasis n p.2) p.1
  exact HasDerivAt.fun_sum (fun n _ =>
    (hasDerivAt_referenceRadialCoefficient hφ n p.1).mul_const (referenceAngularBasis n p.2))

theorem n05_referenceBasisProjection_memLp {D : ReferenceData}
    {u : PolarPoint → ℝ} (hu : MemLp u 2 (radialPhysicalMeasure D)) (I : Finset ℕ) :
    MemLp (referenceBasisProjection I u) 2 (radialPhysicalMeasure D) := by
  rw [r11b_radialPhysicalMeasure_eq_prod] at hu ⊢
  exact memLp_referenceBasisProjection_prod hu I

theorem n05_weakNormalDerivative_basisProjection {D : ReferenceData}
    (hab : D.a ≤ D.b) {u d : PolarPoint → ℝ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hd : MemLp d 2 (radialPhysicalMeasure D))
    (hweak : WeakNormalDerivative D u d) (I : Finset ℕ) :
    WeakNormalDerivative D (referenceBasisProjection I u) (referenceBasisProjection I d) := by
  intro ψ hψ
  have hψLp : MemLp ψ 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp hψ.1.continuous
  have hψrLp : MemLp (radialPartial ψ) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (r11b_radialTest_radialPartial hψ).1.continuous
  rw [referenceBasisProjection_integral_pairing hab hu hψrLp I,
    referenceBasisProjection_integral_pairing hab hd hψLp I]
  have hw := hweak _ (referenceBasisProjection_test hψ I)
  rw [n05_referenceBasisProjection_radialPartial hψ.1 I] at hw
  exact hw

theorem n05_weakNormalDerivative_congr_ae {D : ReferenceData}
    (hab : D.a ≤ D.b) {u v d e : PolarPoint → ℝ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hv : MemLp v 2 (radialPhysicalMeasure D))
    (hd : MemLp d 2 (radialPhysicalMeasure D))
    (he : MemLp e 2 (radialPhysicalMeasure D))
    (huv : u =ᵐ[radialPhysicalMeasure D] v)
    (hde : d =ᵐ[radialPhysicalMeasure D] e)
    (hweak : WeakNormalDerivative D u d) : WeakNormalDerivative D v e := by
  intro ψ hψ
  have hψLp : MemLp ψ 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp hψ.1.continuous
  have hψrLp : MemLp (radialPartial ψ) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (r11b_radialTest_radialPartial hψ).1.continuous
  have hleft := r11b_integral_angularMean_congr_ae hab
    (hu.integrable_mul hψrLp) (hv.integrable_mul hψrLp)
    (huv.mul (show radialPartial ψ =ᵐ[radialPhysicalMeasure D] radialPartial ψ
      from Filter.EventuallyEq.rfl))
  have hright := r11b_integral_angularMean_congr_ae hab
    (hd.integrable_mul hψLp) (he.integrable_mul hψLp)
    (hde.mul (show ψ =ᵐ[radialPhysicalMeasure D] ψ from Filter.EventuallyEq.rfl))
  simp only [Pi.mul_apply] at hleft hright
  rw [← hleft, ← hright]
  exact hweak ψ hψ

end ContinuousFlexibility.Radial
