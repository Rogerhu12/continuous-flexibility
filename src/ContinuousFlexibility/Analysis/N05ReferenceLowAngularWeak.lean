import ContinuousFlexibility.Analysis.N05ReferenceAngularWeakClosure
import ContinuousFlexibility.Analysis.N05ReferenceLowAngularBasis

/-!
# Weak identities for the actual low angular jets

Angular smoothness on each radial slice suffices for periodic integration
by parts. Addition is justified through the actual physical L² pairings.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem n05_referenceAngularJet_weak_of_smooth_slices (D : ReferenceData)
    (u : PolarPoint → ℝ)
    (hu : ∀ r, ContDiff ℝ ∞ (fun θ => u (r, θ)))
    (hp : ∀ r, Function.Periodic (fun θ => u (r, θ)) (2 * Real.pi)) (b : ℕ) :
    n05_weakReferenceAngularJet D u (mixedDerivative 0 b u) b := by
  intro ψ hψ
  have hpoint (r : ℝ) :
      radialAngularMean (fun θ => mixedDerivative 0 b u (r, θ) * ψ (r, θ)) =
        (-1 : ℝ) ^ b * radialAngularMean
          (fun θ => u (r, θ) * mixedDerivative 0 b ψ (r, θ)) := by
    have hφ : ContDiff ℝ ∞ (fun θ : ℝ => ψ (r, θ)) :=
      hψ.1.comp (contDiff_const.prodMk contDiff_id)
    have hφp : Function.Periodic (fun θ : ℝ => ψ (r, θ)) (2 * Real.pi) := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hψ.2.1 (r, θ)
    have h := n05_integral_periodic_iteratedDeriv_mul (hu r) (hp r) b hφ hφp
    simp only [mixedDerivative, iteratedDeriv_zero, radialAngularMean]
    rw [h]
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]

theorem n05_referenceLowAngularJet_weak (D : ReferenceData)
    (u : PolarPoint → ℝ) (b : ℕ) :
    n05_weakReferenceAngularJet D (referenceBasisProjection {0, 1} u)
      (n05_referenceLowAngularJet b u) b := by
  apply n05_referenceAngularJet_weak_of_smooth_slices
  · intro r
    change ContDiff ℝ ∞ (fun θ => ∑ n ∈ ({0, 1} : Finset ℕ),
      referenceAngularCoefficient (fun φ => u (r, φ)) n * referenceAngularBasis n θ)
    apply ContDiff.sum
    intro n _
    exact contDiff_const.mul (contDiff_referenceAngularBasis n)
  · intro r θ
    change (∑ n ∈ ({0, 1} : Finset ℕ),
      referenceAngularCoefficient (fun φ => u (r, φ)) n *
        referenceAngularBasis n (θ + 2 * Real.pi)) = _
    apply Finset.sum_congr rfl
    intro n _
    rw [referenceAngularBasis_periodic_two_pi n θ]

theorem n05_referenceMeanPairing_add {D : ReferenceData} (hab : D.a ≤ D.b)
    {f g k : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D))
    (hg : MemLp g 2 (radialPhysicalMeasure D))
    (hk : MemLp k 2 (radialPhysicalMeasure D)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => (f + g) (r, θ) * k (r, θ))) =
      (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * k (r, θ))) +
        ∫ r in D.a..D.b, radialAngularMean (fun θ => g (r, θ) * k (r, θ)) := by
  rw [r11b_integral_angularMean_mul_eq hab (hf.add hg) hk,
    r11b_integral_angularMean_mul_eq hab hf hk,
    r11b_integral_angularMean_mul_eq hab hg hk]
  simp only [Pi.add_apply, add_mul]
  rw [integral_add (hf.integrable_mul hk) (hg.integrable_mul hk), mul_add]

theorem n05_weakReferenceAngularJet_add {D : ReferenceData} (hab : D.a ≤ D.b)
    {u v d e : PolarPoint → ℝ} {b : ℕ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hv : MemLp v 2 (radialPhysicalMeasure D))
    (hd : MemLp d 2 (radialPhysicalMeasure D))
    (he : MemLp e 2 (radialPhysicalMeasure D))
    (hud : n05_weakReferenceAngularJet D u d b)
    (hve : n05_weakReferenceAngularJet D v e b) :
    n05_weakReferenceAngularJet D (u + v) (d + e) b := by
  intro ψ hψ
  have hψLp : MemLp ψ 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp hψ.1.continuous
  have hψbLp : MemLp (mixedDerivative 0 b ψ) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (contDiff_mixedDerivative hψ.1 0 b).continuous
  rw [n05_referenceMeanPairing_add hab hd he hψLp,
    n05_referenceMeanPairing_add hab hu hv hψbLp, hud ψ hψ, hve ψ hψ, mul_add]

end ContinuousFlexibility.Radial
