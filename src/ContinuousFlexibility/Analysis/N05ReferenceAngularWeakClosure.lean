import ContinuousFlexibility.Analysis.N05ReferenceAngularIntegration
import ContinuousFlexibility.Analysis.N05ReferenceAngularJetCells
import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
import ContinuousFlexibility.Radial.R11bWeakNormalLimit

/-!
# Reference angular weak jets and their actual L² limits

The test class, radial interval, angular average and ordinary test
derivatives are the ones of the reference physical problem. Finite high
projections satisfy this identity without radial smoothness. Physical
L² convergence of a field and its jet preserves the same identity.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

def n05_weakReferenceAngularJet (D : ReferenceData)
    (u d : PolarPoint → ℝ) (b : ℕ) : Prop :=
  ∀ ψ, RadialTest D ψ →
    (∫ r in D.a..D.b, radialAngularMean (fun θ => d (r, θ) * ψ (r, θ))) =
      (-1 : ℝ) ^ b * ∫ r in D.a..D.b, radialAngularMean
        (fun θ => u (r, θ) * mixedDerivative 0 b ψ (r, θ))

theorem n05_referenceHighAngularJet_weak (D : ReferenceData)
    (J : Finset ℕ) (b : ℕ) (f : PolarPoint → ℝ) :
    n05_weakReferenceAngularJet D
      (referenceBasisProjection (J.image (fun n => n + 2)) f)
      (n05_referenceHighAngularJet J b f) b := by
  intro ψ hψ
  have hpoint (r : ℝ) :
      radialAngularMean (fun θ => n05_referenceHighAngularJet J b f (r, θ) * ψ (r, θ)) =
        (-1 : ℝ) ^ b * radialAngularMean (fun θ =>
          referenceBasisProjection (J.image (fun n => n + 2)) f (r, θ) *
            mixedDerivative 0 b ψ (r, θ)) := by
    have hfr : ContDiff ℝ ∞ (fun θ =>
        referenceBasisProjection (J.image (fun n => n + 2)) f (r, θ)) := by
      change ContDiff ℝ ∞ (fun θ => ∑ n ∈ J.image (fun n => n + 2),
        referenceAngularCoefficient (fun φ => f (r, φ)) n * referenceAngularBasis n θ)
      apply ContDiff.sum
      intro n _
      exact contDiff_const.mul (contDiff_referenceAngularBasis n)
    have hfpr : Function.Periodic (fun θ =>
        referenceBasisProjection (J.image (fun n => n + 2)) f (r, θ))
        (2 * Real.pi) := by
      intro θ
      change (∑ n ∈ J.image (fun n => n + 2),
        referenceAngularCoefficient (fun φ => f (r, φ)) n *
          referenceAngularBasis n (θ + 2 * Real.pi)) = _
      apply Finset.sum_congr rfl
      intro n _
      rw [referenceAngularBasis_periodic_two_pi n θ]
    have hφr : ContDiff ℝ ∞ (fun θ : ℝ => ψ (r, θ)) :=
      hψ.1.comp (contDiff_const.prodMk contDiff_id)
    have hφpr : Function.Periodic (fun θ : ℝ => ψ (r, θ)) (2 * Real.pi) := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hψ.2.1 (r, θ)
    have h := n05_integral_periodic_iteratedDeriv_mul hfr hfpr b hφr hφpr
    simp only [n05_referenceHighAngularJet, mixedDerivative, iteratedDeriv_zero,
      radialAngularMean]
    rw [h]
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]

/-- Closure uses continuous physical pairings for the actual test jets;
the conclusion keeps exactly the original weak derivative relation. -/
theorem n05_weakReferenceAngularJet_of_L2_tendsto
    {D : ReferenceData} (hab : D.a ≤ D.b) {b : ℕ}
    {f d : ℕ → PolarPoint → ℝ} {u v : PolarPoint → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (radialPhysicalMeasure D))
    (hd : ∀ n, MemLp (d n) 2 (radialPhysicalMeasure D))
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hv : MemLp v 2 (radialPhysicalMeasure D))
    (hfu : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u)))
    (hdv : Tendsto (fun n => (hd n).toLp (d n)) atTop (𝓝 (hv.toLp v)))
    (hweak : ∀ n, n05_weakReferenceAngularJet D (f n) (d n) b) :
    n05_weakReferenceAngularJet D u v b := by
  intro ψ hψ
  have hψLp : MemLp ψ 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp hψ.1.continuous
  have hψbLp : MemLp (mixedDerivative 0 b ψ) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (contDiff_mixedDerivative hψ.1 0 b).continuous
  have hleft := r11b_tendsto_angularMean_pairing_of_L2_tendsto hab hd hv hψLp hdv
  have hright := r11b_tendsto_angularMean_pairing_of_L2_tendsto hab hf hu hψbLp hfu
  have hseq : (fun n => ∫ r in D.a..D.b,
      radialAngularMean (fun θ => d n (r, θ) * ψ (r, θ))) =
      fun n => (-1 : ℝ) ^ b * ∫ r in D.a..D.b,
        radialAngularMean (fun θ => f n (r, θ) * mixedDerivative 0 b ψ (r, θ)) :=
    funext fun n => hweak n ψ hψ
  rw [hseq] at hleft
  exact tendsto_nhds_unique hleft (hright.const_mul ((-1 : ℝ) ^ b))

end ContinuousFlexibility.Radial
