import ContinuousFlexibility.Analysis.N06ReferenceNormalProjection
import ContinuousFlexibility.Radial.R11bPhysicalCompleteness
import ContinuousFlexibility.Radial.ReferenceCommonInverse

/-!
# The physical normal derivative is independent of the weighted realization

The first-normal estimates at different material weights or attenuation
exponents differentiate the same original physical field. Their actual
normal coefficients agree by the weak equation. Even Fourier completeness
therefore identifies the full L2 fields, and the original weighted output
norms transfer without changing the selected representative or constant.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Uniqueness holds for the full physical normal field, not only each
finite frequency projection. -/
theorem WeakNormalDerivative.n06_unique_of_even_periodic {D : ReferenceData}
    {u d e : PolarPoint → ℝ} (hud : WeakNormalDerivative D u d) (hab : D.a ≤ D.b)
    (hd : MemLp d 2 (radialPhysicalMeasure D))
    (he : MemLp e 2 (radialPhysicalMeasure D))
    (hue : WeakNormalDerivative D u e)
    (hdp : Function.Periodic d (0, Real.pi))
    (hep : Function.Periodic e (0, Real.pi))
    (hde : ∀ r θ, d (r, -θ) = d (r, θ))
    (hee : ∀ r θ, e (r, -θ) = e (r, θ)) :
    d =ᵐ[radialPhysicalMeasure D] e := by
  apply r11b_physical_ae_eq_of_referenceModes hd he hde hee
  · intro r θ
    simpa only [Prod.mk_add_mk, add_zero] using hdp (r, θ)
  · intro r θ
    simpa only [Prod.mk_add_mk, add_zero] using hep (r, θ)
  · filter_upwards [WeakNormalDerivative.n06_coefficient_unique hud hab hd he hue 0]
      with r hr
    simpa only [referenceRadialCoefficient_zero] using hr
  · intro j hj hjEven
    obtain ⟨n, hn⟩ := hjEven
    have hindex : j = 2 * n := by omega
    have hc := WeakNormalDerivative.n06_coefficient_unique hud hab hd he hue n
    have heq (v : PolarPoint → ℝ) : referenceRadialCoefficient v n = referenceMode v j := by
      funext r
      cases n with
      | zero => omega
      | succ k =>
          rw [referenceRadialCoefficient_succ]
          congr 1
          omega
    rw [heq d, heq e] at hc
    exact hc

/-- Two original first-normal output realizations can be placed on the
same representative. This applies, in particular, to the three exponents
retained by `IsRadialReference`. -/
theorem n06_referenceNormal_weighted_realizations_agree {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ δ M N : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ) {u d e : PolarPoint → ℝ}
    (hud : WeakNormalDerivative D u d) (hue : WeakNormalDerivative D u e)
    (hd : OutputRealization D γ M 0 (d, 0))
    (he : OutputRealization D δ N 0 (e, 0)) :
    d =ᵐ[radialPhysicalMeasure D] e ∧
      OutputRealization D δ N 0 (d, 0) ∧
      outputNormSquare D δ N 0 (d, 0) = outputNormSquare D δ N 0 (e, 0) := by
  have hab := hD.choose_spec.1.2.1.le
  have hdLp : MemLp d 2 (radialPhysicalMeasure D) := by
    simpa only [n06_outputRemainder_zero] using r11b_outputRemainder_memLp hD hγ hd
  have heLp : MemLp e 2 (radialPhysicalMeasure D) := by
    simpa only [n06_outputRemainder_zero] using r11b_outputRemainder_memLp hD hδ he
  have heq := WeakNormalDerivative.n06_unique_of_even_periodic hud hab hdLp heLp hue
    hd.2.2.1 he.2.2.1 hd.2.2.2 he.2.2.2
  have hd' : OutputRealization D δ N 0 (d, 0) :=
    OutputRealization.congr_ae hab he ⟨rfl, heq.symm⟩ hd.2.2.1 hd.2.2.2
  exact ⟨heq, hd', outputNormSquare_congr_ae hab hd' ⟨rfl, heq⟩⟩

end ContinuousFlexibility.Radial
