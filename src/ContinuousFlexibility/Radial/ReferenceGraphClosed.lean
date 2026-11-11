import ContinuousFlexibility.Radial.ReferenceGraphNorms
import ContinuousFlexibility.Radial.R11bRadialTests

/-!
# Closure of the actual radial weak graph

The differential expression remains the one in the frozen statement.
Physical L² convergence passes through its test pairings and the actual
border row; the graph is not redefined as the range of an inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter Real
open scoped Topology RealInnerProductSpace
open ContinuousFlexibility.Statements

theorem reference_column_mode_continuous {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D) :
    Continuous (fun x : PolarPoint => referenceColumn D x.1 * cosineMode 2 x.2) := by
  have hcos : Continuous (cosineMode 2) := by
    exact continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  exact ((r11b_continuous_referenceColumn hgeom hborder).comp continuous_fst).mul
    (hcos.comp continuous_snd)

theorem referenceRow_eq_physical_pairing {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D)
    {u : PolarPoint → ℝ} (hu : MemLp u 2 (radialPhysicalMeasure D)) :
    referenceRow D u = (2 * Real.pi)⁻¹ *
      ∫ x, u x * (referenceColumn D x.1 * cosineMode 2 x.2)
        ∂radialPhysicalMeasure D := by
  have hc := r11b_continuous_memLp (D := D) (reference_column_mode_continuous hgeom hborder)
  calc
    referenceRow D u =
        ∫ r in D.a..D.b, radialAngularMean (fun θ =>
          u (r, θ) * (referenceColumn D r * cosineMode 2 θ)) := by
      unfold referenceRow referenceMode
      apply intervalIntegral.integral_congr
      intro r _
      have he : (fun θ => u (r, θ) * (referenceColumn D r * cosineMode 2 θ)) =
          (fun θ => referenceColumn D r * (u (r, θ) * cosineMode 2 θ)) := by
        funext θ
        ring
      change referenceColumn D r * radialAngularMean (fun θ => u (r, θ) * cosineMode 2 θ) =
        radialAngularMean (fun θ => u (r, θ) * (referenceColumn D r * cosineMode 2 θ))
      rw [he, radialAngularMean_const_mul]
    _ = _ := r11b_integral_angularMean_eq hgeom.2.1.le (hu.integrable_mul hc)

theorem reference_mean_pairing_tendsto {D : ReferenceData} (hab : D.a ≤ D.b)
    {f : ℕ → PolarPoint → ℝ} {g k : PolarPoint → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (radialPhysicalMeasure D))
    (hg : MemLp g 2 (radialPhysicalMeasure D))
    (hk : MemLp k 2 (radialPhysicalMeasure D))
    (h : Tendsto (fun n => ∫ x, (f n x - g x) ^ 2 ∂radialPhysicalMeasure D)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ r in D.a..D.b,
      radialAngularMean (fun θ => f n (r, θ) * k (r, θ))) atTop
      (𝓝 (∫ r in D.a..D.b,
        radialAngularMean (fun θ => g (r, θ) * k (r, θ)))) := by
  have he (n : ℕ) :
      (∫ r in D.a..D.b, radialAngularMean (fun θ => f n (r, θ) * k (r, θ))) =
        (2 * Real.pi)⁻¹ * ∫ x, f n x * k x ∂radialPhysicalMeasure D :=
    r11b_integral_angularMean_eq hab ((hf n).integrable_mul hk)
  have he' :
      (∫ r in D.a..D.b, radialAngularMean (fun θ => g (r, θ) * k (r, θ))) =
        (2 * Real.pi)⁻¹ * ∫ x, g x * k x ∂radialPhysicalMeasure D :=
    r11b_integral_angularMean_eq hab (hg.integrable_mul hk)
  simpa only [he, he'] using
    (reference_memLp_pairing_tendsto_of_sub_sq hf hg hk h).const_mul ((2 * Real.pi)⁻¹)

theorem referenceRow_tendsto {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D)
    {f : ℕ → PolarPoint → ℝ} {g : PolarPoint → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (radialPhysicalMeasure D))
    (hg : MemLp g 2 (radialPhysicalMeasure D))
    (h : Tendsto (fun n => ∫ x, (f n x - g x) ^ 2 ∂radialPhysicalMeasure D)
      atTop (𝓝 0)) :
    Tendsto (fun n => referenceRow D (f n)) atTop (𝓝 (referenceRow D g)) := by
  have hc := r11b_continuous_memLp (D := D) (reference_column_mode_continuous hgeom hborder)
  have he (n : ℕ) := referenceRow_eq_physical_pairing hgeom hborder (hf n)
  have he' := referenceRow_eq_physical_pairing hgeom hborder hg
  simpa only [he, he'] using
    (reference_memLp_pairing_tendsto_of_sub_sq hf hg hc h).const_mul ((2 * Real.pi)⁻¹)

/-- Closure holds for every positive attenuation exponent and every fixed
pair of coefficient exponents, before any inverse is assumed. -/
theorem referenceGraphClosed_of_positive {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) :
    ReferenceGraphClosed D γ M₀ M₁ := by
  intro U F Uₙ Fₙ aₙ hgraph hU hF hdiff hFconv hUconv
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hUn (n : ℕ) : OutputMember D γ M₁ (Uₙ n) := (hgraph n).1
  have hFn (n : ℕ) : SourceMember D γ M₀ (Fₙ n) := (hgraph n).2.1
  have huLp : MemLp U.1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ hU
  have hunLp (n : ℕ) : MemLp (Uₙ n).1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ (hUn n)
  have hfLp : MemLp F.1 2 (radialPhysicalMeasure D) :=
    r11b_source_memLp hD hγ hF
  have hfnLp (n : ℕ) : MemLp (Fₙ n).1 2 (radialPhysicalMeasure D) :=
    r11b_source_memLp hD hγ (hFn n)
  have huConv := referenceOutput_sub_sq_tendsto hD hborder hγ hdiff hUconv
  have hfConv := referenceSource_sub_sq_tendsto hD hγ hFn hF hFconv
  have huScalar := referenceOutput_scalar_tendsto hD hborder hγ hdiff hUconv
  have hfScalar := referenceSource_scalar_tendsto hD hγ hFn hF hFconv
  refine ⟨hU, hF, ?_, ?_⟩
  · have hrow := referenceRow_tendsto hgeom hborder hunLp huLp huConv
    have heq : (fun n => referenceRow D (Uₙ n).1) = (fun n => (Fₙ n).2) :=
      funext (fun n => (hgraph n).2.2.1)
    rw [heq] at hrow
    exact tendsto_nhds_unique hrow hfScalar
  · intro ψ hψ
    have hψLp : MemLp ψ 2 (radialPhysicalMeasure D) :=
      r11b_continuous_memLp hψ.1.continuous
    have hLψLp : MemLp
        (fun x : PolarPoint => radialPDE D.w (fun r θ => ψ (r, θ)) x.1 x.2)
        2 (radialPhysicalMeasure D) :=
      r11b_continuous_memLp (r11b_continuous_radialPDE_test hgeom hψ.1)
    have hweak := reference_mean_pairing_tendsto hgeom.2.1.le
      hunLp huLp hLψLp huConv
    change Tendsto (fun n => radialWeakPairing D (Uₙ n).1 ψ) atTop
      (𝓝 (radialWeakPairing D U.1 ψ)) at hweak
    have hright := reference_mean_pairing_tendsto hgeom.2.1.le
      hfnLp hfLp hψLp hfConv
    have hleft := hweak.add (huScalar.mul_const
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        referenceColumn D r * cosineMode 2 θ * ψ (r, θ))))
    have heq :
        (fun n => radialWeakPairing D (Uₙ n).1 ψ + (Uₙ n).2 *
          (∫ r in D.a..D.b, radialAngularMean (fun θ =>
            referenceColumn D r * cosineMode 2 θ * ψ (r, θ)))) =
        (fun n => ∫ r in D.a..D.b,
          radialAngularMean (fun θ => (Fₙ n).1 (r, θ) * ψ (r, θ))) :=
      funext (fun n => (hgraph n).2.2.2 ψ hψ)
    rw [heq] at hleft
    exact tendsto_nhds_unique hleft hright

end ContinuousFlexibility.Radial
