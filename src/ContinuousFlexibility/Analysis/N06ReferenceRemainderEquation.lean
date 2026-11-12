import ContinuousFlexibility.Analysis.N06ReferenceRemainderFields

/-!
# The reference graph equation after removing the actual left tail

Green symmetry moves the left-tail column onto the forcing. All three
physical pairings are integrable before they are subtracted. This theorem
applies to the original maximal weak graph and does not posit a modal
equation, smoothness of the unknown, or a new domain realization.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem n06_referenceRemainder_equation
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hb : RadialTrueBorder D)
    {χ : ℝ → ℝ} (hcutoff : ContDiff ℝ ∞ χ)
    {γ M₀ M₁ μ : ℝ} {η g : PolarPoint → ℝ}
    (hgraph : ReferenceGraph D γ M₀ M₁ (η, μ) (g, 0))
    (aL : ℝ) {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    Integrable (fun p => n06ReferenceRemainder χ η aL p *
      n06ReferenceTestOperator D φ p) (radialPhysicalMeasure D) ∧
    Integrable (fun p => n06ReferenceRemainderForcing D χ g μ aL p * φ p)
      (radialPhysicalMeasure D) ∧
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      n06ReferenceRemainder χ η aL (r, θ) * n06ReferenceTestOperator D φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06ReferenceRemainderForcing D χ g μ aL (r, θ) * φ (r, θ)) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hχ := n06_referenceLeftField_contDiff hcutoff
  have hPφ : Continuous (n06ReferenceTestOperator D φ) :=
    r11b_continuous_radialPDE_test hgeom hφ.1
  have hPχ : Continuous (n06ReferenceTestOperator D (n06ReferenceLeftField χ)) :=
    r11b_continuous_radialPDE_test hgeom hχ
  have hφLp := r11b_continuous_memLp (D := D) hφ.1.continuous
  have hχLp := r11b_continuous_memLp (D := D) hχ.continuous
  have hPφLp := r11b_continuous_memLp (D := D) hPφ
  have hPχLp := r11b_continuous_memLp (D := D) hPχ
  have hνLp := r11b_continuous_memLp (D := D)
    (n06_referenceNuField_continuous hgeom hb)
  have hηI : Integrable (fun p => η p * n06ReferenceTestOperator D φ p)
      (radialPhysicalMeasure D) :=
    r11b_radialPDE_test_pairing_integrable hD hb hgraph.1 hφ
  have hgI : Integrable (fun p => g p * φ p) (radialPhysicalMeasure D) :=
    r11b_source_radialTest_pairing_integrable hD hgraph.2.1 hφ
  have hνI : Integrable (fun p => n06ReferenceNuField D p * φ p)
      (radialPhysicalMeasure D) := hνLp.integrable_mul hφLp
  have hχI : Integrable (fun p => n06ReferenceLeftField χ p * n06ReferenceTestOperator D φ p)
      (radialPhysicalMeasure D) := hχLp.integrable_mul hPφLp
  have hPχI : Integrable (fun p => n06ReferenceTestOperator D (n06ReferenceLeftField χ) p * φ p)
      (radialPhysicalMeasure D) := hPχLp.integrable_mul hφLp
  have hφPχI : Integrable (fun p => φ p * n06ReferenceTestOperator D (n06ReferenceLeftField χ) p)
      (radialPhysicalMeasure D) := hφLp.integrable_mul hPχLp
  have hremI : Integrable (fun p => n06ReferenceRemainder χ η aL p *
      n06ReferenceTestOperator D φ p) (radialPhysicalMeasure D) :=
    n06_integrable_sub_mul hηI hχI aL
  have hforceI : Integrable (fun p => n06ReferenceRemainderForcing D χ g μ aL p * φ p)
      (radialPhysicalMeasure D) :=
    n06_integrable_sub_mul (n06_integrable_sub_mul hgI hνI μ) hPχI aL
  refine ⟨hremI, hforceI, ?_⟩
  have heq := hgraph.2.2.2 φ hφ
  change (∫ r in D.a..D.b, radialAngularMean (fun θ =>
    η (r, θ) * n06ReferenceTestOperator D φ (r, θ))) +
      μ * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06ReferenceNuField D (r, θ) * φ (r, θ))) =
        ∫ r in D.a..D.b, radialAngularMean (fun θ => g (r, θ) * φ (r, θ)) at heq
  rw [r11b_integral_angularMean_eq hgeom.2.1.le hηI,
    r11b_integral_angularMean_eq hgeom.2.1.le hνI,
    r11b_integral_angularMean_eq hgeom.2.1.le hgI] at heq
  have hgreen := reference_smooth_pairing_symm hgeom hχ hφ.1
    (n06_referenceLeftField_periodic χ (2 * Real.pi)) hφ.2.1
  change (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      n06ReferenceLeftField χ (r, θ) * n06ReferenceTestOperator D φ (r, θ))) =
    ∫ r in D.a..D.b, radialAngularMean (fun θ =>
      φ (r, θ) * n06ReferenceTestOperator D (n06ReferenceLeftField χ) (r, θ)) at hgreen
  rw [r11b_integral_angularMean_eq hgeom.2.1.le hχI,
    r11b_integral_angularMean_eq hgeom.2.1.le hφPχI] at hgreen
  have hswap : (∫ p, φ p * n06ReferenceTestOperator D (n06ReferenceLeftField χ) p
      ∂radialPhysicalMeasure D) =
    ∫ p, n06ReferenceTestOperator D (n06ReferenceLeftField χ) p * φ p
      ∂radialPhysicalMeasure D := by
    apply integral_congr_ae
    filter_upwards with p
    exact mul_comm _ _
  rw [hswap] at hgreen
  rw [r11b_integral_angularMean_eq hgeom.2.1.le hremI,
    r11b_integral_angularMean_eq hgeom.2.1.le hforceI]
  simp only [n06ReferenceRemainder, n06ReferenceRemainderForcing]
  rw [n06_integral_sub_mul hηI hχI aL,
    n06_integral_sub_mul (n06_integrable_sub_mul hgI hνI μ) hPχI aL,
    n06_integral_sub_mul hgI hνI μ]
  linear_combination heq - aL * hgreen

end ContinuousFlexibility.Statements
