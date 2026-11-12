import ContinuousFlexibility.Analysis.N01aReferenceZeros

/-!
# Recovering signed source measurability from actual Green reciprocity

The second-mode kernel is nonzero almost everywhere. Pairing a source with
its genuine graph therefore gives an integrable product from which the
signed source is recovered by measurable division.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter MeasureTheory

/-- Measurability can be recovered from a product with an a.e.-nonzero measurable factor. -/
theorem n01a_aemeasurable_of_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hg : AEMeasurable g μ) (hne : ∀ᵐ x ∂μ, g x ≠ 0)
    (hfg : AEMeasurable (fun x => f x * g x) μ) : AEMeasurable f μ := by
  apply (hfg.div hg).congr
  filter_upwards [hne] with x hx
  simp only [Pi.div_apply]
  exact mul_div_cancel_right₀ (f x) hx

/-- The pure graph may be supplied through physical a.e. identification,
so no choice of pointwise representative is added to the inverse statement. -/
theorem n01a_source_aemeasurable_of_pure_graph {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hN : RadialNaturalKernels D)
    {γ M₀ M₁ : ℝ} {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hR : ReferenceGreenReciprocity D γ M₀ M₁)
    (U₀ : RadialUnknown) (F₀ : RadialSource)
    (hPure : ReferenceGraph D γ M₀ M₁ U₀ F₀)
    (hPureEq : U₀.1 =ᵐ[radialPhysicalMeasure D]
      fun p => D.phi p.1 * Radial.cosineMode 2 p.2) :
    ∀ F : RadialSource, SourceMember D γ M₀ F →
      AEMeasurable F.1 (radialPhysicalMeasure D) := by
  intro F hF
  have hprod : Integrable
      (fun p : PolarPoint => F.1 p * U₀.1 p) (radialPhysicalMeasure D) :=
    (hR (G F) U₀ F F₀ (hG.1 F hF) hPure).2.1
  have hm : AEMeasurable
      (fun p : PolarPoint => F.1 p * (D.phi p.1 * Radial.cosineMode 2 p.2))
      (radialPhysicalMeasure D) :=
    hprod.aemeasurable.congr (hPureEq.mono fun p hp => congrArg (fun z => F.1 p * z) hp)
  exact n01a_aemeasurable_of_mul
    (n01a_reference_phi_cosineMode_two_continuous hD).measurable.aemeasurable
    (n01a_reference_phi_cosineMode_two_ne_zero_ae hD hN) hm

/-- Exact-graph specialization used once the explicit reference kernel is in the graph. -/
theorem n01a_source_aemeasurable_of_reference_phi_graph {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hN : RadialNaturalKernels D)
    {γ M₀ M₁ : ℝ} {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hR : ReferenceGreenReciprocity D γ M₀ M₁)
    (hPure : ReferenceGraph D γ M₀ M₁
      ((fun p => D.phi p.1 * Radial.cosineMode 2 p.2), 0)
      ((0 : PolarPoint → ℝ), 1)) :
    ∀ F : RadialSource, SourceMember D γ M₀ F →
      AEMeasurable F.1 (radialPhysicalMeasure D) := by
  exact n01a_source_aemeasurable_of_pure_graph hD hN hG hR _ _ hPure
    (Eventually.of_forall fun _ => rfl)

end ContinuousFlexibility.Statements
