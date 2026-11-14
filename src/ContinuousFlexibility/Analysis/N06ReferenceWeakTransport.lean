module

public import ContinuousFlexibility.Analysis.N06ReferenceTestOperator
public import ContinuousFlexibility.Analysis.N06ReferenceRemainderEquation
public import ContinuousFlexibility.Analysis.N06CanonicalWeakTransport

/-!
# The actual reference graph in positive canonical coordinates

The physical equation and both integrable pairings come from the original
reference graph. The same compact test is transported into that equation.
Its differential expression is the actual corrected reference operator,
and its canonical height is the original test. Consequently no additional
weak PDE assumption is needed to obtain the canonical equation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

theorem n06_referenceGraph_canonicalWeakPairing
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base m : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hb : RadialTrueBorder D)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε)
    (href : referenceStateConditions D S C)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) (hm : K.positive m = true)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {γ M₀ M₁ μ : ℝ} {η g : PolarPoint → ℝ}
    (hgraph : ReferenceGraph D γ M₀ M₁ (η, μ) (g, 0))
    (aL : ℝ) (W : CanonicalL2 S K m)
    (hW : (W : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K (C.referenceState, 0) m (n06ReferenceRemainder χ η aL))
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, W p * canonicalOperator S K L (C.referenceState, 0) m φ p
      ∂canonicalMeasure S K m) =
      ∫ p, (-canonicalSource S K (C.referenceState, 0) m
        (n06ReferenceRemainderForcing D χ g μ aL) p) * φ p
          ∂canonicalMeasure S K m := by
  let Φ : PolarPoint → ℝ := n06CanonicalTestPullback S K (C.referenceState, 0) m φ
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hΦ : RadialTest D Φ := n06CanonicalTestPullback_radialTest hA hz hs hφ
  have hΦperiod : Function.Periodic Φ (0, Real.pi) :=
    n06CanonicalTestPullback_periodic hA hz hs hφ
  have hop : divergenceOperator (L.coefficients (C.referenceState, 0)) Φ =
      n06ReferenceTestOperator D Φ :=
    n06CanonicalTestPullback_reference_operator hN03 hA hgeom href hz hs hm hφ
  obtain ⟨hIL, hIR, heq⟩ := n06_referenceRemainder_equation hD hb hχ hgraph aL hΦ
  have hηperiod : Function.Periodic η (0, Real.pi) := hgraph.1.choose_spec.2.2.1
  have hgperiod : Function.Periodic g (0, Real.pi) := hgraph.2.1.2.2.1
  have hremperiod := n06_referenceRemainder_periodic (χ := χ) hηperiod aL
  have hforceperiod := n06_referenceRemainderForcing_periodic
    hgeom.2.2.1.1 hχ hgperiod μ aL
  have hopperiod := n06_referenceTestOperator_periodic hgeom.2.2.1.1 hΦ.1 hΦperiod
  have hhalf : radialCore D ×ˢ Ioc (0 : ℝ) Real.pi ⊆
      radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans (by linarith only [Real.pi_pos])⟩
  have hILhalf : IntegrableOn (fun p => n06ReferenceRemainder χ η aL p *
      n06ReferenceTestOperator D Φ p) (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) volume :=
    (show IntegrableOn (fun p => n06ReferenceRemainder χ η aL p *
      n06ReferenceTestOperator D Φ p)
        (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume from hIL).mono_set hhalf
  have hIRhalf : IntegrableOn (fun p => n06ReferenceRemainderForcing D χ g μ aL p * Φ p)
      (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) volume :=
    (show IntegrableOn (fun p => n06ReferenceRemainderForcing D χ g μ aL p * Φ p)
      (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume from hIR).mono_set hhalf
  have hcanonical := n06_canonicalWeakPairing_of_physical hA hgeom.2.1.le hz hs hφ
    (n06ReferenceRemainder χ η aL) (n06ReferenceRemainderForcing D χ g μ aL) W hW
    (by rw [hop]; exact hremperiod.mul hopperiod)
    (by rw [hop]; exact hILhalf)
    (hforceperiod.mul hΦperiod) hIRhalf (by rw [hop]; exact heq)
  simpa only [hm, ↓reduceIte, neg_one_mul] using hcanonical

end ContinuousFlexibility.Analysis
