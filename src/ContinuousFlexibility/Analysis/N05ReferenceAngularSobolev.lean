module

public import ContinuousFlexibility.Analysis.N05ReferenceAngularInverseWeak
public import ContinuousFlexibility.Analysis.N05ReferenceAngularSourceSobolev

/-!
# High angular Sobolev preservation by the original reference inverse

All assumptions now concern the physical source and one of its actual
weak angular derivatives. Fourier summability, the output jet, its
weighted membership and its weak identity are conclusions. The same
constant and material exponents work for every angular order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open MeasureTheory
open ContinuousFlexibility.Statements

theorem n05_referenceInverse_highAngularSobolev_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M₀ F →
      ∀ (b : ℕ) (fder : PolarPoint → ℝ),
      SourceDerivativeMember D γ M₀ fder →
      n05_weakReferenceAngularJet D F.1 fder b →
      ∃ uder : PolarPoint → ℝ,
        n05_weakReferenceAngularJet D (n05_referenceHighPart (G F).1) uder b ∧
        MemLp uder 2 (referenceWeightedMeasure D γ (-M₁)) ∧
        outputNormSquare D γ M₁ 0 (uder, 0) ≤
          C ^ 2 * sourceNormSquare D γ M₀ (fder, 0) ∧
        Function.Periodic uder (0, Real.pi) := by
  obtain ⟨C, hC, hbound⟩ := n05_referenceInverse_highWeakAngularJet_bound hD hborder hγ hG
  refine ⟨C, hC, fun F hF b fder hfd hweak => ?_⟩
  obtain ⟨hs, hb⟩ := n05_referenceHighWeakJet_source_summable_bound hD hγ hF hfd hweak
  obtain ⟨uder, huweak, huLp, hub, huperiodic⟩ := hbound F hF b hs
  exact ⟨uder, huweak, huLp,
    hub.trans (mul_le_mul_of_nonneg_left hb (sq_nonneg C)), huperiodic⟩

end ContinuousFlexibility.Radial
