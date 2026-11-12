import ContinuousFlexibility.Radial.R11bFirstNormal
import ContinuousFlexibility.Radial.R11bMaximumGraphUniqueness
import ContinuousFlexibility.Radial.ReferenceNaturalKernel
import ContinuousFlexibility.Radial.ReferenceSourceDensity
import ContinuousFlexibility.Radial.ReferenceSmoothInverse
import ContinuousFlexibility.Radial.ReferenceSmoothCore
import ContinuousFlexibility.Radial.ReferenceSmoothGraphGreen

/-!
# Completing a radial reference on the same selected data

The modal and weighted inverse construction may retain geometric certificates
about its actual profile and cells. This interface performs the first-normal
and graph-closure steps without repackaging the reference data existentially.
Its conclusion concerns the original `D`, so every such certificate remains
available for the subsequent nonlinear construction.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

/-- The R11b and R12 completion steps preserve the actual reference data.
Only the output material exponent is enlarged; the inverse itself is fixed. -/
theorem n05_isRadialReference_of_fixed_mode_inverse {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hgeometry : RadialConstructionGeometry D)
    (hmodes : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ H : RadialModePair D →L[ℝ] RadialModePair D, ModeInverseProperties D j H)
    (hmatched : ∃ H : RadialModePair D →L[ℝ] RadialModePair D,
      ∃ Mdata : RadialMatchingData D, ActualMatchedRepresentation D H Mdata)
    {ε M₀ M₁ : ℝ} (hε : 0 < ε) (hεlt : ε < 1 / 4)
    {G : RadialSource → RadialUnknown}
    (hG : ∀ γ : ℝ,
      γ = referenceBeta - ε ∨ γ = referenceBeta ∨ γ = referenceBeta + ε →
        ReferenceInverseProperties D γ M₀ M₁ G) :
    IsRadialReference D := by
  obtain ⟨L, hL, hnormal⟩ :=
    r11b_firstNormalInverseEstimate hD hborder M₀ M₁ hmodes hmatched
  have hnatural : RadialNaturalKernels D :=
    radialNaturalKernels_of_modeInverses hD hborder hgeometry.1 hmodes
  refine ⟨hD, hnatural, hgeometry.2, hborder,
    ε, M₀, M₁ + L, hε, hεlt, G, ?_⟩
  intro γ hγ
  have hγpos : 0 < γ := by
    rcases hγ with rfl | rfl | rfl <;>
      dsimp only [referenceBeta] <;> linarith only [hε, hεlt]
  have hγabs : |γ| ≤ 1 := by
    rw [abs_of_pos hγpos]
    rcases hγ with rfl | rfl | rfl <;>
      dsimp only [referenceBeta] <;> linarith only [hε, hεlt]
  have hinverse : ReferenceInverseProperties D γ M₀ (M₁ + L) G :=
    r11b_referenceInverse_enlarge hD hborder hmodes hγpos le_rfl
      (le_add_of_nonneg_right hL) (hG γ hγ)
  have hfirst : FirstNormalInverseEstimate D γ M₀ (M₁ + L) G :=
    hnormal γ hγpos hγabs G (hG γ hγ)
  have hcore : ReferenceSmoothCoreClosure D γ M₀ (M₁ + L) := by
    apply referenceSmoothCoreClosure_of_dense_inverse_core hD hinverse
      (ReferenceSmoothFiniteSource D)
    · intro F hF
      obtain ⟨Fₙ, hsmooth, _, hmember, hconv⟩ :=
        hF.exists_smoothFinite_approximation hD
      exact ⟨Fₙ, fun n => ⟨hmember n, hsmooth n⟩, hconv⟩
    · intro F hF hfinite
      exact reference_smooth_inverse_image hD hborder hgeometry.1
        (hmodes 2 le_rfl (by decide)) hinverse hfirst hγpos hF hfinite
  exact ⟨hinverse, referenceGraphClosed_of_positive hD hborder hγpos, hcore,
    referenceGreenReciprocity_of_smooth_core hD hborder hγpos hcore, hfirst⟩

end ContinuousFlexibility.Radial
