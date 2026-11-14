module

public import ContinuousFlexibility.Radial.R11bAngularFrequencySource
public import ContinuousFlexibility.Radial.R11bWeightedModeSquares
public import ContinuousFlexibility.Radial.R11bModeScaling
public import ContinuousFlexibility.Radial.R11bRemainderModes

/-!
# Finite angular frequency bounds for the actual reference inverse

Only selected coefficients of the true inverse are compared. Modal
uniqueness identifies their scaling, including the critical scalar row;
weighted Bessel then gives a constant independent of the finite selection.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem r11b_inverse_angularFrequencySource_mode {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hmodes : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ H : RadialModePair D →L[ℝ] RadialModePair D, ModeInverseProperties D j H)
    {F : RadialSource} {d : PolarPoint → ℝ}
    (hF : SourceMember D γ M₀ F) (hder : WeakAngularDerivative D F.1 d)
    (hd : SourceDerivativeMember D γ M₀ d)
    (J : Finset ℕ) (hJ : ∀ n ∈ J, 0 < n) (n : ℕ) (hn : n ∈ J) :
    referenceMode (G (r11bAngularFrequencySource J F d)).1 (2 * n)
      =ᵐ[volume.restrict (radialCore D)]
        (fun r => ((2 * n : ℕ) : ℝ) * referenceMode (G F).1 (2 * n) r) := by
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hpos : 0 < n := hJ n hn
  obtain ⟨H, hH⟩ := hmodes (2 * n) (by omega) ⟨n, by omega⟩
  have hK : SourceMember D γ M₀ (r11bAngularFrequencySource J F d) :=
    (r11b_angularFrequencySource_member_bound hab J hJ F hd).1
  exact (r11b_graph_mode_scaling hD hborder hγ hγ (hG.1 F hF)
    (hG.1 (r11bAngularFrequencySource J F d) hK)
    (Nat.mul_pos (by decide) hpos) hH ((2 * n : ℕ) : ℝ)
    (r11b_angularFrequencySource_referenceMode hD hγ hF hder hd J hJ n hn)
    (r11b_angularFrequencySource_row J F d n hn)).1

theorem r11b_reference_inverse_finite_frequency_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hmodes : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ H : RadialModePair D →L[ℝ] RadialModePair D, ModeInverseProperties D j H) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : RadialSource) (d : PolarPoint → ℝ),
      SourceMember D γ M₀ F → WeakAngularDerivative D F.1 d →
      SourceDerivativeMember D γ M₀ d → ∀ J : Finset ℕ, (∀ n ∈ J, 0 < n) →
      (∑ n ∈ J, ((2 * n : ℕ) : ℝ) ^ 2 *
        (∑' m, exp (-2 * M₁ * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          ∫ r, (D.localizer m r * referenceMode (G F).1 (2 * n) r) ^ 2
            ∂volume.restrict (radialCore D))) ≤
        C ^ 2 * (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (d, 0)) := by
  obtain ⟨C, hC, hbound⟩ := hG.2.2.2
  refine ⟨2 * C, by positivity, ?_⟩
  intro F d hF hder hd J hJ
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  let K : RadialSource := r11bAngularFrequencySource J F d
  obtain ⟨hK, hKbound⟩ := r11b_angularFrequencySource_member_bound hab J hJ F hd
  obtain ⟨aV, hV, hVbound⟩ := hbound K hK
  have hVlp : MemLp (G K).1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ ⟨aV, hV⟩
  have hscale (n : ℕ) (hn : n ∈ J) :
      r11bWeightedModeSquare D γ M₁ (outputRemainder D aV (G K)) (2 * n) =
        ((2 * n : ℕ) : ℝ) ^ 2 * r11bWeightedModeSquare D γ M₁ (G F).1 (2 * n) := by
    have hpos : 0 < 2 * n := Nat.mul_pos (by decide) (hJ n hn)
    have hmode := r11b_inverse_angularFrequencySource_mode
      hD hborder hγ hG hmodes hF hder hd J hJ n hn
    have hrem := r11b_referenceMode_outputRemainder_ae hVlp aV (2 * n) hpos
    exact r11b_weightedModeSquare_scale_ae D γ M₁ (hrem.trans hmode)
  change (∑ n ∈ J, ((2 * n : ℕ) : ℝ) ^ 2 *
      r11bWeightedModeSquare D γ M₁ (G F).1 (2 * n)) ≤ _
  calc
    _ = ∑ n ∈ J, r11bWeightedModeSquare D γ M₁ (outputRemainder D aV (G K)) (2 * n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (hscale n hn).symm
    _ ≤ outputNormSquare D γ M₁ aV (G K) := r11b_output_even_mode_squares hab J hJ hV
    _ ≤ C ^ 2 * sourceNormSquare D γ M₀ K := hVbound
    _ ≤ C ^ 2 * (4 * (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (d, 0))) :=
      mul_le_mul_of_nonneg_left hKbound (sq_nonneg C)
    _ = (2 * C) ^ 2 *
        (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (d, 0)) := by ring

end ContinuousFlexibility.Radial
