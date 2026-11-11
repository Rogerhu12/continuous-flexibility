import ContinuousFlexibility.Radial.R11bModeDerivativeBounds
import ContinuousFlexibility.Radial.ProfileWeightedL2
import ContinuousFlexibility.Radial.R11bWeightedSynthesis
import ContinuousFlexibility.Radial.R11bNormalReconstruction

/-!
# The first normal estimate for the same reference inverse

A single output-weight increment works for every admitted positive exponent
and every inverse on the original spaces. Ordinary L2 control supplies
summability of the derivative modes; exact finite synthesis preserves the
weighted bound, which passes to the actual normal derivative.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory Real
open scoped BigOperators ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem r11b_firstNormalInverseEstimate {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (M₀ M₁ : ℝ)
    (hmodes : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ H : RadialModePair D →L[ℝ] RadialModePair D, ModeInverseProperties D j H)
    (hmatched : ∃ H : RadialModePair D →L[ℝ] RadialModePair D,
      ∃ Mdata : RadialMatchingData D, ActualMatchedRepresentation D H Mdata) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ γ : ℝ, 0 < γ → |γ| ≤ 1 →
      ∀ G : RadialSource → RadialUnknown,
        ReferenceInverseProperties D γ M₀ M₁ G →
          FirstNormalInverseEstimate D γ M₀ (M₁ + L) G := by
  obtain ⟨L, hL, hest⟩ :=
    r11b_mode_derivative_bounds hD hborder M₀ M₁ hmodes hmatched
  refine ⟨L, hL, ?_⟩
  intro γ hγ habs G hG
  obtain ⟨A, hA, hmode⟩ := hest γ hγ habs G hG
  refine ⟨A + 1, by linarith only [hA], ?_⟩
  intro F d hF hder hd
  obtain ⟨c, hc, hcEq, hs, hb⟩ := hmode F d hF hder hd
  have hpart : RadialPartition D := hD.choose_spec.2.1
  have hab : D.a < D.b := hD.choose_spec.1.2.1
  let S : ℝ := sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (d, 0)
  let E : ℕ → ℝ := fun n => ∑' m,
    exp (-2 * (M₁ + L) * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
      profileScalarCellSquare D (deriv (c n)) m
  obtain ⟨K, hK, hl2⟩ :=
    profile_weighted_derivative_controls_L2 hD γ (M₁ + L) hγ
  have hdLp (n : ℕ) : MemLp (deriv (c n)) 2 (volume.restrict (radialCore D)) :=
    (hl2 (c n) (hc n) (hs n)).1
  have hdBound (n : ℕ) :
      (∫ r in radialCore D, deriv (c n) r ^ 2) ≤ K * E n :=
    (hl2 (c n) (hc n) (hs n)).2
  have hdSq : Summable (fun n => ∫ r in radialCore D, deriv (c n) r ^ 2) := by
    apply summable_of_sum_le (c := K * (A * S))
      (fun n => integral_nonneg (fun r => sq_nonneg _))
    intro J
    calc
      (∑ n ∈ J, ∫ r in radialCore D, deriv (c n) r ^ 2) ≤
          ∑ n ∈ J, K * E n :=
        Finset.sum_le_sum (fun n _ => hdBound n)
      _ = K * ∑ n ∈ J, E n := by rw [Finset.mul_sum]
      _ ≤ K * (A * S) := mul_le_mul_of_nonneg_left (hb J) hK.le
  have hfinite (N : ℕ) :
      RadialCellIntegrable D (r11bEvenPartialSum (fun n => deriv (c n)) N) ∧
      Summable (outputCellSquare D γ (M₁ + L)
        (r11bEvenPartialSum (fun n => deriv (c n)) N)) ∧
      (∑' m, outputCellSquare D γ (M₁ + L)
        (r11bEvenPartialSum (fun n => deriv (c n)) N) m) =
          ∑ n ∈ Finset.range N, E n := by
    have h := r11b_even_finiteSynthesis_output hpart hab.le (Finset.range N)
      (fun n => deriv (c n)) (γ := γ) (M := M₁ + L)
      (fun n _ => hdLp n)
      (fun n _ => by simpa only [profileScalarCellSquare] using hs n)
    change RadialCellIntegrable D (r11bEvenPartialSum (fun n => deriv (c n)) N) ∧
      Summable (outputCellSquare D γ (M₁ + L)
        (r11bEvenPartialSum (fun n => deriv (c n)) N)) ∧
      (∑' m, outputCellSquare D γ (M₁ + L)
        (r11bEvenPartialSum (fun n => deriv (c n)) N) m) =
          ∑ n ∈ Finset.range N, E n at h
    exact h
  have hcell (N : ℕ) : Summable (outputCellSquare D γ (M₁ + L)
      (r11bEvenPartialSum (fun n => deriv (c n)) N)) :=
    (hfinite N).2.1
  have hbound (N : ℕ) :
      (∑' m, outputCellSquare D γ (M₁ + L)
        (r11bEvenPartialSum (fun n => deriv (c n)) N) m) ≤ A * S := by
    rw [(hfinite N).2.2]
    exact hb (Finset.range N)
  have hgraph := hG.1 F hF
  have hULp : MemLp (G F).1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ hgraph.1
  obtain ⟨aL, hreal⟩ := hgraph.1
  have hup : ∀ r, Function.Periodic (fun θ => (G F).1 (r, θ)) Real.pi := by
    intro r θ
    simpa using hreal.2.2.1 (r, θ)
  have hue : ∀ r, Function.Even (fun θ => (G F).1 (r, θ)) :=
    fun r θ => hreal.2.2.2 r θ
  obtain ⟨ur, hnormal, houtput, hout⟩ :=
    r11b_normal_reconstruction_of_mode_bounds hpart hab γ (M₁ + L)
      hULp hup hue c hc hcEq hdLp hdSq hcell hbound
  have hsrcNonneg (X : RadialSource) : 0 ≤ sourceNormSquare D γ M₀ X := by
    unfold sourceNormSquare
    refine add_nonneg (sq_nonneg _) (tsum_nonneg fun m => ?_)
    unfold sourceCellSquare
    exact mul_nonneg (exp_pos _).le (r11b_referenceCellSquare_nonneg hab.le m X.1)
  have hS : 0 ≤ S := add_nonneg (hsrcNonneg F) (hsrcNonneg (d, 0))
  have hAA : A ≤ (A + 1) ^ 2 := by nlinarith only [sq_nonneg A, hA]
  exact ⟨ur, hnormal, houtput, hout.trans (mul_le_mul_of_nonneg_right hAA hS)⟩

end

end ContinuousFlexibility.Radial
