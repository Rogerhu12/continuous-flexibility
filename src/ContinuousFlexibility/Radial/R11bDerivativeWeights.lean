import ContinuousFlexibility.Radial.R11bWeightMonotonicity

/-!
# Weight changes for the source angular derivative

The derivative is required to have a finite source-weight norm, without the
evenness and compatibility conditions imposed on the original source.
Both coefficient monotonicity and strict attenuation embeddings preserve the
same derivative representative. The first normal estimate consequently
transports to stronger source and weaker output coefficient weights.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real MeasureTheory
open ContinuousFlexibility.Statements

/-- Increasing the coefficient exponent strengthens the derivative norm. -/
theorem r11b_sourceDerivative_coefficient_mono {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ Mlo Mhi : ℝ} (hM : Mlo ≤ Mhi) {fθ : PolarPoint → ℝ}
    (hfθ : SourceDerivativeMember D γ Mhi fθ) :
    SourceDerivativeMember D γ Mlo fθ ∧
      sourceNormSquare D γ Mlo (fθ, 0) ≤ sourceNormSquare D γ Mhi (fθ, 0) := by
  have hmono := r11b_sourceCellSquare_mono hab (γ := γ) hM fθ
  have hs : Summable (sourceCellSquare D γ Mlo fθ) :=
    Summable.of_nonneg_of_le
      (r11b_sourceCellSquare_nonneg hab γ Mlo fθ) hmono hfθ.2
  refine ⟨⟨hfθ.1, hs⟩, ?_⟩
  simpa [sourceNormSquare] using (Summable.tsum_le_tsum hmono hs hfθ.2)

theorem r11b_sourceDerivativeMember_of_le {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ Mlo Mhi : ℝ} (hM : Mlo ≤ Mhi) {fθ : PolarPoint → ℝ}
    (hfθ : SourceDerivativeMember D γ Mhi fθ) : SourceDerivativeMember D γ Mlo fθ :=
  (r11b_sourceDerivative_coefficient_mono hab hM hfθ).1

theorem r11b_sourceDerivativeNormSquare_mono {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ Mlo Mhi : ℝ} (hM : Mlo ≤ Mhi) {fθ : PolarPoint → ℝ}
    (hfθ : SourceDerivativeMember D γ Mhi fθ) :
    sourceNormSquare D γ Mlo (fθ, 0) ≤ sourceNormSquare D γ Mhi (fθ, 0) :=
  (r11b_sourceDerivative_coefficient_mono hab hM hfθ).2

/-- A strict attenuation margin absorbs any fixed change of coefficient
exponent for the angular derivative, with one constant for all inputs. -/
theorem r11b_sourceDerivative_embedding {D : ReferenceData} (hab : D.a ≤ D.b)
    (Mlo Mhi γlo γhi : ℝ) (hγ : γlo < γhi) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ fθ : PolarPoint → ℝ,
      SourceDerivativeMember D γhi Mhi fθ →
        SourceDerivativeMember D γlo Mlo fθ ∧
          sourceNormSquare D γlo Mlo (fθ, 0) ≤
            K * sourceNormSquare D γhi Mhi (fθ, 0) := by
  obtain ⟨K, hK, hweight⟩ := r11b_exp_weight_le (2 * Mlo) (2 * Mhi) γlo γhi hγ
  refine ⟨K, hK, fun fθ hfθ => ?_⟩
  obtain ⟨hs, hnorm⟩ := r11b_weighted_tsum_le
    (fun m => exp (2 * Mlo * radialQ (D.cellIndex m) + 2 * γlo * radialS (D.cellIndex m)))
    (fun m => exp (2 * Mhi * radialQ (D.cellIndex m) + 2 * γhi * radialS (D.cellIndex m)))
    (fun m => referenceCellSquare D m fθ)
    (fun _ => (exp_pos _).le) (fun m => r11b_referenceCellSquare_nonneg hab m fθ)
    (fun m => hweight (D.cellIndex m)) hfθ.2
  refine ⟨⟨hfθ.1, hs⟩, ?_⟩
  change (∑' m, sourceCellSquare D γlo Mlo fθ m) ≤
    K * ∑' m, sourceCellSquare D γhi Mhi fθ m at hnorm
  simpa [sourceNormSquare] using hnorm

theorem r11b_sourceDerivativeMember_of_lt {D : ReferenceData} (hab : D.a ≤ D.b)
    {Mlo Mhi γlo γhi : ℝ} (hγ : γlo < γhi) {fθ : PolarPoint → ℝ}
    (hfθ : SourceDerivativeMember D γhi Mhi fθ) :
    SourceDerivativeMember D γlo Mlo fθ := by
  obtain ⟨_, _, h⟩ := r11b_sourceDerivative_embedding hab Mlo Mhi γlo γhi hγ
  exact (h fθ hfθ).1

/-- The same weak normal derivative and the same bound constant work after
increasing both coefficient exponents. No graph uniqueness is used here. -/
theorem r11b_firstNormalInverseEstimate_mono {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M₀ M₀' M₁ M₁' : ℝ} (h₀ : M₀ ≤ M₀') (h₁ : M₁ ≤ M₁')
    {G : RadialSource → RadialUnknown}
    (hG : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    FirstNormalInverseEstimate D γ M₀' M₁' G := by
  obtain ⟨C, hC, hestimate⟩ := hG
  refine ⟨C, hC, fun F fθ hF hderiv hfθ => ?_⟩
  obtain ⟨ur, hur, hU, hnorm⟩ := hestimate F fθ
    (r11b_sourceMember_of_le hab h₀ hF) hderiv
    (r11b_sourceDerivativeMember_of_le hab h₀ hfθ)
  refine ⟨ur, hur, r11b_outputRealization_of_le hab h₁ hU, ?_⟩
  calc outputNormSquare D γ M₁' 0 (ur, 0)
      ≤ outputNormSquare D γ M₁ 0 (ur, 0) :=
        r11b_outputNormSquare_antitone hab h₁ hU
    _ ≤ C ^ 2 * (sourceNormSquare D γ M₀ F +
        sourceNormSquare D γ M₀ (fθ, 0)) := hnorm
    _ ≤ C ^ 2 * (sourceNormSquare D γ M₀' F +
        sourceNormSquare D γ M₀' (fθ, 0)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (r11b_sourceNormSquare_mono hab h₀ hF)
          (r11b_sourceDerivativeNormSquare_mono hab h₀ hfθ)) (sq_nonneg C)

end ContinuousFlexibility.Radial
