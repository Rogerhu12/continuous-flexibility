import ContinuousFlexibility.Analysis.N01aReferenceNormalization

/-!
# The actual inverse at a pure normalization source

The source consists of zero physical forcing and a scalar normalization row.
Applying the existing reference inverse above the working exponent produces
an actual distributional solution and its weighted first normal derivative.
No identification with the reference eigenfunction is assumed here.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- Every pure scalar row is an admissible physical source. -/
theorem sourceMember_pure_row (D : ReferenceData) (γ M η : ℝ) :
    SourceMember D γ M ((0 : PolarPoint → ℝ), η) := by
  have hz : sourceCellSquare D γ M (0 : PolarPoint → ℝ) = fun _ => 0 := by
    funext m
    simp [sourceCellSquare, referenceCellSquare, radialAngularMean]
  refine ⟨RadialCellIntegrable.zero D, ?_⟩
  simp [hz, radialAngularMean, Function.Periodic]

/-- The zero angular derivative belongs to the derivative source space. -/
theorem n01a_sourceDerivativeMember_zero (D : ReferenceData) (γ M : ℝ) :
    SourceDerivativeMember D γ M (0 : PolarPoint → ℝ) :=
  ⟨(sourceMember_pure_row D γ M 0).1, (sourceMember_pure_row D γ M 0).2.1⟩

theorem sourceNormSquare_pure_row (D : ReferenceData) (γ M η : ℝ) :
    sourceNormSquare D γ M ((0 : PolarPoint → ℝ), η) = η ^ 2 := by
  simp [sourceNormSquare, sourceCellSquare, referenceCellSquare, radialAngularMean]

theorem weakAngularDerivative_zero (D : ReferenceData) :
    WeakAngularDerivative D (0 : PolarPoint → ℝ) 0 := by
  simp [WeakAngularDerivative, radialAngularMean]

/-- The inverse supplies the same normalized actual field at all three
exponents.  Its scalar component is not set to zero by this extraction. -/
theorem exists_reference_pure_row_output {D : ReferenceData} (hD : IsRadialReference D) :
    ∃ ε M₀ M₁ : ℝ, ∃ U : RadialUnknown,
      0 < ε ∧ ε < 1 / 4 ∧
      (∀ γ : ℝ, γ = referenceBeta - ε ∨ γ = referenceBeta ∨
          γ = referenceBeta + ε →
        ReferenceGraph D γ M₀ M₁ U ((0 : PolarPoint → ℝ), 1)) ∧
      referenceRow D U.1 = 1 ∧
      ∃ ur : PolarPoint → ℝ, WeakNormalDerivative D U.1 ur ∧
        OutputRealization D (referenceBeta + ε) M₁ 0 (ur, 0) := by
  obtain ⟨ε, M₀, M₁, hε, hεsmall, G, hG⟩ := hD.2.2.2.2
  let F : RadialSource := ((0 : PolarPoint → ℝ), 1)
  have hF (γ : ℝ) : SourceMember D γ M₀ F :=
    sourceMember_pure_row D γ M₀ 1
  have hgraph (γ : ℝ)
      (hγ : γ = referenceBeta - ε ∨ γ = referenceBeta ∨ γ = referenceBeta + ε) :
      ReferenceGraph D γ M₀ M₁ (G F) F := (hG γ hγ).1.1 F (hF γ)
  have hplus := hG (referenceBeta + ε) (Or.inr (Or.inr rfl))
  obtain ⟨C, hC, hnormal⟩ := hplus.2.2.2.2
  obtain ⟨ur, hur, hreal, hbound⟩ :=
    hnormal F 0 (hF _) (weakAngularDerivative_zero D)
      (n01a_sourceDerivativeMember_zero D (referenceBeta + ε) M₀)
  refine ⟨ε, M₀, M₁, G F, hε, hεsmall, hgraph, ?_, ur, hur, hreal⟩
  exact (hgraph referenceBeta (Or.inr (Or.inl rfl))).2.2.1

end ContinuousFlexibility.Statements
