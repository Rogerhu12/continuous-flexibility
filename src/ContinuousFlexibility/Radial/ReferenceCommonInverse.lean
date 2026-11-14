module

public import ContinuousFlexibility.Radial.ReferenceExponentComparison

/-!
# One inverse for all reference exponents on a fixed geometry

Uniqueness in the lowest exponent identifies the inverse representatives
obtained in the stronger domains. The local L² identity transports their
norms and output realizations. Thus separate existence results at the
three exponents can be assembled without making another geometric choice.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter

theorem outputRemainder_congr_ae {D : ReferenceData} {aL : ℝ}
    {U V : RadialUnknown} (hUV : RadialRepresentativeEq D U V) :
    outputRemainder D aL U =ᵐ[radialPhysicalMeasure D] outputRemainder D aL V := by
  filter_upwards [hUV.2] with x hx
  exact congrArg (fun t : ℝ => t - aL * D.chiLeft x.1) hx

/-- The periodic and even representative is retained explicitly; these are
pointwise conditions, whereas cell membership and norms are a.e. conditions. -/
theorem OutputRealization.congr_ae {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M aL : ℝ} {U V : RadialUnknown}
    (hU : OutputRealization D γ M aL U) (hUV : RadialRepresentativeEq D U V)
    (hper : Function.Periodic V.1 (0, Real.pi))
    (heven : ∀ r θ, V.1 (r, -θ) = V.1 (r, θ)) :
    OutputRealization D γ M aL V := by
  have hr := outputRemainder_congr_ae (aL := aL) hUV
  have hsq : outputCellSquare D γ M (outputRemainder D aL U) =
      outputCellSquare D γ M (outputRemainder D aL V) := by
    funext m
    unfold outputCellSquare
    rw [referenceCellSquare_congr_ae hab m hU.1 hr]
  refine ⟨hU.1.congr_ae hr, ?_, hper, heven⟩
  rw [← hsq]
  exact hU.2.1

theorem outputNormSquare_congr_ae {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M aL : ℝ} {U V : RadialUnknown}
    (hU : OutputRealization D γ M aL U) (hUV : RadialRepresentativeEq D U V) :
    outputNormSquare D γ M aL U = outputNormSquare D γ M aL V := by
  unfold outputNormSquare
  rw [hUV.1]
  congr 1
  apply tsum_congr
  intro m
  unfold outputCellSquare
  rw [referenceCellSquare_congr_ae hab m hU.1
    (outputRemainder_congr_ae (aL := aL) hUV)]

/-- An inverse at a lower exponent is also the inverse at a higher exponent
whenever an inverse at that higher exponent exists with the same two
coefficient powers. No enlargement of the output coefficient loss is used. -/
theorem ReferenceInverseProperties.of_lower_exponent
    {D : ReferenceData} (hab : D.a ≤ D.b) {γlo γ M₀ M₁ : ℝ}
    {G H : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γlo M₀ M₁ G)
    (hH : ReferenceInverseProperties D γ M₀ M₁ H) (hγ : γlo ≤ γ) :
    ReferenceInverseProperties D γ M₀ M₁ G := by
  have hsource : ∀ F, SourceMember D γ M₀ F → SourceMember D γlo M₀ F :=
    fun F hF => hF.mono_weights hab hγ le_rfl
  have hsame : ∀ F, SourceMember D γ M₀ F →
      RadialRepresentativeEq D (G F) (H F) := by
    intro F hF
    exact hG.2.1 (H F) F ((hH.1 F hF).lower_exponent hab hγ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F hF
    have hg := hG.1 F (hsource F hF)
    have hh := hH.1 F hF
    obtain ⟨a, ha⟩ := hg.1
    obtain ⟨b, hb⟩ := hh.1
    have hout := hb.congr_ae hab (hsame F hF).symm ha.2.2.1 ha.2.2.2
    exact ⟨⟨b, hout⟩, hF, hg.2.2⟩
  · intro U F hUF
    exact hG.2.1 U F (hUF.lower_exponent hab hγ)
  · intro F K hF hK c d
    exact hG.2.2.1 F K (hsource F hF) (hsource K hK) c d
  · obtain ⟨C, hC, hbound⟩ := hH.2.2.2
    refine ⟨C, hC, ?_⟩
    intro F hF
    obtain ⟨a, ha⟩ := (hG.1 F (hsource F hF)).1
    obtain ⟨b, hb, hbnd⟩ := hbound F hF
    refine ⟨b, hb.congr_ae hab (hsame F hF).symm ha.2.2.1 ha.2.2.2, ?_⟩
    rw [← outputNormSquare_congr_ae hab hb (hsame F hF).symm]
    exact hbnd

/-- A least exponent selects one actual function on the common source type. -/
theorem exists_common_reference_inverse {D : ReferenceData} (hab : D.a ≤ D.b)
    (J : Set ℝ) {γlo M₀ M₁ : ℝ} (hlo : γlo ∈ J)
    (hle : ∀ γ ∈ J, γlo ≤ γ)
    (hbounded : ∀ γ ∈ J, BoundedReferenceInverse D γ M₀ M₁) :
    ∃ G : RadialSource → RadialUnknown,
      ∀ γ ∈ J, ReferenceInverseProperties D γ M₀ M₁ G := by
  obtain ⟨G, hG⟩ := hbounded γlo hlo
  refine ⟨G, ?_⟩
  intro γ hγ
  obtain ⟨H, hH⟩ := hbounded γ hγ
  exact hG.of_lower_exponent hab hH (hle γ hγ)

/-- The three frozen exponents use the inverse selected at the lowest one. -/
theorem exists_common_three_reference_inverse {D : ReferenceData} (hab : D.a ≤ D.b)
    {ε M₀ M₁ : ℝ} (hε : 0 ≤ ε)
    (hbounded : ∀ γ : ℝ,
      γ = referenceBeta - ε ∨ γ = referenceBeta ∨ γ = referenceBeta + ε →
        BoundedReferenceInverse D γ M₀ M₁) :
    ∃ G : RadialSource → RadialUnknown, ∀ γ : ℝ,
      γ = referenceBeta - ε ∨ γ = referenceBeta ∨ γ = referenceBeta + ε →
        ReferenceInverseProperties D γ M₀ M₁ G := by
  apply exists_common_reference_inverse hab
    {γ | γ = referenceBeta - ε ∨ γ = referenceBeta ∨ γ = referenceBeta + ε}
    (γlo := referenceBeta - ε)
  · exact Or.inl rfl
  · intro γ hγ
    rcases hγ with rfl | rfl | rfl <;> linarith
  · exact hbounded

end ContinuousFlexibility.Statements
