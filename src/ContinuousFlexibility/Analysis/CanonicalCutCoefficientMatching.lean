module

public import ContinuousFlexibility.Analysis.CanonicalGluedAiryIntegral
public import ContinuousFlexibility.Analysis.NegativeCanonicalClosedEffective

/-!
# The two actual effective fields agree on the cut

The Airy quadratic form is invariant under reversal of its radial axis.
The true cut transmission law supplies exactly that reversal of the
forward derivative and equality of the physical heights. Consequently
the two forward-only effective physical coefficient fields have the same
values on the whole cut. Stored coefficient values on the cut are not
used in this identity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Invariance of the actual adjugate density under a reflected radial
derivative. This is algebraic and includes the absolute Jacobian factor. -/
theorem adjugateAiry_coefficients_eq_of_reflected_derivative
    {F₀ F₁ : PolarPoint → PolarPoint} {h₀ h₁ : PolarPoint → ℝ} {p : PolarPoint}
    (hξ : (F₁ p).1 = (F₀ p).1) (hh : h₁ p = h₀ p)
    (hD : ∀ v : PolarPoint, fderiv ℝ F₁ p v =
      (-(fderiv ℝ F₀ p v).1, (fderiv ℝ F₀ p v).2)) :
    (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F₁ h₁).a p =
        (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F₀ h₀).a p ∧
      (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F₁ h₁).b p =
        (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F₀ h₀).b p ∧
      (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F₁ h₁).c p =
        (adjugateCoordinatePrincipalCoefficients canonicalAiryPrincipalCoefficients F₀ h₀).c p := by
  have hJ : planeJacobian F₁ p = -planeJacobian F₀ p := by
    dsimp only [planeJacobian]
    rw [hD (1, 0), hD (0, 1)]
    ring
  simp only [adjugateCoordinatePrincipalCoefficients, coefficientQuadratic,
    canonicalAiryPrincipalCoefficients, hξ, hh, hJ, abs_neg, hD (1, 0), hD (0, 1)]
  constructor
  · ring
  · constructor <;> ring

/-- Actual PartA/PartB force equality of the two closed effective fields
at every point of their common current cut. -/
theorem canonicalCut_closedCoefficients_match
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    let p := canonicalCutPoint S K z m θ
    (negativeCanonicalClosedCoefficients S K z (K.cutPair m).2).a p =
        (negativeCanonicalClosedCoefficients S K z (K.cutPair m).1).a p ∧
      (negativeCanonicalClosedCoefficients S K z (K.cutPair m).2).b p =
        (negativeCanonicalClosedCoefficients S K z (K.cutPair m).1).b p ∧
      (negativeCanonicalClosedCoefficients S K z (K.cutPair m).2).c p =
        (negativeCanonicalClosedCoefficients S K z (K.cutPair m).1).c p := by
  have hvalues₀ := (canonicalCut_closed_and_chart hA hB hz hs m false θ).2
  have hvalues₁ := (canonicalCut_closed_and_chart hA hB hz hs m true θ).2
  change K.chart z (K.cutPair m).1 (canonicalCutPoint S K z m θ) =
    (K.cutRadius m, θ) at hvalues₀
  change K.chart z (K.cutPair m).2 (canonicalCutPoint S K z m θ) =
    (K.cutRadius m, θ) at hvalues₁
  have hξ : (K.chart z (K.cutPair m).2 (canonicalCutPoint S K z m θ)).1 =
      (K.chart z (K.cutPair m).1 (canonicalCutPoint S K z m θ)).1 := by
    rw [hvalues₀, hvalues₁]
  have hjets := canonicalCut_height_and_firstJets hA hB hz hs m θ
  exact adjugateAiry_coefficients_eq_of_reflected_derivative hξ hjets.1 hjets.2.2.2

end ContinuousFlexibility.Analysis
