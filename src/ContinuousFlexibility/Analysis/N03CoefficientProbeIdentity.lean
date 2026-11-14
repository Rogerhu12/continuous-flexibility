module

public import ContinuousFlexibility.Analysis.EffectiveCoefficientProbeIdentity

/-!
# The actual N03 error determines two effective coefficient numerators

The four height elements are the genuine compact radial even periodic
probes. The N03 clause is applied to their decoded fields. The effective
operator is used only where its actual action equals the stored corrected
operator. In particular this statement does not assert a common physical
domain for a family of effective fields.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def decodedCorrectionError (S : PhysicalSpacesData) (L : ReturnCorrectionData S)
    (z : AnnularState S × ℝ) (r : CircleSpace S) (η : HeightPair S) : PolarPoint → ℝ :=
  (S.height (3 / 4 : ℝ)).decode ((L.error z r η).val)

/-- No smoothness of `L.coefficients z` is assumed. The actual N03 action
on four encoded tests and a true smooth effective field suffice. -/
theorem n03Error_coefficientProbe_identities
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hN03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hone : χ =ᶠ[𝓝 p.1] (fun _ : ℝ => 1))
    {ηr ηc ηrc ηcc : HeightPair S}
    (hηr : heightPairField S ηr = radialLinearProbe χ)
    (hηc : heightPairField S ηc = radialCosineProbe χ)
    (hηrc : heightPairField S ηrc =
      fun q => radialLinearProbe χ q * radialCosineProbe χ q)
    (hηcc : heightPairField S ηcc =
      fun q => radialCosineProbe χ q * radialCosineProbe χ q)
    {B : SymmetricCoefficients}
    (hAa : DifferentiableAt ℝ (originalCoefficients D S C z).a p)
    (hAb : DifferentiableAt ℝ (originalCoefficients D S C z).b p)
    (hAc : DifferentiableAt ℝ (originalCoefficients D S C z).c p)
    (hBa : DifferentiableAt ℝ B.a p) (hBb : DifferentiableAt ℝ B.b p)
    (hBc : DifferentiableAt ℝ B.c p)
    (heffective : ∀ f : PolarPoint → ℝ, ContDiff ℝ ∞ f →
      divergenceOperator (L.coefficients z) f p = divergenceOperator B f p) :
    coefficientErrorCrossNumerator χ
        (decodedCorrectionError S L z (R.residual z) ηr)
        (decodedCorrectionError S L z (R.residual z) ηc)
        (decodedCorrectionError S L z (R.residual z) ηrc) p =
          -4 * ((originalCoefficients D S C z).b p - B.b p) * Real.sin (2 * p.2) ∧
      coefficientErrorSquareNumerator χ
        (decodedCorrectionError S L z (R.residual z) ηc)
        (decodedCorrectionError S L z (R.residual z) ηcc) p =
          8 * ((originalCoefficients D S C z).c p - B.c p) * Real.sin (2 * p.2) ^ 2 := by
  have herror (η : HeightPair S) :
      divergenceOperator (originalCoefficients D S C z) (heightPairField S η) p -
          divergenceOperator (L.coefficients z) (heightPairField S η) p =
        decodedCorrectionError S L z (R.residual z) η p :=
    hN03.2.2.2.2.2.1 z hz hsector η p hp
  have hr := herror ηr
  have hc := herror ηc
  have hrc := herror ηrc
  have hcc := herror ηcc
  rw [hηr] at hr
  rw [hηc] at hc
  rw [hηrc] at hrc
  rw [hηcc] at hcc
  have hfr := contDiff_radialLinearProbe hχ
  have hfc := contDiff_radialCosineProbe hχ
  exact effectiveCoefficientProbe_identities hχ hone hAa hAb hAc hBa hBb hBc
    (divergenceDifference_eq_of_effective_action hr (heffective _ hfr))
    (divergenceDifference_eq_of_effective_action hc (heffective _ hfc))
    (divergenceDifference_eq_of_effective_action hrc (heffective _ (hfr.mul hfc)))
    (divergenceDifference_eq_of_effective_action hcc (heffective _ (hfc.mul hfc)))

end ContinuousFlexibility.Analysis
