import ContinuousFlexibility.Analysis.EvenPeriodicCoefficientProbes
import ContinuousFlexibility.Analysis.N04bOperatorCarre

/-!
# Genuine coefficient identities from four even periodic operator probes

The product rule is reused from `N04bOperatorCarre` on the N04b line.
It is applied only to the original smooth operator and the actual smooth
effective operator. An intermediate stored operator need not have smooth
coefficients: equality of its four actual test values is sufficient.

The resulting identities retain the single sine factor for the mixed
coefficient and the double sine factor for the angular coefficient.
Quantitative division by these factors is a separate analytic step.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def divergenceDifference (A B : SymmetricCoefficients)
    (u : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  divergenceOperator A u p - divergenceOperator B u p

/-- The actual product defect of the difference of two smooth operators.
The six assumptions concern only their genuine first coefficient jets. -/
theorem divergenceDifference_product
    {A B : SymmetricCoefficients} {f g : PolarPoint → ℝ} {p : PolarPoint}
    (hAa : DifferentiableAt ℝ A.a p) (hAb : DifferentiableAt ℝ A.b p)
    (hAc : DifferentiableAt ℝ A.c p) (hBa : DifferentiableAt ℝ B.a p)
    (hBb : DifferentiableAt ℝ B.b p) (hBc : DifferentiableAt ℝ B.c p)
    (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p) :
    divergenceDifference A B (fun q => f q * g q) p -
        f p * divergenceDifference A B g p - g p * divergenceDifference A B f p =
      2 * ((A.a p - B.a p) * radialPartial f p * radialPartial g p +
        (A.b p - B.b p) * (radialPartial f p * angularPartial g p +
          angularPartial f p * radialPartial g p) +
        (A.c p - B.c p) * angularPartial f p * angularPartial g p) := by
  have hA := n04b_divergenceOperator_product hAa hAb hAc hf hg
  have hB := n04b_divergenceOperator_product hBa hBb hBc hf hg
  dsimp only [divergenceDifference]
  linear_combination hA - hB

def coefficientErrorCrossNumerator (χ : ℝ → ℝ)
    (Er Ec Erc : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  Erc p - radialLinearProbe χ p * Ec p - radialCosineProbe χ p * Er p

def coefficientErrorSquareNumerator (χ : ℝ → ℝ)
    (Ec Ecc : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  Ecc p - 2 * radialCosineProbe χ p * Ec p

/-- Four actual test values recover the two coefficient numerators.
No regularity of any other representation of the operator is assumed. -/
theorem effectiveCoefficientProbe_identities
    {A B : SymmetricCoefficients} {χ : ℝ → ℝ} {p : PolarPoint}
    (hχ : ContDiff ℝ ∞ χ) (hone : χ =ᶠ[𝓝 p.1] (fun _ : ℝ => 1))
    (hAa : DifferentiableAt ℝ A.a p) (hAb : DifferentiableAt ℝ A.b p)
    (hAc : DifferentiableAt ℝ A.c p) (hBa : DifferentiableAt ℝ B.a p)
    (hBb : DifferentiableAt ℝ B.b p) (hBc : DifferentiableAt ℝ B.c p)
    {Er Ec Erc Ecc : PolarPoint → ℝ}
    (hr : divergenceDifference A B (radialLinearProbe χ) p = Er p)
    (hc : divergenceDifference A B (radialCosineProbe χ) p = Ec p)
    (hrc : divergenceDifference A B
      (fun q => radialLinearProbe χ q * radialCosineProbe χ q) p = Erc p)
    (hcc : divergenceDifference A B
      (fun q => radialCosineProbe χ q * radialCosineProbe χ q) p = Ecc p) :
    coefficientErrorCrossNumerator χ Er Ec Erc p =
        -4 * (A.b p - B.b p) * Real.sin (2 * p.2) ∧
      coefficientErrorSquareNumerator χ Ec Ecc p =
        8 * (A.c p - B.c p) * Real.sin (2 * p.2) ^ 2 := by
  have hf : ContDiffAt ℝ 2 (radialLinearProbe χ) p :=
    (contDiff_radialLinearProbe hχ).contDiffAt.of_le (by simp)
  have hg : ContDiffAt ℝ 2 (radialCosineProbe χ) p :=
    (contDiff_radialCosineProbe hχ).contDiffAt.of_le (by simp)
  have hj := coefficientProbes_partials hone
  have hcross := divergenceDifference_product hAa hAb hAc hBa hBb hBc hf hg
  have hsquare := divergenceDifference_product hAa hAb hAc hBa hBb hBc hg hg
  rw [hrc, hr, hc] at hcross
  rw [hcc, hc] at hsquare
  constructor
  · change Erc p - radialLinearProbe χ p * Ec p - radialCosineProbe χ p * Er p = _
    rw [hcross, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2]
    ring
  · calc
      coefficientErrorSquareNumerator χ Ec Ecc p =
          Ecc p - radialCosineProbe χ p * Ec p - radialCosineProbe χ p * Ec p := by
            dsimp only [coefficientErrorSquareNumerator]
            ring
      _ = _ := hsquare
      _ = 8 * (A.c p - B.c p) * Real.sin (2 * p.2) ^ 2 := by
        rw [hj.2.2.1, hj.2.2.2]
        ring

/-- An arbitrary intermediate operator is used only through its actual
value on the test. The smooth effective field supplies the product rule. -/
theorem divergenceDifference_eq_of_effective_action
    {A L B : SymmetricCoefficients} {f : PolarPoint → ℝ} {p : PolarPoint} {e : ℝ}
    (herror : divergenceOperator A f p - divergenceOperator L f p = e)
    (heffective : divergenceOperator L f p = divergenceOperator B f p) :
    divergenceDifference A B f p = e := by
  dsimp only [divergenceDifference]
  rw [← heffective]
  exact herror

end ContinuousFlexibility.Analysis
