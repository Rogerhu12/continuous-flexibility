module

public import ContinuousFlexibility.Analysis.PrincipalCoefficientPullback

/-!
# Actual height conjugation of a divergence operator

The scalar conjugation formula is a product-rule identity for the actual
height and test function. It produces both the weighted principal density
and the potential before any change of coordinates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Multiplication of a symmetric principal density by the square of a height. -/
def heightWeightedCoefficients (A : SymmetricCoefficients)
    (h : PolarPoint → ℝ) : SymmetricCoefficients where
  a y := h y ^ 2 * A.a y
  b y := h y ^ 2 * A.b y
  c y := h y ^ 2 * A.c y

theorem differentiableAt_heightWeightedCoefficients
    {A : SymmetricCoefficients} {h : PolarPoint → ℝ} {x : PolarPoint}
    (ha : DifferentiableAt ℝ A.a x) (hb : DifferentiableAt ℝ A.b x)
    (hc : DifferentiableAt ℝ A.c x) (hh : DifferentiableAt ℝ h x) :
    DifferentiableAt ℝ (heightWeightedCoefficients A h).a x ∧
      DifferentiableAt ℝ (heightWeightedCoefficients A h).b x ∧
      DifferentiableAt ℝ (heightWeightedCoefficients A h).c x := by
  have hsq : DifferentiableAt ℝ (fun y => h y ^ 2) x := by
    simpa only [pow_two] using hh.fun_mul hh
  exact ⟨hsq.fun_mul ha, hsq.fun_mul hb, hsq.fun_mul hc⟩

/-- The actual Lagrange product identity. No transformed operator or
potential identity is supplied as a premise. -/
theorem heightConjugation_divergence
    {A : SymmetricCoefficients} {h v : PolarPoint → ℝ} {x : PolarPoint}
    (ha : DifferentiableAt ℝ A.a x) (hb : DifferentiableAt ℝ A.b x)
    (hc : DifferentiableAt ℝ A.c x)
    (hh : ContDiffAt ℝ 2 h x) (hv : ContDiffAt ℝ 2 v x) :
    h x * divergenceOperator A (fun y => h y * v y) x =
      divergenceOperator (heightWeightedCoefficients A h) v x +
        h x * v x * divergenceOperator A h x := by
  have hh1 : DifferentiableAt ℝ h x := hh.differentiableAt (by norm_num)
  have hv1 : DifferentiableAt ℝ v x := hv.differentiableAt (by norm_num)
  have hhh : DifferentiableAt ℝ (fun y => h y * h y) x :=
    hh1.fun_mul hh1
  have hwa : DifferentiableAt ℝ (fun y => (h y * h y) * A.a y) x :=
    hhh.fun_mul ha
  have hwb : DifferentiableAt ℝ (fun y => (h y * h y) * A.b y) x :=
    hhh.fun_mul hb
  have hwc : DifferentiableAt ℝ (fun y => (h y * h y) * A.c y) x :=
    hhh.fun_mul hc
  simp only [divergenceOperator, heightWeightedCoefficients, pow_two]
  rw [divergence_expansion_of_coefficients ha hb hc (hh.mul hv),
    divergence_expansion_of_coefficients hwa hwb hwc hv,
    divergence_expansion_of_coefficients ha hb hc hh]
  unfold radialPartial angularPartial
  simp only [polar_directional_mul hh1 hv1, polar_second_directional_mul hh hv,
    polar_directional_mul hhh ha, polar_directional_mul hhh hb,
    polar_directional_mul hhh hc, polar_directional_mul hh1 hh1]
  ring

end ContinuousFlexibility.Analysis
