import ContinuousFlexibility.Radial.ModeCoreGraph

/-!
# From the actual differential expression to the frozen weak equation

The profile's flat endpoints annihilate the boundary Wronskian. A
globally smooth lift therefore satisfies the exact modal weak equation
on every region where its pointwise source equation holds. The test
condition is the ordinary support condition in the frozen definition.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- Reuse the proved smooth-core Green symmetry in ordinary radial coordinates. -/
theorem matchingJacobi_symmetric_integral {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u v : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (j : ℕ) :
    (∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w v r) =
      ∫ r in D.a..D.b, v r * radialJacobi ((j : ℝ) ^ 2) D.w u r := by
  rw [← matchingSmoothVector_jacobi_pairing hD j hu hv,
    ← matchingSmoothVector_jacobi_pairing hD j hv hu]
  exact matchingSmoothVector_jacobi_symm hD j hu hv

/-- A smooth actual representative and its actual pointwise weighted
source give the frozen weak modal equation on any test region. -/
theorem modeLocalEquation_of_smooth_pointwise {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {j : ℕ} {J : Set ℝ}
    {U F : RadialModePair D} {u f : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u)
    (hU : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    (hF : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] f)
    (hscalar : U.2 = 0)
    (heq : ∀ r ∈ J, radialJacobi ((j : ℝ) ^ 2) D.w u r =
      -(12 * D.w r / r ^ 2) * f r) :
    ModeLocalEquation D j J U F := by
  intro ψ hψ _ hsupp
  rw [hscalar, zero_mul, sub_zero]
  calc
    (∫ r in D.a..D.b, U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) =
        ∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r := by
      apply matchingInterval_congr_ae hD
      filter_upwards [hU] with r hr
      rw [hr]
    _ = ∫ r in D.a..D.b, ψ r * radialJacobi ((j : ℝ) ^ 2) D.w u r :=
      matchingJacobi_symmetric_integral hD hu hψ j
    _ = -(∫ r in D.a..D.b, (12 * D.w r / r ^ 2) * F.1 r * ψ r) := by
      rw [← intervalIntegral.integral_neg]
      apply matchingInterval_congr_ae hD
      filter_upwards [hF] with r hr
      by_cases hz : ψ r = 0
      · simp only [hz, zero_mul, mul_zero, neg_zero]
      · rw [heq r (hsupp hz), hr]
        ring

end ContinuousFlexibility.Radial
