import ContinuousFlexibility.Analysis.OneHighCircleFourierComposition

/-!
# Tame bound for the actual differentiated composed speed

The ordinary chain rule writes the source as `A + A*y`, with
`A = u' ∘ h` and `y = h' - 1`. Composition and the one-high-factor product
estimate then give the exact linear dependence on the high defect norm
needed in the flow argument. The constant uses only the prescribed low
circle geometry, and is uniform in both functions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function MeasureTheory
open scoped ContDiff

def circleFlowSourceConstant (P c M : ℝ) (s : ℕ) : ℝ :=
  max 1 ((1 + (2 : ℝ) ^ s * circleSobolevEmbeddingConstant P * M) *
    circleLiftCompositionConstant P c M s +
      (2 : ℝ) ^ s * circleSobolevEmbeddingConstant P *
        circleLiftCompositionConstant P c M 1 * (1 + M))

theorem circleFlowSourceConstant_one_le (P c M : ℝ) (s : ℕ) :
    1 ≤ circleFlowSourceConstant P c M s := le_max_left _ _

variable {P : ℝ} [Fact (0 < P)]

/-- The actual first derivative of a composition satisfies the tame
source bound, with no independent chain-rule or norm premises. -/
theorem circleLift_composed_derivative_sobolev_le (s : ℕ)
    (u : ℝ → ℝ) (hp : Periodic u P) (hu : ContDiff ℝ ∞ u)
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (hlift : ∀ x, h (x + P) = h x + P)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (hlower : ∀ x, c ≤ deriv h x)
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M) :
    circleRealSobolevNorm (s : ℝ)
        (periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh) 1) ≤
      circleFlowSourceConstant P c M s *
        (circleRealSobolevNorm (s : ℝ) (periodicCircleJet u hp hu 1) +
          circleRealSobolevNorm 3 (periodicCircleJet u hp hu 1) *
            circleRealSobolevNorm (s : ℝ) (circleLiftDefectJet h hh hlift 0)) := by
  let D := periodicCircleJet (deriv u) (periodic_circle_deriv hp) (contDiff_infty_iff_deriv.mp hu).2
  let A := periodicCircleJet ((deriv u) ∘ h)
    (periodic_comp_circleLift (periodic_circle_deriv hp) hlift)
    ((contDiff_infty_iff_deriv.mp hu).2.comp hh)
  let Y := circleLiftDefectJet h hh hlift
  have hD := periodicCircleJet_hasDerivAt (deriv u) (periodic_circle_deriv hp)
    (contDiff_infty_iff_deriv.mp hu).2
  have hA := periodicCircleJet_hasDerivAt ((deriv u) ∘ h)
    (periodic_comp_circleLift (periodic_circle_deriv hp) hlift)
    ((contDiff_infty_iff_deriv.mp hu).2.comp hh)
  have hY := circleLiftDefectJet_hasDerivAt h hh hlift
  have hDzero : D 0 = periodicCircleJet u hp hu 1 := periodicCircleJet_deriv_zero u hp hu
  rw [← hDzero]
  let U := circleRealSobolevNorm (s : ℝ) (D 0)
  let V := circleRealSobolevNorm 3 (D 0)
  let Z := circleRealSobolevNorm (s : ℝ) (Y 0)
  let E := circleSobolevEmbeddingConstant P
  let C := circleLiftCompositionConstant P c M s
  let C₁ := circleLiftCompositionConstant P c M 1
  let α := (1 + (2 : ℝ) ^ s * E * M) * C
  let β := α + (2 : ℝ) ^ s * E * C₁ * (1 + M)
  have hU : 0 ≤ U := circle_real_sobolevNorm_nonneg _ _
  have hV : 0 ≤ V := circle_real_sobolevNorm_nonneg _ _
  have hZ : 0 ≤ Z := circle_real_sobolevNorm_nonneg _ _
  have hE : 0 ≤ E := zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)
  have hC : 0 ≤ C := zero_le_one.trans (circleLiftCompositionConstant_one_le P c M s)
  have hC₁ : 0 ≤ C₁ := zero_le_one.trans (circleLiftCompositionConstant_one_le P c M 1)
  have hAmem := circle_frequencyWeighted_memLp_of_derivatives
    (fun k => circleComplexify (A k)) (circleComplexify_hasDerivAt A hA) s
  have hYmem := circle_frequencyWeighted_memLp_of_derivatives
    (fun k => circleComplexify (Y k)) (circleComplexify_hasDerivAt Y hY) s
  have hAone := circle_fourier_memLp_one_of_derivatives
    (fun k => circleComplexify (A k)) (circleComplexify_hasDerivAt A hA) 0
  have hYone := circle_fourier_memLp_one_of_derivatives
    (fun k => circleComplexify (Y k)) (circleComplexify_hasDerivAt Y hY) 0
  have hproductMem := circle_frequencyWeighted_mul_memLp s
    (circleComplexify (A 0)) (circleComplexify (Y 0)) hAone hYone hAmem hYmem
  have hproductMem' : MemLp (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (fourierCoeff (circleComplexify (A 0 * Y 0)))) 2 Measure.count := by
    simpa only [circleComplexify_mul] using hproductMem
  have hYlower : circleRealSobolevNorm ((s - 1 : ℕ) : ℝ) (Y 0) ≤ Z :=
    circle_real_sobolevNorm_mono_of_derivatives Y hY (Nat.sub_le s 1)
  have hAhigh : circleRealSobolevNorm (s : ℝ) (A 0) ≤ C * (U + V * Z) :=
    (circleLift_sobolev_comp_le s hc hM (deriv u) (periodic_circle_deriv hp)
      (contDiff_infty_iff_deriv.mp hu).2 h hh hlift hlower hlow).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hYlower hV)) hC)
  have hD1 : circleRealSobolevNorm 1 (D 0) ≤ V :=
    circle_real_sobolevNorm_mono_of_derivatives D hD (by norm_num : (1 : ℕ) ≤ 3)
  have hY0 : circleRealSobolevNorm 0 (Y 0) ≤ M :=
    (circle_real_sobolevNorm_mono_of_derivatives Y hY (by norm_num : (0 : ℕ) ≤ 3)).trans hlow
  have hY1 : circleRealSobolevNorm 1 (Y 0) ≤ M :=
    (circle_real_sobolevNorm_mono_of_derivatives Y hY (by norm_num : (1 : ℕ) ≤ 3)).trans hlow
  have hA1 : circleRealSobolevNorm 1 (A 0) ≤ C₁ * (1 + M) * V := by
    calc
      _ ≤ C₁ * (circleRealSobolevNorm 1 (D 0) + V * circleRealSobolevNorm 0 (Y 0)) :=
        circleLift_sobolev_comp_le 1 hc hM (deriv u) (periodic_circle_deriv hp)
          (contDiff_infty_iff_deriv.mp hu).2 h hh hlift hlower hlow
      _ ≤ C₁ * (V + V * M) :=
        mul_le_mul_of_nonneg_left (add_le_add hD1 (mul_le_mul_of_nonneg_left hY0 hV)) hC₁
      _ = _ := by ring
  have hAYlow : circleRealFourierL1Norm (Y 0) ≤ E * M :=
    (circle_real_fourierL1Norm_le_sobolev_one_of_derivatives Y hY 0).trans
      (mul_le_mul_of_nonneg_left hY1 hE)
  have hAAlow : circleRealFourierL1Norm (A 0) ≤ E * C₁ * (1 + M) * V := by
    have hh := (circle_real_fourierL1Norm_le_sobolev_one_of_derivatives A hA 0).trans
      (mul_le_mul_of_nonneg_left hA1 hE)
    simpa only [mul_assoc] using hh
  have hfactor :
      periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh) 1 =
        A 0 + A 0 * Y 0 := by
    simpa only [circleLiftDerivativeJet_zero_eq_one_add_defect, mul_add, mul_one] using
      periodicCircleJet_comp_one u hp hu h hh hlift
  have hcoefficient : 0 ≤ 1 + (2 : ℝ) ^ s * E * M := by positivity
  have hαβ : α ≤ β := le_add_of_nonneg_right (by positivity)
  calc
    _ = circleRealSobolevNorm (s : ℝ) (A 0 + A 0 * Y 0) := by rw [hfactor]
    _ ≤ circleRealSobolevNorm (s : ℝ) (A 0) +
        circleRealSobolevNorm (s : ℝ) (A 0 * Y 0) :=
      circle_real_sobolevNorm_add_le (A 0) (A 0 * Y 0) (s : ℝ) hAmem hproductMem'
    _ ≤ circleRealSobolevNorm (s : ℝ) (A 0) + (2 : ℝ) ^ s *
        (circleRealSobolevNorm (s : ℝ) (A 0) * circleRealFourierL1Norm (Y 0) +
          circleRealFourierL1Norm (A 0) * Z) :=
      add_le_add le_rfl (circle_real_sobolevNorm_mul_le_of_derivatives A Y hA hY s)
    _ ≤ circleRealSobolevNorm (s : ℝ) (A 0) + (2 : ℝ) ^ s *
        (circleRealSobolevNorm (s : ℝ) (A 0) * (E * M) +
          (E * C₁ * (1 + M) * V) * Z) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hAYlow (circle_real_sobolevNorm_nonneg _ _))
          (mul_le_mul_of_nonneg_right hAAlow hZ)) (by positivity))
    _ = (1 + (2 : ℝ) ^ s * E * M) * circleRealSobolevNorm (s : ℝ) (A 0) +
        (2 : ℝ) ^ s * E * C₁ * (1 + M) * (V * Z) := by ring
    _ ≤ (1 + (2 : ℝ) ^ s * E * M) * (C * (U + V * Z)) +
        (2 : ℝ) ^ s * E * C₁ * (1 + M) * (V * Z) :=
      add_le_add (mul_le_mul_of_nonneg_left hAhigh hcoefficient) le_rfl
    _ = α * U + β * (V * Z) := by dsimp only [α, β]; ring
    _ ≤ β * U + β * (V * Z) := add_le_add (mul_le_mul_of_nonneg_right hαβ hU) le_rfl
    _ = β * (U + V * Z) := by ring
    _ ≤ circleFlowSourceConstant P c M s * (U + V * Z) :=
      mul_le_mul_of_nonneg_right (le_max_right 1 β) (add_nonneg hU (mul_nonneg hV hZ))

end ContinuousFlexibility.Analysis
