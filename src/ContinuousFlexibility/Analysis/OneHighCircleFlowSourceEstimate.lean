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

private theorem circle_source_add_mul_sobolev_le
    (A Y : ℕ → C(AddCircle P, ℝ))
    (hA : ∀ n : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => A n (y : AddCircle P)) (A (n + 1) (x : AddCircle P)) x)
    (hY : ∀ n : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Y n (y : AddCircle P)) (Y (n + 1) (x : AddCircle P)) x)
    (s : ℕ) :
    circleRealSobolevNorm (s : ℝ) (A 0 + A 0 * Y 0) ≤
      circleRealSobolevNorm (s : ℝ) (A 0) + (2 : ℝ) ^ s *
        (circleRealSobolevNorm (s : ℝ) (A 0) * circleRealFourierL1Norm (Y 0) +
          circleRealFourierL1Norm (A 0) * circleRealSobolevNorm (s : ℝ) (Y 0)) := by
  have hAmem := circle_frequencyWeighted_memLp_of_derivatives
    (fun k => circleComplexify (A k)) (circleComplexify_hasDerivAt A hA) s
  have hYmem := circle_frequencyWeighted_memLp_of_derivatives
    (fun k => circleComplexify (Y k)) (circleComplexify_hasDerivAt Y hY) s
  have hAone := circle_fourier_memLp_one_of_derivatives
    (fun k => circleComplexify (A k)) (circleComplexify_hasDerivAt A hA) 0
  have hYone := circle_fourier_memLp_one_of_derivatives
    (fun k => circleComplexify (Y k)) (circleComplexify_hasDerivAt Y hY) 0
  have hproduct := circle_frequencyWeighted_mul_memLp s
    (circleComplexify (A 0)) (circleComplexify (Y 0)) hAone hYone hAmem hYmem
  have hp : MemLp (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (fourierCoeff (circleComplexify (A 0 * Y 0)))) 2 Measure.count := by
    simpa only [circleComplexify_mul] using hproduct
  exact (circle_real_sobolevNorm_add_le (A 0) (A 0 * Y 0) (s : ℝ) hAmem hp).trans
    (add_le_add le_rfl (circle_real_sobolevNorm_mul_le_of_derivatives A Y hA hY s))

private theorem circle_source_scalar_bound
    {S A FA FY U V Z K E M C C₁ : ℝ}
    (hA0 : 0 ≤ A) (hU : 0 ≤ U) (hV : 0 ≤ V) (hZ : 0 ≤ Z)
    (hK : 0 ≤ K) (hE : 0 ≤ E) (hM : 0 ≤ M) (hC₁ : 0 ≤ C₁)
    (hsource : S ≤ A + K * (A * FY + FA * Z))
    (hhigh : A ≤ C * (U + V * Z))
    (hFY : FY ≤ E * M) (hFA : FA ≤ E * C₁ * (1 + M) * V) :
    S ≤ max 1 ((1 + K * E * M) * C + K * E * C₁ * (1 + M)) * (U + V * Z) := by
  let α : ℝ := (1 + K * E * M) * C
  let β : ℝ := α + K * E * C₁ * (1 + M)
  have hcoefficient : 0 ≤ 1 + K * E * M := by positivity
  have hαβ : α ≤ β := le_add_of_nonneg_right (by positivity)
  calc
    S ≤ A + K * (A * FY + FA * Z) := hsource
    _ ≤ A + K * (A * (E * M) + (E * C₁ * (1 + M) * V) * Z) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hFY hA0)
          (mul_le_mul_of_nonneg_right hFA hZ)) hK)
    _ = (1 + K * E * M) * A + K * E * C₁ * (1 + M) * (V * Z) := by ring
    _ ≤ (1 + K * E * M) * (C * (U + V * Z)) +
        K * E * C₁ * (1 + M) * (V * Z) :=
      add_le_add (mul_le_mul_of_nonneg_left hhigh hcoefficient) le_rfl
    _ = α * U + β * (V * Z) := by dsimp only [α, β]; ring
    _ ≤ β * U + β * (V * Z) :=
      add_le_add (mul_le_mul_of_nonneg_right hαβ hU) le_rfl
    _ = β * (U + V * Z) := by ring
    _ ≤ max 1 β * (U + V * Z) :=
      mul_le_mul_of_nonneg_right (le_max_right 1 β) (add_nonneg hU (mul_nonneg hV hZ))

private theorem circle_source_composition_fourierL1_le
    (v : ℝ → ℝ) (hp : Periodic v P) (hv : ContDiff ℝ ∞ v)
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (hlift : ∀ x, h (x + P) = h x + P)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (hlower : ∀ x, c ≤ deriv h x)
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M) :
    circleRealFourierL1Norm
        (periodicCircleJet (v ∘ h) (periodic_comp_circleLift hp hlift) (hv.comp hh) 0) ≤
      circleSobolevEmbeddingConstant P * circleLiftCompositionConstant P c M 1 * (1 + M) *
        circleRealSobolevNorm 3 (periodicCircleJet v hp hv 0) := by
  let D := periodicCircleJet v hp hv
  let A := periodicCircleJet (v ∘ h) (periodic_comp_circleLift hp hlift) (hv.comp hh)
  let Y := circleLiftDefectJet h hh hlift
  have hD := periodicCircleJet_hasDerivAt v hp hv
  have hA := periodicCircleJet_hasDerivAt (v ∘ h) (periodic_comp_circleLift hp hlift) (hv.comp hh)
  have hY := circleLiftDefectJet_hasDerivAt h hh hlift
  have hD1 : circleRealSobolevNorm 1 (D 0) ≤ circleRealSobolevNorm 3 (D 0) := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      circle_real_sobolevNorm_mono_of_derivatives D hD (by norm_num : (1 : ℕ) ≤ 3)
  have hY0 : circleRealSobolevNorm 0 (Y 0) ≤ M := by
    have hm : circleRealSobolevNorm 0 (Y 0) ≤ circleRealSobolevNorm 3 (Y 0) := by
      simpa only [Nat.cast_zero, Nat.cast_ofNat] using
        circle_real_sobolevNorm_mono_of_derivatives Y hY (by norm_num : (0 : ℕ) ≤ 3)
    exact hm.trans hlow
  have hcomp : circleRealSobolevNorm 1 (A 0) ≤
      circleLiftCompositionConstant P c M 1 *
        (circleRealSobolevNorm 1 (D 0) +
          circleRealSobolevNorm 3 (D 0) * circleRealSobolevNorm 0 (Y 0)) := by
    simpa only [Nat.cast_one, Nat.cast_zero, Nat.sub_self] using
      circleLift_sobolev_comp_le 1 hc hM v hp hv h hh hlift hlower hlow
  have hlowA : circleRealSobolevNorm 1 (A 0) ≤
      circleLiftCompositionConstant P c M 1 * (1 + M) *
        circleRealSobolevNorm 3 (D 0) := by
    apply hcomp.trans
    calc
      _ ≤ circleLiftCompositionConstant P c M 1 *
          (circleRealSobolevNorm 3 (D 0) + circleRealSobolevNorm 3 (D 0) * M) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hD1 (mul_le_mul_of_nonneg_left hY0 (circle_real_sobolevNorm_nonneg _ _)))
          (zero_le_one.trans (circleLiftCompositionConstant_one_le P c M 1))
      _ = _ := by ring
  have hhbound := (circle_real_fourierL1Norm_le_sobolev_one_of_derivatives A hA 0).trans
    (mul_le_mul_of_nonneg_left hlowA
      (zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)))
  simpa only [mul_assoc] using hhbound

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
  have hA := periodicCircleJet_hasDerivAt ((deriv u) ∘ h)
    (periodic_comp_circleLift (periodic_circle_deriv hp) hlift)
    ((contDiff_infty_iff_deriv.mp hu).2.comp hh)
  have hY := circleLiftDefectJet_hasDerivAt h hh hlift
  have hDzero : D 0 = periodicCircleJet u hp hu 1 := periodicCircleJet_deriv_zero u hp hu
  rw [← hDzero]
  have hYlower : circleRealSobolevNorm ((s - 1 : ℕ) : ℝ) (Y 0) ≤
      circleRealSobolevNorm (s : ℝ) (Y 0) :=
    circle_real_sobolevNorm_mono_of_derivatives Y hY (Nat.sub_le s 1)
  have hAhigh : circleRealSobolevNorm (s : ℝ) (A 0) ≤
      circleLiftCompositionConstant P c M s *
        (circleRealSobolevNorm (s : ℝ) (D 0) +
          circleRealSobolevNorm 3 (D 0) * circleRealSobolevNorm (s : ℝ) (Y 0)) :=
    (circleLift_sobolev_comp_le s hc hM (deriv u) (periodic_circle_deriv hp)
      (contDiff_infty_iff_deriv.mp hu).2 h hh hlift hlower hlow).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hYlower
          (circle_real_sobolevNorm_nonneg _ _)))
        (zero_le_one.trans (circleLiftCompositionConstant_one_le P c M s)))
  have hY1 : circleRealSobolevNorm 1 (Y 0) ≤ M := by
    have hm : circleRealSobolevNorm 1 (Y 0) ≤ circleRealSobolevNorm 3 (Y 0) := by
      simpa only [Nat.cast_one, Nat.cast_ofNat] using
        circle_real_sobolevNorm_mono_of_derivatives Y hY (by norm_num : (1 : ℕ) ≤ 3)
    exact hm.trans hlow
  have hFY : circleRealFourierL1Norm (Y 0) ≤ circleSobolevEmbeddingConstant P * M :=
    (circle_real_fourierL1Norm_le_sobolev_one_of_derivatives Y hY 0).trans
      (mul_le_mul_of_nonneg_left hY1
        (zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)))
  have hFA := circle_source_composition_fourierL1_le (deriv u) (periodic_circle_deriv hp)
    (contDiff_infty_iff_deriv.mp hu).2 h hh hlift hc hM hlower hlow
  have hfactor :
      periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh) 1 =
        A 0 + A 0 * Y 0 := by
    simpa only [circleLiftDerivativeJet_zero_eq_one_add_defect, mul_add, mul_one] using
      periodicCircleJet_comp_one u hp hu h hh hlift
  rw [hfactor]
  have hsum := circle_source_add_mul_sobolev_le A Y hA hY s
  exact circle_source_scalar_bound
    (circle_real_sobolevNorm_nonneg _ _) (circle_real_sobolevNorm_nonneg _ _)
    (circle_real_sobolevNorm_nonneg _ _) (circle_real_sobolevNorm_nonneg _ _)
    (by positivity) (zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)) hM
    (zero_le_one.trans (circleLiftCompositionConstant_one_le P c M 1))
    hsum hAhigh hFY hFA

end ContinuousFlexibility.Analysis
