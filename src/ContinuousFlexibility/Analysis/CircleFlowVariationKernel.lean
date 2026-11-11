import ContinuousFlexibility.Analysis.OneHighCircleFourierInverseBasic
import ContinuousFlexibility.Analysis.OneHighCircleFourierComposition
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The actual scalar flow variation kernel

The external-parameter variational formula contains the kernel
(u ∘ h) / h', where h is the actual forward circle flow. Its Sobolev
estimate is linear in the high forcing norm and in the high derivative
defect of h. All derivatives below are those of the actual functions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function MeasureTheory
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]

def circleLiftInverseJacobian (h : ℝ → ℝ) (θ : ℝ) : ℝ :=
  1 + circleLiftReciprocalDefect h θ

theorem circleLiftInverseJacobian_apply (h : ℝ → ℝ) (θ : ℝ) :
    circleLiftInverseJacobian h θ = (deriv h θ)⁻¹ := by
  simp only [circleLiftInverseJacobian, circleLiftReciprocalDefect,
    Function.comp_apply, circleReciprocalDefect, circleLiftDerivativeDefect]
  rw [show (1 : ℝ) + (deriv h θ - 1) = deriv h θ by ring]
  ring

theorem periodic_circleLiftInverseJacobian (h : ℝ → ℝ)
    (hlift : ∀ θ, h (θ + P) = h θ + P) :
    Periodic (circleLiftInverseJacobian h) P := by
  intro θ
  simp only [circleLiftInverseJacobian,
    periodic_circleLiftReciprocalDefect h hlift θ]

theorem contDiff_circleLiftInverseJacobian {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ θ, c ≤ deriv h θ) :
    ContDiff ℝ ∞ (circleLiftInverseJacobian h) :=
  contDiff_const.add (contDiff_circleLiftReciprocalDefect hh hc hlower)

def circleLiftInverseJacobianJet (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ θ, h (θ + P) = h θ + P) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ θ, c ≤ deriv h θ) (n : ℕ) : C(AddCircle P, ℝ) :=
  periodicCircleJet (circleLiftInverseJacobian h)
    (periodic_circleLiftInverseJacobian h hlift)
    (contDiff_circleLiftInverseJacobian hh hc hlower) n

theorem circleLiftInverseJacobianJet_sobolev_le
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ θ, h (θ + P) = h θ + P)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : ∀ θ, c ≤ deriv h θ)
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M)
    (s : ℕ) :
    circleRealSobolevNorm (s : ℝ)
        (circleLiftInverseJacobianJet h hh hlift hc hlower 0) ≤
      1 + circleReciprocalSobolevConstant c (circleLiftLowBound P M) s *
        circleRealSobolevNorm (s : ℝ) (circleLiftDefectJet h hh hlift 0) := by
  have he : circleLiftInverseJacobianJet h hh hlift hc hlower 0 =
      1 + circleLiftReciprocalJet h hh hlift hc hlower 0 := by
    ext θ
    induction θ using QuotientAddGroup.induction_on
    simp only [circleLiftInverseJacobianJet, circleLiftReciprocalJet,
      periodicCircleJet_coe_apply, iteratedDeriv_zero, circleLiftInverseJacobian,
      ContinuousMap.add_apply, ContinuousMap.one_apply]
  rw [he]
  have hone : MemLp (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (fourierCoeff (circleComplexify (1 : C(AddCircle P, ℝ))))) 2 Measure.count := by
    rw [circleComplexify_one]
    exact circle_frequencyWeighted_memLp_const (s : ℝ) (1 : ℂ)
  have hj := periodicCircleJet_hasDerivAt
    (circleLiftReciprocalDefect h) (periodic_circleLiftReciprocalDefect h hlift)
    (contDiff_circleLiftReciprocalDefect hh hc hlower)
  have hrec := circle_frequencyWeighted_memLp_of_derivatives
    (fun k => circleComplexify (circleLiftReciprocalJet h hh hlift hc hlower k))
    (circleComplexify_hasDerivAt _ hj) s
  have htri := circle_real_sobolevNorm_add_le 1
    (circleLiftReciprocalJet h hh hlift hc hlower 0) (s : ℝ) hone hrec
  simp only [circle_real_sobolevNorm_one] at htri
  exact htri.trans (add_le_add le_rfl
    (circleLiftReciprocalJet_sobolev_le h hh hlift hc hM hlower hlow s))

def circleLiftVariationKernel (u h : ℝ → ℝ) (θ : ℝ) : ℝ :=
  u (h θ) * circleLiftInverseJacobian h θ

theorem circleLiftVariationKernel_apply (u h : ℝ → ℝ) (θ : ℝ) :
    circleLiftVariationKernel u h θ = u (h θ) / deriv h θ := by
  rw [circleLiftVariationKernel, circleLiftInverseJacobian_apply, div_eq_mul_inv]

theorem periodic_circleLiftVariationKernel {u h : ℝ → ℝ}
    (hp : Periodic u P) (hlift : ∀ θ, h (θ + P) = h θ + P) :
    Periodic (circleLiftVariationKernel u h) P :=
  (periodic_comp_circleLift hp hlift).mul (periodic_circleLiftInverseJacobian h hlift)

theorem contDiff_circleLiftVariationKernel {u h : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hh : ContDiff ℝ ∞ h)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ θ, c ≤ deriv h θ) :
    ContDiff ℝ ∞ (circleLiftVariationKernel u h) :=
  (hu.comp hh).mul (contDiff_circleLiftInverseJacobian hh hc hlower)

def circleLiftVariationKernelConstant (P c M : ℝ) (s : ℕ) : ℝ :=
  let E := circleSobolevEmbeddingConstant P
  let R₁ := circleReciprocalSobolevConstant c (circleLiftLowBound P M) 1
  let Rₛ := circleReciprocalSobolevConstant c (circleLiftLowBound P M) s
  let A := E * circleLiftCompositionConstant P c M 1 * (1 + M)
  let B := E * (1 + R₁ * M)
  max 1 ((2 : ℝ) ^ s *
    (circleLiftCompositionConstant P c M s * B + A * (1 + Rₛ)))

theorem circleLiftVariationKernelConstant_one_le (P c M : ℝ) (s : ℕ) :
    1 ≤ circleLiftVariationKernelConstant P c M s := le_max_left _ _

/-- The first-variation kernel has a genuine one-high-factor bound.
Only fixed low lift geometry enters the constant. -/
theorem circleLift_variationKernel_sobolev_le
    (s : ℕ) (u : ℝ → ℝ) (hp : Periodic u P) (hu : ContDiff ℝ ∞ u)
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ θ, h (θ + P) = h θ + P)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : ∀ θ, c ≤ deriv h θ)
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M) :
    circleRealSobolevNorm (s : ℝ)
      (periodicCircleJet (circleLiftVariationKernel u h)
        (periodic_circleLiftVariationKernel hp hlift)
        (contDiff_circleLiftVariationKernel hu hh hc hlower) 0) ≤
      circleLiftVariationKernelConstant P c M s *
        (circleRealSobolevNorm (s : ℝ) (periodicCircleJet u hp hu 0) +
          circleRealSobolevNorm 3 (periodicCircleJet u hp hu 0) *
            (1 + circleRealSobolevNorm (s : ℝ) (circleLiftDefectJet h hh hlift 0))) := by
  let U := periodicCircleJet u hp hu
  let Q := circleLiftDefectJet h hh hlift
  let V := periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh)
  let R := circleLiftInverseJacobianJet h hh hlift hc hlower
  let E := circleSobolevEmbeddingConstant P
  let Cₛ := circleLiftCompositionConstant P c M s
  let C₁ := circleLiftCompositionConstant P c M 1
  let Rₛ := circleReciprocalSobolevConstant c (circleLiftLowBound P M) s
  let R₁ := circleReciprocalSobolevConstant c (circleLiftLowBound P M) 1
  let A := E * C₁ * (1 + M)
  let B := E * (1 + R₁ * M)
  let us := circleRealSobolevNorm (s : ℝ) (U 0)
  let ul := circleRealSobolevNorm 3 (U 0)
  let qs := circleRealSobolevNorm (s : ℝ) (Q 0)
  have hE : 0 ≤ E := zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)
  have hCs : 0 ≤ Cₛ := zero_le_one.trans (circleLiftCompositionConstant_one_le P c M s)
  have hC1 : 0 ≤ C₁ := zero_le_one.trans (circleLiftCompositionConstant_one_le P c M 1)
  have hRs : 0 ≤ Rₛ := circleReciprocalSobolevConstant_nonneg _ _ s hc
    (zero_le_one.trans (circleLiftLowBound_one_le hM))
  have hR1 : 0 ≤ R₁ := circleReciprocalSobolevConstant_nonneg _ _ 1 hc
    (zero_le_one.trans (circleLiftLowBound_one_le hM))
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hE hC1) (add_nonneg zero_le_one hM)
  have hB : 0 ≤ B := mul_nonneg hE (add_nonneg zero_le_one (mul_nonneg hR1 hM))
  have hus : 0 ≤ us := circle_real_sobolevNorm_nonneg _ _
  have hul : 0 ≤ ul := circle_real_sobolevNorm_nonneg _ _
  have hqs : 0 ≤ qs := circle_real_sobolevNorm_nonneg _ _
  have hU := periodicCircleJet_hasDerivAt u hp hu
  have hQ := circleLiftDefectJet_hasDerivAt h hh hlift
  have hV := periodicCircleJet_hasDerivAt (u ∘ h)
    (periodic_comp_circleLift hp hlift) (hu.comp hh)
  have hR := periodicCircleJet_hasDerivAt (circleLiftInverseJacobian h)
    (periodic_circleLiftInverseJacobian h hlift)
    (contDiff_circleLiftInverseJacobian hh hc hlower)
  have hqsmall (n : ℕ) (hn : n ≤ 3) :
      circleRealSobolevNorm (n : ℝ) (Q 0) ≤ M :=
    (circle_real_sobolevNorm_mono_of_derivatives Q hQ hn).trans hlow
  have hVs : circleRealSobolevNorm (s : ℝ) (V 0) ≤ Cₛ * (us + ul * qs) := by
    have hm := circle_real_sobolevNorm_mono_of_derivatives Q hQ (Nat.sub_le s 1)
    exact (circleLift_sobolev_comp_le s hc hM u hp hu h hh hlift hlower hlow).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hm hul)) hCs)
  have hRs' : circleRealSobolevNorm (s : ℝ) (R 0) ≤ 1 + Rₛ * qs :=
    circleLiftInverseJacobianJet_sobolev_le h hh hlift hc hM hlower hlow s
  have hRlow : circleRealFourierL1Norm (R 0) ≤ B := by
    have hs1 : circleRealSobolevNorm 1 (R 0) ≤ 1 + R₁ * M :=
      (circleLiftInverseJacobianJet_sobolev_le h hh hlift hc hM hlower hlow 1).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hqsmall 1 (by omega)) hR1))
    exact (circle_real_fourierL1Norm_le_sobolev_one_of_derivatives R hR 0).trans
      (mul_le_mul_of_nonneg_left hs1 hE)
  have hVlow : circleRealFourierL1Norm (V 0) ≤ A * ul := by
    have hu1 : circleRealSobolevNorm 1 (U 0) ≤ ul :=
      circle_real_sobolevNorm_mono_of_derivatives U hU (show 1 ≤ 3 by omega)
    have hv1 := circleLift_sobolev_comp_le 1 hc hM u hp hu h hh hlift hlower hlow
    have hq0 := hqsmall 0 (by omega)
    calc
      _ ≤ E * circleRealSobolevNorm 1 (V 0) :=
        circle_real_fourierL1Norm_le_sobolev_one_of_derivatives V hV 0
      _ ≤ E * (C₁ * (circleRealSobolevNorm 1 (U 0) +
          ul * circleRealSobolevNorm 0 (Q 0))) :=
        mul_le_mul_of_nonneg_left hv1 hE
      _ ≤ E * (C₁ * (ul + ul * M)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (add_le_add hu1 (mul_le_mul_of_nonneg_left hq0 hul)) hC1) hE
      _ = A * ul := by dsimp only [A]; ring
  have he :
      periodicCircleJet (circleLiftVariationKernel u h)
        (periodic_circleLiftVariationKernel hp hlift)
        (contDiff_circleLiftVariationKernel hu hh hc hlower) 0 = V 0 * R 0 := by
    ext θ
    induction θ using QuotientAddGroup.induction_on
    simp only [V, R, circleLiftInverseJacobianJet, periodicCircleJet_coe_apply,
      iteratedDeriv_zero, ContinuousMap.mul_apply, circleLiftVariationKernel,
      Function.comp_apply]
  rw [he]
  have hprod := circle_real_sobolevNorm_mul_le_of_derivatives V R hV hR s
  have hterms :
      circleRealSobolevNorm (s : ℝ) (V 0) * circleRealFourierL1Norm (R 0) +
        circleRealFourierL1Norm (V 0) * circleRealSobolevNorm (s : ℝ) (R 0) ≤
      (Cₛ * B + A * (1 + Rₛ)) * (us + ul * (1 + qs)) := by
    have H0 : us + ul * qs ≤ us + ul * (1 + qs) := by nlinarith only [hul]
    have H1 : ul ≤ us + ul * (1 + qs) := by
      nlinarith only [hus, mul_nonneg hul hqs]
    have H2 : ul * qs ≤ us + ul * (1 + qs) := by nlinarith only [hus, hul]
    calc
      _ ≤ (Cₛ * (us + ul * qs)) * B + (A * ul) * (1 + Rₛ * qs) :=
        add_le_add
          (mul_le_mul hVs hRlow (frequencyL1Norm_nonneg _ _)
            (mul_nonneg hCs (add_nonneg hus (mul_nonneg hul hqs))))
          (mul_le_mul hVlow hRs' (circle_real_sobolevNorm_nonneg _ _) (mul_nonneg hA hul))
      _ = (Cₛ * B) * (us + ul * qs) + A * ul + (A * Rₛ) * (ul * qs) := by ring
      _ ≤ (Cₛ * B) * (us + ul * (1 + qs)) +
          A * (us + ul * (1 + qs)) + (A * Rₛ) * (us + ul * (1 + qs)) :=
        add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left H0 (mul_nonneg hCs hB))
            (mul_le_mul_of_nonneg_left H1 hA))
          (mul_le_mul_of_nonneg_left H2 (mul_nonneg hA hRs))
      _ = _ := by ring
  have hbase := hprod.trans (mul_le_mul_of_nonneg_left hterms (by positivity))
  change circleRealSobolevNorm (s : ℝ) (V 0 * R 0) ≤
    circleLiftVariationKernelConstant P c M s * (us + ul * (1 + qs))
  calc
    _ ≤ ((2 : ℝ) ^ s * (Cₛ * B + A * (1 + Rₛ))) * (us + ul * (1 + qs)) := by
      simpa only [mul_assoc] using hbase
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (le_max_right _ _) (add_nonneg hus (mul_nonneg hul (add_nonneg zero_le_one hqs)))

end ContinuousFlexibility.Analysis
