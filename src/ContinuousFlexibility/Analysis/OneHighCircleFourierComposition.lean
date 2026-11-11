import ContinuousFlexibility.Analysis.OneHighCircleFourierCompositionStep

/-!
# Uniform tame composition by genuine circle lifts

The constant is constructed recursively from the period, derivative lower
bound, and prescribed low geometry. It is uniform in the outer function and
the lift, and all norms are the actual normalized Fourier/Bessel norms.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]

/-- The explicitly constructed constant in tame circle composition. -/
def circleLiftCompositionConstant (P c M : ℝ) : ℕ → ℝ
  | 0 => circleLiftCompositionLowConstant P 0 c M
  | n + 1 => if n ≤ 2 then circleLiftCompositionLowConstant P (n + 1) c M else
      max 1 (circleLiftCompositionStepConstant P (n - 3) c M
        (circleLiftCompositionConstant P c M n))

theorem circleLiftCompositionConstant_one_le (P c M : ℝ) (s : ℕ) :
    1 ≤ circleLiftCompositionConstant P c M s := by
  cases s with
  | zero => exact circleLiftCompositionLowConstant_one_le P 0 c M
  | succ n =>
    rw [circleLiftCompositionConstant]
    split_ifs
    · exact circleLiftCompositionLowConstant_one_le P (n + 1) c M
    · exact le_max_left _ _

private theorem circleLift_sobolev_comp_le_low_tame (u : ℝ → ℝ) (hp : Periodic u P)
    (hu : ContDiff ℝ ∞ u) (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hlift : ∀ x, h (x + P) = h x + P) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : ∀ x, c ≤ deriv h x)
    (hlow : circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M)
    (s : ℕ) (hs : s ≤ 3) :
    circleRealSobolevNorm (s : ℝ)
        (periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh) 0) ≤
      circleLiftCompositionLowConstant P s c M *
        (circleRealSobolevNorm (s : ℝ) (periodicCircleJet u hp hu 0) +
          circleRealSobolevNorm 3 (periodicCircleJet u hp hu 0) *
            circleRealSobolevNorm ((s - 1 : ℕ) : ℝ) (circleLiftDefectJet h hh hlift 0)) := by
  apply (circleLift_sobolev_comp_le_low u hp hu h hh hlift hc hM hlower hlow s hs).trans
  apply mul_le_mul_of_nonneg_left _
    ((by positivity : (0 : ℝ) ≤ 1).trans (circleLiftCompositionLowConstant_one_le P s c M))
  exact le_add_of_nonneg_right (mul_nonneg
    (circle_real_sobolevNorm_nonneg _ _) (circle_real_sobolevNorm_nonneg _ _))

/-- Tame composition at every natural order. In particular, the asserted
estimate for `s ≥ 1` has a constant depending only on `P`, `c`, and `M`.
The order-zero extension is included for convenient induction and reuse. -/
theorem circleLift_sobolev_comp_le (s : ℕ) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    ∀ (u : ℝ → ℝ) (hp : Periodic u P) (hu : ContDiff ℝ ∞ u)
      (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (hlift : ∀ x, h (x + P) = h x + P),
      (∀ x, c ≤ deriv h x) →
      circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M →
      circleRealSobolevNorm (s : ℝ)
          (periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh) 0) ≤
        circleLiftCompositionConstant P c M s *
          (circleRealSobolevNorm (s : ℝ) (periodicCircleJet u hp hu 0) +
            circleRealSobolevNorm 3 (periodicCircleJet u hp hu 0) *
              circleRealSobolevNorm ((s - 1 : ℕ) : ℝ) (circleLiftDefectJet h hh hlift 0)) := by
  induction s with
  | zero =>
    intro u hp hu h hh hlift hlower hlow
    exact circleLift_sobolev_comp_le_low_tame u hp hu h hh hlift hc hM hlower hlow 0 (by omega)
  | succ n ih =>
    intro u hp hu h hh hlift hlower hlow
    by_cases hn : n ≤ 2
    · simpa only [circleLiftCompositionConstant, if_pos hn] using
        circleLift_sobolev_comp_le_low_tame u hp hu h hh hlift hc hM hlower hlow
          (n + 1) (by omega)
    · have hprev := ih (deriv u) (periodic_circle_deriv hp)
        (contDiff_infty_iff_deriv.mp hu).2 h hh hlift hlower hlow
      have hr : n - 3 + 3 = n := by omega
      have hr' : n - 3 + 4 = n + 1 := by omega
      have hp' : n - 1 = n - 3 + 2 := by omega
      have hstep := circleLift_sobolev_comp_le_step u hp hu h hh hlift hc hM
        ((by positivity : (0 : ℝ) ≤ 1).trans (circleLiftCompositionConstant_one_le P c M n))
        hlower hlow (n - 3) (by simpa only [hr, hp'] using hprev)
      have hT : 0 ≤ circleRealSobolevNorm ((n + 1 : ℕ) : ℝ) (periodicCircleJet u hp hu 0) +
          circleRealSobolevNorm 3 (periodicCircleJet u hp hu 0) *
            circleRealSobolevNorm (n : ℝ) (circleLiftDefectJet h hh hlift 0) :=
        add_nonneg (circle_real_sobolevNorm_nonneg _ _)
          (mul_nonneg (circle_real_sobolevNorm_nonneg _ _) (circle_real_sobolevNorm_nonneg _ _))
      rw [hr, hr'] at hstep
      have hbound := hstep.trans (mul_le_mul_of_nonneg_right (le_max_right 1
        (circleLiftCompositionStepConstant P (n - 3) c M
          (circleLiftCompositionConstant P c M n))) hT)
      simpa only [circleLiftCompositionConstant, if_neg hn, Nat.add_sub_cancel] using hbound

/-- Uniformity is explicit: the same constant works for every smooth
periodic outer function and every lift satisfying the fixed low bounds. -/
theorem exists_circleLift_composition_constant (s : ℕ) (c M : ℝ) (hc : 0 < c)
    (hM : 0 ≤ M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : ℝ → ℝ) (hp : Periodic u P) (hu : ContDiff ℝ ∞ u)
      (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (hlift : ∀ x, h (x + P) = h x + P),
      (∀ x, c ≤ deriv h x) →
      circleRealSobolevNorm 3 (circleLiftDefectJet h hh hlift 0) ≤ M →
      circleRealSobolevNorm (s : ℝ)
          (periodicCircleJet (u ∘ h) (periodic_comp_circleLift hp hlift) (hu.comp hh) 0) ≤
        C * (circleRealSobolevNorm (s : ℝ) (periodicCircleJet u hp hu 0) +
          circleRealSobolevNorm 3 (periodicCircleJet u hp hu 0) *
            circleRealSobolevNorm ((s - 1 : ℕ) : ℝ) (circleLiftDefectJet h hh hlift 0)) :=
  ⟨circleLiftCompositionConstant P c M s, circleLiftCompositionConstant_one_le P c M s,
    circleLift_sobolev_comp_le s hc hM⟩

end ContinuousFlexibility.Analysis
