module

public import ContinuousFlexibility.Analysis.OneHighCircleReciprocalBasic
public import ContinuousFlexibility.Analysis.OneHighCircleScalarComposition

/-!
# Uniform Sobolev estimates for the reciprocal defect

The lower bound for the denominator controls every outer derivative on the
entire segment to zero. The resulting constant depends only on the positive
lower bound, the prescribed low Fourier norm, and the Sobolev order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function Set
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]

def circleReciprocalSobolevConstant (c R : ℝ) (s : ℕ) : ℝ :=
  circleScalarCompositionConstant s R (circleReciprocalDerivativeBound c)

theorem circleReciprocalSobolevConstant_nonneg (c R : ℝ) (s : ℕ)
    (hc : 0 < c) (hR : 0 ≤ R) : 0 ≤ circleReciprocalSobolevConstant c R s := by
  have hB := circleReciprocalDerivativeBound_nonneg hc
  unfold circleReciprocalSobolevConstant circleScalarCompositionConstant
  split_ifs
  · exact hB 1
  · exact mul_nonneg (by positivity)
      (add_nonneg (hB 1) (circleScalarCompositionCoefficient_nonneg s hR hB))

/-- The genuine reciprocal of a smooth periodic derivative defect satisfies
the uniform one-high estimate at every natural order, including zero. -/
theorem circle_reciprocal_sobolev_le
    (s : ℕ) (c R : ℝ) (hc : 0 < c) (hR : 0 ≤ R)
    (v : ℝ → ℝ) (hp : Periodic v P) (hv : ContDiff ℝ ∞ v)
    (hlower : ∀ x, c - 1 ≤ v x)
    (hlow : circleRealFourierL1Norm (periodicCircleJet v hp hv 0) ≤ R) :
    circleRealSobolevNorm (s : ℝ)
      (periodicCircleJet (circleReciprocalDefect ∘ v)
        (periodic_circleReciprocal_comp hp)
        (contDiff_circleReciprocal_comp hv hc hlower) 0) ≤
      circleReciprocalSobolevConstant c R s *
        circleRealSobolevNorm (s : ℝ) (periodicCircleJet v hp hv 0) := by
  let S : Set ℝ := Ici (min 1 c - 1)
  have h0 : (0 : ℝ) ∈ S := by
    exact sub_nonpos.mpr (min_le_left 1 c)
  have hvin : ∀ x, v x ∈ S := by
    intro x
    exact (sub_le_sub_right (min_le_right 1 c) 1).trans (hlower x)
  have hΦ : ∀ z ∈ S, ContDiffAt ℝ ∞ circleReciprocalDefect z := by
    intro z hz
    have hd : 0 < min (1 : ℝ) c := lt_min (by norm_num) hc
    have hden : 0 < 1 + z := by
      have hz' : min 1 c - 1 ≤ z := hz
      linarith
    exact contDiffAt_circleReciprocalDefect z hden.ne'
  have h := circle_scalar_composition_sobolev_le s v circleReciprocalDefect hp hv
    (convex_Ici (min 1 c - 1)) h0 hvin hΦ
    (circleReciprocalDerivativeBound_nonneg hc)
    (fun z hz n hn _ => circleReciprocalDefect_iteratedDeriv_bound hc hz hn) hlow
  simpa only [circleReciprocalSobolevConstant, circleReciprocalDefect_zero,
    sub_zero, Function.comp_def] using h

end ContinuousFlexibility.Analysis
