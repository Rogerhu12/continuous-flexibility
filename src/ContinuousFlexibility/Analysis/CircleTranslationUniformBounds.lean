import ContinuousFlexibility.Analysis.CirclePositiveInverseModel
import ContinuousFlexibility.Analysis.CircleReturnBounded

/-!
# Uniform circle translations and the actual inverse lift

The translation is the existing chart-composition operator with zero
perturbation. Every angular L² norm, and hence every supplied circle
grading, is unchanged by translation. The inverse of a lift with travel
`t` is the inverse of its zero-travel lift evaluated at `θ - t`.
Consequently travel contributes no constant to inverse-composition bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory Statements
open scoped ContDiff ENNReal

theorem circleNorm_translate_le
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (travel : ℕ → ℝ) (s : ℕ) :
    circleNorm T γ s (fun m θ => u m (θ + travel m)) ≤ circleNorm T γ s u := by
  have h := circleNorm_le_of_jet_bound
    (v := fun m θ => u m (θ + travel m)) hu s 0 0 (C := 1) zero_le_one
  simp only [Nat.add_zero, one_mul] at h
  apply h
  intro m j
  have hp : Function.Periodic (iteratedDeriv (j.val 0).val (u m)) Real.pi := by
    have heq : (fun θ => u m (θ + Real.pi)) = u m := funext (hu.1 m).2
    intro θ
    have hd := congrArg (fun f : ℝ → ℝ => iteratedDeriv (j.val 0).val f θ) heq
    simpa only [iteratedDeriv_comp_add_const] using hd
  have hshift := circle_angleL2_shift
    ((hu.1 m).1.continuous_iteratedDeriv (j.val 0).val (by simp)) hp (travel m)
  simp only [iteratedDeriv_comp_add_const, hshift, one_pow, ENNReal.ofReal_one,
    one_mul, le_refl]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

/-- The already realized chart composition with zero perturbation. -/
def circleTranslationContinuousLinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (travel : ℕ → ℝ) :
    S.Space →L[ℝ] S.Space :=
  circleShiftedChartComposeContinuousLinear hS hT hD hγ travel 0

theorem circleTranslationContinuousLinear_decode
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (travel : ℕ → ℝ) (u : S.Space) :
    S.decode (circleTranslationContinuousLinear hS hT hD hγ travel u) =
      fun m θ => S.decode u m (θ + travel m) := by
  simp only [circleTranslationContinuousLinear, circleShiftedChartComposeContinuousLinear_apply,
    circleShiftedChartComposeLinear_decode, map_zero, Pi.zero_apply, add_zero]

theorem circleTranslationContinuousLinear_grading_le
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (travel : ℕ → ℝ)
    (s : ℕ) (u : S.Space) :
    S.grading s (circleTranslationContinuousLinear hS hT hD hγ travel u) ≤ S.grading s u := by
  apply (circleGrading_le_iff_circleNorm hS s _ (apply_nonneg _ _)).mpr
  intro i hi
  rw [circleTranslationContinuousLinear_decode]
  exact (circleNorm_translate_le (hS.2.2.2.1 u) travel i).trans
    ((circleGrading_le_iff_circleNorm hS s u (apply_nonneg _ _)).mp le_rfl i hi)

theorem circleShiftedChartComposeLinear_eq_zero_travel
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (travel : ℕ → ℝ) (e u : S.Space) :
    circleShiftedChartComposeLinear hS hT hD hγ travel e u =
      circleShiftedChartComposeLinear hS hT hD hγ (fun _ => 0) e
        (circleTranslationContinuousLinear hS hT hD hγ travel u) := by
  apply hS.2.2.2.2.2.1
  rw [circleShiftedChartComposeLinear_decode, circleShiftedChartComposeLinear_decode]
  funext m θ
  rw [circleTranslationContinuousLinear_decode]
  congr 1
  ring

theorem circleAffineInverse_eq_zero_travel
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (travel : ℕ → ℝ)
    (e : S.Space) (he : e ∈ circlePositiveLiftDomain S) (m : ℕ) (θ : ℝ) :
    circleAffineInverse travel e m θ =
      circleAffineInverse (fun _ => 0) e m (θ - travel m) := by
  apply circleAffineInverse_eq_of_leftInverse hS hT hD hγ travel e
    (fun j t => circleAffineInverse (fun _ => 0) e j (t - travel j))
  intro j t
  have harg : circleAffineLift travel (S.decode e) 1 j t - travel j =
      circleAffineLift (fun _ => 0) (S.decode e) 1 j t := by
    simp only [circleAffineLift, one_mul]
    ring
  rw [harg]
  exact Function.leftInverse_invFun
    (strictMono_of_deriv_pos (fun y => by
      rw [circleAffineLift_deriv hS]
      exact he j y)).injective t

theorem circlePositiveInverseComposeLinear_eq_zero_travel
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (travel : ℕ → ℝ)
    (e u : S.Space) (he : e ∈ circlePositiveLiftDomain S) :
    circlePositiveInverseComposeLinear hS hT hD hγ travel e u =
      circleTranslationContinuousLinear hS hT hD hγ (fun m => -travel m)
        (circlePositiveInverseComposeLinear hS hT hD hγ (fun _ => 0) e u) := by
  apply hS.2.2.2.2.2.1
  rw [circlePositiveInverseComposeLinear_decode hS hT hD hγ travel e u he,
    circleTranslationContinuousLinear_decode,
    circlePositiveInverseComposeLinear_decode hS hT hD hγ (fun _ => 0) e u he]
  funext m θ
  exact congrArg (S.decode u m)
    (by simpa only [sub_eq_add_neg] using
      circleAffineInverse_eq_zero_travel hS hT hD hγ travel e he m θ)

end ContinuousFlexibility.Statements
