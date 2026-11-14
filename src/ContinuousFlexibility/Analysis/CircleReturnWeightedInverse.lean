module

public import ContinuousFlexibility.Analysis.CircleReturnInverseLinear
public import ContinuousFlexibility.Analysis.CircleReturnBounded

/-!
# The return inverse in the supplied weighted circle model

The actual integral-coefficient inverse is linear on the full circle
carrier. A common sample-weight bound on the reciprocal small-divisor
margins gives its fixed-loss tame estimate. The two inverse laws then
hold in the supplied model, by its injective decoder.

The quantitative margin hypothesis is explicit. Pointwise irrationality
alone is not used as a substitute for that uniform weighted hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis MeasureTheory
open scoped ContDiff ENNReal NNReal

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

/-- The full-domain scalar inverse on the actual decoded circle fields. -/
def circleReturnInverseFieldLinear (hS : IsCircleModel T γ S)
    (travel margin : ℕ → ℝ) (hmargin : ∀ m, 0 < margin m)
    (hdiv : ∀ m j : ℕ, 1 ≤ j → margin m / j ≤ |Real.sin (j * travel m)|) :
    S.Space →ₗ[ℝ] (ℕ → ℝ → ℝ) where
  toFun u m := circleReturnSolution (S.decode u m) (travel m)
  map_add' u v := by
    funext m θ
    have hu := (hS.2.2.2.1 u).1 m
    have hv := (hS.2.2.2.1 v).1 m
    simpa only [map_add, Pi.add_apply] using congrFun
      (circleReturnSolution_add (hmargin m) (hdiv m) hu.1 hv.1 hu.2 hv.2) θ
  map_smul' c u := by
    funext m θ
    simpa only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul] using
      congrFun (circleReturnSolution_smul (S.decode u m) (travel m) c) θ

theorem circleReturnInverseFieldLinear_apply (hS : IsCircleModel T γ S)
    (travel margin : ℕ → ℝ) (hmargin : ∀ m, 0 < margin m)
    (hdiv : ∀ m j : ℕ, 1 ≤ j → margin m / j ≤ |Real.sin (j * travel m)|)
    (u : S.Space) (m : ℕ) :
    circleReturnInverseFieldLinear hS travel margin hmargin hdiv u m =
      circleReturnSolution (S.decode u m) (travel m) := rfl

/-- The scalar inverse estimate absorbs the reciprocal divisor into the
specified power of the actual sample weight. -/
theorem circleReturnSolution_weighted_L2_bound
    {u : ℕ → ℝ → ℝ} (hu : CircleMember T γ u)
    (travel margin : ℕ → ℝ) (hmargin : ∀ m, 0 < margin m)
    (hdiv : ∀ m j : ℕ, 1 ≤ j → margin m / j ≤ |Real.sin (j * travel m)|)
    (k : ℕ) {A : ℝ} (hbound : ∀ m, (margin m)⁻¹ ≤ A * T.M (T.sample m) ^ k)
    (m b : ℕ) :
    eLpNorm (iteratedDeriv b (circleReturnSolution (u m) (travel m))) 2 angleMeasure ≤
      ENNReal.ofReal ((circleReturnL2Constant * A) * T.M (T.sample m) ^ k) *
        eLpNorm (iteratedDeriv (b + 3) (u m)) 2 angleMeasure := by
  apply (eLpNorm_iteratedDeriv_circleReturnSolution_le_all
    (hmargin m) (hdiv m) (hu.1 m).1 (hu.1 m).2 b).trans
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound m) circleReturnL2Constant_nonneg

theorem circleReturnInverseField_member (hS : IsCircleModel T γ S)
    (travel margin : ℕ → ℝ) (hmargin : ∀ m, 0 < margin m)
    (hdiv : ∀ m j : ℕ, 1 ≤ j → margin m / j ≤ |Real.sin (j * travel m)|)
    (k : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ m, (margin m)⁻¹ ≤ A * T.M (T.sample m) ^ k)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (u : S.Space) :
    CircleMember T γ (circleReturnInverseFieldLinear hS travel margin hmargin hdiv u) := by
  have hu := hS.2.2.2.1 u
  apply circleMember_of_L2_derivative_bound hu 3 k
    (mul_nonneg circleReturnL2Constant_nonneg hA) hM hH
  · intro m
    exact ⟨contDiff_circleReturnSolution (hmargin m) (hdiv m) (hu.1 m).1 (hu.1 m).2,
      periodic_circleReturnSolution _ _⟩
  · exact circleReturnSolution_weighted_L2_bound hu travel margin hmargin hdiv k hbound

/-- The actual inverse linear map in the existing physical model. -/
def circleReturnInverseLinear (hS : IsCircleModel T γ S)
    (travel margin : ℕ → ℝ) (hmargin : ∀ m, 0 < margin m)
    (hdiv : ∀ m j : ℕ, 1 ≤ j → margin m / j ≤ |Real.sin (j * travel m)|)
    (k : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ m, (margin m)⁻¹ ≤ A * T.M (T.sample m) ^ k)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m)) :
    S.Space →ₗ[ℝ] S.Space :=
  liftCircleLinear hS (circleReturnInverseFieldLinear hS travel margin hmargin hdiv)
    (circleReturnInverseField_member hS travel margin hmargin hdiv k hA hbound hM hH)

section InverseProperties

variable (hS : IsCircleModel T γ S) (travel margin : ℕ → ℝ)
  (hmargin : ∀ m, 0 < margin m)
  (hdiv : ∀ m j : ℕ, 1 ≤ j → margin m / j ≤ |Real.sin (j * travel m)|)
  (k : ℕ) {A : ℝ} (hA : 0 ≤ A)
  (hbound : ∀ m, (margin m)⁻¹ ≤ A * T.M (T.sample m) ^ k)
  (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))

theorem circleReturnInverseLinear_decode (u : S.Space) (m : ℕ) :
    S.decode (circleReturnInverseLinear hS travel margin hmargin hdiv k hA hbound hM hH u) m =
      circleReturnSolution (S.decode u m) (travel m) := by
  have hdecode := liftCircleLinear_decode hS
    (circleReturnInverseFieldLinear hS travel margin hmargin hdiv)
    (circleReturnInverseField_member hS travel margin hmargin hdiv k hA hbound hM hH) u
  exact congrFun hdecode m

theorem circleReturnInverseLinear_tame :
    IsTameLinear S.grading S.grading
      (circleReturnInverseLinear hS travel margin hmargin hdiv k hA hbound hM hH)
      (3 + k) 0 := by
  let F : S.Space →ₗ[ℝ] (ℕ → ℝ → ℝ) :=
    circleReturnInverseFieldLinear hS travel margin hmargin hdiv
  have hF : ∀ u, CircleMember T γ (F u) :=
    circleReturnInverseField_member hS travel margin hmargin hdiv k hA hbound hM hH
  have hb : ∀ n, ∃ B : ℝ≥0, ∀ u,
      circleNorm T γ n (F u) ≤ (B : ℝ) * S.grading (n + (3 + k)) u := by
    intro n
    refine ⟨⟨circleReturnL2Constant * A, mul_nonneg circleReturnL2Constant_nonneg hA⟩, ?_⟩
    intro u
    have hu := hS.2.2.2.1 u
    have h := circleNorm_le_of_L2_derivative_bound hu n 3 k
      (mul_nonneg circleReturnL2Constant_nonneg hA) hM hH
      (circleReturnSolution_weighted_L2_bound hu travel margin hmargin hdiv k hbound)
    have hg : circleNorm T γ (n + 3 + k) (S.decode u) ≤
        S.grading (n + (3 + k)) u := by
      rw [Nat.add_assoc]
      exact ((circleGrading_le_iff_circleNorm hS (n + (3 + k)) u
        (apply_nonneg _ _)).mp (le_refl (S.grading (n + (3 + k)) u)))
        (n + (3 + k)) le_rfl
    exact h.trans (mul_le_mul_of_nonneg_left hg
      (mul_nonneg circleReturnL2Constant_nonneg hA))
  exact liftCircleLinear_isTame hS F hF S.grading
    (gradedSeminorm_monotone (fun i => S.level i) S.bond) (3 + k) hb

theorem circleReturnInverseLinear_odd (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleReturnInverseLinear hS travel margin hmargin hdiv k hA hbound hM hH u) m (-θ) =
      -S.decode (circleReturnInverseLinear hS travel margin hmargin hdiv k hA hbound hM hH u) m θ := by
  rw [circleReturnInverseLinear_decode]
  exact odd_circleReturnSolution _ _ θ

theorem circleReturnInverseLinear_right_inverse (u : S.Space)
    (he : ∀ m, Function.Even (S.decode u m))
    (hz : ∀ m, angularMean (S.decode u m) = 0) :
    circleReturnLinear hS travel
      (circleReturnInverseLinear hS travel margin hmargin hdiv k hA hbound hM hH u) = u := by
  apply hS.2.2.2.2.2.1
  funext m θ
  rw [circleReturnLinear_decode, circleReturnInverseLinear_decode]
  have hu := (hS.2.2.2.1 u).1 m
  have hm : ∫ θ in (0 : ℝ)..Real.pi, S.decode u m θ = 0 := by
    have h := hz m
    unfold angularMean at h
    exact (mul_eq_zero.mp h).resolve_left (one_div_ne_zero Real.pi_ne_zero)
  exact congrFun (circleReturnSolution_right_inverse (hmargin m) (hdiv m)
    hu.1 hu.2 (he m) hm) θ

theorem circleReturnInverseLinear_left_inverse (u : S.Space)
    (ho : ∀ m θ, S.decode u m (-θ) = -S.decode u m θ) :
    circleReturnInverseLinear hS travel margin hmargin hdiv k hA hbound hM hH
      (circleReturnLinear hS travel u) = u := by
  apply hS.2.2.2.2.2.1
  funext m θ
  rw [circleReturnInverseLinear_decode]
  have hdecode : S.decode (circleReturnLinear hS travel u) m =
      circleReturnShift (travel m) (S.decode u m) := by
    funext t
    exact circleReturnLinear_decode hS travel u m t
  rw [hdecode]
  have hu := (hS.2.2.2.1 u).1 m
  exact congrFun (circleReturnSolution_left_inverse (hmargin m) (hdiv m)
    hu.1 hu.2 (ho m)) θ

end InverseProperties

end ContinuousFlexibility.Statements
