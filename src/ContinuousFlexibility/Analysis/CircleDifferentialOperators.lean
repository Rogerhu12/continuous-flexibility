import ContinuousFlexibility.Analysis.CircleWeightedEstimate
import ContinuousFlexibility.Analysis.CircleSobolevPointwise
import ContinuousFlexibility.Analysis.TameLinear
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Angular differentiation in the supplied circle model

The actual weighted angular derivative has one derivative of loss and no
loss of sample weight.  Its membership proof shifts the angular index in
the complete energy sum.  The decoder then realizes this operation as a
continuous linear map in the original circle space.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal NNReal BigOperators

theorem circleMember_angularDerivative
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) :
    CircleMember T γ (fun m => deriv (u m)) := by
  have hreg (m : ℕ) : ContDiff ℝ ∞ (deriv (u m)) :=
    (contDiff_infty_iff_deriv.mp (hu.1 m).1).2
  apply circleMember_of_jet_bound hu 1 0
  · intro m
    refine ⟨hreg m, ?_⟩
    simpa only [iteratedDeriv_one] using
      circlePeriodic_iteratedDeriv_real (hu.1 m).2 1
  · exact fun m b => memLp_angleMeasure_iteratedDeriv_of_contDiff (hreg m) b
  · intro s
    refine ⟨1, by norm_num, ?_⟩
    intro m j
    simp only [Nat.add_zero, one_mul, iteratedDeriv_succ']
    exact le_rfl

theorem circleNorm_angularDerivative_le
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (s : ℕ) :
    circleNorm T γ s (fun m => deriv (u m)) ≤ circleNorm T γ (s + 1) u := by
  have h := circleNorm_le_of_jet_bound (v := fun m => deriv (u m))
    hu s 1 0 (C := 1) (by norm_num) (by
      intro m j
      simp only [Nat.add_zero, one_pow, ENNReal.ofReal_one, one_mul,
        iteratedDeriv_succ']
      exact le_rfl)
  simpa only [Nat.add_zero, one_mul] using h

def circleDerivativeFieldLinear
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) : S.Space →ₗ[ℝ] (ℕ → ℝ → ℝ) where
  toFun u m := deriv (S.decode u m)
  map_add' u v := by
    funext m θ
    have hu := (contDiff_infty_iff_deriv.mp ((hS.2.2.2.1 u).1 m).1).1 θ
    have hv := (contDiff_infty_iff_deriv.mp ((hS.2.2.2.1 v).1 m).1).1 θ
    simp only [map_add, Pi.add_apply]
    exact deriv_add hu hv
  map_smul' c u := by
    funext m θ
    have hu := (contDiff_infty_iff_deriv.mp ((hS.2.2.2.1 u).1 m).1).1 θ
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    exact deriv_const_smul c hu

theorem circleDerivativeFieldLinear_apply
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (u : S.Space) (m : ℕ) (θ : ℝ) :
    circleDerivativeFieldLinear hS u m θ = deriv (S.decode u m) θ := rfl

def circleDerivativeLinear
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) : S.Space →ₗ[ℝ] S.Space :=
  liftCircleLinear hS (circleDerivativeFieldLinear hS)
    (fun u => circleMember_angularDerivative (hS.2.2.2.1 u))

theorem circleDerivativeLinear_decode
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (u : S.Space) :
    S.decode (circleDerivativeLinear hS u) = fun m => deriv (S.decode u m) := by
  exact liftCircleLinear_decode hS (circleDerivativeFieldLinear hS)
    (fun v => circleMember_angularDerivative (hS.2.2.2.1 v)) u

theorem circleDerivativeLinear_isTame
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) :
    IsTameLinear S.grading S.grading (circleDerivativeLinear hS) 1 0 := by
  apply liftCircleLinear_isTame hS (circleDerivativeFieldLinear hS)
    (fun u => circleMember_angularDerivative (hS.2.2.2.1 u))
    S.grading (gradedSeminorm_monotone (fun i => S.level i) S.bond) 1
  intro n
  refine ⟨1, ?_⟩
  intro u
  simp only [NNReal.coe_one, one_mul]
  have h := circleNorm_angularDerivative_le (hS.2.2.2.1 u) n
  have hg := ((circleGrading_le_iff_circleNorm hS (n + 1) u
    (apply_nonneg _ _)).mp (le_refl (S.grading (n + 1) u))) (n + 1) le_rfl
  exact h.trans hg

def circleDerivativeContinuousLinear
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) : S.Space →L[ℝ] S.Space :=
  (circleDerivativeLinear_isTame hS).toContinuousLinearMap
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (gradedSeminorm_monotone (fun i => S.level i) S.bond)

theorem circleDerivativeContinuousLinear_decode
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (u : S.Space) :
    S.decode (circleDerivativeContinuousLinear hS u) =
      fun m => deriv (S.decode u m) := by
  have heq : circleDerivativeContinuousLinear hS u = circleDerivativeLinear hS u :=
    IsTameLinear.toContinuousLinearMap_apply (circleDerivativeLinear_isTame hS)
      (withSeminorms_graded (fun i => S.level i) S.bond)
      (withSeminorms_graded (fun i => S.level i) S.bond)
      (gradedSeminorm_monotone (fun i => S.level i) S.bond) u
  rw [heq]
  exact circleDerivativeLinear_decode hS u

end ContinuousFlexibility.Statements
