import ContinuousFlexibility.Analysis.N04FlowQualitative
import ContinuousFlexibility.Analysis.ParameterizedInverseFirstDerivative

/-!
# Genuine inverses for the regularized mixed flow

The original closed-time equation gives a strictly positive angular
Jacobian at every external parameter. The actual inverse is therefore
jointly smooth on the whole parameter space, even though quantitative
bounds are only required on the fixed parameter box.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04Flow_angular_deriv_pos
    {F : ℝ × N04FlowPoint → ℝ} {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (v : ℝ × ℝ) (θ : ℝ) :
    0 < deriv (fun η : ℝ => Θ v t η) θ := by
  rw [(circleFlow_hasDerivAt_angle
    (G := fun z : PolarPoint => F (z.1, (v, z.2)))
    (Θ := fun z : PolarPoint => Θ v z.1 z.2)
    (n04Flow_field_contDiff hF v) Real.pi_pos (fun r => hperiod r v)
    (n04Flow_time_continuousOn hΘ v) (hΘ.1 v)
    (fun r hr η => n04Flow_time_hasDerivAt hΘ v η hr) ht θ).deriv]
  exact Real.exp_pos _

theorem contDiff_n04FlowInverse
    {F : ℝ × N04FlowPoint → ℝ} {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi)
    (hΘ : N04FlowEquations F Θ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContDiff ℝ ∞ (parameterizedCircleInverse (fun q : N04FlowPoint => Θ q.1 t q.2)) :=
  contDiff_parameterizedCircleInverse Real.pi_ne_zero
    (n04Flow_contDiff_slice hF hperiod hΘ ht)
    (fun q => n04Flow_angular_deriv_pos hF hperiod hΘ ht q.1 q.2)
    (fun v θ => n04Flow_period_add hF hperiod hΘ v θ ht)

theorem scalarFamilyLift_circleInverse_identities
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {f : P × ℝ → ℝ} {T : ℝ} (hT : T ≠ 0) (hf : ContDiff ℝ ∞ f)
    (hpositive : ∀ q : P × ℝ, 0 < deriv (fun θ => f (q.1, θ)) q.2)
    (hperiod : ∀ p θ, f (p, θ + T) = f (p, θ) + T) :
    Function.LeftInverse (scalarFamilyLift (parameterizedCircleInverse f))
      (scalarFamilyLift f) ∧
    Function.RightInverse (scalarFamilyLift (parameterizedCircleInverse f))
      (scalarFamilyLift f) := by
  constructor
  · intro q
    exact Prod.ext rfl (parameterizedCircleInverse_left_inverse hpositive q)
  · intro q
    exact Prod.ext rfl (parameterizedCircleInverse_right_inverse hT hf hperiod q)

theorem scalarFamilyLift_circleInverse_fderiv_comp
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {f : P × ℝ → ℝ} {T : ℝ} (hT : T ≠ 0) (hf : ContDiff ℝ ∞ f)
    (hpositive : ∀ q : P × ℝ, 0 < deriv (fun θ => f (q.1, θ)) q.2)
    (hperiod : ∀ p θ, f (p, θ + T) = f (p, θ) + T) (x : P × ℝ) :
    (fderiv ℝ (scalarFamilyLift (parameterizedCircleInverse f)) x).comp
      (fderiv ℝ (scalarFamilyLift f)
        (scalarFamilyLift (parameterizedCircleInverse f) x)) =
      ContinuousLinearMap.id ℝ (P × ℝ) := by
  let F : P × ℝ → P × ℝ := scalarFamilyLift f
  let G : P × ℝ → P × ℝ := scalarFamilyLift (parameterizedCircleInverse f)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk hf
  have hG : ContDiff ℝ ∞ G := contDiff_fst.prodMk
    (contDiff_parameterizedCircleInverse hT hf hpositive hperiod)
  obtain ⟨hleft, hright⟩ := scalarFamilyLift_circleInverse_identities hT hf hpositive hperiod
  have he : G ∘ F = id := funext hleft
  have hrightAt : F (G x) = x := hright x
  change (fderiv ℝ G x).comp (fderiv ℝ F (G x)) = _
  calc
    _ = (fderiv ℝ G (F (G x))).comp (fderiv ℝ F (G x)) := by rw [hrightAt]
    _ = fderiv ℝ (G ∘ F) (G x) :=
      (fderiv_comp (G x) (hG.differentiable (by simp) _)
        (hF.differentiable (by simp) _)).symm
    _ = _ := by rw [he, fderiv_id]

end ContinuousFlexibility.Analysis
