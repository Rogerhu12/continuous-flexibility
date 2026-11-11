import ContinuousFlexibility.Analysis.ParameterizedScalarInverse
import ContinuousFlexibility.Analysis.PeriodicScalarFlow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual smooth inverses of parameterized circle lifts

The displacement of a continuous degree-one periodic lift is periodic
and hence bounded. The intermediate value theorem then gives
surjectivity. A positive angular derivative supplies injectivity.
The actual chosen inverse therefore satisfies both inverse identities,
and the parameterized implicit theorem supplies its joint smoothness.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

/-- Every continuous degree-one periodic lift is surjective. The proof
uses a bound on its periodic displacement, without a derivative bound. -/
theorem surjective_of_continuous_periodic_lift
    {f : ℝ → ℝ} {T : ℝ} (hT : T ≠ 0) (hf : Continuous f)
    (hperiod : ∀ θ : ℝ, f (θ + T) = f θ + T) :
    Function.Surjective f := by
  have hc : Continuous (fun z : ℝ × ℝ => f z.2 - z.2) :=
    (hf.comp continuous_snd).sub continuous_snd
  obtain ⟨M, _, hM⟩ := exists_norm_bound_periodic_compact
    (S := ({0} : Set ℝ)) (F := fun z : ℝ × ℝ => f z.2 - z.2)
    isCompact_singleton hT hc.continuousOn
    (fun _ _ θ => by
      change f (θ + T) - (θ + T) = f θ - θ
      rw [hperiod θ]
      ring)
  have hb (θ : ℝ) : |f θ - θ| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM 0 (by simp) θ
  intro y
  apply mem_range_of_exists_le_of_exists_ge hf
  · refine ⟨y - M, ?_⟩
    have h := (abs_le.mp (hb (y - M))).2
    linarith
  · refine ⟨y + M, ?_⟩
    have h := (abs_le.mp (hb (y + M))).1
    linarith

/-- The actual pointwise inverse of each circle lift. -/
def parameterizedCircleInverse {P : Type*} (F : P × ℝ → ℝ) (z : P × ℝ) : ℝ :=
  Function.invFun (fun θ => F (z.1, θ)) z.2

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  {F : P × ℝ → ℝ} {T : ℝ}

/-- The chosen inverse is a right inverse at every parameter and angle. -/
theorem parameterizedCircleInverse_right_inverse
    (hT : T ≠ 0) (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ p θ, F (p, θ + T) = F (p, θ) + T) (z : P × ℝ) :
    F (z.1, parameterizedCircleInverse F z) = z.2 := by
  have hc : Continuous (fun θ : ℝ => F (z.1, θ)) :=
    hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hs := surjective_of_continuous_periodic_lift hT hc (hperiod z.1)
  exact Function.rightInverse_invFun hs z.2

/-- Positive actual angular derivatives make the chosen inverse a left inverse. -/
theorem parameterizedCircleInverse_left_inverse
    (hpositive : ∀ z : P × ℝ, 0 < deriv (fun θ => F (z.1, θ)) z.2)
    (z : P × ℝ) :
    parameterizedCircleInverse F (z.1, F z) = z.2 := by
  exact Function.leftInverse_invFun
    (strictMono_of_deriv_pos (f := fun θ : ℝ => F (z.1, θ))
      (fun θ => hpositive (z.1, θ))).injective z.2

/-- The actual pointwise inverse is jointly smooth in every parameter and angle. -/
theorem contDiff_parameterizedCircleInverse
    (hT : T ≠ 0) (hF : ContDiff ℝ ∞ F)
    (hpositive : ∀ z : P × ℝ, 0 < deriv (fun θ => F (z.1, θ)) z.2)
    (hperiod : ∀ p θ, F (p, θ + T) = F (p, θ) + T) :
    ContDiff ℝ ∞ (parameterizedCircleInverse F) :=
  contDiff_parameterized_scalar_rightInverse hF hpositive
    (parameterizedCircleInverse_right_inverse hT hF hperiod)

/-- The actual inverse has the same degree-one angular equivariance. -/
theorem parameterizedCircleInverse_period_add
    (hT : T ≠ 0) (hF : ContDiff ℝ ∞ F)
    (hpositive : ∀ z : P × ℝ, 0 < deriv (fun θ => F (z.1, θ)) z.2)
    (hperiod : ∀ p θ, F (p, θ + T) = F (p, θ) + T) (p : P) (θ : ℝ) :
    parameterizedCircleInverse F (p, θ + T) =
      parameterizedCircleInverse F (p, θ) + T := by
  have hr := parameterizedCircleInverse_right_inverse hT hF hperiod
  apply (strictMono_of_deriv_pos (f := fun φ : ℝ => F (p, φ))
    (fun φ => hpositive (p, φ))).injective
  change F (p, parameterizedCircleInverse F (p, θ + T)) =
    F (p, parameterizedCircleInverse F (p, θ) + T)
  exact (hr (p, θ + T)).trans
    ((hperiod p (parameterizedCircleInverse F (p, θ))).trans
      (congrArg (fun x : ℝ => x + T) (hr (p, θ)))).symm

/-- Reflection covariance of the forward lifts passes to their actual inverses. -/
theorem parameterizedCircleInverse_reflect
    {σ : P → P}
    (hT : T ≠ 0) (hF : ContDiff ℝ ∞ F)
    (hpositive : ∀ z : P × ℝ, 0 < deriv (fun θ => F (z.1, θ)) z.2)
    (hperiod : ∀ p θ, F (p, θ + T) = F (p, θ) + T)
    (hreflect : ∀ p θ, F (σ p, -θ) = -F (p, θ)) (p : P) (θ : ℝ) :
    parameterizedCircleInverse F (σ p, -θ) =
      -parameterizedCircleInverse F (p, θ) := by
  have hr := parameterizedCircleInverse_right_inverse hT hF hperiod
  apply (strictMono_of_deriv_pos (f := fun φ : ℝ => F (σ p, φ))
    (fun φ => hpositive (σ p, φ))).injective
  change F (σ p, parameterizedCircleInverse F (σ p, -θ)) =
    F (σ p, -parameterizedCircleInverse F (p, θ))
  exact (hr (σ p, -θ)).trans
    ((hreflect p (parameterizedCircleInverse F (p, θ))).trans
      (congrArg (fun x : ℝ => -x) (hr (p, θ)))).symm

/-- Its actual angular derivative is the reciprocal forward Jacobian. -/
theorem hasDerivAt_parameterizedCircleInverse
    (hT : T ≠ 0) (hF : ContDiff ℝ ∞ F)
    (hpositive : ∀ z : P × ℝ, 0 < deriv (fun θ => F (z.1, θ)) z.2)
    (hperiod : ∀ p θ, F (p, θ + T) = F (p, θ) + T) (p : P) (θ : ℝ) :
    HasDerivAt (fun φ => parameterizedCircleInverse F (p, φ))
      (deriv (fun φ => F (p, φ)) (parameterizedCircleInverse F (p, θ)))⁻¹ θ := by
  have hG := contDiff_parameterizedCircleInverse hT hF hpositive hperiod
  have hGs : ContDiff ℝ ∞ (fun φ : ℝ => parameterizedCircleInverse F (p, φ)) :=
    hG.comp (contDiff_const.prodMk contDiff_id)
  have hg := (hGs.differentiable (by simp) θ).hasDerivAt
  have hp := hpositive (p, parameterizedCircleInverse F (p, θ))
  have hf := (differentiableAt_of_deriv_ne_zero hp.ne').hasDerivAt
  have hc := hf.comp θ hg
  have he : (fun φ : ℝ => F (p, φ)) ∘
      (fun φ : ℝ => parameterizedCircleInverse F (p, φ)) = id := by
    funext φ
    exact parameterizedCircleInverse_right_inverse hT hF hperiod (p, φ)
  rw [he] at hc
  have hprod := hc.unique (hasDerivAt_id θ)
  have hrecip :
      deriv (fun φ => parameterizedCircleInverse F (p, φ)) θ =
        (deriv (fun φ => F (p, φ)) (parameterizedCircleInverse F (p, θ)))⁻¹ := by
    apply mul_left_cancel₀ hp.ne'
    rw [hprod, mul_inv_cancel₀ hp.ne']
  exact hg.congr_deriv hrecip

/-- The inverse angular Jacobian is strictly positive. -/
theorem parameterizedCircleInverse_deriv_pos
    (hT : T ≠ 0) (hF : ContDiff ℝ ∞ F)
    (hpositive : ∀ z : P × ℝ, 0 < deriv (fun θ => F (z.1, θ)) z.2)
    (hperiod : ∀ p θ, F (p, θ + T) = F (p, θ) + T) (p : P) (θ : ℝ) :
    0 < deriv (fun φ => parameterizedCircleInverse F (p, φ)) θ := by
  rw [(hasDerivAt_parameterizedCircleInverse hT hF hpositive hperiod p θ).deriv]
  exact inv_pos.mpr (hpositive (p, parameterizedCircleInverse F (p, θ)))

end ContinuousFlexibility.Analysis
