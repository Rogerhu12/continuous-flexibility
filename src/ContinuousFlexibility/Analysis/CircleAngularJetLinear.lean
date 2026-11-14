module

public import ContinuousFlexibility.Analysis.CircleDifferentialOperators

/-!
# Linear evaluation of every actual circle angular jet

Repeated differentiation stays in the supplied circle model. Composing
its decoder with point evaluations therefore gives a linear functional
for each angular derivative, with the exact iterated-derivative formula.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circleIteratedDerivativeLinear (hS : IsCircleModel T γ S) :
    ℕ → (S.Space →ₗ[ℝ] S.Space)
  | 0 => LinearMap.id
  | n + 1 => (circleDerivativeLinear hS).comp (circleIteratedDerivativeLinear hS n)

theorem circleIteratedDerivativeLinear_decode (hS : IsCircleModel T γ S)
    (n : ℕ) (u : S.Space) :
    S.decode (circleIteratedDerivativeLinear hS n u) =
      fun m => iteratedDeriv n (S.decode u m) := by
  induction n with
  | zero => simp only [circleIteratedDerivativeLinear, LinearMap.id_apply, iteratedDeriv_zero]
  | succ n ih =>
    change S.decode (circleDerivativeLinear hS (circleIteratedDerivativeLinear hS n u)) = _
    rw [circleDerivativeLinear_decode, ih]
    simp only [iteratedDeriv_succ]

def circleAngularJetEvaluationLinear (hS : IsCircleModel T γ S)
    (b m : ℕ) (θ : ℝ) : S.Space →ₗ[ℝ] ℝ :=
  (LinearMap.proj θ).comp ((LinearMap.proj m).comp
    (S.decode.comp (circleIteratedDerivativeLinear hS b)))

theorem circleAngularJetEvaluationLinear_apply (hS : IsCircleModel T γ S)
    (b m : ℕ) (θ : ℝ) (u : S.Space) :
    circleAngularJetEvaluationLinear hS b m θ u = iteratedDeriv b (S.decode u m) θ := by
  change S.decode (circleIteratedDerivativeLinear hS b u) m θ = _
  rw [circleIteratedDerivativeLinear_decode]

end ContinuousFlexibility.Statements
