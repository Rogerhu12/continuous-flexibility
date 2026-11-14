module

public import ContinuousFlexibility.Analysis.N04PulledFieldsWeightedEvaluationPower
public import ContinuousFlexibility.Analysis.CircleSobolevPointwise

/-!
# Angular power bounds with one low order for a circle family

The circle evaluation loss is added to the loss sequence before the low
order is chosen. A finite parameter prefix then pays one power per
parameter derivative. The sample-height factor survives evaluation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {I E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {T : MaterialData} {γ : ℝ} {H : CircleModelData}
  {U : Set E} {p : ℕ → Seminorm ℝ E}

/-- The low order is independent of the parameter prefix. The high
loss and the parameter charge are chosen before the spatial order and
the low-ball radius. Every supplied genuine circle tower has this bound. -/
theorem N04PulledFieldsFixedBaseFamily.circle_diagonal_angular_power
    {g : I → E → H.Space} (hg : N04PulledFieldsFixedBaseFamily p H.grading U g)
    (hp : Monotone p) (hIp : HasInterpolation p) (hH : IsCircleModel T γ H)
    (hpos : ∀ m, 0 < T.H (T.sample m)) :
    ∃ B : ℕ, ∀ K : ℕ, ∃ highLoss shift : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ N k : ℕ, k ≤ K → ∀ b : ℕ, b ≤ N →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ i (J : SmoothDirections U (g i)) x, x ∈ U → ∀ w : E,
        p B x ≤ R → p B w ≤ 1 → ∀ m θ,
        |iteratedDeriv b (H.decode (J.D k x (fun _ => w)) m) θ| ≤
          C * T.H (T.sample m) ^ γ *
            (1 + p (N + highLoss) x + p (N + highLoss) w) ^
              (((b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1)) := by
  exact N04PulledFieldsFixedBaseFamily.weighted_evaluation_power_two
    (I := I) (M := ℕ) (P := ℝ) (E := E) (F := H.Space)
    (p := p) (q := H.grading) (U := U) (f := g) hg hp hIp
    (fun b u m θ => iteratedDeriv b (H.decode u m) θ)
    (fun m => T.H (T.sample m) ^ γ)
    (fun m => Real.rpow_nonneg (hpos m).le γ) 1
    (2 * circleSobolevConstant)
    (mul_nonneg (by norm_num) circleSobolevConstant_nonneg)
    (fun b u m θ => circleModel_iteratedDeriv_abs_le hH hpos u m b θ)

end ContinuousFlexibility.Analysis
