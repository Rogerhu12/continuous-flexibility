import ContinuousFlexibility.Analysis.N04PulledFieldsWeightedEvaluationPower
import ContinuousFlexibility.Analysis.CircleSobolevPointwise

/-!
# Angular power bounds with one low order for a circle family

The circle evaluation loss is added to the loss sequence before the low
order is chosen. A finite parameter prefix then pays one power per
parameter derivative. The sample-height factor survives evaluation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

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
  let ev : ℕ → H.Space → (ℕ × ℝ) → ℝ := fun b u y =>
    iteratedDeriv b (H.decode u y.1) y.2
  let weight : (ℕ × ℝ) → ℝ := fun y => T.H (T.sample y.1) ^ γ
  have hweight (y : ℕ × ℝ) : 0 ≤ weight y := Real.rpow_nonneg (hpos y.1).le γ
  have heval (b : ℕ) (u : H.Space) (y : ℕ × ℝ) :
      |ev b u y| ≤ (2 * circleSobolevConstant * H.grading (b + 1) u) * weight y :=
    circleModel_iteratedDeriv_abs_le hH hpos u y.1 b y.2
  obtain ⟨B, hB⟩ := N04PulledFieldsFixedBaseFamily.weighted_evaluation_power
    (I := I) (M := ℕ × ℝ) (E := E) (F := H.Space)
    (p := p) (q := H.grading) (U := U) (f := g) hg hp hIp ev weight hweight 1
    (2 * circleSobolevConstant)
    (mul_nonneg (by norm_num) circleSobolevConstant_nonneg) heval
  refine ⟨B, fun K => ?_⟩
  obtain ⟨highLoss, shift, hprefix⟩ := hB K
  refine ⟨highLoss, shift, fun R hR N k hk b hb => ?_⟩
  obtain ⟨C, hC, hc⟩ := hprefix R hR N k hk b hb
  exact ⟨C, hC, fun i J x hx w hxlow hwlow m θ =>
    hc i J x hx w hxlow hwlow (m, θ)⟩

end ContinuousFlexibility.Analysis
