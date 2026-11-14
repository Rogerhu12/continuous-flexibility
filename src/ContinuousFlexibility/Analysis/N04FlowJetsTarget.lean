module

public import ContinuousFlexibility.Statements.Analysis

/-!
# Fixed-loss mixed spatial jets of a genuine periodic scalar flow

This target quantifies only actual derivatives of the original field.
The material envelope and the state precede neither the output constants
nor the fixed loss. The angular Gronwall exponent is controlled
separately from the possibly large parameter derivatives of the field.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

abbrev N04FlowPoint := (ℝ × ℝ) × ℝ

def n04FlowParameterBox : Set (ℝ × ℝ) :=
  Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1

/-- Actual spatial jets in the two external parameters and the angle.
Time is not one of the differentiated coordinates. -/
def N04FlowRawJetBounds {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (inputLoss : ℕ)
    (A : ℕ → ℝ) (z : E) (W : ℝ) (F : ℝ × N04FlowPoint → ℝ) : Prop :=
  ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ q : N04FlowPoint,
    q.1 ∈ n04FlowParameterBox →
      ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => F (t, y)) q‖ ≤
        A n * W ^ (A n) * (1 + p (n + inputLoss) z)

/-- A time-integrated angular Lipschitz bound. Parameter derivatives
are not placed in this Gronwall exponent. -/
def N04FlowAngularControl (F : ℝ × N04FlowPoint → ℝ) (Λ : ℝ) : Prop :=
  ∃ α : ℝ → ℝ, ContinuousOn α (Icc (0 : ℝ) 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ α t) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ n04FlowParameterBox, ∀ θ : ℝ,
      |deriv (fun η : ℝ => F (t, (v, η))) θ| ≤ α t) ∧
    (∫ t in (0 : ℝ)..1, α t) ≤ Λ

/-- The chosen family solves the actual scalar equation, including both
closed time endpoints. Its initial angle is independent of the external
parameters. -/
def N04FlowEquations (F : ℝ × N04FlowPoint → ℝ)
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) : Prop :=
  (∀ v θ, Θ v 0 θ = θ) ∧
    ∀ v θ, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => Θ v s θ)
        (F (t, (v, Θ v t θ))) (Icc (0 : ℝ) 1) t

/-- Genuine joint spatial smoothness, a periodic lift, actual angular
Jacobian bounds, and actual mixed Fréchet-jet bounds for the displacement. -/
def N04FlowJetBounds {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (B : ℕ → ℝ)
    (z : E) (W Λ : ℝ) (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1,
    ContDiff ℝ ∞ (fun q : N04FlowPoint => Θ q.1 t q.2) ∧
    (∀ v θ, Θ v t (θ + Real.pi) = Θ v t θ + Real.pi) ∧
    (∀ v ∈ n04FlowParameterBox, ∀ θ : ℝ,
      Real.exp (-Λ) ≤ deriv (fun η : ℝ => Θ v t η) θ ∧
        deriv (fun η : ℝ => Θ v t η) θ ≤ Real.exp Λ) ∧
    (∀ n : ℕ, ∀ q : N04FlowPoint, q.1 ∈ n04FlowParameterBox →
      ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => Θ y.1 t y.2 - y.2) q‖ ≤
        B n * W ^ (B n) * (1 + p (n + loss) z))

/-- One common low state order and one loss work at every spatial order.
The constants may depend on the supplied order-by-order field constants
and on the angular integral bound, but precede the state, the material
envelope, the actual field, and the actual chosen flow. -/
def N04FlowJetsTarget : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module ℝ E],
    ∀ p : ℕ → Seminorm ℝ E, Monotone p → HasInterpolation p →
    ∀ inputLoss : ℕ, ∃ base loss : ℕ,
    ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
    ∀ Λ : ℝ, 0 ≤ Λ →
    ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 →
      ∀ W : ℝ, 1 ≤ W →
      ∀ F : ℝ × N04FlowPoint → ℝ,
        ContDiff ℝ ∞ F →
        (∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi) →
        N04FlowRawJetBounds p inputLoss A z W F →
        N04FlowAngularControl F Λ →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
        N04FlowEquations F Θ →
        N04FlowJetBounds p loss B z W Λ Θ

end ContinuousFlexibility.Statements
