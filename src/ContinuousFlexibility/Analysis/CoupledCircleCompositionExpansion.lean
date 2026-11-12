import ContinuousFlexibility.Analysis.CoupledCircleCompositionTerms

/-!
# Finite expansions for every angular composition jet

Repeated angular differentiation produces a finite list of actual terms.
The list retains the derivative budget needed by the fixed-loss estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements.CoupledCircleCompositionTerm

open Set
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {k : ℕ}

def derivativeTerms (t : CoupledCircleCompositionTerm k) :
    List (CoupledCircleCompositionTerm k) :=
  [t.chainIdentity, t.chainBase] ++ (List.ofFn t.baseDerivative) ++
    List.ofFn t.directionDerivative

theorem derivativeTerms_order (t : CoupledCircleCompositionTerm k) :
    ∀ τ ∈ t.derivativeTerms, τ.order ≤ t.order + 1 := by
  intro τ hτ
  simp only [derivativeTerms, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_ofFn] at hτ
  rcases hτ with ((rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩ <;>
    simp only [chainIdentity_order, chainBase_order, baseDerivative_order,
      directionDerivative_order, le_refl]

def evaluateTerms (L : List (CoupledCircleCompositionTerm k)) (v ψ : ℝ → ℝ)
    (w : Fin k → ℝ → ℝ) (θ : ℝ) : ℝ :=
  (L.map fun t => t.evaluate v ψ w θ).sum

@[simp] theorem evaluateTerms_nil (v ψ : ℝ → ℝ) (w : Fin k → ℝ → ℝ) (θ : ℝ) :
    evaluateTerms ([] : List (CoupledCircleCompositionTerm k)) v ψ w θ = 0 := rfl

@[simp] theorem evaluateTerms_cons (t : CoupledCircleCompositionTerm k)
    (L : List (CoupledCircleCompositionTerm k)) (v ψ : ℝ → ℝ)
    (w : Fin k → ℝ → ℝ) (θ : ℝ) :
    evaluateTerms (t :: L) v ψ w θ = t.evaluate v ψ w θ + evaluateTerms L v ψ w θ := rfl

theorem evaluateTerms_append (L R : List (CoupledCircleCompositionTerm k)) (v ψ : ℝ → ℝ)
    (w : Fin k → ℝ → ℝ) (θ : ℝ) :
    evaluateTerms (L ++ R) v ψ w θ = evaluateTerms L v ψ w θ + evaluateTerms R v ψ w θ := by
  simp only [evaluateTerms, List.map_append, List.sum_append]

theorem evaluateTerms_contDiff (L : List (CoupledCircleCompositionTerm k))
    {v ψ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hψ : ContDiff ℝ ∞ ψ)
    {w : Fin k → ℝ → ℝ} (hw : ∀ i, ContDiff ℝ ∞ (w i)) :
    ContDiff ℝ ∞ (evaluateTerms L v ψ w) := by
  induction L with
  | nil => exact contDiff_const
  | cons t L ih => exact (t.evaluate_contDiff hv hψ hw).add ih

theorem evaluate_derivativeTerms (t : CoupledCircleCompositionTerm k)
    {v ψ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hψ : ContDiff ℝ ∞ ψ)
    {w : Fin k → ℝ → ℝ} (hw : ∀ i, ContDiff ℝ ∞ (w i)) (θ : ℝ) :
    evaluateTerms t.derivativeTerms v ψ w θ = deriv (t.evaluate v ψ w) θ := by
  rw [t.evaluate_deriv hv hψ hw]
  simp only [evaluateTerms, derivativeTerms, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  ring

def differentiateTerms (L : List (CoupledCircleCompositionTerm k)) :
    List (CoupledCircleCompositionTerm k) := L.flatMap derivativeTerms

theorem differentiateTerms_order {L : List (CoupledCircleCompositionTerm k)} {n : ℕ}
    (hL : ∀ t ∈ L, t.order ≤ n) :
    ∀ t ∈ differentiateTerms L, t.order ≤ n + 1 := by
  intro t ht
  obtain ⟨τ, hτ, htτ⟩ := List.mem_flatMap.mp ht
  exact (τ.derivativeTerms_order t htτ).trans (Nat.add_le_add_right (hL τ hτ) 1)

theorem evaluate_differentiateTerms (L : List (CoupledCircleCompositionTerm k))
    {v ψ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hψ : ContDiff ℝ ∞ ψ)
    {w : Fin k → ℝ → ℝ} (hw : ∀ i, ContDiff ℝ ∞ (w i)) (θ : ℝ) :
    evaluateTerms (differentiateTerms L) v ψ w θ = deriv (evaluateTerms L v ψ w) θ := by
  induction L with
  | nil =>
    change 0 = deriv (fun _ : ℝ => (0 : ℝ)) θ
    simp only [deriv_const]
  | cons t L ih =>
    change evaluateTerms (t.derivativeTerms ++ differentiateTerms L) v ψ w θ = _
    rw [evaluateTerms_append, evaluate_derivativeTerms t hv hψ hw, ih]
    exact (deriv_add ((t.evaluate_contDiff hv hψ hw).differentiable (by simp) θ)
      ((evaluateTerms_contDiff L hv hψ hw).differentiable (by simp) θ)).symm

def expansion (r k : ℕ) : ℕ → List (CoupledCircleCompositionTerm k)
  | 0 => [initial r k]
  | b + 1 => differentiateTerms (expansion r k b)

theorem expansion_order (r k b : ℕ) :
    ∀ t ∈ expansion r k b, t.order ≤ r + b := by
  induction b with
  | zero => simp only [expansion, List.mem_singleton, forall_eq, initial_order, Nat.add_zero, le_refl]
  | succ b ih =>
    simpa only [expansion, Nat.add_assoc] using differentiateTerms_order ih

theorem evaluate_expansion (r k b : ℕ) {v ψ : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hψ : ContDiff ℝ ∞ ψ)
    {w : Fin k → ℝ → ℝ} (hw : ∀ i, ContDiff ℝ ∞ (w i)) :
    evaluateTerms (expansion r k b) v ψ w =
      iteratedDeriv b (fun θ => iteratedDeriv r v (θ + ψ θ) * ∏ i, w i θ) := by
  induction b with
  | zero =>
    funext θ
    simp only [expansion, evaluateTerms_cons, evaluateTerms_nil, add_zero,
      initial_evaluate, iteratedDeriv_zero]
  | succ b ih =>
    funext θ
    rw [expansion, evaluate_differentiateTerms _ hv hψ hw, ih, iteratedDeriv_succ]

end ContinuousFlexibility.Statements.CoupledCircleCompositionTerm
