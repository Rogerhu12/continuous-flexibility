import ContinuousFlexibility.Analysis.PositiveConformalBoundaryJets
import ContinuousFlexibility.Analysis.PositiveFiberInterpolationSymmetry
import ContinuousFlexibility.Analysis.AngularTaylorPolynomial

/-!
# Circle symmetries of the finite conformal coordinate construction

The two matrix traces have the symmetries of a positive even metric:
d is even and e is odd, and both are periodic. The finite recursion
therefore gives an even radial coordinate and an odd degree-one angular
lift. These are properties of the constructed data and polynomial.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem conformal_periodic_deriv
    {f : ℝ → ℝ} {T : ℝ} (hf : ContDiff ℝ ∞ f) (hp : Periodic f T) :
    Periodic (deriv f) T := by
  intro θ
  have h₁ := ((hf.differentiable (by simp) (θ + T)).hasDerivAt).comp θ
    ((hasDerivAt_id θ).add_const T)
  have he : (f ∘ fun t : ℝ => t + T) = f := funext hp
  simp only [id_eq] at h₁
  rw [he, mul_one] at h₁
  exact h₁.deriv.symm

private theorem conformal_deriv_reflect
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (side : Bool)
    (he : ∀ θ, f (-θ) = if side then -f θ else f θ) (θ : ℝ) :
    deriv f (-θ) = if side then deriv f θ else -deriv f θ := by
  have h₁ := ((hf.differentiable (by simp) (-θ)).hasDerivAt).comp θ
    ((hasDerivAt_id θ).neg)
  cases side
  · have he' : (f ∘ fun t : ℝ => -t) = f := funext he
    rw [he'] at h₁
    have h := h₁.unique (hf.differentiable (by simp) θ).hasDerivAt
    change deriv f (-θ) = -deriv f θ
    linarith
  · have he' : (f ∘ fun t : ℝ => -t) = fun t => -f t := funext he
    rw [he'] at h₁
    have h := h₁.unique (hf.differentiable (by simp) θ).hasDerivAt.neg
    change deriv f (-θ) = deriv f θ
    linarith

/-- Every data derivative is periodic, including the derivative of the
zeroth angular lift. Positive radial orders themselves are periodic. -/
theorem positiveConformalBoundaryData_periodic
    {D E : ℕ → ℝ → ℝ} {T : ℝ}
    (hD : ∀ j, ContDiff ℝ ∞ (D j)) (hE : ∀ j, ContDiff ℝ ∞ (E j))
    (hDp : ∀ j, Periodic (D j) T) (hEp : ∀ j, Periodic (E j) T)
    (v : ℝ) (n : ℕ) (side : Bool) :
    Periodic (deriv (positiveConformalBoundaryData D E v n side)) T ∧
      (0 < n → Periodic (positiveConformalBoundaryData D E v n side) T) := by
  induction n using Nat.strong_induction_on generalizing side with
  | h n ih =>
      cases n with
      | zero =>
          refine ⟨?_, by omega⟩
          intro θ
          have he : positiveConformalBoundaryData D E v 0 side =
              (fun η => if side then η else v) := by
            funext η
            rw [positiveConformalBoundaryData]
          rw [he]
          cases side <;> simp
      | succ n =>
          have hp : Periodic (positiveConformalBoundaryData D E v (n + 1) side) T := by
            intro θ
            simp only [positiveConformalBoundaryData]
            apply Finset.sum_congr rfl
            intro j _
            rw [hEp j θ, hDp j θ,
              (ih (n - j) (by omega) side).1 θ,
              (ih (n - j) (by omega) (!side)).1 θ]
          exact ⟨conformal_periodic_deriv
            (contDiff_positiveConformalBoundaryData hD hE v (n + 1) side) hp, fun _ => hp⟩

theorem positiveConformalBoundaryData_reflect
    {D E : ℕ → ℝ → ℝ}
    (hD : ∀ j, ContDiff ℝ ∞ (D j)) (hE : ∀ j, ContDiff ℝ ∞ (E j))
    (hDe : ∀ j θ, D j (-θ) = D j θ) (hEo : ∀ j θ, E j (-θ) = -E j θ)
    (v : ℝ) (n : ℕ) (side : Bool) (θ : ℝ) :
    positiveConformalBoundaryData D E v n side (-θ) =
      if side then -positiveConformalBoundaryData D E v n side θ
      else positiveConformalBoundaryData D E v n side θ := by
  induction n using Nat.strong_induction_on generalizing side θ with
  | h n ih =>
      cases n with
      | zero => cases side <;> simp only [positiveConformalBoundaryData,
          Bool.false_eq_true, ↓reduceIte]
      | succ n =>
          have hd (j : ℕ) (s : Bool) :
              deriv (positiveConformalBoundaryData D E v (n - j) s) (-θ) =
                if s then deriv (positiveConformalBoundaryData D E v (n - j) s) θ
                else -deriv (positiveConformalBoundaryData D E v (n - j) s) θ :=
            conformal_deriv_reflect (contDiff_positiveConformalBoundaryData hD hE v (n - j) s)
              s (fun η => ih (n - j) (by omega) s η) θ
          cases side
          · simp only [positiveConformalBoundaryData, Bool.not_false, Bool.false_eq_true,
              ↓reduceIte]
            apply Finset.sum_congr rfl
            intro j _
            rw [hDe j θ, hEo j θ, hd j false, hd j true]
            simp only [Bool.false_eq_true, ↓reduceIte]
            ring
          · simp only [positiveConformalBoundaryData, Bool.not_true, ↓reduceIte]
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [hDe j θ, hEo j θ, hd j true, hd j false]
            simp only [Bool.false_eq_true, ↓reduceIte]
            ring

/-- Only the actual boundary traces need the metric symmetries. The
coefficient fields may have arbitrary values away from the boundary. -/
theorem positiveConformalBoundaryPolynomial_symmetry
    {d e : PolarPoint → ℝ} {c T : ℝ}
    (hd : ∀ θ, ContDiffAt ℝ ∞ d (c, θ))
    (he : ∀ θ, ContDiffAt ℝ ∞ e (c, θ))
    (hdp : ∀ j, Periodic (radialBoundaryJet d c j) T)
    (hep : ∀ j, Periodic (radialBoundaryJet e c j) T)
    (hde : ∀ j θ, radialBoundaryJet d c j (-θ) = radialBoundaryJet d c j θ)
    (heo : ∀ j θ, radialBoundaryJet e c j (-θ) = -radialBoundaryJet e c j θ)
    (N : ℕ) (v r θ : ℝ) :
    let X := positiveConformalBoundaryPolynomial N c v d e
    X false (r, θ + T) = X false (r, θ) ∧
      X true (r, θ + T) = X true (r, θ) + T ∧
      X false (r, -θ) = X false (r, θ) ∧
      X true (r, -θ) = -X true (r, θ) := by
  have hD := contDiff_radialBoundaryJet_of_contDiffAt c hd
  have hE := contDiff_radialBoundaryJet_of_contDiffAt c he
  have hp := positiveConformalBoundaryData_periodic hD hE hdp hep v
  have hr := positiveConformalBoundaryData_reflect hD hE hde heo v
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply boundaryTaylorPolynomial_angleInvariant (fun η => η + T)
    intro j _ η
    by_cases hj : j = 0
    · subst j
      simp only [positiveConformalBoundaryData, Bool.false_eq_true, ↓reduceIte]
    · exact (hp j false).2 (Nat.pos_of_ne_zero hj) η
  · apply boundaryTaylorPolynomial_period_add
    · intro η
      simp only [positiveConformalBoundaryData, ↓reduceIte]
    · intro j hj _
      exact (hp j true).2 hj
  · apply boundaryTaylorPolynomial_angleInvariant (fun η => -η)
    intro j _ η
    exact hr j false η
  · apply boundaryTaylorPolynomial_reflect
    intro j _ η
    exact hr j true η

end ContinuousFlexibility.Analysis
