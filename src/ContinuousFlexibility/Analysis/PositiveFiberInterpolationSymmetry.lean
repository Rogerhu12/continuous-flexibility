import ContinuousFlexibility.Analysis.PositiveReferenceCollarFactory

/-!
# Angular symmetries of the actual positive interpolation

The parameterized primitive uses the same radial integrals at transformed
angles. Thus any pointwise angular invariance of the supplied endpoint
fields is retained, including periodicity and evenness. The radial jets
and finite Taylor polynomials retain the same invariance.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem radialBoundaryJet_angleInvariant
    {F : PolarPoint → ℝ} (τ : ℝ → ℝ)
    (hF : ∀ x θ, F (x, τ θ) = F (x, θ)) (c : ℝ) (j : ℕ) (θ : ℝ) :
    radialBoundaryJet F c j (τ θ) = radialBoundaryJet F c j θ := by
  have he : (fun x => F (x, τ θ)) = (fun x => F (x, θ)) := funext (fun x => hF x θ)
  simp only [radialBoundaryJet, he]

theorem boundaryTaylorPolynomial_angleInvariant
    {n : ℕ} {A : ℕ → ℝ → ℝ} (τ : ℝ → ℝ)
    (hA : ∀ j ≤ n, ∀ θ, A j (τ θ) = A j θ) (c x θ : ℝ) :
    boundaryTaylorPolynomial n c A (x, τ θ) = boundaryTaylorPolynomial n c A (x, θ) := by
  unfold boundaryTaylorPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) θ]

theorem radialPartial_angleInvariant
    {F : PolarPoint → ℝ} (hF : Differentiable ℝ F) (τ : ℝ → ℝ)
    (hInv : ∀ x θ, F (x, τ θ) = F (x, θ)) (x θ : ℝ) :
    radialPartial F (x, τ θ) = radialPartial F (x, θ) := by
  rw [← deriv_cylinder_radial_slice hF x (τ θ),
    ← deriv_cylinder_radial_slice hF x θ]
  have he : (fun r => F (r, τ θ)) = (fun r => F (r, θ)) :=
    funext (fun r => hInv r θ)
  rw [he]

theorem parameterizedPositiveReferenceCoordinate_angleInvariant
    {A : Bool → PolarPoint → ℝ} (τ : ℝ → ℝ)
    (hA : ∀ side x θ, A side (x, τ θ) = A side (x, θ))
    (l r δ v m x θ : ℝ) :
    parameterizedPositiveReferenceCoordinate l r δ v m A (x, τ θ) =
      parameterizedPositiveReferenceCoordinate l r δ v m A (x, θ) := by
  have he (side : Bool) :
      (fun t => A side (t, τ θ) / m) = (fun t => A side (t, θ) / m) := by
    funext t
    rw [hA side t θ]
  simp only [parameterizedPositiveReferenceCoordinate, he]

/-- This applies to the explicit coordinate selected by the endpoint
factory, so no symmetry of a proposed output chart is assumed. -/
theorem positiveReferenceCollarCoordinate_angleInvariant
    {n : ℕ} {A : ℕ → ℝ → ℝ} {Ref : PolarPoint → ℝ}
    (hA : ∀ j ≤ n + 1, ContDiff ℝ ∞ (A j)) (hRef : ContDiff ℝ ∞ Ref)
    (τ : ℝ → ℝ)
    (hAInv : ∀ j ≤ n + 1, ∀ θ, A j (τ θ) = A j θ)
    (hRefInv : ∀ x θ, Ref (x, τ θ) = Ref (x, θ))
    (l r δ v m : ℝ) (root : Bool) (x θ : ℝ) :
    positiveReferenceCollarCoordinate n l r δ v m root A Ref (x, τ θ) =
      positiveReferenceCollarCoordinate n l r δ v m root A Ref (x, θ) := by
  apply parameterizedPositiveReferenceCoordinate_angleInvariant τ
  intro side s η
  have hsmooth : ContDiff ℝ ∞ (positiveReferenceCollarField n l r root A Ref side) := by
    by_cases hs : side = root
    · simpa only [positiveReferenceCollarField, if_pos hs] using
        contDiff_boundaryTaylorPolynomial hA (if side then r else l)
    · simpa only [positiveReferenceCollarField, if_neg hs] using hRef
  apply radialPartial_angleInvariant (hsmooth.differentiable (by simp)) τ
  intro t ζ
  by_cases hs : side = root
  · simpa only [positiveReferenceCollarField, if_pos hs] using
      boundaryTaylorPolynomial_angleInvariant τ hAInv (if side then r else l) t ζ
  · simpa only [positiveReferenceCollarField, if_neg hs] using hRefInv t ζ

end ContinuousFlexibility.Analysis
