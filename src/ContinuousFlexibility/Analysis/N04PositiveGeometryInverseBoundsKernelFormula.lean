import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsRadial
import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsKernelCalculus

/-!
# The literal finite radial collar as a scalar integral

The free finite coefficients are the positive endpoint derivatives.
Taking the actual radial derivative of the original Taylor polynomial
gives the displayed polynomial slope.  This identifies the existing
collar, including its fixed normalization, with an explicit integral
formula suitable for uniform coefficient and radial jet estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

def n04PositiveGeometry_taylorSlopeKernel (n : ℕ) (c : ℝ)
    (a : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), a j / (j.val.factorial : ℝ) * (t - c) ^ j.val

def n04PositiveGeometry_collarSlopeKernel (n : ℕ) (l r : ℝ) (root : Bool)
    (a : Fin (n + 1) → ℝ) (side : Bool) (t : ℝ) : ℝ :=
  if side = root then
    n04PositiveGeometry_taylorSlopeKernel n (if root then r else l) a t
  else 1

def n04PositiveGeometry_scalarCollarKernel (n : ℕ) (l r δ : ℝ) (root : Bool)
    (p : (Fin (n + 1) → ℝ) × ℝ) : ℝ :=
  positiveReferenceCollarCoordinate n l r δ l (r - l) root
    (n04PositiveGeometry_radialCoefficientField n l r (fun _ => p.1) root)
    Prod.fst (p.2, 0)

theorem n04PositiveGeometry_scalarCollarKernel_formula
    (n : ℕ) (l r δ : ℝ) (root : Bool) (p : (Fin (n + 1) → ℝ) × ℝ) :
    n04PositiveGeometry_scalarCollarKernel n l r δ root p =
      l + (r - l) * positiveReferenceCoordinate l r δ
        (fun t => n04PositiveGeometry_collarSlopeKernel n l r root p.1 false t / (r - l))
        (fun t => n04PositiveGeometry_collarSlopeKernel n l r root p.1 true t / (r - l)) p.2 := by
  let A : ℕ → ℝ → ℝ :=
    n04PositiveGeometry_radialCoefficientField n l r (fun _ => p.1) root
  have hA (j : ℕ) (_hj : j ≤ n + 1) : ContDiff ℝ ∞ (A j) := by
    cases j <;> exact contDiff_const
  let Q := positiveReferenceCollarField n l r root A Prod.fst
  have hQ (side : Bool) : ContDiff ℝ ∞ (Q side) := by
    by_cases hs : side = root
    · simpa only [Q, positiveReferenceCollarField, if_pos hs] using
        contDiff_boundaryTaylorPolynomial hA (if side then r else l)
    · simpa only [Q, positiveReferenceCollarField, if_neg hs] using
        (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : PolarPoint → ℝ))
  have hslope (side : Bool) (t : ℝ) :
      radialPartial (Q side) (t, 0) =
        n04PositiveGeometry_collarSlopeKernel n l r root p.1 side t := by
    by_cases hs : side = root
    · subst side
      have hrad := (hasDerivAt_boundaryTaylorPolynomial_radial n
        (if root then r else l) t 0 A).deriv
      rw [← deriv_cylinder_radial_slice ((hQ root).differentiable (by simp)) t 0]
      simp only [Q, positiveReferenceCollarField, if_pos rfl, ite_true] at hrad ⊢
      rw [hrad]
      simp only [n04PositiveGeometry_collarSlopeKernel, if_pos rfl, ite_true,
        boundaryTaylorPolynomial, n04PositiveGeometry_taylorSlopeKernel, Finset.sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [show A (j.val + 1) 0 = p.1 j from
        n04PositiveGeometry_radialCoefficientField_succ n l r
          (fun _ => p.1) root j 0]
    · have hfield : Q side = Prod.fst := by
        simp only [Q, positiveReferenceCollarField, if_neg hs]
      rw [hfield, radialPartial_fst]
      simp only [n04PositiveGeometry_collarSlopeKernel, if_neg hs]
  have hscaled (side : Bool) :
      (fun t => radialPartial (Q side) (t, 0) / (r - l)) =
        (fun t => n04PositiveGeometry_collarSlopeKernel n l r root p.1 side t / (r - l)) := by
    funext t
    rw [hslope side t]
  change l + (r - l) * positiveReferenceCoordinate l r δ
    (fun t => radialPartial (Q false) (t, 0) / (r - l))
    (fun t => radialPartial (Q true) (t, 0) / (r - l)) p.2 = _
  rw [hscaled false, hscaled true]

section SlopeBounds

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {W : I → ℝ} {p : I → E}

/-- The finite Taylor slope is polynomial in its actual coefficients and
radial argument.  Every derivative has a component polynomial envelope
whenever those input fields do. -/
theorem n04PositiveGeometry_taylorSlopeKernel_bounds
    (hW : ∀ i, 1 ≤ W i) (n : ℕ)
    (a : I → E → Fin (n + 1) → ℝ) (t : I → E → ℝ) (c : I → ℝ)
    (ha : ∀ j, N04PositiveKernelJetBounds W p (fun i y => a i y j))
    (ht : N04PositiveKernelJetBounds W p t)
    (hc : HasPositiveEnvelope W (fun i => |c i|)) :
    N04PositiveKernelJetBounds W p
      (fun i y => n04PositiveGeometry_taylorSlopeKernel n (c i) (a i y) (t i y)) := by
  have hshift := ht.sub (N04PositiveKernelJetBounds.const (p := p) hW c hc) hW
  apply N04PositiveKernelJetBounds.sum hW Finset.univ
  intro j _
  have hfact := N04PositiveKernelJetBounds.const (p := p) hW
    (fun _ => ((j.val.factorial : ℝ)⁻¹))
    (hasPositiveEnvelope_const W hW |(j.val.factorial : ℝ)⁻¹|)
  simpa only [div_eq_mul_inv] using ((ha j).mul hfact hW).mul (hshift.pow hW j.val) hW

theorem n04PositiveGeometry_collarSlopeKernel_bounds
    (hW : ∀ i, 1 ≤ W i) (n : ℕ) (root side : Bool)
    (a : I → E → Fin (n + 1) → ℝ) (t : I → E → ℝ) (l r : I → ℝ)
    (ha : ∀ j, N04PositiveKernelJetBounds W p (fun i y => a i y j))
    (ht : N04PositiveKernelJetBounds W p t)
    (hl : HasPositiveEnvelope W (fun i => |l i|))
    (hr : HasPositiveEnvelope W (fun i => |r i|)) :
    N04PositiveKernelJetBounds W p
      (fun i y => n04PositiveGeometry_collarSlopeKernel n (l i) (r i) root (a i y) side (t i y)) := by
  by_cases hs : side = root
  · simp only [n04PositiveGeometry_collarSlopeKernel, if_pos hs]
    apply n04PositiveGeometry_taylorSlopeKernel_bounds hW n a t
      (fun i => if root then r i else l i) ha ht
    cases root <;> assumption
  · simp only [n04PositiveGeometry_collarSlopeKernel, if_neg hs]
    exact N04PositiveKernelJetBounds.const hW (fun _ => 1)
      (by simpa only [abs_one] using hasPositiveEnvelope_const W hW 1)

end SlopeBounds

end ContinuousFlexibility.Analysis
