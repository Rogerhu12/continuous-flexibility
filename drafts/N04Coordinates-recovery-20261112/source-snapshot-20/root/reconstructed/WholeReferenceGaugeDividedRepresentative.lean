import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData
import ContinuousFlexibility.Analysis.CanonicalDividedRepresentative

/-!
# The removable representative of the same fixed-reference atlas

The raw principal fields of the positive reference gauge are the actual
stored coefficient fields. A cubic representative for their difference
therefore identifies the existing dividedDifference, including every
ordinary interior mixed derivative. No atlas field is replaced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

theorem n04WholeReferenceGaugeAtlasData_divided_matches_representative
    {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) {base : ℕ} {ε : ℝ}
    (hV : N04PartB S C L
      (n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N) base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (v : Fin 3) {q : PolarPoint → ℝ} (hq : ContDiff ℝ ∞ q)
    (hfactor : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ),
      canonicalCoefficientComponent v
        (inverseChartPrincipalCoefficients (L.coefficients z)
          (wholePositiveReferenceGaugeChart (ψ i) (σ z i))
          (wholePositiveReferenceGaugeInverse (τ z i) (χ i))
          (wholePositiveReferenceGaugeHeight (h₀ i) (σ z i) (Q z i))) p -
      canonicalCoefficientComponent v
        (inverseChartPrincipalCoefficients (L.coefficients (C.referenceState, 0))
          (wholePositiveReferenceGaugeChart (ψ i) (σ (C.referenceState, 0) i))
          (wholePositiveReferenceGaugeInverse (τ (C.referenceState, 0) i) (χ i))
          (wholePositiveReferenceGaugeHeight (h₀ i)
            (σ (C.referenceState, 0) i) (Q (C.referenceState, 0) i))) p =
        (p.1 * (1 - p.1)) ^ 3 * q p) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    EqOn (canonicalCoefficientComponent v (V.dividedDifference z m)) q
        (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ (canonicalCoefficientComponent v (V.dividedDifference z m))
        (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) ∧
      ∀ a b : ℕ,
        EqOn (mixedDerivative a b (canonicalCoefficientComponent v (V.dividedDifference z m)))
          (mixedDerivative a b q) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  have hf := n04WholeReferenceGaugeAtlasData_positive_fields
    C L K e cell ψ χ h₀ τ σ Q N z m i hi
  rcases hf with ⟨hl, hr, _, _, _, _, hm, _, _, _, hc, _⟩
  change V.left m = 0 at hl
  change V.right m = 1 at hr
  change V.positive m = true at hm
  change V.coefficients z m = _ at hc
  have hf₀ := n04WholeReferenceGaugeAtlasData_positive_fields
    C L K e cell ψ χ h₀ τ σ Q N (C.referenceState, 0) m i hi
  rcases hf₀ with ⟨_, _, _, _, _, _, _, _, _, _, hc₀, _⟩
  change V.coefficients (C.referenceState, 0) m = _ at hc₀
  have hdomain : canonicalOpen S V m = Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
    change Ioo (V.left m) (V.right m) ×ˢ (univ : Set ℝ) = _
    rw [hl, hr]
  have hnum : ∀ p ∈ canonicalOpen S V m,
      canonicalCoefficientNumerator S C V z m v p =
        ((p.1 - V.left m) * (V.right m - p.1)) ^ 3 * q p := by
    intro p hp
    have hp' : p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := hdomain ▸ hp
    have hpclosed : p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) :=
      ⟨⟨hp'.1.1.le, hp'.1.2.le⟩, hp'.2⟩
    change canonicalCoefficientComponent v (V.coefficients z m) p -
      canonicalCoefficientComponent v (V.coefficients (C.referenceState, 0) m) p = _
    rw [hc, hc₀, hl, hr, sub_zero]
    exact hfactor p hpclosed
  simpa only [hdomain] using
    (canonicalDividedComponent_matches_cubicRepresentative hV hz hs m hm v hq hnum)

end ContinuousFlexibility.Analysis
