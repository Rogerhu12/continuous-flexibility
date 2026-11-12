import ContinuousFlexibility.Analysis.N06RootBoundaryPolynomialBounds

/-!
# Boundary difference estimates for the actual root-flow witnesses

The estimates are transferred from the explicit finite formulas to the
same G and G0 that solve the true root transport equations. No state
continuity or chosen derivative of either witness is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

namespace N04bRootCoordinateProperties

variable {d c d₀ c₀ : PolarPoint → ℝ} {β β₀ : ℝ → ℝ}
  {Φ Φ₀ : ℝ → ℝ → ℝ} {R R₀ σ σ₀ : ℝ}
  {G G₀ : ℝ × ℝ × ℝ → ℝ}

/-- The current and reference root-flow witnesses inherit the polynomial
jet comparison of their actual physical inputs. The output is exactly
the boundary data used by the order-four chart / order-three height patch. -/
theorem n06_boundary_witness_jet_comparison
    (P : N04bRootCoordinateProperties d c β Φ R σ G)
    (P₀ : N04bRootCoordinateProperties d₀ c₀ β₀ Φ₀ R₀ σ₀ G₀)
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hd₀ : ContDiff ℝ ∞ d₀) (hc₀ : ContDiff ℝ ∞ c₀)
    (n : ℕ) {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hinput : ∀ i, N06RootJetPair (n + 3) M δ
      (n06RootBoundaryInputs d c β i) (n06RootBoundaryInputs d₀ c₀ β₀ i)) :
    let A := n06RootBoundaryPolynomialCost n M
    N06RootJetPair n A δ
      (radialBoundaryJet (extendedRootEven G) 0 1)
      (radialBoundaryJet (extendedRootEven G₀) 0 1) ∧
    N06RootJetPair n A δ
      (radialBoundaryJet (extendedRootEven G) 0 2)
      (radialBoundaryJet (extendedRootEven G₀) 0 2) ∧
    N06RootJetPair n A δ
      (radialBoundaryJet (extendedRootEven G) 0 3)
      (radialBoundaryJet (extendedRootEven G₀) 0 3) ∧
    N06RootJetPair n A δ
      (radialBoundaryJet (extendedRootEven G) 0 4)
      (radialBoundaryJet (extendedRootEven G₀) 0 4) ∧
    N06RootJetPair n A δ
      (radialBoundaryJet (extendedRootOddCoefficient G) 0 0)
      (radialBoundaryJet (extendedRootOddCoefficient G₀) 0 0) ∧
    N06RootJetPair n A δ
      (radialBoundaryJet (extendedRootOddCoefficient G) 0 1)
      (radialBoundaryJet (extendedRootOddCoefficient G₀) 0 1) ∧
    N06RootJetPair n A δ
      (radialBoundaryJet (extendedRootOddCoefficient G) 0 2)
      (radialBoundaryJet (extendedRootOddCoefficient G₀) 0 2) ∧
    N06RootJetPair n A δ
      (radialBoundaryJet (extendedRootOddCoefficient G) 0 3)
      (radialBoundaryJet (extendedRootOddCoefficient G₀) 0 3) := by
  obtain ⟨hE₁, hE₂, hE₃, hE₄, hO₀, hO₁, hO₂, hO₃⟩ :=
    P.n06_boundary_finite_formulas hd hc
  obtain ⟨hE₁₀, hE₂₀, hE₃₀, hE₄₀, hO₀₀, hO₁₀, hO₂₀, hO₃₀⟩ :=
    P₀.n06_boundary_finite_formulas hd₀ hc₀
  simpa only [hE₁, hE₂, hE₃, hE₄, hO₀, hO₁, hO₂, hO₃,
    hE₁₀, hE₂₀, hE₃₀, hE₄₀, hO₀₀, hO₁₀, hO₂₀, hO₃₀] using
      n06_rootBoundaryFormulas_jet_comparison n hM hδ
        (n06RootBoundaryInputs d c β) (n06RootBoundaryInputs d₀ c₀ β₀) hinput

end N04bRootCoordinateProperties

end ContinuousFlexibility.Analysis
