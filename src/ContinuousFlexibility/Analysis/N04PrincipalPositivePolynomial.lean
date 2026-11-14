import ContinuousFlexibility.Analysis.N04PrincipalPairAlgebra

/-!
# The three inverse-adjugate polynomials preserve paired bounds

One common scale and the same four inverse-derivative entries produce
all three principal components. Each product difference keeps exactly
one copy of the external material weight through the paired algebra.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- The inverse-adjugate formula with the reciprocal determinant already
supplied as a scalar input. -/
def n04PrincipalPositivePolynomial (v : Fin 3)
    (a b c H I r₁ r₂ t₁ t₂ : ℝ) : ℝ :=
  H ^ 2 * I *
    (if v = 0 then a * t₂ ^ 2 - 2 * b * t₂ * r₂ + c * r₂ ^ 2
     else if v = 1 then -(a * t₂ * t₁) + b * (t₂ * r₁ + r₂ * t₁) - c * r₂ * r₁
     else a * t₁ ^ 2 - 2 * b * t₁ * r₁ + c * r₁ ^ 2)

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {ι : Type*} {U : Set X} {Ω : Set PolarPoint}
  {p : ℕ → Seminorm ℝ X} {E W : ι → ℝ}
  {a b c H I r₁ r₂ t₁ t₂ : ι → X → PolarPoint → ℝ}
  {a₀ b₀ c₀ H₀ I₀ r₁₀ r₂₀ t₁₀ t₂₀ : ι → PolarPoint → ℝ}

theorem n04PrincipalPositivePolynomial_pairBounds
    (hp : Monotone p) (hInterp : HasInterpolation p) (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 < W m)
    (ha : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W a a₀)
    (hb : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W b b₀)
    (hc : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W c c₀)
    (hH : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W H H₀)
    (hI : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W I I₀)
    (hr₁ : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W r₁ r₁₀)
    (hr₂ : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W r₂ r₂₀)
    (ht₁ : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W t₁ t₁₀)
    (ht₂ : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W t₂ t₂₀)
    (v : Fin 3) :
    N04PrincipalPairBounds (U := U) (Ω := Ω) p E W
      (fun m x q => n04PrincipalPositivePolynomial v (a m x q) (b m x q) (c m x q)
        (H m x q) (I m x q) (r₁ m x q) (r₂ m x q) (t₁ m x q) (t₂ m x q))
      (fun m q => n04PrincipalPositivePolynomial v (a₀ m q) (b₀ m q) (c₀ m q)
        (H₀ m q) (I₀ m q) (r₁₀ m q) (r₂₀ m q) (t₁₀ m q) (t₂₀ m q)) := by
  have hscale := (hH.mul hH hp hInterp hU hΩ hE hW).mul hI hp hInterp hU hΩ hE hW
  have htwob := hb.add hb hp hU hΩ hE (fun m => (hW m).le)
  fin_cases v
  · have hfirst := ha.mul (ht₂.mul ht₂ hp hInterp hU hΩ hE hW) hp hInterp hU hΩ hE hW
    have hmiddle := (htwob.mul ht₂ hp hInterp hU hΩ hE hW).mul hr₂ hp hInterp hU hΩ hE hW
    have hlast := hc.mul (hr₂.mul hr₂ hp hInterp hU hΩ hE hW) hp hInterp hU hΩ hE hW
    have hsum := (hfirst.sub hmiddle hp hU hΩ hE (fun m => (hW m).le)).add hlast
      hp hU hΩ hE (fun m => (hW m).le)
    have hfinal := hscale.mul hsum hp hInterp hU hΩ hE hW
    simpa [n04PrincipalPositivePolynomial, pow_two, two_mul]
      using hfinal
  · have hfirst := ((ha.mul ht₂ hp hInterp hU hΩ hE hW).mul ht₁
      hp hInterp hU hΩ hE hW).neg hU hΩ
    have hcross := (ht₂.mul hr₁ hp hInterp hU hΩ hE hW).add
      (hr₂.mul ht₁ hp hInterp hU hΩ hE hW) hp hU hΩ hE (fun m => (hW m).le)
    have hmiddle := hb.mul hcross hp hInterp hU hΩ hE hW
    have hlast := (hc.mul hr₂ hp hInterp hU hΩ hE hW).mul hr₁ hp hInterp hU hΩ hE hW
    have hsum := (hfirst.add hmiddle hp hU hΩ hE (fun m => (hW m).le)).sub hlast
      hp hU hΩ hE (fun m => (hW m).le)
    have hfinal := hscale.mul hsum hp hInterp hU hΩ hE hW
    simpa [n04PrincipalPositivePolynomial, pow_two] using hfinal
  · have hfirst := ha.mul (ht₁.mul ht₁ hp hInterp hU hΩ hE hW) hp hInterp hU hΩ hE hW
    have hmiddle := (htwob.mul ht₁ hp hInterp hU hΩ hE hW).mul hr₁ hp hInterp hU hΩ hE hW
    have hlast := hc.mul (hr₁.mul hr₁ hp hInterp hU hΩ hE hW) hp hInterp hU hΩ hE hW
    have hsum := (hfirst.sub hmiddle hp hU hΩ hE (fun m => (hW m).le)).add hlast
      hp hU hΩ hE (fun m => (hW m).le)
    have hfinal := hscale.mul hsum hp hInterp hU hΩ hE hW
    simpa [n04PrincipalPositivePolynomial, pow_two, two_mul]
      using hfinal

end ContinuousFlexibility.Analysis
