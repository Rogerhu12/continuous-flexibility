module

public import ContinuousFlexibility.Analysis.RootDividedHeight
public import ContinuousFlexibility.Analysis.N04NegativeHeightIdentity
public import ContinuousFlexibility.Analysis.N03UniformRootBandGeometry

/-!
# The actual stored height on the fixed uncorrected root band

The existing determinant identity for the actual canonical height and
the genuine root division identify the same height with a smooth
formula. All premises are actual whole-band chart/coefficient facts
already supplied by the fixed-cutoff construction, with the original
chosen inverse input and scale retained.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n03_fixedRoot_height_eq_dividedHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C E L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {g : ℝ → ℝ} {R δ x θ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hx : 0 < x)
    (hxR : δ * x ≤ R / 4)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) R)
    {G : ℝ × ℝ × ℝ → ℝ}
    (hown : (n01ComponentRoot C m rightEnd +
      n01ComponentRootOrientation rightEnd * (δ * x), θ) ∈ physicalPieceOpen S K z
        (if rightEnd then (K.cutPair m).2 else (K.cutPair m).1))
    (hchart : K.chart z (if rightEnd then (K.cutPair m).2 else (K.cutPair m).1)
      (n01ComponentRoot C m rightEnd + n01ComponentRootOrientation rightEnd * (δ * x), θ) =
        extendedRootEvenOddChart G (x, θ))
    (hcoeff : let p : PolarPoint := (n01ComponentRoot C m rightEnd +
        n01ComponentRootOrientation rightEnd * (δ * x), θ)
      (L.coefficients z).a p = (originalCoefficients D S C z).a p ∧
      (L.coefficients z).b p = (originalCoefficients D S C z).b p ∧
      (L.coefficients z).c p = (originalCoefficients D S C z).c p) :
    let r := n01ComponentRoot C m rightEnd
    let σ := n01ComponentRootOrientation rightEnd
    let V : PolarPoint → ℝ := fun q => rootCoefficientRadialFactor D.w g
      (stateProfile D S C z.1) (stateHeight D S C z) r σ (δ * q.1, q.2)
    K.height z (if rightEnd then (K.cutPair m).2 else (K.cutPair m).1)
      (r + σ * (δ * x), θ) = rootDividedHeight δ V G (x, θ) := by
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let p : PolarPoint := (r + σ * (δ * x), θ)
  let V : PolarPoint → ℝ := fun q => rootCoefficientRadialFactor D.w g
    (stateProfile D S C z.1) (stateHeight D S C z) r σ (δ * q.1, q.2)
  have hq : (δ * x, θ) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [mul_pos hδ hx]
  obtain ⟨hr, hw, hg, hD, hQ, hweq, hdivide⟩ := hstrip (δ * x, θ) hq
  have hV : 0 < V (x, θ) := by
    change 0 < rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ (δ * x, θ)
    rw [rootCoefficientRadialFactor_eq hr hw hg hD hQ.ne']
    exact div_pos (rootProfileRadicand_pos hr hw hg) (pow_pos hD 2)
  have hfactor := rootCoefficientDiscriminant_factorization
    ((contDiff_stateProfile_of_n01 hS hT hN z.1).differentiable (by simp) _)
    hr hw hg hD hQ.ne' hweq hdivide
  have hdisc : (L.coefficients z).b p ^ 2 -
      (L.coefficients z).a p * (L.coefficients z).c p = (δ * x) * V (x, θ) := by
    rw [hcoeff.1, hcoeff.2.1, hcoeff.2.2]
    exact hfactor
  have hh := (negativeCutPair_height_eq_fourthRoot hS hT hN hL hA hB hz hs m rightEnd
    p hown).2
  rw [hchart] at hh
  exact hh.trans (rootDividedHeight_eq_of_radial_factor hδ hx hV hdisc)

end ContinuousFlexibility.Analysis
