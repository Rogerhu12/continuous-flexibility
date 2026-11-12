import ContinuousFlexibility.Analysis.N06WeakCylinderGraph

/-!
# One family of weak modal representatives for every finite cutoff

The actual cylinder equation gives all countably many modal equations.
Choosing their H2 representatives once makes every finite reconstruction
and every finite tail use the same radial functions and derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- A single family of genuine H2 representatives works simultaneously for all
finite Fourier cutoffs and their tails. -/
theorem n06_unit_weakPDE_all_modes
    {U F : PolarPoint → ℝ} {a c V q : ℝ → ℝ} {K : ℝ}
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hU : MemLp U 2 (cylinderWindowMeasure 0))
    (hF : MemLp F 2 (cylinderWindowMeasure 0))
    (hweak : n06UnitReferenceWeakEquation a c V U F)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K) :
    ∃ v : ℕ → ℝ → ℝ,
      (∀ i, N06WeakModeRepresentative a c V
        (n06HalfCosineCoefficient U i) (n06HalfCosineCoefficient F i) (v i)
          (((2 * i : ℕ) : ℝ))) ∧
      ∀ i, n06WeakModeGraphSquare (((2 * i : ℕ) : ℝ)) (v i) ≤
        16384 * K ^ 10 *
          ((∫ y in (0 : ℝ)..1, n06HalfCosineCoefficient F i y ^ 2) +
            ∫ y in (0 : ℝ)..1, n06HalfCosineCoefficient U i y ^ 2) := by
  have hex (i : ℕ) : ∃ v : ℝ → ℝ,
      N06WeakModeRepresentative a c V
        (n06HalfCosineCoefficient U i) (n06HalfCosineCoefficient F i) v
          (((2 * i : ℕ) : ℝ)) ∧
      n06WeakModeGraphSquare (((2 * i : ℕ) : ℝ)) v ≤
        16384 * K ^ 10 *
          ((∫ y in (0 : ℝ)..1, n06HalfCosineCoefficient F i y ^ 2) +
            ∫ y in (0 : ℝ)..1, n06HalfCosineCoefficient U i y ^ 2) := by
    obtain ⟨v, huv, hv, hvAC, hv₀, hv₁, hv₂, hode, hbound⟩ :=
      n06_weakGraphStatement a c V q (n06HalfCosineCoefficient U i)
        (n06HalfCosineCoefficient F i) (((2 * i : ℕ) : ℝ)) K ha hc hV hq
        (n06_halfCosineCoefficient_memLp hU i) (n06_halfCosineCoefficient_memLp hF i)
        (n06_unit_weakEquation_modal ha hc hV hU hF hweak i)
        hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂
    exact ⟨v, ⟨huv, hv, hvAC, hv₀, hv₁, hv₂, hode⟩, hbound⟩
  choose v hv hb using hex
  exact ⟨v, hv, hb⟩

end ContinuousFlexibility.Analysis
