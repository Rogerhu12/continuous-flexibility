import ContinuousFlexibility.Analysis.N06WeakCylinderPDE
import ContinuousFlexibility.Analysis.N06WeakFiniteGraph

/-!
# From the actual weak cylinder PDE to finite graph control

Every modal equation and every graph-field membership below is derived
from the original two-variable weak equation and its L2 representatives.
The finite reconstruction uses their normalized half-period coefficients.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n06_canonical_unit_measure_eq_window
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (hl : K.left m = 0) (hr : K.right m = 1) :
    canonicalMeasure S K m = cylinderWindowMeasure 0 := by
  simpa only [canonicalMeasure, hl, hr] using n06_unitCanonicalMeasure_eq_window

/-- The original canonical test class and canonical L2 measure give exactly the
unit weak equation when the canonical radial endpoints are zero and one. -/
theorem n06_canonical_unit_weakEquation
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (hl : K.left m = 0) (hr : K.right m = 1)
    {a c V : ℝ → ℝ} (U F : CanonicalL2 S K m)
    (hweak : ∀ φ, CanonicalTest S K m φ →
      (∫ p, U p * n06UnitReferenceTestOperator a c V φ p ∂canonicalMeasure S K m) =
        ∫ p, F p * φ p ∂canonicalMeasure S K m) :
    n06UnitReferenceWeakEquation a c V U F := by
  intro φ hφ
  have h := hweak φ ((n06_unitCanonicalTest_iff hl hr φ).mp hφ)
  simpa only [n06_canonical_unit_measure_eq_window hl hr] using h

/-- Finite graph control at every angular order for actual L2 weak solutions
of the two-variable reference PDE. No modal equation is an input assumption. -/
theorem n06_unit_weakPDE_finite_graph_bound
    (s : Finset ℕ) {U F : PolarPoint → ℝ} {a c V q : ℝ → ℝ} {K : ℝ}
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
    let u := n06HalfCosineCoefficient U
    let f := n06HalfCosineCoefficient F
    ∃ v : ℕ → ℝ → ℝ,
      (∀ i ∈ s, N06WeakModeRepresentative a c V (u i) (f i) (v i) (((2 * i : ℕ) : ℝ))) ∧
      (∀ k : ℕ, mixedDerivative 0 k (r11bFiniteSynthesis s u referenceAngularBasis)
        =ᵐ[cylinderWindowMeasure 0]
          mixedDerivative 0 k (r11bFiniteSynthesis s v referenceAngularBasis)) ∧
      ∃ hULp : ∀ k : ℕ, MemLp
          (mixedDerivative 0 k (r11bFiniteSynthesis s u referenceAngularBasis)) 2
            (cylinderWindowMeasure 0),
      ∃ hFLp : ∀ k : ℕ, MemLp
          (mixedDerivative 0 k (r11bFiniteSynthesis s f referenceAngularBasis)) 2
            (cylinderWindowMeasure 0),
      ∃ hgraph : ∀ k : ℕ, ∀ r : Fin 5,
          MemLp (n06WeakFiniteGraphFields s v k r) 2 (cylinderWindowMeasure 0),
        ∀ b : ℕ,
          (∑ k : Fin (b + 1), ∑ r : Fin 5,
            ‖(hgraph k.val r).toLp (n06WeakFiniteGraphFields s v k.val r)‖ ^ 2) ≤
            16384 * K ^ 10 *
              ((∑ k : Fin (b + 1), ‖(hFLp k.val).toLp
                (mixedDerivative 0 k.val (r11bFiniteSynthesis s f referenceAngularBasis))‖ ^ 2) +
                ∑ k : Fin (b + 1), ‖(hULp k.val).toLp
                  (mixedDerivative 0 k.val (r11bFiniteSynthesis s u referenceAngularBasis))‖ ^ 2) := by
  exact n06_weak_even_finite_graph_bound s (n06HalfCosineCoefficient U)
    (n06HalfCosineCoefficient F) ha hc hV hq
    (fun i _ => n06_halfCosineCoefficient_memLp hU i)
    (fun i _ => n06_halfCosineCoefficient_memLp hF i)
    (fun i _ => n06_unit_weakEquation_modal ha hc hV hU hF hweak i)
    hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂

end ContinuousFlexibility.Analysis
