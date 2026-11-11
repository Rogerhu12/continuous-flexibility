import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Continuous parameter dependence of a uniformly contracting equation

Only continuity in the parameter at each fixed argument is required.
The a posteriori contraction estimate compares a nearby solution with
the fixed solution at the parameter under consideration.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter
open scoped Topology NNReal

/-- A family of actual fixed points is continuous when the maps contract
with one common constant and depend continuously on the parameter. -/
theorem continuous_tailFixedPoint {P X : Type*} [TopologicalSpace P] [MetricSpace X]
    (K : ℝ≥0) (F : P → X → X) (u : P → X)
    (hF : ∀ p, ContractingWith K (F p))
    (hcont : ∀ x, Continuous (fun p => F p x))
    (hfix : ∀ p, F p (u p) = u p) : Continuous u := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound (p : P) :
      dist (u p) (u p₀) ≤ dist (u p₀) (F p (u p₀)) / (1 - (K : ℝ)) := by
    simpa only [dist_comm (u p) (u p₀)] using
      (hF p).dist_le_of_fixedPoint (u p₀) (hfix p)
  have hlim : Tendsto (fun p => dist (u p₀) (F p (u p₀)) / (1 - (K : ℝ)))
      (𝓝 p₀) (𝓝 0) := by
    have hd : Continuous (fun p => dist (u p₀) (F p (u p₀))) :=
      continuous_const.dist (hcont (u p₀))
    have h : Tendsto (fun p => dist (u p₀) (F p (u p₀)) / (1 - (K : ℝ)))
        (𝓝 p₀) (𝓝 (dist (u p₀) (F p₀ (u p₀)) / (1 - (K : ℝ)))) :=
      hd.continuousAt.tendsto.div_const (1 - (K : ℝ))
    simpa only [hfix p₀, dist_self, zero_div] using h
  exact squeeze_zero (fun p => dist_nonneg) hbound hlim

/-- The choice of a fixed point made by the contraction theorem is
continuous; no continuity property of the choice operation is assumed. -/
theorem continuous_tailContractingChoice {P X : Type*} [TopologicalSpace P]
    [MetricSpace X] [Nonempty X] [CompleteSpace X]
    (K : ℝ≥0) (F : P → X → X) (hF : ∀ p, ContractingWith K (F p))
    (hcont : ∀ x, Continuous (fun p => F p x)) :
    Continuous (fun p => ContractingWith.fixedPoint (F p) (hF p)) :=
  continuous_tailFixedPoint K F _ hF hcont fun p => (hF p).fixedPoint_isFixedPt

end ContinuousFlexibility.Radial
