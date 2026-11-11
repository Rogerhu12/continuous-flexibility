import ContinuousFlexibility.Radial.R11bPartitionSquare
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Measurability recovered from localized fields

A finite-at-each-point partition of one reconstructs the field as the
almost-everywhere limit of its measurable partial sums. No measurability
of the unlocalized representative is assumed.
-/

namespace ContinuousFlexibility.Radial

open Filter MeasureTheory
open scoped BigOperators Topology

theorem r11b_aestronglyMeasurable_of_localized
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (χ : ℕ → α → ℝ) (f : α → ℝ)
    (hlocal : ∀ m, AEStronglyMeasurable (fun x => χ m x * f x) μ)
    (hfinite : ∀ᵐ x ∂μ, (Function.support (fun m => χ m x)).Finite)
    (hsum : ∀ᵐ x ∂μ, (∑' m, χ m x) = 1) :
    AEStronglyMeasurable f μ := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n x => ∑ m ∈ Finset.range n, χ m x * f x)
  · intro n
    exact (Finset.range n).aestronglyMeasurable_fun_sum (fun m _ => hlocal m)
  · filter_upwards [hfinite, hsum] with x hfin hsumx
    have hs : Summable (fun m => χ m x) := summable_of_hasFiniteSupport hfin
    have hlim := hs.hasSum.tendsto_sum_nat.mul_const (f x)
    simpa only [hsumx, one_mul, Finset.sum_mul] using hlim

end ContinuousFlexibility.Radial
