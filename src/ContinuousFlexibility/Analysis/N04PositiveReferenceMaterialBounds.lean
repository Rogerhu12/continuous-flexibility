import ContinuousFlexibility.Analysis.CanonicalPositiveReferenceFamily

/-!
# The quantitative certificate retained with a positive reference family

The reference coordinate and height are chosen once, before the spatial
order. Their global derivative bounds and the positive-order bounds of
the genuine inverse use the same midpoint sample. This certificate is
produced by the actual degree-three reference construction; it is not a
current-state or transport assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

/-- All-order material bounds of the same chosen reference coordinate and
height. No global zeroth-order bound of the unbounded inverse is required. -/
def N04PositiveReferenceMaterialBounds {ι : Type*} (T : MaterialData)
    (cell : ι → ℕ) (Y H : ι → ℝ → ℝ) : Prop :=
  ∃ C0 : ℝ, 1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
    ∀ N : ℕ, ∃ M : ℝ, 1 ≤ M ∧ ∀ i,
      (∀ k, k ≤ N → ∀ x : ℝ,
        |iteratedDeriv (k + 1) (Y i) x| ≤ M * (C0 * T.E0 (T.sample (cell i))) ^ M ∧
        |iteratedDeriv k (H i) x| ≤ M * (C0 * T.E0 (T.sample (cell i))) ^ M ∧
        |iteratedDeriv k (fun t => (H i t)⁻¹) x| ≤
          M * (C0 * T.E0 (T.sample (cell i))) ^ M) ∧
      ∀ x : ℝ, |iteratedDeriv (N + 1) (Function.invFun (Y i)) x| ≤
        M * (C0 * T.E0 (T.sample (cell i))) ^ M

end ContinuousFlexibility.Analysis
