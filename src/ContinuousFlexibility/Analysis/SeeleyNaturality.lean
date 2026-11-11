import ContinuousFlexibility.Analysis.SeeleyJetExtension
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Seeley extension respects linear maps and closed derivative graphs

The scalar reflection coefficients are independent of the target Banach space.
Consequently the extension commutes with every bounded linear map.  More
generally, a pair of functions taking values in any closed linear relation
continues to satisfy that relation after extension.  This applies to a closed
angular derivative graph on circle-valued slices, including unbounded angular
derivatives, without replacing an isotropic Sobolev order by twice that order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

variable {ι F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The reflection series commutes with bounded linear maps at every derivative
order.  The input bound supplies convergence of the actual series. -/
theorem seeleyReflection_map (S : SeeleyData ι) (n : ℕ) (L : F →L[ℝ] G)
    {f : ℝ → F} (hf : ∃ M : ℝ, ∀ y, 0 ≤ y → ‖f y‖ ≤ M)
    {x : ℝ} (hx : x ≤ 0) :
    L (seeleyReflection S n f x) = seeleyReflection S n (fun y ↦ L (f y)) x := by
  rw [seeleyReflection, seeleyReflection,
    L.map_tsum (summable_seeleyReflection S n hf hx)]
  apply tsum_congr
  intro i
  exact L.map_smul _ _

/-- One and the same extension commutes with bounded linear maps between its
target Banach spaces. -/
theorem seeleyExtend_map (S : SeeleyData ι) (L : F →L[ℝ] G)
    {f : ℝ → F} (hf : ∃ M : ℝ, ∀ y, 0 ≤ y → ‖f y‖ ≤ M) (x : ℝ) :
    L (seeleyExtend S f x) = seeleyExtend S (fun y ↦ L (f y)) x := by
  by_cases hx : 0 ≤ x
  · simp only [seeleyExtend, if_pos hx]
  · simp only [seeleyExtend, if_neg hx]
    exact seeleyReflection_map S 0 L hf (le_of_not_ge hx)

/-- Any closed linear relation is preserved by each reflected jet.  In
particular, this applies to closed graphs of unbounded linear operators. -/
theorem seeleyReflection_mem_closedLinearRelation (S : SeeleyData ι) (n : ℕ)
    (P : Submodule ℝ (F × G)) (hP : IsClosed (P : Set (F × G)))
    {u : ℝ → F} {v : ℝ → G}
    (hu : ∃ M : ℝ, ∀ y, 0 ≤ y → ‖u y‖ ≤ M)
    (hv : ∃ M : ℝ, ∀ y, 0 ≤ y → ‖v y‖ ≤ M)
    (hrel : ∀ y, 0 ≤ y → (u y, v y) ∈ P) {x : ℝ} (hx : x ≤ 0) :
    (seeleyReflection S n u x, seeleyReflection S n v x) ∈ P := by
  have hsum := (summable_seeleyReflection S n hu hx).hasSum.prodMk
    (summable_seeleyReflection S n hv hx).hasSum
  have he : (∑' i, ((S.a i * (-S.b i) ^ n) • u (-S.b i * x),
        (S.a i * (-S.b i) ^ n) • v (-S.b i * x))) =
      (seeleyReflection S n u x, seeleyReflection S n v x) := hsum.tsum_eq
  rw [← he]
  apply tsum_mem hP
  intro i
  have hy : 0 ≤ -S.b i * x := mul_nonneg_of_nonpos_of_nonpos
    (neg_nonpos.mpr (S.b_nonneg i)) hx
  simpa only [Prod.smul_mk] using P.smul_mem (S.a i * (-S.b i) ^ n) (hrel _ hy)

/-- The fixed extension preserves every closed linear relation pointwise on
the whole real line. -/
theorem seeleyExtend_mem_closedLinearRelation (S : SeeleyData ι)
    (P : Submodule ℝ (F × G)) (hP : IsClosed (P : Set (F × G)))
    {u : ℝ → F} {v : ℝ → G}
    (hu : ∃ M : ℝ, ∀ y, 0 ≤ y → ‖u y‖ ≤ M)
    (hv : ∃ M : ℝ, ∀ y, 0 ≤ y → ‖v y‖ ≤ M)
    (hrel : ∀ y, 0 ≤ y → (u y, v y) ∈ P) (x : ℝ) :
    (seeleyExtend S u x, seeleyExtend S v x) ∈ P := by
  by_cases hx : 0 ≤ x
  · simpa only [seeleyExtend, if_pos hx] using hrel x hx
  · simp only [seeleyExtend, if_neg hx]
    exact seeleyReflection_mem_closedLinearRelation S 0 P hP hu hv hrel (le_of_not_ge hx)

/-- Applying a common scalar cutoff before extension also preserves the
relation.  This is the part needed for the two endpoint pieces of an interval. -/
theorem seeleyExtend_cutoff_mem_closedLinearRelation (S : SeeleyData ι)
    (P : Submodule ℝ (F × G)) (hP : IsClosed (P : Set (F × G)))
    (χ : ℝ → ℝ) {u : ℝ → F} {v : ℝ → G}
    (hu : ∃ M : ℝ, ∀ y, 0 ≤ y → ‖χ y • u y‖ ≤ M)
    (hv : ∃ M : ℝ, ∀ y, 0 ≤ y → ‖χ y • v y‖ ≤ M)
    (hrel : ∀ y, 0 ≤ y → (u y, v y) ∈ P) (x : ℝ) :
    (seeleyExtend S (fun y ↦ χ y • u y) x,
      seeleyExtend S (fun y ↦ χ y • v y) x) ∈ P := by
  apply seeleyExtend_mem_closedLinearRelation S P hP hu hv
  intro y hy
  simpa only [Prod.smul_mk] using P.smul_mem (χ y) (hrel y hy)

end ContinuousFlexibility.Analysis
