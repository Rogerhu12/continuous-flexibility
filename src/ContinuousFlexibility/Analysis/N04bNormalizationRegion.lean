import ContinuousFlexibility.Radial.ReferenceColumnSmooth

/-!
# An actual normalization region away from the negative components

The reference column vanishes on the negative radial set because its
cutoff is supported where the reference derivative is positive. Its
continuity extends this vanishing to the closure. The complement of that
closure is consequently one open normalization region containing the
actual column support. Every negative physical piece misses this region,
even when its artificial boundary moves.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

/-- Only the fixed reference sign set enters this region. -/
def n04bNormalizationRegion (D : ReferenceData) : Set ℝ :=
  (closure {r : ℝ | deriv D.w r < 0})ᶜ

theorem n04bNormalizationRegion_isOpen (D : ReferenceData) :
    IsOpen (n04bNormalizationRegion D) :=
  isClosed_closure.isOpen_compl

theorem n04b_not_mem_normalizationRegion_of_negative
    {D : ReferenceData} {r : ℝ} (hr : deriv D.w r < 0) :
    r ∉ n04bNormalizationRegion D := by
  intro h
  exact h (subset_closure hr)

/-- The actual border column, not an arbitrary source representative,
is supported in the open normalization region. -/
theorem n04b_referenceColumn_support_normalizationRegion
    {D : ReferenceData} (hgeom : RadialProfileGeometry D)
    (hborder : RadialTrueBorder D) :
    Function.support (referenceColumn D) ⊆ n04bNormalizationRegion D := by
  have hχ : tsupport D.chi ⊆ {r : ℝ | 0 ≤ deriv D.w r} := by
    intro r hr
    exact (hborder.2.2.1 hr).2.le
  have hzero : {r : ℝ | deriv D.w r < 0} ⊆
      {r : ℝ | referenceColumn D r = 0} := by
    intro r hr
    by_contra h
    have hn : 0 ≤ deriv D.w r :=
      hχ (Radial.referenceColumn_tsupport_subset (subset_closure h))
    exact (not_lt_of_ge hn) hr
  have hclosed : closure {r : ℝ | deriv D.w r < 0} ⊆
      {r : ℝ | referenceColumn D r = 0} :=
    closure_minimal hzero
      (isClosed_eq (Radial.referenceColumn_contDiff hgeom hborder).continuous
        continuous_const)
  intro r hr
  exact fun hneg => hr (hclosed hneg)

/-- A genuine negative domain has empty intersection with the chosen
normalization cylinder, without being a radial strip itself. -/
theorem n04b_negative_domain_normalization_inter
    {D : ReferenceData} {Ω : Set PolarPoint}
    (hnegative : ∀ p ∈ Ω, deriv D.w p.1 < 0) :
    Ω ∩ (n04bNormalizationRegion D ×ˢ (univ : Set ℝ)) = ∅ := by
  apply Set.Subset.antisymm
  · intro p hp
    exact (n04b_not_mem_normalizationRegion_of_negative (hnegative p hp.1) hp.2.1).elim
  · exact empty_subset _

end ContinuousFlexibility.Analysis
