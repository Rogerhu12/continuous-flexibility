module

public import ContinuousFlexibility.Radial.InnerRadialActualPieces

/-!
# Actual positive-gap charts from the original coefficients

The columns are selected once from the radial initial-value construction.
Their boundary and differential equations are proved there, rather than
stored as new assumptions. For an actual profile the surrounding positive
range and global nonnegativity follow directly from its original geometry.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements
open scoped ContDiff

def innerRadialGapChartOfCoefficients (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {n : ℕ} (G : InnerRadialChainGeometry D n) (j : ℝ)
    (central piece : Fin (n + 1)) (hAway : piece ≠ central) (hj : 0 < j)
    {s A B : ℝ} (hs : 0 < s) (hA : 0 < A)
    (hAl : A < G.left piece) (hhB : G.right piece < B)
    (hwnonneg : ∀ r, 0 ≤ D.w r) (hwpos : ∀ r ∈ Ioo A B, 0 < D.w r)
    (hslope : ∀ r ∈ Icc (G.left piece) (G.right piece), s ≤ r * deriv D.w r / D.w r) :
    InnerRadialGapChart D G j central piece := by
  let hex := exists_innerGapPoissonColumns hA hAl (G.left_lt_right piece) hhB
    hw hwnonneg hwpos (fun r hr => hs.le.trans (hslope r hr)) j
  let p : Fin 2 → ℝ → ℝ := Classical.choose hex
  have hp := Classical.choose_spec hex
  exact
    { away_center := hAway
      frequency_pos := hj
      slope := s
      slope_pos := hs
      slope_lower := hslope
      columns := p
      columns_smooth := hp.1
      columns_boundary := hp.2.1
      columns_homogeneous := hp.2.2 }

theorem innerRadialProfile_weight_nonneg {D : ReferenceData} (hD : RadialProfileGeometry D)
    (r : ℝ) : 0 ≤ D.w r := by
  by_cases hr : r ∈ radialCore D
  · exact (hD.2.2.2.2.1 r hr).le
  · have hout : r ≤ D.a ∨ D.b ≤ r := by
      simpa only [radialCore, mem_Ioo, not_and_or, not_lt] using hr
    rw [hD.2.2.1.2 r hout] <;> exact le_rfl

theorem innerRadialProfile_positive_mem_core {D : ReferenceData}
    (hD : RadialProfileGeometry D) {r : ℝ} (hr : 0 < D.w r) : r ∈ radialCore D := by
  by_contra hnot
  have hout : r ≤ D.a ∨ D.b ≤ r := by
    simpa only [radialCore, mem_Ioo, not_and_or, not_lt] using hnot
  exact hr.ne' (hD.2.2.1.2 r hout)

/-- The actual profile supplies the positive interval automatically.
Only the raw, already derived positive slope is needed at this stage. -/
def innerRadialGapChartOfProfile (D : ReferenceData) (hD : RadialProfileGeometry D)
    {n : ℕ} (G : InnerRadialChainGeometry D n) (j : ℝ)
    (central piece : Fin (n + 1)) (hAway : piece ≠ central) (hj : 0 < j)
    {s : ℝ} (hs : 0 < s)
    (hslope : ∀ r ∈ Icc (G.left piece) (G.right piece), s ≤ r * deriv D.w r / D.w r) :
    InnerRadialGapChart D G j central piece := by
  have hl := innerRadialProfile_positive_mem_core hD
    (G.weight_pos piece _ (left_mem_Icc.mpr (G.left_lt_right piece).le))
  have hr := innerRadialProfile_positive_mem_core hD
    (G.weight_pos piece _ (right_mem_Icc.mpr (G.left_lt_right piece).le))
  exact innerRadialGapChartOfCoefficients D hD.2.2.1.1 G j central piece hAway hj hs
    hD.1 hl.1 hr.2 (innerRadialProfile_weight_nonneg hD) hD.2.2.2.2.1 hslope

end ContinuousFlexibility.Radial
