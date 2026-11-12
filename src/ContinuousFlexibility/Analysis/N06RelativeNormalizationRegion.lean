import ContinuousFlexibility.Analysis.N06RelativeCanonicalBoundaryPatch
import ContinuousFlexibility.Radial.ReferenceColumnSmooth
import Mathlib.Topology.MetricSpace.Thickening

/-!
# One actual normalization region for all separated boundary collars

The true border has compact support in the strictly positive-type region.
Its closed support and the closed nonpositive-type set have disjoint
uniform thickenings. This constructs one open normalization region before
any state or piece is considered. A concrete radius on every physical
interval then keeps the two actual relative corrections out of that region.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

/-- A concrete radius, with no positive lower bound on the piece width. -/
def n06RootSeparatedPatchRadius (ρ l r : ℝ) : ℝ :=
  min (ρ / 2) ((r - l) / 4)

theorem n06RootSeparatedPatchRadius_properties {ρ l r : ℝ}
    (hρ : 0 < ρ) (hlr : l < r) :
    0 < n06RootSeparatedPatchRadius ρ l r ∧
      n06RootSeparatedPatchRadius ρ l r < ρ ∧
      2 * n06RootSeparatedPatchRadius ρ l r < r - l := by
  have hp : 0 < min (ρ / 2) ((r - l) / 4) := by
    apply lt_min <;> linarith
  have hρbound : min (ρ / 2) ((r - l) / 4) ≤ ρ / 2 := min_le_left _ _
  have hwidth : min (ρ / 2) ((r - l) / 4) ≤ (r - l) / 4 := min_le_right _ _
  exact ⟨hp, by dsimp only [n06RootSeparatedPatchRadius]; linarith,
    by dsimp only [n06RootSeparatedPatchRadius]; linarith⟩

/-- The open set is constructed from the true reference profile and border.
Every endpoint of nonpositive type has a uniformly disjoint collar. -/
theorem n06_exists_common_relativeNormalizationRegion
    {D : ReferenceData} (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ U : Set ℝ,
      IsOpen U ∧ tsupport D.chi ⊆ U ∧ Function.support (referenceColumn D) ⊆ U ∧
      ∀ c : ℝ, deriv D.w c ≤ 0 → Disjoint (Metric.ball c ρ) U := by
  let Z : Set ℝ := {r | deriv D.w r ≤ 0}
  have hw : ContDiff ℝ ∞ (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hgeom.2.2.1.1).2
  have hZ : IsClosed Z :=
    isClosed_le hw.continuous continuous_const
  have hsep : Disjoint (tsupport D.chi) Z := by
    apply Set.disjoint_left.mpr
    intro r hr hz
    exact (not_le.mpr (hborder.2.2.1 hr).2) hz
  obtain ⟨ρ, hρ, hthick⟩ := hsep.exists_thickenings hborder.2.1 hZ
  let U := Metric.thickening ρ (tsupport D.chi)
  have hχ : tsupport D.chi ⊆ U := Metric.self_subset_thickening hρ _
  refine ⟨ρ, hρ, U, Metric.isOpen_thickening, hχ, ?_, ?_⟩
  · exact (subset_tsupport (referenceColumn D)).trans
      (Radial.referenceColumn_tsupport_subset.trans hχ)
  · intro c hc
    exact hthick.symm.mono_left (Metric.ball_subset_thickening (show c ∈ Z from hc) ρ)

/-- The radius and one common open region are selected before every state.
The boundary type premise identifies the genuine root or negative-cut
pieces, rather than asserting that arbitrary positive subdivisions are
root pieces. On all such pieces the explicit patch fixes the same region. -/
theorem n06_exists_relativeCanonical_common_normalization
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D)
    (hA : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ U : Set ℝ,
      IsOpen U ∧ tsupport D.chi ⊆ U ∧ Function.support (referenceColumn D) ⊆ U ∧
      ∀ m : ℕ, deriv D.w (K.physicalLeft m) ≤ 0 →
        deriv D.w (K.physicalRight m) ≤ 0 →
        let δ := n06RootSeparatedPatchRadius ρ (K.physicalLeft m) (K.physicalRight m)
        0 < δ ∧ δ < ρ ∧ 2 * δ < K.physicalRight m - K.physicalLeft m ∧
        ∀ (z : AnnularState S × ℝ) (p : PolarPoint),
          p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) → p.1 ∈ U →
          n06RelativeCanonicalChart C K δ z m =ᶠ[𝓝 p] K.chart (C.referenceState, 0) m ∧
          n06RelativeCanonicalHeight C K δ z m =ᶠ[𝓝 p] K.height (C.referenceState, 0) m := by
  obtain ⟨ρ, hρ, U, hU, hχ, hcolumn, hsep⟩ :=
    n06_exists_common_relativeNormalizationRegion hgeom hborder
  refine ⟨ρ, hρ, U, hU, hχ, hcolumn, ?_⟩
  intro m hleft hright
  dsimp only
  let δ := n06RootSeparatedPatchRadius ρ (K.physicalLeft m) (K.physicalRight m)
  have hδ := n06RootSeparatedPatchRadius_properties hρ (hA.2.2.2.1 m).1
  refine ⟨hδ.1, hδ.2.1, hδ.2.2, ?_⟩
  have hL : Disjoint (Metric.ball (K.physicalLeft m) δ) U :=
    (hsep _ hleft).mono_left (Metric.ball_subset_ball hδ.2.1.le)
  have hR : Disjoint (Metric.ball (K.physicalRight m) δ) U :=
    (hsep _ hright).mono_left (Metric.ball_subset_ball hδ.2.1.le)
  intro z p hp hpU
  have hp₀ := hA.2.2.2.2.2.2.2.2.1 (C.referenceState, 0) href hsref m p hp
  exact ⟨n06RelativeChartPatch_fixed_germ hδ.1 _ _ hL hR hpU,
    n06RelativeHeightPatch_fixed_germ hδ.1 _ _ hL hR hpU hp₀.2.1.continuousAt hp₀.2.2.2⟩

end ContinuousFlexibility.Statements
