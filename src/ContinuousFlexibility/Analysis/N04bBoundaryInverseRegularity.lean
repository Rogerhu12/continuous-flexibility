module

public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Topology.Closure

/-!
# Genuine closed inverse and pullback regularity

The boundary contract specifies an actual local inverse germ. It therefore
controls the stored inverse on the whole canonical closed strip, including
the ordinary derivatives used in transmission. Interior points use the
open inverse chart; boundary points use the genuine inverse germ.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

theorem n04b_boundaryInverseGerm_contDiffAt
    {F G : PolarPoint → PolarPoint} {p : PolarPoint}
    (h : CanonicalBoundaryInverseGerm F G p) :
    ContDiffAt ℝ ∞ G (F p) := by
  obtain ⟨e, hF, hp, he, hG⟩ := h
  exact he.congr_of_eventuallyEq hG

/-- The stored inverse is genuinely smooth at every point of the canonical
closed strip, not just its interior. -/
theorem n04b_inverseChart_contDiffAt_closed
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalClosed S K m) :
    ContDiffAt ℝ ∞ (K.inverseChart z m) p := by
  have hcharts := hA.charts z hz hs m
  have hclosed := hA.boundary z hz hs m
  have hx : K.inverseChart z m p ∈ physicalPieceClosed S K z m :=
    hclosed.2.1 hp
  have hFx : K.chart z m (K.inverseChart z m p) = p :=
    hclosed.2.2.2.1 p hp
  by_cases hi : K.inverseChart z m p ∈ physicalPieceOpen S K z m
  · have hpopen : p ∈ canonicalOpen S K m := by
      rw [← hFx]
      exact hcharts.1 hi
    exact (hcharts.2.2.2.2.2.1 p hpopen).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpopen)
  · have hfront :
        K.inverseChart z m p ∈ frontier (physicalPieceOpen S K z m) := by
      rw [(hA.domains z hz hs m).1.frontier_eq]
      exact ⟨hx, hi⟩
    have hg := n04b_boundaryInverseGerm_contDiffAt
      (hclosed.2.2.2.2.2 _ hfront)
    simpa only [hFx] using hg

/-- Smooth physical tests give smooth canonical unknowns on the closed
strip with the actual stored inverse and positive height factor. -/
theorem n04b_canonicalHeight_contDiffAt_closed
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalClosed S K m)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiffAt ℝ ∞ (canonicalHeight S K z m u) p := by
  have hclosed := hA.boundary z hz hs m
  have hx : K.inverseChart z m p ∈ physicalPieceClosed S K z m :=
    hclosed.2.1 hp
  have hh := hclosed.2.2.2.2.1 _ hx
  have hG := n04b_inverseChart_contDiffAt_closed hA hz hs m hp
  have heq : canonicalHeight S K z m u =
      (fun q => u (K.inverseChart z m q) /
        K.height z m (K.inverseChart z m q)) := by
    funext q
    rfl
  rw [heq]
  exact (hu.contDiffAt.comp p hG).div (hh.2.1.comp p hG) (ne_of_gt hh.2.2.2)

end ContinuousFlexibility.Analysis
