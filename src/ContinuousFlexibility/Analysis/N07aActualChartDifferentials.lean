module

public import ContinuousFlexibility.Analysis.N07aCanonicalAtomBounds

/-!
# Differential inverse identities on the actual physical pieces

These identities use the two genuine inverse relations on their open
domains. They do not identify a current physical piece with a reference
rectangle.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

theorem n07a_actualChart_fderiv_inverse
    (hgeom : CanonicalGeometry D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {y : PolarPoint}
    (hy : y ∈ canonicalOpen S K m) :
    (fderiv ℝ (K.chart z m) (K.inverseChart z m y)).comp
        (fderiv ℝ (K.inverseChart z m) y) = ContinuousLinearMap.id ℝ PolarPoint ∧
      (fderiv ℝ (K.inverseChart z m) y).comp
        (fderiv ℝ (K.chart z m) (K.inverseChart z m y)) =
          ContinuousLinearMap.id ℝ PolarPoint := by
  have hc := hgeom.charts z hz hs m
  have hΩ : IsOpen (physicalPieceOpen S K z m) := (hgeom.domains z hz hs m).1
  have hQ : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hx := hc.2.1 hy
  have hF := (hc.2.2.2.2.1.contDiffAt (hΩ.mem_nhds hx)).differentiableAt
    (by simp)
  have hG := (hc.2.2.2.2.2.1.contDiffAt (hQ.mem_nhds hy)).differentiableAt
    (by simp)
  have hFG : (K.chart z m ∘ K.inverseChart z m) =ᶠ[𝓝 y] id := by
    filter_upwards [hQ.mem_nhds hy] with q hq
    exact hc.2.2.2.1 q hq
  have hGF : (K.inverseChart z m ∘ K.chart z m) =ᶠ[𝓝 (K.inverseChart z m y)] id := by
    filter_upwards [hΩ.mem_nhds hx] with q hq
    exact hc.2.2.1 q hq
  constructor
  · exact ((hF.hasFDerivAt.comp y hG.hasFDerivAt).congr_of_eventuallyEq hFG.symm).unique
      (hasFDerivAt_id y)
  · have hG' : HasFDerivAt (K.inverseChart z m) (fderiv ℝ (K.inverseChart z m) y)
        (K.chart z m (K.inverseChart z m y)) := by
      rw [hc.2.2.2.1 y hy]
      exact hG.hasFDerivAt
    exact ((hG'.comp (K.inverseChart z m y) hF.hasFDerivAt).congr_of_eventuallyEq
      hGF.symm).unique (hasFDerivAt_id (K.inverseChart z m y))

end ContinuousFlexibility.Analysis
