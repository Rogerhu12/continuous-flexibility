import ContinuousFlexibility.Analysis.CanonicalRootTransportBoundary

/-!
# The true reference point of a current root-circle point

The inverse zero-edge image places the reference point on the same root
circle. The actual closed inverse identities send that point back to the
original current point. Its angular coordinate is retained rather than
silently identified with the current angle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem canonicalReferencePoint_root_data
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (hcut : CanonicalCutGeometry S C K base ε)
    (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs₀ : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (θ : ℝ) :
    let k := if side then (K.cutPair m).2 else (K.cutPair m).1
    let c := if side then C.right m else C.left m
    let q := canonicalReferencePoint C K z k (c, θ)
    q.1 = c ∧ q ∈ physicalPieceClosed S K (C.referenceState, 0) k ∧
      canonicalCurrentPoint C K z k q = (c, θ) := by
  let k := if side then (K.cutPair m).2 else (K.cutPair m).1
  let c := if side then C.right m else C.left m
  let q := canonicalReferencePoint C K z k (c, θ)
  have hroot := canonicalCutRoot_mem_closed_and_zero hA hcut hz hs m side θ
  have hcurrent := hA.boundary z hz hs k
  have hreference := hA.boundary _ hz₀ hs₀ k
  have hqC : K.chart z k (c, θ) ∈ canonicalClosed S K k := hcurrent.1 hroot.1
  have hzero : K.inverseChart (C.referenceState, 0) k ''
      ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) = ({c} ×ˢ (univ : Set ℝ)) := by
    cases side
    · exact (hcut.2 _ hz₀ hs₀ m).2.2.2.2.1
    · exact (hcut.2 _ hz₀ hs₀ m).2.2.2.2.2
  have hmem := mem_image_of_mem (K.inverseChart (C.referenceState, 0) k)
    (show K.chart z k (c, θ) ∈ ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) from
      ⟨hroot.2, mem_univ _⟩)
  rw [hzero] at hmem
  have hq : q ∈ physicalPieceClosed S K (C.referenceState, 0) k := hreference.2.1 hqC
  have he : K.chart (C.referenceState, 0) k q = K.chart z k (c, θ) :=
    hreference.2.2.2.1 _ hqC
  refine ⟨hmem.1, hq, ?_⟩
  change K.inverseChart z k (K.chart (C.referenceState, 0) k q) = (c, θ)
  rw [he]
  exact hcurrent.2.2.1 _ hroot.1

end ContinuousFlexibility.Analysis
