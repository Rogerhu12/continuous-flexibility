import ContinuousFlexibility.Geometry.SphereNoncongruence
import ContinuousFlexibility.Contracts.GraphCylinderVolume

/-!
# One actual cap length for the full marked sphere construction

The single compact height bound selects `L = capLength cRight lo 1`.
Projection onto the actual physical disk transports the source height gap to
the physical graph. This same length supplies the real cap intersection, the
jointly smooth embedded sphere family, and the actual noncongruent members.
No second cap length is selected by a separate existence theorem.
-/

noncomputable section

namespace ContinuousFlexibility

open Set
open scoped ContDiff Manifold Topology

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}
local notation "SphereTimeModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

set_option backward.isDefEq.respectTransparency false

/-- Actual projection surjectivity carries a simultaneous source height gap
to the graph over the physical closed disk. No selection of inverse points
or regularity of such a selection is assumed. -/
theorem IsometricGraphDevelopment.physical_height_gap_of_source_height_gap
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R bottom : ℝ}
    (hR : B.b ≤ R)
    (hsource : ∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ≤ R →
      bottom < D.rotationFamily t x 2) :
    ∀ t : ℝ, ∀ y : PolarPoint, cartesianRadius y ≤ R →
      bottom < D.physicalHeight (planarRotation t y) := by
  intro t y hy
  have hm : y ∈ graphBaseProjection ''
      (D.rotationFamily t '' {x : PolarPoint | cartesianRadius x ≤ R}) := by
    rw [D.rotationFamily_projects_onto_disk t hR]
    exact hy
  obtain ⟨v, ⟨x, hx, rfl⟩, hv⟩ := hm
  have hs := hsource t x hx
  rw [D.rotationFamily_physical_height, hv] at hs
  exact hs

/-- The actual cap meeting at the supplied length gives the full real
regularity package for every admissible marker strength and support radius. -/
theorem IsometricGraphDevelopment.markedSphere_regular_of_cap_meeting
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : B.b < R) (hL : 0 < L)
    (hmeet : ∀ t : ℝ, graphPhaseDiskImage D R t ∩ capDiskImage R B.cRight L =
      capAttachingRim R B.cRight)
    (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64) :
    ContMDiff SphereTimeModel 𝓘(ℝ, E3) ∞
      (sphereGraphCapFamily D (markedCapMap R B.cRight L k ρ) R L) ∧
    ∀ t : ℝ, Topology.IsEmbedding (D.markedSphereSlice R L k ρ t) ∧
      ∀ x : SpherePoint, Function.Injective
        (mfderiv (𝓡 2) 𝓘(ℝ, E3) (D.markedSphereSlice R L k ρ t) x) := by
  refine ⟨D.contMDiff_markedSphereFamily (k := k) hR hL hρ hsmall, ?_⟩
  intro t
  refine ⟨?_, D.markedSphereFamily_mfderiv_injective (k := k) hR hL hk hρ hsmall t⟩
  exact isEmbedding_sphereGraphCapFamily D hR hL
    (contDiff_markedCapMap (B.b_pos.trans hR) hL B.cRight k ρ)
    (fun _ hy => markedCapMap_capSphereRadialMap_rim_germ (k := k)
      (B.b_pos.trans hR) hL hρ hsmall B.cRight hy)
    (markedCapMap_injOn (B.b_pos.trans hR) hL hk hρ hsmall B.cRight)
    (fun _ hy => markedCap_boundary (k := k) (B.b_pos.trans hR) hL hρ hsmall B.cRight hy)
    (D.marked_cap_meeting_subset (k := k) hR hL hρ hsmall (hmeet t))

/-- One genuinely selected cap length works simultaneously for the source
height bound, physical height bound, actual unmarked intersection, and all
admissible marked smooth embeddings. The explicit equality records the single
choice from the compact source height bound. -/
theorem IsometricGraphDevelopment.exists_markedSphere_common_cap_length
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R : ℝ} (hR : B.b < R) :
    ∃ L : ℝ, 0 < L ∧
      (∃ lo : ℝ, L = capLength B.cRight lo 1 ∧
        ∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ≤ R → lo ≤ D.rotationFamily t x 2) ∧
      (∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ≤ R →
        B.cRight - L * capDrop < D.rotationFamily t x 2) ∧
      (∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ≤ R →
        B.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) ∧
      (∀ t : ℝ, graphPhaseDiskImage D R t ∩ capDiskImage R B.cRight L =
        capAttachingRim R B.cRight) ∧
      ∀ k ρ : ℝ, 0 ≤ k → 0 < ρ → ρ < L / 64 →
        ContMDiff SphereTimeModel 𝓘(ℝ, E3) ∞
          (sphereGraphCapFamily D (markedCapMap R B.cRight L k ρ) R L) ∧
        ∀ t : ℝ, Topology.IsEmbedding (D.markedSphereSlice R L k ρ t) ∧
          ∀ x : SpherePoint, Function.Injective
            (mfderiv (𝓡 2) 𝓘(ℝ, E3) (D.markedSphereSlice R L k ρ t) x) := by
  obtain ⟨lo, hi, hbounds⟩ := D.exists_rotationFamily_height_bounds R
  let L := capLength B.cRight lo 1
  have hL : 0 < L := capLength_pos B.cRight lo (by norm_num)
  have hbottom : B.cRight - L * capDrop < lo :=
    capLength_bottom_lt B.cRight lo (by norm_num)
  have hsource : ∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ≤ R →
      B.cRight - L * capDrop < D.rotationFamily t x 2 :=
    fun t x hx => hbottom.trans_le (hbounds t x hx).1
  have hphysical := D.physical_height_gap_of_source_height_gap hR.le hsource
  have hmeet (t : ℝ) : graphPhaseDiskImage D R t ∩ capDiskImage R B.cRight L =
      capAttachingRim R B.cRight :=
    D.graph_cap_intersection hR hL (fun t x hx => (hbounds t x hx).1) hbottom t
  exact ⟨L, hL, ⟨lo, rfl, fun t x hx => (hbounds t x hx).1⟩, hsource, hphysical,
    hmeet, fun k ρ hk hρ hsmall =>
      D.markedSphere_regular_of_cap_meeting hR hL hmeet hk hρ hsmall⟩

/-- The same selected length also supplies actual noncongruent closed sphere
members. Both the required embedding hypothesis and the common bottom gap of
the supplied-length noncongruence theorem are instantiated here. -/
theorem IsometricGraphDevelopment.exists_common_cap_markedSphere_noncongruent
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R : ℝ} (hR : B.b < R) :
    ∃ L : ℝ, 0 < L ∧
      (∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ≤ R →
        B.cRight - L * capDrop < D.rotationFamily t x 2) ∧
      (∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ≤ R →
        B.cRight - L * capDrop < D.physicalHeight (planarRotation t x)) ∧
      (∀ t : ℝ, graphPhaseDiskImage D R t ∩ capDiskImage R B.cRight L =
        capAttachingRim R B.cRight) ∧
      ∃ k : ℝ, 0 < k ∧ ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ,
        0 < ρ ∧ ρ < L / 64 ∧ k * ρ ^ 2 / 2 < ε ∧
        ContMDiff SphereTimeModel 𝓘(ℝ, E3) ∞
          (sphereGraphCapFamily D (markedCapMap R B.cRight L k ρ) R L) ∧
        (∀ t : ℝ, Topology.IsEmbedding (D.markedSphereSlice R L k ρ t) ∧
          ∀ x : SpherePoint, Function.Injective
            (mfderiv (𝓡 2) 𝓘(ℝ, E3) (D.markedSphereSlice R L k ρ t) x)) ∧
        ∃ s t : ℝ, ∀ A : E3 ≃ᵃⁱ[ℝ] E3,
          A '' range (D.markedSphereSlice R L k ρ s) ≠ range (D.markedSphereSlice R L k ρ t) := by
  obtain ⟨L, hL, _, hsource, hphysical, hmeet, hregular⟩ :=
    D.exists_markedSphere_common_cap_length hR
  obtain ⟨k, hk, hradius⟩ := D.exists_markedSphere_noncongruent_given_length hR hL
    (fun k ρ hk hρ hsmall t => ((hregular k ρ hk hρ hsmall).2 t).1) hsource
  refine ⟨L, hL, hsource, hphysical, hmeet, k, hk, fun ε hε => ?_⟩
  obtain ⟨ρ, hρ, hsmall, hheight, hnoncongruent⟩ := hradius ε hε
  exact ⟨ρ, hρ, hsmall, hheight, (hregular k ρ hk.le hρ hsmall).1,
    (hregular k ρ hk.le hρ hsmall).2, hnoncongruent⟩

end ContinuousFlexibility
