import ContinuousFlexibility.Geometry.SphereMarkerRigidity
import ContinuousFlexibility.Geometry.GraphOrbitVariation

/-!
# Actual noncongruent closed sphere images

The actual compact sphere images form a continuous compact-set family. Actual
finite affine congruence candidates force this family to be constant if all its
members are congruent. Above the common bottom plane, its part in the central
closed cylinder recovers the actual graph disk, contradicting the previously
proved nonconstant graph images. All marker choices use the supplied cap length.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Filter TopologicalSpace
open scoped ContDiff Manifold Topology

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}
local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

set_option backward.isDefEq.respectTransparency false

def graphRecoveryCylinder (R bottom : ℝ) : Set E3 :=
  {v | cartesianRadius (graphBaseProjection v) ≤ R ∧ bottom < v 2}

def IsometricGraphDevelopment.markedSphereCompact {B : FlatAnnularCore}
    (D : IsometricGraphDevelopment B) {R L : ℝ} (hR : B.b < R) (hL : 0 < L)
    (k ρ t : ℝ) : Compacts E3 :=
  graphPhaseCompact D R t ⊔
    ⟨markedCapMap R B.cRight L k ρ '' {y : PolarPoint | cartesianRadius y ≤ 1},
      (isCompact_closedCartesianDisk 1).image
        (contDiff_markedCapMap (B.b_pos.trans hR) hL B.cRight k ρ).continuous⟩

theorem IsometricGraphDevelopment.continuous_markedSphereCompact {B : FlatAnnularCore}
    (D : IsometricGraphDevelopment B) {R L : ℝ} (hR : B.b < R) (hL : 0 < L) (k ρ : ℝ) :
    Continuous (D.markedSphereCompact hR hL k ρ) :=
  (continuous_graphPhaseCompact D R).sup continuous_const

theorem IsometricGraphDevelopment.coe_markedSphereCompact {B : FlatAnnularCore}
    (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : B.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (t : ℝ) :
    (D.markedSphereCompact hR hL k ρ t : Set E3) =
      range (D.markedSphereSlice R L k ρ t) := by
  change graphPhaseDiskImage D R t ∪
    (markedCapMap R B.cRight L k ρ '' {y : PolarPoint | cartesianRadius y ≤ 1}) = _
  exact (sphereGraphCapFamily_range D hR hL
    (C := markedCapMap R B.cRight L k ρ)
    (fun _ hy => markedCapMap_capSphereRadialMap_rim_germ (k := k)
      (B.b_pos.trans hR) hL hρ hsmall B.cRight hy) t).symm

/-- The cap is unchanged in the physical central cylinder. Its only points
strictly above the bottom there lie on the attaching rim, also in the graph. -/
theorem IsometricGraphDevelopment.markedCap_in_recoveryCylinder_subset_graph
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : B.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (t : ℝ) :
    (markedCapMap R B.cRight L k ρ '' {y : PolarPoint | cartesianRadius y ≤ 1}) ∩
      graphRecoveryCylinder R (B.cRight - L * capDrop) ⊆ graphPhaseDiskImage D R t := by
  rintro v ⟨⟨y, hy, rfl⟩, hrad, hheight⟩
  have hRp := B.b_pos.trans hR
  have hb : cartesianRadius (capDiskBase R L y) ≤ R := by
    simpa only [markedCapMap_base] using hrad
  have heq := markedCapMap_eq_capDiskMap_of_inner hRp hL hρ hsmall B.cRight
    (k := k) (by linarith : cartesianRadius (capDiskBase R L y) ≤ R + L / 16)
  rw [heq] at hrad hheight ⊢
  obtain ⟨hs, _⟩ := capDisk_upper_cylinder_meeting hRp hL B.cRight hy hrad hheight
  have hyr : cartesianRadius y = 1 := by
    unfold capDiskParameter at hs
    have hz : 1 - cartesianRadius y = 0 :=
      (mul_eq_zero.mp hs).resolve_left (add_pos hL hRp).ne'
    linarith
  rw [capDisk_boundary R B.cRight L hyr]
  refine ⟨R • y, ?_, ?_⟩
  · change cartesianRadius (R • y) ≤ R
    rw [capDisk_radius_smul, abs_of_pos hRp, hyr, mul_one]
  · have hp : B.b < cartesianRadius (R • y) := by
      rw [capDisk_radius_smul, abs_of_pos hRp, hyr, mul_one]
      exact hR
    exact D.phase_flat_outside t hp

/-- An exact set-theoretic recovery from the same actual marked sphere image. -/
theorem IsometricGraphDevelopment.markedSphere_recovers_graph {B : FlatAnnularCore}
    (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : B.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hgap : ∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ≤ R →
      B.cRight - L * capDrop < D.rotationFamily t x 2) (t : ℝ) :
    range (D.markedSphereSlice R L k ρ t) ∩ graphRecoveryCylinder R (B.cRight - L * capDrop) =
      graphPhaseDiskImage D R t := by
  have hrange := sphereGraphCapFamily_range D hR hL
    (C := markedCapMap R B.cRight L k ρ)
    (fun _ hy => markedCapMap_capSphereRadialMap_rim_germ (k := k)
      (B.b_pos.trans hR) hL hρ hsmall B.cRight hy) t
  change range (fun x : SpherePoint =>
    sphereGraphCapFamily D (markedCapMap R B.cRight L k ρ) R L (x, t)) ∩ _ = _
  rw [hrange]
  apply Set.Subset.antisymm
  · rintro v ⟨hv | hv, hc⟩
    · exact hv
    · exact D.markedCap_in_recoveryCylinder_subset_graph (k := k) hR hL hρ hsmall t ⟨hv, hc⟩
  · rintro v ⟨x, hx, rfl⟩
    exact ⟨Or.inl ⟨x, hx, rfl⟩,
      D.phase_disk_projection_bound t hR.le hx, hgap t x hx⟩

/-- The compact topology is the genuine compact-image topology. Finite images
are derived from the actual finite affine congruence set. -/
theorem IsometricGraphDevelopment.markedSphere_noncongruent_of_finite_congruences
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R L k ρ : ℝ}
    (hR : B.b < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (hgap : ∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ≤ R →
      B.cRight - L * capDrop < D.rotationFamily t x 2)
    (hfinite : {A : E3 ≃ᵃⁱ[ℝ] E3 | ∃ s t : ℝ,
      A '' range (D.markedSphereSlice R L k ρ s) = range (D.markedSphereSlice R L k ρ t)}.Finite) :
    ∃ s t : ℝ, ∀ A : E3 ≃ᵃⁱ[ℝ] E3,
      A '' range (D.markedSphereSlice R L k ρ s) ≠ range (D.markedSphereSlice R L k ρ t) := by
  classical
  by_contra hnone
  push Not at hnone
  have himages : (range (fun t : ℝ => range (D.markedSphereSlice R L k ρ t))).Finite := by
    apply (Set.Finite.image (fun A : E3 ≃ᵃⁱ[ℝ] E3 =>
      A '' range (D.markedSphereSlice R L k ρ 0)) hfinite).subset
    rintro Y ⟨t, rfl⟩
    obtain ⟨A, he⟩ := hnone 0 t
    exact ⟨A, ⟨0, t, he⟩, he⟩
  let K := D.markedSphereCompact hR hL k ρ
  have hmap : MapsTo (fun X : Compacts E3 => (X : Set E3)) (range K)
      (range (fun t : ℝ => range (D.markedSphereSlice R L k ρ t))) := by
    rintro X ⟨t, rfl⟩
    exact ⟨t, (D.coe_markedSphereCompact hR hL hρ hsmall t).symm⟩
  have hKfin : (range K).Finite :=
    Set.Finite.of_injOn hmap SetLike.coe_injective.injOn himages
  have hwhole (t : ℝ) : range (D.markedSphereSlice R L k ρ t) =
      range (D.markedSphereSlice R L k ρ 0) := by
    have he := congrArg (fun X : Compacts E3 => (X : Set E3))
      (continuous_finite_compact_family_constant (D.continuous_markedSphereCompact hR hL k ρ)
        hKfin t 0)
    simpa only [D.coe_markedSphereCompact hR hL hρ hsmall] using he
  have hgraph (t : ℝ) : graphPhaseDiskImage D R t = graphPhaseDiskImage D R 0 := by
    rw [← D.markedSphere_recovers_graph (k := k) hR hL hρ hsmall hgap t,
      ← D.markedSphere_recovers_graph (k := k) hR hL hρ hsmall hgap 0, hwhole t]
  obtain ⟨t, ht⟩ := D.exists_rotationFamily_image_ne hR
  have hzero : D.rotationFamily 0 = D.map := funext D.rotationFamily_zero
  apply ht
  simpa only [graphPhaseDiskImage, hzero] using hgraph t

/-- The final result uses the true marker construction at the supplied length.
No finite-candidate or preserved-frame hypothesis remains. -/
theorem IsometricGraphDevelopment.exists_markedSphere_noncongruent_given_length
    {B : FlatAnnularCore} (D : IsometricGraphDevelopment B) {R L : ℝ}
    (hR : B.b < R) (hL : 0 < L)
    (hRegular : ∀ k ρ : ℝ, 0 ≤ k → 0 < ρ → ρ < L / 64 →
      ∀ t, Topology.IsEmbedding (D.markedSphereSlice R L k ρ t))
    (hgap : ∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ≤ R →
      B.cRight - L * capDrop < D.rotationFamily t x 2) :
    ∃ k : ℝ, 0 < k ∧ ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ,
      0 < ρ ∧ ρ < L / 64 ∧ k * ρ ^ 2 / 2 < ε ∧
      ∃ s t : ℝ, ∀ A : E3 ≃ᵃⁱ[ℝ] E3,
        A '' range (D.markedSphereSlice R L k ρ s) ≠ range (D.markedSphereSlice R L k ρ t) := by
  obtain ⟨k, hk, hradius⟩ := D.exists_markedSphere_finite_congruences_given_length hR hL hRegular
  refine ⟨k, hk, fun ε hε => ?_⟩
  obtain ⟨ρ, hρ, hsmall, hheight, _, _, hcount⟩ := hradius ε hε
  exact ⟨ρ, hρ, hsmall, hheight, D.markedSphere_noncongruent_of_finite_congruences
    hR hL hρ hsmall hgap (Set.finite_of_encard_le_coe hcount)⟩

end ContinuousFlexibility
