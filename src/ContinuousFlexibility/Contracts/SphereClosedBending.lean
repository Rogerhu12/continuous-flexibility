module

public import ContinuousFlexibility.Geometry.SphereCommonCapLength
public import ContinuousFlexibility.Geometry.SphereFixedDiskBridges
public import ContinuousFlexibility.Geometry.SphereOrientedEnclosed
public import ContinuousFlexibility.Geometry.SphereImmersion

/-!
# Geometric closure of a genuine annular core

Starting with an actual core, select one cap length and one marker, and use
that same sphere family for the metric, disks, image noncongruence, outward
shape geometry and all three invariants. This is the geometric implication in
the paper. The existence of a core is a separate analytical theorem.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set

set_option backward.isDefEq.respectTransparency false

theorem IsometricGraphDevelopment.nonempty_closedBending
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R : ℝ}
    (hR : A.b < R) : Nonempty Statements.ClosedBending := by
  obtain ⟨L, hL, _, hb, hmeet, k, hk, hρexists⟩ :=
    D.exists_common_cap_markedSphere_noncongruent hR
  obtain ⟨ρ, hρ, hsmall, _, hsmooth, hregular, hnoncongruent⟩ :=
    hρexists 1 (by norm_num)
  let F := sphereGraphCapFamily D (markedCapMap R A.cRight L k ρ) R L
  let g := D.markedSphereMetric (k := k) hR hL hk.le hρ hsmall
  let O := D.markedSphereOrientedEnclosed (k := k) hR hL hk.le hρ hsmall hb hmeet
  refine ⟨{
    metric := g
    family := F
    joint_smooth := hsmooth
    phase_embedding := fun t => isSmoothEmbedding_sphere_of_mfderiv_injective
      (D.markedSphereFamily_slice_contMDiff (k := k) hR hL hρ hsmall t)
      (hregular t).2 (hregular t).1
    same_metric := fun t x v w =>
      D.markedSphereFamily_pullback_metric (k := k) hR hL hk.le hρ hsmall t x v w
    periodic := fun x t => sphereGraphCapFamily_periodic D (markedCapMap R A.cRight L k ρ) R L x t
    fixed_regions := D.markedSphereFixedDiskRegions (k := k) hR hL hρ hsmall
    noncongruent := hnoncongruent
    enclosed := O
    area_finite := D.markedSphereFamily_area_lt_top (k := k) hR hL hρ hsmall
    area_positive := D.markedSphereFamily_area_pos (k := k) hR hL hρ hsmall
    area_constant := D.markedSphereFamily_area_invariant (k := k) hR hL hρ hsmall hmeet
    volume_finite := fun t => D.markedCapInterior_volume_lt_top t R L k ρ hL hk.le hρ
    volume_positive := fun t => D.markedCapInterior_volume_pos hR hL t k ρ hk.le hρ (hb t)
    volume_constant := fun t => D.markedCapInterior_volume hR hL t k ρ hk.le hρ hsmall
    mean_integrable := fun t =>
      D.integrable_markedSphereAmbientMean (k := k) hR hL hk.le hρ hsmall t (hmeet t)
    mean_constant := D.markedSphereTotalMean_invariant (k := k) hR hL hk.le hρ hsmall hmeet
  }⟩

/-- The full geometric output follows from a genuinely inhabited annular
core, without a separate cap, embedding, metric, or invariant hypothesis. -/
theorem mainStatement_of_flatAnnularCore
    (hcore : Nonempty FlatAnnularCore) : Statements.MainStatement := by
  obtain ⟨A⟩ := hcore
  exact A.graphDevelopment.nonempty_closedBending (R := A.b + 1) (by linarith)

end ContinuousFlexibility
