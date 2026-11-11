import ContinuousFlexibility.Analysis.PlanarInverseRegularity
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Genuine planar inverse germs from actual inverse identities

The inverse function theorem makes the image of an open smooth
nondegenerate chart open. Injectivity then identifies any actual right
inverse with its smooth local inverse on a full target neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem n04b_isOpen_image_of_planeJacobian_ne_zero
    {F : PolarPoint → PolarPoint} {S : Set PolarPoint}
    (hS : IsOpen S) (hF : ContDiffOn ℝ ∞ F S)
    (hJ : ∀ p ∈ S, planeJacobian F p ≠ 0) :
    IsOpen (F '' S) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨p, hp, rfl⟩
  obtain ⟨e, he, hpe, _⟩ := exists_smooth_localInverse_of_planeJacobian_ne_zero
    (hF.contDiffAt (hS.mem_nhds hp)) (hJ p hp)
  have hOpen := e.isOpen_image_source_inter hS
  have hmem : F p ∈ e '' (e.source ∩ S) :=
    ⟨p, ⟨hpe, hp⟩, congrFun he p⟩
  apply mem_of_superset (hOpen.mem_nhds hmem)
  rintro q ⟨x, hx, rfl⟩
  exact ⟨x, hx.2, (congrFun he x).symm⟩

/-- The actual right inverse agrees with the genuine local inverse on a
full neighborhood. No continuity or inverse-germ hypothesis is supplied. -/
theorem n04b_boundaryInverseGerm_of_rightInverse
    {F G : PolarPoint → PolarPoint} {S T : Set PolarPoint} {p : PolarPoint}
    (hS : IsOpen S) (hT : IsOpen T)
    (hF : ContDiffAt ℝ ∞ F p) (hJ : planeJacobian F p ≠ 0)
    (hInj : InjOn F S) (hMaps : MapsTo G T S) (hRight : RightInvOn G F T)
    (hp : p ∈ S) (hFp : F p ∈ T) :
    CanonicalBoundaryInverseGerm F G p := by
  obtain ⟨e, he, hpe, hsmooth⟩ :=
    exists_smooth_localInverse_of_planeJacobian_ne_zero hF hJ
  have heq : e.symm (F p) = p := by
    rw [← he]
    exact e.left_inv hpe
  have hyt : F p ∈ e.target := by
    rw [← he]
    exact e.map_source hpe
  have hsn : S ∈ 𝓝 (e.symm (F p)) := by
    rw [heq]
    exact hS.mem_nhds hp
  have heS : ∀ᶠ y in 𝓝 (F p), e.symm y ∈ S :=
    hsmooth.continuousAt.tendsto.eventually hsn
  refine ⟨e, he, hpe, hsmooth, ?_⟩
  filter_upwards [hT.mem_nhds hFp, e.open_target.mem_nhds hyt, heS] with y hy hye hys
  apply hInj (hMaps hy) hys
  calc
    F (G y) = y := hRight hy
    _ = F (e.symm y) := by
      rw [← he]
      exact (e.right_inv hye).symm

end ContinuousFlexibility.Analysis
