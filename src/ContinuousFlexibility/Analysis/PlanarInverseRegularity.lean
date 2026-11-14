module

public import ContinuousFlexibility.Analysis.CanonicalEndpointInverse
public import Mathlib.Data.Set.Function

/-!
# Smoothness of actual planar inverses on open sets

A pointwise local inverse from the actual inverse function theorem agrees
with any right inverse that takes its values in the injectivity domain.
No continuity of the supplied right inverse is assumed. In particular,
a genuine bijection of two open sets has a smooth actual `invFunOn`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Injectivity identifies an actual right inverse with the local smooth
inverse. The maps-to condition is sufficient; inverse continuity is a
conclusion of the argument. -/
theorem contDiffOn_planar_rightInverse_of_injOn
    {F G : PolarPoint → PolarPoint} {S T : Set PolarPoint}
    (hS : IsOpen S) (hT : IsOpen T)
    (hF : ContDiffOn ℝ ∞ F S)
    (hJ : ∀ p ∈ S, planeJacobian F p ≠ 0)
    (hInj : InjOn F S) (hG : MapsTo G T S) (hRight : RightInvOn G F T) :
    ContDiffOn ℝ ∞ G T := by
  intro y hy
  have hp : G y ∈ S := hG hy
  obtain ⟨e, he, hpe, hlocal⟩ :=
    exists_smooth_localInverse_of_planeJacobian_ne_zero
      (hF.contDiffAt (hS.mem_nhds hp)) (hJ (G y) hp)
  have heq : e.symm y = G y := by
    calc
      e.symm y = e.symm (F (G y)) := congrArg e.symm (hRight hy).symm
      _ = G y := by
        rw [← he]
        exact e.left_inv hpe
  have hsmooth : ContDiffAt ℝ ∞ e.symm y := by
    simpa only [hRight hy] using hlocal
  have hyt : y ∈ e.target := by
    rw [← hRight hy, ← he]
    exact e.map_source hpe
  have hsn : S ∈ 𝓝 (e.symm y) := by
    rw [heq]
    exact hS.mem_nhds hp
  have heS : ∀ᶠ z in 𝓝 y, e.symm z ∈ S :=
    hsmooth.continuousAt.tendsto.eventually hsn
  have hsame : G =ᶠ[𝓝 y] e.symm := by
    filter_upwards [hT.mem_nhds hy, e.open_target.mem_nhds hyt, heS] with z hz hze hzs
    apply hInj (hG hz) hzs
    calc
      F (G z) = z := hRight hz
      _ = F (e.symm z) := by
        rw [← he]
        exact (e.right_inv hze).symm
  exact (hsmooth.congr_of_eventuallyEq hsame).contDiffWithinAt

/-- The chosen inverse on the actual source of a planar bijection is
smooth throughout the actual open target. -/
theorem contDiffOn_planar_invFunOn_of_bijOn
    {F : PolarPoint → PolarPoint} {S T : Set PolarPoint}
    (hS : IsOpen S) (hT : IsOpen T)
    (hF : ContDiffOn ℝ ∞ F S)
    (hJ : ∀ p ∈ S, planeJacobian F p ≠ 0)
    (hBij : BijOn F S T) :
    ContDiffOn ℝ ∞ (Function.invFunOn F S) T :=
  contDiffOn_planar_rightInverse_of_injOn hS hT hF hJ hBij.injOn
    hBij.surjOn.mapsTo_invFunOn hBij.surjOn.rightInvOn_invFunOn

end ContinuousFlexibility.Analysis
