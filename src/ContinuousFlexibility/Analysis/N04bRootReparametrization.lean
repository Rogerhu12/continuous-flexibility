module

public import ContinuousFlexibility.Analysis.N04bRootTravelCharts
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Nonnegative endpoints and interior regularity of the actual root maps

This module uses the single root-coordinate and oriented-strip
representations from `N04bRootTravelIntervals` and `N04bRootTravelCharts`.
It adds their nonnegative scalar bijection, endpoint identities, and
positive-argument smoothness. No fractional-power smoothness is asserted
through a root where its argument vanishes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04b_invOn_rootTravel_nonneg :
    InvOn n04bRootCoordinate n04bRootTravel (Ici 0) (Ici 0) := by
  constructor
  · intro r hr
    exact n04b_rootCoordinate_rootTravel hr
  · intro t ht
    exact n04b_rootTravel_rootCoordinate ht

theorem n04b_bijOn_rootTravel_nonneg :
    BijOn n04bRootTravel (Ici 0) (Ici 0) := by
  have hf : MapsTo n04bRootTravel (Ici 0) (Ici 0) := fun r hr =>
    mul_nonneg (by norm_num) (Real.rpow_nonneg hr _)
  have hg : MapsTo n04bRootCoordinate (Ici 0) (Ici 0) := fun t ht =>
    Real.rpow_nonneg (div_nonneg (mul_nonneg (by norm_num) ht) (by norm_num)) _
  exact ⟨hf, n04b_invOn_rootTravel_nonneg.1.injOn,
    n04b_invOn_rootTravel_nonneg.2.surjOn hg⟩

theorem n04b_bijOn_rootCoordinate_nonneg :
    BijOn n04bRootCoordinate (Ici 0) (Ici 0) := by
  have hi := n04b_invOn_rootTravel_nonneg
  exact ⟨hi.1.mapsTo n04b_bijOn_rootTravel_nonneg.surjOn,
    Set.LeftInvOn.injOn hi.2, hi.1.surjOn n04b_bijOn_rootTravel_nonneg.mapsTo⟩

theorem n04bTravelOrientation_middle (T : ℝ) (side : Bool) :
    n04bTravelOrientation T side (T / 2) = T / 2 := by
  cases side <;> dsimp [n04bTravelOrientation] <;> ring

theorem n04b_rootStripInverse_cut {T : ℝ} (hT : 0 < T) (side : Bool) (θ : ℝ) :
    n04bRootStripInverse T side (n04bRootCutRadius T, θ) = (T / 2, θ) := by
  rw [n04bRootStripInverse_eq_signedTravel]
  simp only [n04bSignedTravel, n04b_rootTravel_cut hT, sub_self, mul_zero, add_zero]

/-- The endpoint formula is algebraic and asserts no root smoothness. -/
theorem n04b_rootStripInverse_root (T : ℝ) (side : Bool) (θ : ℝ) :
    n04bRootStripInverse T side (0, θ) = (if side then T else 0, θ) := by
  rw [n04bRootStripInverse_eq_signedTravel]
  cases side <;> apply Prod.ext <;>
    norm_num [n04bSignedTravel, n04bRootTravel] <;> ring

theorem n04b_rootStripChart_cut (T : ℝ) (side : Bool) (θ : ℝ) :
    n04bRootStripChart T side (T / 2, θ) = (n04bRootCutRadius T, θ) := by
  simp only [n04bRootStripChart, n04bRootHalfCoordinate,
    n04bTravelOrientation_middle, n04b_rootCoordinate_middle]

/-- Both physical cut traces are the genuine inverse curve of the whole
travel chart, evaluated in the interior of its canonical travel strip. -/
theorem n04b_rootPhysicalInverse_cutPoint
    {Ω : Set PolarPoint} {Γ X : PolarPoint → PolarPoint} {T : ℝ}
    (hT : 0 < T) (hΓ : BijOn Γ Ω (Ioo 0 T ×ˢ (univ : Set ℝ)))
    (hX : MapsTo X (Ioo 0 T ×ˢ (univ : Set ℝ)) Ω)
    (hΓX : ∀ p ∈ Ioo 0 T ×ˢ (univ : Set ℝ), Γ (X p) = p)
    (side : Bool) (θ : ℝ) :
    n04bRootPhysicalInverse X T side (n04bRootCutRadius T, θ) =
      n04bTravelCutPoint Ω Γ (T / 2) θ := by
  rw [n04b_rootPhysicalInverse_at_cut X hT]
  exact (n04b_travelCutPoint_eq_of_inverse hΓ hX hΓX
    ⟨by linarith, by linarith⟩ θ).symm

theorem n04b_contDiffAt_rootTravel {r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ∞ n04bRootTravel r := by
  exact contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne hr.ne')

theorem n04b_contDiffAt_rootCoordinate {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ n04bRootCoordinate t := by
  have h : ContDiffAt ℝ ∞ (fun s : ℝ => 3 * s / 2) t :=
    (contDiffAt_const.mul contDiffAt_id).div_const 2
  exact h.rpow_const_of_ne
    (ne_of_gt (div_pos (mul_pos (by norm_num) ht) (by norm_num)))

theorem n04b_contDiff_travelOrientation (T : ℝ) (side : Bool) :
    ContDiff ℝ ∞ (n04bTravelOrientation T side) := by
  cases side with
  | false => exact contDiff_id
  | true => exact contDiff_const.sub contDiff_id

theorem n04b_contDiffAt_rootStripInverse (T : ℝ) (side : Bool)
    {p : PolarPoint} (hp : 0 < p.1) :
    ContDiffAt ℝ ∞ (n04bRootStripInverse T side) p := by
  rw [n04bRootStripInverse_eq_signedTravel]
  have ht : ContDiffAt ℝ ∞ (fun q : PolarPoint => n04bRootTravel q.1) p :=
    (n04b_contDiffAt_rootTravel hp).comp p contDiffAt_fst
  exact (contDiffAt_const.add (contDiffAt_const.mul
    (ht.sub contDiffAt_const))).prodMk contDiffAt_snd

theorem n04b_contDiffAt_rootStripChart (T : ℝ) (side : Bool)
    {p : PolarPoint} (hp : 0 < n04bTravelOrientation T side p.1) :
    ContDiffAt ℝ ∞ (n04bRootStripChart T side) p := by
  have ht : ContDiffAt ℝ ∞
      (fun q : PolarPoint => n04bTravelOrientation T side q.1) p :=
    (n04b_contDiff_travelOrientation T side).contDiffAt.comp p contDiffAt_fst
  exact ((n04b_contDiffAt_rootCoordinate hp).comp p ht).prodMk contDiffAt_snd

end ContinuousFlexibility.Analysis
