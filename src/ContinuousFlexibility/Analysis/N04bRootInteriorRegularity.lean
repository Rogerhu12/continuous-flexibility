module

public import ContinuousFlexibility.Analysis.N04bConstructedRootTransmission
public import ContinuousFlexibility.Analysis.N04bContinuousInverseGerm
public import ContinuousFlexibility.Geometry.PlanarOrientation
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Genuine interior germs of the explicit root travel formulas

The formulas extend across the artificial positive cut radius, since its
travel value lies inside the full travel strip. Their actual derivatives,
smooth height and actual inverse give a full inverse germ there.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04b_continuous_rootCoordinate : Continuous n04bRootCoordinate :=
  (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2 / 3)).comp
    ((continuous_const.mul continuous_id).div_const 2)

theorem n04b_continuous_rootTravel : Continuous n04bRootTravel :=
  continuous_const.mul (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2))

theorem n04b_continuous_travelOrientation (T : ℝ) (side : Bool) :
    Continuous (n04bTravelOrientation T side) := by
  cases side with
  | false => exact continuous_id
  | true => exact continuous_const.sub continuous_id

theorem n04b_continuous_rootStripChart (T : ℝ) (side : Bool) :
    Continuous (n04bRootStripChart T side) :=
  ((n04b_continuous_rootCoordinate.comp
    (n04b_continuous_travelOrientation T side)).comp continuous_fst).prodMk continuous_snd

theorem n04b_continuous_rootStripInverse (T : ℝ) (side : Bool) :
    Continuous (n04bRootStripInverse T side) :=
  (((n04b_continuous_travelOrientation T side).comp
    n04b_continuous_rootTravel).comp continuous_fst).prodMk continuous_snd

theorem n04b_contDiffAt_rootPhysicalChart
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {p : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F p)
    (hs : 0 < n04bTravelOrientation T side (F p).1) :
    ContDiffAt ℝ ∞ (n04bRootPhysicalChart F T side) p := by
  have ho : ContDiffAt ℝ ∞ (fun q => n04bTravelOrientation T side (F q).1) p := by
    cases side with
    | false => exact hF.fst
    | true => exact contDiffAt_const.sub hF.fst
  exact ((n04b_contDiffAt_rootCoordinate hs).comp p ho).prodMk hF.snd

theorem n04b_planeJacobian_rootPhysicalChart
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p)
    (hs : 0 < n04bTravelOrientation T side (F p).1) :
    planeJacobian (n04bRootPhysicalChart F T side) p =
      n04bRootDifferentialScale F T side p * planeJacobian F p := by
  unfold planeJacobian
  rw [n04b_fderiv_rootPhysicalChart_apply hF hs (1, 0),
    n04b_fderiv_rootPhysicalChart_apply hF hs (0, 1)]
  ring

theorem n04b_contDiffAt_rootPhysicalHeight
    {A : SymmetricCoefficients} {v : PolarPoint → ℝ}
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {p : PolarPoint}
    (ha : ContDiffAt ℝ ∞ A.a p) (hv : ContDiffAt ℝ ∞ v p)
    (hF : ContDiffAt ℝ ∞ F p)
    (hap : 0 < A.a p) (hvp : 0 < v p)
    (hs : 0 < n04bTravelOrientation T side (F p).1) :
    ContDiffAt ℝ ∞ (n04bRootPhysicalHeight A v F T side) p := by
  have hξ := n04bRootPhysicalChart_fst_pos hs
  have hsqrt : ContDiffAt ℝ ∞
      (fun q => Real.sqrt (n04bRootPhysicalChart F T side q).1) p :=
    (n04b_contDiffAt_rootPhysicalChart hF hs).fst.sqrt hξ.ne'
  have hQ : ContDiffAt ℝ ∞
      (fun q => A.a q * v q / Real.sqrt (n04bRootPhysicalChart F T side q).1) p :=
    (ha.mul hv).div hsqrt (Real.sqrt_pos.mpr hξ).ne'
  have hQpos : 0 < A.a p * v p / Real.sqrt (n04bRootPhysicalChart F T side p).1 :=
    div_pos (mul_pos hap hvp) (Real.sqrt_pos.mpr hξ)
  exact (hQ.sqrt hQpos.ne').inv (Real.sqrt_pos.mpr hQpos).ne'

theorem n04bRootStripInverse_chart_of_oriented_nonneg
    (T : ℝ) (side : Bool) {q : PolarPoint}
    (hq : 0 ≤ n04bTravelOrientation T side q.1) :
    n04bRootStripInverse T side (n04bRootStripChart T side q) = q := by
  apply Prod.ext
  · change n04bTravelOrientation T side
      (n04bRootTravel (n04bRootCoordinate (n04bTravelOrientation T side q.1))) = q.1
    rw [n04b_rootTravel_rootCoordinate hq, n04bTravelOrientation_involutive]
  · rfl

theorem n04b_travelOrientation_pos_of_fullStrip
    {T : ℝ} (side : Bool) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) :
    0 < n04bTravelOrientation T side s := by
  cases side with
  | false => exact hs.1
  | true => exact sub_pos.mpr hs.2

/-- The actual full travel inverse supplies a genuine inverse germ of
the root formula at every physical interior point, including the cut. -/
theorem n04b_rootPhysical_interior_inverse_germ
    {F X : PolarPoint → PolarPoint} {Ω : Set PolarPoint} {T : ℝ}
    (side : Bool)
    (hMaps : MapsTo F Ω (Ioo (0 : ℝ) T ×ˢ univ))
    (hLeft : LeftInvOn X F Ω)
    (hRight : RightInvOn X F (Ioo (0 : ℝ) T ×ˢ univ))
    (hX : ContDiffOn ℝ ∞ X (Ioo (0 : ℝ) T ×ˢ univ))
    {p : PolarPoint} (hp : p ∈ Ω)
    (hF : ContDiffAt ℝ ∞ F p) (hJ : planeJacobian F p ≠ 0) :
    CanonicalBoundaryInverseGerm (n04bRootPhysicalChart F T side)
      (n04bRootPhysicalInverse X T side) p := by
  let q := n04bRootPhysicalChart F T side p
  have hs := n04b_travelOrientation_pos_of_fullStrip side (hMaps hp).1
  have hq : 0 < q.1 := n04bRootPhysicalChart_fst_pos hs
  have hBack : n04bRootStripInverse T side q = F p :=
    n04bRootStripInverse_chart_of_oriented_nonneg T side hs.le
  have hBackMem : n04bRootStripInverse T side q ∈
      Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) := by
    rw [hBack]
    exact hMaps hp
  have hXAt := hX.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hBackMem)
  have hInverse : ContDiffAt ℝ ∞ (n04bRootPhysicalInverse X T side) q :=
    hXAt.comp q (n04b_contDiffAt_rootStripInverse T side hq)
  have hValue : n04bRootPhysicalInverse X T side q = p := by
    change X (n04bRootStripInverse T side q) = p
    rw [hBack]
    exact hLeft hp
  have hNear : ∀ᶠ y in 𝓝 q,
      n04bRootStripInverse T side y ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) :=
    (n04b_continuous_rootStripInverse T side).continuousAt.tendsto.eventually
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hBackMem)
  have hNearPos : ∀ᶠ y : PolarPoint in 𝓝 q, 0 < y.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hq
  have hInverseRight : ∀ᶠ y in 𝓝 q,
      n04bRootPhysicalChart F T side (n04bRootPhysicalInverse X T side y) = y := by
    filter_upwards [hNear, hNearPos] with y hy hy0
    change n04bRootStripChart T side (F (X (n04bRootStripInverse T side y))) = y
    rw [hRight hy]
    exact n04bRootStripChart_inverse_of_nonneg T side hy0.le
  apply n04b_boundaryInverseGerm_of_continuous_rightInverse
    (n04b_contDiffAt_rootPhysicalChart hF hs) ?_ hInverse.continuousAt hValue hInverseRight
  rw [n04b_planeJacobian_rootPhysicalChart (hF.differentiableAt (by simp)) hs]
  exact mul_ne_zero (n04bRootDifferentialScale_ne_zero hs) hJ

end ContinuousFlexibility.Analysis
