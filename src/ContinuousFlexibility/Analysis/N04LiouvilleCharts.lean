import ContinuousFlexibility.Scalar.FormPullback
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Reference Liouville charts on compact radial pieces

A radial interval is sent to the unit interval, with either orientation, while
the lifted angular coordinate is unchanged. The height is determined by the
actual positive reference density: its square times the reference density and
the absolute actual Jacobian is one.

These are the reference geometric charts used in N04 Part A. No assertion about
the state-dependent characteristic coordinates or the Tricomi operator in
Part B is made here. Closed physical endpoints are regular because the
reference density is positive there; the chart itself is globally smooth.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Affine radial coordinate; reversal sends the right endpoint to zero. -/
def n04UnitCoordinate (l r : ℝ) (reversed : Bool) (x : ℝ) : ℝ :=
  if reversed then (r - x) / (r - l) else (x - l) / (r - l)

/-- The inverse affine radial coordinate with the same orientation. -/
def n04UnitInverseCoordinate (l r : ℝ) (reversed : Bool) (y : ℝ) : ℝ :=
  if reversed then r - (r - l) * y else l + (r - l) * y

/-- The radial derivative of the affine chart. -/
def n04UnitSlope (l r : ℝ) (reversed : Bool) : ℝ :=
  if reversed then -(r - l)⁻¹ else (r - l)⁻¹

/-- Unit-width cylindrical chart, with the angular lift fixed. -/
def n04UnitChart (l r : ℝ) (reversed : Bool) (p : PolarPoint) : PolarPoint :=
  (n04UnitCoordinate l r reversed p.1, p.2)

/-- The actual inverse of the unit-width cylindrical chart. -/
def n04UnitInverseChart (l r : ℝ) (reversed : Bool) (p : PolarPoint) : PolarPoint :=
  (n04UnitInverseCoordinate l r reversed p.1, p.2)

/-- Positive Liouville height for the reference radial density. -/
def n04LiouvilleHeight (w : ℝ → ℝ) (l r : ℝ) (p : PolarPoint) : ℝ :=
  (w p.1 / (r - l)) ^ (-1 / 2 : ℝ)

theorem n04UnitInverseCoordinate_coordinate {l r : ℝ} (hlr : l < r)
    (reversed : Bool) (x : ℝ) :
    n04UnitInverseCoordinate l r reversed (n04UnitCoordinate l r reversed x) = x := by
  have hΔ : r - l ≠ 0 := (sub_pos.mpr hlr).ne'
  cases reversed <;>
    dsimp [n04UnitInverseCoordinate, n04UnitCoordinate] <;>
    field_simp [hΔ] <;> ring

theorem n04UnitCoordinate_inverseCoordinate {l r : ℝ} (hlr : l < r)
    (reversed : Bool) (y : ℝ) :
    n04UnitCoordinate l r reversed (n04UnitInverseCoordinate l r reversed y) = y := by
  have hΔ : r - l ≠ 0 := (sub_pos.mpr hlr).ne'
  cases reversed <;>
    dsimp [n04UnitInverseCoordinate, n04UnitCoordinate] <;>
    field_simp [hΔ] <;> ring

theorem n04UnitCoordinate_mem_Ioo {l r : ℝ} (hlr : l < r)
    (reversed : Bool) {x : ℝ} (hx : x ∈ Ioo l r) :
    n04UnitCoordinate l r reversed x ∈ Ioo (0 : ℝ) 1 := by
  have hΔ : 0 < r - l := sub_pos.mpr hlr
  cases reversed with
  | false =>
    change 0 < (x - l) / (r - l) ∧ (x - l) / (r - l) < 1
    constructor
    · exact div_pos (sub_pos.mpr hx.1) hΔ
    · apply (div_lt_iff₀ hΔ).mpr
      linarith [hx.2]
  | true =>
    change 0 < (r - x) / (r - l) ∧ (r - x) / (r - l) < 1
    constructor
    · exact div_pos (sub_pos.mpr hx.2) hΔ
    · apply (div_lt_iff₀ hΔ).mpr
      linarith [hx.1]

theorem n04UnitInverseCoordinate_mem_Ioo {l r : ℝ} (hlr : l < r)
    (reversed : Bool) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    n04UnitInverseCoordinate l r reversed y ∈ Ioo l r := by
  have hΔ : 0 < r - l := sub_pos.mpr hlr
  have h0 : 0 < (r - l) * y := mul_pos hΔ hy.1
  have h1 : (r - l) * y < (r - l) * 1 := mul_lt_mul_of_pos_left hy.2 hΔ
  cases reversed with
  | false =>
    change l < l + (r - l) * y ∧ l + (r - l) * y < r
    constructor <;> linarith
  | true =>
    change l < r - (r - l) * y ∧ r - (r - l) * y < r
    constructor <;> linarith

theorem n04UnitCoordinate_left {l r : ℝ} (hlr : l < r) (reversed : Bool) :
    n04UnitCoordinate l r reversed l = if reversed then 1 else 0 := by
  have hΔ : r - l ≠ 0 := (sub_pos.mpr hlr).ne'
  cases reversed <;> simp [n04UnitCoordinate, hΔ]

theorem n04UnitCoordinate_right {l r : ℝ} (hlr : l < r) (reversed : Bool) :
    n04UnitCoordinate l r reversed r = if reversed then 0 else 1 := by
  have hΔ : r - l ≠ 0 := (sub_pos.mpr hlr).ne'
  cases reversed <;> simp [n04UnitCoordinate, hΔ]

theorem n04UnitInverseCoordinate_zero (l r : ℝ) (reversed : Bool) :
    n04UnitInverseCoordinate l r reversed 0 = if reversed then r else l := by
  cases reversed <;> simp [n04UnitInverseCoordinate]

theorem n04UnitInverseCoordinate_one (l r : ℝ) (reversed : Bool) :
    n04UnitInverseCoordinate l r reversed 1 = if reversed then l else r := by
  cases reversed <;> dsimp [n04UnitInverseCoordinate] <;> ring

theorem n04UnitChart_mapsTo {l r : ℝ} (hlr : l < r) (reversed : Bool) :
    MapsTo (n04UnitChart l r reversed)
      (Ioo l r ×ˢ univ) (Ioo (0 : ℝ) 1 ×ˢ univ) := by
  intro p hp
  exact ⟨n04UnitCoordinate_mem_Ioo hlr reversed hp.1, mem_univ _⟩

theorem n04UnitInverseChart_mapsTo {l r : ℝ} (hlr : l < r) (reversed : Bool) :
    MapsTo (n04UnitInverseChart l r reversed)
      (Ioo (0 : ℝ) 1 ×ˢ univ) (Ioo l r ×ˢ univ) := by
  intro p hp
  exact ⟨n04UnitInverseCoordinate_mem_Ioo hlr reversed hp.1, mem_univ _⟩

theorem n04UnitInverseChart_chart {l r : ℝ} (hlr : l < r)
    (reversed : Bool) (p : PolarPoint) :
    n04UnitInverseChart l r reversed (n04UnitChart l r reversed p) = p := by
  apply Prod.ext
  · exact n04UnitInverseCoordinate_coordinate hlr reversed p.1
  · rfl

theorem n04UnitChart_inverseChart {l r : ℝ} (hlr : l < r)
    (reversed : Bool) (p : PolarPoint) :
    n04UnitChart l r reversed (n04UnitInverseChart l r reversed p) = p := by
  apply Prod.ext
  · exact n04UnitCoordinate_inverseCoordinate hlr reversed p.1
  · rfl

theorem contDiff_n04UnitCoordinate (l r : ℝ) (reversed : Bool) :
    ContDiff ℝ ∞ (n04UnitCoordinate l r reversed) := by
  cases reversed with
  | false => exact (contDiff_id.sub contDiff_const).div_const (r - l)
  | true => exact (contDiff_const.sub contDiff_id).div_const (r - l)

theorem contDiff_n04UnitInverseCoordinate (l r : ℝ) (reversed : Bool) :
    ContDiff ℝ ∞ (n04UnitInverseCoordinate l r reversed) := by
  cases reversed with
  | false => exact contDiff_const.add (contDiff_const.mul contDiff_id)
  | true => exact contDiff_const.sub (contDiff_const.mul contDiff_id)

theorem contDiff_n04UnitChart (l r : ℝ) (reversed : Bool) :
    ContDiff ℝ ∞ (n04UnitChart l r reversed) :=
  ((contDiff_n04UnitCoordinate l r reversed).comp contDiff_fst).prodMk contDiff_snd

theorem contDiff_n04UnitInverseChart (l r : ℝ) (reversed : Bool) :
    ContDiff ℝ ∞ (n04UnitInverseChart l r reversed) :=
  ((contDiff_n04UnitInverseCoordinate l r reversed).comp contDiff_fst).prodMk contDiff_snd

theorem hasDerivAt_n04UnitCoordinate (l r : ℝ) (reversed : Bool) (x : ℝ) :
    HasDerivAt (n04UnitCoordinate l r reversed) (n04UnitSlope l r reversed) x := by
  cases reversed with
  | false =>
    change HasDerivAt (fun y : ℝ => (y - l) / (r - l)) (r - l)⁻¹ x
    have hd : HasDerivAt (fun y : ℝ => (y - l) • (r - l)⁻¹)
        ((1 : ℝ) • (r - l)⁻¹) x :=
      ((hasDerivAt_id x).sub_const l).smul_const ((r - l)⁻¹)
    simpa only [smul_eq_mul, one_mul, div_eq_mul_inv] using hd
  | true =>
    change HasDerivAt (fun y : ℝ => (r - y) / (r - l)) (-(r - l)⁻¹) x
    have hd : HasDerivAt (fun y : ℝ => (r - y) • (r - l)⁻¹)
        ((0 - 1 : ℝ) • (r - l)⁻¹) x :=
      ((hasDerivAt_const x r).sub (hasDerivAt_id x)).smul_const ((r - l)⁻¹)
    simpa only [zero_sub, smul_eq_mul, neg_mul, one_mul, div_eq_mul_inv] using hd

/-- The actual derivative, in a form whose coordinate evaluations are explicit. -/
def n04UnitChartDerivative (l r : ℝ) (reversed : Bool) :
    PolarPoint →L[ℝ] PolarPoint :=
  (n04UnitSlope l r reversed • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem n04UnitChartDerivative_apply (l r : ℝ) (reversed : Bool) (v : PolarPoint) :
    n04UnitChartDerivative l r reversed v = (n04UnitSlope l r reversed * v.1, v.2) := by
  simp only [n04UnitChartDerivative, ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]

theorem hasFDerivAt_n04UnitChart (l r : ℝ) (reversed : Bool) (p : PolarPoint) :
    HasFDerivAt (n04UnitChart l r reversed) (n04UnitChartDerivative l r reversed) p := by
  have hx : HasFDerivAt
      (fun q : PolarPoint => n04UnitCoordinate l r reversed q.1)
      (n04UnitSlope l r reversed • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    simpa only [Function.comp_def] using
      (hasDerivAt_n04UnitCoordinate l r reversed p.1).comp_hasFDerivAt p
        hasFDerivAt_fst
  exact hx.prodMk hasFDerivAt_snd

theorem n04UnitChart_planeJacobian (l r : ℝ) (reversed : Bool) (p : PolarPoint) :
    planeJacobian (n04UnitChart l r reversed) p = n04UnitSlope l r reversed := by
  simp only [planeJacobian, (hasFDerivAt_n04UnitChart l r reversed p).fderiv,
    n04UnitChartDerivative_apply,
    mul_one, mul_zero, zero_mul, sub_zero]

theorem n04UnitChart_abs_planeJacobian {l r : ℝ} (hlr : l < r)
    (reversed : Bool) (p : PolarPoint) :
    |planeJacobian (n04UnitChart l r reversed) p| = (r - l)⁻¹ := by
  rw [n04UnitChart_planeJacobian]
  have hΔ : 0 < (r - l)⁻¹ := inv_pos.mpr (sub_pos.mpr hlr)
  cases reversed <;> simp [n04UnitSlope, abs_of_pos hΔ]

theorem n04UnitChart_planeJacobian_ne_zero {l r : ℝ} (hlr : l < r)
    (reversed : Bool) (p : PolarPoint) :
    planeJacobian (n04UnitChart l r reversed) p ≠ 0 := by
  apply abs_pos.mp
  rw [n04UnitChart_abs_planeJacobian hlr reversed p]
  exact inv_pos.mpr (sub_pos.mpr hlr)

theorem n04UnitChart_lift (l r : ℝ) (reversed : Bool) (P : ℝ) (p : PolarPoint) :
    n04UnitChart l r reversed (p + (0, P)) =
      n04UnitChart l r reversed p + (0, P) := by
  simp only [n04UnitChart, Prod.fst_add, Prod.snd_add,
    Prod.mk_add_mk, add_zero]

theorem n04UnitInverseChart_lift (l r : ℝ) (reversed : Bool)
    (P : ℝ) (p : PolarPoint) :
    n04UnitInverseChart l r reversed (p + (0, P)) =
      n04UnitInverseChart l r reversed p + (0, P) := by
  simp only [n04UnitInverseChart, Prod.fst_add, Prod.snd_add,
    Prod.mk_add_mk, add_zero]

theorem n04LiouvilleHeight_lift (w : ℝ → ℝ) (l r P : ℝ) (p : PolarPoint) :
    n04LiouvilleHeight w l r (p + (0, P)) = n04LiouvilleHeight w l r p := by
  simp only [n04LiouvilleHeight, Prod.fst_add, add_zero]

theorem n04UnitChart_reflection (l r : ℝ) (reversed : Bool) (p : PolarPoint) :
    n04UnitChart l r reversed (p.1, -p.2) =
      ((n04UnitChart l r reversed p).1, -(n04UnitChart l r reversed p).2) := rfl

theorem n04UnitInverseChart_reflection (l r : ℝ) (reversed : Bool) (p : PolarPoint) :
    n04UnitInverseChart l r reversed (p.1, -p.2) =
      ((n04UnitInverseChart l r reversed p).1, -(n04UnitInverseChart l r reversed p).2) := rfl

theorem n04LiouvilleHeight_reflection (w : ℝ → ℝ) (l r : ℝ) (p : PolarPoint) :
    n04LiouvilleHeight w l r (p.1, -p.2) = n04LiouvilleHeight w l r p := rfl

theorem n04UnitChart_planeJacobian_reflection (l r : ℝ) (reversed : Bool)
    (p : PolarPoint) :
    planeJacobian (n04UnitChart l r reversed) (p.1, -p.2) =
      planeJacobian (n04UnitChart l r reversed) p := by
  simp only [n04UnitChart_planeJacobian]

theorem n04LiouvilleHeight_pos {w : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) {p : PolarPoint} (hp : 0 < w p.1) :
    0 < n04LiouvilleHeight w l r p :=
  Real.rpow_pos_of_pos (div_pos hp (sub_pos.mpr hlr)) _

/-- Positivity at the point gives genuine two-sided smoothness of the height. -/
theorem contDiffAt_n04LiouvilleHeight {w : ℝ → ℝ} {l r : ℝ}
    (hw : ContDiff ℝ ∞ w) (hlr : l < r) {p : PolarPoint} (hp : 0 < w p.1) :
    ContDiffAt ℝ ∞ (n04LiouvilleHeight w l r) p := by
  have hq : ContDiffAt ℝ ∞ (fun q : PolarPoint => w q.1 / (r - l)) p :=
    ((hw.comp contDiff_fst).div_const (r - l)).contDiffAt
  exact hq.rpow_const_of_ne (div_pos hp (sub_pos.mpr hlr)).ne'

theorem contDiffOn_n04LiouvilleHeight {w : ℝ → ℝ} {l r : ℝ}
    (hw : ContDiff ℝ ∞ w) (hlr : l < r) {s : Set PolarPoint}
    (hs : ∀ p ∈ s, 0 < w p.1) :
    ContDiffOn ℝ ∞ (n04LiouvilleHeight w l r) s := by
  intro p hp
  exact (contDiffAt_n04LiouvilleHeight hw hlr (hs p hp)).contDiffWithinAt

theorem n04LiouvilleHeight_sq {w : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) {p : PolarPoint} (hp : 0 < w p.1) :
    n04LiouvilleHeight w l r p ^ 2 = (w p.1 / (r - l))⁻¹ := by
  have hq : 0 < w p.1 / (r - l) := div_pos hp (sub_pos.mpr hlr)
  dsimp only [n04LiouvilleHeight]
  rw [← Real.rpow_two, ← Real.rpow_mul hq.le]
  norm_num [Real.rpow_neg_one]

/-- Exact normalization of the reference density by the actual Jacobian. -/
theorem n04LiouvilleHeight_normalization {w : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) (reversed : Bool) {p : PolarPoint} (hp : 0 < w p.1) :
    n04LiouvilleHeight w l r p ^ 2 * w p.1 *
      |planeJacobian (n04UnitChart l r reversed) p| = 1 := by
  rw [n04LiouvilleHeight_sq hlr hp, n04UnitChart_abs_planeJacobian hlr reversed p,
    mul_assoc, ← div_eq_mul_inv]
  exact inv_mul_cancel₀ (div_pos hp (sub_pos.mpr hlr)).ne'

/-- Closed physical endpoints require only positivity on the closed interval. -/
theorem n04Liouville_closed_regular {w : ℝ → ℝ} {l r : ℝ}
    (hw : ContDiff ℝ ∞ w) (hlr : l < r) (reversed : Bool)
    (hwpos : ∀ x ∈ Icc l r, 0 < w x) {p : PolarPoint} (hp : p.1 ∈ Icc l r) :
    ContDiffAt ℝ ∞ (n04UnitChart l r reversed) p ∧
      ContDiffAt ℝ ∞ (n04LiouvilleHeight w l r) p ∧
      planeJacobian (n04UnitChart l r reversed) p ≠ 0 ∧
      0 < n04LiouvilleHeight w l r p :=
  ⟨(contDiff_n04UnitChart l r reversed).contDiffAt,
    contDiffAt_n04LiouvilleHeight hw hlr (hwpos p.1 hp),
    n04UnitChart_planeJacobian_ne_zero hlr reversed p,
    n04LiouvilleHeight_pos hlr (hwpos p.1 hp)⟩

end ContinuousFlexibility.Analysis
