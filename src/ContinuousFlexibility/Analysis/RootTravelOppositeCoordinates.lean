import ContinuousFlexibility.Analysis.N04bRootInteriorRegularity

/-!
# The two root coordinates of one actual travel chart

The two orientations use complementary travel times. Their coordinate,
height and Jacobian relations hold throughout the full open travel strip,
including points beyond either artificial half cut. No reference half or
state-dependent domain is identified with another domain here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- The other root coordinate, expressed using the same total travel. -/
def n04bOppositeRootRadial (T ξ : ℝ) : ℝ :=
  n04bRootCoordinate (T - n04bRootTravel ξ)

/-- The root change preserves the actual travel angle. -/
def n04bOppositeRootMap (T : ℝ) (q : PolarPoint) : PolarPoint :=
  (n04bOppositeRootRadial T q.1, q.2)

theorem n04bTravelOrientation_not (T : ℝ) (side : Bool) (s : ℝ) :
    n04bTravelOrientation T (!side) s = T - n04bTravelOrientation T side s := by
  cases side <;> simp [n04bTravelOrientation] <;> ring

theorem n04b_rootHalfCoordinate_opposite {T s : ℝ} (side : Bool)
    (hs : s ∈ Ioo (0 : ℝ) T) :
    n04bRootHalfCoordinate T side s =
      n04bOppositeRootRadial T (n04bRootHalfCoordinate T (!side) s) := by
  have ho := n04b_travelOrientation_pos_of_fullStrip (!side) hs
  unfold n04bOppositeRootRadial n04bRootHalfCoordinate
  rw [n04b_rootTravel_rootCoordinate ho.le, n04bTravelOrientation_not]
  congr 1
  ring

theorem n04b_rootHalfCoordinate_travel_sum {T s : ℝ} (side : Bool)
    (hs : s ∈ Ioo (0 : ℝ) T) :
    n04bRootTravel (n04bRootHalfCoordinate T side s) +
        n04bRootTravel (n04bRootHalfCoordinate T (!side) s) = T := by
  have ha := n04b_travelOrientation_pos_of_fullStrip side hs
  have hb := n04b_travelOrientation_pos_of_fullStrip (!side) hs
  change n04bRootTravel (n04bRootCoordinate (n04bTravelOrientation T side s)) +
    n04bRootTravel (n04bRootCoordinate (n04bTravelOrientation T (!side) s)) = T
  rw [n04b_rootTravel_rootCoordinate ha.le, n04b_rootTravel_rootCoordinate hb.le,
    n04bTravelOrientation_not]
  ring

theorem n04b_rootPhysicalChart_opposite
    {F : PolarPoint → PolarPoint} {T : ℝ} (side : Bool) {p : PolarPoint}
    (hp : (F p).1 ∈ Ioo (0 : ℝ) T) :
    n04bRootPhysicalChart F T side p =
      n04bOppositeRootMap T (n04bRootPhysicalChart F T (!side) p) := by
  apply Prod.ext
  · exact n04b_rootHalfCoordinate_opposite side hp
  · rfl

theorem n04bOppositeRootRadial_pos {T ξ : ℝ}
    (htravel : n04bRootTravel ξ < T) : 0 < n04bOppositeRootRadial T ξ :=
  n04bRootCoordinate_pos (sub_pos.mpr htravel)

theorem n04b_contDiffAt_oppositeRootRadial {T ξ : ℝ}
    (hξ : 0 < ξ) (htravel : n04bRootTravel ξ < T) :
    ContDiffAt ℝ ∞ (n04bOppositeRootRadial T) ξ := by
  have hi : ContDiffAt ℝ ∞ (fun y : ℝ => T - n04bRootTravel y) ξ :=
    contDiffAt_const.sub (n04b_contDiffAt_rootTravel hξ)
  exact (n04b_contDiffAt_rootCoordinate (sub_pos.mpr htravel)).comp ξ hi

theorem n04b_hasDerivAt_oppositeRootRadial {T ξ : ℝ}
    (hξ : 0 < ξ) (htravel : n04bRootTravel ξ < T) :
    HasDerivAt (n04bOppositeRootRadial T)
      (-(Real.sqrt ξ / Real.sqrt (n04bOppositeRootRadial T ξ))) ξ := by
  have hd := (n04b_hasDerivAt_rootCoordinate (sub_pos.mpr htravel)).comp ξ
    ((n04b_hasDerivAt_rootTravel hξ).const_sub T)
  change HasDerivAt (fun y => n04bRootCoordinate (T - n04bRootTravel y)) _ ξ
  apply hd.congr_deriv
  simp only [n04bOppositeRootRadial, div_eq_mul_inv]
  ring

theorem n04bRootDifferentialScale_opposite
    {F : PolarPoint → PolarPoint} {T : ℝ} (side : Bool) {p : PolarPoint}
    (hp : (F p).1 ∈ Ioo (0 : ℝ) T) :
    n04bRootDifferentialScale F T side p =
      -(Real.sqrt (n04bRootPhysicalChart F T (!side) p).1 /
          Real.sqrt (n04bRootPhysicalChart F T side p).1) *
        n04bRootDifferentialScale F T (!side) p := by
  have ha := Real.sqrt_pos.mpr (n04bRootPhysicalChart_fst_pos
    (n04b_travelOrientation_pos_of_fullStrip side hp))
  have hb := Real.sqrt_pos.mpr (n04bRootPhysicalChart_fst_pos
    (n04b_travelOrientation_pos_of_fullStrip (!side) hp))
  have hsign : (if side then (-1 : ℝ) else 1) =
      -(if !side then (-1 : ℝ) else 1) := by cases side <;> norm_num
  unfold n04bRootDifferentialScale
  rw [hsign]
  field_simp [ha.ne', hb.ne'] <;> ring

/-- Both rows of the actual differential, for an arbitrary direction. -/
theorem n04b_fderiv_rootPhysicalChart_opposite
    {F : PolarPoint → PolarPoint} {T : ℝ} (side : Bool) {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (hp : (F p).1 ∈ Ioo (0 : ℝ) T)
    (v : PolarPoint) :
    fderiv ℝ (n04bRootPhysicalChart F T side) p v =
      (-(Real.sqrt (n04bRootPhysicalChart F T (!side) p).1 /
          Real.sqrt (n04bRootPhysicalChart F T side p).1) *
          (fderiv ℝ (n04bRootPhysicalChart F T (!side)) p v).1,
        (fderiv ℝ (n04bRootPhysicalChart F T (!side)) p v).2) := by
  simp only [n04b_fderiv_rootPhysicalChart_apply hF
      (n04b_travelOrientation_pos_of_fullStrip side hp) v,
    n04b_fderiv_rootPhysicalChart_apply hF
      (n04b_travelOrientation_pos_of_fullStrip (!side) hp) v,
    n04bRootDifferentialScale_opposite side hp]
  apply Prod.ext
  · ring
  · rfl

theorem n04b_abs_planeJacobian_rootPhysicalChart_opposite
    {F : PolarPoint → PolarPoint} {T : ℝ} (side : Bool) {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) (hp : (F p).1 ∈ Ioo (0 : ℝ) T) :
    |planeJacobian (n04bRootPhysicalChart F T side) p| =
      |planeJacobian (n04bRootPhysicalChart F T (!side)) p| *
        Real.sqrt ((n04bRootPhysicalChart F T (!side) p).1 /
          (n04bRootPhysicalChart F T side p).1) := by
  have hsa := n04b_travelOrientation_pos_of_fullStrip side hp
  have hsb := n04b_travelOrientation_pos_of_fullStrip (!side) hp
  have ha := n04bRootPhysicalChart_fst_pos hsa
  have hb := n04bRootPhysicalChart_fst_pos hsb
  rw [n04b_planeJacobian_rootPhysicalChart hF hsa,
    n04b_planeJacobian_rootPhysicalChart hF hsb, abs_mul, abs_mul,
    n04bRootDifferentialScale_abs hsa, n04bRootDifferentialScale_abs hsb,
    Real.sqrt_div' _ ha.le]
  field_simp [(Real.sqrt_pos.mpr ha).ne', (Real.sqrt_pos.mpr hb).ne'] <;> ring

/-- The coefficient and characteristic gap are common at the physical point.
Only the positive root coordinate changes the height. -/
theorem n04b_rootPhysicalHeight_opposite
    {A : SymmetricCoefficients} {v : PolarPoint → ℝ}
    {F : PolarPoint → PolarPoint} {T : ℝ} (side : Bool) {p : PolarPoint}
    (ha : 0 < A.a p) (hv : 0 < v p) (hp : (F p).1 ∈ Ioo (0 : ℝ) T) :
    n04bRootPhysicalHeight A v F T side p =
      n04bRootPhysicalHeight A v F T (!side) p *
        Real.sqrt (Real.sqrt (n04bRootPhysicalChart F T side p).1 /
          Real.sqrt (n04bRootPhysicalChart F T (!side) p).1) := by
  have hsa := Real.sqrt_pos.mpr (n04bRootPhysicalChart_fst_pos
    (n04b_travelOrientation_pos_of_fullStrip side hp))
  have hsb := Real.sqrt_pos.mpr (n04bRootPhysicalChart_fst_pos
    (n04b_travelOrientation_pos_of_fullStrip (!side) hp))
  have hab := Real.sqrt_pos.mpr (mul_pos ha hv)
  unfold n04bRootPhysicalHeight
  rw [Real.sqrt_div' (A.a p * v p) hsa.le,
    Real.sqrt_div' (A.a p * v p) hsb.le,
    Real.sqrt_div' (Real.sqrt (n04bRootPhysicalChart F T side p).1) hsb.le]
  field_simp [hab.ne', (Real.sqrt_pos.mpr hsa).ne',
    (Real.sqrt_pos.mpr hsb).ne'] <;> ring

theorem n04b_nested_sqrt_ratio_eq_rpow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (Real.sqrt a / Real.sqrt b) = (a / b) ^ (1 / 4 : ℝ) := by
  rw [← Real.sqrt_div' a hb, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (div_nonneg ha hb)]
  norm_num

/-- The normalized two-root relation uses the actual common cut radius. -/
theorem n04b_rootHalfCoordinate_normalized_sum {T s : ℝ} (hT : 0 < T)
    (side : Bool) (hs : s ∈ Ioo (0 : ℝ) T) :
    (n04bRootHalfCoordinate T side s / n04bRootCutRadius T) ^ (3 / 2 : ℝ) +
      (n04bRootHalfCoordinate T (!side) s / n04bRootCutRadius T) ^ (3 / 2 : ℝ) = 2 := by
  have ha := n04bRootCoordinate_pos (n04b_travelOrientation_pos_of_fullStrip side hs)
  have hb := n04bRootCoordinate_pos (n04b_travelOrientation_pos_of_fullStrip (!side) hs)
  have hρ := n04bRootCutRadius_pos hT
  have hsum := n04b_rootHalfCoordinate_travel_sum side hs
  have hcut := n04b_rootTravel_cut hT
  rw [Real.div_rpow ha.le hρ.le, Real.div_rpow hb.le hρ.le, ← add_div]
  apply (div_eq_iff (Real.rpow_pos_of_pos hρ (3 / 2 : ℝ)).ne').mpr
  unfold n04bRootTravel at hsum hcut
  nlinarith

theorem n04b_rootHalfCoordinate_normalized_opposite {T s : ℝ} (hT : 0 < T)
    (side : Bool) (hs : s ∈ Ioo (0 : ℝ) T) :
    n04bRootHalfCoordinate T side s / n04bRootCutRadius T =
      (2 - (n04bRootHalfCoordinate T (!side) s /
        n04bRootCutRadius T) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
  have hsum := n04b_rootHalfCoordinate_normalized_sum hT side hs
  have hnonneg : 0 ≤ n04bRootHalfCoordinate T side s / n04bRootCutRadius T :=
    div_nonneg (n04bRootCoordinate_pos
      (n04b_travelOrientation_pos_of_fullStrip side hs)).le (n04bRootCutRadius_pos hT).le
  have he : 2 - (n04bRootHalfCoordinate T (!side) s /
      n04bRootCutRadius T) ^ (3 / 2 : ℝ) =
      (n04bRootHalfCoordinate T side s / n04bRootCutRadius T) ^ (3 / 2 : ℝ) := by
    linarith
  rw [he, ← Real.rpow_mul hnonneg]
  norm_num

end ContinuousFlexibility.Analysis
