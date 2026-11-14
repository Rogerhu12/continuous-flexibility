module

public import ContinuousFlexibility.Contracts.CapInteriorClosure
public import ContinuousFlexibility.Contracts.GraphBoundaryNormals

/-!
# Actual outward normal rays for the unmarked cap disk

The solid is the existing capRevolutionInterior. The two flat pieces include
their turning circles. On the middle wall, the actual normal ray has a radial
defining function with positive derivative. No outwardness is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem capRadialOffset_gt_quarter {t : ℝ} (ht : t ∈ Ioo (1 / 4 : ℝ) (3 / 4)) :
    1 / 4 < capRadialOffset t := by
  have hleft {u : ℝ} (hu : 1 / 4 < u) (hu' : u ≤ 1 / 2) :
      1 / 4 < capRadialOffset u := by
    have hp : 0 < ∫ v in (1 / 4 : ℝ)..u, capRadialVelocity v := by
      apply intervalIntegral.integral_pos hu contDiff_capRadialVelocity.continuous.continuousOn
      · intro v hv
        exact capRadialVelocity_nonneg (hv.2.trans hu')
      · exact ⟨1 / 4, ⟨le_rfl, hu.le⟩,
          by rw [capRadialVelocity_eq_one le_rfl]; norm_num⟩
    have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (contDiff_capRadialVelocity.continuous.intervalIntegrable 0 (1 / 4))
      (contDiff_capRadialVelocity.continuous.intervalIntegrable (1 / 4) u)
    change capRadialOffset (1 / 4) + (∫ v in (1 / 4 : ℝ)..u, capRadialVelocity v) =
      capRadialOffset u at ha
    rw [capRadialOffset_eq_left le_rfl] at ha
    linarith
  by_cases h : t ≤ 1 / 2
  · exact hleft ht.1 h
  · rw [← capRadialOffset_reflection t]
    exact hleft (by linarith [ht.2]) (by linarith)

/-- The wall is strictly outside both flat turning circles at every interior height. -/
theorem capWallRadius_gt_rim (R h : ℝ) {L z : ℝ} (hL : 0 < L)
    (hz : z ∈ Ioo (h - L * capDrop) h) : R + L / 4 < capWallRadius R h L z := by
  have hp := capRadialOffset_gt_quarter
    (capHeightParameter_mem (cap_normalized_height_mem hL hz))
  unfold capWallRadius
  nlinarith [mul_lt_mul_of_pos_left hp hL]

private theorem capInterior_top_pointsOutward (R h : ℝ) {L : ℝ} (hL : 0 < L)
    {p : E3} (hp : p 2 = h) (hr : cartesianRadius (graphBaseProjection p) ≤ R + L / 4) :
    PointsOutwardFrom (capRevolutionInterior R h L) p (e3Basis 2) := by
  refine ⟨L * capDrop, mul_pos hL capDrop_pos, fun t ht => ?_⟩
  have hm : (p - t • e3Basis 2) 2 = h - t := by simp [hp, e3Basis]
  have hp' : (p + t • e3Basis 2) 2 = h + t := by simp [hp, e3Basis]
  have hb : graphBaseProjection (p - t • e3Basis 2) = graphBaseProjection p := by
    apply Prod.ext <;> simp [graphBaseProjection, e3Basis]
  have hz : h - t ∈ Ioo (h - L * capDrop) h := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  constructor
  · change (p - t • e3Basis 2) 2 ∈ Ioo (h - L * capDrop) h ∧ _
    rw [hm, hb]
    exact ⟨hz, hr.trans_lt (capWallRadius_gt_rim R h hL hz)⟩
  · intro hc
    have hh := (closure_capRevolutionInterior_subset R h hL hc).1.2
    rw [hp'] at hh
    linarith [ht.1]

private theorem capInterior_bottom_pointsOutward (R h : ℝ) {L : ℝ} (hL : 0 < L)
    {p : E3} (hp : p 2 = h - L * capDrop)
    (hr : cartesianRadius (graphBaseProjection p) ≤ R + L / 4) :
    PointsOutwardFrom (capRevolutionInterior R h L) p (-e3Basis 2) := by
  refine ⟨L * capDrop, mul_pos hL capDrop_pos, fun t ht => ?_⟩
  have hm : (p - t • (-e3Basis 2)) 2 = h - L * capDrop + t := by simp [hp, e3Basis]
  have hp' : (p + t • (-e3Basis 2)) 2 = h - L * capDrop - t := by
    simp [hp, e3Basis, sub_eq_add_neg]
  have hb : graphBaseProjection (p - t • (-e3Basis 2)) = graphBaseProjection p := by
    apply Prod.ext <;> simp [graphBaseProjection, e3Basis]
  have hz : h - L * capDrop + t ∈ Ioo (h - L * capDrop) h :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  constructor
  · change (p - t • (-e3Basis 2)) 2 ∈ Ioo (h - L * capDrop) h ∧ _
    rw [hm, hb]
    exact ⟨hz, hr.trans_lt (capWallRadius_gt_rim R h hL hz)⟩
  · intro hc
    have hh := (closure_capRevolutionInterior_subset R h hL hc).1.1
    rw [hp'] at hh
    linarith [ht.1]

private theorem capDiskNormalRay_radius (R h L t : ℝ) {y : PolarPoint} (hy : y ≠ 0)
    (hp : 0 < capMeridianRadius R L (capDiskParameter R L y) +
      t * capDownwardVelocity (capDiskParameter R L y / L)) :
    cartesianRadius (graphBaseProjection (capDiskMap R h L y + t • capDiskNormal R L y)) =
      capMeridianRadius R L (capDiskParameter R L y) +
        t * capDownwardVelocity (capDiskParameter R L y / L) := by
  have hρ := cartesianRadius_pos hy
  have hb : graphBaseProjection (capDiskMap R h L y + t • capDiskNormal R L y) =
      ((capMeridianRadius R L (capDiskParameter R L y) +
        t * capDownwardVelocity (capDiskParameter R L y / L)) / cartesianRadius y) • y := by
    apply Prod.ext <;> simp [graphBaseProjection, capDiskBase] <;> ring
  rw [hb, capDisk_radius_smul, abs_of_pos (div_pos hp hρ)]
  exact div_mul_cancel₀ _ hρ.ne'

private theorem capDiskNormalRay_height (R h L t : ℝ) (y : PolarPoint) :
    (capDiskMap R h L y + t • capDiskNormal R L y) 2 =
      capMeridianHeight h L (capDiskParameter R L y) +
        t * capRadialVelocity (capDiskParameter R L y / L) := by
  simp [capDiskHeight]

private theorem capDiskNormal_middle_pointsOutward {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) {y : PolarPoint}
    (hy : cartesianRadius y ≤ 1)
    (hs : capDiskParameter R L y / L ∈ Ioo (1 / 4 : ℝ) (3 / 4)) :
    PointsOutwardFrom (capRevolutionInterior R h L)
      (capDiskMap R h L y) (capDiskNormal R L y) := by
  let s := capDiskParameter R L y
  let r := capMeridianRadius R L s
  let z := capMeridianHeight h L s
  let d := capDownwardVelocity (s / L)
  let c := capRadialVelocity (s / L)
  let p := capDiskMap R h L y
  let n := capDiskNormal R L y
  have hy0 : y ≠ 0 := by
    intro he
    subst y
    have hh : (L + R) / L < 3 / 4 := by
      simpa [capDiskParameter, cartesianRadius] using hs.2
    have hh' := (div_lt_iff₀ hL).mp hh
    linarith
  have hr : 0 < r := capDisk_meridian_radius_pos hR hL hy hy0
  have hd : 0 < d := capDownwardVelocity_pos hs
  have hz : z ∈ Ioo (h - L * capDrop) h := by
    have hh := (capHeightDrop_mem_open_iff (s / L)).mpr hs
    dsimp only [z, capMeridianHeight]
    constructor
    · nlinarith [mul_lt_mul_of_pos_left hh.2 hL]
    · nlinarith [mul_pos hL hh.1]
  have hparameter : (h - z) / L = capHeightDrop (s / L) := by
    dsimp only [z, capMeridianHeight]
    field_simp [hL.ne']
    ring
  have hw : HasDerivAt (capWallRadius R h L) (-c / d) z := by
    have hh := hasDerivAt_capWallRadius R h hL hz
    have hinv : capHeightParameter (capHeightDrop (s / L)) = s / L :=
      capHeightParameter_drop (s := s / L) hs
    rw [hparameter, hinv] at hh
    exact hh
  have hunit : c ^ 2 + d ^ 2 = 1 := by
    dsimp only [c, d, capRadialVelocity, capDownwardVelocity]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * capTurn (s / L))]
  have hcoef : d - (-c / d) * c = d⁻¹ := by
    field_simp [hd.ne']
    nlinarith [hunit]
  let g : ℝ → ℝ := fun t => r + t * d - capWallRadius R h L (z + t * c)
  have hg : HasDerivAt g d⁻¹ 0 := by
    have hfirst : HasDerivAt (fun t : ℝ => r + t * d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add r
    have hline : HasDerivAt (fun t : ℝ => z + t * c) c 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add z
    have hw0 : HasDerivAt (capWallRadius R h L) (-c / d) (z + (0 : ℝ) * c) := by
      simpa only [zero_mul, add_zero] using hw
    have hh := hfirst.sub (hw0.comp 0 hline)
    rw [hcoef] at hh
    exact hh
  have hgzero : g 0 = 0 := by
    dsimp only [g]
    simp only [zero_mul, add_zero]
    exact sub_eq_zero.mpr (capWallRadius_at_meridian R h hL hs).symm
  obtain ⟨ε, hε, hsigns⟩ := positive_derivative_two_sided_sign hg hgzero (inv_pos.mpr hd)
  let U : Set ℝ := {t | 0 < r + t * d ∧ z + t * c ∈ Ioo (h - L * capDrop) h}
  have hradcont : Continuous (fun t : ℝ => r + t * d) :=
    continuous_const.add (continuous_id.mul continuous_const)
  have hzcont : Continuous (fun t : ℝ => z + t * c) :=
    continuous_const.add (continuous_id.mul continuous_const)
  have hU : IsOpen U :=
    (isOpen_lt continuous_const hradcont).inter (isOpen_Ioo.preimage hzcont)
  have hU0 : (0 : ℝ) ∈ U := by
    simpa only [U, mem_ofPred_eq, zero_mul, add_zero] using And.intro hr hz
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp (hU.mem_nhds hU0)
  have hray (t : ℝ) (ht : t ∈ U) :
      cartesianRadius (graphBaseProjection (p + t • n)) = r + t * d :=
    capDiskNormalRay_radius R h L t hy0 ht.1
  have hheight (t : ℝ) : (p + t • n) 2 = z + t * c :=
    capDiskNormalRay_height R h L t y
  change PointsOutwardFrom (capRevolutionInterior R h L) p n
  refine ⟨min ε δ, lt_min hε hδ, fun t ht => ?_⟩
  have htε : t ∈ Ioo (0 : ℝ) ε := ⟨ht.1, ht.2.trans_le (min_le_left ε δ)⟩
  have htδ : t < δ := ht.2.trans_le (min_le_right ε δ)
  have hplus : t ∈ U := hbound (y := t)
    (by simpa [Real.dist_eq, abs_of_pos ht.1] using htδ)
  have hminus : -t ∈ U := hbound (y := -t)
    (by simpa [Real.dist_eq, abs_neg, abs_of_pos ht.1] using htδ)
  have hsign := hsigns t htε
  have hrayminus : p - t • n = p + (-t) • n := by simp only [neg_smul, sub_eq_add_neg]
  constructor
  · rw [hrayminus]
    change (p + (-t) • n) 2 ∈ Ioo (h - L * capDrop) h ∧ _
    rw [hheight (-t), hray (-t) hminus]
    exact ⟨hminus.2, sub_neg.mp hsign.2⟩
  · intro hc
    have hh := (closure_capRevolutionInterior_subset R h hL hc).2
    rw [hheight t, capExtendedWallRadius_eq hL hplus.2, hray t hplus] at hh
    exact not_le_of_gt (sub_pos.mp hsign.1) hh

/-- The explicit unit normal points from the actual cap body to its exterior,
at every point of the closed cap disk, including the axis and turning circles. -/
theorem capDiskNormal_pointsOutwardFrom {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ)
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1) :
    PointsOutwardFrom (capRevolutionInterior R h L)
      (capDiskMap R h L y) (capDiskNormal R L y) := by
  by_cases ht : capDiskParameter R L y ≤ L / 4
  · rw [capDiskNormal_top_collar R hL ht]
    apply capInterior_top_pointsOutward R h hL
    · simpa only [capDiskMap_two, capDiskHeight] using capMeridianHeight_eq_left h hL ht
    · rw [show graphBaseProjection (capDiskMap R h L y) = capDiskBase R L y by simp [capDiskMap],
        capDiskBase_radius hR hL hy, capMeridianRadius_eq_left R hL ht]
      linarith
  · by_cases hb : 3 * L / 4 ≤ capDiskParameter R L y
    · rw [capDiskNormal_bottom_collar R hL hb]
      apply capInterior_bottom_pointsOutward R h hL
      · simpa only [capDiskMap_two, capDiskHeight] using capMeridianHeight_eq_right h hL hb
      · rw [show graphBaseProjection (capDiskMap R h L y) = capDiskBase R L y by simp [capDiskMap],
          capDiskBase_radius hR hL hy, capMeridianRadius_eq_right R hL hb]
        linarith
    · apply capDiskNormal_middle_pointsOutward hR hL h hy
      exact ⟨(lt_div_iff₀ hL).mpr (by linarith), (div_lt_iff₀ hL).mpr (by linarith)⟩

end ContinuousFlexibility
