import ContinuousFlexibility.Contracts.GraphCapHomeomorph
import ContinuousFlexibility.Geometry.MarkedCapDisk
import ContinuousFlexibility.Geometry.GraphCapAttachment

/-!
# A fixed actual ambient deformation inserting the cap marker

The physical bump is supported strictly inside the flat top annulus. A positive
vertical scaling about the bottom plane inserts it into the top cap, fixes the
bottom plane, and is the identity near the whole moving graph disk.

The same physical bump can be nonzero above a bottom-disk point. Such a point
is fixed because its height equals the scaling center, not because the ambient
map is locally the identity. No transport of Euclidean normals is asserted.
The actual marked inside region is constructed separately by integration.
-/

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def markerAmbientBump (R L k ρ : ℝ) (q : PolarPoint) : ℝ :=
  markerBump 1 2 k ρ (q - markedCapCenter R L)

def markerAmbientScale (R L k ρ : ℝ) (q : PolarPoint) : ℝ :=
  1 + markerAmbientBump R L k ρ q / (L * capDrop)

theorem contDiff_markerAmbientBump (R L k ρ : ℝ) :
    ContDiff ℝ ∞ (markerAmbientBump R L k ρ) :=
  (contDiff_markerBump 1 2 k ρ).comp (contDiff_id.sub contDiff_const)

theorem contDiff_markerAmbientScale (R L k ρ : ℝ) :
    ContDiff ℝ ∞ (markerAmbientScale R L k ρ) :=
  contDiff_const.add ((contDiff_markerAmbientBump R L k ρ).div_const _)

theorem markerAmbientBump_nonneg (R L : ℝ) {k ρ : ℝ}
    (hk : 0 ≤ k) (hρ : 0 < ρ) (q : PolarPoint) : 0 ≤ markerAmbientBump R L k ρ q :=
  (markerBump_bounds (by norm_num) (by norm_num) hk hρ.ne' _).1

theorem markerAmbientScale_pos (R : ℝ) {L k ρ : ℝ}
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (q : PolarPoint) :
    0 < markerAmbientScale R L k ρ q := by
  have hd : 0 < L * capDrop := mul_pos hL capDrop_pos
  have hb := div_nonneg (markerAmbientBump_nonneg R L hk hρ q) hd.le
  unfold markerAmbientScale
  linarith

/-- A strict support buffer also separates the physical marker from both
turning circles of the cap, including their full neighborhoods. -/
theorem markerAmbientBump_support_bounds {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {q : PolarPoint} (hq : markerAmbientBump R L k ρ q ≠ 0) :
    R + L / 16 < cartesianRadius q ∧ cartesianRadius q < R + 3 * L / 16 := by
  refine ⟨markedCap_marker_support_lower hR hL hρ hsmall hq, ?_⟩
  have hd := markedCap_marker_support_distance hρ hq
  have htri : cartesianRadius q ≤ cartesianRadius (q - markedCapCenter R L) +
      cartesianRadius (markedCapCenter R L) := by
    simpa only [cartesianRadius, map_sub, sub_add_cancel] using
      (norm_add_le (Complex.equivRealProdCLM.symm q -
        Complex.equivRealProdCLM.symm (markedCapCenter R L))
        (Complex.equivRealProdCLM.symm (markedCapCenter R L)))
  rw [markedCapCenter_radius hR hL] at htri
  linarith

theorem markerAmbientBump_eq_zero_of_inner {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {q : PolarPoint} (hq : cartesianRadius q ≤ R + L / 16) :
    markerAmbientBump R L k ρ q = 0 := by
  by_contra hn
  exact not_lt_of_ge hq (markerAmbientBump_support_bounds hR hL hρ hsmall hn).1

theorem markerAmbientBump_eq_zero_of_outer {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {q : PolarPoint} (hq : R + 3 * L / 16 ≤ cartesianRadius q) :
    markerAmbientBump R L k ρ q = 0 := by
  by_contra hn
  exact not_lt_of_ge hq (markerAmbientBump_support_bounds hR hL hρ hsmall hn).2

/-- The same phase-independent ambient homeomorphism will define the marked
inside. Its positive scaling is proved from the actual nonnegative bump. -/
def markerAmbientHomeomorph (R h L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) : E3 ≃ₜ E3 :=
  euclideanCoordinatesHomeomorph.trans
    ((verticalScaleHomeomorph (h - L * capDrop) (markerAmbientScale R L k ρ)
      (contDiff_markerAmbientScale R L k ρ).continuous
      (markerAmbientScale_pos R hL hk hρ)).trans euclideanCoordinatesHomeomorph.symm)

@[simp] theorem markerAmbientHomeomorph_base (R h L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (v : E3) :
    graphBaseProjection (markerAmbientHomeomorph R h L k ρ hL hk hρ v) =
      graphBaseProjection v := by
  simp [markerAmbientHomeomorph, verticalScaleHomeomorph, euclideanCoordinatesHomeomorph,
    euclideanVectorOfCoordinates, graphBaseProjection, e3Basis]

@[simp] theorem markerAmbientHomeomorph_height (R h L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (v : E3) :
    markerAmbientHomeomorph R h L k ρ hL hk hρ v 2 = h - L * capDrop +
      markerAmbientScale R L k ρ (graphBaseProjection v) * (v 2 - (h - L * capDrop)) := by
  simp [markerAmbientHomeomorph, verticalScaleHomeomorph, euclideanCoordinatesHomeomorph,
    euclideanVectorOfCoordinates, graphBaseProjection, e3Basis]

@[simp] theorem markerAmbientHomeomorph_symm_base (R h L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (v : E3) :
    graphBaseProjection ((markerAmbientHomeomorph R h L k ρ hL hk hρ).symm v) =
      graphBaseProjection v := by
  simp [markerAmbientHomeomorph, verticalScaleHomeomorph, euclideanCoordinatesHomeomorph,
    euclideanVectorOfCoordinates, graphBaseProjection, e3Basis]

@[simp] theorem markerAmbientHomeomorph_symm_height (R h L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (v : E3) :
    (markerAmbientHomeomorph R h L k ρ hL hk hρ).symm v 2 = h - L * capDrop +
      (markerAmbientScale R L k ρ (graphBaseProjection v))⁻¹ *
        (v 2 - (h - L * capDrop)) := by
  simp [markerAmbientHomeomorph, verticalScaleHomeomorph, euclideanCoordinatesHomeomorph,
    euclideanVectorOfCoordinates, graphBaseProjection, e3Basis]

theorem markerAmbientHomeomorph_fixes_bottom (R h L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) {v : E3}
    (hv : v 2 = h - L * capDrop) : markerAmbientHomeomorph R h L k ρ hL hk hρ v = v := by
  apply e3_eq_of_base_height
  · exact markerAmbientHomeomorph_base R h L k ρ hL hk hρ v
  · simp only [markerAmbientHomeomorph_height, hv, sub_self, mul_zero, add_zero]

theorem markerAmbientHomeomorph_eq_self_of_bump_eq_zero (R h L k ρ : ℝ)
    (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) {v : E3}
    (hv : markerAmbientBump R L k ρ (graphBaseProjection v) = 0) :
    markerAmbientHomeomorph R h L k ρ hL hk hρ v = v := by
  apply e3_eq_of_base_height
  · exact markerAmbientHomeomorph_base R h L k ρ hL hk hρ v
  · rw [markerAmbientHomeomorph_height]
    simp only [markerAmbientScale, hv, zero_div, add_zero, one_mul]
    ring

theorem markerAmbientHomeomorph_eq_self_of_inner {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (h : ℝ) {v : E3} (hv : cartesianRadius (graphBaseProjection v) ≤ R + L / 16) :
    markerAmbientHomeomorph R h L k ρ hL hk hρ v = v :=
  markerAmbientHomeomorph_eq_self_of_bump_eq_zero R h L k ρ hL hk hρ
    (markerAmbientBump_eq_zero_of_inner hR hL hρ hsmall hv)

theorem markerAmbientHomeomorph_eq_self_of_outer {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (h : ℝ) {v : E3} (hv : R + 3 * L / 16 ≤ cartesianRadius (graphBaseProjection v)) :
    markerAmbientHomeomorph R h L k ρ hL hk hρ v = v :=
  markerAmbientHomeomorph_eq_self_of_bump_eq_zero R h L k ρ hL hk hρ
    (markerAmbientBump_eq_zero_of_outer hR hL hρ hsmall hv)

theorem markerAmbientHomeomorph_inner_germ {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (h : ℝ) {v : E3} (hv : cartesianRadius (graphBaseProjection v) < R + L / 16) :
    (markerAmbientHomeomorph R h L k ρ hL hk hρ : E3 → E3) =ᶠ[𝓝 v] id := by
  have hn : ∀ᶠ w in 𝓝 v, cartesianRadius (graphBaseProjection w) < R + L / 16 :=
    (isOpen_lt (continuous_cartesianRadius.comp continuous_graphBaseProjection)
      continuous_const).mem_nhds hv
  filter_upwards [hn] with w hw
  exact markerAmbientHomeomorph_eq_self_of_inner hR hL hk hρ hsmall h hw.le

theorem markerAmbientHomeomorph_outer_germ {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (h : ℝ) {v : E3} (hv : R + 3 * L / 16 < cartesianRadius (graphBaseProjection v)) :
    (markerAmbientHomeomorph R h L k ρ hL hk hρ : E3 → E3) =ᶠ[𝓝 v] id := by
  have hn : ∀ᶠ w in 𝓝 v, R + 3 * L / 16 < cartesianRadius (graphBaseProjection w) :=
    (isOpen_lt continuous_const
      (continuous_cartesianRadius.comp continuous_graphBaseProjection)).mem_nhds hv
  filter_upwards [hn] with w hw
  exact markerAmbientHomeomorph_eq_self_of_outer hR hL hk hρ hsmall h hw.le

/-- The top, middle, and bottom branches give the actual marked cap. The
bottom branch does not require the physical bump to vanish. -/
theorem markerAmbientHomeomorph_capDiskMap {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (h : ℝ) {y : PolarPoint} (hy : cartesianRadius y ≤ 1) :
    markerAmbientHomeomorph R h L k ρ hL hk hρ (capDiskMap R h L y) =
      markedCapMap R h L k ρ y := by
  have hbase : graphBaseProjection (capDiskMap R h L y) = capDiskBase R L y := by
    simp [capDiskMap]
  apply e3_eq_of_base_height
  · simp only [markerAmbientHomeomorph_base, hbase, markedCapMap_base]
  · rw [markerAmbientHomeomorph_height, markedCapMap_height, capDiskMap_two, hbase]
    by_cases ht : capDiskParameter R L y ≤ L / 4
    · have hz : capDiskHeight R h L y = h := capMeridianHeight_eq_left h hL ht
      rw [hz]
      simp only [markedCapBump, markedCapCutoff_eq_one hL ht, one_mul,
        markerAmbientScale, markerAmbientBump]
      rw [show h - (h - L * capDrop) = L * capDrop by ring, add_mul, one_mul,
        div_mul_cancel₀ _ (mul_pos hL capDrop_pos).ne']
      ring
    · by_cases hb : 3 * L / 4 ≤ capDiskParameter R L y
      · have hz : capDiskHeight R h L y = h - L * capDrop :=
          capMeridianHeight_eq_right h hL hb
        rw [hz, markedCapBump_eq_zero_bottom hL k ρ hb]
        simp only [sub_self, mul_zero, add_zero]
      · have hs : capDiskParameter R L y ∈ Icc (L / 4) (3 * L / 4) :=
          ⟨(lt_of_not_ge ht).le, (lt_of_not_ge hb).le⟩
        have hrad : R + L / 4 ≤ cartesianRadius (capDiskBase R L y) := by
          rw [capDiskBase_radius hR hL hy]
          exact markedCap_meridian_middle_lower R hL hs
        have hzero : markerAmbientBump R L k ρ (capDiskBase R L y) = 0 :=
          markerAmbientBump_eq_zero_of_outer hR hL hρ hsmall (by linarith)
        have hmark : markedCapBump R L k ρ y = 0 := by
          change markedCapCutoff R L y * markerAmbientBump R L k ρ (capDiskBase R L y) = 0
          rw [hzero, mul_zero]
        rw [hmark]
        simp only [markerAmbientScale, hzero, zero_div, add_zero, one_mul]
        ring

/-- The actual physical projection, rather than the source disk parameter,
places every moving graph point in the fixed inner neighborhood. -/
theorem IsometricGraphDevelopment.markerAmbientHomeomorph_rotationFamily
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) {x : PolarPoint} (hx : cartesianRadius x ≤ R) :
    markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ (D.rotationFamily t x) =
      D.rotationFamily t x := by
  apply markerAmbientHomeomorph_eq_self_of_inner (A.b_pos.trans hR) hL hk hρ hsmall A.cRight
  have hr := D.phase_disk_projection_bound t hR.le hx
  linarith

theorem IsometricGraphDevelopment.markerAmbientHomeomorph_image_graphDisk
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R L k ρ : ℝ}
    (hR : A.b < R) (hL : 0 < L) (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    (t : ℝ) :
    markerAmbientHomeomorph R A.cRight L k ρ hL hk hρ '' graphPhaseDiskImage D R t =
      graphPhaseDiskImage D R t := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hw
    rw [D.markerAmbientHomeomorph_rotationFamily hR hL hk hρ hsmall t hx]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨D.rotationFamily t x, ⟨x, hx, rfl⟩,
      D.markerAmbientHomeomorph_rotationFamily hR hL hk hρ hsmall t hx⟩

end ContinuousFlexibility
