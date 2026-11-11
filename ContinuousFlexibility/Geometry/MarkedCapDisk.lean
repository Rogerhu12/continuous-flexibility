import ContinuousFlexibility.Geometry.CapDisk
import ContinuousFlexibility.Geometry.MarkerBump
import ContinuousFlexibility.Geometry.PlanarRotations
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# A marker inserted into the actual top collar of the cap

The cutoff depends on the meridian parameter, so the elliptic bump is not
duplicated on the bottom disk with the same planar projection. The chosen
center is `(R + L / 8, 0)`, and the elliptic coefficients are fixed to `1,2`.
This file does not assert the final closed-surface curvature comparison.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def markedCapCenter (R L : ℝ) : PolarPoint := (R + L / 8, 0)

def markedCapCutoff (R L : ℝ) (y : PolarPoint) : ℝ :=
  1 - capTurn (capDiskParameter R L y / L)

def markedCapBump (R L k ρ : ℝ) (y : PolarPoint) : ℝ :=
  markedCapCutoff R L y * markerBump 1 2 k ρ (capDiskBase R L y - markedCapCenter R L)

def markedCapHeight (R h L k ρ : ℝ) (y : PolarPoint) : ℝ :=
  capDiskHeight R h L y + markedCapBump R L k ρ y

def markedCapMap (R h L k ρ : ℝ) : PolarPoint → E3 :=
  graphMap (capDiskBase R L) (markedCapHeight R h L k ρ)

def markedCapEmbeddingMap (R h L k ρ : ℝ) (y : capDiskDomain) : E3 :=
  markedCapMap R h L k ρ y

theorem markedCapCutoff_bounds (R L : ℝ) (y : PolarPoint) :
    0 ≤ markedCapCutoff R L y ∧ markedCapCutoff R L y ≤ 1 := by
  have h0 := capTurn_nonneg (capDiskParameter R L y / L)
  have h1 := capTurn_le_one (capDiskParameter R L y / L)
  dsimp [markedCapCutoff]
  constructor <;> linarith

theorem markedCapCutoff_eq_zero {R L : ℝ} (hL : 0 < L) {y : PolarPoint}
    (hy : 3 * L / 4 ≤ capDiskParameter R L y) : markedCapCutoff R L y = 0 := by
  have ht : (3 / 4 : ℝ) ≤ capDiskParameter R L y / L :=
    (le_div_iff₀ hL).2 (by linarith)
  simp [markedCapCutoff, capTurn_eq_one ht]

theorem markedCapCutoff_eq_one {R L : ℝ} (hL : 0 < L) {y : PolarPoint}
    (hy : capDiskParameter R L y ≤ L / 4) : markedCapCutoff R L y = 1 := by
  have ht : capDiskParameter R L y / L ≤ (1 / 4 : ℝ) :=
    (div_le_iff₀ hL).2 (by linarith)
  simp [markedCapCutoff, capTurn_eq_zero ht]

theorem markedCapCutoff_axis_germ {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    markedCapCutoff R L =ᶠ[𝓝 0] fun _ => 0 := by
  have hn : {y : PolarPoint | cartesianRadius y < (1 / 4 : ℝ)} ∈ 𝓝 0 :=
    (isOpen_lt continuous_cartesianRadius continuous_const).mem_nhds
      (by norm_num [cartesianRadius])
  filter_upwards [hn] with y hy
  exact markedCapCutoff_eq_zero hL (capDisk_axis_parameter hR hL hy)

theorem contDiff_markedCapCutoff {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    ContDiff ℝ ∞ (markedCapCutoff R L) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y = 0
  · subst y
    exact contDiffAt_const.congr_of_eventuallyEq (markedCapCutoff_axis_germ hR hL)
  · have hs : ContDiffAt ℝ ∞ (capDiskParameter R L) y :=
      contDiffAt_const.mul (contDiffAt_const.sub (contDiffAt_cartesianRadius hy))
    exact contDiffAt_const.sub
      (contDiff_capTurn.contDiffAt.comp y (hs.div_const L))

theorem markedCap_contDiff_base {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    ContDiff ℝ ∞ (capDiskBase R L) := by
  have hm := contDiff_capDiskMap hR hL (0 : ℝ)
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff.comp hm
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff.comp hm
  convert h0.prodMk h1 using 1
  funext y
  simp

theorem markedCap_contDiff_height {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    ContDiff ℝ ∞ (capDiskHeight R h L) := by
  have hm := contDiff_capDiskMap hR hL h
  have h2 := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff.comp hm
  convert h2 using 1
  funext y
  simp

theorem contDiff_markedCapBump {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (k ρ : ℝ) :
    ContDiff ℝ ∞ (markedCapBump R L k ρ) :=
  (contDiff_markedCapCutoff hR hL).mul
    ((contDiff_markerBump 1 2 k ρ).comp
      ((markedCap_contDiff_base hR hL).sub contDiff_const))

theorem contDiff_markedCapMap {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h k ρ : ℝ) :
    ContDiff ℝ ∞ (markedCapMap R h L k ρ) :=
  contDiff_graphMap (markedCap_contDiff_base hR hL)
    ((markedCap_contDiff_height hR hL h).add (contDiff_markedCapBump hR hL k ρ))

theorem markedCapBump_nonneg (R L : ℝ) {k ρ : ℝ} (hk : 0 ≤ k) (hρ : 0 < ρ)
    (y : PolarPoint) : 0 ≤ markedCapBump R L k ρ y :=
  mul_nonneg (markedCapCutoff_bounds R L y).1
    (markerBump_bounds (by norm_num) (by norm_num) hk hρ.ne' _).1

theorem markedCapBump_eq_zero_bottom {R L : ℝ} (hL : 0 < L) (k ρ : ℝ)
    {y : PolarPoint} (hy : 3 * L / 4 ≤ capDiskParameter R L y) :
    markedCapBump R L k ρ y = 0 := by
  simp [markedCapBump, markedCapCutoff_eq_zero hL hy]

private theorem markedCap_offset_middle_lower {t : ℝ}
    (ht : t ∈ Icc (1 / 4 : ℝ) (3 / 4)) : 1 / 4 ≤ capRadialOffset t := by
  have hm : MonotoneOn capRadialOffset (Iic (1 / 2 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic _)
      contDiff_capRadialOffset.continuous.continuousOn
    · intro x _
      exact (hasDerivAt_capRadialOffset x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hasDerivAt_capRadialOffset x).deriv]
      have hx' : x ∈ Iic (1 / 2 : ℝ) :=
        (interior_subset : interior (Iic (1 / 2 : ℝ)) ⊆ Iic (1 / 2 : ℝ)) hx
      exact capRadialVelocity_nonneg hx'
  have hleft (u : ℝ) (hu : 1 / 4 ≤ u) (hu' : u ≤ 1 / 2) :
      1 / 4 ≤ capRadialOffset u := by
    have hh := hm (show (1 / 4 : ℝ) ∈ Iic (1 / 2 : ℝ) by norm_num) hu' hu
    rw [capRadialOffset_eq_left (le_refl (1 / 4 : ℝ))] at hh
    exact hh
  by_cases ht2 : t ≤ 1 / 2
  · exact hleft t ht.1 ht2
  · rw [← capRadialOffset_reflection t]
    exact hleft (1 - t) (by linarith [ht.2]) (by linarith)

theorem markedCap_meridian_middle_lower (R : ℝ) {L s : ℝ}
    (hL : 0 < L) (hs : s ∈ Icc (L / 4) (3 * L / 4)) :
    R + L / 4 ≤ capMeridianRadius R L s := by
  have ht : s / L ∈ Icc (1 / 4 : ℝ) (3 / 4) :=
    ⟨(le_div_iff₀ hL).2 (by linarith [hs.1]),
      (div_le_iff₀ hL).2 (by linarith [hs.2])⟩
  have hh := mul_le_mul_of_nonneg_left (markedCap_offset_middle_lower ht) hL.le
  dsimp [capMeridianRadius]
  nlinarith

theorem markedCapCenter_radius {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    cartesianRadius (markedCapCenter R L) = R + L / 8 := by
  change ‖Complex.equivRealProdCLM.symm (R + L / 8, 0)‖ = R + L / 8
  rw [Complex.equivRealProdCLM_symm_apply]
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show 0 < R + L / 8 by linarith)]

private theorem markedCap_radius_le_sub_add (x p : PolarPoint) :
    cartesianRadius x ≤ cartesianRadius (x - p) + cartesianRadius p := by
  simpa only [cartesianRadius, map_sub, sub_add_cancel] using
    (norm_add_le (Complex.equivRealProdCLM.symm x - Complex.equivRealProdCLM.symm p)
      (Complex.equivRealProdCLM.symm p))

theorem markedCap_marker_support_radius {R L ρ k : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {x : PolarPoint} (hx : markerBump 1 2 k ρ (x - markedCapCenter R L) ≠ 0) :
    cartesianRadius x < R + L / 4 := by
  have hq : markerQuadratic 1 2 (x - markedCapCenter R L) < ρ ^ 2 := by
    by_contra h
    exact hx (markerBump_eq_zero hρ.ne' (le_of_not_gt h))
  have hsq := cartesianRadius_sq_coordinates (x - markedCapCenter R L)
  have hn := capDisk_radius_nonneg (x - markedCapCenter R L)
  have hd : cartesianRadius (x - markedCapCenter R L) < ρ := by
    dsimp [markerQuadratic, coordinateEuclideanPair] at hq hsq
    nlinarith [sq_nonneg (x - markedCapCenter R L).2]
  have htri := markedCap_radius_le_sub_add x (markedCapCenter R L)
  rw [markedCapCenter_radius hR hL] at htri
  linarith

/-- A nonzero marker can only occur on the top horizontal branch. -/
theorem markedCapBump_nonzero_top {R L ρ k : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1) (hb : markedCapBump R L k ρ y ≠ 0) :
    capDiskParameter R L y < L / 4 := by
  have hc := (mul_ne_zero_iff.mp hb).1
  have hm := (mul_ne_zero_iff.mp hb).2
  have hhigh : capDiskParameter R L y < 3 * L / 4 := by
    by_contra hn
    exact hc (markedCapCutoff_eq_zero hL (le_of_not_gt hn))
  have hrad := markedCap_marker_support_radius hR hL hρ hsmall hm
  rw [capDiskBase_radius hR hL hy] at hrad
  by_contra htop
  have hlow := markedCap_meridian_middle_lower R hL ⟨le_of_not_gt htop, hhigh.le⟩
  linarith

theorem markedCapBump_nonzero_height {R L ρ k : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ)
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1) (hb : markedCapBump R L k ρ y ≠ 0) :
    capDiskHeight R h L y = h :=
  capMeridianHeight_eq_left h hL (markedCapBump_nonzero_top hR hL hρ hsmall hy hb).le

theorem markedCapBump_eq_zero_of_not_top {R L ρ k : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1) (hs : L / 4 ≤ capDiskParameter R L y) :
    markedCapBump R L k ρ y = 0 := by
  by_contra hn
  exact (not_lt_of_ge hs) (markedCapBump_nonzero_top hR hL hρ hsmall hy hn)

@[simp] theorem markedCapMap_base (R h L k ρ : ℝ) (y : PolarPoint) :
    graphBaseProjection (markedCapMap R h L k ρ y) = capDiskBase R L y := by
  simp [markedCapMap]

@[simp] theorem markedCapMap_height (R h L k ρ : ℝ) (y : PolarPoint) :
    markedCapMap R h L k ρ y 2 = capDiskHeight R h L y + markedCapBump R L k ρ y := by
  simp [markedCapMap, markedCapHeight]

theorem markedCapMap_injOn {R L k ρ : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ) :
    Set.InjOn (markedCapMap R h L k ρ) {y : PolarPoint | cartesianRadius y ≤ 1} := by
  intro x hx y hy he
  have hb : capDiskBase R L x = capDiskBase R L y := by
    simpa using congrArg graphBaseProjection he
  have hz : capDiskHeight R h L x + markedCapBump R L k ρ x =
      capDiskHeight R h L y + markedCapBump R L k ρ y := by
    simpa using congrArg (fun v : E3 => v 2) he
  have hbx := markedCapBump_nonneg R L hk hρ x
  have hby := markedCapBump_nonneg R L hk hρ y
  have hzx := (capMeridianHeight_bounds h hL (capDiskParameter R L x)).2
  have hzy := (capMeridianHeight_bounds h hL (capDiskParameter R L y)).2
  change capDiskHeight R h L x ≤ h at hzx
  change capDiskHeight R h L y ≤ h at hzy
  have hez : capDiskHeight R h L x = capDiskHeight R h L y := by
    by_cases hx0 : markedCapBump R L k ρ x = 0
    · by_cases hy0 : markedCapBump R L k ρ y = 0
      · simpa [hx0, hy0] using hz
      · have hytop := markedCapBump_nonzero_height hR hL hρ hsmall h hy hy0
        have hypos : 0 < markedCapBump R L k ρ y := lt_of_le_of_ne hby (Ne.symm hy0)
        linarith
    · have hxtop := markedCapBump_nonzero_height hR hL hρ hsmall h hx hx0
      by_cases hy0 : markedCapBump R L k ρ y = 0
      · have hxpos : 0 < markedCapBump R L k ρ x := lt_of_le_of_ne hbx (Ne.symm hx0)
        linarith
      · exact hxtop.trans (markedCapBump_nonzero_height hR hL hρ hsmall h hy hy0).symm
  apply capDiskMap_injOn hR hL h hx hy
  ext i
  fin_cases i <;> simp [capDiskMap, hb, hez]

theorem markedCap_top_height_germ {R L : ℝ} (hL : 0 < L) (h : ℝ) {y : PolarPoint}
    (hy : capDiskParameter R L y < L / 4) :
    capDiskHeight R h L =ᶠ[𝓝 y] fun _ => h := by
  have hc : Continuous (capDiskParameter R L) :=
    continuous_const.mul (continuous_const.sub continuous_cartesianRadius)
  have hn : {z : PolarPoint | capDiskParameter R L z < L / 4} ∈ 𝓝 y :=
    (isOpen_lt hc continuous_const).mem_nhds hy
  filter_upwards [hn] with z hz
  exact capMeridianHeight_eq_left h hL hz.le

theorem markedCap_base_fderiv_injective_top {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (h : ℝ) {y : PolarPoint} (hy : cartesianRadius y ≤ 1)
    (htop : capDiskParameter R L y < L / 4) :
    Function.Injective (fderiv ℝ (capDiskBase R L) y) := by
  have hp := (markedCap_contDiff_base hR hL).differentiable (by simp) y
  have hz := (markedCap_contDiff_height hR hL h).differentiable (by simp) y
  have hdz : fderiv ℝ (capDiskHeight R h L) y = 0 := by
    rw [(markedCap_top_height_germ hL h htop).fderiv_eq (𝕜 := ℝ)]
    exact fderiv_const_apply h
  intro u v huv
  apply capDiskMap_fderiv_injective hR hL h hy
  rw [capDiskMap, fderiv_graphMap hp hz, hdz]
  ext i
  fin_cases i <;> simp [huv]

theorem markedCapBump_fderiv_eq_zero {R L k ρ : ℝ} (hk : 0 ≤ k) (hρ : 0 < ρ)
    {y : PolarPoint} (hy : markedCapBump R L k ρ y = 0) :
    fderiv ℝ (markedCapBump R L k ρ) y = 0 := by
  have hm : IsLocalMin (markedCapBump R L k ρ) y := by
    filter_upwards [] with z
    rw [hy]
    exact markedCapBump_nonneg R L hk hρ z
  exact hm.fderiv_eq_zero

theorem markedCapMap_fderiv_injective {R L k ρ : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ)
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1) :
    Function.Injective (fderiv ℝ (markedCapMap R h L k ρ) y) := by
  have hp := (markedCap_contDiff_base hR hL).differentiable (by simp) y
  have hz := (markedCap_contDiff_height hR hL h).differentiable (by simp) y
  have hb := (contDiff_markedCapBump hR hL k ρ).differentiable (by simp) y
  have hzb : DifferentiableAt ℝ (markedCapHeight R h L k ρ) y := hz.add hb
  by_cases hzero : markedCapBump R L k ρ y = 0
  · have heq : fderiv ℝ (markedCapMap R h L k ρ) y = fderiv ℝ (capDiskMap R h L) y := by
      rw [markedCapMap, capDiskMap, fderiv_graphMap hp hzb, fderiv_graphMap hp hz]
      have hd : fderiv ℝ (markedCapHeight R h L k ρ) y = fderiv ℝ (capDiskHeight R h L) y := by
        change fderiv ℝ (fun z => capDiskHeight R h L z + markedCapBump R L k ρ z) y = _
        rw [fderiv_fun_add hz hb, markedCapBump_fderiv_eq_zero hk hρ hzero,
          add_zero]
      rw [hd]
    rw [heq]
    exact capDiskMap_fderiv_injective hR hL h hy
  · exact graphMap_fderiv_injective_of_planar hp hzb
      (markedCap_base_fderiv_injective_top hR hL h hy
        (markedCapBump_nonzero_top hR hL hρ hsmall hy hzero))

theorem isEmbedding_markedCapEmbeddingMap {R L k ρ : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ) :
    Topology.IsEmbedding (markedCapEmbeddingMap R h L k ρ) := by
  let : CompactSpace capDiskDomain := isCompact_iff_compactSpace.mp isCompact_capDiskDomain_set
  have hc : Continuous (markedCapEmbeddingMap R h L k ρ) :=
    ((contDiff_markedCapMap hR hL h k ρ).continuous).comp continuous_subtype_val
  apply (hc.isClosedEmbedding ?_).isEmbedding
  intro x y hxy
  apply Subtype.ext
  exact markedCapMap_injOn hR hL hk hρ hsmall h x.property y.property hxy

theorem markedCap_smooth_embedding {R L k ρ : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hk : 0 ≤ k) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ) :
    ContDiff ℝ ∞ (markedCapMap R h L k ρ) ∧
    Topology.IsEmbedding (markedCapEmbeddingMap R h L k ρ) ∧
    ∀ y : PolarPoint, cartesianRadius y ≤ 1 →
      Function.Injective (fderiv ℝ (markedCapMap R h L k ρ) y) :=
  ⟨contDiff_markedCapMap hR hL h k ρ,
    isEmbedding_markedCapEmbeddingMap hR hL hk hρ hsmall h,
    fun _ hy => markedCapMap_fderiv_injective hR hL hk hρ hsmall h hy⟩

theorem markedCap_marker_support_distance {R L ρ k : ℝ} (hρ : 0 < ρ)
    {x : PolarPoint} (hx : markerBump 1 2 k ρ (x - markedCapCenter R L) ≠ 0) :
    cartesianRadius (x - markedCapCenter R L) < ρ := by
  have hq : markerQuadratic 1 2 (x - markedCapCenter R L) < ρ ^ 2 := by
    by_contra h
    exact hx (markerBump_eq_zero hρ.ne' (le_of_not_gt h))
  have hsq := cartesianRadius_sq_coordinates (x - markedCapCenter R L)
  have hn := capDisk_radius_nonneg (x - markedCapCenter R L)
  dsimp [markerQuadratic, coordinateEuclideanPair] at hq hsq
  nlinarith [sq_nonneg (x - markedCapCenter R L).2]

theorem markedCap_marker_support_lower {R L ρ k : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {x : PolarPoint} (hx : markerBump 1 2 k ρ (x - markedCapCenter R L) ≠ 0) :
    R + L / 16 < cartesianRadius x := by
  have hd := markedCap_marker_support_distance hρ hx
  have htri := markedCap_radius_le_sub_add (markedCapCenter R L) x
  have hsym : cartesianRadius (markedCapCenter R L - x) =
      cartesianRadius (x - markedCapCenter R L) := by
    unfold cartesianRadius
    rw [map_sub, map_sub, norm_sub_rev]
  rw [markedCapCenter_radius hR hL, hsym] at htri
  linarith

theorem markedCapBump_eq_zero_of_inner {R L ρ k : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {y : PolarPoint} (hy : cartesianRadius (capDiskBase R L y) ≤ R + L / 16) :
    markedCapBump R L k ρ y = 0 := by
  have hm : markerBump 1 2 k ρ (capDiskBase R L y - markedCapCenter R L) = 0 := by
    by_contra hn
    exact (not_lt_of_ge hy) (markedCap_marker_support_lower hR hL hρ hsmall hn)
  simp [markedCapBump, hm]

theorem markedCapMap_eq_capDiskMap_of_inner {R L ρ k : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ)
    {y : PolarPoint} (hy : cartesianRadius (capDiskBase R L y) ≤ R + L / 16) :
    markedCapMap R h L k ρ y = capDiskMap R h L y := by
  have hb := markedCapBump_eq_zero_of_inner (k := k) hR hL hρ hsmall hy
  ext i
  fin_cases i <;> simp [markedCapMap, capDiskMap, markedCapHeight, hb]

/-- The actual marked cap, in physical top-plane coordinates. -/
theorem markedCapMap_rimChart {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h k ρ : ℝ)
    {x : PolarPoint} (hx0 : 0 < cartesianRadius x) (hx : cartesianRadius x < R + L / 4) :
    markedCapMap R h L k ρ (capDiskRimChart R L x) =
      graphMap id (fun z => h + markerBump 1 2 k ρ (z - markedCapCenter R L)) x := by
  have hb := capDiskBase_rimChart hR hL hx0 hx
  have hs : capDiskParameter R L (capDiskRimChart R L x) ≤ L / 4 := by
    rw [capDiskRimChart_parameter hR hL hx0 hx]
    linarith
  have hz : capDiskHeight R h L (capDiskRimChart R L x) = h :=
    capMeridianHeight_eq_left h hL hs
  have hc := markedCapCutoff_eq_one hL hs
  ext i
  fin_cases i <;> simp [markedCapMap, markedCapHeight, markedCapBump, hb, hz, hc]

theorem markedCapMap_rimChart_germ {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h k ρ : ℝ)
    {x : PolarPoint} (hx0 : 0 < cartesianRadius x) (hx : cartesianRadius x < R + L / 4) :
    (markedCapMap R h L k ρ ∘ capDiskRimChart R L) =ᶠ[𝓝 x]
      graphMap id (fun z => h + markerBump 1 2 k ρ (z - markedCapCenter R L)) := by
  have hn : {z : PolarPoint | 0 < cartesianRadius z ∧ cartesianRadius z < R + L / 4} ∈ 𝓝 x :=
    ((isOpen_lt continuous_const continuous_cartesianRadius).inter
      (isOpen_lt continuous_cartesianRadius continuous_const)).mem_nhds ⟨hx0, hx⟩
  filter_upwards [hn] with z hz
  exact markedCapMap_rimChart hR hL h k ρ hz.1 hz.2

theorem markedCapMap_rim_germ {R L ρ k : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ)
    {x : PolarPoint} (hx : cartesianRadius x = R) :
    (markedCapMap R h L k ρ ∘ capDiskRimChart R L) =ᶠ[𝓝 x] graphMap id (fun _ => h) := by
  have hn : {z : PolarPoint | 0 < cartesianRadius z ∧ cartesianRadius z < R + L / 16} ∈ 𝓝 x :=
    ((isOpen_lt continuous_const continuous_cartesianRadius).inter
      (isOpen_lt continuous_cartesianRadius continuous_const)).mem_nhds
      (by change 0 < cartesianRadius x ∧ cartesianRadius x < R + L / 16
          rw [hx]; constructor <;> linarith)
  filter_upwards [hn] with z hz
  have hz4 : cartesianRadius z < R + L / 4 := by linarith [hz.2]
  change markedCapMap R h L k ρ (capDiskRimChart R L z) = _
  rw [markedCapMap_eq_capDiskMap_of_inner hR hL hρ hsmall h
    (by rw [capDiskBase_rimChart hR hL hz.1 hz4]; exact hz.2.le)]
  exact capDiskMap_rimChart hR hL h hz.1 hz4

theorem markedCap_marker_center_positive {k ρ : ℝ} (hk : 0 < k) (hρ : 0 < ρ) :
    0 < markerBump 1 2 k ρ 0 := by
  have hi : 0 < ∫ t in (0 : ℝ)..ρ ^ 2, markerKernel ρ t :=
    intervalIntegral.integral_pos (sq_pos_of_pos hρ)
      (contDiff_markerKernel ρ).continuous.continuousOn
      (fun t _ => markerKernel_nonneg ρ t)
      ⟨0, ⟨le_refl 0, (sq_nonneg ρ)⟩, by simp⟩
  simpa [markerBump, markerQuadratic, markerPrimitive] using mul_pos (half_pos hk) hi

def markedCapCenterParameter (R L : ℝ) : PolarPoint :=
  capDiskRimChart R L (markedCapCenter R L)

theorem markedCapCenterParameter_mem {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    cartesianRadius (markedCapCenterParameter R L) < 1 := by
  have hc0 : 0 < cartesianRadius (markedCapCenter R L) := by
    rw [markedCapCenter_radius hR hL]; linarith
  have hc4 : cartesianRadius (markedCapCenter R L) < R + L / 4 := by
    rw [markedCapCenter_radius hR hL]; linarith
  rw [markedCapCenterParameter, capDiskRimChart_radius hR hL hc0 hc4,
    capDiskRimScale, markedCapCenter_radius hR hL]
  have hd : 0 < (R + L / 8 - R) / (L + R) :=
    div_pos (by linarith) (add_pos hL hR)
  linarith

theorem markedCapBump_center_positive {R L k ρ : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hk : 0 < k) (hρ : 0 < ρ) : 0 < markedCapBump R L k ρ (markedCapCenterParameter R L) := by
  have hc0 : 0 < cartesianRadius (markedCapCenter R L) := by
    rw [markedCapCenter_radius hR hL]; linarith
  have hc4 : cartesianRadius (markedCapCenter R L) < R + L / 4 := by
    rw [markedCapCenter_radius hR hL]; linarith
  have hs : capDiskParameter R L (markedCapCenterParameter R L) ≤ L / 4 := by
    rw [markedCapCenterParameter, capDiskRimChart_parameter hR hL hc0 hc4,
      markedCapCenter_radius hR hL]
    linarith
  rw [markedCapBump, markedCapCutoff_eq_one hL hs, one_mul, markedCapCenterParameter,
    capDiskBase_rimChart hR hL hc0 hc4, sub_self]
  exact markedCap_marker_center_positive hk hρ

theorem markedCapBump_bounds (R L : ℝ) {k ρ : ℝ} (hk : 0 ≤ k) (hρ : 0 < ρ)
    (y : PolarPoint) : 0 ≤ markedCapBump R L k ρ y ∧
      markedCapBump R L k ρ y ≤ k * ρ ^ 2 / 2 := by
  refine ⟨markedCapBump_nonneg R L hk hρ y, ?_⟩
  have hm := markerBump_bounds (A := (1 : ℝ)) (B := (2 : ℝ))
    (by norm_num) (by norm_num) hk hρ.ne' (capDiskBase R L y - markedCapCenter R L)
  calc
    markedCapBump R L k ρ y ≤ 1 * markerBump 1 2 k ρ
        (capDiskBase R L y - markedCapCenter R L) :=
      mul_le_mul_of_nonneg_right (markedCapCutoff_bounds R L y).2 hm.1
    _ ≤ k * ρ ^ 2 / 2 := by simpa using hm.2

theorem markedCapHeight_bounds {R L k ρ : ℝ} (hL : 0 < L)
    (hk : 0 ≤ k) (hρ : 0 < ρ) (h : ℝ) (y : PolarPoint) :
    h - L * capDrop ≤ markedCapHeight R h L k ρ y ∧
    markedCapHeight R h L k ρ y ≤ h + k * ρ ^ 2 / 2 := by
  have hz := capMeridianHeight_bounds h hL (capDiskParameter R L y)
  have hb := markedCapBump_bounds R L hk hρ y
  change h - L * capDrop ≤ capDiskHeight R h L y ∧ capDiskHeight R h L y ≤ h at hz
  dsimp [markedCapHeight]
  constructor <;> linarith

theorem markedCapBump_zero_germ_of_quadratic {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) {y : PolarPoint}
    (hy : ρ ^ 2 < markerQuadratic 1 2 (capDiskBase R L y - markedCapCenter R L)) :
    markedCapBump R L k ρ =ᶠ[𝓝 y] fun _ => 0 := by
  have hc : Continuous (fun z => markerQuadratic 1 2 (capDiskBase R L z - markedCapCenter R L)) :=
    (contDiff_markerQuadratic 1 2).continuous.comp
      ((markedCap_contDiff_base hR hL).continuous.sub continuous_const)
  have hn : {z : PolarPoint | ρ ^ 2 < markerQuadratic 1 2
      (capDiskBase R L z - markedCapCenter R L)} ∈ 𝓝 y :=
    (isOpen_lt continuous_const hc).mem_nhds hy
  filter_upwards [hn] with z hz
  simp [markedCapBump, markerBump_eq_zero hρ.ne' hz.le]

/-- The whole germ is unchanged off the top branch, including both transition endpoints. -/
theorem markedCapBump_zero_germ_of_not_top {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64)
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1) (hs : L / 4 ≤ capDiskParameter R L y) :
    markedCapBump R L k ρ =ᶠ[𝓝 y] fun _ => 0 := by
  by_cases hs2 : capDiskParameter R L y ≤ 3 * L / 4
  · have hr := markedCap_meridian_middle_lower R hL ⟨hs, hs2⟩
    rw [← capDiskBase_radius hR hL hy] at hr
    have htri := markedCap_radius_le_sub_add (capDiskBase R L y) (markedCapCenter R L)
    rw [markedCapCenter_radius hR hL] at htri
    have hd : L / 8 ≤ cartesianRadius (capDiskBase R L y - markedCapCenter R L) := by
      linarith
    apply markedCapBump_zero_germ_of_quadratic hR hL hρ
    have hsq := cartesianRadius_sq_coordinates (capDiskBase R L y - markedCapCenter R L)
    dsimp [markerQuadratic, coordinateEuclideanPair] at hsq ⊢
    nlinarith [sq_nonneg (capDiskBase R L y - markedCapCenter R L).2]
  · have hc : Continuous (capDiskParameter R L) :=
      continuous_const.mul (continuous_const.sub continuous_cartesianRadius)
    have hn : {z : PolarPoint | 3 * L / 4 < capDiskParameter R L z} ∈ 𝓝 y :=
      (isOpen_lt continuous_const hc).mem_nhds (lt_of_not_ge hs2)
    filter_upwards [hn] with z hz
    exact markedCapBump_eq_zero_bottom hL k ρ hz.le

theorem markedCapMap_germ_of_not_top {R L k ρ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hρ : 0 < ρ) (hsmall : ρ < L / 64) (h : ℝ)
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1) (hs : L / 4 ≤ capDiskParameter R L y) :
    markedCapMap R h L k ρ =ᶠ[𝓝 y] capDiskMap R h L := by
  filter_upwards [markedCapBump_zero_germ_of_not_top (k := k) hR hL hρ hsmall hy hs] with z hz
  ext i
  fin_cases i <;> simp [markedCapMap, capDiskMap, markedCapHeight, hz]

end ContinuousFlexibility
