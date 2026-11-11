import ContinuousFlexibility.Geometry.CapRevolution
import ContinuousFlexibility.Contracts.CartesianMetricRegularity

/-!
# The actual cap disk, including its smooth axis

The closed Cartesian unit disk parameterizes the meridian from the bottom
axis to the attaching rim. Near the axis the formula is exactly a linear
horizontal disk, so no differentiability of the radius at zero is assumed.
The marker placement and gluing to the moving graph remain later steps.
-/

noncomputable section

namespace ContinuousFlexibility

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def capDiskParameter (R L : ℝ) (y : PolarPoint) : ℝ :=
  (L + R) * (1 - cartesianRadius y)

def capDiskBase (R L : ℝ) (y : PolarPoint) : PolarPoint :=
  (capMeridianRadius R L (capDiskParameter R L y) / cartesianRadius y) • y

def capDiskHeight (R h L : ℝ) (y : PolarPoint) : ℝ :=
  capMeridianHeight h L (capDiskParameter R L y)

def capDiskMap (R h L : ℝ) : PolarPoint → E3 :=
  graphMap (capDiskBase R L) (capDiskHeight R h L)

@[simp] theorem capDiskMap_zero (R h L : ℝ) (y : PolarPoint) :
    capDiskMap R h L y 0 = (capDiskBase R L y).1 := by simp [capDiskMap]

@[simp] theorem capDiskMap_one (R h L : ℝ) (y : PolarPoint) :
    capDiskMap R h L y 1 = (capDiskBase R L y).2 := by simp [capDiskMap]

@[simp] theorem capDiskMap_two (R h L : ℝ) (y : PolarPoint) :
    capDiskMap R h L y 2 = capDiskHeight R h L y := by simp [capDiskMap]

theorem capDisk_radius_nonneg (y : PolarPoint) : 0 ≤ cartesianRadius y := norm_nonneg _

theorem capDisk_radius_eq_zero_iff (y : PolarPoint) : cartesianRadius y = 0 ↔ y = 0 := by
  constructor
  · intro h
    by_contra hn
    exact (ne_of_gt (cartesianRadius_pos hn)) h
  · rintro rfl
    simp [cartesianRadius]

theorem capDisk_radius_smul (a : ℝ) (y : PolarPoint) :
    cartesianRadius (a • y) = |a| * cartesianRadius y := by
  simp [cartesianRadius, Real.norm_eq_abs]

theorem capDisk_axis_parameter {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {y : PolarPoint} (hy : cartesianRadius y < 1 / 4) :
    3 * L / 4 ≤ capDiskParameter R L y := by
  have hm := mul_pos (add_pos hL hR) (show 0 < 1 / 4 - cartesianRadius y by linarith)
  unfold capDiskParameter
  nlinarith

theorem capDisk_axis_base {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {y : PolarPoint} (hy : cartesianRadius y < 1 / 4) :
    capDiskBase R L y = (L + R) • y := by
  unfold capDiskBase
  rw [capMeridianRadius_eq_right R hL (capDisk_axis_parameter hR hL hy)]
  rw [show R + L - capDiskParameter R L y = (L + R) * cartesianRadius y by
    unfold capDiskParameter; ring]
  by_cases h0 : y = 0
  · subst y
    simp
  · rw [mul_div_cancel_right₀ _ (cartesianRadius_pos h0).ne']

theorem capDisk_axis_height {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ)
    {y : PolarPoint} (hy : cartesianRadius y < 1 / 4) :
    capDiskHeight R h L y = h - L * capDrop :=
  capMeridianHeight_eq_right h hL (capDisk_axis_parameter hR hL hy)

theorem capDisk_axis_formula {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ)
    {y : PolarPoint} (hy : cartesianRadius y < 1 / 4) :
    capDiskMap R h L y =
      graphMap (fun x : PolarPoint => (L + R) • x) (fun _ => h - L * capDrop) y := by
  ext i
  fin_cases i <;> simp [capDiskMap, capDisk_axis_base hR hL hy,
    capDisk_axis_height hR hL h hy]

theorem capDisk_axis_germ {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    capDiskMap R h L =ᶠ[𝓝 0]
      graphMap (fun x : PolarPoint => (L + R) • x) (fun _ => h - L * capDrop) := by
  have hn : {y : PolarPoint | cartesianRadius y < (1 / 4 : ℝ)} ∈ 𝓝 0 :=
    (isOpen_lt continuous_cartesianRadius continuous_const).mem_nhds
      (by norm_num [cartesianRadius])
  filter_upwards [hn] with y hy
  exact capDisk_axis_formula hR hL h hy

theorem contDiff_capDiskMap {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    ContDiff ℝ ∞ (capDiskMap R h L) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y = 0
  · subst y
    have hG : ContDiff ℝ ∞
        (graphMap (fun x : PolarPoint => (L + R) • x) (fun _ => h - L * capDrop)) :=
      contDiff_graphMap (((L + R) • ContinuousLinearMap.id ℝ PolarPoint).contDiff) contDiff_const
    exact hG.contDiffAt.congr_of_eventuallyEq (capDisk_axis_germ hR hL h)
  · have hρ := contDiffAt_cartesianRadius hy
    have hs : ContDiffAt ℝ ∞ (capDiskParameter R L) y :=
      contDiffAt_const.mul (contDiffAt_const.sub hρ)
    apply contDiffAt_graphMap
    · exact (((contDiff_capMeridianRadius R L).contDiffAt.comp y hs).div hρ
        (cartesianRadius_pos hy).ne').smul contDiffAt_id
    · exact (contDiff_capMeridianHeight h L).contDiffAt.comp y hs

theorem capDiskParameter_mem {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1) :
    capDiskParameter R L y ∈ Icc 0 (L + R) := by
  have hρ := capDisk_radius_nonneg y
  have hS := add_pos hL hR
  unfold capDiskParameter
  constructor <;> nlinarith

theorem capDisk_meridian_radius_pos {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1) (hn : y ≠ 0) :
    0 < capMeridianRadius R L (capDiskParameter R L y) := by
  have hs := capDiskParameter_mem hR hL hy
  have hρ := cartesianRadius_pos hn
  have hS := add_pos hL hR
  apply capMeridianRadius_pos hR hL
  unfold capDiskParameter at *
  constructor <;> nlinarith

theorem capDiskBase_radius {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {y : PolarPoint} (hy : cartesianRadius y ≤ 1) :
    cartesianRadius (capDiskBase R L y) = capMeridianRadius R L (capDiskParameter R L y) := by
  by_cases h0 : y = 0
  · subst y
    have haxis : cartesianRadius (0 : PolarPoint) < 1 / 4 := by norm_num [cartesianRadius]
    rw [capDisk_axis_base hR hL haxis]
    simp only [smul_zero]
    rw [capMeridianRadius_eq_right R hL (capDisk_axis_parameter hR hL haxis)]
    simp [capDiskParameter, cartesianRadius]
    ring
  · have hρ := cartesianRadius_pos h0
    have hr := capDisk_meridian_radius_pos hR hL hy h0
    rw [capDiskBase, capDisk_radius_smul, abs_of_pos (div_pos hr hρ)]
    exact div_mul_cancel₀ _ hρ.ne'

theorem capDiskMap_injOn {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    Set.InjOn (capDiskMap R h L) {y : PolarPoint | cartesianRadius y ≤ 1} := by
  intro x hx y hy he
  have hb : capDiskBase R L x = capDiskBase R L y := by
    simpa [capDiskMap] using congrArg graphBaseProjection he
  have hz : capDiskHeight R h L x = capDiskHeight R h L y := by
    simpa [capDiskMap] using congrArg (fun v : E3 => v 2) he
  have hr : capMeridianRadius R L (capDiskParameter R L x) =
      capMeridianRadius R L (capDiskParameter R L y) := by
    simpa only [capDiskBase_radius hR hL hx, capDiskBase_radius hR hL hy]
      using congrArg cartesianRadius hb
  have hs : capDiskParameter R L x = capDiskParameter R L y :=
    capMeridian_injective R h hL (Prod.ext hr hz)
  have hρ : cartesianRadius x = cartesianRadius y := by
    unfold capDiskParameter at hs
    have hS := add_pos hL hR
    nlinarith
  by_cases hx0 : x = 0
  · subst x
    exact ((capDisk_radius_eq_zero_iff y).mp (by simpa [cartesianRadius] using hρ.symm)).symm
  · have ha : capMeridianRadius R L (capDiskParameter R L x) / cartesianRadius x ≠ 0 :=
      (div_pos (capDisk_meridian_radius_pos hR hL hx hx0) (cartesianRadius_pos hx0)).ne'
    unfold capDiskBase at hb
    rw [← hs, ← hρ] at hb
    have hc := congrArg (fun z : PolarPoint =>
      (capMeridianRadius R L (capDiskParameter R L x) / cartesianRadius x)⁻¹ • z) hb
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hc

abbrev capDiskDomain := {y : PolarPoint // cartesianRadius y ≤ 1}

theorem isCompact_capDiskDomain_set : IsCompact {y : PolarPoint | cartesianRadius y ≤ 1} := by
  have heq : Complex.equivRealProdCLM '' Metric.closedBall (0 : ℂ) 1 =
      {y : PolarPoint | cartesianRadius y ≤ 1} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change ‖Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z)‖ ≤ 1
      rw [ContinuousLinearEquiv.symm_apply_apply]
      simpa using hz
    · intro hy
      refine ⟨Complex.equivRealProdCLM.symm y, ?_,
        Complex.equivRealProdCLM.apply_symm_apply y⟩
      simpa [cartesianRadius] using hy
  rw [← heq]
  exact (isCompact_closedBall (0 : ℂ) 1).image Complex.equivRealProdCLM.continuous

def capDiskEmbeddingMap (R h L : ℝ) (y : capDiskDomain) : E3 := capDiskMap R h L y

theorem isEmbedding_capDiskEmbeddingMap {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    Topology.IsEmbedding (capDiskEmbeddingMap R h L) := by
  let : CompactSpace capDiskDomain := isCompact_iff_compactSpace.mp isCompact_capDiskDomain_set
  have hc : Continuous (capDiskEmbeddingMap R h L) :=
    ((contDiff_capDiskMap hR hL h).continuous).comp continuous_subtype_val
  apply (hc.isClosedEmbedding ?_).isEmbedding
  intro x y hxy
  apply Subtype.ext
  exact capDiskMap_injOn hR hL h x.property y.property hxy

theorem hasFDerivAt_capDiskMap_axis {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    HasFDerivAt (capDiskMap R h L)
      (graphDifferential ((L + R) • ContinuousLinearMap.id ℝ PolarPoint) 0) 0 := by
  have hb : HasFDerivAt (fun x : PolarPoint => (L + R) • x)
      ((L + R) • ContinuousLinearMap.id ℝ PolarPoint) 0 :=
    (hasFDerivAt_id (0 : PolarPoint)).const_smul (L + R)
  have hd := hasFDerivAt_graphMap hb (hasFDerivAt_const (h - L * capDrop) 0)
  exact hd.congr_of_eventuallyEq (capDisk_axis_germ hR hL h)

theorem capDiskMap_axis_fderiv_injective {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    Function.Injective (fderiv ℝ (capDiskMap R h L) 0) := by
  rw [(hasFDerivAt_capDiskMap_axis hR hL h).fderiv]
  intro u v huv
  have hS := (add_pos hL hR).ne'
  apply Prod.ext
  · apply mul_left_cancel₀ hS
    simpa [graphDifferential, e3Basis] using congrArg (fun w : E3 => w 0) huv
  · apply mul_left_cancel₀ hS
    simpa [graphDifferential, e3Basis] using congrArg (fun w : E3 => w 1) huv

/-- This identity uses the radius only at positive polar radius; no global
choice or derivative of the angular argument is involved. -/
theorem capDiskMap_polarMap (R h L : ℝ) {p : PolarPoint} (hp : 0 < p.1) :
    capDiskMap R h L (polarMap p) =
      capRevolution R h L ((L + R) * (1 - p.1), p.2) := by
  have hρ : cartesianRadius (polarMap p) = p.1 := cartesianRadius_polarPosition hp p.2
  ext i
  fin_cases i
  · change capDiskMap R h L (polarMap p) 0 =
      capRevolution R h L ((L + R) * (1 - p.1), p.2) 0
    rw [capDiskMap_zero, capRevolution_zero]
    change (capMeridianRadius R L (capDiskParameter R L (polarMap p)) /
      cartesianRadius (polarMap p)) * (polarMap p).1 = _
    unfold capDiskParameter
    rw [hρ]
    simp only [polarMap, polarPosition]
    field_simp [hp.ne']
  · change capDiskMap R h L (polarMap p) 1 =
      capRevolution R h L ((L + R) * (1 - p.1), p.2) 1
    rw [capDiskMap_one, capRevolution_one]
    change (capMeridianRadius R L (capDiskParameter R L (polarMap p)) /
      cartesianRadius (polarMap p)) * (polarMap p).2 = _
    unfold capDiskParameter
    rw [hρ]
    simp only [polarMap, polarPosition]
    field_simp [hp.ne']
  · change capDiskMap R h L (polarMap p) 2 =
      capRevolution R h L ((L + R) * (1 - p.1), p.2) 2
    rw [capDiskMap_two, capRevolution_two]
    change capMeridianHeight h L (capDiskParameter R L (polarMap p)) = _
    unfold capDiskParameter
    rw [hρ]

theorem capDiskMap_polar_germ (R h L : ℝ) {p : PolarPoint} (hp : 0 < p.1) :
    (capDiskMap R h L ∘ polarMap) =ᶠ[𝓝 p]
      (capRevolution R h L ∘ fun q : PolarPoint => ((L + R) * (1 - q.1), q.2)) := by
  have hn : {q : PolarPoint | 0 < q.1} ∈ 𝓝 p :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hp
  filter_upwards [hn] with q hq
  exact capDiskMap_polarMap R h L hq

/-- The argument chooses a polar preimage only; it is never differentiated.
Surjectivity of the genuine polar Jacobian transports the immersion back to
Cartesian coordinates, including points on an argument branch cut. -/
theorem capDiskMap_fderiv_injective_nonaxis {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) {y : PolarPoint}
    (hy : cartesianRadius y ≤ 1) (hy0 : y ≠ 0) :
    Function.Injective (fderiv ℝ (capDiskMap R h L) y) := by
  let S : ℝ := L + R
  have hS : 0 < S := add_pos hL hR
  let p : PolarPoint := (cartesianRadius y, (Complex.equivRealProdCLM.symm y).arg)
  have hpρ : 0 < p.1 := cartesianRadius_pos hy0
  have hp : polarMap p = y := polarMap_cartesianCoordinates y
  let T : PolarPoint → PolarPoint := fun q => (S * (1 - q.1), q.2)
  let J : PolarPoint →L[ℝ] PolarPoint :=
    ((-S) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hJ_apply (v : PolarPoint) : J v = (-S * v.1, v.2) := by simp [J]
  have hfst : HasFDerivAt (fun q : PolarPoint => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun q : PolarPoint => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hasFDerivAt_snd
  have hT : HasFDerivAt T J p := by
    have h1 : HasFDerivAt (fun q : PolarPoint => S * (1 - q.1))
        ((-S) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
      convert! (((hasFDerivAt_const (1 : ℝ) p).sub hfst).const_mul S) using 1
      apply ContinuousLinearMap.ext
      intro v
      simp
    exact h1.prodMk hsnd
  have hJinj : Function.Injective J := by
    intro u v huv
    rw [hJ_apply, hJ_apply] at huv
    have h1 := congrArg (fun w : PolarPoint => w.1) huv
    have h2 := congrArg (fun w : PolarPoint => w.2) huv
    apply Prod.ext
    · exact mul_left_cancel₀ (neg_ne_zero.mpr hS.ne') h1
    · exact h2
  have heq : (capDiskMap R h L ∘ polarMap) =ᶠ[𝓝 p] (capRevolution R h L ∘ T) :=
    capDiskMap_polar_germ R h L hpρ
  have hD : DifferentiableAt ℝ (capDiskMap R h L) (polarMap p) := by
    rw [hp]
    exact (contDiff_capDiskMap hR hL h).differentiable (by simp) y
  have hdleft := hD.hasFDerivAt.comp p (hasFDerivAt_polarMap p)
  have hdright := ((contDiff_capRevolution R h L).differentiable
    (by simp) (T p)).hasFDerivAt.comp p hT
  have hder := heq.fderiv_eq (𝕜 := ℝ)
  rw [hdleft.fderiv, hdright.fderiv, hp] at hder
  have hr : capMeridianRadius R L (T p).1 ≠ 0 :=
    (capDisk_meridian_radius_pos hR hL hy hy0).ne'
  have hcomp : Function.Injective
      ((fderiv ℝ (capDiskMap R h L) y).comp (polarJacobian p)) := by
    rw [hder]
    exact (capRevolution_fderiv_injective R h hL hr).comp hJinj
  intro u v huv
  obtain ⟨a, ha⟩ := (polarJacobian_bijective hpρ.ne').surjective u
  obtain ⟨b, hb⟩ := (polarJacobian_bijective hpρ.ne').surjective v
  have hab : a = b := hcomp (by
    simpa only [ContinuousLinearMap.comp_apply, ha, hb] using huv)
  exact ha.symm.trans ((congrArg (polarJacobian p) hab).trans hb)

theorem capDiskMap_fderiv_injective {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) {y : PolarPoint}
    (hy : cartesianRadius y ≤ 1) :
    Function.Injective (fderiv ℝ (capDiskMap R h L) y) := by
  by_cases hy0 : y = 0
  · subst y
    exact capDiskMap_axis_fderiv_injective hR hL h
  · exact capDiskMap_fderiv_injective_nonaxis hR hL h hy hy0

theorem capDisk_outer_collar (R h : ℝ) {L : ℝ} (hL : 0 < L)
    {y : PolarPoint} (hy : capDiskParameter R L y ≤ L / 4) :
    capDiskMap R h L y = graphMap id (fun _ => h)
      (((R + capDiskParameter R L y) / cartesianRadius y) • y) := by
  ext i
  fin_cases i <;> simp [capDiskMap, capDiskBase, capDiskHeight,
    capMeridianRadius_eq_left R hL hy, capMeridianHeight_eq_left h hL hy]

theorem capDisk_boundary (R h L : ℝ) {y : PolarPoint} (hy : cartesianRadius y = 1) :
    capDiskMap R h L y = graphMap id (fun _ => h) (R • y) := by
  have hs : capDiskParameter R L y = 0 := by simp [capDiskParameter, hy]
  ext i
  fin_cases i <;> simp [capDiskMap, capDiskBase, capDiskHeight, hs, hy,
    capMeridianRadius, capMeridianHeight]

theorem capDisk_inside_cylinder_bottom {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) {y : PolarPoint}
    (hy : cartesianRadius y ≤ 1)
    (hinside : cartesianRadius (graphBaseProjection (capDiskMap R h L y)) < R) :
    capDiskMap R h L y 2 = h - L * capDrop := by
  have hr : capMeridianRadius R L (capDiskParameter R L y) < R := by
    simpa only [capDiskMap, graphBaseProjection_graphMap, capDiskBase_radius hR hL hy]
      using hinside
  have hs := capDiskParameter_mem hR hL hy
  have ht : L < capDiskParameter R L y := by
    by_contra hn
    exact (not_lt_of_ge (capMeridianRadius_core_le R hL ⟨hs.1, le_of_not_gt hn⟩)) hr
  simp only [capDiskMap, graphMap_two, capDiskHeight]
  exact capMeridianHeight_eq_right h hL (by linarith)

/-- The explicit positive length puts the entire part of this actual cap
inside the central cylinder strictly below the supplied graph-height bound. -/
theorem capDisk_inside_cylinder_below {R : ℝ} (hR : 0 < R) (h lo : ℝ)
    {ε : ℝ} (hε : 0 < ε) {y : PolarPoint} (hy : cartesianRadius y ≤ 1)
    (hinside : cartesianRadius
      (graphBaseProjection (capDiskMap R h (capLength h lo ε) y)) < R) :
    capDiskMap R h (capLength h lo ε) y 2 < lo := by
  rw [capDisk_inside_cylinder_bottom hR (capLength_pos h lo hε) h hy hinside]
  exact capLength_bottom_lt h lo hε

theorem capDiskMap_smooth_embedding {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    ContDiff ℝ ∞ (capDiskMap R h L) ∧
      Topology.IsEmbedding (capDiskEmbeddingMap R h L) ∧
      ∀ y : PolarPoint, cartesianRadius y ≤ 1 →
        Function.Injective (fderiv ℝ (capDiskMap R h L) y) :=
  ⟨contDiff_capDiskMap hR hL h, isEmbedding_capDiskEmbeddingMap hR hL h,
    fun _ hy => capDiskMap_fderiv_injective hR hL h hy⟩

/-- The actual radial coordinate transition from the physical attaching
plane to the cap parameter disk. It reverses the radial direction. -/
def capDiskRimScale (R L : ℝ) (x : PolarPoint) : ℝ :=
  1 - (cartesianRadius x - R) / (L + R)

def capDiskRimChart (R L : ℝ) (x : PolarPoint) : PolarPoint :=
  (capDiskRimScale R L x / cartesianRadius x) • x

theorem capDiskRimScale_pos {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {x : PolarPoint} (hx : cartesianRadius x < R + L / 4) :
    0 < capDiskRimScale R L x := by
  have hS := add_pos hL hR
  have hd : (cartesianRadius x - R) / (L + R) < 1 :=
    (div_lt_one hS).2 (by linarith)
  unfold capDiskRimScale
  linarith

theorem capDiskRimChart_radius {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {x : PolarPoint} (hx0 : 0 < cartesianRadius x)
    (hx : cartesianRadius x < R + L / 4) :
    cartesianRadius (capDiskRimChart R L x) = capDiskRimScale R L x := by
  rw [capDiskRimChart, capDisk_radius_smul,
    abs_of_pos (div_pos (capDiskRimScale_pos hR hL hx) hx0)]
  exact div_mul_cancel₀ _ hx0.ne'

theorem capDiskRimChart_parameter {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {x : PolarPoint} (hx0 : 0 < cartesianRadius x)
    (hx : cartesianRadius x < R + L / 4) :
    capDiskParameter R L (capDiskRimChart R L x) = cartesianRadius x - R := by
  rw [capDiskParameter, capDiskRimChart_radius hR hL hx0 hx]
  unfold capDiskRimScale
  field_simp [(add_pos hL hR).ne']; ring

theorem capDiskBase_rimChart {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {x : PolarPoint} (hx0 : 0 < cartesianRadius x)
    (hx : cartesianRadius x < R + L / 4) :
    capDiskBase R L (capDiskRimChart R L x) = x := by
  unfold capDiskBase
  rw [capDiskRimChart_parameter hR hL hx0 hx, capDiskRimChart_radius hR hL hx0 hx,
    capMeridianRadius_eq_left R hL (show cartesianRadius x - R ≤ L / 4 by linarith)]
  rw [show R + (cartesianRadius x - R) = cartesianRadius x by ring]
  unfold capDiskRimChart
  rw [smul_smul]
  have he : (cartesianRadius x / capDiskRimScale R L x) *
      (capDiskRimScale R L x / cartesianRadius x) = 1 := by
    field_simp [hx0.ne', (capDiskRimScale_pos hR hL hx).ne']
  rw [he, one_smul]

/-- On a whole physical annulus, rather than just on its boundary circle,
the cap becomes exactly the horizontal graph in this explicit chart. -/
theorem capDiskMap_rimChart {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ)
    {x : PolarPoint} (hx0 : 0 < cartesianRadius x)
    (hx : cartesianRadius x < R + L / 4) :
    capDiskMap R h L (capDiskRimChart R L x) = graphMap id (fun _ => h) x := by
  have hb := capDiskBase_rimChart hR hL hx0 hx
  have hz : capDiskHeight R h L (capDiskRimChart R L x) = h := by
    unfold capDiskHeight
    rw [capDiskRimChart_parameter hR hL hx0 hx]
    exact capMeridianHeight_eq_left h hL (by linarith)
  ext i
  fin_cases i <;> simp [capDiskMap, hb, hz]

theorem contDiffAt_capDiskRimChart (R L : ℝ) {x : PolarPoint} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (capDiskRimChart R L) x := by
  have hρ := contDiffAt_cartesianRadius hx
  have hq : ContDiffAt ℝ ∞ (capDiskRimScale R L) x :=
    contDiffAt_const.sub ((hρ.sub contDiffAt_const).div_const (L + R))
  exact (hq.div hρ (cartesianRadius_pos hx).ne').smul contDiffAt_id

theorem capDiskMap_rim_germ {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ)
    {x : PolarPoint} (hx : cartesianRadius x = R) :
    (capDiskMap R h L ∘ capDiskRimChart R L) =ᶠ[𝓝 x] graphMap id (fun _ => h) := by
  have hn : {y : PolarPoint | 0 < cartesianRadius y ∧ cartesianRadius y < R + L / 4} ∈ 𝓝 x :=
    ((isOpen_lt continuous_const continuous_cartesianRadius).inter
      (isOpen_lt continuous_cartesianRadius continuous_const)).mem_nhds
      (by change 0 < cartesianRadius x ∧ cartesianRadius x < R + L / 4
          rw [hx]
          constructor <;> linarith)
  filter_upwards [hn] with y hy
  exact capDiskMap_rimChart hR hL h hy.1 hy.2

theorem capDiskRimChart_fderiv_injective {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {x : PolarPoint} (hx : cartesianRadius x = R) :
    Function.Injective (fderiv ℝ (capDiskRimChart R L) x) := by
  have hx0 : x ≠ 0 := by
    intro h0
    have hh := hx
    simp only [h0, cartesianRadius, map_zero, norm_zero] at hh
    exact hR.ne' hh.symm
  have hd := ((contDiff_capDiskMap hR hL (0 : ℝ)).differentiable (by simp)
    (capDiskRimChart R L x)).hasFDerivAt.comp x
      ((contDiffAt_capDiskRimChart R L hx0).differentiableAt (by simp)).hasFDerivAt
  have he := (capDiskMap_rim_germ hR hL (0 : ℝ) hx).fderiv_eq (𝕜 := ℝ)
  rw [hd.fderiv] at he
  have hi : Function.Injective (fderiv ℝ (graphMap id (fun _ : PolarPoint => (0 : ℝ))) x) :=
    graphMap_fderiv_injective_of_planar differentiableAt_id (differentiableAt_const 0)
      (by simpa using Function.injective_id)
  intro u v huv
  apply hi
  rw [← he]
  exact congrArg (fderiv ℝ (capDiskMap R 0 L) (capDiskRimChart R L x)) huv

theorem capDisk_meridian_at_rim (R : ℝ) {L s : ℝ} (hL : 0 < L) (hs : 0 ≤ s)
    (hr : capMeridianRadius R L s = R) : s = 0 ∨ s = L := by
  by_cases h0 : s = 0
  · exact Or.inl h0
  · right
    have hpos : 0 < s := lt_of_le_of_ne hs (Ne.symm h0)
    by_cases hlt : s < L
    · have hc := capMeridianRadius_core_lt R hL ⟨hpos, hlt⟩
      rw [hr] at hc
      exact (lt_irrefl R hc).elim
    · have hright : 3 * L / 4 ≤ s := by linarith [le_of_not_gt hlt]
      rw [capMeridianRadius_eq_right R hL hright] at hr
      linarith

/-- The cap can meet the upper part of the closed central cylinder only
along its attaching rim. This also covers the cylinder boundary `r=R`. -/
theorem capDisk_upper_cylinder_meeting {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) {y : PolarPoint}
    (hy : cartesianRadius y ≤ 1)
    (hrad : cartesianRadius (graphBaseProjection (capDiskMap R h L y)) ≤ R)
    (hheight : h - L * capDrop < capDiskMap R h L y 2) :
    capDiskParameter R L y = 0 ∧ capDiskMap R h L y 2 = h := by
  have hr : capMeridianRadius R L (capDiskParameter R L y) ≤ R := by
    simpa only [capDiskMap, graphBaseProjection_graphMap, capDiskBase_radius hR hL hy]
      using hrad
  have hs := capDiskParameter_mem hR hL hy
  have heq : capMeridianRadius R L (capDiskParameter R L y) = R := by
    by_contra hn
    have hlt : cartesianRadius (graphBaseProjection (capDiskMap R h L y)) < R := by
      simpa only [capDiskMap, graphBaseProjection_graphMap, capDiskBase_radius hR hL hy]
        using lt_of_le_of_ne hr hn
    rw [capDisk_inside_cylinder_bottom hR hL h hy hlt] at hheight
    exact lt_irrefl _ hheight
  rcases capDisk_meridian_at_rim R hL hs.1 heq with ht | ht
  · refine ⟨ht, ?_⟩
    simp [capDiskMap, capDiskHeight, ht, capMeridianHeight]
  · have hh : capDiskMap R h L y 2 = h - L * capDrop := by
      simp only [capDiskMap, graphMap_two, capDiskHeight, ht]
      exact capMeridianHeight_eq_right h hL (by linarith)
    rw [hh] at hheight
    exact (lt_irrefl _ hheight).elim

end ContinuousFlexibility
