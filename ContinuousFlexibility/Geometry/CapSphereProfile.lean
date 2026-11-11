import ContinuousFlexibility.Geometry.CapDisk

/-!
# An actual radial profile for the cap's sphere chart

This file constructs a positive-speed radial reparameterization.  Its germ at
the axis is exactly linear, and its germ at the unit circle is the reciprocal
formula required by stereographic inversion.  It does not construct a sphere
map or assume the existence of a compatible profile.
-/

noncomputable section

namespace ContinuousFlexibility

open Set MeasureTheory Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def capSphereCutoff (q : ℝ) : ℝ := Real.smoothTransition (4 * q - 2)

def capSphereHead (q : ℝ) : ℝ := 1 - capSphereCutoff q

def capSphereTail (q : ℝ) : ℝ := capSphereCutoff q / q ^ 2

def capSphereHeadIntegral : ℝ := ∫ q in (0 : ℝ)..1, capSphereHead q

def capSphereTailIntegral : ℝ := ∫ q in (0 : ℝ)..1, capSphereTail q

def capSphereSlope (a : ℝ) : ℝ :=
  (1 - a * capSphereTailIntegral) / capSphereHeadIntegral

def capSphereSpeed (a q : ℝ) : ℝ :=
  capSphereSlope a * capSphereHead q + a * capSphereTail q

def capSphereProfile (a q : ℝ) : ℝ := ∫ u in (0 : ℝ)..q, capSphereSpeed a u

def capSphereRatio (R L : ℝ) : ℝ := R / (L + R)

def capSphereRadialMap (a : ℝ) (y : PolarPoint) : PolarPoint :=
  (capSphereProfile a (cartesianRadius y) / cartesianRadius y) • y

theorem contDiff_capSphereCutoff : ContDiff ℝ ∞ capSphereCutoff :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem capSphereCutoff_nonneg (q : ℝ) : 0 ≤ capSphereCutoff q :=
  Real.smoothTransition.nonneg _

theorem capSphereCutoff_le_one (q : ℝ) : capSphereCutoff q ≤ 1 :=
  Real.smoothTransition.le_one _

theorem capSphereCutoff_eq_zero {q : ℝ} (hq : q ≤ 1 / 2) : capSphereCutoff q = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem capSphereCutoff_eq_one {q : ℝ} (hq : 3 / 4 ≤ q) : capSphereCutoff q = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem capSphereHead_nonneg (q : ℝ) : 0 ≤ capSphereHead q :=
  sub_nonneg.mpr (capSphereCutoff_le_one q)

theorem capSphereTail_nonneg (q : ℝ) : 0 ≤ capSphereTail q :=
  div_nonneg (capSphereCutoff_nonneg q) (sq_nonneg q)

theorem capSphereHead_eq_one {q : ℝ} (hq : q ≤ 1 / 2) : capSphereHead q = 1 := by
  simp [capSphereHead, capSphereCutoff_eq_zero hq]

theorem capSphereTail_eq_zero {q : ℝ} (hq : q ≤ 1 / 2) : capSphereTail q = 0 := by
  simp [capSphereTail, capSphereCutoff_eq_zero hq]

theorem capSphereTail_zero_germ : capSphereTail =ᶠ[𝓝 0] fun _ => 0 := by
  have hn : {q : ℝ | q < 1 / 2} ∈ 𝓝 0 :=
    (isOpen_lt continuous_id continuous_const).mem_nhds (by norm_num)
  filter_upwards [hn] with q hq
  exact capSphereTail_eq_zero hq.le

theorem contDiff_capSphereHead : ContDiff ℝ ∞ capSphereHead :=
  contDiff_const.sub contDiff_capSphereCutoff

theorem contDiff_capSphereTail : ContDiff ℝ ∞ capSphereTail := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : q = 0
  · subst q
    have hc : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) 0 := contDiffAt_const
    exact hc.congr_of_eventuallyEq capSphereTail_zero_germ
  · exact contDiff_capSphereCutoff.contDiffAt.div (contDiffAt_id.pow 2) (pow_ne_zero 2 hq)

theorem capSphereHeadIntegral_pos : 0 < capSphereHeadIntegral := by
  apply intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
    contDiff_capSphereHead.continuous.continuousOn
  · intro q _
    exact capSphereHead_nonneg q
  · exact ⟨0, by norm_num, by rw [capSphereHead_eq_one (by norm_num)]; norm_num⟩

theorem capSphereTailIntegral_nonneg : 0 ≤ capSphereTailIntegral :=
  intervalIntegral.integral_nonneg (by norm_num) fun q _ => capSphereTail_nonneg q

private theorem capSphere_inv_sq_integrable :
    IntervalIntegrable (fun q : ℝ => 1 / q ^ 2) volume (1 / 2) 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact continuousOn_const.div (continuousOn_id.pow 2) (fun q hq =>
    pow_ne_zero 2 (by linarith [hq.1]))

private theorem capSphere_integral_inv_sq :
    (∫ q : ℝ in (1 / 2)..1, 1 / q ^ 2) = 1 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun q : ℝ => -(q⁻¹)) (f' := fun q : ℝ => 1 / q ^ 2)
    (fun q hq => by
      have hq' : q ≠ 0 := by
        rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hq
        linarith [hq.1]
      convert (hasDerivAt_inv hq').neg using 1
      simp)
    capSphere_inv_sq_integrable
  norm_num at he ⊢
  exact he

theorem capSphereTailIntegral_le_one : capSphereTailIntegral ≤ 1 := by
  have hzero : (∫ q in (0 : ℝ)..(1 / 2), capSphereTail q) = 0 := by
    have he := intervalIntegral.integral_congr (μ := volume)
      (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) (f := capSphereTail) (g := fun _ => (0 : ℝ))
      (fun q hq => capSphereTail_eq_zero (by simpa using hq.2))
    simpa using he
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (contDiff_capSphereTail.continuous.intervalIntegrable (0 : ℝ) (1 / 2))
    (contDiff_capSphereTail.continuous.intervalIntegrable (1 / 2 : ℝ) 1)
  rw [hzero, zero_add] at hadd
  unfold capSphereTailIntegral
  rw [← hadd]
  calc
    _ ≤ ∫ q : ℝ in (1 / 2)..1, 1 / q ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (contDiff_capSphereTail.continuous.intervalIntegrable _ _) capSphere_inv_sq_integrable
      intro q _
      exact div_le_div_of_nonneg_right (capSphereCutoff_le_one q) (sq_nonneg q)
    _ = 1 := capSphere_integral_inv_sq

theorem capSphereSlope_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    0 < capSphereSlope a := by
  apply div_pos _ capSphereHeadIntegral_pos
  have hh := mul_le_mul_of_nonneg_left capSphereTailIntegral_le_one ha.le
  nlinarith

theorem contDiff_capSphereSpeed (a : ℝ) : ContDiff ℝ ∞ (capSphereSpeed a) :=
  (contDiff_const.mul contDiff_capSphereHead).add (contDiff_const.mul contDiff_capSphereTail)

theorem capSphereSpeed_eq_left (a : ℝ) {q : ℝ} (hq : q ≤ 1 / 2) :
    capSphereSpeed a q = capSphereSlope a := by
  simp [capSphereSpeed, capSphereHead_eq_one hq, capSphereTail_eq_zero hq]

theorem capSphereSpeed_eq_right (a : ℝ) {q : ℝ} (hq : 3 / 4 ≤ q) :
    capSphereSpeed a q = a / q ^ 2 := by
  simp [capSphereSpeed, capSphereHead, capSphereTail, capSphereCutoff_eq_one hq, div_eq_mul_inv]

theorem capSphereSpeed_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (q : ℝ) :
    0 < capSphereSpeed a q := by
  by_cases hq : q ≤ 1 / 2
  · rw [capSphereSpeed_eq_left a hq]
    exact capSphereSlope_pos ha ha1
  · have hq0 : 0 < q := by linarith
    by_cases hc : capSphereCutoff q < 1
    · have hh := mul_pos (capSphereSlope_pos ha ha1) (sub_pos.mpr hc)
      have ht := mul_nonneg ha.le (capSphereTail_nonneg q)
      dsimp [capSphereSpeed, capSphereHead] at *
      linarith
    · have hc1 : capSphereCutoff q = 1 := le_antisymm (capSphereCutoff_le_one q) (le_of_not_gt hc)
      simp only [capSphereSpeed, capSphereHead, capSphereTail, hc1, sub_self, mul_zero, zero_add]
      exact mul_pos ha (div_pos zero_lt_one (sq_pos_of_pos hq0))

theorem hasDerivAt_capSphereProfile (a q : ℝ) :
    HasDerivAt (capSphereProfile a) (capSphereSpeed a q) q :=
  intervalIntegral.integral_hasDerivAt_right
    ((contDiff_capSphereSpeed a).continuous.intervalIntegrable _ _)
    (contDiff_capSphereSpeed a).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    (contDiff_capSphereSpeed a).continuous.continuousAt

theorem contDiff_capSphereProfile (a : ℝ) : ContDiff ℝ ∞ (capSphereProfile a) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun q => (hasDerivAt_capSphereProfile a q).differentiableAt, ?_⟩
  have hd : deriv (capSphereProfile a) = capSphereSpeed a :=
    funext fun q => (hasDerivAt_capSphereProfile a q).deriv
  rw [hd]
  exact contDiff_capSphereSpeed a

@[simp] theorem capSphereProfile_zero (a : ℝ) : capSphereProfile a 0 = 0 := by
  simp [capSphereProfile]

@[simp] theorem capSphereProfile_one (a : ℝ) : capSphereProfile a 1 = 1 := by
  unfold capSphereProfile capSphereSpeed
  rw [intervalIntegral.integral_add
    ((contDiff_const.mul contDiff_capSphereHead).continuous.intervalIntegrable _ _)
    ((contDiff_const.mul contDiff_capSphereTail).continuous.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  change capSphereSlope a * capSphereHeadIntegral + a * capSphereTailIntegral = 1
  unfold capSphereSlope
  field_simp [capSphereHeadIntegral_pos.ne']
  ring

theorem capSphereProfile_eq_left (a : ℝ) {q : ℝ} (hq : q ≤ 1 / 2) :
    capSphereProfile a q = capSphereSlope a * q := by
  have he := intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := q)
    (f := capSphereSpeed a) (g := fun _ => capSphereSlope a) (fun u hu =>
      capSphereSpeed_eq_left a (hu.2.trans (max_le (by norm_num) hq)))
  simpa [capSphereProfile, mul_comm] using he

theorem capSphereProfile_eq_right (a : ℝ) {q : ℝ} (hq : 3 / 4 ≤ q) :
    capSphereProfile a q = 1 + a - a / q := by
  have hd : ∀ u ∈ uIcc (1 : ℝ) q,
      HasDerivAt (fun u : ℝ => 1 + a - a / u) (capSphereSpeed a u) u := by
    intro u hu
    have hu' : 3 / 4 ≤ u := (le_min (by norm_num) hq).trans hu.1
    have hu0 : u ≠ 0 := by linarith
    rw [capSphereSpeed_eq_right a hu']
    convert (hasDerivAt_const u (1 + a)).sub
      ((hasDerivAt_inv hu0).const_mul a) using 1
    · funext v
      simp [div_eq_mul_inv]
    · simp [div_eq_mul_inv]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((contDiff_capSphereSpeed a).continuous.intervalIntegrable (1 : ℝ) q)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((contDiff_capSphereSpeed a).continuous.intervalIntegrable (0 : ℝ) 1)
    ((contDiff_capSphereSpeed a).continuous.intervalIntegrable (1 : ℝ) q)
  change capSphereProfile a 1 + _ = capSphereProfile a q at hadd
  rw [capSphereProfile_one, he] at hadd
  norm_num at hadd
  linarith

theorem strictMono_capSphereProfile {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    StrictMono (capSphereProfile a) := by
  apply strictMono_of_deriv_pos
  intro q
  rw [(hasDerivAt_capSphereProfile a q).deriv]
  exact capSphereSpeed_pos ha ha1 q

theorem capSphereRatio_mem {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    capSphereRatio R L ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact div_pos hR (add_pos hL hR)
  · exact (div_lt_one (add_pos hL hR)).2 (by linarith)

theorem capSphereProfile_pos {a q : ℝ} (ha : 0 < a) (ha1 : a < 1) (hq : 0 < q) :
    0 < capSphereProfile a q := by
  simpa only [capSphereProfile_zero] using strictMono_capSphereProfile ha ha1 hq

theorem capSphereProfile_nonneg {a q : ℝ} (ha : 0 < a) (ha1 : a < 1) (hq : 0 ≤ q) :
    0 ≤ capSphereProfile a q := by
  simpa only [capSphereProfile_zero] using (strictMono_capSphereProfile ha ha1).monotone hq

@[simp] theorem capSphereRadialMap_zero (a : ℝ) : capSphereRadialMap a 0 = 0 := by
  simp [capSphereRadialMap]

theorem capSphereRadialMap_boundary (a : ℝ) {y : PolarPoint}
    (hy : cartesianRadius y = 1) : capSphereRadialMap a y = y := by
  simp [capSphereRadialMap, hy]

theorem capSphereRadialMap_eq_left (a : ℝ) {y : PolarPoint}
    (hy : cartesianRadius y ≤ 1 / 2) :
    capSphereRadialMap a y = capSphereSlope a • y := by
  by_cases hy0 : y = 0
  · subst y
    simp
  · rw [capSphereRadialMap, capSphereProfile_eq_left a hy,
      mul_div_cancel_right₀ _ (cartesianRadius_pos hy0).ne']

theorem capSphereRadialMap_zero_germ (a : ℝ) :
    capSphereRadialMap a =ᶠ[𝓝 0] fun y : PolarPoint => capSphereSlope a • y := by
  have hn : {y : PolarPoint | cartesianRadius y < 1 / 2} ∈ 𝓝 0 :=
    (isOpen_lt continuous_cartesianRadius continuous_const).mem_nhds
      (by norm_num [cartesianRadius])
  filter_upwards [hn] with y hy
  exact capSphereRadialMap_eq_left a hy.le

theorem contDiff_capSphereRadialMap (a : ℝ) : ContDiff ℝ ∞ (capSphereRadialMap a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y = 0
  · subst y
    have hc : ContDiff ℝ ∞ (fun y : PolarPoint => capSphereSlope a • y) :=
      (capSphereSlope a • ContinuousLinearMap.id ℝ PolarPoint).contDiff
    exact hc.contDiffAt.congr_of_eventuallyEq (capSphereRadialMap_zero_germ a)
  · have hr := contDiffAt_cartesianRadius hy
    exact (((contDiff_capSphereProfile a).contDiffAt.comp y hr).div hr
      (cartesianRadius_pos hy).ne').smul contDiffAt_id

theorem capSphereRadialMap_radius {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (y : PolarPoint) :
    cartesianRadius (capSphereRadialMap a y) = capSphereProfile a (cartesianRadius y) := by
  by_cases hy : y = 0
  · subst y
    simp [cartesianRadius]
  · have hr := cartesianRadius_pos hy
    rw [capSphereRadialMap, capDisk_radius_smul,
      abs_of_pos (div_pos (capSphereProfile_pos ha ha1 hr) hr)]
    exact div_mul_cancel₀ _ hr.ne'

theorem capSphereRadialMap_injective {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Function.Injective (capSphereRadialMap a) := by
  intro x y he
  have hr := congrArg cartesianRadius he
  rw [capSphereRadialMap_radius ha ha1, capSphereRadialMap_radius ha ha1] at hr
  have hr' := (strictMono_capSphereProfile ha ha1).injective hr
  by_cases hx : x = 0
  · subst x
    exact ((capDisk_radius_eq_zero_iff y).mp (by simpa [cartesianRadius] using hr'.symm)).symm
  · have hc : capSphereProfile a (cartesianRadius x) / cartesianRadius x ≠ 0 :=
      (div_pos (capSphereProfile_pos ha ha1 (cartesianRadius_pos hx)) (cartesianRadius_pos hx)).ne'
    unfold capSphereRadialMap at he
    rw [← hr'] at he
    have hh := congrArg (fun z : PolarPoint =>
      (capSphereProfile a (cartesianRadius x) / cartesianRadius x)⁻¹ • z) he
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh

theorem capSphereRadialMap_mapsTo_disk {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    MapsTo (capSphereRadialMap a) {y : PolarPoint | cartesianRadius y ≤ 1}
      {y : PolarPoint | cartesianRadius y ≤ 1} := by
  intro y hy
  change cartesianRadius (capSphereRadialMap a y) ≤ 1
  rw [capSphereRadialMap_radius ha ha1]
  simpa only [capSphereProfile_one] using (strictMono_capSphereProfile ha ha1).monotone hy

theorem capSphereRadialMap_surjOn_disk (a : ℝ) :
    SurjOn (capSphereRadialMap a) {y : PolarPoint | cartesianRadius y ≤ 1}
      {y : PolarPoint | cartesianRadius y ≤ 1} := by
  intro y hy
  by_cases hy0 : y = 0
  · subst y
    exact ⟨0, by norm_num [cartesianRadius], capSphereRadialMap_zero a⟩
  · have hr := cartesianRadius_pos hy0
    have hiv := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
      (contDiff_capSphereProfile a).continuous.continuousOn
    have hmem : cartesianRadius y ∈ Icc (capSphereProfile a 0) (capSphereProfile a 1) := by
      rw [capSphereProfile_zero, capSphereProfile_one]
      exact ⟨hr.le, hy⟩
    obtain ⟨q, hq, hqy⟩ := hiv hmem
    have hq0 : 0 < q := by
      by_contra hn
      have he : q = 0 := le_antisymm (le_of_not_gt hn) hq.1
      rw [he, capSphereProfile_zero] at hqy
      linarith
    let x : PolarPoint := (q / cartesianRadius y) • y
    have hx : cartesianRadius x = q := by
      dsimp only [x]
      rw [capDisk_radius_smul, abs_of_pos (div_pos hq0 hr)]
      exact div_mul_cancel₀ _ hr.ne'
    refine ⟨x, ?_, ?_⟩
    · change cartesianRadius x ≤ 1
      rw [hx]
      exact hq.2
    rw [capSphereRadialMap, hx, hqy]
    dsimp [x]
    rw [smul_smul]
    have he : cartesianRadius y / q * (q / cartesianRadius y) = 1 := by
      field_simp [hr.ne', hq0.ne']
    rw [he, one_smul]

theorem capSphereRadialMap_bijOn_disk {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    BijOn (capSphereRadialMap a) {y : PolarPoint | cartesianRadius y ≤ 1}
      {y : PolarPoint | cartesianRadius y ≤ 1} :=
  ⟨capSphereRadialMap_mapsTo_disk ha ha1, (capSphereRadialMap_injective ha ha1).injOn,
    capSphereRadialMap_surjOn_disk a⟩

theorem hasFDerivAt_capSphereRadialMap_zero (a : ℝ) :
    HasFDerivAt (capSphereRadialMap a)
      (capSphereSlope a • ContinuousLinearMap.id ℝ PolarPoint) 0 := by
  have hd : HasFDerivAt (fun y : PolarPoint => capSphereSlope a • y)
      (capSphereSlope a • ContinuousLinearMap.id ℝ PolarPoint) 0 :=
    (hasFDerivAt_id (0 : PolarPoint)).const_smul (capSphereSlope a)
  exact hd.congr_of_eventuallyEq (capSphereRadialMap_zero_germ a)

theorem capSphereRadialMap_polarMap (a : ℝ) {p : PolarPoint} (hp : 0 < p.1) :
    capSphereRadialMap a (polarMap p) = polarMap (capSphereProfile a p.1, p.2) := by
  have hr : cartesianRadius (polarMap p) = p.1 := cartesianRadius_polarPosition hp p.2
  apply Prod.ext
  · change (capSphereProfile a (cartesianRadius (polarMap p)) /
      cartesianRadius (polarMap p)) * (polarMap p).1 = _
    rw [hr]
    simp only [polarMap, polarPosition]
    field_simp [hp.ne']
  · change (capSphereProfile a (cartesianRadius (polarMap p)) /
      cartesianRadius (polarMap p)) * (polarMap p).2 = _
    rw [hr]
    simp only [polarMap, polarPosition]
    field_simp [hp.ne']

theorem capSphereRadialMap_polar_germ (a : ℝ) {p : PolarPoint} (hp : 0 < p.1) :
    (capSphereRadialMap a ∘ polarMap) =ᶠ[𝓝 p]
      (polarMap ∘ fun q : PolarPoint => (capSphereProfile a q.1, q.2)) := by
  have hn : {q : PolarPoint | 0 < q.1} ∈ 𝓝 p :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hp
  filter_upwards [hn] with q hq
  exact capSphereRadialMap_polarMap a hq

theorem capSphereRadialMap_fderiv_injective {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (y : PolarPoint) :
    Function.Injective (fderiv ℝ (capSphereRadialMap a) y) := by
  by_cases hy : y = 0
  · subst y
    rw [(hasFDerivAt_capSphereRadialMap_zero a).fderiv]
    intro u v huv
    change capSphereSlope a • u = capSphereSlope a • v at huv
    have he := congrArg (fun z : PolarPoint => (capSphereSlope a)⁻¹ • z) huv
    simpa only [smul_smul, inv_mul_cancel₀ (capSphereSlope_pos ha ha1).ne', one_smul] using he
  · let p : PolarPoint := (cartesianRadius y, (Complex.equivRealProdCLM.symm y).arg)
    have hpρ : 0 < p.1 := cartesianRadius_pos hy
    have hp : polarMap p = y := polarMap_cartesianCoordinates y
    let T : PolarPoint → PolarPoint := fun q => (capSphereProfile a q.1, q.2)
    let J : PolarPoint →L[ℝ] PolarPoint :=
      (capSphereSpeed a p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)
    have hJ_apply (v : PolarPoint) : J v = (capSphereSpeed a p.1 * v.1, v.2) := by
      simp [J]
    have hfirst : HasFDerivAt (fun q : PolarPoint => capSphereProfile a q.1)
        (capSphereSpeed a p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
      (hasDerivAt_capSphereProfile a p.1).comp_hasFDerivAt p hasFDerivAt_fst
    have hT : HasFDerivAt T J p := hfirst.prodMk hasFDerivAt_snd
    have hJinj : Function.Injective J := by
      intro u v huv
      rw [hJ_apply, hJ_apply] at huv
      apply Prod.ext
      · exact mul_left_cancel₀ (capSphereSpeed_pos ha ha1 p.1).ne'
          (congrArg (fun w : PolarPoint => w.1) huv)
      · have h2 := congrArg (fun w : PolarPoint => w.2) huv
        exact h2
    have heq : (capSphereRadialMap a ∘ polarMap) =ᶠ[𝓝 p] (polarMap ∘ T) :=
      capSphereRadialMap_polar_germ a hpρ
    have hdleft := ((contDiff_capSphereRadialMap a).differentiable (by simp)
      (polarMap p)).hasFDerivAt.comp p (hasFDerivAt_polarMap p)
    have hdright := (hasFDerivAt_polarMap (T p)).comp p hT
    have hder := heq.fderiv_eq (𝕜 := ℝ)
    rw [hdleft.fderiv, hdright.fderiv, hp] at hder
    have hcomp : Function.Injective
        ((fderiv ℝ (capSphereRadialMap a) y).comp (polarJacobian p)) := by
      rw [hder]
      exact (polarJacobian_bijective (capSphereProfile_pos ha ha1 hpρ).ne').injective.comp hJinj
    intro u v huv
    obtain ⟨u', hu⟩ := (polarJacobian_bijective hpρ.ne').surjective u
    obtain ⟨v', hv⟩ := (polarJacobian_bijective hpρ.ne').surjective v
    have huv' : u' = v' := hcomp (by
      simpa only [ContinuousLinearMap.comp_apply, hu, hv] using huv)
    exact hu.symm.trans ((congrArg (polarJacobian p) huv').trans hv)

/-- The reciprocal collar profile gives precisely the physical radius required
by inversion between normalized north and south stereographic coordinates. -/
theorem capDiskParameter_capSphereRadialMap {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) {y : PolarPoint} (hy : 3 / 4 ≤ cartesianRadius y) :
    capDiskParameter R L (capSphereRadialMap (capSphereRatio R L) y) =
      R / cartesianRadius y - R := by
  have ha := capSphereRatio_mem hR hL
  have hr : cartesianRadius y ≠ 0 := by linarith
  rw [capDiskParameter, capSphereRadialMap_radius ha.1 ha.2,
    capSphereProfile_eq_right _ hy]
  unfold capSphereRatio
  field_simp [(add_pos hL hR).ne', hr]
  ring

theorem capDiskMap_capSphereRadialMap_collar {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) {y : PolarPoint}
    (hy : 3 / 4 ≤ cartesianRadius y)
    (hflat : R / cartesianRadius y < R + L / 4) :
    capDiskMap R h L (capSphereRadialMap (capSphereRatio R L) y) =
      graphMap id (fun _ => h) ((R / cartesianRadius y ^ 2) • y) := by
  have ha := capSphereRatio_mem hR hL
  have hr : 0 < cartesianRadius y := by linarith
  have hf := capSphereProfile_pos ha.1 ha.2 hr
  have hs : capDiskParameter R L (capSphereRadialMap (capSphereRatio R L) y) ≤ L / 4 := by
    rw [capDiskParameter_capSphereRadialMap hR hL hy]
    linarith
  rw [capDisk_outer_collar R h hL hs]
  apply congrArg (graphMap id (fun _ => h))
  rw [capDiskParameter_capSphereRadialMap hR hL hy, capSphereRadialMap_radius ha.1 ha.2]
  unfold capSphereRadialMap
  rw [smul_smul]
  congr 1
  field_simp [hr.ne', hf.ne']
  ring

theorem capDiskMap_capSphereRadialMap_rim_germ {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L) (h : ℝ) {y : PolarPoint}
    (hy : cartesianRadius y = 1) :
    (capDiskMap R h L ∘ capSphereRadialMap (capSphereRatio R L)) =ᶠ[𝓝 y]
      fun z : PolarPoint => graphMap id (fun _ => h) ((R / cartesianRadius z ^ 2) • z) := by
  let d : ℝ := max (3 / 4) (R / (R + L / 4))
  have hden : 0 < R + L / 4 := by linarith
  have hd : d < 1 := max_lt (by norm_num) ((div_lt_one hden).2 (by linarith))
  have hn : {z : PolarPoint | d < cartesianRadius z} ∈ 𝓝 y :=
    (isOpen_lt continuous_const continuous_cartesianRadius).mem_nhds
      (by change d < cartesianRadius y; rwa [hy])
  filter_upwards [hn] with z hz
  have hquarter : (3 / 4 : ℝ) ≤ cartesianRadius z := (le_max_left _ _).trans hz.le
  have hr : 0 < cartesianRadius z := by linarith
  have hratio : R / (R + L / 4) < cartesianRadius z := (le_max_right _ _).trans_lt hz
  have hflat : R / cartesianRadius z < R + L / 4 := by
    apply (div_lt_iff₀ hr).2
    have hh := (div_lt_iff₀ hden).mp hratio
    nlinarith
  exact capDiskMap_capSphereRadialMap_collar hR hL h hquarter hflat

end ContinuousFlexibility
