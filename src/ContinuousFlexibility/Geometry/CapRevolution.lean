module

public import ContinuousFlexibility.Geometry.CapMeridian
public import ContinuousFlexibility.Geometry.GraphEmbedding
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Order.Compact

/-!
# The actual surface obtained by revolving the constructed cap meridian

The angular-coordinate map has its true Euclidean pullback tensor and an
injective differential away from the axis. The circle-coordinate map is used
for actual image injectivity; real angular parameters are periodic.
Axis charts, the marked top extension and the standard-sphere assembly remain
separate obligations of the fixed-cap construction in Section 2.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def capRevolution (R h L : ℝ) (x : PolarPoint) : E3 :=
  graphMap (fun q => (capMeridianRadius R L q.1 * Real.cos q.2,
    capMeridianRadius R L q.1 * Real.sin q.2))
    (fun q => capMeridianHeight h L q.1) x

@[simp] theorem capRevolution_zero (R h L : ℝ) (x : PolarPoint) :
    capRevolution R h L x 0 = capMeridianRadius R L x.1 * Real.cos x.2 := by
  simp [capRevolution]

@[simp] theorem capRevolution_one (R h L : ℝ) (x : PolarPoint) :
    capRevolution R h L x 1 = capMeridianRadius R L x.1 * Real.sin x.2 := by
  simp [capRevolution]

@[simp] theorem capRevolution_two (R h L : ℝ) (x : PolarPoint) :
    capRevolution R h L x 2 = capMeridianHeight h L x.1 := by simp [capRevolution]

theorem contDiff_capRevolution (R h L : ℝ) : ContDiff ℝ ∞ (capRevolution R h L) := by
  apply contDiff_graphMap
  · exact (((contDiff_capMeridianRadius R L).comp contDiff_fst).mul
      contDiff_snd.cos).prodMk
      (((contDiff_capMeridianRadius R L).comp contDiff_fst).mul contDiff_snd.sin)
  · exact (contDiff_capMeridianHeight h L).comp contDiff_fst

theorem capRevolution_fderiv (R h : ℝ) {L : ℝ} (hL : 0 < L)
    (x v : PolarPoint) :
    fderiv ℝ (capRevolution R h L) x v =
      (capRadialVelocity (x.1 / L) * v.1 * Real.cos x.2 -
        capMeridianRadius R L x.1 * Real.sin x.2 * v.2) • e3Basis 0 +
      (capRadialVelocity (x.1 / L) * v.1 * Real.sin x.2 +
        capMeridianRadius R L x.1 * Real.cos x.2 * v.2) • e3Basis 1 +
      (-capDownwardVelocity (x.1 / L) * v.1) • e3Basis 2 := by
  have hfst : HasFDerivAt (fun q : PolarPoint => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun q : PolarPoint => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    hasFDerivAt_snd
  have hr := (hasDerivAt_capMeridianRadius R hL x.1).comp_hasFDerivAt x hfst
  have hz := (hasDerivAt_capMeridianHeight h hL x.1).comp_hasFDerivAt x hfst
  have hc := (Real.hasDerivAt_cos x.2).comp_hasFDerivAt x hsnd
  have hs := (Real.hasDerivAt_sin x.2).comp_hasFDerivAt x hsnd
  have hd := hasFDerivAt_graphMap ((hr.mul hc).prodMk (hr.mul hs)) hz
  change HasFDerivAt (capRevolution R h L) _ x at hd
  rw [hd.fderiv]
  ext i
  fin_cases i <;> simp [graphDifferential, e3Basis] <;> ring

/-- The intrinsic metric is `ds² + r(s)² dθ²`, identified through the actual
derivative in Euclidean three-space. -/
theorem capRevolution_pullback_metric (R h : ℝ) {L : ℝ} (hL : 0 < L)
    (x u v : PolarPoint) :
    inner ℝ (fderiv ℝ (capRevolution R h L) x u)
      (fderiv ℝ (capRevolution R h L) x v) =
        u.1 * v.1 + capMeridianRadius R L x.1 ^ 2 * u.2 * v.2 := by
  rw [capRevolution_fderiv R h hL, capRevolution_fderiv R h hL,
    e3_inner_coordinates]
  simp [e3Basis]
  have ht := Real.cos_sq_add_sin_sq x.2
  have hv : capRadialVelocity (x.1 / L) ^ 2 + capDownwardVelocity (x.1 / L) ^ 2 = 1 := by
    dsimp [capRadialVelocity, capDownwardVelocity]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * capTurn (x.1 / L))]
  linear_combination
    (capRadialVelocity (x.1 / L) ^ 2 * u.1 * v.1 +
      capMeridianRadius R L x.1 ^ 2 * u.2 * v.2) * ht + u.1 * v.1 * hv

theorem capRevolution_fderiv_injective (R h : ℝ) {L : ℝ} (hL : 0 < L)
    {x : PolarPoint} (hr : capMeridianRadius R L x.1 ≠ 0) :
    Function.Injective (fderiv ℝ (capRevolution R h L) x) := by
  have hker (v : PolarPoint) (hv : fderiv ℝ (capRevolution R h L) x v = 0) : v = 0 := by
    have hm := capRevolution_pullback_metric R h hL x v v
    rw [hv, inner_zero_left] at hm
    have h1 : v.1 = 0 := by nlinarith [sq_nonneg (capMeridianRadius R L x.1 * v.2)]
    have h2 : capMeridianRadius R L x.1 * v.2 = 0 := by
      nlinarith [sq_nonneg v.1]
    exact Prod.ext h1 ((mul_eq_zero.mp h2).resolve_left hr)
  intro u v huv
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, huv, sub_self]

theorem capRevolution_left_collar (R h : ℝ) {L : ℝ} (hL : 0 < L)
    {x : PolarPoint} (hx : x.1 ≤ L / 4) :
    capRevolution R h L x =
      graphMap id (fun _ => h) ((R + x.1) * Real.cos x.2, (R + x.1) * Real.sin x.2) := by
  ext i
  fin_cases i <;> simp [capRevolution, capMeridianRadius_eq_left R hL hx,
    capMeridianHeight_eq_left h hL hx]

theorem capRevolution_right_collar (R h : ℝ) {L : ℝ} (hL : 0 < L)
    {x : PolarPoint} (hx : 3 * L / 4 ≤ x.1) :
    capRevolution R h L x =
      graphMap id (fun _ => h - L * capDrop)
        ((R + L - x.1) * Real.cos x.2, (R + L - x.1) * Real.sin x.2) := by
  ext i
  fin_cases i <;> simp [capRevolution, capMeridianRadius_eq_right R hL hx,
    capMeridianHeight_eq_right h hL hx]

def capCylinderMap (R h L : ℝ) (q : ℝ × Circle) : E3 :=
  (capMeridianRadius R L q.1 * (q.2 : ℂ).re) • e3Basis 0 +
    (capMeridianRadius R L q.1 * (q.2 : ℂ).im) • e3Basis 1 +
    capMeridianHeight h L q.1 • e3Basis 2

@[simp] theorem capCylinderMap_zero (R h L : ℝ) (q : ℝ × Circle) :
    capCylinderMap R h L q 0 = capMeridianRadius R L q.1 * (q.2 : ℂ).re := by
  simp [capCylinderMap, e3Basis]

@[simp] theorem capCylinderMap_one (R h L : ℝ) (q : ℝ × Circle) :
    capCylinderMap R h L q 1 = capMeridianRadius R L q.1 * (q.2 : ℂ).im := by
  simp [capCylinderMap, e3Basis]

@[simp] theorem capCylinderMap_two (R h L : ℝ) (q : ℝ × Circle) :
    capCylinderMap R h L q 2 = capMeridianHeight h L q.1 := by
  simp [capCylinderMap, e3Basis]

theorem continuous_capCylinderMap (R h L : ℝ) : Continuous (capCylinderMap R h L) := by
  have hr : Continuous (fun q : ℝ × Circle => capMeridianRadius R L q.1) :=
    (contDiff_capMeridianRadius R L).continuous.comp continuous_fst
  have hz : Continuous (fun q : ℝ × Circle => capMeridianHeight h L q.1) :=
    (contDiff_capMeridianHeight h L).continuous.comp continuous_fst
  have hu : Continuous (fun q : ℝ × Circle => (q.2 : ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  exact (((hr.mul (Complex.continuous_re.comp hu)).smul continuous_const).add
    ((hr.mul (Complex.continuous_im.comp hu)).smul continuous_const)).add
      (hz.smul continuous_const)

theorem capCylinderMap_radial_sq (R h L : ℝ) (q : ℝ × Circle) :
    capCylinderMap R h L q 0 ^ 2 + capCylinderMap R h L q 1 ^ 2 =
      capMeridianRadius R L q.1 ^ 2 := by
  have hu : (q.2 : ℂ).re ^ 2 + (q.2 : ℂ).im ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, pow_two] using Circle.normSq_coe q.2
  simp only [capCylinderMap_zero, capCylinderMap_one]
  calc
    _ = capMeridianRadius R L q.1 ^ 2 *
        ((q.2 : ℂ).re ^ 2 + (q.2 : ℂ).im ^ 2) := by ring
    _ = _ := by rw [hu, mul_one]

/-- No angular quotient is hidden in the injectivity statement: the angular
variable is an actual point of the unit circle. -/
theorem capCylinderMap_injOn {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    Set.InjOn (capCylinderMap R h L) {q : ℝ × Circle | q.1 ∈ Icc 0 L} := by
  rintro ⟨s, u⟩ hs ⟨t, v⟩ ht he
  have hrs : 0 < capMeridianRadius R L s := hR.trans_le (capMeridianRadius_core_le R hL hs)
  have hrt : 0 < capMeridianRadius R L t := hR.trans_le (capMeridianRadius_core_le R hL ht)
  have h0 : capMeridianRadius R L s * (u : ℂ).re =
      capMeridianRadius R L t * (v : ℂ).re := by
    simpa using congrArg (fun y : E3 => y 0) he
  have h1 : capMeridianRadius R L s * (u : ℂ).im =
      capMeridianRadius R L t * (v : ℂ).im := by
    simpa using congrArg (fun y : E3 => y 1) he
  have hz : capMeridianHeight h L s = capMeridianHeight h L t := by
    simpa using congrArg (fun y : E3 => y 2) he
  have hc : (capMeridianRadius R L s : ℂ) * (u : ℂ) =
      (capMeridianRadius R L t : ℂ) * (v : ℂ) := by
    apply Complex.ext
    · simpa using h0
    · simpa using h1
  have hr : capMeridianRadius R L s = capMeridianRadius R L t := by
    have hn := congrArg norm hc
    simpa [norm_mul, abs_of_pos hrs, abs_of_pos hrt] using hn
  have hst : s = t := capMeridian_injective R h hL (Prod.ext hr hz)
  apply Prod.ext hst
  apply Circle.ext
  apply Complex.ext
  · apply mul_left_cancel₀ hrs.ne'
    simpa only [← hst] using h0
  · apply mul_left_cancel₀ hrs.ne'
    simpa only [← hst] using h1

abbrev capClosedCylinder (L : ℝ) := Icc (0 : ℝ) L × Circle

def capClosedCylinderMap (R h L : ℝ) (q : capClosedCylinder L) : E3 :=
  capCylinderMap R h L ((q.1 : ℝ), q.2)

theorem continuous_capClosedCylinderMap (R h L : ℝ) :
    Continuous (capClosedCylinderMap R h L) :=
  (continuous_capCylinderMap R h L).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem capClosedCylinderMap_injective {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    Function.Injective (capClosedCylinderMap R h L) := by
  intro q p he
  have hh := capCylinderMap_injOn hR hL h
    (show ((q.1 : ℝ), q.2).1 ∈ Icc 0 L from q.1.property)
    (show ((p.1 : ℝ), p.2).1 ∈ Icc 0 L from p.1.property) he
  have hs : (q.1 : ℝ) = (p.1 : ℝ) := congrArg (fun v : ℝ × Circle => v.1) hh
  have hu : q.2 = p.2 := congrArg (fun v : ℝ × Circle => v.2) hh
  exact Prod.ext (Subtype.ext hs) hu

theorem isEmbedding_capClosedCylinderMap {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ) :
    Topology.IsEmbedding (capClosedCylinderMap R h L) := by
  exact ((continuous_capClosedCylinderMap R h L).isClosedEmbedding
    (capClosedCylinderMap_injective hR hL h)).isEmbedding

theorem capCylinderMap_core_outside {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (h : ℝ)
    {q : ℝ × Circle} (hq : q.1 ∈ Icc 0 L) :
    R ^ 2 ≤ capCylinderMap R h L q 0 ^ 2 + capCylinderMap R h L q 1 ^ 2 := by
  rw [capCylinderMap_radial_sq]
  have hr := capMeridianRadius_core_le R hL hq
  nlinarith

/-- Within the central open cylinder, the part after the attaching rim has
exactly the bottom height, as required for the later enclosed-volume region. -/
theorem capCylinderMap_inside_cylinder_bottom {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (h : ℝ) {q : ℝ × Circle} (hq : 0 ≤ q.1)
    (hinside : capCylinderMap R h L q 0 ^ 2 + capCylinderMap R h L q 1 ^ 2 < R ^ 2) :
    capCylinderMap R h L q 2 = h - L * capDrop := by
  have hs : L < q.1 := by
    by_contra hn
    exact (not_lt_of_ge (capCylinderMap_core_outside hR hL h
      ⟨hq, le_of_not_gt hn⟩)) hinside
  rw [capCylinderMap_two, capMeridianHeight_eq_right h hL (by linarith)]

end ContinuousFlexibility
