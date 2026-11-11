import ContinuousFlexibility.Scalar.RectangleParameterIntegral
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Smooth division by the two endpoint factors

The existing `dslope` is the single endpoint quotient. Its genuine
fixed-interval integral formula gives smoothness across the endpoint.
Applying it twice divides a function with two zeros by both root
distances; the same construction treats both orientations.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators

theorem rootDivision_affine_mem
    {U : Set ℝ} (hU : Convex ℝ U) {a x t : ℝ}
    (ha : a ∈ U) (hx : x ∈ U) (ht : t ∈ Icc (0 : ℝ) 1) :
    a + t * (x - a) ∈ U := by
  have hh : (1 - t) • a + t • x ∈ U :=
    hU ha hx (sub_nonneg.mpr ht.2) ht.1 (by ring)
  convert hh using 1 <;> simp only [smul_eq_mul] <;> ring

/-- The true difference quotient, including the derivative at the anchor,
is the fixed compact integral of the original derivative. -/
theorem dslope_eq_intervalIntegral_deriv
    {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hf : ContDiffOn ℝ ∞ f U) {a x : ℝ} (ha : a ∈ U) (hx : x ∈ U) :
    dslope f a x = ∫ t in (0 : ℝ)..1, deriv f (a + t * (x - a)) := by
  by_cases hxa : x = a
  · subst x
    simp only [dslope_same, sub_self, mul_zero, add_zero,
      intervalIntegral.integral_const, sub_zero, one_smul]
  have hseg : uIcc a x ⊆ U := hconv.ordConnected.uIcc_subset ha hx
  have hdf : ContDiffOn ℝ ∞ (deriv f) U :=
    hf.deriv_of_isOpen hU (by simp)
  have hFTC : (∫ y in a..x, deriv f y) = f x - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => ((hf.contDiffAt (hU.mem_nhds (hseg hy))).differentiableAt
        (by simp)).hasDerivAt)
      (hdf.continuousOn.mono hseg).intervalIntegrable
  have hchange := intervalIntegral.smul_integral_comp_mul_add
    (f := deriv f) (a := (0 : ℝ)) (b := 1) (x - a) a
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] at hchange
  have he : (fun t : ℝ => deriv f ((x - a) * t + a)) =
      fun t => deriv f (a + t * (x - a)) := by
    funext t
    congr 1
    ring
  rw [he] at hchange
  apply mul_left_cancel₀ (sub_ne_zero.mpr hxa)
  calc
    (x - a) * dslope f a x = f x - f a := by
      simpa only [smul_eq_mul] using sub_smul_dslope f a x
    _ = ∫ y in a..x, deriv f y := hFTC.symm
    _ = (x - a) * ∫ t in (0 : ℝ)..1, deriv f (a + t * (x - a)) := hchange.symm

/-- Smooth division at a root on an open real interval. No global
smoothness outside that interval is required. -/
theorem contDiffOn_dslope_of_convex
    {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hf : ContDiffOn ℝ ∞ f U) {a : ℝ} (ha : a ∈ U) :
    ContDiffOn ℝ ∞ (dslope f a) U := by
  have hdf : ContDiffOn ℝ ∞ (deriv f) U :=
    hf.deriv_of_isOpen hU (by simp)
  have hparam : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => deriv f (a + p.2 * (p.1 - a))) (x, t) := by
    intro x hx t ht
    exact (hdf.contDiffAt
      (hU.mem_nhds (rootDivision_affine_mem hconv ha hx ht))).comp (x, t)
        (contDiffAt_const.add
          (contDiffAt_snd.mul (contDiffAt_fst.sub contDiffAt_const)))
  have hi : ContDiffOn ℝ ∞
      (fun x : ℝ => ∫ t in (0 : ℝ)..1, deriv f (a + t * (x - a))) U := by
    intro x hx
    exact (contDiffAt_intervalIntegral_parameter hU (by norm_num) hparam hx).contDiffWithinAt
  exact hi.congr (fun x hx => dslope_eq_intervalIntegral_deriv hU hconv hf ha hx)

/-- Scalar linear precomposition for actual ordinary jets on an open
domain. Smoothness of the original function is only local. -/
theorem iteratedDeriv_comp_const_mul_of_contDiffOn
    {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (c : ℝ) {x : ℝ} (hx : c * x ∈ U) (n : ℕ) :
    iteratedDeriv n (fun y => f (c * y)) x = c ^ n * iteratedDeriv n f (c * x) := by
  let L : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ
  have hL (y : ℝ) : L y = c * y := by
    simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  have hx' : L x ∈ U := by simpa only [hL] using hx
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hd := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn
    hx' (by simp : (n : ℕ∞ω) ≤ ∞)
  rw [iteratedFDerivWithin_of_isOpen n hpre hx',
    iteratedFDerivWithin_of_isOpen n hU hx'] at hd
  have he : (fun y => f (c * y)) = f ∘ L := by
    funext y
    simp only [Function.comp_apply, hL]
  rw [he, iteratedDeriv_eq_iteratedFDeriv, hd,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [hL, mul_one, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const, Fintype.card_fin, smul_eq_mul]

theorem iteratedDeriv_comp_rootAffine
    {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (a c : ℝ) {x : ℝ}
    (hx : a + c * (x - a) ∈ U) (n : ℕ) :
    iteratedDeriv n (fun y => f (a + c * (y - a))) x =
      c ^ n * iteratedDeriv n f (a + c * (x - a)) := by
  let V : Set ℝ := (fun y : ℝ => a + y) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have hg : ContDiffOn ℝ ∞ (fun y : ℝ => f (a + y)) V :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hy => hy)
  change iteratedDeriv n (fun y => (fun q => f (a + c * q)) (y - a)) x = _
  rw [iteratedDeriv_comp_sub_const]
  have h := iteratedDeriv_comp_const_mul_of_contDiffOn hV hg c hx n
  simpa only [iteratedDeriv_comp_const_add] using h

/-- Every actual jet of the endpoint quotient is an integral of the
next original jet. The scalar factor records the exact radial order. -/
theorem iteratedDeriv_dslope_eq_intervalIntegral
    {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hf : ContDiffOn ℝ ∞ f U) {a x : ℝ} (ha : a ∈ U) (hx : x ∈ U) (n : ℕ) :
    iteratedDeriv n (dslope f a) x =
      ∫ t in (0 : ℝ)..1, t ^ n * iteratedDeriv (n + 1) f (a + t * (x - a)) := by
  let F : ℝ × ℝ → ℝ := fun p => deriv f (a + p.2 * (p.1 - a))
  have hdf : ContDiffOn ℝ ∞ (deriv f) U := hf.deriv_of_isOpen hU (by simp)
  have hparam : ∀ y ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ F (y, t) := by
    intro y hy t ht
    exact (hdf.contDiffAt
      (hU.mem_nhds (rootDivision_affine_mem hconv ha hy ht))).comp (y, t)
        (contDiffAt_const.add
          (contDiffAt_snd.mul (contDiffAt_fst.sub contDiffAt_const)))
  have he : dslope f a =ᶠ[𝓝 x]
      (fun y => ∫ t in Icc (0 : ℝ) 1, F (y, t)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [dslope_eq_intervalIntegral_deriv hU hconv hf ha hy]
    simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc, F]
  have hI : iteratedDeriv n (fun y => ∫ t in Icc (0 : ℝ) 1, F (y, t)) x =
      ∫ t in Icc (0 : ℝ) 1, iteratedDeriv n (fun y => F (y, t)) x := by
    simpa only [iteratedDeriv_eq_iteratedFDeriv] using
      iteratedFDeriv_compactIntegral_parameter_apply hU isCompact_Icc hparam n hx
        (fun _ : Fin n => (1 : ℝ))
  rw [Filter.EventuallyEq.iteratedDeriv_eq n he, hI]
  have hpoint : (∫ t in Icc (0 : ℝ) 1, iteratedDeriv n (fun y => F (y, t)) x) =
      ∫ t in Icc (0 : ℝ) 1, t ^ n * iteratedDeriv (n + 1) f (a + t * (x - a)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    simpa only [F, iteratedDeriv_succ'] using
      iteratedDeriv_comp_rootAffine hU hdf a t
        (rootDivision_affine_mem hconv ha hx ht) n
  rw [hpoint]
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc]

/-- Dividing once does not enlarge a uniform next-jet bound on the
closed interval. It also does not divide by the interval length. -/
theorem abs_iteratedDeriv_dslope_le
    {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hf : ContDiffOn ℝ ∞ f U) {l h a x M : ℝ}
    (hclosed : Icc l h ⊆ U) (ha : a ∈ Icc l h) (hx : x ∈ Icc l h)
    (hM : 0 ≤ M) (n : ℕ)
    (hbound : ∀ y ∈ Icc l h, |iteratedDeriv (n + 1) f y| ≤ M) :
    |iteratedDeriv n (dslope f a) x| ≤ M := by
  rw [iteratedDeriv_dslope_eq_intervalIntegral hU hconv hf (hclosed ha) (hclosed hx) n]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M)
    (f := fun t => t ^ n * iteratedDeriv (n + 1) f (a + t * (x - a)))
    (fun t ht => by
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using uIoc_subset_uIcc ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht'.1 n)]
      calc
        t ^ n * |iteratedDeriv (n + 1) f (a + t * (x - a))| ≤ 1 * M :=
          mul_le_mul (pow_le_one₀ ht'.1 ht'.2)
            (hbound _ (rootDivision_affine_mem (convex_Icc l h) ha hx ht'))
            (abs_nonneg _) zero_le_one
        _ = M := one_mul M)
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hb

/-- The actual two-root divided function, using the existing endpoint
quotient twice. It is defined at the two endpoints as well. -/
def twoRootDivided (f : ℝ → ℝ) (l h r : ℝ) : ℝ :=
  -dslope (dslope f l) h r

theorem twoRootDivided_mul_rootFactors
    {f : ℝ → ℝ} {l h : ℝ} (hlh : l < h) (hl : f l = 0) (hh : f h = 0)
    (r : ℝ) :
    (r - l) * (h - r) * twoRootDivided f l h r = f r := by
  have hs : dslope f l h = 0 := by
    have he := sub_smul_dslope f l h
    simp only [smul_eq_mul, hl, hh, sub_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hlh.ne')
  have he₁ := sub_smul_dslope f l r
  have he₂ := sub_smul_dslope (dslope f l) h r
  simp only [smul_eq_mul, hl, sub_zero] at he₁
  simp only [smul_eq_mul, hs, sub_zero] at he₂
  calc
    (r - l) * (h - r) * twoRootDivided f l h r =
        (r - l) * ((r - h) * dslope (dslope f l) h r) := by
      dsimp only [twoRootDivided]
      ring
    _ = (r - l) * dslope f l r := by rw [he₂]
    _ = f r := he₁

theorem contDiffOn_twoRootDivided
    {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hf : ContDiffOn ℝ ∞ f U) {l h : ℝ} (hl : l ∈ U) (hh : h ∈ U) :
    ContDiffOn ℝ ∞ (twoRootDivided f l h) U :=
  (contDiffOn_dslope_of_convex hU hconv
    (contDiffOn_dslope_of_convex hU hconv hf hl) hh).neg

/-- Two root divisions cost exactly two original radial derivatives;
the estimate is uniform even when the component length tends to zero. -/
theorem abs_iteratedDeriv_twoRootDivided_le
    {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hf : ContDiffOn ℝ ∞ f U) {l h x M : ℝ} (hlh : l ≤ h)
    (hclosed : Icc l h ⊆ U) (hx : x ∈ Icc l h) (hM : 0 ≤ M) (n : ℕ)
    (hbound : ∀ y ∈ Icc l h, |iteratedDeriv (n + 2) f y| ≤ M) :
    |iteratedDeriv n (twoRootDivided f l h) x| ≤ M := by
  have hl : l ∈ Icc l h := ⟨le_rfl, hlh⟩
  have hh : h ∈ Icc l h := ⟨hlh, le_rfl⟩
  have hg := contDiffOn_dslope_of_convex hU hconv hf (hclosed hl)
  have hb : ∀ y ∈ Icc l h, |iteratedDeriv (n + 1) (dslope f l) y| ≤ M := by
    intro y hy
    exact abs_iteratedDeriv_dslope_le hU hconv hf hclosed hl hy hM (n + 1) hbound
  have hi := abs_iteratedDeriv_dslope_le hU hconv hg hclosed hh hx hM n hb
  simpa only [twoRootDivided, iteratedDeriv_neg, abs_neg] using hi

/-- A linear distance lower bound gives a positive lower bound for the
smooth two-root quotient. No endpoint distance is divided out at a root. -/
theorem twoRootDivided_lower_of_distance_bound
    {f : ℝ → ℝ} {l h c r : ℝ} (hlh : l < h)
    (hl : f l = 0) (hh : f h = 0) (hc : 0 ≤ c)
    (hr : r ∈ Ioo l h)
    (hbound : c * min (r - l) (h - r) ≤ f r) :
    c / (h - l) ≤ twoRootDivided f l h r := by
  have hL : 0 < h - l := sub_pos.mpr hlh
  have hprod : 0 < (r - l) * (h - r) :=
    mul_pos (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hdist : (r - l) * (h - r) ≤ min (r - l) (h - r) * (h - l) := by
    rcases le_total (r - l) (h - r) with hd | hd
    · rw [min_eq_left hd]
      nlinarith only [sq_nonneg (r - l)]
    · rw [min_eq_right hd]
      nlinarith only [sq_nonneg (h - r)]
  have hid := twoRootDivided_mul_rootFactors hlh hl hh r
  have hp : ((r - l) * (h - r)) * c ≤
      ((r - l) * (h - r)) * (twoRootDivided f l h r * (h - l)) := by
    calc
      ((r - l) * (h - r)) * c ≤ (min (r - l) (h - r) * (h - l)) * c :=
        mul_le_mul_of_nonneg_right hdist hc
      _ = (c * min (r - l) (h - r)) * (h - l) := by ring
      _ ≤ f r * (h - l) := mul_le_mul_of_nonneg_right hbound hL.le
      _ = ((r - l) * (h - r)) * (twoRootDivided f l h r * (h - l)) := by
        rw [← hid]
        ring
  exact (div_le_iff₀ hL).mpr (le_of_mul_le_mul_left hp hprod)

/-- The same bound includes the two true root values by continuity. -/
theorem twoRootDivided_lower_on_Icc
    {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hf : ContDiffOn ℝ ∞ f U) {l h c r : ℝ} (hlh : l < h)
    (hclosed : Icc l h ⊆ U) (hl : f l = 0) (hh : f h = 0) (hc : 0 ≤ c)
    (hbound : ∀ y ∈ Ioo l h, c * min (y - l) (h - y) ≤ f y)
    (hr : r ∈ Icc l h) :
    c / (h - l) ≤ twoRootDivided f l h r := by
  have hcont : ContinuousOn (twoRootDivided f l h) (Icc l h) :=
    (contDiffOn_twoRootDivided hU hconv hf
      (hclosed ⟨le_rfl, hlh.le⟩) (hclosed ⟨hlh.le, le_rfl⟩)).continuousOn.mono hclosed
  have hclosure : ContinuousOn (twoRootDivided f l h) (closure (Ioo l h)) := by
    simpa only [closure_Ioo hlh.ne] using hcont
  have hr' : r ∈ closure (Ioo l h) := by simpa only [closure_Ioo hlh.ne] using hr
  exact le_on_closure
    (fun y hy => twoRootDivided_lower_of_distance_bound hlh hl hh hc hy (hbound y hy))
    continuousOn_const hclosure hr'

end ContinuousFlexibility.Analysis
