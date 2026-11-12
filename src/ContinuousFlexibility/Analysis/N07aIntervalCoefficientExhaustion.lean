import ContinuousFlexibility.Analysis.N07aIntervalEnergyClosure
import ContinuousFlexibility.Analysis.IntervalWeakDivergence
import ContinuousFlexibility.Analysis.SpacesLpCurveDerivative
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Interior exhaustion of the actual open-interval coefficients

The affine inset moves the closed unit interval strictly into its interior.
A smooth cutoff then gives globally smooth approximating coefficients,
without extending the original coefficient or the weak unknown across an
endpoint. On the closed unit interval all derivatives are the actual
derivatives at the inset point, with their affine factors. The vanishing
cylinder weight increases under this inset, so its lower bound is retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

def n07aIntervalInsetGap (n : ℕ) : ℝ := 1 / ((n : ℝ) + 4)

theorem n07aIntervalInsetGap_pos (n : ℕ) : 0 < n07aIntervalInsetGap n := by
  unfold n07aIntervalInsetGap
  positivity

theorem n07aIntervalInsetGap_le (n : ℕ) : n07aIntervalInsetGap n ≤ 1 / 4 := by
  unfold n07aIntervalInsetGap
  apply one_div_le_one_div_of_le (by norm_num)
  linarith [Nat.cast_nonneg (α := ℝ) n]

def n07aIntervalInsetSlope (n : ℕ) : ℝ := 1 - 2 * n07aIntervalInsetGap n

theorem n07aIntervalInsetSlope_bounds (n : ℕ) :
    n07aIntervalInsetSlope n ∈ Icc (0 : ℝ) 1 := by
  have hp := n07aIntervalInsetGap_pos n
  have hb := n07aIntervalInsetGap_le n
  dsimp only [n07aIntervalInsetSlope]
  constructor <;> linarith

def n07aIntervalInset (n : ℕ) (x : ℝ) : ℝ :=
  n07aIntervalInsetGap n + n07aIntervalInsetSlope n * x

theorem n07aIntervalInset_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (n07aIntervalInset n) (n07aIntervalInsetSlope n) x := by
  unfold n07aIntervalInset
  simpa only [mul_one] using
    ((hasDerivAt_id' x).const_mul (n07aIntervalInsetSlope n)).const_add
      (n07aIntervalInsetGap n)

theorem n07aIntervalInset_contDiff (n : ℕ) : ContDiff ℝ ∞ (n07aIntervalInset n) :=
  contDiff_const.add (contDiff_const.mul contDiff_id)

theorem n07aIntervalInset_mem (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    n07aIntervalInset n x ∈ Ioo (0 : ℝ) 1 := by
  have hp := n07aIntervalInsetGap_pos n
  have hs := n07aIntervalInsetSlope_bounds n
  have hl := mul_nonneg hs.1 hx.1
  have hu := mul_le_of_le_one_right hs.1 hx.2
  dsimp only [n07aIntervalInset, n07aIntervalInsetSlope] at *
  constructor <;> linarith

theorem n07aIntervalInset_weight_le (n : ℕ) (x : ℝ) :
    cylinderWeight x ≤ cylinderWeight (n07aIntervalInset n x) := by
  have hp := n07aIntervalInsetGap_pos n
  have hb := n07aIntervalInsetGap_le n
  have hid : cylinderWeight (n07aIntervalInset n x) - cylinderWeight x =
      n07aIntervalInsetGap n * (1 - n07aIntervalInsetGap n) * (2 * x - 1) ^ 2 := by
    simp only [cylinderWeight, n07aIntervalInset, n07aIntervalInsetSlope]
    ring
  have hn := mul_nonneg (mul_nonneg hp.le (by linarith :
    0 ≤ 1 - n07aIntervalInsetGap n)) (sq_nonneg (2 * x - 1))
  linarith

theorem n07aIntervalInsetGap_tendsto :
    Tendsto n07aIntervalInsetGap atTop (𝓝 (0 : ℝ)) := by
  unfold n07aIntervalInsetGap
  have h := (tendsto_add_atTop_iff_nat 4).mpr
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h

theorem n07aIntervalInsetSlope_tendsto :
    Tendsto n07aIntervalInsetSlope atTop (𝓝 (1 : ℝ)) := by
  unfold n07aIntervalInsetSlope
  simpa only [mul_zero, sub_zero] using
    tendsto_const_nhds.sub (n07aIntervalInsetGap_tendsto.const_mul 2)

theorem n07aIntervalInset_tendsto (x : ℝ) :
    Tendsto (fun n => n07aIntervalInset n x) atTop (𝓝 x) := by
  simpa only [n07aIntervalInset, one_mul, zero_add] using
    n07aIntervalInsetGap_tendsto.add (n07aIntervalInsetSlope_tendsto.mul_const x)

private def n07aIntervalInsetBump (n : ℕ) : ContDiffBump (1 / 2 : ℝ) where
  rIn := (1 - n07aIntervalInsetGap n) / 2
  rOut := (1 - n07aIntervalInsetGap n / 2) / 2
  rIn_pos := by linarith [n07aIntervalInsetGap_le n]
  rIn_lt_rOut := by linarith [n07aIntervalInsetGap_pos n]

private theorem n07aIntervalInsetBump_support (n : ℕ) :
    tsupport (n07aIntervalInsetBump n : ℝ → ℝ) ⊆ Ioo (0 : ℝ) 1 := by
  rw [(n07aIntervalInsetBump n).tsupport_eq]
  intro x hx
  have hd := Metric.mem_closedBall.mp hx
  rw [Real.dist_eq, abs_le] at hd
  dsimp only [n07aIntervalInsetBump] at hd
  have hp := n07aIntervalInsetGap_pos n
  constructor <;> linarith [hd.1, hd.2]

private theorem n07aIntervalInsetBump_germ (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (n07aIntervalInsetBump n : ℝ → ℝ) =ᶠ[𝓝 (n07aIntervalInset n x)] (fun _ => 1) := by
  have hs := n07aIntervalInsetSlope_bounds n
  have hp := n07aIntervalInsetGap_pos n
  have hl := mul_nonneg hs.1 hx.1
  have hu := mul_le_of_le_one_right hs.1 hx.2
  have hball : n07aIntervalInset n x ∈
      Metric.ball (1 / 2 : ℝ) (n07aIntervalInsetBump n).rIn := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp only [n07aIntervalInset, n07aIntervalInsetSlope, n07aIntervalInsetBump] at *
    constructor <;> linarith
  filter_upwards [Metric.isOpen_ball.mem_nhds hball] with y hy
  exact (n07aIntervalInsetBump n).one_of_mem_closedBall
    (Metric.ball_subset_closedBall hy)

private def n07aIntervalTruncatedCoefficient (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => n07aIntervalInsetBump n x * f x

private theorem n07aIntervalTruncatedCoefficient_contDiff (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo (0 : ℝ) 1)) :
    ContDiff ℝ ∞ (n07aIntervalTruncatedCoefficient n f) :=
  contDiff_of_contDiffOn_of_tsupport_subset isOpen_Ioo
    ((n07aIntervalInsetBump n).contDiff.contDiffOn.mul hf)
    (tsupport_mul_subset_left.trans (n07aIntervalInsetBump_support n))

private theorem n07aIntervalTruncatedCoefficient_germ (n : ℕ) (f : ℝ → ℝ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    n07aIntervalTruncatedCoefficient n f =ᶠ[𝓝 (n07aIntervalInset n x)] f := by
  filter_upwards [n07aIntervalInsetBump_germ n hx] with y hy
  simp only [n07aIntervalTruncatedCoefficient, hy, one_mul]

/-- The genuine coefficient approximation; only the coefficient is cut off. -/
def n07aIntervalCoeffApprox (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => n07aIntervalTruncatedCoefficient n f (n07aIntervalInset n x)

theorem n07aIntervalCoeffApprox_contDiff (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo (0 : ℝ) 1)) :
    ContDiff ℝ ∞ (n07aIntervalCoeffApprox n f) :=
  (n07aIntervalTruncatedCoefficient_contDiff n hf).comp (n07aIntervalInset_contDiff n)

theorem n07aIntervalCoeffApprox_eq (n : ℕ) (f : ℝ → ℝ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    n07aIntervalCoeffApprox n f x = f (n07aIntervalInset n x) :=
  (n07aIntervalTruncatedCoefficient_germ n f hx).self_of_nhds

theorem n07aIntervalCoeffApprox_deriv (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv (n07aIntervalCoeffApprox n f) x =
      deriv f (n07aIntervalInset n x) * n07aIntervalInsetSlope n := by
  have hG := n07aIntervalTruncatedCoefficient_contDiff n hf
  have hd := ((hG.differentiable (by simp) (n07aIntervalInset n x)).hasDerivAt).comp x
    (n07aIntervalInset_hasDerivAt n x)
  have hd' : HasDerivAt (n07aIntervalCoeffApprox n f)
      (deriv (n07aIntervalTruncatedCoefficient n f) (n07aIntervalInset n x) *
        n07aIntervalInsetSlope n) x :=
    hd.congr_of_eventuallyEq (Eventually.of_forall fun y =>
      (Function.comp_apply :
        (n07aIntervalTruncatedCoefficient n f ∘ n07aIntervalInset n) y =
          n07aIntervalTruncatedCoefficient n f (n07aIntervalInset n y)).symm)
  rw [hd'.deriv, (n07aIntervalTruncatedCoefficient_germ n f hx).deriv_eq]

theorem n07aIntervalCoeffApprox_second (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv (deriv (n07aIntervalCoeffApprox n f)) x =
      deriv (deriv f) (n07aIntervalInset n x) * n07aIntervalInsetSlope n ^ 2 := by
  let G := n07aIntervalTruncatedCoefficient n f
  have hG : ContDiff ℝ ∞ G := n07aIntervalTruncatedCoefficient_contDiff n hf
  have hd : deriv (n07aIntervalCoeffApprox n f) =
      fun y => deriv G (n07aIntervalInset n y) * n07aIntervalInsetSlope n :=
    funext fun y => (((hG.differentiable (by simp) (n07aIntervalInset n y)).hasDerivAt).comp y
      (n07aIntervalInset_hasDerivAt n y)).deriv
  have hGd := (contDiff_infty_iff_deriv.mp hG).2
  have hdc := ((hGd.differentiable (by simp) (n07aIntervalInset n x)).hasDerivAt).comp x
    (n07aIntervalInset_hasDerivAt n x)
  have hdc' : HasDerivAt (fun y => deriv G (n07aIntervalInset n y))
      (deriv (deriv G) (n07aIntervalInset n x) * n07aIntervalInsetSlope n) x :=
    hdc.congr_of_eventuallyEq (Eventually.of_forall fun y =>
      (Function.comp_apply : (deriv G ∘ n07aIntervalInset n) y =
        deriv G (n07aIntervalInset n y)).symm)
  have hdd := hdc'.mul_const (n07aIntervalInsetSlope n)
  rw [hd, hdd.deriv, (n07aIntervalTruncatedCoefficient_germ n f hx).deriv.deriv_eq]
  ring

theorem n07aIntervalCoeffApprox_tendsto {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo (0 : ℝ) 1)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => n07aIntervalCoeffApprox n f x) atTop (𝓝 (f x)) := by
  have ht : Tendsto (fun n => f (n07aIntervalInset n x)) atTop (𝓝 (f x)) :=
    ((hf.continuousAt (isOpen_Ioo.mem_nhds hx)).tendsto.comp
      (n07aIntervalInset_tendsto x)).congr'
        (Eventually.of_forall fun n => (Function.comp_apply :
          (f ∘ fun k => n07aIntervalInset k x) n = f (n07aIntervalInset n x)))
  exact ht.congr' (Eventually.of_forall fun n =>
    (n07aIntervalCoeffApprox_eq n f (Ioo_subset_Icc_self hx)).symm)

theorem n07aIntervalCoeffApprox_deriv_tendsto {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo (0 : ℝ) 1)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => deriv (n07aIntervalCoeffApprox n f) x) atTop (𝓝 (deriv f x)) := by
  have hdf : ContinuousOn (deriv f) (Ioo (0 : ℝ) 1) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  have hlim : Tendsto (fun n => deriv f (n07aIntervalInset n x)) atTop (𝓝 (deriv f x)) :=
    ((hdf.continuousAt (isOpen_Ioo.mem_nhds hx)).tendsto.comp
      (n07aIntervalInset_tendsto x)).congr'
        (Eventually.of_forall fun n => (Function.comp_apply :
          (deriv f ∘ fun k => n07aIntervalInset k x) n = deriv f (n07aIntervalInset n x)))
  have hm : Tendsto (fun n => deriv f (n07aIntervalInset n x) * n07aIntervalInsetSlope n)
      atTop (𝓝 (deriv f x)) := by
    simpa only [mul_one] using hlim.mul n07aIntervalInsetSlope_tendsto
  exact hm.congr' (Eventually.of_forall fun n =>
    (n07aIntervalCoeffApprox_deriv n hf (Ioo_subset_Icc_self hx)).symm)

end ContinuousFlexibility.Analysis
