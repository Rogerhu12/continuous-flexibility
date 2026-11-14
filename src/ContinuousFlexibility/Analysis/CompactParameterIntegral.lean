module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

/-!
# Smooth dependence of a compact parameter integral

A fixed smooth cutoff converts the integral over `[0,1]` into a
parameter-dependent convolution. This uses the existing finite-order
convolution theorem and needs smoothness only on an open neighborhood
of the integration interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Convolution

set_option backward.isDefEq.respectTransparency false

/-- Smoothness in a finite-dimensional parameter survives integration over
the fixed interval. The integrand need only be smooth for `|t| < 3`. -/
theorem contDiffOn_compactParameterIntegral
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : ℕ∞} {U : Set P} (hU : IsOpen U) {H : P × ℝ → ℝ}
    (hH : ∀ p ∈ U, ∀ t : ℝ, |t| < 3 → ContDiffAt ℝ n H (p, t)) :
    ContDiffOn ℝ n (fun p => ∫ t in (0 : ℝ)..1, H (p, t)) U := by
  let β : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let f : ℝ → ℝ := (Ioc (0 : ℝ) 1).indicator (fun _ => 1)
  let g : P → ℝ → ℝ := fun p x => β (-x) * H (p, -x)
  have hf : Integrable f volume := by
    apply (integrable_indicator_iff measurableSet_Ioc).2
    exact integrableOn_const (by simp)
  have hgs : ∀ p x, p ∈ U → x ∉ closedBall (0 : ℝ) 2 → g p x = 0 := by
    intro p x _ hx
    have hx' : 2 < |x| := by simpa only [mem_closedBall, Real.dist_eq,
      sub_zero, not_le] using hx
    have hβ : β (-x) = 0 := β.zero_of_le_dist (by
      change (2 : ℝ) ≤ dist (-x) 0
      simpa only [Real.dist_eq, sub_zero, abs_neg] using hx'.le)
    simp only [g, hβ, zero_mul]
  have hg : ContDiffOn ℝ n (fun q : P × ℝ => g q.1 q.2) (U ×ˢ univ) := by
    intro q hq
    apply ContDiffAt.contDiffWithinAt
    by_cases hqsmall : |q.2| < 3
    · have harg : ContDiffAt ℝ n (fun y : P × ℝ => (y.1, -y.2)) q :=
        contDiffAt_fst.prodMk contDiffAt_snd.neg
      have hβ : ContDiffAt ℝ n (fun y : P × ℝ => β (-y.2)) q :=
        β.contDiffAt.comp q contDiffAt_snd.neg
      exact hβ.mul ((hH q.1 hq.1 (-q.2) (by simpa only [abs_neg] using hqsmall)).comp q harg)
    · have hlarge : 2 < |-q.2| := by
        rw [abs_neg]
        exact lt_of_lt_of_le (by norm_num) (le_of_not_gt hqsmall)
      have he : ∀ᶠ y : P × ℝ in 𝓝 q, 2 < |-y.2| :=
        (continuousAt_snd.neg.abs).eventually (Ioi_mem_nhds hlarge)
      apply (contDiffAt_const : ContDiffAt ℝ n (fun _ : P × ℝ => (0 : ℝ)) q).congr_of_eventuallyEq
      filter_upwards [he] with y hy
      change β (-y.2) * H (y.1, -y.2) = 0
      rw [β.zero_of_le_dist (by
        change (2 : ℝ) ≤ dist (-y.2) 0
        simpa only [Real.dist_eq, sub_zero] using hy.le), zero_mul]
  have hconv : ContDiffOn ℝ n
      (fun p => (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g p) 0) U := by
    apply contDiffOn_convolution_right_with_param_comp (ContinuousLinearMap.mul ℝ ℝ)
      (contDiffOn_const : ContDiffOn ℝ n (fun _ : P => (0 : ℝ)) U)
      hU (isCompact_closedBall (0 : ℝ) 2) hgs hf.locallyIntegrable
    simpa only [Function.HasUncurry.uncurry, Function.hasUncurryBase,
      Function.hasUncurryInduction, id_eq, Function.comp_def] using hg
  apply hconv.congr
  intro p _
  rw [convolution_def]
  have hi : (fun t : ℝ => ContinuousLinearMap.mul ℝ ℝ (f t) (g p (0 - t))) =
      (Ioc (0 : ℝ) 1).indicator (fun t => H (p, t)) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · have hβ : β t = 1 := β.one_of_mem_closedBall (by
        change dist t 0 ≤ (1 : ℝ)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1.le]
        exact ht.2)
      simp only [f, g, indicator_of_mem ht, ContinuousLinearMap.mul_apply',
        zero_sub, neg_neg, hβ, one_mul]
    · simp only [f, indicator_of_notMem ht, ContinuousLinearMap.mul_apply', zero_mul]
  rw [hi, integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le zero_le_one]


/-- A radial primitive is as smooth as its integrand near its base
radius. The interval is allowed to point in either direction. -/
theorem contDiffAt_radialPrimitive
    {n : ℕ∞} {a b r θ : ℝ} (hr : r ∈ Ioo a b)
    {H : ℝ × ℝ → ℝ}
    (hH : ∀ p : ℝ × ℝ, p.1 ∈ Ioo a b → ContDiffAt ℝ n H p) :
    ContDiffAt ℝ n (fun p : ℝ × ℝ => ∫ s in r..p.1, H (s, p.2)) (r, θ) := by
  let δ : ℝ := min (r - a) (b - r) / 4
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)) (by norm_num)
  have hleft : 4 * δ ≤ r - a := by
    dsimp only [δ]
    linarith [min_le_left (r - a) (b - r)]
  have hright : 4 * δ ≤ b - r := by
    dsimp only [δ]
    linarith [min_le_right (r - a) (b - r)]
  let U : Set (ℝ × ℝ) := Ioo (r - δ) (r + δ) ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  let K : (ℝ × ℝ) × ℝ → ℝ := fun q => H (r + (q.1.1 - r) * q.2, q.1.2)
  have hK : ∀ p ∈ U, ∀ t : ℝ, |t| < 3 → ContDiffAt ℝ n K (p, t) := by
    intro p hp t ht
    have hpabs : |p.1 - r| < δ := abs_lt.mpr ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
    have hprod : |(p.1 - r) * t| < 3 * δ := by
      rw [abs_mul, mul_comm]
      exact (mul_le_mul_of_nonneg_right ht.le (abs_nonneg _)).trans_lt
        (mul_lt_mul_of_pos_left hpabs (by norm_num))
    have hinside : r + (p.1 - r) * t ∈ Ioo a b := by
      obtain ⟨hl, hu⟩ := abs_lt.mp hprod
      exact ⟨by linarith, by linarith⟩
    have harg : ContDiffAt ℝ n
        (fun q : (ℝ × ℝ) × ℝ => (r + (q.1.1 - r) * q.2, q.1.2)) (p, t) :=
      (contDiffAt_const.add ((contDiffAt_fst.fst.sub contDiffAt_const).mul
        contDiffAt_snd)).prodMk contDiffAt_fst.snd
    exact (hH (r + (p.1 - r) * t, p.2) hinside).comp (p, t) harg
  have hp : (r, θ) ∈ U := ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
  have hI := (contDiffOn_compactParameterIntegral hU hK).contDiffAt (hU.mem_nhds hp)
  have hJ : ContDiffAt ℝ n
      (fun p : ℝ × ℝ => (p.1 - r) * ∫ t in (0 : ℝ)..1,
        H (r + (p.1 - r) * t, p.2)) (r, θ) :=
    (contDiffAt_fst.sub contDiffAt_const).mul hI
  apply hJ.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro p
  have hscale := intervalIntegral.smul_integral_comp_add_mul
    (fun s => H (s, p.2)) (a := (0 : ℝ)) (b := 1) (p.1 - r) r
  have hlast : r + (p.1 - r) = p.1 := by ring
  simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, hlast] using hscale.symm


/-- Local form on an arbitrary open subset of the plane. This is the
version used at a point of the strictly hyperbolic flow region. -/
theorem contDiffAt_radialPrimitive_of_isOpen
    {n : ℕ∞} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {p : ℝ × ℝ} (hp : p ∈ U)
    {H : ℝ × ℝ → ℝ} (hH : ContDiffOn ℝ n H U) :
    ContDiffAt ℝ n (fun q : ℝ × ℝ => ∫ s in p.1..q.1, H (s, q.2)) p := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let V : Set (ℝ × ℝ) := ball p (ε / 4)
  let K : (ℝ × ℝ) × ℝ → ℝ :=
    fun q => H (p.1 + (q.1.1 - p.1) * q.2, q.1.2)
  have hK : ∀ q ∈ V, ∀ t : ℝ, |t| < 3 → ContDiffAt ℝ n K (q, t) := by
    intro q hq t ht
    have hd : |q.1 - p.1| < ε / 4 ∧ |q.2 - p.2| < ε / 4 := by
      simpa only [V, mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff] using hq
    have hprod : |(q.1 - p.1) * t| < 3 * (ε / 4) := by
      rw [abs_mul, mul_comm]
      exact (mul_le_mul_of_nonneg_right ht.le (abs_nonneg _)).trans_lt
        (mul_lt_mul_of_pos_left hd.1 (by norm_num))
    have hinside : (p.1 + (q.1 - p.1) * t, q.2) ∈ U := by
      apply hball
      rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
      constructor
      · have heq : p.1 + (q.1 - p.1) * t - p.1 = (q.1 - p.1) * t := by ring
        rw [heq]
        linarith
      · linarith [hd.2]
    have harg : ContDiffAt ℝ n
        (fun y : (ℝ × ℝ) × ℝ => (p.1 + (y.1.1 - p.1) * y.2, y.1.2)) (q, t) :=
      (contDiffAt_const.add ((contDiffAt_fst.fst.sub contDiffAt_const).mul
        contDiffAt_snd)).prodMk contDiffAt_fst.snd
    exact (hH.contDiffAt (hU.mem_nhds hinside)).comp (q, t) harg
  have hpV : p ∈ V := mem_ball_self (by positivity)
  have hI := (contDiffOn_compactParameterIntegral isOpen_ball hK).contDiffAt
    (isOpen_ball.mem_nhds hpV)
  have hJ : ContDiffAt ℝ n
      (fun q : ℝ × ℝ => (q.1 - p.1) * ∫ t in (0 : ℝ)..1,
        H (p.1 + (q.1 - p.1) * t, q.2)) p :=
    (contDiffAt_fst.sub contDiffAt_const).mul hI
  apply hJ.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro q
  have hscale := intervalIntegral.smul_integral_comp_add_mul
    (fun s => H (s, q.2)) (a := (0 : ℝ)) (b := 1) (q.1 - p.1) p.1
  have hlast : p.1 + (q.1 - p.1) = q.1 := by ring
  simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, hlast] using hscale.symm

end ContinuousFlexibility.Analysis
