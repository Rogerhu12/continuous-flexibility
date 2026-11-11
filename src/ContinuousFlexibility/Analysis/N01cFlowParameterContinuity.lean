import ContinuousFlexibility.Analysis.N01cFlowVariation
import ContinuousFlexibility.Analysis.OneHighCircleFlowContinuity

/-!
# Parameter continuity obtained from the actual time ODE

The inhomogeneous integrating-factor formula bounds differences of trajectories
of two speeds.  The actual parameter derivative of a smooth periodic speed is
bounded on each compact parameter and time strip, after reducing the angle to
one period.  These estimates prove local Lipschitz dependence on the speed
parameter and joint continuity from individual continuous time trajectories.

The final theorem derives the true first parameter derivative without assuming
joint continuity or any parameter derivative of the flow.  The constants here
are ordinary compact bounds; obtaining the N01 coefficient-power and
one-high-factor estimates still requires the geometric speed bounds and root
regularization.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

set_option backward.isDefEq.respectTransparency false

/-- A true inhomogeneous scalar ODE with zero initial value is bounded by
its forcing.  The exponential constant is obtained from the integrating
factor and does not assume a variational equation for another family. -/
theorem scalar_inhomogeneousODE_abs_bound
    {κ F y : ℝ → ℝ} {a b M N : ℝ} (hab : a ≤ b)
    (hκ : ContinuousOn κ (Icc a b)) (hF : ContinuousOn F (Icc a b))
    (hy : ContinuousOn y (Icc a b))
    (hdy : ∀ t ∈ Ioo a b, HasDerivAt y (κ t * y t + F t) t)
    (hya : y a = 0) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hκbound : ∀ t ∈ Icc a b, |κ t| ≤ M)
    (hFbound : ∀ t ∈ Icc a b, |F t| ≤ N) :
    |y b| ≤ ((b - a) * Real.exp ((b - a) * M) ^ 2) * N := by
  have hI (t : ℝ) (ht : t ∈ Icc a b) :
      |∫ r in a..t, κ r| ≤ (b - a) * M := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := t) (C := M) (f := κ) (fun r hr => by
        have hr' : r ∈ Icc a t := by
          simpa only [uIcc_of_le ht.1] using uIoc_subset_uIcc hr
        simpa only [Real.norm_eq_abs] using hκbound r ⟨hr'.1, hr'.2.trans ht.2⟩)
    have hi' : |∫ r in a..t, κ r| ≤ M * (t - a) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.1)] using hi
    calc
      |∫ r in a..t, κ r| ≤ M * (t - a) := hi'
      _ ≤ M * (b - a) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hM
      _ = (b - a) * M := mul_comm _ _
  have hEb : Real.exp (∫ r in a..b, κ r) ≤ Real.exp ((b - a) * M) :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (hI b ⟨hab, le_rfl⟩))
  have hEt (t : ℝ) (ht : t ∈ Icc a b) :
      Real.exp (-(∫ r in a..t, κ r)) ≤ Real.exp ((b - a) * M) :=
    Real.exp_le_exp.mpr ((neg_le_abs _).trans (hI t ht))
  have hJ₀ := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := Real.exp ((b - a) * M) * N)
    (f := fun t => Real.exp (-(∫ r in a..t, κ r)) * F t) (fun t ht => by
      have ht' : t ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hEt t ht') (hFbound t ht')
        (abs_nonneg _) (Real.exp_pos _).le)
  have hJ : |∫ t in a..b, Real.exp (-(∫ r in a..t, κ r)) * F t| ≤
      (Real.exp ((b - a) * M) * N) * (b - a) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hJ₀
  have he := scalar_inhomogeneousODE_eq_exp_mul hab hκ hF hy hdy
  rw [hya, zero_add] at he
  calc
    |y b| = Real.exp (∫ r in a..b, κ r) *
        |∫ t in a..b, Real.exp (-(∫ r in a..t, κ r)) * F t| := by
      rw [he, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp ((b - a) * M) *
        ((Real.exp ((b - a) * M) * N) * (b - a)) :=
      mul_le_mul hEb hJ (abs_nonneg _) (Real.exp_pos _).le
    _ = ((b - a) * Real.exp ((b - a) * M) ^ 2) * N := by ring

/-- A speed perturbation bound controls the difference of two true time
trajectories with the same initial value. -/
theorem circleTrajectory_twoSpeeds_difference_bound
    {G H : PolarPoint → ℝ} {u v : ℝ → ℝ} {a b M N : ℝ}
    (hab : a ≤ b) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Ioo a b, HasDerivAt u (G (t, u t)) t)
    (hdv : ∀ t ∈ Ioo a b, HasDerivAt v (H (t, v t)) t)
    (ha : u a = v a) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hangle : ∀ t ∈ Icc a b, ∀ θ : ℝ, |angularPartial H (t, θ)| ≤ M)
    (hspeed : ∀ t ∈ Icc a b, ∀ θ : ℝ, |G (t, θ) - H (t, θ)| ≤ N) :
    |u b - v b| ≤ ((b - a) * Real.exp ((b - a) * M) ^ 2) * N := by
  have hκ : ContinuousOn
      (fun t => circleSpeedSecant H (t, (v t, u t))) (Icc a b) :=
    (contDiff_circleSpeedSecant hH).continuous.comp_continuousOn
      (continuousOn_id.prodMk (hv.prodMk hu))
  have hF : ContinuousOn (fun t => G (t, u t) - H (t, u t)) (Icc a b) :=
    (hG.continuous.comp_continuousOn (continuousOn_id.prodMk hu)).sub
      (hH.continuous.comp_continuousOn (continuousOn_id.prodMk hu))
  have hdy (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun r => u r - v r)
        (circleSpeedSecant H (t, (v t, u t)) * (u t - v t) +
          (G (t, u t) - H (t, u t))) t := by
    apply ((hdu t ht).sub (hdv t ht)).congr_deriv
    have hsec := circleSpeed_sub_eq_secant hH t (v t) (u t)
    linarith
  exact scalar_inhomogeneousODE_abs_bound hab hκ hF (hu.sub hv) hdy
    (sub_eq_zero.mpr ha) hM hN
    (fun t ht => circleSpeedSecant_abs_le hH (hangle t ht) _ _)
    (fun t ht => hspeed t ht (u t))

/-- The actual derivative bound on a parameter interval controls the
actual speed difference, by the fundamental theorem of calculus. -/
theorem circleSpeed_parameter_difference_bound
    {G : ℝ × PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    {c d q₀ q N : ℝ} (hq₀ : q₀ ∈ Icc c d) (hq : q ∈ Icc c d)
    (p : PolarPoint)
    (hbound : ∀ ρ ∈ Icc c d, |circleSpeedParameterDeriv G (ρ, p)| ≤ N) :
    |G (q, p) - G (q₀, p)| ≤ N * |q - q₀| := by
  have hc : Continuous (fun ρ : ℝ => circleSpeedParameterDeriv G (ρ, p)) :=
    (contDiff_circleSpeedParameterDeriv hG).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hint : (∫ ρ in q₀..q, circleSpeedParameterDeriv G (ρ, p)) =
      G (q, p) - G (q₀, p) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun ρ _ => hasDerivAt_circleSpeed_parameterSlice hG ρ p)
      (hc.intervalIntegrable q₀ q)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := q₀) (b := q) (C := N)
    (f := fun ρ => circleSpeedParameterDeriv G (ρ, p)) (fun ρ hρ => by
      have hρ' := uIoc_subset_uIcc hρ
      have hmem : ρ ∈ Icc c d :=
        ⟨(le_min hq₀.1 hq.1).trans hρ'.1,
          hρ'.2.trans (max_le hq₀.2 hq.2)⟩
      simpa only [Real.norm_eq_abs] using hbound ρ hmem)
  simpa only [Real.norm_eq_abs, hint] using hi

/-- A local parameter Lipschitz estimate obtained from the time equations.
The angle bound is needed only for the fixed baseline speed. -/
theorem circleParameterTrajectory_local_lipschitz_bound
    {G : ℝ × PolarPoint → ℝ} {Θ : PolarPoint → ℝ}
    {a b c d θ₀ M N q₀ q t : ℝ} (hG : ContDiff ℝ ∞ G)
    (htime : ∀ ρ : ℝ, ContinuousOn (fun r => Θ (ρ, r)) (Icc a b))
    (hinit : ∀ ρ : ℝ, Θ (ρ, a) = θ₀)
    (hflow : ∀ ρ : ℝ, ∀ r ∈ Ioo a b,
      HasDerivAt (fun s => Θ (ρ, s)) (G (ρ, (r, Θ (ρ, r)))) r)
    (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hangle : ∀ r ∈ Icc a b, ∀ θ : ℝ,
      |angularPartial (fun p => G (q₀, p)) (r, θ)| ≤ M)
    (hparameter : ∀ ρ ∈ Icc c d, ∀ r ∈ Icc a b, ∀ θ : ℝ,
      |circleSpeedParameterDeriv G (ρ, (r, θ))| ≤ N)
    (hq₀ : q₀ ∈ Icc c d) (hq : q ∈ Icc c d) (ht : t ∈ Icc a b) :
    |Θ (q, t) - Θ (q₀, t)| ≤
      (((b - a) * Real.exp ((b - a) * M) ^ 2) * N) * |q - q₀| := by
  have hGq : ContDiff ℝ ∞ (fun p : PolarPoint => G (q, p)) :=
    hG.comp (contDiff_const.prodMk contDiff_id)
  have hG₀ : ContDiff ℝ ∞ (fun p : PolarPoint => G (q₀, p)) :=
    hG.comp (contDiff_const.prodMk contDiff_id)
  have hspeed (r : ℝ) (hr : r ∈ Icc a t) (θ : ℝ) :
      |G (q, (r, θ)) - G (q₀, (r, θ))| ≤ N * |q - q₀| :=
    circleSpeed_parameter_difference_bound hG hq₀ hq (r, θ)
      (fun ρ hρ => hparameter ρ hρ r ⟨hr.1, hr.2.trans ht.2⟩ θ)
  have he := circleTrajectory_twoSpeeds_difference_bound ht.1 hGq hG₀
    ((htime q).mono (Icc_subset_Icc le_rfl ht.2))
    ((htime q₀).mono (Icc_subset_Icc le_rfl ht.2))
    (fun r hr => hflow q r ⟨hr.1, hr.2.trans_le ht.2⟩)
    (fun r hr => hflow q₀ r ⟨hr.1, hr.2.trans_le ht.2⟩)
    ((hinit q).trans (hinit q₀).symm) hM (mul_nonneg hN (abs_nonneg _))
    (fun r hr => hangle r ⟨hr.1, hr.2.trans ht.2⟩) hspeed
  have hE : Real.exp ((t - a) * M) ≤ Real.exp ((b - a) * M) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (sub_le_sub_right ht.2 a) hM)
  have hE₂ : Real.exp ((t - a) * M) ^ 2 ≤ Real.exp ((b - a) * M) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hE hE (Real.exp_pos _).le (Real.exp_pos _).le
  have hC : (t - a) * Real.exp ((t - a) * M) ^ 2 ≤
      (b - a) * Real.exp ((b - a) * M) ^ 2 :=
    mul_le_mul (sub_le_sub_right ht.2 a) hE₂ (sq_nonneg _)
      (sub_nonneg.mpr (ht.1.trans ht.2))
  calc
    |Θ (q, t) - Θ (q₀, t)| ≤
        ((t - a) * Real.exp ((t - a) * M) ^ 2) * (N * |q - q₀|) := he
    _ ≤ ((b - a) * Real.exp ((b - a) * M) ^ 2) * (N * |q - q₀|) :=
      mul_le_mul_of_nonneg_right hC (mul_nonneg hN (abs_nonneg _))
    _ = (((b - a) * Real.exp ((b - a) * M) ^ 2) * N) * |q - q₀| := by ring

/-- Periodicity and smoothness provide a uniform bound for the actual
parameter derivative on every compact parameter and time strip. -/
theorem exists_circleSpeedParameterDeriv_bound
    {G : ℝ × PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    {P : ℝ} (hP : 0 < P)
    (hperiod : ∀ q t : ℝ, Function.Periodic (fun θ => G (q, (t, θ))) P)
    (c d a b : ℝ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ q ∈ Icc c d, ∀ t ∈ Icc a b, ∀ θ : ℝ,
      |circleSpeedParameterDeriv G (q, (t, θ))| ≤ N := by
  have hp (q t : ℝ) :
      Function.Periodic (fun θ => circleSpeedParameterDeriv G (q, (t, θ))) P := by
    intro θ
    have he : (fun ρ : ℝ => G (ρ, (t, θ + P))) =
        fun ρ : ℝ => G (ρ, (t, θ)) := funext (fun ρ => hperiod ρ t θ)
    calc
      circleSpeedParameterDeriv G (q, (t, θ + P)) =
          deriv (fun ρ : ℝ => G (ρ, (t, θ + P))) q :=
        (hasDerivAt_circleSpeed_parameterSlice hG q (t, θ + P)).deriv.symm
      _ = deriv (fun ρ : ℝ => G (ρ, (t, θ))) q := by rw [he]
      _ = circleSpeedParameterDeriv G (q, (t, θ)) :=
        (hasDerivAt_circleSpeed_parameterSlice hG q (t, θ)).deriv
  obtain ⟨N, hN⟩ :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
      (s := Icc c d ×ˢ (Icc a b ×ˢ Icc (0 : ℝ) P))
      (contDiff_circleSpeedParameterDeriv hG).continuous.continuousOn
  refine ⟨max 0 N, le_max_left _ _, ?_⟩
  intro q hq t ht θ
  obtain ⟨η, hη, he⟩ := (hp q t).exists_mem_Ico₀ hP θ
  rw [he]
  have hm : |circleSpeedParameterDeriv G (q, (t, η))| ≤ N := by
    simpa only [Real.norm_eq_abs] using hN (q, (t, η)) ⟨hq, ht, ⟨hη.1, hη.2.le⟩⟩
  exact hm.trans (le_max_right _ _)

/-- Individual classical time solutions for a smooth periodic parameter
family are jointly continuous.  No parameter continuity of the supplied
trajectory family is assumed. -/
theorem circleParameterTrajectory_continuousOn
    {G : ℝ × PolarPoint → ℝ} {Θ : PolarPoint → ℝ} {a b θ₀ P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ q t : ℝ, Function.Periodic (fun θ => G (q, (t, θ))) P)
    (htime : ∀ q : ℝ, ContinuousOn (fun r => Θ (q, r)) (Icc a b))
    (hinit : ∀ q : ℝ, Θ (q, a) = θ₀)
    (hflow : ∀ q : ℝ, ∀ t ∈ Ioo a b,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t) :
    ContinuousOn Θ ((univ : Set ℝ) ×ˢ Icc a b) := by
  intro p hp
  have hab : a ≤ b := hp.2.1.trans hp.2.2
  have hG₀ : ContDiff ℝ ∞ (fun x : PolarPoint => G (p.1, x)) :=
    hG.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨M, hM, hangle⟩ :=
    exists_circleSpeed_angular_bound hG₀ hP (hperiod p.1) a b
  obtain ⟨N, hN, hparameter⟩ :=
    exists_circleSpeedParameterDeriv_bound hG hP hperiod (p.1 - 1) (p.1 + 1) a b
  let K : ℝ := 1 + ((b - a) * Real.exp ((b - a) * M) ^ 2) * N
  have hC : 0 ≤ ((b - a) * Real.exp ((b - a) * M) ^ 2) * N :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg _)) hN
  have hK : 0 < K := by dsimp only [K]; linarith
  have hbase : p.1 ∈ Icc (p.1 - 1) (p.1 + 1) := by
    constructor <;> linarith
  have hbound (q : ℝ) (hq : q ∈ Icc (p.1 - 1) (p.1 + 1))
      (t : ℝ) (ht : t ∈ Icc a b) :
      |Θ (q, t) - Θ (p.1, t)| ≤ K * |q - p.1| := by
    have h := circleParameterTrajectory_local_lipschitz_bound hG htime hinit hflow
      hM hN hangle hparameter hbase hq ht
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    dsimp only [K]
    linarith
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, htime'⟩ :=
    Metric.continuousWithinAt_iff.mp (htime p.1 p.2 hp.2) (ε / 2) (half_pos hε)
  refine ⟨min δ (min 1 (ε / 2 / K)),
    lt_min hδ (lt_min zero_lt_one (div_pos (half_pos hε) hK)), ?_⟩
  intro q hq hdist
  have hfirst : dist q.1 p.1 ≤ dist q p := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hsecond : dist q.2 p.2 ≤ dist q p := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hparameter_dist : dist q.1 p.1 < min 1 (ε / 2 / K) :=
    hfirst.trans_lt (hdist.trans_le (min_le_right _ _))
  have hparameter_one : |q.1 - p.1| < 1 := by
    simpa only [Real.dist_eq] using hparameter_dist.trans_le (min_le_left _ _)
  have hqparameter : q.1 ∈ Icc (p.1 - 1) (p.1 + 1) := by
    have hh := abs_lt.mp hparameter_one
    constructor <;> linarith
  have htime_dist : dist q.2 p.2 < δ :=
    hsecond.trans_lt (hdist.trans_le (min_le_left _ _))
  have hparameter_small : K * |q.1 - p.1| < ε / 2 := by
    have hh : dist q.1 p.1 < ε / 2 / K :=
      hparameter_dist.trans_le (min_le_right _ _)
    rw [Real.dist_eq] at hh
    simpa only [mul_comm] using (lt_div_iff₀ hK).mp hh
  have htime_small := htime' hq.2 htime_dist
  calc
    dist (Θ q) (Θ p) ≤ dist (Θ q) (Θ (p.1, q.2)) +
        dist (Θ (p.1, q.2)) (Θ p) := dist_triangle _ _ _
    _ ≤ K * |q.1 - p.1| + dist (Θ (p.1, q.2)) (Θ p) := by
      apply add_le_add_right
      simpa only [Real.dist_eq] using hbound q.1 hqparameter q.2 hq.2
    _ < ε := by linarith

/-- The genuine first parameter variation of a classical periodic
trajectory family.  Both joint continuity and the parameter derivative
are conclusions of the actual time equations. -/
theorem circleParameterTrajectory_hasDerivAt_parameter
    {G : ℝ × PolarPoint → ℝ} {Θ : PolarPoint → ℝ} {a b θ₀ P : ℝ}
    (hab : a ≤ b) (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ q t : ℝ, Function.Periodic (fun θ => G (q, (t, θ))) P)
    (htime : ∀ q : ℝ, ContinuousOn (fun r => Θ (q, r)) (Icc a b))
    (hinit : ∀ q : ℝ, Θ (q, a) = θ₀)
    (hflow : ∀ q : ℝ, ∀ t ∈ Ioo a b,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    (q₀ : ℝ) :
    HasDerivAt (fun q => Θ (q, b))
      (Real.exp (∫ t in a..b,
          angularPartial (fun p => G (q₀, p)) (t, Θ (q₀, t))) *
        ∫ t in a..b,
          Real.exp (-(∫ r in a..t,
            angularPartial (fun p => G (q₀, p)) (r, Θ (q₀, r)))) *
              circleSpeedParameterDeriv G (q₀, (t, Θ (q₀, t)))) q₀ :=
  continuousCircleTrajectory_hasDerivAt_parameter hab hG
    (circleParameterTrajectory_continuousOn hG hP hperiod htime hinit hflow)
    hinit hflow q₀

end ContinuousFlexibility.Analysis
