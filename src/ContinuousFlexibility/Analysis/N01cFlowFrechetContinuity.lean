module

public import ContinuousFlexibility.Analysis.N01cFlowFrechetParameters

/-!
# Finite-dimensional parameter continuity from the actual scalar time ODE

The speed's genuine parameter Fréchet derivative has an operator-norm
bound on a compact parameter ball, a compact time interval and one angular
period.  Integrating along the actual parameter segment bounds the speed
difference.  The already proved two-speed trajectory estimate then gives
local parameter Lipschitz continuity uniformly in time.

Consequently the smooth finite-dimensional parameter conclusion now
requires only the actual classical trajectories, their fixed initial
value, and a jointly smooth periodic speed.  Joint continuity and all
parameter derivatives of the trajectory family are conclusions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

set_option backward.isDefEq.respectTransparency false

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual operator-norm bound along a parameter segment controls
the actual difference of the two speeds. -/
theorem circleVectorSpeed_parameter_difference_bound
    {G : E × PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    (q₀ q : E) (p : PolarPoint) {N : ℝ}
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖circleVectorSpeedParameterDeriv G (q₀ + s • (q - q₀), p)‖ ≤ N) :
    |G (q, p) - G (q₀, p)| ≤ N * ‖q - q₀‖ := by
  have hi := circleSpeed_parameter_difference_bound
    (contDiff_circleVectorSpeedLine hG q₀ (q - q₀))
    (c := 0) (d := 1) (q₀ := 0) (q := 1)
    (N := N * ‖q - q₀‖)
    (by constructor <;> norm_num) (by constructor <;> norm_num) p
    (fun s hs => by
      rw [circleVectorSpeedLine_parameterDeriv hG]
      have hb : ‖circleVectorSpeedParameterDeriv G
          (q₀ + s • (q - q₀), p) (q - q₀)‖ ≤ N * ‖q - q₀‖ :=
        ((circleVectorSpeedParameterDeriv G
          (q₀ + s • (q - q₀), p)).le_opNorm (q - q₀)).trans
          (mul_le_mul_of_nonneg_right (hbound s hs) (norm_nonneg _))
      simpa only [Real.norm_eq_abs] using hb)
  have hend : q₀ + (q - q₀) = q := by abel
  simpa only [circleVectorSpeedLine, zero_smul, one_smul, add_zero,
    hend, sub_zero, abs_one, mul_one] using hi

/-- The classical time equations imply a local vector-parameter
Lipschitz bound, uniformly up to the two time endpoints. -/
theorem circleVectorTrajectory_local_lipschitz_bound
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ}
    {a b θ₀ M N t : ℝ} {q₀ q : E} (hG : ContDiff ℝ ∞ G)
    (htime : ∀ ρ : E, ContinuousOn (fun r => Θ (ρ, r)) (Icc a b))
    (hinit : ∀ ρ : E, Θ (ρ, a) = θ₀)
    (hflow : ∀ ρ : E, ∀ r ∈ Ioo a b,
      HasDerivAt (fun s => Θ (ρ, s)) (G (ρ, (r, Θ (ρ, r)))) r)
    (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hangle : ∀ r ∈ Icc a b, ∀ θ : ℝ,
      |angularPartial (fun p => G (q₀, p)) (r, θ)| ≤ M)
    (hparameter : ∀ s ∈ Icc (0 : ℝ) 1, ∀ r ∈ Icc a b, ∀ θ : ℝ,
      ‖circleVectorSpeedParameterDeriv G (q₀ + s • (q - q₀), (r, θ))‖ ≤ N)
    (ht : t ∈ Icc a b) :
    |Θ (q, t) - Θ (q₀, t)| ≤
      (((b - a) * Real.exp ((b - a) * M) ^ 2) * N) * ‖q - q₀‖ := by
  have hGq : ContDiff ℝ ∞ (fun p : PolarPoint => G (q, p)) :=
    hG.comp (contDiff_const.prodMk contDiff_id)
  have hG₀ : ContDiff ℝ ∞ (fun p : PolarPoint => G (q₀, p)) :=
    hG.comp (contDiff_const.prodMk contDiff_id)
  have hspeed (r : ℝ) (hr : r ∈ Icc a t) (θ : ℝ) :
      |G (q, (r, θ)) - G (q₀, (r, θ))| ≤ N * ‖q - q₀‖ :=
    circleVectorSpeed_parameter_difference_bound hG q₀ q (r, θ)
      (fun s hs => hparameter s hs r ⟨hr.1, hr.2.trans ht.2⟩ θ)
  have he := circleTrajectory_twoSpeeds_difference_bound ht.1 hGq hG₀
    ((htime q).mono (Icc_subset_Icc le_rfl ht.2))
    ((htime q₀).mono (Icc_subset_Icc le_rfl ht.2))
    (fun r hr => hflow q r ⟨hr.1, hr.2.trans_le ht.2⟩)
    (fun r hr => hflow q₀ r ⟨hr.1, hr.2.trans_le ht.2⟩)
    ((hinit q).trans (hinit q₀).symm) hM (mul_nonneg hN (norm_nonneg _))
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
        ((t - a) * Real.exp ((t - a) * M) ^ 2) * (N * ‖q - q₀‖) := he
    _ ≤ ((b - a) * Real.exp ((b - a) * M) ^ 2) * (N * ‖q - q₀‖) :=
      mul_le_mul_of_nonneg_right hC (mul_nonneg hN (norm_nonneg _))
    _ = (((b - a) * Real.exp ((b - a) * M) ^ 2) * N) * ‖q - q₀‖ := by ring

/-- The actual parameter derivative of a periodic speed has a uniform
operator-norm bound on a compact parameter and time strip. -/
theorem exists_circleVectorSpeedParameterDeriv_bound
    {G : E × PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    {P : ℝ} (hP : 0 < P)
    (hperiod : ∀ q : E, ∀ t : ℝ, Function.Periodic (fun θ => G (q, (t, θ))) P)
    {K : Set E} (hK : IsCompact K) (a b : ℝ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ q ∈ K, ∀ t ∈ Icc a b, ∀ θ : ℝ,
      ‖circleVectorSpeedParameterDeriv G (q, (t, θ))‖ ≤ N := by
  have hd (q : E) (p : PolarPoint) :
      HasFDerivAt (fun ρ : E => G (ρ, p))
        (circleVectorSpeedParameterDeriv G (q, p)) q :=
    (hG.differentiable (by simp) (q, p)).hasFDerivAt.comp q
      (hasFDerivAt_prodMk_left q p)
  have hp (q : E) (t : ℝ) :
      Function.Periodic (fun θ => circleVectorSpeedParameterDeriv G (q, (t, θ))) P := by
    intro θ
    have he : (fun ρ : E => G (ρ, (t, θ + P))) =
        fun ρ : E => G (ρ, (t, θ)) := funext (fun ρ => hperiod ρ t θ)
    calc
      circleVectorSpeedParameterDeriv G (q, (t, θ + P)) =
          fderiv ℝ (fun ρ : E => G (ρ, (t, θ + P))) q := (hd q (t, θ + P)).fderiv.symm
      _ = fderiv ℝ (fun ρ : E => G (ρ, (t, θ))) q := by rw [he]
      _ = circleVectorSpeedParameterDeriv G (q, (t, θ)) := (hd q (t, θ)).fderiv
  obtain ⟨N, hN⟩ :=
    (hK.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
      (s := K ×ˢ (Icc a b ×ˢ Icc (0 : ℝ) P))
      (contDiff_circleVectorSpeedParameterDeriv hG).continuous.continuousOn
  refine ⟨max 0 N, le_max_left _ _, ?_⟩
  intro q hq t ht θ
  obtain ⟨η, hη, he⟩ := (hp q t).exists_mem_Ico₀ hP θ
  rw [he]
  exact (hN (q, (t, η)) ⟨hq, ht, ⟨hη.1, hη.2.le⟩⟩).trans (le_max_right _ _)

/-- Individual classical time trajectories of a smooth periodic
finite-dimensional speed family are jointly continuous. -/
theorem circleVectorTrajectory_continuousOn
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {a b θ₀ P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ q : E, ∀ t : ℝ, Function.Periodic (fun θ => G (q, (t, θ))) P)
    (htime : ∀ q : E, ContinuousOn (fun r => Θ (q, r)) (Icc a b))
    (hinit : ∀ q : E, Θ (q, a) = θ₀)
    (hflow : ∀ q : E, ∀ t ∈ Ioo a b,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t) :
    ContinuousOn Θ ((univ : Set E) ×ˢ Icc a b) := by
  intro p hp
  have hab : a ≤ b := hp.2.1.trans hp.2.2
  have hG₀ : ContDiff ℝ ∞ (fun x : PolarPoint => G (p.1, x)) :=
    hG.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨M, hM, hangle⟩ :=
    exists_circleSpeed_angular_bound hG₀ hP (hperiod p.1) a b
  obtain ⟨N, hN, hparameter⟩ := exists_circleVectorSpeedParameterDeriv_bound
    hG hP hperiod (isCompact_closedBall p.1 1) a b
  let K : ℝ := 1 + ((b - a) * Real.exp ((b - a) * M) ^ 2) * N
  have hC : 0 ≤ ((b - a) * Real.exp ((b - a) * M) ^ 2) * N :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg _)) hN
  have hK : 0 < K := by dsimp only [K]; linarith
  have hsegment (q : E) (hq : dist q p.1 ≤ 1) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      p.1 + s • (q - p.1) ∈ Metric.closedBall p.1 1 := by
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm]
    have he : p.1 + s • (q - p.1) - p.1 = s • (q - p.1) := by abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    have hq' : ‖q - p.1‖ ≤ 1 := by simpa only [dist_eq_norm] using hq
    exact (mul_le_mul_of_nonneg_left hq' hs.1).trans (by simpa only [mul_one] using hs.2)
  have hbound (q : E) (hq : dist q p.1 ≤ 1)
      (t : ℝ) (ht : t ∈ Icc a b) :
      |Θ (q, t) - Θ (p.1, t)| ≤ K * ‖q - p.1‖ := by
    have h := circleVectorTrajectory_local_lipschitz_bound (q₀ := p.1) (q := q)
      hG htime hinit hflow
      hM hN hangle
      (fun s hs r hr θ => hparameter _ (hsegment q hq s hs) r hr θ) ht
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
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
  have hqparameter : dist q.1 p.1 ≤ 1 :=
    (hparameter_dist.trans_le (min_le_left _ _)).le
  have htime_dist : dist q.2 p.2 < δ :=
    hsecond.trans_lt (hdist.trans_le (min_le_left _ _))
  have hparameter_small : K * ‖q.1 - p.1‖ < ε / 2 := by
    have hh : dist q.1 p.1 < ε / 2 / K :=
      hparameter_dist.trans_le (min_le_right _ _)
    rw [dist_eq_norm] at hh
    simpa only [mul_comm] using (lt_div_iff₀ hK).mp hh
  have htime_small := htime' hq.2 htime_dist
  calc
    dist (Θ q) (Θ p) ≤ dist (Θ q) (Θ (p.1, q.2)) +
        dist (Θ (p.1, q.2)) (Θ p) := dist_triangle _ _ _
    _ ≤ K * ‖q.1 - p.1‖ + dist (Θ (p.1, q.2)) (Θ p) :=
      add_le_add
        (by simpa only [Real.dist_eq] using hbound q.1 hqparameter q.2 hq.2) le_rfl
    _ < ε := by linarith

/-- Genuine all-order finite-dimensional parameter dependence of a
supplied classical periodic trajectory at every closed-interval time.
No parameter continuity or derivative of the family is a premise. -/
theorem circleVectorTrajectory_contDiff_parameter_of_classical
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {a b θ₀ P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ q : E, ∀ t : ℝ, Function.Periodic (fun θ => G (q, (t, θ))) P)
    (htime : ∀ q : E, ContinuousOn (fun r => Θ (q, r)) (Icc a b))
    (hinit : ∀ q : E, Θ (q, a) = θ₀)
    (hflow : ∀ q : E, ∀ t ∈ Ioo a b,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ ∞ (fun q => Θ (q, t)) :=
  circleVectorTrajectory_contDiff_parameter hG
    (circleVectorTrajectory_continuousOn hG hP hperiod htime hinit hflow) hinit hflow ht

end ContinuousFlexibility.Analysis
