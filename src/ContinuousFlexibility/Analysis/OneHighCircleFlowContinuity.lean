import ContinuousFlexibility.Analysis.OneHighCircleFlowVariational
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Continuity and the angular Jacobian of classical periodic flows

Periodicity bounds the speed's angular derivative on a compact time
strip. The exact difference formula gives a common Lipschitz constant in
the initial angle. Together with continuity of each time trajectory this
proves joint continuity, so the angular derivative is obtained from the
genuine flow equation without a regularity hypothesis on the family.
The angular period is an arbitrary positive real number.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem circleSpeedSecant_abs_le {G : PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    {t M : ℝ} (hbound : ∀ η : ℝ, |angularPartial G (t, η)| ≤ M) (x y : ℝ) :
    |circleSpeedSecant G (t, (x, y))| ≤ M := by
  have hc : Continuous (fun s : ℝ => angularPartial G (t, (y - x) * s + x)) :=
    (contDiff_cylinder_angularPartial hG).continuous.comp
      (continuous_const.prodMk ((continuous_const.mul continuous_id).add continuous_const))
  have hm := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (μ := volume)
    zero_le_one (hc.abs.intervalIntegrable 0 1) (intervalIntegrable_const (c := M))
    (fun s _ => hbound ((y - x) * s + x))
  have ha := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := fun s => angularPartial G (t, (y - x) * s + x)) zero_le_one
  simpa only [circleSpeedSecant, intervalIntegral.integral_const, sub_zero,
    one_smul] using ha.trans hm

theorem exists_circleSpeed_angular_bound {G : PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    {P : ℝ} (hP : 0 < P) (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc a b, ∀ θ : ℝ, |angularPartial G (t, θ)| ≤ M := by
  have hp (t : ℝ) : Function.Periodic (fun θ => angularPartial G (t, θ)) P := by
    intro θ
    have he : (fun η => G (t, η + P)) = fun η => G (t, η) := funext (hperiod t)
    calc
      angularPartial G (t, θ + P) = deriv (fun η => G (t, η)) (θ + P) :=
        (deriv_cylinder_angular_slice (hG.differentiable (by simp)) t (θ + P)).symm
      _ = deriv (fun η => G (t, η + P)) θ :=
        (deriv_comp_add_const (fun η => G (t, η)) P θ).symm
      _ = deriv (fun η => G (t, η)) θ := by rw [he]
      _ = angularPartial G (t, θ) :=
        deriv_cylinder_angular_slice (hG.differentiable (by simp)) t θ
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc a b ×ˢ Icc (0 : ℝ) P)
    (contDiff_cylinder_angularPartial hG).continuous.continuousOn
  refine ⟨max 0 M, le_max_left _ _, ?_⟩
  intro t ht θ
  obtain ⟨η, hη, he⟩ := (hp t).exists_mem_Ico₀ hP θ
  rw [he]
  have hm : |angularPartial G (t, η)| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM (t, η) ⟨ht, ⟨hη.1, hη.2.le⟩⟩
  exact hm.trans (le_max_right _ _)

/-- Uniform Lipschitz dependence follows from the genuine time equation,
before any initial-angle derivative has been constructed. -/
theorem circleFlow_angle_lipschitz_bound {G Θ : PolarPoint → ℝ} {a b M : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    (hM : 0 ≤ M) (hbound : ∀ r ∈ Icc a b, ∀ η : ℝ, |angularPartial G (r, η)| ≤ M)
    {t : ℝ} (ht : t ∈ Icc a b) (η θ : ℝ) :
    |Θ (t, η) - Θ (t, θ)| ≤ Real.exp ((b - a) * M) * |η - θ| := by
  have htime (ξ : ℝ) : ContinuousOn (fun r => Θ (r, ξ)) (Icc a t) :=
    (hΘ ξ).mono (Icc_subset_Icc le_rfl ht.2)
  have hκ : ContinuousOn
      (fun r => circleSpeedSecant G (r, (Θ (r, θ), Θ (r, η)))) (Icc a t) :=
    (contDiff_circleSpeedSecant hG).continuous.comp_continuousOn
      (continuousOn_id.prodMk ((htime θ).prodMk (htime η)))
  have hI : (∫ r in a..t, circleSpeedSecant G (r, (Θ (r, θ), Θ (r, η)))) ≤
      (t - a) * M := by
    have hm := intervalIntegral.integral_mono_on (μ := volume) ht.1
      (hκ.intervalIntegrable_of_Icc ht.1) (intervalIntegrable_const (c := M))
      (fun r hr => (le_abs_self _).trans
        (circleSpeedSecant_abs_le hG (hbound r ⟨hr.1, hr.2.trans ht.2⟩) _ _))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
  have hlength : (t - a) * M ≤ (b - a) * M :=
    mul_le_mul_of_nonneg_right (sub_le_sub_right ht.2 a) hM
  have he := circleFlow_difference_eq_mul_exp ht.1 hG htime
    (fun r hr => hflow r ⟨hr.1, hr.2.trans_le ht.2⟩) η θ
  calc
    |Θ (t, η) - Θ (t, θ)| = |η - θ| *
        Real.exp (∫ r in a..t, circleSpeedSecant G (r, (Θ (r, θ), Θ (r, η)))) := by
      rw [he, hinit η, hinit θ, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ |η - θ| * Real.exp ((b - a) * M) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hI.trans hlength)) (abs_nonneg _)
    _ = Real.exp ((b - a) * M) * |η - θ| := mul_comm _ _

private theorem continuousOn_of_time_continuous_of_angle_bound
    {Θ : PolarPoint → ℝ} {a b K : ℝ} (hK : 0 < K)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun t => Θ (t, θ)) (Icc a b))
    (hbound : ∀ t ∈ Icc a b, ∀ η θ : ℝ, |Θ (t, η) - Θ (t, θ)| ≤ K * |η - θ|) :
    ContinuousOn Θ (Icc a b ×ˢ (univ : Set ℝ)) := by
  intro p hp
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, htime⟩ := Metric.continuousWithinAt_iff.mp (hΘ p.2 p.1 hp.1)
    (ε / 2) (half_pos hε)
  refine ⟨min δ (ε / 2 / K), lt_min hδ (div_pos (half_pos hε) hK), ?_⟩
  intro q hq hdist
  have ht : dist q.1 p.1 < δ := by
    have hfirst : dist q.1 p.1 ≤ dist q p := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    exact hfirst.trans_lt (hdist.trans_le (min_le_left _ _))
  have hθ : dist q.2 p.2 < ε / 2 / K := by
    have hsecond : dist q.2 p.2 ≤ dist q p := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    exact hsecond.trans_lt (hdist.trans_le (min_le_right _ _))
  have hangle : K * |q.2 - p.2| < ε / 2 := by
    rw [Real.dist_eq] at hθ
    have hh := (lt_div_iff₀ hK).mp hθ
    simpa only [mul_comm] using hh
  have htime' := htime hq.1 ht
  calc
    dist (Θ q) (Θ p) ≤ dist (Θ q) (Θ (q.1, p.2)) +
        dist (Θ (q.1, p.2)) (Θ p) := dist_triangle _ _ _
    _ ≤ K * |q.2 - p.2| + dist (Θ (q.1, p.2)) (Θ p) := by
      apply add_le_add_right
      simpa only [Real.dist_eq] using hbound q.1 hq.1 q.2 p.2
    _ < ε := by linarith

/-- Smooth periodic speed and individual classical time solutions imply
joint continuity of the whole flow on the closed strip. -/
theorem circleFlow_continuousOn {G Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t) :
    ContinuousOn Θ (Icc a b ×ˢ (univ : Set ℝ)) := by
  obtain ⟨M, hM, hbound⟩ := exists_circleSpeed_angular_bound hG hP hperiod a b
  exact continuousOn_of_time_continuous_of_angle_bound (Real.exp_pos _) hΘ
    (fun t ht η θ => circleFlow_angle_lipschitz_bound hG hΘ hinit hflow hM hbound ht η θ)

/-- The variational exponential for an actual classical periodic flow.
No joint continuity or angular regularity is an input. -/
theorem circleFlow_hasDerivAt_angle {G Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    HasDerivAt (fun η => Θ (t, η))
      (Real.exp (∫ r in a..t, angularPartial G (r, Θ (r, θ)))) θ :=
  continuousCircleFlow_hasDerivAt_angle hG
    (circleFlow_continuousOn hG hP hperiod hΘ hinit hflow) hinit hflow ht θ

theorem circleFlow_angle_strictMono {G Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) : StrictMono (fun θ => Θ (t, θ)) := by
  apply strictMono_of_deriv_pos
  intro θ
  rw [(circleFlow_hasDerivAt_angle hG hP hperiod hΘ hinit hflow ht θ).deriv]
  exact Real.exp_pos _

/-- The lift law follows from uniqueness of the actual scalar time
equation. It is not imposed as a condition on the flow family. -/
theorem circleFlow_lift_add {G Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) : Θ (t, θ + P) = Θ (t, θ) + P := by
  have hu : ContinuousOn (fun r => Θ (r, θ + P) - P) (Icc a t) :=
    ((hΘ (θ + P)).mono (Icc_subset_Icc le_rfl ht.2)).sub continuousOn_const
  have hv : ContinuousOn (fun r => Θ (r, θ)) (Icc a t) :=
    (hΘ θ).mono (Icc_subset_Icc le_rfl ht.2)
  have hdu (r : ℝ) (hr : r ∈ Ioo a t) :
      HasDerivAt (fun r => Θ (r, θ + P) - P) (G (r, Θ (r, θ + P) - P)) r := by
    apply ((hflow r ⟨hr.1, hr.2.trans_le ht.2⟩ (θ + P)).sub_const P).congr_deriv
    simpa only [sub_add_cancel] using hperiod r (Θ (r, θ + P) - P)
  have he := circleTrajectory_difference_eq_mul_exp ht.1 hG hu hv hdu
    (fun r hr => hflow r ⟨hr.1, hr.2.trans_le ht.2⟩ θ)
  simp only [hinit, add_sub_cancel_right, sub_self, zero_mul] at he
  linarith

end ContinuousFlexibility.Analysis
