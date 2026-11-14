module

public import ContinuousFlexibility.Analysis.NeighborhoodCircleFlowVariational

/-!
# Regularity and lift law of the constructed circle flow

A continuous angular derivative of a periodic speed is uniformly bounded
on a compact time strip. Exact differences prove joint continuity, the
positive angular Jacobian, and uniqueness. No radial derivative is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology

theorem continuousAngleSpeedSecant_abs_le {dG : PolarPoint → ℝ} (hdG : Continuous dG)
    {t M : ℝ} (hbound : ∀ η : ℝ, |dG (t, η)| ≤ M) (x y : ℝ) :
    |continuousAngleSpeedSecant dG (t, (x, y))| ≤ M := by
  have hc : Continuous (fun s : ℝ => dG (t, (y - x) * s + x)) :=
    hdG.comp
      (continuous_const.prodMk ((continuous_const.mul continuous_id).add continuous_const))
  have hm := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (μ := volume)
    zero_le_one (hc.abs.intervalIntegrable 0 1) (intervalIntegrable_const (c := M))
    (fun s _ => hbound ((y - x) * s + x))
  have ha := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := fun s => dG (t, (y - x) * s + x)) zero_le_one
  simpa only [continuousAngleSpeedSecant, intervalIntegral.integral_const, sub_zero,
    one_smul] using ha.trans hm

/-- Uniform Lipschitz dependence follows from the genuine time equation,
before any initial-angle derivative has been constructed. -/
theorem continuousAngleFlow_angle_lipschitz_bound {G dG Θ : PolarPoint → ℝ} {a b M : ℝ}
    (hdG : Continuous dG)
    (hderiv : ∀ t x, HasDerivAt (fun y => G (t, y)) (dG (t, x)) x)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    (hM : 0 ≤ M) (hbound : ∀ r ∈ Icc a b, ∀ η : ℝ, |dG (r, η)| ≤ M)
    {t : ℝ} (ht : t ∈ Icc a b) (η θ : ℝ) :
    |Θ (t, η) - Θ (t, θ)| ≤ Real.exp ((b - a) * M) * |η - θ| := by
  have htime (ξ : ℝ) : ContinuousOn (fun r => Θ (r, ξ)) (Icc a t) :=
    (hΘ ξ).mono (Icc_subset_Icc le_rfl ht.2)
  have hκ : ContinuousOn
      (fun r => continuousAngleSpeedSecant dG (r, (Θ (r, θ), Θ (r, η)))) (Icc a t) :=
    (continuous_continuousAngleSpeedSecant hdG).comp_continuousOn
      (continuousOn_id.prodMk ((htime θ).prodMk (htime η)))
  have hI : (∫ r in a..t, continuousAngleSpeedSecant dG (r, (Θ (r, θ), Θ (r, η)))) ≤
      (t - a) * M := by
    have hm := intervalIntegral.integral_mono_on (μ := volume) ht.1
      (hκ.intervalIntegrable_of_Icc ht.1) (intervalIntegrable_const (c := M))
      (fun r hr => (le_abs_self _).trans
        (continuousAngleSpeedSecant_abs_le hdG (hbound r ⟨hr.1, hr.2.trans ht.2⟩) _ _))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
  have hlength : (t - a) * M ≤ (b - a) * M :=
    mul_le_mul_of_nonneg_right (sub_le_sub_right ht.2 a) hM
  have he := continuousAngleFlow_difference_eq_mul_exp ht.1 hdG hderiv htime
    (fun r hr => hflow r ⟨hr.1, hr.2.trans_le ht.2⟩) η θ
  calc
    |Θ (t, η) - Θ (t, θ)| = |η - θ| *
        Real.exp (∫ r in a..t, continuousAngleSpeedSecant dG (r, (Θ (r, θ), Θ (r, η)))) := by
      rw [he, hinit η, hinit θ, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ |η - θ| * Real.exp ((b - a) * M) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hI.trans hlength)) (abs_nonneg _)
    _ = Real.exp ((b - a) * M) * |η - θ| := mul_comm _ _

private theorem continuousAngleFlow_continuousOn_of_bound
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
      apply add_le_add <;> try exact le_rfl
      simpa only [Real.dist_eq] using hbound q.1 hq.1 q.2 p.2
    _ < ε := by linarith

/-- Continuous angular derivative and individual classical time solutions imply
joint continuity of the whole flow on the closed strip. -/
theorem continuousAngleFlow_continuousOn {G dG Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hdG : Continuous dG)
    (hderiv : ∀ t x, HasDerivAt (fun y => G (t, y)) (dG (t, x)) x) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t) :
    ContinuousOn Θ (Icc a b ×ˢ (univ : Set ℝ)) := by
  obtain ⟨M, hM, hbound⟩ := exists_continuous_periodic_strip_bound hdG hP
    (continuousAngleSpeed_derivative_periodic hderiv hperiod) a b
  exact continuousAngleFlow_continuousOn_of_bound (Real.exp_pos _) hΘ
    (fun t ht η θ => continuousAngleFlow_angle_lipschitz_bound hdG hderiv hΘ hinit hflow hM hbound ht η θ)

/-- The variational exponential for an actual classical periodic flow.
No joint continuity or angular regularity is an input. -/
theorem continuousAngleFlow_hasDerivAt_angle {G dG Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hdG : Continuous dG)
    (hderiv : ∀ t x, HasDerivAt (fun y => G (t, y)) (dG (t, x)) x) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    HasDerivAt (fun η => Θ (t, η))
      (Real.exp (∫ r in a..t, dG (r, Θ (r, θ)))) θ :=
  continuousAngleFlow_hasDerivAt_angle_of_continuous hdG hderiv
    (continuousAngleFlow_continuousOn hdG hderiv hP hperiod hΘ hinit hflow) hinit hflow ht θ

theorem continuousAngleFlow_angle_strictMono {G dG Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hdG : Continuous dG)
    (hderiv : ∀ t x, HasDerivAt (fun y => G (t, y)) (dG (t, x)) x) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) : StrictMono (fun θ => Θ (t, θ)) := by
  apply strictMono_of_deriv_pos
  intro θ
  rw [(continuousAngleFlow_hasDerivAt_angle hdG hderiv hP hperiod hΘ hinit hflow ht θ).deriv]
  exact Real.exp_pos _

/-- The lift law follows from uniqueness of the actual scalar time
equation. It is not imposed as a condition on the flow family. -/
theorem continuousAngleFlow_lift_add {G dG Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hdG : Continuous dG)
    (hderiv : ∀ t x, HasDerivAt (fun y => G (t, y)) (dG (t, x)) x)
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
  have he := continuousAngleTrajectory_difference_eq_mul_exp ht.1 hdG hderiv hu hv hdu
    (fun r hr => hflow r ⟨hr.1, hr.2.trans_le ht.2⟩ θ)
  simp only [hinit, add_sub_cancel_right, sub_self, zero_mul] at he
  linarith

/-- Existence and every ordinary circle-flow property follow from the
actual continuous speed and its continuous angular derivative. -/
theorem exists_regular_continuousAngleFlow {G dG : PolarPoint → ℝ} {a b P : ℝ}
    (hab : a ≤ b) (hG : Continuous G) (hdG : Continuous dG)
    (hderiv : ∀ t x, HasDerivAt (fun y => G (t, y)) (dG (t, x)) x)
    (hP : 0 < P) (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P) :
    ∃ Θ : PolarPoint → ℝ, (∀ θ, Θ (a, θ) = θ) ∧
      (∀ θ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b)) ∧
      (∀ t ∈ Ioo a b, ∀ θ,
        HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t) ∧
      (∀ t ∈ Icc a b, ∀ θ,
        0 < deriv (fun η => Θ (t, η)) θ ∧ Θ (t, θ + P) = Θ (t, θ) + P) := by
  obtain ⟨Θ, hinit, hΘ, hflow⟩ :=
    exists_continuousAngleFlow hab hG hdG hderiv hP hperiod
  refine ⟨Θ, hinit, hΘ, hflow, ?_⟩
  intro t ht θ
  constructor
  · rw [(continuousAngleFlow_hasDerivAt_angle hdG hderiv hP hperiod hΘ hinit hflow ht θ).deriv]
    exact Real.exp_pos _
  · exact continuousAngleFlow_lift_add hdG hderiv hperiod hΘ hinit hflow ht θ

end ContinuousFlexibility.Analysis
