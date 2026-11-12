import ContinuousFlexibility.Analysis.N05OpticalRootQuotient

/-!
# An explicit two-sided collar from an optical root lower bound

The full-component lower bound first gives the actual inward derivative
at the root. A bound for the actual second derivative on a supplied
two-sided working interval then chooses a collar of explicit radius.
The same integral quotient remains positive on both sides of the root.

The working interval is an original domain of the profile. In particular,
this file does not infer a positive-side neighborhood from containment of
an open negative component in a material cell.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The two-root distance lower bound controls the actual derivative at
the left root; apply this to the inward affine slice at a right root. -/
theorem n05_optical_root_slope_lower
    {F : ℝ → ℝ} {L α : ℝ} {M : NNReal} (hL : 0 < L)
    (hF : ∀ x ∈ Icc (0 : ℝ) L, ContDiffAt ℝ 2 F x)
    (hzero : F 0 = 0)
    (hsecond : ∀ x ∈ Icc (0 : ℝ) L, |deriv (deriv F) x| ≤ M)
    (hlower : ∀ x ∈ Icc (0 : ℝ) L, α * min x (L - x) ≤ F x) :
    α ≤ deriv F 0 := by
  have hhalf : Icc (0 : ℝ) (L / 2) ⊆ Icc (0 : ℝ) L :=
    Icc_subset_Icc le_rfl (by linarith)
  have hFhalf : ∀ x ∈ Icc (0 : ℝ) (L / 2), ContDiffAt ℝ 2 F x :=
    fun x hx => hF x (hhalf hx)
  have hLip : LipschitzOnWith M (deriv F) (Icc (0 : ℝ) (L / 2)) :=
    n05_optical_deriv_lipschitz hFhalf (fun x hx => hsecond x (hhalf hx))
  have hlo : ∀ x ∈ Icc (0 : ℝ) (L / 2), α * x ≤ F x := by
    intro x hx
    have hh := hlower x (hhalf hx)
    rw [min_eq_left (by linarith only [hx.2])] at hh
    exact hh
  have hq := n05OpticalRootQuotient_lower (half_pos hL) hFhalf hzero hLip hlo
    0 ⟨le_rfl, (half_pos hL).le⟩
  simpa only [n05OpticalRootQuotient, mul_zero, intervalIntegral.integral_const,
    sub_zero, one_smul] using hq

/-- This radius uses only the original working radius, the root slope
lower bound and the second derivative bound. -/
def n05OpticalRootCollarRadius (ρ α M : ℝ) : ℝ :=
  min ρ (α / (2 * (M + 1)))

theorem n05OpticalRootCollarRadius_bounds {ρ α M : ℝ}
    (hρ : 0 < ρ) (hα : 0 < α) (hM : 0 ≤ M) :
    0 < n05OpticalRootCollarRadius ρ α M ∧
      n05OpticalRootCollarRadius ρ α M ≤ ρ ∧
      M * n05OpticalRootCollarRadius ρ α M ≤ α / 2 ∧
      (n05OpticalRootCollarRadius ρ α M)⁻¹ ≤ ρ⁻¹ + 2 * (M + 1) / α := by
  have hden : 0 < 2 * (M + 1) := by positivity
  have hδ : 0 < n05OpticalRootCollarRadius ρ α M :=
    lt_min hρ (div_pos hα hden)
  have hsmall : n05OpticalRootCollarRadius ρ α M ≤ α / (2 * (M + 1)) :=
    min_le_right _ _
  have hsmall' := (le_div_iff₀ hden).mp hsmall
  refine ⟨hδ, min_le_left _ _, ?_, ?_⟩
  · nlinarith only [hsmall', hδ.le]
  · by_cases hh : ρ ≤ α / (2 * (M + 1))
    · rw [n05OpticalRootCollarRadius, min_eq_left hh]
      exact le_add_of_nonneg_right (by positivity)
    · rw [n05OpticalRootCollarRadius, min_eq_right (le_of_not_ge hh), inv_div]
      exact le_add_of_nonneg_left (inv_nonneg.mpr hρ.le)

theorem n05OpticalRootCollarRadius_inv_polynomial {ρ α M Λ : ℝ}
    (hρ : 0 < ρ) (hα : 0 < α) (hM : 0 ≤ M) (hΛ : 1 ≤ Λ)
    (hρinv : ρ⁻¹ ≤ Λ) (hαinv : α⁻¹ ≤ Λ) (hMΛ : M ≤ Λ) :
    (n05OpticalRootCollarRadius ρ α M)⁻¹ ≤ 5 * Λ ^ 2 := by
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  apply (n05OpticalRootCollarRadius_bounds hρ hα hM).2.2.2.trans
  have hterm : 2 * (M + 1) / α ≤ 2 * (Λ + 1) * Λ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul (by linarith only [hMΛ]) hαinv
      (inv_nonneg.mpr hα.le) (by positivity)
  have hΛsq : Λ ≤ Λ ^ 2 := by nlinarith only [mul_nonneg hΛ0 (sub_nonneg.mpr hΛ)]
  nlinarith only [hρinv, hterm, hΛsq]

theorem n05_optical_symmetric_unit_mul_mem {ρ x t : ℝ}
    (hx : x ∈ Icc (-ρ) ρ) (ht : t ∈ Icc (0 : ℝ) 1) :
    t * x ∈ Icc (-ρ) ρ := by
  have hh : |t * x| ≤ ρ := by
    rw [abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg x)).trans
      (by simpa only [one_mul] using abs_le.mpr hx)
  exact abs_le.mp hh

/-- The actual derivative and its averaged root quotient are bounded on
the same explicitly chosen two-sided collar. No quotient derivative or
coordinate derivative is supplied as an input. -/
theorem n05_optical_root_collar_bounds
    {F : ℝ → ℝ} {ρ α M : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hM : 0 ≤ M)
    (hF : ∀ x ∈ Icc (-ρ) ρ, ContDiffAt ℝ 2 F x)
    (hslope : α ≤ deriv F 0)
    (hsecond : ∀ x ∈ Icc (-ρ) ρ, |deriv (deriv F) x| ≤ M) :
    let δ := n05OpticalRootCollarRadius ρ α M;
    ∀ x ∈ Icc (-δ) δ,
      α / 2 ≤ deriv F x ∧
      |deriv F x| ≤ |deriv F 0| + M * δ ∧
      α / 2 ≤ n05OpticalRootQuotient F x ∧
      |n05OpticalRootQuotient F x| ≤ |deriv F 0| + M * δ := by
  let δ := n05OpticalRootCollarRadius ρ α M
  obtain ⟨hδ, hδρ, hδM, _⟩ := n05OpticalRootCollarRadius_bounds hρ hα hM
  change ∀ x ∈ Icc (-δ) δ, _
  have hsub : Icc (-δ) δ ⊆ Icc (-ρ) ρ :=
    Icc_subset_Icc (neg_le_neg hδρ) hδρ
  have hLip : LipschitzOnWith ⟨M, hM⟩ (deriv F) (Icc (-ρ) ρ) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => ((hF x hx).derivWithin (m := 1)
        (by norm_num)).differentiableAt (by norm_num)) _ (convex_Icc (-ρ) ρ)
    intro x hx
    change ‖deriv (deriv F) x‖ ≤ M
    simpa only [Real.norm_eq_abs] using hsecond x hx
  have hder (x : ℝ) (hx : x ∈ Icc (-δ) δ) :
      α / 2 ≤ deriv F x ∧ |deriv F x| ≤ |deriv F 0| + M * δ := by
    have hh := hLip.dist_le_mul x (hsub hx) 0 ⟨by linarith, hρ.le⟩
    change dist (deriv F x) (deriv F 0) ≤ M * dist x 0 at hh
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at hh
    have hdiff : |deriv F x - deriv F 0| ≤ M * δ :=
      hh.trans (mul_le_mul_of_nonneg_left (abs_le.mpr hx) hM)
    constructor
    · have hlo := (abs_le.mp hdiff).1
      linarith only [hslope, hlo, hδM]
    · calc
        |deriv F x| = |deriv F x - deriv F 0 + deriv F 0| :=
          congrArg abs (sub_add_cancel (deriv F x) (deriv F 0)).symm
        _ ≤ |deriv F x - deriv F 0| + |deriv F 0| := abs_add_le _ _
        _ ≤ M * δ + |deriv F 0| := add_le_add hdiff le_rfl
        _ = |deriv F 0| + M * δ := add_comm _ _
  intro x hx
  have hi : IntervalIntegrable (fun t => deriv F (t * x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    have hc : ContinuousOn (deriv F) (Icc (-δ) δ) := fun y hy =>
      ((hF y (hsub hy)).derivWithin (m := 1) (by norm_num)).continuousAt.continuousWithinAt
    exact hc.comp (continuous_id.mul continuous_const).continuousOn
      (fun t ht => n05_optical_symmetric_unit_mul_mem hx ht)
  refine ⟨(hder x hx).1, (hder x hx).2, ?_, ?_⟩
  · have hb := intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const hi
      (fun t ht => (hder (t * x) (n05_optical_symmetric_unit_mul_mem hx ht)).1)
    simpa only [n05OpticalRootQuotient, intervalIntegral.integral_const,
      sub_zero, one_smul] using hb
  · have hb := intervalIntegral.integral_mono_on zero_le_one hi.abs intervalIntegrable_const
      (fun t ht => (hder (t * x) (n05_optical_symmetric_unit_mul_mem hx ht)).2)
    exact (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans
      (by simpa only [n05OpticalRootQuotient, intervalIntegral.integral_const,
        sub_zero, one_smul] using hb)

end ContinuousFlexibility.Statements
