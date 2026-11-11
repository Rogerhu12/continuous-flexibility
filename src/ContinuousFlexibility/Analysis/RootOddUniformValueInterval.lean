import ContinuousFlexibility.Analysis.RootExtensionPhysicalBounds
import ContinuousFlexibility.Analysis.RootTravelUniformBounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A fixed positive value interval throughout a root collar

The actual first radial derivative controls variation away from the
root. A bound on one angular period controls every angle. Applied to
the genuine extended odd coefficient, this uses two derivatives of the
original smooth inverse input, and selects the collar before that input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem periodicScalar_radial_value_control
    {f : PolarPoint → ℝ} {M x : ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hperiod : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (hB : CSBound 1 (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) f M)
    (hx : x ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    |f (x, θ)| ≤ M ∧ |f (x, θ) - f (0, θ)| ≤ M * x := by
  have hpair : Function.Periodic (fun η => (f (x, η), f (0, η))) Real.pi := by
    intro η
    exact Prod.ext (hperiod x η) (hperiod 0 η)
  obtain ⟨t, ht, he⟩ := hpair.exists_mem_Ico₀ Real.pi_pos θ
  have hxt : f (x, θ) = f (x, t) := congrArg Prod.fst he
  have hzt : f (0, θ) = f (0, t) := congrArg Prod.snd he
  rw [hxt, hzt]
  have ht' : t ∈ Icc (-Real.pi) Real.pi :=
    ⟨(neg_nonpos.mpr Real.pi_pos.le).trans ht.1, ht.2.le⟩
  have hp : (x, t) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi := ⟨hx, ht'⟩
  have hz : (0, t) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi :=
    ⟨⟨le_rfl, zero_le_one⟩, ht'⟩
  have hmean := ((convex_Icc (0 : ℝ) 1).prod
      (convex_Icc (-Real.pi) Real.pi)).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (fun q _ => hf.differentiable (by simp) q)
    (fun q hq => hB.fderiv_norm_le le_rfl hq) hz hp
  have hnorm : ‖((x, t) : PolarPoint) - (0, t)‖ = x := by
    simp only [Prod.mk_sub_mk, sub_zero, sub_self, Prod.norm_mk,
      Real.norm_of_nonneg hx.1, norm_zero, max_eq_left hx.1]
  exact ⟨by simpa only [Real.norm_eq_abs] using hB.norm_le hp,
    by simpa only [hnorm, Real.norm_eq_abs] using hmean⟩

/-- The radius depends on the numerical bounds and the available band,
and is selected before every member of the smooth periodic family. -/
theorem exists_periodicScalar_uniform_positive_band
    {η l M : ℝ} (hη : 0 < η) (hηone : η ≤ 1) (hl : 0 < l) (hM : 0 ≤ M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ η ∧
      ∀ f : PolarPoint → ℝ, ContDiff ℝ ∞ f →
        (∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi) →
        CSBound 1 (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) f M →
        (∀ θ, l ≤ f (0, θ)) →
        ∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ, f (x, θ) ∈ Icc (l / 2) (1 + M) := by
  have hMone : 0 < M + 1 := by linarith
  let ρ := min η (l / (2 * (M + 1)))
  have hρ : 0 < ρ := lt_min hη (div_pos hl (mul_pos (by norm_num) hMone))
  have hρη : ρ ≤ η := min_le_left _ _
  have hρM : M * ρ ≤ l / 2 := by
    calc
      M * ρ ≤ (M + 1) * ρ := mul_le_mul_of_nonneg_right (by linarith) hρ.le
      _ ≤ (M + 1) * (l / (2 * (M + 1))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hMone.le
      _ = l / 2 := by field_simp [hMone.ne'] <;> ring
  refine ⟨ρ, hρ, hρη, ?_⟩
  intro f hf hperiod hB hzero x hx θ
  obtain ⟨hvalue, hdiff⟩ := periodicScalar_radial_value_control hf hperiod hB
    ⟨hx.1, hx.2.trans (hρη.trans hηone)⟩ θ
  constructor
  · have hvariation := (abs_le.mp hdiff).1
    have hMx := mul_le_mul_of_nonneg_left hx.2 hM
    have hroot := hzero θ
    linarith only [hvariation, hMx, hρM, hroot]
  · exact (le_abs_self _).trans (hvalue.trans (le_add_of_nonneg_left zero_le_one))

/-- The true root odd coefficient has a uniform positive value interval
from its genuine boundary lower bound and two actual input derivatives.
No derivative bound for the divided field is an independent input. -/
theorem exists_rootOddCoefficient_uniform_positive_band
    {η κ M : ℝ} (hη : 0 < η) (hηone : η ≤ 1) (hκ : 0 < κ) (hM : 0 ≤ M) :
    ∃ ρ u : ℝ, 0 < ρ ∧ ρ ≤ η ∧ 0 < u ∧
      ∀ G : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ G →
        (∀ r ζ θ, G (r, ζ, θ + Real.pi) = G (r, ζ, θ) + Real.pi) →
        CSBound 2
          (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G M →
        (∀ θ, κ ≤ rootOddCoefficient G (0, θ)) →
        ∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ,
          extendedRootOddCoefficient G (x, θ) ∈ Icc (κ / 2) u := by
  obtain ⟨C, hC, hbound⟩ := exists_csBound_extendedRootOddCoefficient 1
  have hCM : 0 ≤ C * M := mul_nonneg hC.le hM
  obtain ⟨ρ, hρ, hρη, hpositive⟩ :=
    exists_periodicScalar_uniform_positive_band hη hηone hκ hCM
  refine ⟨ρ, 1 + C * M, hρ, hρη, add_pos_of_pos_of_nonneg zero_lt_one hCM, ?_⟩
  intro G hG hperiod hB hzero
  have hχperiod : ∀ r, 0 ≤ r →
      Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) Real.pi :=
    fun r _ => rootOddCoefficient_periodic hperiod r
  have hperiod' : ∀ r,
      Function.Periodic (fun θ => extendedRootOddCoefficient G (r, θ)) Real.pi := by
    intro r θ
    exact seeleyPeriodicExtension_periodic hχperiod r θ
  apply hpositive (extendedRootOddCoefficient G)
    (contDiff_extendedRootOddCoefficient hG Real.pi_ne_zero hχperiod) hperiod'
    (hbound G hG Real.pi Real.pi_ne_zero hχperiod M hB)
  intro θ
  rw [extendedRootOddCoefficient_of_nonneg G (p := (0, θ)) (le_refl (0 : ℝ))]
  exact hzero θ

end ContinuousFlexibility.Analysis
