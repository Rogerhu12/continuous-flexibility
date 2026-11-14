module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# A local derivative estimate for the buffer cutoff error

The homogeneous positive-buffer equation bounds the second derivative
on a layer of width `1 / m`. The mean value theorem then bounds the
first derivative by `C m` times the exponentially small height on that
same layer. No global supremum on a long cap enters this estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set

/-- A local height and second-derivative bound control the first
derivative at the beginning of a one-sided layer. -/
theorem innerBuffer_local_derivative_bound {u : ℝ → ℝ} {x δ M K : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K)
    (hu : ∀ y ∈ Icc x (x + δ), DifferentiableAt ℝ u y)
    (hdu : ∀ y ∈ Icc x (x + δ), DifferentiableAt ℝ (deriv u) y)
    (hheight : ∀ y ∈ Icc x (x + δ), |u y| ≤ M)
    (hsecond : ∀ y ∈ Icc x (x + δ), |deriv (deriv u) y| ≤ K) :
    |deriv u x| ≤ 2 * M / δ + K * δ := by
  have hxx : x ∈ Icc x (x + δ) := ⟨le_rfl, le_add_of_nonneg_right hδ.le⟩
  have hright : x + δ ∈ Icc x (x + δ) := ⟨hxx.2, le_rfl⟩
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope u (by linarith : x < x + δ)
    (fun y hy => (hu y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hu y (Ioo_subset_Icc_self hy)).differentiableWithinAt)
  have hc' : c ∈ Icc x (x + δ) := Ioo_subset_Icc_self hc
  have hdc : |deriv u c| ≤ 2 * M / δ := by
    rw [hslope, show x + δ - x = δ by ring, abs_div, abs_of_pos hδ]
    apply div_le_div_of_nonneg_right _ hδ.le
    exact (abs_sub _ _).trans (by linarith only [hheight (x + δ) hright, hheight x hxx])
  have hdif := Convex.norm_image_sub_le_of_norm_deriv_le hdu
    (fun y hy => by simpa only [Real.norm_eq_abs] using hsecond y hy)
    (convex_Icc x (x + δ)) hc' hxx
  have hdif' : |deriv u x - deriv u c| ≤ K * δ := by
    have hdist : |x - c| ≤ δ := by
      rw [abs_of_nonpos (sub_nonpos.mpr hc'.1)]
      linarith only [hc'.2]
    exact (show |deriv u x - deriv u c| ≤ K * |x - c| from hdif).trans
      (mul_le_mul_of_nonneg_left hdist hK)
  calc
    |deriv u x| = |(deriv u x - deriv u c) + deriv u c| := by rw [sub_add_cancel]
    _ ≤ |deriv u x - deriv u c| + |deriv u c| := abs_add_le _ _
    _ ≤ K * δ + 2 * M / δ := add_le_add hdif' hdc
    _ = _ := add_comm _ _

/-- The actual equation `u'' = V u` on a mass-scale layer yields the
`m` derivative factor in the cutoff commutator estimate. -/
theorem innerBuffer_mass_scale_derivative {u V : ℝ → ℝ} {x m M C : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hu : ∀ y ∈ Icc x (x + 1 / m), DifferentiableAt ℝ u y)
    (hdu : ∀ y ∈ Icc x (x + 1 / m), DifferentiableAt ℝ (deriv u) y)
    (hheight : ∀ y ∈ Icc x (x + 1 / m), |u y| ≤ M)
    (hpotential : ∀ y ∈ Icc x (x + 1 / m), |V y| ≤ C * m ^ 2)
    (heq : ∀ y ∈ Icc x (x + 1 / m), deriv (deriv u) y = V y * u y) :
    |deriv u x| ≤ (2 + C) * m * M := by
  have hsecond : ∀ y ∈ Icc x (x + 1 / m),
      |deriv (deriv u) y| ≤ C * m ^ 2 * M := by
    intro y hy
    rw [heq y hy, abs_mul]
    exact mul_le_mul (hpotential y hy) (hheight y hy) (abs_nonneg _)
      (mul_nonneg hC (sq_nonneg _))
  have h := innerBuffer_local_derivative_bound (one_div_pos.mpr hm)
    (mul_nonneg (mul_nonneg hC (sq_nonneg _)) hM) hu hdu hheight hsecond
  convert h using 1
  field_simp [hm.ne']

/-- The cutoff commutator has the expected `m²` pointwise factor.
The support length supplies the remaining square-root factor in `L²`. -/
theorem innerBuffer_commutator_bound {m M C C₁ C₂ p p' χ' χ'' : ℝ}
    (hm : 0 ≤ m) (hM : 0 ≤ M) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hp : |p| ≤ M) (hp' : |p'| ≤ (2 + C) * m * M)
    (hχ' : |χ'| ≤ C₁ * m) (hχ'' : |χ''| ≤ C₂ * m ^ 2) :
    |-χ'' * p - 2 * χ' * p'| ≤ (C₂ + 2 * C₁ * (2 + C)) * m ^ 2 * M := by
  calc
    _ ≤ |-χ'' * p| + |2 * χ' * p'| := abs_sub _ _
    _ = |χ''| * |p| + 2 * |χ'| * |p'| := by
      rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (C₂ * m ^ 2) * M + (2 * (C₁ * m)) * ((2 + C) * m * M) := by
      apply add_le_add
      · exact mul_le_mul hχ'' hp (abs_nonneg _) (mul_nonneg hC₂ (sq_nonneg _))
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hχ' (by norm_num)) hp'
          (abs_nonneg _) (by positivity)
    _ = _ := by ring

end ContinuousFlexibility.Radial
