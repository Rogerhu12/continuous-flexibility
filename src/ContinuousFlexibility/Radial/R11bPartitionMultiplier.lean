import ContinuousFlexibility.Radial.R11bPartitionL2

/-!
# Physical multipliers bounded on each localized cell

A multiplier may be unbounded globally. Its square bound on the support of
each localizer suffices, provided the corresponding weighted square integrals
are summable. This applies to both the physical density and its reciprocal.
-/

namespace ContinuousFlexibility.Radial

open Filter MeasureTheory
open scoped BigOperators Topology ENNReal

theorem r11b_memLp_mul_of_localized_square_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (χ : ℕ → α → ℝ) (f a : α → ℝ) (A : ℕ → ℝ) {B : ℕ}
    (hlocal : ∀ m, MemLp (fun x => χ m x * f x) 2 μ)
    (ha : AEStronglyMeasurable a μ) (hA : ∀ m, 0 ≤ A m)
    (hbound : ∀ m, ∀ᵐ x ∂μ, χ m x ≠ 0 → |a x| ^ 2 ≤ A m)
    (hfinite : ∀ᵐ x ∂μ, (Function.support (fun m => χ m x)).Finite)
    (hcard : ∀ᵐ x ∂μ, (Function.support (fun m => χ m x)).ncard ≤ B)
    (hsum : ∀ᵐ x ∂μ, (∑' m, χ m x) = 1)
    (hintegral : Summable (fun m => A m * ∫ x, (χ m x * f x) ^ 2 ∂μ)) :
    MemLp (fun x => a x * f x) 2 μ ∧
      (∫ x, (a x * f x) ^ 2 ∂μ) ≤
        (B : ℝ) * ∑' m, A m * ∫ x, (χ m x * f x) ^ 2 ∂μ := by
  have hm (m : ℕ) :
      AEStronglyMeasurable (fun x => χ m x * (a x * f x)) μ := by
    apply (ha.mul (hlocal m).aestronglyMeasurable).congr
    exact Eventually.of_forall (fun x => mul_left_comm (a x) (χ m x) (f x))
  have hb (m : ℕ) : ∀ᵐ x ∂μ,
      (χ m x * (a x * f x)) ^ 2 ≤ A m * (χ m x * f x) ^ 2 := by
    filter_upwards [hbound m] with x hx
    by_cases hz : χ m x = 0
    · simp [hz]
    · have ha_sq : a x ^ 2 ≤ A m := by
        simpa only [sq_abs] using hx hz
      calc
        (χ m x * (a x * f x)) ^ 2 = a x ^ 2 * (χ m x * f x) ^ 2 := by ring
        _ ≤ A m * (χ m x * f x) ^ 2 :=
          mul_le_mul_of_nonneg_right ha_sq (sq_nonneg (χ m x * f x))
  have hmajor (m : ℕ) :
      Integrable (fun x => A m * (χ m x * f x) ^ 2) μ :=
    (hlocal m).integrable_sq.const_mul (A m)
  have hwint (m : ℕ) :
      Integrable (fun x => (χ m x * (a x * f x)) ^ 2) μ := by
    apply (hmajor m).mono ((hm m).pow 2)
    filter_upwards [hb m] with x hx
    change ‖(χ m x * (a x * f x)) ^ 2‖ ≤ ‖A m * (χ m x * f x) ^ 2‖
    rw [Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (mul_nonneg (hA m) (sq_nonneg _))]
    exact hx
  have hwlocal (m : ℕ) : MemLp (fun x => χ m x * (a x * f x)) 2 μ :=
    (memLp_two_iff_integrable_sq (hm m)).mpr (hwint m)
  have hi (m : ℕ) :
      (∫ x, (χ m x * (a x * f x)) ^ 2 ∂μ) ≤
        A m * ∫ x, (χ m x * f x) ^ 2 ∂μ := by
    calc
      _ ≤ ∫ x, A m * (χ m x * f x) ^ 2 ∂μ :=
        integral_mono_ae (hwint m) (hmajor m) (hb m)
      _ = _ := by rw [integral_const_mul]
  have hws : Summable (fun m => ∫ x, (χ m x * (a x * f x)) ^ 2 ∂μ) :=
    Summable.of_nonneg_of_le
      (fun m => integral_nonneg (fun x => sq_nonneg (χ m x * (a x * f x))))
      hi hintegral
  obtain ⟨haf, hI⟩ := r11b_memLp_of_localized_square_summable χ
    (fun x => a x * f x) hwlocal hfinite hcard hsum hws
  refine ⟨haf, hI.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Summable.tsum_le_tsum hi hws hintegral) (Nat.cast_nonneg B)

end ContinuousFlexibility.Radial
