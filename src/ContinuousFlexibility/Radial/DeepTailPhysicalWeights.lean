module

public import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# Coefficient weights and physical endpoint distance

The cubic attenuation dominates every fixed Gaussian endpoint power.
Fixed shifts of the physical cell index cost only another coefficient
power; this includes the next-cell cap on a left tail.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

/-- A fixed shift in the coefficient weight costs one fixed coefficient
power and one scalar constant. -/
theorem physicalWeight_shift (A : ℝ) (hA : 0 ≤ A) (shift : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n,
      radialE (n + shift) ^ A ≤ C * radialE n ^ C := by
  obtain ⟨c, B, hshift⟩ := radialQ_shift_le shift
  let M : ℝ := exp (A * B)
  let L : ℝ := max 0 (A * c)
  let C : ℝ := M + L + 1
  have hM : 0 < M := exp_pos _
  have hL : 0 ≤ L := le_max_left _ _
  have hC : 0 < C := by dsimp [C]; positivity
  have hMC : M ≤ C := by dsimp [C]; linarith
  have hAC : A * c ≤ C := by
    have hh : A * c ≤ L := le_max_right _ _
    dsimp [C]
    linarith
  refine ⟨C, hC, fun n => ?_⟩
  have hq := mul_le_mul_of_nonneg_left (hshift n) hA
  have hc := mul_le_mul_of_nonneg_right hAC (radialQ_nonneg n)
  have hexp : A * radialQ (n + shift) ≤ A * B + C * radialQ n := by
    nlinarith
  calc
    radialE (n + shift) ^ A = exp (A * radialQ (n + shift)) := by
      rw [radialE, ← exp_mul, mul_comm]
    _ ≤ exp (A * B + C * radialQ n) := exp_le_exp.mpr hexp
    _ = M * radialE n ^ C := by
      rw [exp_add, radialE, ← exp_mul]
      congr 1
      congr 1
      exact mul_comm _ _
    _ ≤ C * radialE n ^ C := mul_le_mul_of_nonneg_right hMC
      (rpow_nonneg (exp_pos _).le _)

/-- The same fixed-index shift preserves the natural cubic attenuation. -/
theorem physicalEnvelope_shift (A : ℝ) (hA : 0 ≤ A) (shift : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n,
      radialE (n + shift) ^ A * exp (-radialS (n + shift)) ≤
        C * radialE n ^ C * exp (-radialS n) := by
  obtain ⟨C, hC, hweight⟩ := physicalWeight_shift A hA shift
  refine ⟨C, hC, fun n => ?_⟩
  exact mul_le_mul (hweight n)
    (exp_le_exp.mpr (neg_le_neg (radialS_monotone (Nat.le_add_right n shift))))
    (exp_pos _).le (mul_nonneg hC.le (rpow_nonneg (exp_pos _).le _))

/-- The attenuation defeats every prescribed power of the physical
Gaussian distance, uniformly over all indices including zero. -/
theorem physicalEnvelope_le_gaussian (A : ℝ) (order shift : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n,
      radialE n ^ A * exp (-radialS n) ≤
        C * exp (-((order : ℝ) * ((n : ℝ) + shift) ^ 2)) := by
  obtain ⟨K, hK, hbound⟩ := radial_scale_absorption A (2 * order)
    (ε := (1 / 2 : ℝ)) (by norm_num)
  refine ⟨K * exp (2 * order * (shift : ℝ) ^ 2),
    mul_pos hK (exp_pos _), fun n => ?_⟩
  have horder : 0 ≤ (order : ℝ) := Nat.cast_nonneg _
  have hS : 0 ≤ radialS n := by unfold radialS; positivity
  have hsq : ((n : ℝ) + shift) ^ 2 ≤ 2 * (n : ℝ) ^ 2 + 2 * (shift : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - shift)]
  have hexp : (1 / 2 : ℝ) * radialS n + (-radialS n - 2 * order * (n : ℝ) ^ 2) ≤
      2 * order * (shift : ℝ) ^ 2 - (order : ℝ) * ((n : ℝ) + shift) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq horder]
  calc
    _ = (radialE n ^ A * exp (2 * order * (n : ℝ) ^ 2)) *
        exp (-radialS n - 2 * order * (n : ℝ) ^ 2) := by
      rw [mul_assoc, ← exp_add]
      congr 1
      congr 1
      ring
    _ ≤ (K * exp ((1 / 2 : ℝ) * radialS n)) *
        exp (-radialS n - 2 * order * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (hbound n) (exp_pos _).le
    _ = K * exp ((1 / 2 : ℝ) * radialS n +
        (-radialS n - 2 * order * (n : ℝ) ^ 2)) := by rw [mul_assoc, ← exp_add]
    _ ≤ K * exp (2 * order * (shift : ℝ) ^ 2 -
        (order : ℝ) * ((n : ℝ) + shift) ^ 2) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexp) hK.le
    _ = _ := by simp only [sub_eq_add_neg, exp_add, mul_assoc]

/-- An actual Gaussian lower bound for the distance converts the node
envelope to any chosen integer power of that distance. -/
theorem physicalEnvelope_le_distance_power (A : ℝ) (order shift : ℕ)
    {d0 : ℝ} (hd0 : 0 < d0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (d : ℝ),
      d0 * exp (-((n : ℝ) + shift) ^ 2) ≤ d →
      radialE n ^ A * exp (-radialS n) ≤ C * d ^ order := by
  obtain ⟨K, hK, hbound⟩ := physicalEnvelope_le_gaussian A order shift
  refine ⟨K / d0 ^ order, div_pos hK (pow_pos hd0 _), fun n d hd => ?_⟩
  have hratio : exp (-((n : ℝ) + shift) ^ 2) ≤ d / d0 := by
    apply (le_div_iff₀ hd0).mpr
    simpa only [mul_comm] using hd
  have hpow := pow_le_pow_left₀ (exp_pos (-((n : ℝ) + shift) ^ 2)).le hratio order
  have heq : exp (-((order : ℝ) * ((n : ℝ) + shift) ^ 2)) =
      exp (-((n : ℝ) + shift) ^ 2) ^ order := by
    rw [← exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ K * exp (-((order : ℝ) * ((n : ℝ) + shift) ^ 2)) := hbound n
    _ = K * exp (-((n : ℝ) + shift) ^ 2) ^ order := by rw [heq]
    _ ≤ K * (d / d0) ^ order := mul_le_mul_of_nonneg_left hpow hK.le
    _ = _ := by rw [div_pow]; ring

end ContinuousFlexibility.Radial
