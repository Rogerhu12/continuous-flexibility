module

public import ContinuousFlexibility.Analysis.OneHighCylinderFrequency

/-!
# Physical mixed-frequency weights for cylinder Sobolev estimates

Both physical frequency scales remain explicit. Coordinate derivative
monomials are dominated by the total Sobolev weight; conversely, the weight
is bounded by pure radial and angular endpoint weights. Subadditivity places
the full output order on one input in a genuine convolution estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ENNReal

theorem cylinderFrequencyWeight_sq (a q : ℝ) (ζ : ℝ × ℤ) :
    cylinderFrequencyWeight a q ζ ^ 2 = 1 + (a * ζ.1) ^ 2 + (q * (ζ.2 : ℝ)) ^ 2 := by
  rw [cylinderFrequencyWeight_apply, Real.sq_sqrt (by positivity)]

theorem cylinderFrequencyWeight_one_le (a q : ℝ) (ζ : ℝ × ℤ) :
    1 ≤ cylinderFrequencyWeight a q ζ := by
  have hs := cylinderFrequencyWeight_sq a q ζ
  have hp := (cylinderFrequencyWeight_pos a q ζ).le
  nlinarith [sq_nonneg (a * ζ.1), sq_nonneg (q * (ζ.2 : ℝ))]

theorem cylinder_radialFrequency_le_weight (a q : ℝ) (ζ : ℝ × ℤ) :
    |a * ζ.1| ≤ cylinderFrequencyWeight a q ζ := by
  apply (sq_le_sq₀ (abs_nonneg _) (cylinderFrequencyWeight_pos a q ζ).le).mp
  rw [sq_abs, cylinderFrequencyWeight_sq]
  nlinarith [sq_nonneg (q * (ζ.2 : ℝ))]

theorem cylinder_angularFrequency_le_weight (a q : ℝ) (ζ : ℝ × ℤ) :
    |q * (ζ.2 : ℝ)| ≤ cylinderFrequencyWeight a q ζ := by
  apply (sq_le_sq₀ (abs_nonneg _) (cylinderFrequencyWeight_pos a q ζ).le).mp
  rw [sq_abs, cylinderFrequencyWeight_sq]
  nlinarith [sq_nonneg (a * ζ.1)]

theorem cylinder_mixedFrequency_le_weight (a q : ℝ) (ζ : ℝ × ℤ)
    {r t s : ℕ} (hrt : r + t ≤ s) :
    |a * ζ.1| ^ r * |q * (ζ.2 : ℝ)| ^ t ≤ cylinderFrequencyWeight a q ζ ^ s := by
  calc
    _ ≤ cylinderFrequencyWeight a q ζ ^ r * cylinderFrequencyWeight a q ζ ^ t :=
      mul_le_mul
        (pow_le_pow_left₀ (abs_nonneg _) (cylinder_radialFrequency_le_weight a q ζ) r)
        (pow_le_pow_left₀ (abs_nonneg _) (cylinder_angularFrequency_le_weight a q ζ) t)
        (pow_nonneg (abs_nonneg _) t)
        (pow_nonneg (cylinderFrequencyWeight_pos a q ζ).le r)
    _ = cylinderFrequencyWeight a q ζ ^ (r + t) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (cylinderFrequencyWeight_one_le a q ζ) hrt

theorem cylinderFrequencyWeight_le_one_add_coordinates (a q : ℝ) (ζ : ℝ × ℤ) :
    cylinderFrequencyWeight a q ζ ≤ 1 + |a * ζ.1| + |q * (ζ.2 : ℝ)| := by
  apply (sq_le_sq₀ (cylinderFrequencyWeight_pos a q ζ).le (by positivity)).mp
  rw [cylinderFrequencyWeight_sq]
  nlinarith [sq_abs (a * ζ.1), sq_abs (q * (ζ.2 : ℝ)), abs_nonneg (a * ζ.1),
    abs_nonneg (q * (ζ.2 : ℝ)), mul_nonneg (abs_nonneg (a * ζ.1))
      (abs_nonneg (q * (ζ.2 : ℝ)))]

theorem cylinderFrequencyWeight_nat_pow_le (a q : ℝ) (ζ : ℝ × ℤ) (s : ℕ) :
    cylinderFrequencyWeight a q ζ ^ s ≤ (3 : ℝ) ^ s *
      (1 + |a * ζ.1| ^ s + |q * (ζ.2 : ℝ)| ^ s) := by
  let M := max (1 : ℝ) (max |a * ζ.1| |q * (ζ.2 : ℝ)|)
  have h1 : 1 ≤ M := le_max_left _ _
  have hx : |a * ζ.1| ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hy : |q * (ζ.2 : ℝ)| ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hW : cylinderFrequencyWeight a q ζ ≤ 3 * M :=
    (cylinderFrequencyWeight_le_one_add_coordinates a q ζ).trans (by linarith)
  have hM : M ^ s ≤ 1 + |a * ζ.1| ^ s + |q * (ζ.2 : ℝ)| ^ s := by
    dsimp only [M]
    rcases le_total |a * ζ.1| |q * (ζ.2 : ℝ)| with hxy | hyx
    · rw [max_eq_right hxy]
      rcases le_total 1 |q * (ζ.2 : ℝ)| with h | h
      · rw [max_eq_right h]
        nlinarith [pow_nonneg (abs_nonneg (a * ζ.1)) s]
      · rw [max_eq_left h, one_pow]
        nlinarith [pow_nonneg (abs_nonneg (a * ζ.1)) s,
          pow_nonneg (abs_nonneg (q * (ζ.2 : ℝ))) s]
    · rw [max_eq_left hyx]
      rcases le_total 1 |a * ζ.1| with h | h
      · rw [max_eq_right h]
        nlinarith [pow_nonneg (abs_nonneg (q * (ζ.2 : ℝ))) s]
      · rw [max_eq_left h, one_pow]
        nlinarith [pow_nonneg (abs_nonneg (a * ζ.1)) s,
          pow_nonneg (abs_nonneg (q * (ζ.2 : ℝ))) s]
  calc
    _ ≤ (3 * M) ^ s := pow_le_pow_left₀ (cylinderFrequencyWeight_pos a q ζ).le hW s
    _ = (3 : ℝ) ^ s * M ^ s := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hM (by positivity)

theorem cylinderFrequencyWeight_add_le (a q : ℝ) (ζ η : ℝ × ℤ) :
    cylinderFrequencyWeight a q (ζ + η) ≤
      cylinderFrequencyWeight a q ζ + cylinderFrequencyWeight a q η := by
  let x := a * ζ.1
  let y := q * (ζ.2 : ℝ)
  let u := a * η.1
  let v := q * (η.2 : ℝ)
  let X := cylinderFrequencyWeight a q ζ
  let Y := cylinderFrequencyWeight a q η
  have hX : 0 ≤ X := (cylinderFrequencyWeight_pos a q ζ).le
  have hY : 0 ≤ Y := (cylinderFrequencyWeight_pos a q η).le
  have hsX : X ^ 2 = 1 + x ^ 2 + y ^ 2 := cylinderFrequencyWeight_sq a q ζ
  have hsY : Y ^ 2 = 1 + u ^ 2 + v ^ 2 := cylinderFrequencyWeight_sq a q η
  have hXY : (X * Y) ^ 2 = (1 + x ^ 2 + y ^ 2) * (1 + u ^ 2 + v ^ 2) := by
    rw [mul_pow, hsX, hsY]
  have hdotSq : (x * u + y * v) ^ 2 ≤ (X * Y) ^ 2 := by
    nlinarith [sq_nonneg (x * v - y * u), sq_nonneg x, sq_nonneg y,
      sq_nonneg u, sq_nonneg v]
  have hdot : x * u + y * v ≤ X * Y := by
    by_cases h : x * u + y * v ≤ 0
    · exact h.trans (mul_nonneg hX hY)
    · exact (sq_le_sq₀ (le_of_lt (lt_of_not_ge h)) (mul_nonneg hX hY)).mp hdotSq
  have hs : cylinderFrequencyWeight a q (ζ + η) ^ 2 =
      1 + (x + u) ^ 2 + (y + v) ^ 2 := by
    rw [cylinderFrequencyWeight_sq]
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, mul_add, x, y, u, v]
  apply (sq_le_sq₀ (cylinderFrequencyWeight_pos a q (ζ + η)).le
    (add_nonneg hX hY)).mp
  nlinarith [hdot]

theorem cylinderFrequencyWeight_add_pow_le (a q : ℝ) (ζ η : ℝ × ℤ) (s : ℕ) :
    cylinderFrequencyWeight a q (ζ + η) ^ s ≤ (2 : ℝ) ^ s *
      (cylinderFrequencyWeight a q ζ ^ s + cylinderFrequencyWeight a q η ^ s) := by
  have hbase : cylinderFrequencyWeight a q (ζ + η) ≤
      2 * max (cylinderFrequencyWeight a q ζ) (cylinderFrequencyWeight a q η) :=
    (cylinderFrequencyWeight_add_le a q ζ η).trans (by
      linarith [le_max_left (cylinderFrequencyWeight a q ζ) (cylinderFrequencyWeight a q η),
        le_max_right (cylinderFrequencyWeight a q ζ) (cylinderFrequencyWeight a q η)])
  have hp := pow_le_pow_left₀ (cylinderFrequencyWeight_pos a q (ζ + η)).le hbase s
  rw [mul_pow] at hp
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases le_total (cylinderFrequencyWeight a q ζ) (cylinderFrequencyWeight a q η) with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (pow_nonneg (cylinderFrequencyWeight_pos a q ζ).le s)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (pow_nonneg (cylinderFrequencyWeight_pos a q η).le s)

theorem cylinder_norm_frequencyWeighted_nat (a q : ℝ) (s : ℕ)
    (F : ℝ × ℤ → ℂ) (ζ : ℝ × ℤ) :
    ‖frequencyWeighted (cylinderFrequencyWeight a q) (s : ℝ) F ζ‖ =
      cylinderFrequencyWeight a q ζ ^ s * ‖F ζ‖ := by
  rw [frequencyWeighted_apply, norm_smul, Real.rpow_natCast,
    Real.norm_of_nonneg (pow_nonneg (cylinderFrequencyWeight_pos a q ζ).le s)]

end ContinuousFlexibility.Analysis
