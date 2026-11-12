import ContinuousFlexibility.Analysis.N07aCanonicalModeEnergySum

/-!
# Weighted derivative norms controlled by the actual cylinder energy

All multipliers act on the original interval L² classes. These five
bounds are precisely the weights in the expanded cubic principal
difference, so no higher Hessian graph needs to be constructed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory

theorem n07aCylinderPower_ae (p : ℕ) (u : N07aIntervalL2) :
    (n07aCylinderPower p u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x => cylinderWeight x ^ p * u x :=
  n07aIntervalC0Mul_ae _ _ u

theorem n07aCylinderSquare_integrable (p : ℕ) (u : N07aIntervalL2) :
    Integrable (fun x => cylinderWeight x ^ p * u x ^ 2)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply ((Lp.memLp u).integrable_mul (Lp.memLp (n07aCylinderPower p u))).congr
  filter_upwards [n07aCylinderPower_ae p u] with x hx
  simp only [Pi.mul_apply]
  rw [hx]
  ring

theorem n07aCylinderPower_norm_sq (p : ℕ) (u : N07aIntervalL2) :
    ‖n07aCylinderPower p u‖ ^ 2 = n07aCylinderSquare (2 * p) u := by
  have hn := norm_toLp_sq_eq_integral_sq (Lp.memLp (n07aCylinderPower p u))
  rw [Lp.toLp_coeFn] at hn
  rw [hn, n07aCylinderSquare_eq]
  apply integral_congr_ae
  filter_upwards [n07aCylinderPower_ae p u] with x hx
  rw [hx, mul_pow, ← pow_mul]
  congr 2
  omega

theorem n07aCylinderSquare_smul (p : ℕ) (c : ℝ) (u : N07aIntervalL2) :
    n07aCylinderSquare p (c • u) = c ^ 2 * n07aCylinderSquare p u := by
  rw [n07aCylinderSquare_eq, n07aCylinderSquare_eq, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c u] with x hx
  simp only [hx, Pi.smul_apply, smul_eq_mul]
  ring

theorem n07aCylinderSquare_antitone {p q : ℕ} (hpq : p ≤ q)
    (u : N07aIntervalL2) : n07aCylinderSquare q u ≤ n07aCylinderSquare p u := by
  rw [n07aCylinderSquare_eq, n07aCylinderSquare_eq]
  apply integral_mono_ae (n07aCylinderSquare_integrable q u)
    (n07aCylinderSquare_integrable p u)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hx' := Ioo_subset_Icc_self hx
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hpq
  have hsmall : cylinderWeight x ^ r ≤ 1 :=
    pow_le_one₀ (cylinderWeight_nonneg hx') (cylinderWeight_le_one hx')
  have h := mul_le_mul_of_nonneg_left hsmall
    (pow_nonneg (cylinderWeight_nonneg hx') p)
  simpa only [pow_add, mul_one] using mul_le_mul_of_nonneg_right h (sq_nonneg (u x))

theorem n07aCylinderEnergy_terms (j : ℝ) (u d dd : N07aIntervalL2) :
    n07aCylinderSquare 2 d ≤ n07aCylinderEnergy j u d dd ∧
    (1 + j ^ 2) * n07aCylinderSquare 3 u ≤ n07aCylinderEnergy j u d dd ∧
    n07aCylinderSquare 4 dd ≤ n07aCylinderEnergy j u d dd ∧
    (1 + j ^ 2) ^ 2 * n07aCylinderSquare 6 u ≤ n07aCylinderEnergy j u d dd ∧
    (1 + j ^ 2) * n07aCylinderSquare 5 d ≤ n07aCylinderEnergy j u d dd := by
  have h₂ := n07aCylinderSquare_nonneg 2 d
  have h₃ := mul_nonneg (by positivity : 0 ≤ 1 + j ^ 2) (n07aCylinderSquare_nonneg 3 u)
  have h₄ := n07aCylinderSquare_nonneg 4 dd
  have h₆ := mul_nonneg (sq_nonneg (1 + j ^ 2)) (n07aCylinderSquare_nonneg 6 u)
  have h₅ := mul_nonneg (by positivity : 0 ≤ 1 + j ^ 2) (n07aCylinderSquare_nonneg 5 d)
  unfold n07aCylinderEnergy
  constructor
  · linarith only [h₂, h₃, h₄, h₆, h₅]
  constructor
  · linarith only [h₂, h₃, h₄, h₆, h₅]
  constructor
  · linarith only [h₂, h₃, h₄, h₆, h₅]
  constructor <;> linarith only [h₂, h₃, h₄, h₆, h₅]

/-- The five terms appearing after expansion of a cubic coefficient
difference are bounded by the same original weak mode energy. -/
theorem n07aCylinderEnergy_weighted_norms (j : ℝ) (u d dd : N07aIntervalL2) :
    ‖n07aCylinderPower 3 dd‖ ^ 2 ≤ n07aCylinderEnergy j u d dd ∧
    ‖n07aCylinderPower 2 d‖ ^ 2 ≤ n07aCylinderEnergy j u d dd ∧
    j ^ 2 * ‖n07aCylinderPower 3 d‖ ^ 2 ≤ n07aCylinderEnergy j u d dd ∧
    j ^ 2 * ‖n07aCylinderPower 2 u‖ ^ 2 ≤ n07aCylinderEnergy j u d dd ∧
    j ^ 4 * ‖n07aCylinderPower 3 u‖ ^ 2 ≤ n07aCylinderEnergy j u d dd := by
  obtain ⟨h₂, h₃, h₄, h₆, h₅⟩ := n07aCylinderEnergy_terms j u d dd
  simp only [n07aCylinderPower_norm_sq, show 2 * 3 = 6 from rfl, show 2 * 2 = 4 from rfl]
  refine ⟨(n07aCylinderSquare_antitone (by norm_num : 4 ≤ 6) dd).trans h₄,
    (n07aCylinderSquare_antitone (by norm_num : 2 ≤ 4) d).trans h₂, ?_, ?_, ?_⟩
  · exact (mul_le_mul
      (by nlinarith : j ^ 2 ≤ 1 + j ^ 2)
      (n07aCylinderSquare_antitone (by norm_num : 5 ≤ 6) d)
      (n07aCylinderSquare_nonneg 6 d) (by positivity)).trans h₅
  · exact (mul_le_mul
      (by nlinarith : j ^ 2 ≤ 1 + j ^ 2)
      (n07aCylinderSquare_antitone (by norm_num : 3 ≤ 4) u)
      (n07aCylinderSquare_nonneg 4 u) (by positivity)).trans h₃
  · exact (mul_le_mul_of_nonneg_right
      (by nlinarith [sq_nonneg j] : j ^ 4 ≤ (1 + j ^ 2) ^ 2)
      (n07aCylinderSquare_nonneg 6 u)).trans h₆

end ContinuousFlexibility.Analysis
