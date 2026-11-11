import ContinuousFlexibility.Radial.InnerCoefficientWeights

/-!
# The fixed coefficient loss in the two inner inverse estimates

Two local reciprocal weight comparisons cost one fixed power of the cell
coefficient. The loss exponent therefore depends on the unweighted local
Dirichlet exponent, not on the weight exponent selected before N.
Fixed multiplicative constants in the coarse estimate are absorbed into
one further coefficient power, uniformly over all later transition cells.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

theorem inner_dirichlet_coefficient_cost {K R g p : ℝ} (m : ℕ)
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hg : 0 ≤ g)
    (hRbound : R ≤ sqrt (radialE m)) (hgbound : g ≤ K * radialE m ^ p) :
    R ^ 2 * g ≤ K * radialE m ^ (p + 1) := by
  have hE : 0 < radialE m := exp_pos _
  have hRsq : R ^ 2 ≤ radialE m := by
    simpa only [sq_sqrt hE.le] using
      (sq_le_sq₀ hR (sqrt_nonneg _)).mpr hRbound
  calc
    R ^ 2 * g ≤ radialE m * (K * radialE m ^ p) :=
      mul_le_mul hRsq hgbound hg hE.le
    _ = K * radialE m ^ (p + 1) := by
      rw [rpow_add hE, rpow_one]
      ring

/-- The exponent ℓ can be fixed once the local unweighted exponent p is
known. All dependence on the chosen first index remains in the constant. -/
theorem inner_dirichlet_fixed_loss_cost {K R g p ℓ : ℝ} {N m : ℕ}
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hg : 0 ≤ g)
    (hRbound : R ≤ sqrt (radialE m)) (hgbound : g ≤ K * radialE m ^ p)
    (hm : N ≤ m) (hℓ : p + 1 ≤ ℓ) :
    innerCoefficientLoss N ℓ m * (R ^ 2 * g) ≤ K * radialE N ^ (p + 1) := by
  calc
    _ ≤ innerCoefficientLoss N ℓ m * (K * radialE m ^ (p + 1)) :=
      mul_le_mul_of_nonneg_left
        (inner_dirichlet_coefficient_cost m hK hR hg hRbound hgbound)
        (innerCoefficientLoss_pos N ℓ m).le
    _ = K * (innerCoefficientLoss N ℓ m * radialE m ^ (p + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (innerCoefficientLoss_absorb hm hℓ) hK

theorem inner_dirichlet_coarse_cost {K R g p : ℝ} {m n : ℕ}
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hg : 0 ≤ g) (hp : 0 ≤ p)
    (hRbound : R ≤ sqrt (radialE m)) (hgbound : g ≤ K * radialE m ^ p)
    (hmn : m ≤ n) :
    R ^ 2 * g ≤ K * radialE n ^ (p + 1) :=
  (inner_dirichlet_coefficient_cost m hK hR hg hRbound hgbound).trans
    (mul_le_mul_of_nonneg_left
      (inner_coefficient_power_le hmn (by linarith : 0 ≤ p + 1)) hK)

/-- Fixed constants can be absorbed without allowing an exponent to
depend on n or j. -/
theorem inner_coefficient_absorb_constant {K p : ℝ} (hK : 0 ≤ K)
    {n : ℕ} (hQ : 1 ≤ radialQ n) :
    K * radialE n ^ p ≤ radialE n ^ (p + (K + 1)) := by
  have hE : 0 < radialE n := exp_pos _
  have hKq : K + 1 ≤ (K + 1) * radialQ n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hQ (by linarith : 0 ≤ K + 1)
  have hKexp : K ≤ exp ((K + 1) * radialQ n) := by
    have h := add_one_le_exp ((K + 1) * radialQ n)
    linarith only [h, hKq]
  have hpower : K ≤ radialE n ^ (K + 1) := by
    rw [radialE, ← exp_mul]
    simpa only [mul_comm] using hKexp
  calc
    K * radialE n ^ p ≤ radialE n ^ (K + 1) * radialE n ^ p :=
      mul_le_mul_of_nonneg_right hpower (rpow_pos_of_pos hE p).le
    _ = radialE n ^ ((K + 1) + p) := (rpow_add hE _ _).symm
    _ = radialE n ^ (p + (K + 1)) := by
      congr 1
      ring

/-- The coefficient cost of the local inverse and the bounded Poisson
correction give precisely the coarse form E_n^C. -/
theorem inner_coefficient_absorb_cost_and_correction {K C p : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hp : 0 ≤ p) {n : ℕ} (hQ : 1 ≤ radialQ n) :
    K * radialE n ^ p + C ≤ radialE n ^ (p + (K + C + 1)) := by
  have hEpow : 1 ≤ radialE n ^ p := by
    rw [radialE, ← exp_mul, one_le_exp_iff]
    exact mul_nonneg (zero_le_one.trans hQ) hp
  calc
    _ ≤ K * radialE n ^ p + C * radialE n ^ p := by
      exact add_le_add (le_refl _) (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hEpow hC)
    _ = (K + C) * radialE n ^ p := by ring
    _ ≤ _ := inner_coefficient_absorb_constant (add_nonneg hK hC) hQ

end ContinuousFlexibility.Radial
