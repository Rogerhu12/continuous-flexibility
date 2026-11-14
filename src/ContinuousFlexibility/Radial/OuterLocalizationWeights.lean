module

public import ContinuousFlexibility.Radial.DeepTailPhysicalWeights
public import ContinuousFlexibility.Radial.OuterEnvelope

/-!
# Actual cell labels and nearby edge weights

The two-cell displacement between a localizer label and a deep-tail edge
costs a coefficient power.  The coefficient of the cubic attenuation
remains exactly one.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

theorem outer_radialS_shift_two_bound {n : ℕ} (hn : 1 ≤ n) :
    radialS (n + 2) - radialS n ≤ 18 * radialQ n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have heq : radialS (n + 2) - radialS n =
      4 * (n : ℝ) ^ 2 + 8 * n + 16 / 3 := by
    unfold radialS
    push_cast
    ring
  calc
    _ = 4 * (n : ℝ) ^ 2 + 8 * n + 16 / 3 := heq
    _ ≤ 18 * (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (outer_nat_sq_le_radialQ hn) (by norm_num)

theorem outer_radialS_nearby_bound {p i : ℕ} (hp : 1 ≤ p) (hi : 1 ≤ i)
    (hpi : p ≤ i + 2) (hip : i ≤ p + 2) :
    |radialS p - radialS i| ≤ 18 * radialQ i := by
  rcases le_total p i with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (radialS_monotone h))]
    calc
      _ = radialS i - radialS p := by ring
      _ ≤ radialS (p + 2) - radialS p := sub_le_sub_right (radialS_monotone hip) _
      _ ≤ 18 * radialQ p := outer_radialS_shift_two_bound hp
      _ ≤ _ := mul_le_mul_of_nonneg_left (radialQ_monotone h) (by norm_num)
  · rw [abs_of_nonneg (sub_nonneg.mpr (radialS_monotone h))]
    exact (sub_le_sub_right (radialS_monotone hpi) _).trans
      (outer_radialS_shift_two_bound hi)

/-- Moving each endpoint by at most two labels preserves full cubic decay. -/
theorem outer_attenuation_nearby {p q i k : ℕ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hi : 1 ≤ i) (hk : 1 ≤ k)
    (hpi : p ≤ i + 2) (hip : i ≤ p + 2)
    (hqk : q ≤ k + 2) (hkq : k ≤ q + 2) :
    exp (-|radialS p - radialS q|) ≤
      radialE i ^ (18 : ℝ) * radialE k ^ (18 : ℝ) *
        exp (-|radialS i - radialS k|) := by
  have hleft : |radialS i - radialS p| ≤ 18 * radialQ i := by
    rw [abs_sub_comm]
    exact outer_radialS_nearby_bound hp hi hpi hip
  have hright := outer_radialS_nearby_bound hq hk hqk hkq
  have htriangle := abs_sub_le (radialS i) (radialS p) (radialS k)
  have htriangle' := abs_sub_le (radialS p) (radialS q) (radialS k)
  rw [outer_radialE_rpow, outer_radialE_rpow, ← exp_add, ← exp_add]
  exact exp_le_exp.mpr (by linarith)

/-- A fixed scalar prefactor is absorbed by one positive cell weight. -/
theorem outer_prefactor_le_envelope {n : ℕ} (hn : 1 ≤ n) {A : ℝ} (hA : 0 ≤ A) :
    A ≤ radialE n ^ A := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ : 1 ≤ radialQ n :=
    (show (1 : ℝ) ≤ (n : ℝ) ^ 2 by nlinarith).trans (outer_nat_sq_le_radialQ hn)
  rw [outer_radialE_rpow]
  calc
    A ≤ exp A := by linarith [add_one_le_exp A]
    _ ≤ _ := exp_le_exp.mpr (le_mul_of_one_le_right hA hQ)

/-- A coefficient weight at a nearby edge is a fixed power of the cell weight. -/
theorem outer_coefficient_weight_nearby {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ p i : ℕ, 1 ≤ i → p ≤ i + 2 →
      radialE p ^ A ≤ radialE i ^ C := by
  obtain ⟨C, hC, hshift⟩ := physicalWeight_shift A hA 2
  refine ⟨2 * C, by positivity, ?_⟩
  intro p i hi hpi
  calc
    radialE p ^ A ≤ radialE (i + 2) ^ A := by
      rw [outer_radialE_rpow, outer_radialE_rpow]
      exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (radialQ_monotone hpi) hA)
    _ ≤ C * radialE i ^ C := hshift i
    _ ≤ radialE i ^ C * radialE i ^ C :=
      mul_le_mul_of_nonneg_right (outer_prefactor_le_envelope hi hC.le)
        (rpow_nonneg (exp_pos _).le _)
    _ = radialE i ^ (2 * C) := by
      rw [← rpow_add (show 0 < radialE i from exp_pos _)]
      congr 1
      ring

end ContinuousFlexibility.Radial
