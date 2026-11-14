module

public import ContinuousFlexibility.Radial.TailMassResistanceData

/-!
# Quantitative consequences of the two-sided deep-tail bounds

The two large mass--resistance products are both needed: one controls the
relative length of the mass interval in resistance coordinates, and the other
controls the same error after shifting the mass weight to the next node.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

/-- The squared resistance error is stable under either neighboring mass.
This algebraic lemma also applies to the preceding gap, so mass recovery
does not require a second orientation-specific argument. -/
theorem tail_weighted_resistance_square_bound {Λ μ ν I R η K : ℝ}
    (hμ : 0 < μ) (hν : 0 < ν) (hI : 0 ≤ I) (hR : 0 < R)
    (hη : 0 ≤ η) (hK : 0 < K) (hsmall : Λ * μ * I ≤ η)
    (hleft : K ≤ Λ * μ * R) (hright : K ≤ Λ * ν * R) :
    μ * (I / R) ^ 2 ≤ (η / K) ^ 2 * ν := by
  have hr : I / R ≤ η / K := by
    calc
      I / R = I * R⁻¹ := div_eq_mul_inv _ _
      _ ≤ I * (Λ * μ / K) :=
        mul_le_mul_of_nonneg_left (tail_inverse_resistance_bound hK hR hleft) hI
      _ = (Λ * μ * I) / K := by ring
      _ ≤ η / K := div_le_div_of_nonneg_right hsmall hK.le
  have hmr : μ * (I / R) ≤ η * ν / K := by
    calc
      μ * (I / R) = (μ * I) * R⁻¹ := by ring
      _ ≤ (μ * I) * (Λ * ν / K) :=
        mul_le_mul_of_nonneg_left (tail_inverse_resistance_bound hK hR hright)
          (mul_nonneg hμ.le hI)
      _ = (Λ * μ * I) * ν / K := by ring
      _ ≤ η * ν / K := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsmall hν.le) hK.le
  calc
    μ * (I / R) ^ 2 = (μ * (I / R)) * (I / R) := by ring
    _ ≤ (η * ν / K) * (η / K) :=
      mul_le_mul hmr hr (div_nonneg hI hR.le)
        (div_nonneg (mul_nonneg hη hν.le) hK.le)
    _ = _ := by ring

theorem deepTail_inner_resistance_ratio_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    tailInnerResistance T n / tailResistance T n ≤ T.η / T.K := by
  have hK : 0 < T.K := lt_trans zero_lt_one hT.2.2.2.2.2.2.1
  calc
    _ = tailInnerResistance T n * (tailResistance T n)⁻¹ := div_eq_mul_inv _ _
    _ ≤ tailInnerResistance T n * (T.Λ * tailMass T n / T.K) :=
      mul_le_mul_of_nonneg_left (deepTail_inverse_resistance_left hT n)
        (tailInnerResistance_pos hT n).le
    _ = (T.Λ * tailMass T n * tailInnerResistance T n) / T.K := by ring
    _ ≤ T.η / T.K :=
      div_le_div_of_nonneg_right (deepTail_mass_resistance_small hT n) hK.le

theorem deepTail_weighted_inner_resistance_ratio_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    tailMass T n * (tailInnerResistance T n / tailResistance T n) ≤
      T.η * tailMass T (n + 1) / T.K := by
  have hK : 0 < T.K := lt_trans zero_lt_one hT.2.2.2.2.2.2.1
  calc
    _ = (tailMass T n * tailInnerResistance T n) * (tailResistance T n)⁻¹ := by ring
    _ ≤ (tailMass T n * tailInnerResistance T n) *
        (T.Λ * tailMass T (n + 1) / T.K) :=
      mul_le_mul_of_nonneg_left (deepTail_inverse_resistance_right hT n)
        (mul_nonneg (tailMass_pos hT n).le (tailInnerResistance_pos hT n).le)
    _ = (T.Λ * tailMass T n * tailInnerResistance T n) *
        tailMass T (n + 1) / T.K := by ring
    _ ≤ T.η * tailMass T (n + 1) / T.K :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (deepTail_mass_resistance_small hT n)
          (tailMass_pos hT (n + 1)).le) hK.le

/-- The small mass-side interpolation error is still small after shifting
from the left node's mass to the right node's mass. -/
theorem deepTail_shifted_inner_resistance_sq_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    tailMass T n * (tailInnerResistance T n / tailResistance T n) ^ 2 ≤
      (T.η / T.K) ^ 2 * tailMass T (n + 1) := by
  have hr : 0 ≤ tailInnerResistance T n / tailResistance T n :=
    (div_pos (tailInnerResistance_pos hT n) (tailResistance_pos hT n)).le
  have hηK : 0 ≤ T.η / T.K := div_nonneg hT.2.2.2.2.1.le
    (lt_trans zero_lt_one hT.2.2.2.2.2.2.1).le
  calc
    _ = (tailMass T n * (tailInnerResistance T n / tailResistance T n)) *
        (tailInnerResistance T n / tailResistance T n) := by ring
    _ ≤ (T.η * tailMass T (n + 1) / T.K) * (T.η / T.K) :=
      mul_le_mul (deepTail_weighted_inner_resistance_ratio_le hT n)
        (deepTail_inner_resistance_ratio_le hT n) hr
        (by simpa only [div_mul_eq_mul_div] using
          mul_nonneg hηK (tailMass_pos hT (n + 1)).le)
    _ = _ := by ring

/-- For recovery of node values from a physical solution, the same estimate
controls the current mass error by the preceding node's mass. -/
theorem deepTail_previous_gap_mass_error {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    tailMass T (n + 1) *
        (tailInnerResistance T (n + 1) / tailResistance T n) ^ 2 ≤
      (T.η / T.K) ^ 2 * tailMass T n :=
  tail_weighted_resistance_square_bound
    (tailMass_pos hT (n + 1)) (tailMass_pos hT n)
    (tailInnerResistance_pos hT (n + 1)).le (tailResistance_pos hT n)
    hT.2.2.2.2.1.le (lt_trans zero_lt_one hT.2.2.2.2.2.2.1)
    (deepTail_mass_resistance_small hT (n + 1))
    (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.2.1
    (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.1

/-- Fixed numerical margins sufficient for all Poisson diagonal estimates. -/
theorem tail_poisson_factors_small {η K : ℝ}
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 16) (hK : 32 ≤ K) :
    (3 / 4 : ℝ) ≤ (1 - η / K) ^ 2 ∧
      (1 + η) / (1 - η) ≤ (3 / 2 : ℝ) ∧
      (η + (η / K) ^ 2) / (1 - η) ≤ (1 / 4 : ℝ) ∧
      2 / K ≤ (1 / 4 : ℝ) := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hK
  have hden : 0 < 1 - η := by linarith only [hηsmall]
  have hratio₀ : 0 ≤ η / K := div_nonneg hη hKpos.le
  have hratio : η / K ≤ 1 / 16 :=
    (div_le_self hη (by linarith only [hK])).trans hηsmall
  have hsq : (η / K) ^ 2 ≤ (1 / 16 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hratio₀ hratio 2
  refine ⟨?_, (div_le_iff₀ hden).mpr ?_, (div_le_iff₀ hden).mpr ?_,
    (div_le_iff₀ hKpos).mpr ?_⟩
  · nlinarith only [hratio, sq_nonneg (η / K)]
  · linarith only [hηsmall]
  · nlinarith only [hηsmall, hsq]
  · linarith only [hK]

/-- Subtracting the two free edge terms preserves diagonal dominance. -/
theorem tail_node_diagonal_bounds {A K q₀ q₁ r₀ r₁ : ℝ}
    (hA : 0 < A) (hK : 32 ≤ K)
    (hq₀ : (3 / 4 : ℝ) * A ≤ q₀ ∧ q₀ ≤ (3 / 2 : ℝ) * A)
    (hq₁ : 0 ≤ q₁ ∧ q₁ ≤ (1 / 4 : ℝ) * A)
    (hr₀ : 0 ≤ r₀ ∧ r₀ ≤ A / K) (hr₁ : 0 ≤ r₁ ∧ r₁ ≤ A / K) :
    A / 2 ≤ q₀ + q₁ - r₀ - r₁ ∧ q₀ + q₁ - r₀ - r₁ ≤ 2 * A := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hK
  have hAK : A / K ≤ A / 8 :=
    div_le_div_of_nonneg_left hA.le (by norm_num) (by linarith only [hK])
  constructor
  · linarith only [hq₀.1, hq₁.1, hr₀.2, hr₁.2, hAK]
  · linarith only [hq₀.2, hq₁.2, hr₀.1, hr₁.1, hA]

theorem deepTail_inner_edge_ratio_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    tailInnerResistance T n / (tailInnerResistance T n + tailResistance T n) ≤
      T.η / T.K := by
  apply le_trans _ (deepTail_inner_resistance_ratio_le hT n)
  exact div_le_div_of_nonneg_left (tailInnerResistance_pos hT n).le
    (tailResistance_pos hT n) (le_add_of_nonneg_left (tailInnerResistance_pos hT n).le)

theorem deepTail_shifted_inner_edge_sq_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    tailMass T n *
        (tailInnerResistance T n / (tailInnerResistance T n + tailResistance T n)) ^ 2 ≤
      (T.η / T.K) ^ 2 * tailMass T (n + 1) := by
  apply le_trans _ (deepTail_shifted_inner_resistance_sq_le hT n)
  apply mul_le_mul_of_nonneg_left _ (tailMass_pos hT n).le
  apply pow_le_pow_left₀
    (div_nonneg (tailInnerResistance_pos hT n).le
      (add_pos (tailInnerResistance_pos hT n) (tailResistance_pos hT n)).le)
  exact div_le_div_of_nonneg_left (tailInnerResistance_pos hT n).le
    (tailResistance_pos hT n) (le_add_of_nonneg_left (tailInnerResistance_pos hT n).le)

/-- Replacing a gap resistance by the full edge resistance improves either
of the inverse-resistance bounds. -/
theorem deepTail_inverse_edge_le_inverse_gap {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    (tailInnerResistance T n + tailResistance T n)⁻¹ ≤ (tailResistance T n)⁻¹ := by
  simpa only [one_div] using one_div_le_one_div_of_le (tailResistance_pos hT n)
    (le_add_of_nonneg_left (tailInnerResistance_pos hT n).le)

theorem deepTail_inverse_edge_left {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    (tailInnerResistance T n + tailResistance T n)⁻¹ ≤ T.Λ * tailMass T n / T.K :=
  (deepTail_inverse_edge_le_inverse_gap hT n).trans (deepTail_inverse_resistance_left hT n)

theorem deepTail_inverse_edge_right {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    (tailInnerResistance T n + tailResistance T n)⁻¹ ≤ T.Λ * tailMass T (n + 1) / T.K :=
  (deepTail_inverse_edge_le_inverse_gap hT n).trans (deepTail_inverse_resistance_right hT n)

end ContinuousFlexibility.Radial
