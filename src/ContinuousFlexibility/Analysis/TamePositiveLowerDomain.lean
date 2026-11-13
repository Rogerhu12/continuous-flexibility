import ContinuousFlexibility.Statements.Analysis

/-!
# A common open domain below a positive affine lower bound

Scaling the original linear data gives an open domain containing every
point with the prescribed lower bound. Its smaller positive lower bound
is fixed before any derivative order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

variable {E I J : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem exists_open_lower_domain_of_smul
    (d : E → I → J → ℝ) (V : Set E) (hV : IsOpen V)
    (hmem : ∀ e, e ∈ V ↔ ∀ i j, 0 < 1 + d e i j)
    (hsmul : ∀ c e i j, d (c • e) i j = c * d e i j)
    (a : ℝ) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∃ U : Set E, IsOpen U ∧ U ⊆ V ∧
      (∀ e, (∀ i j, a ≤ 1 + d e i j) → e ∈ U) ∧
      ∀ e ∈ U, ∀ i j, c ≤ 1 + d e i j := by
  let c : ℝ := min a 1 / 2
  let t : ℝ := 1 - c
  have hc : 0 < c := half_pos (lt_min ha zero_lt_one)
  have hca : c < a := (half_lt_self (lt_min ha zero_lt_one)).trans_le (min_le_left _ _)
  have ht : 0 < t := by
    have hmin : min a 1 ≤ 1 := min_le_right _ _
    dsimp only [t, c]
    linarith
  let U : Set E := (fun e : E => t⁻¹ • e) ⁻¹' V
  have hU : IsOpen U := hV.preimage (continuous_const.smul continuous_id)
  have hprod (b : ℝ) : (1 + t⁻¹ * b) * t = t + b := by
    calc
      _ = t + (t⁻¹ * t) * b := by ring
      _ = t + b := by rw [inv_mul_cancel₀ ht.ne', one_mul]
  have hlow (e : E) (he : e ∈ U) (i : I) (j : J) :
      c < 1 + d e i j := by
    have hh : 0 < 1 + d (t⁻¹ • e) i j := (hmem _).mp he i j
    rw [hsmul] at hh
    have hp := mul_pos hh ht
    rw [hprod] at hp
    dsimp only [t] at hp
    linarith
  refine ⟨c, hc, U, hU, ?_, ?_, ?_⟩
  · intro e he
    exact (hmem e).mpr (fun i j => hc.trans (hlow e he i j))
  · intro e he
    apply (hmem (t⁻¹ • e)).mpr
    intro i j
    rw [hsmul]
    by_contra hn
    have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) ht.le
    rw [hprod] at hp
    have hh := he i j
    dsimp only [t] at hp
    linarith
  · intro e he i j
    exact (hlow e he i j).le

end ContinuousFlexibility.Analysis
