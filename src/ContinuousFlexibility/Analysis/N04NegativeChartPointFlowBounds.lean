import ContinuousFlexibility.Analysis.N04NegativeGeometrySpatialFlowPrefix

/-!
# Spatial flow powers using only one physical radial fiber

All numerical bounds concern the same radial parameters and every
angle on their trajectory. A smooth extension may be used to construct
the actual local flow, but no estimate outside the physical half enters
its spatial jet bound. The original whole-box theorem is unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- The finite weighted prefix uses only original field jets on the
fixed radial fiber. Higher raw bounds are witnesses for the genuine
smooth field and do not enter the output polynomial. -/
theorem n04NegativeChart_flow_spatial_point_weighted_prefix (Λ : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧ ∀ {A ρ : ℝ}, 1 ≤ A → 1 ≤ ρ →
      ∀ (F : ℝ × N04FlowPoint → ℝ), ContDiff ℝ ∞ F →
      (∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi) →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ, N04FlowEquations F Θ →
      ∀ q : N04FlowPoint, ∀ M : ℕ → ℝ, (∀ j, 0 ≤ M j) →
      (∀ j, ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ,
        ‖iteratedFDeriv ℝ (j + 1) (fun y : N04FlowPoint => F (t, y)) (q.1, θ)‖ ≤ M j) →
      ∀ α : ℝ → ℝ, ContinuousOn α (Icc (0 : ℝ) 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ α t) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ θ,
        |deriv (fun η => F (t, (q.1, η))) θ| ≤ α t) →
      (∫ t in (0 : ℝ)..1, α t) ≤ Λ →
      (∀ j, j ≤ N → ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ,
        ‖iteratedFDeriv ℝ (j + 1) (fun y : N04FlowPoint => F (t, y)) (q.1, θ)‖ ≤
          A * ρ ^ j) →
      ∀ k, k ≤ N → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (k + 1) (fun y : N04FlowPoint => Θ y.1 t y.2) q‖ ≤
          C * A ^ e * ρ ^ k := by
  classical
  choose P hP hflow using fun k => exists_n04Flow_spatialJet_point_polynomial Λ k
  choose c e hc hpoly using fun k =>
    n04NegativeGeometry_flowPolynomial_weighted_prefix (P k) k (hP k)
  let C : ℝ := 1 + ∑ i : Fin (N + 1), c i.val
  let d : ℕ := ∑ i : Fin (N + 1), e i.val
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => zero_le_one.trans (hc i.val))
  have hcC (k : ℕ) (hk : k ≤ N) : c k ≤ C :=
    (Finset.single_le_sum (fun i _ => zero_le_one.trans (hc i.val))
      (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (N + 1)))).trans
      (le_add_of_nonneg_left zero_le_one)
  have hed (k : ℕ) (hk : k ≤ N) : e k ≤ d :=
    Finset.single_le_sum (fun (i : Fin (N + 1)) _ => Nat.zero_le (e i.val))
      (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (N + 1)))
  refine ⟨C, d, hC, ?_⟩
  intro A ρ hA hρ F hF hperiod Θ hΘ q M hM hraw α hα hα0 hαbound hΛ hprefix
    k hk t ht
  let R : ℕ → ℝ := fun j => if j ≤ N then A * ρ ^ j else M j
  have hR (j : ℕ) : 0 ≤ R j := by
    by_cases hj : j ≤ N
    · simpa only [R, if_pos hj] using
        mul_nonneg (zero_le_one.trans hA) (pow_nonneg (zero_le_one.trans hρ) j)
    · simpa only [R, if_neg hj] using hM j
  have hrawR (j : ℕ) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
      ‖iteratedFDeriv ℝ (j + 1) (fun y : N04FlowPoint => F (r, y)) (q.1, θ)‖ ≤ R j := by
    by_cases hj : j ≤ N
    · simpa only [R, if_pos hj] using hprefix j hj r hr θ
    · simpa only [R, if_neg hj] using hraw j r hr θ
  have hjet := hflow k R hR F hF hperiod Θ hΘ q hrawR
    α hα hα0 hαbound hΛ t ht
  have hnum : flowJetPolynomialEval (P k) R ≤ c k * A ^ e k * ρ ^ k :=
    hpoly k hA hρ R hR (fun j hj => by
      simp only [R, if_pos (hj.trans hk), le_refl])
  exact hjet.trans (hnum.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (hcC k hk) (pow_le_pow_right₀ hA (hed k hk))
      (pow_nonneg (zero_le_one.trans hA) _) (zero_le_one.trans hC))
    (pow_nonneg (zero_le_one.trans hρ) _)))

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_flow_spatial_point_weighted_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_flow_spatial_point_weighted_prefix
