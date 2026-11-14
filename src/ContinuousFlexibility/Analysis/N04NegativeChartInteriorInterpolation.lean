import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization
import ContinuousFlexibility.Analysis.N04NegativeChartTransportAngularBounds

/-! Two scalar steps preserve the common interior interpolation budget. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem n04NegativeChart_angular_scale_mono
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    {B₀ B D₀ D K N k b : ℕ} (hB : B₀ ≤ B) (hD : D₀ ≤ D) (x w : E) :
    (1 + p (N + K * (D - D₀) + K * D₀ + B₀ + 1) x +
      p (N + K * (D - D₀) + K * D₀ + B₀ + 1) w) ^
        (((b + k * D₀ : ℕ) : ℝ) / ((N + K * (D - D₀) + K * D₀ : ℕ) + 1 : ℝ)) ≤
    (1 + p (N + K * D + B + 1) x + p (N + K * D + B + 1) w) ^
        (((b + k * D : ℕ) : ℝ) / ((N + K * D : ℕ) + 1 : ℝ)) := by
  have hsum : N + K * (D - D₀) + K * D₀ = N + K * D := by
    rw [Nat.add_assoc, ← Nat.mul_add, Nat.sub_add_cancel hD]
  rw [hsum]
  have hscale : 1 + p (N + K * D + B₀ + 1) x + p (N + K * D + B₀ + 1) w ≤
      1 + p (N + K * D + B + 1) x + p (N + K * D + B + 1) w :=
    add_le_add (add_le_add le_rfl (hp (by omega) x)) (hp (by omega) w)
  have hscaleOne : 1 ≤ 1 + p (N + K * D + B + 1) x + p (N + K * D + B + 1) w :=
    (le_add_of_nonneg_right (apply_nonneg _ _)).trans
      (le_add_of_nonneg_right (apply_nonneg _ _))
  have hdegree : ((b + k * D₀ : ℕ) : ℝ) / ((N + K * D : ℕ) + 1 : ℝ) ≤
      ((b + k * D : ℕ) : ℝ) / ((N + K * D : ℕ) + 1 : ℝ) :=
    div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (Nat.add_le_add_left (Nat.mul_le_mul_left k hD) b)) (by positivity)
  exact (Real.rpow_le_rpow (by positivity) hscale (by positivity)).trans
    (Real.rpow_le_rpow_of_exponent_le hscaleOne hdegree)

/-- A first jet on the same normalized segment controls order zero
without changing the distributed spatial power. Positive jets are equal. -/
theorem n04NegativeChart_raw_reference_difference
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : E → ℝ}
    (J : SmoothDirections U f) (Jd : SmoothDirections U (fun x => f x - f 0))
    (p : ℕ → Seminorm ℝ E) (base high : ℕ)
    (hc : Convex ℝ U) (hzero : (0 : E) ∈ U)
    {k : ℕ} {x : E} (hx : x ∈ U) (hlow : p base x ≤ 1)
    (v : Fin k → E) (hv : ∀ i, p base (v i) ≤ 1)
    {R M : ℝ} (hhigh : p high x ≤ R) (hvh : ∀ i, p high (v i) ≤ R)
    (hb : ∀ j : ℕ, j ≤ max 1 k → 0 < j → ∀ y ∈ U, p base y ≤ 1 →
      ∀ u : Fin j → E, (∀ i, p base (u i) ≤ 1) → p high y ≤ R →
        (∀ i, p high (u i) ≤ R) → ‖J.D j y u‖ ≤ M) :
    ‖Jd.D k x v‖ ≤ M := by
  by_cases hk : k = 0
  · subst k
    rw [smoothDirections_D_zero_apply Jd hx v]
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, (0 : E) + t • x ∈ U := by
      intro t ht
      have h := hc hzero hx (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
      simpa only [smul_zero] using h
    have hscale (q : Seminorm ℝ E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
        q ((0 : E) + t • x) ≤ q x := by
      rw [zero_add, map_smul_eq_mul, Real.norm_of_nonneg ht.1]
      exact mul_le_of_le_one_left (apply_nonneg _ _) ht.2
    have hd := smoothDirections_abs_sub_le_of_firstJet_bound J hseg (fun t ht => by
      have hh := hb 1 (le_max_left _ _) zero_lt_one _ (hseg t ht)
        ((hscale (p base) ht).trans hlow) (Fin.cons x Fin.elim0)
        (fun i => Fin.cases hlow (fun j => Fin.elim0 j) i)
        ((hscale (p high) ht).trans hhigh)
        (fun i => Fin.cases hhigh (fun j => Fin.elim0 j) i)
      simpa only [Real.norm_eq_abs] using hh)
    simpa only [zero_add, Real.norm_eq_abs] using hd
  · rw [smoothDirections_D_sub_constant J Jd (Nat.pos_of_ne_zero hk) hx v]
    exact hb k (le_max_right _ _) (Nat.pos_of_ne_zero hk) x hx hlow v hv hhigh hvh

end ContinuousFlexibility.Analysis
