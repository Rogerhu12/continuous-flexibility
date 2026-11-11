import ContinuousFlexibility.Radial.OuterFirstOrderState

/-!
# Operator norms of the actual value/flux transfer

The product space carries its usual maximum norm. The manuscript uses
the Euclidean state energy, so both comparisons are proved explicitly.
The transfer below is the solution operator of the actual differential
equation, including its inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real

set_option backward.isDefEq.respectTransparency false

def outerStateEnergy (v : ℝ × ℝ) : ℝ := v.1 ^ 2 + v.2 ^ 2

theorem outerStateEnergy_nonneg (v : ℝ × ℝ) : 0 ≤ outerStateEnergy v := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem norm_sq_le_outerStateEnergy (v : ℝ × ℝ) :
    ‖v‖ ^ 2 ≤ outerStateEnergy v := by
  change (max |v.1| |v.2|) ^ 2 ≤ v.1 ^ 2 + v.2 ^ 2
  rcases le_total |v.1| |v.2| with h | h
  · rw [max_eq_right h, sq_abs]
    nlinarith [sq_nonneg v.1]
  · rw [max_eq_left h, sq_abs]
    nlinarith [sq_nonneg v.2]

theorem outerStateEnergy_le_two_norm_sq (v : ℝ × ℝ) :
    outerStateEnergy v ≤ 2 * ‖v‖ ^ 2 := by
  have h1 : |v.1| ≤ ‖v‖ := le_max_left _ _
  have h2 : |v.2| ≤ ‖v‖ := le_max_right _ _
  have hs1 := (sq_le_sq₀ (abs_nonneg v.1) (norm_nonneg v)).2 h1
  have hs2 := (sq_le_sq₀ (abs_nonneg v.2) (norm_nonneg v)).2 h2
  rw [sq_abs] at hs1 hs2
  dsimp only [outerStateEnergy]
  linarith

theorem outerStateOperator_norm_le {A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)} {L : ℝ}
    (hL : 0 ≤ L) (h : ∀ v, outerStateEnergy (A v) ≤ L * outerStateEnergy v) :
    ‖A‖ ≤ sqrt (2 * L) := by
  apply A.opNorm_le_bound (sqrt_nonneg _)
  intro v
  have hh : ‖A v‖ ^ 2 ≤ (sqrt (2 * L) * ‖v‖) ^ 2 := by
    calc
      _ ≤ outerStateEnergy (A v) := norm_sq_le_outerStateEnergy _
      _ ≤ L * outerStateEnergy v := h v
      _ ≤ L * (2 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (outerStateEnergy_le_two_norm_sq v) hL
      _ = _ := by rw [mul_pow, sq_sqrt (by positivity : 0 ≤ 2 * L)]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).1 hh

/-- A two-sided energy estimate controls the genuine inverse transfer. -/
theorem outerStateEquiv_norms_le {A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)} {L : ℝ}
    (hL : 0 ≤ L)
    (h : ∀ v, outerStateEnergy (A v) ≤ L * outerStateEnergy v ∧
      outerStateEnergy v ≤ L * outerStateEnergy (A v)) :
    ‖A.toContinuousLinearMap‖ + ‖A.symm.toContinuousLinearMap‖ ≤
      2 * sqrt (2 * L) := by
  have hf := outerStateOperator_norm_le (A := A.toContinuousLinearMap) hL (fun v => (h v).1)
  have hi := outerStateOperator_norm_le (A := A.symm.toContinuousLinearMap) hL (by
    intro v
    change outerStateEnergy (A.symm v) ≤ L * outerStateEnergy v
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using (h (A.symm v)).2)
  linarith

/-- No abstract transfer is assumed: every initial state is realized by
the actual first-order ODE before the energy estimate is applied. -/
theorem outerStateTransfer_norms_le
    {a b c d L : ℝ} (hab : a ≤ b)
    {alpha beta : ℝ → ℝ} (halpha : ContinuousOn alpha (Icc a b))
    (hbeta : ContinuousOn beta (Icc a b)) (hc : c ∈ Icc a b) (hd : d ∈ Icc a b)
    (hL : 0 ≤ L)
    (henergy : ∀ u z : ℝ → ℝ, OuterFirstOrderSystem alpha beta u z (Icc a b) →
      outerStateEnergy (u d, z d) ≤ L * outerStateEnergy (u c, z c) ∧
        outerStateEnergy (u c, z c) ≤ L * outerStateEnergy (u d, z d)) :
    ‖(outerStateTransfer hab halpha hbeta hc hd).toContinuousLinearMap‖ +
        ‖(outerStateTransfer hab halpha hbeta hc hd).symm.toContinuousLinearMap‖ ≤
      2 * sqrt (2 * L) := by
  apply outerStateEquiv_norms_le hL
  intro v
  obtain ⟨u, z, hv, hs⟩ := exists_outerFirstOrder_state hab halpha hbeta c v
  have ht := outerStateTransfer_actual hab halpha hbeta hc hd hs
  rw [hv] at ht
  rw [ht]
  simpa only [hv] using henergy u z hs

/-- The harmless finite-dimensional norm constant is absorbed into the
quadratic exponent, uniformly for every positive cell index. -/
theorem outerStateTransfer_norms_le_exp
    {a b c d Q τ : ℝ} {n : ℕ} (hab : a ≤ b) (hn : 1 ≤ n)
    {alpha beta : ℝ → ℝ} (halpha : ContinuousOn alpha (Icc a b))
    (hbeta : ContinuousOn beta (Icc a b)) (hc : c ∈ Icc a b) (hd : d ∈ Icc a b)
    (hQ : 0 ≤ Q) (hτ : 0 ≤ τ)
    (henergy : ∀ u z : ℝ → ℝ, OuterFirstOrderSystem alpha beta u z (Icc a b) →
      outerStateEnergy (u d, z d) ≤ exp (Q * (n : ℝ) ^ 2 + τ) * outerStateEnergy (u c, z c) ∧
        outerStateEnergy (u c, z c) ≤ exp (Q * (n : ℝ) ^ 2 + τ) * outerStateEnergy (u d, z d)) :
    ‖(outerStateTransfer hab halpha hbeta hc hd).toContinuousLinearMap‖ +
        ‖(outerStateTransfer hab halpha hbeta hc hd).symm.toContinuousLinearMap‖ ≤
      exp ((Q + 2) * (n : ℝ) ^ 2 + τ) := by
  let E := exp (Q * (n : ℝ) ^ 2 + τ)
  have hE : 1 ≤ E := one_le_exp_iff.mpr (by positivity)
  have hs : sqrt (2 * E) ≤ 2 * E := by
    have hsq := sq_sqrt (by positivity : 0 ≤ 2 * E)
    nlinarith [sqrt_nonneg (2 * E)]
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
  have he1 : 2 ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have he2 : 4 ≤ exp 2 := by
    have hh : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
    rw [hh]
    nlinarith
  calc
    _ ≤ 2 * sqrt (2 * E) := outerStateTransfer_norms_le hab halpha hbeta hc hd
      (le_of_lt (exp_pos _)) henergy
    _ ≤ 4 * E := by linarith
    _ ≤ exp 2 * E := mul_le_mul_of_nonneg_right he2 (le_of_lt (exp_pos _))
    _ = exp (Q * (n : ℝ) ^ 2 + τ + 2) := by rw [← exp_add]; congr 1; ring
    _ ≤ _ := exp_le_exp.mpr (by nlinarith)

end ContinuousFlexibility.Radial
