import ContinuousFlexibility.Analysis.N04NegativeGeometryFlowCoefficientBounds

/-! A finite composition bound on one physical radial fiber. Its numerical
inputs concern that fiber only; global smoothness supplies the genuine jets. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- The derivative in the transported angle costs one original spatial
derivative. Every positive inner derivative returns one spatial power. -/
theorem n04NegativeChart_angleComposition_point_prefix
    {F : ℝ × N04FlowPoint → ℝ} {Θ : N04FlowPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (hΘ : ContDiff ℝ ∞ Θ)
    (K : ℕ) (t : ℝ) (q : N04FlowPoint) {M B ρ : ℝ}
    (hM : 0 ≤ M) (hB : 1 ≤ B) (hρ : 1 ≤ ρ)
    (hraw : ∀ j, j ≤ K → ∀ θ,
      ‖iteratedFDeriv ℝ (j + 1) (fun y : N04FlowPoint => F (t, y)) (q.1, θ)‖ ≤
        M * ρ ^ j)
    (hflow : ∀ j, 1 ≤ j → j ≤ K →
      ‖iteratedFDeriv ℝ j Θ q‖ ≤ B * ρ ^ (j - 1)) :
    ∀ j, j ≤ K →
      ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
        deriv (fun θ => F (t, (y.1, θ))) (Θ y)) q‖ ≤
          ((K.factorial : ℝ) * M * B ^ K) * ρ ^ j := by
  intro j hj
  let Ψ : N04FlowPoint → N04FlowPoint := fun y => (y.1, Θ y)
  have hΨ : ContDiff ℝ ∞ Ψ := contDiff_fst.prodMk hΘ
  have hi (a : ℕ) (ha : 1 ≤ a) (haj : a ≤ j) :
      ‖iteratedFDeriv ℝ a Ψ q‖ ≤ B * ρ ^ (a - 1) := by
    have hp : ‖iteratedFDeriv ℝ a (fun y : N04FlowPoint => y.1) q‖ ≤ 1 := by
      simpa only [ContinuousLinearMap.coe_fst'] using
        (flowJet_norm_iteratedFDeriv_clm_le
          (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) ha q).trans
          (ContinuousLinearMap.norm_fst_le ℝ (ℝ × ℝ) ℝ)
    change ‖iteratedFDeriv ℝ a (fun y : N04FlowPoint => (y.1, Θ y)) q‖ ≤ _
    rw [iteratedFDeriv_prodMk contDiffAt_fst hΘ.contDiffAt (by simp),
      ContinuousMultilinearMap.opNorm_prod]
    exact max_le (hp.trans (one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hρ)))
      (hflow a ha (haj.trans hj))
  have ho (a : ℕ) (haj : a ≤ j) :
      ‖iteratedFDeriv ℝ a (fun y : N04FlowPoint =>
        deriv (fun θ => F (t, (y.1, θ))) y.2) (Ψ q)‖ ≤ M * ρ ^ a :=
    (n04NegativeGeometry_field_angle_jet_le hF t (Ψ q) a).trans
      (hraw a (haj.trans hj) (Θ q))
  have hb := n04NegativeGeometry_weighted_composition_jet_le hΨ
    (n04NegativeGeometry_field_angle_contDiff hF t) q j hB hρ ho hi
  have hfac : (j.factorial : ℝ) ≤ (K.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hj
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_right hfac hM)
      (pow_le_pow_right₀ hB hj) (pow_nonneg (zero_le_one.trans hB) _)
      (mul_nonneg (Nat.cast_nonneg _) hM)) (pow_nonneg (zero_le_one.trans hρ) _))

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_angleComposition_point_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_angleComposition_point_prefix
