import ContinuousFlexibility.Analysis.N04FlowPolynomialBounds
import ContinuousFlexibility.Analysis.FlowJetMaterialClosure

/-!
# The fixed-loss mixed scalar-flow target

The actual jet polynomial is chosen before the state and material
envelope. State interpolation is applied once to each expanded
monomial. The zeroth displacement uses the original speed integral,
while every positive-order displacement uses the actual flow-jet
polynomial plus the initial projection.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The complete mixed spatial estimate, with one low order and one
loss chosen before all field constants and derivative orders. -/
theorem n04FlowJetsTarget_proof : N04FlowJetsTarget := by
  intro E _ _ p hp hI inputLoss
  obtain ⟨base, loss, hmaterial⟩ :=
    flowJetPolynomial_le_material_one_high hp hI (inputLoss + 1)
  refine ⟨base, max loss inputLoss, ?_⟩
  intro A hA Λ _hΛ
  choose P hPdegree hPbound using fun n => exists_n04Flow_spatialJet_polynomial Λ n
  have hpacked (n : ℕ) :
      ∃ C : ℝ, 0 < C ∧ ∀ z : E, p base z ≤ 1 →
        ∀ W : ℝ, 1 ≤ W →
          flowJetPolynomialEval (P n ++ [(1, [])])
            (fun k => A (k + 1) * W ^ (A (k + 1)) *
              (1 + p (k + (inputLoss + 1)) z)) ≤
            C * W ^ C * (1 + p ((n + 1) + loss) z) :=
    hmaterial (n + 1) (P n ++ [(1, [])])
      (((hPdegree n).append (FlowJetPolynomialDegreeLE.const zero_le_one n)).mono
        (Nat.le_succ n)) (fun k => A (k + 1)) (fun k => hA (k + 1))
  choose C hC hestimate using hpacked
  let B : ℕ → ℝ
    | 0 => A 0
    | n + 1 => C n
  refine ⟨B, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact zero_lt_one.trans_le (hA 0)
    | succ n => exact hC n
  · intro z hz W hW F hF hperiod hraw hangular Θ hΘ t ht
    have hW0 : 0 ≤ W := zero_le_one.trans hW
    have hΦ := n04Flow_contDiff_slice hF hperiod hΘ ht
    refine ⟨hΦ, (fun v θ => n04Flow_period_add hF hperiod hΘ v θ ht),
      (fun v hv θ => n04Flow_angular_bounds hF hperiod hΘ hangular hv ht θ), ?_⟩
    intro n q hq
    cases n with
    | zero =>
      have hM : 0 ≤ A 0 * W ^ (A 0) * (1 + p inputLoss z) :=
        mul_nonneg
          (mul_nonneg (zero_le_one.trans (hA 0)) (Real.rpow_nonneg hW0 _))
          (add_nonneg zero_le_one (apply_nonneg _ _))
      have hb := n04Flow_displacement_abs_le hF hΘ q.1 q.2 hM
        (fun r hr θ => by
          simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.zero_add] using
            hraw 0 r hr (q.1, θ) hq) ht
      change ‖iteratedFDeriv ℝ 0
        (fun y : N04FlowPoint => Θ y.1 t y.2 - y.2) q‖ ≤
          A 0 * W ^ (A 0) * (1 + p (0 + max loss inputLoss) z)
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.zero_add]
      exact hb.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl ((hp (le_max_right loss inputLoss)) z))
        (mul_nonneg (zero_le_one.trans (hA 0)) (Real.rpow_nonneg hW0 _)))
    | succ n =>
      let M : ℕ → ℝ := fun k =>
        A (k + 1) * W ^ (A (k + 1)) * (1 + p (k + (inputLoss + 1)) z)
      have hM (k : ℕ) : 0 ≤ M k :=
        mul_nonneg
          (mul_nonneg (zero_le_one.trans (hA (k + 1))) (Real.rpow_nonneg hW0 _))
          (add_nonneg zero_le_one (apply_nonneg _ _))
      have hpositive : N04FlowPositiveRawBounds M F := by
        intro k r hr y hy
        have hi : (k + 1) + inputLoss = k + (inputLoss + 1) := by omega
        simpa only [M, hi] using hraw (k + 1) r hr y hy
      have hjet := hPbound n M hM F hF hperiod hpositive hangular Θ hΘ t ht q hq
      have hc : ‖iteratedFDeriv ℝ (n + 1) (fun y : N04FlowPoint => y.2) q‖ ≤ 1 := by
        simpa only [ContinuousLinearMap.coe_snd'] using
          (flowJet_norm_iteratedFDeriv_clm_le
            (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (Nat.succ_pos n) q).trans
            (ContinuousLinearMap.norm_snd_le ℝ (ℝ × ℝ) ℝ)
      have hdisplacement :
          ‖iteratedFDeriv ℝ (n + 1)
            (fun y : N04FlowPoint => Θ y.1 t y.2 - y.2) q‖ ≤
              flowJetPolynomialEval (P n) M + 1 := by
        have he :
            (fun y : N04FlowPoint => Θ y.1 t y.2 - y.2) =
              (fun y : N04FlowPoint => Θ y.1 t y.2) - (fun y : N04FlowPoint => y.2) := by
          funext y
          exact (Pi.sub_apply _ _ y).symm
        rw [he, iteratedFDeriv_sub_apply
          (hΦ.contDiffAt.of_le (by simp : ((n + 1 : ℕ) : ℕ∞ω) ≤ ∞)) contDiffAt_snd]
        exact (norm_sub_le _ _).trans (add_le_add hjet hc)
      change ‖iteratedFDeriv ℝ (n + 1)
        (fun y : N04FlowPoint => Θ y.1 t y.2 - y.2) q‖ ≤
          C n * W ^ (C n) * (1 + p ((n + 1) + max loss inputLoss) z)
      calc
        _ ≤ flowJetPolynomialEval (P n) M + 1 := hdisplacement
        _ = flowJetPolynomialEval (P n ++ [(1, [])]) M := by
          rw [flowJetPolynomialEval_append, flowJetPolynomialEval_const]
        _ ≤ C n * W ^ (C n) * (1 + p ((n + 1) + loss) z) :=
          hestimate n z hz W hW
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (add_le_add le_rfl
            ((hp (Nat.add_le_add_left (le_max_left loss inputLoss) (n + 1))) z))
          (mul_nonneg (hC n).le (Real.rpow_nonneg hW0 _))

end ContinuousFlexibility.Analysis

#print axioms ContinuousFlexibility.Analysis.n04FlowJetsTarget_proof
