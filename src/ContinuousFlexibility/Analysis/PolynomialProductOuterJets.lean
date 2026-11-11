import ContinuousFlexibility.Analysis.PolynomialJetOperations

/-!
# Scalar product jets on a ball with component-power radius

The coordinate projections have bounded positive derivatives. Their
zeroth values use only the stated radius. The ordinary product rule
therefore bounds every Taylor jet of multiplication by a component
power, with constants chosen before the component and evaluation point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem norm_iteratedFDeriv_linear_on_polynomial_ball
    {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W : I → ℝ) (hW : ∀ i, 1 ≤ W i) {A Q : ℝ} (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (L : E →L[ℝ] F) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, ‖x‖ ≤ A * W i ^ Q →
      ‖iteratedFDeriv ℝ n L x‖ ≤ C * W i ^ Q := by
  refine ⟨‖L‖ * (A + 1), mul_nonneg (norm_nonneg _) (add_nonneg hA zero_le_one), ?_⟩
  intro i x hx
  have hpow : 1 ≤ W i ^ Q := Real.one_le_rpow (hW i) hQ
  have hpow0 : 0 ≤ W i ^ Q := zero_le_one.trans hpow
  cases n with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact (L.le_opNorm x).trans ((mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans
        ((mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hpow0)
          (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm))
  | succ n =>
      apply (norm_iteratedFDeriv_linear_of_pos L (n + 1) (by omega) x).trans
      have hscale : 1 ≤ (A + 1) * W i ^ Q := by
        simpa only [one_mul] using
          mul_le_mul (show (1 : ℝ) ≤ A + 1 by linarith only [hA]) hpow
            zero_le_one (add_nonneg hA zero_le_one)
      exact (le_mul_of_one_le_right (norm_nonneg _) hscale).trans_eq
        (mul_assoc _ _ _).symm

theorem norm_iteratedFDeriv_mul_on_polynomial_ball
    {I : Type*} (W : I → ℝ) (hW : ∀ i, 1 ≤ W i)
    {A Q : ℝ} (hA : 0 ≤ A) (hQ : 0 ≤ Q) (n : ℕ) :
    ∃ C P : ℝ, 0 ≤ C ∧ 0 ≤ P ∧ ∀ (i : I) (z : ℝ × ℝ),
      ‖z‖ ≤ A * W i ^ Q →
        ‖iteratedFDeriv ℝ n (fun y : ℝ × ℝ => y.1 * y.2) z‖ ≤ C * W i ^ P := by
  let U : I → Set (ℝ × ℝ) := fun i => Metric.ball 0 ((A + 1) * W i ^ Q)
  have hU (i : I) : IsOpen (U i) := isOpen_ball
  have hcoord (L : (ℝ × ℝ) →L[ℝ] ℝ) (k : ℕ) :
      ∃ C P : ℝ, 0 ≤ C ∧ 0 ≤ P ∧ ∀ i z, z ∈ U i →
        ‖iteratedFDeriv ℝ k L z‖ ≤ C * W i ^ P := by
    obtain ⟨C, hC, hb⟩ := norm_iteratedFDeriv_linear_on_polynomial_ball W hW
      (add_nonneg hA zero_le_one) hQ L k
    refine ⟨C, Q, hC, hQ, fun i z hz => hb i z ?_⟩
    exact le_of_lt (by simpa only [U, Metric.mem_ball, dist_zero_right] using hz)
  obtain ⟨C, P, hC, hP, hb⟩ := norm_iteratedFDeriv_mul_polynomial_bound W hW U hU
    (fun _ z => z.1) (fun _ z => z.2)
    (fun _ => contDiff_fst.contDiffOn) (fun _ => contDiff_snd.contDiffOn) n
    (fun k _ => hcoord (ContinuousLinearMap.fst ℝ ℝ ℝ) k)
    (fun k _ => hcoord (ContinuousLinearMap.snd ℝ ℝ ℝ) k)
  refine ⟨C, P, hC, hP, fun i z hz => hb i z ?_⟩
  have hpow : 0 < W i ^ Q := Real.rpow_pos_of_pos (zero_lt_one.trans_le (hW i)) _
  change dist z 0 < (A + 1) * W i ^ Q
  rw [dist_zero_right]
  exact hz.trans_lt (by nlinarith only [hpow])

end ContinuousFlexibility.Analysis
