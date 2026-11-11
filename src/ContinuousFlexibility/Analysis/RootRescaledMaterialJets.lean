import ContinuousFlexibility.Analysis.RootRescaledFieldJets

/-!
# Material bounds for the original regularized root vector field

The same-order spatial estimate is packaged in the exact raw-field input
of N04FlowJetsTarget. Constants are selected before the state, envelope,
collar, and coefficient fields. No interpolation or additional loss is
needed for this step because the coefficient jets enter linearly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem rootRescaledField_rawMaterialJets
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (inputLoss : ℕ)
    (A : ℕ → ℝ) (hA : ∀ n, 1 ≤ A n) :
    ∃ B : ℕ → ℝ, (∀ n, 1 ≤ B n) ∧
      ∀ z : E, ∀ W : ℝ, 1 ≤ W → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      ∀ d c : PolarPoint → ℝ, ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
      (∀ n r, |r| ≤ δ → ∀ θ,
        ‖iteratedFDeriv ℝ n d (r, θ)‖ ≤
          A n * W ^ (A n) * (1 + p (n + inputLoss) z)) →
      (∀ n r, |r| ≤ δ → ∀ θ,
        ‖iteratedFDeriv ℝ n c (r, θ)‖ ≤
          A n * W ^ (A n) * (1 + p (n + inputLoss) z)) →
      N04FlowRawJetBounds p inputLoss B z W (rootRescaledField d c δ) := by
  let H : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), A i
  have hAH (n k : ℕ) (hk : k ≤ n) : A k ≤ H n :=
    Finset.single_le_sum (fun i _ => zero_le_one.trans (hA i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hH (n : ℕ) : 1 ≤ H n := (hA n).trans (hAH n n le_rfl)
  let B : ℕ → ℝ := fun n =>
    max 1 (max (4 * linearWeightedCompositionJetConstant n * H n) (H n))
  have hB (n : ℕ) : 1 ≤ B n := le_max_left _ _
  refine ⟨B, hB, ?_⟩
  intro z W hW δ hδ hδone d c hd hc hdb hcb n t ht q hq
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hstate (k : ℕ) : 0 ≤ 1 + p (k + inputLoss) z :=
    add_nonneg zero_le_one (apply_nonneg _ _)
  let M : ℝ := H n * W ^ (H n) * (1 + p (n + inputLoss) z)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (zero_le_one.trans (hH n)) (Real.rpow_nonneg hW0 _)) (hstate n)
  have hcoef (k : ℕ) (hk : k ≤ n) :
      A k * W ^ (A k) * (1 + p (k + inputLoss) z) ≤ M := by
    exact mul_le_mul
      (mul_le_mul (hAH n k hk)
        (Real.rpow_le_rpow_of_exponent_le hW (hAH n k hk))
        (Real.rpow_nonneg hW0 _) (zero_le_one.trans (hH n)))
      (add_le_add (le_refl (1 : ℝ)) ((hp (Nat.add_le_add_right hk inputLoss)) z))
      (hstate k)
      (mul_nonneg (zero_le_one.trans (hH n)) (Real.rpow_nonneg hW0 _))
  have ht2 : t ^ 2 ≤ 1 := by
    simpa only [pow_two, one_mul] using mul_le_mul ht.2 ht.2 ht.1 zero_le_one
  have hr : |δ * q.1.1 * t ^ 2| ≤ δ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hδ, abs_of_nonneg (sq_nonneg t)]
    calc
      _ ≤ (δ * 1) * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left (abs_le.mpr hq.1) hδ) ht2
        (sq_nonneg t) (by simpa only [mul_one] using hδ)
      _ = δ := by ring
  have hraw := rootRescaledField_jet_le hd hc hδ hδone hM ht hq n
    (fun k hk => (hdb k _ hr q.2).trans (hcoef k hk))
    (fun k hk => (hcb k _ hr q.2).trans (hcoef k hk))
  have hCB : 4 * linearWeightedCompositionJetConstant n * H n ≤ B n :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hHB : H n ≤ B n := (le_max_right _ _).trans (le_max_right _ _)
  have hpack :
      (4 * linearWeightedCompositionJetConstant n * H n) * W ^ (H n) ≤
        B n * W ^ (B n) :=
    mul_le_mul hCB (Real.rpow_le_rpow_of_exponent_le hW hHB)
      (Real.rpow_nonneg hW0 _) (zero_le_one.trans (hB n))
  exact hraw.trans (by
    dsimp only [M]
    calc
      _ = ((4 * linearWeightedCompositionJetConstant n * H n) * W ^ (H n)) *
          (1 + p (n + inputLoss) z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hpack (hstate n))

end ContinuousFlexibility.Analysis
