module

public import ContinuousFlexibility.Analysis.RootStationaryFlowJetPolynomial
public import ContinuousFlexibility.Analysis.RootRescaledFieldJets
public import ContinuousFlexibility.Analysis.FlowJetMaterialClosure

/-!
# Material bounds for the actual root-axis flow jets

The original drift and factored speed are evaluated only at the root.
The existing pointwise field-jet theorem is used at scale one and zero
parameters. The stationary-flow polynomial then preserves one high
state seminorm with a single common loss. No parameter-box radius,
common profile-germ radius, or chosen normalization scale enters these
estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The true regularized field jets on the root axis use only the raw
coefficient jets at that same root point. All numerical envelopes are
chosen before the state, material weight, coefficients and angle. -/
theorem rootRegularizedField_zero_rawMaterialJets
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (inputLoss : ℕ)
    (A : ℕ → ℝ) (hA : ∀ n, 1 ≤ A n) :
    ∃ B : ℕ → ℝ, (∀ n, 1 ≤ B n) ∧
      ∀ z : E, ∀ W : ℝ, 1 ≤ W →
      ∀ d c : PolarPoint → ℝ, ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
      ∀ θ : ℝ,
      (∀ n, ‖iteratedFDeriv ℝ n d (0, θ)‖ ≤
        A n * W ^ (A n) * (1 + p (n + inputLoss) z)) →
      (∀ n, ‖iteratedFDeriv ℝ n c (0, θ)‖ ≤
        A n * W ^ (A n) * (1 + p (n + inputLoss) z)) →
      ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ n
          (fun y : N04FlowPoint => rootRegularizedField d c (t, y))
            ((0, 0), θ)‖ ≤
          B n * W ^ (B n) * (1 + p (n + inputLoss) z) := by
  let H : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), A i
  have hAH (n k : ℕ) (hk : k ≤ n) : A k ≤ H n :=
    Finset.single_le_sum (fun i _ => zero_le_one.trans (hA i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hH (n : ℕ) : 1 ≤ H n := (hA n).trans (hAH n n le_rfl)
  let B : ℕ → ℝ := fun n =>
    max 1 (max (4 * linearWeightedCompositionJetConstant n * H n) (H n))
  have hB (n : ℕ) : 1 ≤ B n := le_max_left _ _
  refine ⟨B, hB, ?_⟩
  intro z W hW d c hd hc θ hdb hcb n t ht
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
  have hq : ((0, 0) : ℝ × ℝ) ∈ n04FlowParameterBox := by
    norm_num [n04FlowParameterBox]
  have hraw := rootRescaledField_jet_le
    (δ := 1) (q := ((0, 0), θ)) hd hc zero_le_one le_rfl hM ht hq n
    (fun k hk => by
      simpa only [one_mul, zero_mul] using (hdb k).trans (hcoef k hk))
    (fun k hk => by
      simpa only [one_mul, zero_mul] using (hcb k).trans (hcoef k hk))
  have hraw' :
      ‖iteratedFDeriv ℝ n
        (fun y : N04FlowPoint => rootRegularizedField d c (t, y))
          ((0, 0), θ)‖ ≤
        (4 * linearWeightedCompositionJetConstant n) * M := by
    simpa only [rootRescaledField, one_mul] using hraw
  have hCB : 4 * linearWeightedCompositionJetConstant n * H n ≤ B n :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hHB : H n ≤ B n := (le_max_right _ _).trans (le_max_right _ _)
  have hpack :
      (4 * linearWeightedCompositionJetConstant n * H n) * W ^ (H n) ≤
        B n * W ^ (B n) :=
    mul_le_mul hCB (Real.rpow_le_rpow_of_exponent_le hW hHB)
      (Real.rpow_nonneg hW0 _) (zero_le_one.trans (hB n))
  exact hraw'.trans (by
    dsimp only [M]
    calc
      _ = ((4 * linearWeightedCompositionJetConstant n * H n) * W ^ (H n)) *
          (1 + p (n + inputLoss) z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hpack (hstate n))

/-- Actual positive-order jets of any genuine root flow at the root axis.
The common low order and output loss precede the coefficient tower and
the material weight. No derivative bound for the flow is assumed. -/
theorem rootRegularizedFlow_zero_positiveJets_le_material
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ d c : PolarPoint → ℝ, ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
        (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) →
        (∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi) →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
        N04FlowEquations (rootRegularizedField d c) Θ →
      ∀ θ : ℝ,
      (∀ n, ‖iteratedFDeriv ℝ n d (0, θ)‖ ≤
        A n * W ^ (A n) * (1 + p (n + inputLoss) z)) →
      (∀ n, ‖iteratedFDeriv ℝ n c (0, θ)‖ ≤
        A n * W ^ (A n) * (1 + p (n + inputLoss) z)) →
      ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (n + 1)
          (fun y : N04FlowPoint => Θ y.1 t y.2) ((0, 0), θ)‖ ≤
          B n * W ^ (B n) * (1 + p ((n + 1) + loss) z) := by
  classical
  obtain ⟨base, loss, hmaterial⟩ :=
    flowJetPolynomial_le_material_one_high hp hI (inputLoss + 1)
  choose P hP hflow using exists_rootRegularizedFlow_zero_spatialJet_polynomial
  refine ⟨base, loss, ?_⟩
  intro A hA
  obtain ⟨C, hC, hraw⟩ := rootRegularizedField_zero_rawMaterialJets hp inputLoss A hA
  have hpacked (n : ℕ) :
      ∃ B : ℝ, 0 < B ∧ ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
        flowJetPolynomialEval (P n)
          (fun k => C (k + 1) * W ^ (C (k + 1)) *
            (1 + p (k + (inputLoss + 1)) z)) ≤
          B * W ^ B * (1 + p ((n + 1) + loss) z) :=
    hmaterial (n + 1) (P n) ((hP n).mono (Nat.le_succ n))
      (fun k => C (k + 1)) (fun k => hC (k + 1))
  choose B hB hb using hpacked
  refine ⟨B, hB, ?_⟩
  intro z hz W hW d c hd hc hdperiod hcperiod Θ hΘ θ hdb hcb n t ht
  let M : ℕ → ℝ := fun k => C (k + 1) * W ^ (C (k + 1)) *
    (1 + p (k + (inputLoss + 1)) z)
  have hM (k : ℕ) : 0 ≤ M k :=
    mul_nonneg
      (mul_nonneg (zero_le_one.trans (hC (k + 1)))
        (Real.rpow_nonneg (zero_le_one.trans hW) _))
      (add_nonneg zero_le_one (apply_nonneg _ _))
  have hrootraw (k : ℕ) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      ‖iteratedFDeriv ℝ (k + 1)
        (fun y : N04FlowPoint => rootRegularizedField d c (r, y))
          ((0, 0), θ)‖ ≤ M k := by
    have h := hraw z W hW d c hd hc θ hdb hcb (k + 1) r hr
    have hi : k + 1 + inputLoss = k + (inputLoss + 1) := by omega
    simpa only [M, hi] using h
  exact (hflow n M hM d c hd hc hdperiod hcperiod Θ hΘ θ hrootraw t ht).trans
    (hb n z hz W hW)

end ContinuousFlexibility.Analysis
