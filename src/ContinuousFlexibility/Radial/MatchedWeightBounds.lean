import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# Uniform weights for matched inverse blocks

Section 6 of the manuscript estimates an unweighted block by
`C₀ * exp (a * (qₖ + qₘ) + d * qₙ - |Sₖ - Sₘ|)`.  On an outer output
cell, the transition index satisfies `qₙ ≤ c₁ * qₖ + C₁`.  This file proves
the resulting uniform weighted decay and Schur bounds on a whole compact
interval of exponents.

The convention here is the one in `sourceCellSquare` and `outputCellSquare`:
the source weight is `exp (M₀ * q + γ * S)` and the output weight is
`exp (-M₁ * q + γ * S)`.  Thus the manuscript's total loss is `M₀ + M₁`.
Actual block bounds and the transition-index comparison are hypotheses;
the scalar estimates do not assert that an actual matched inverse has them.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- The output weight divided by the source weight, at exponent level. -/
def matchedConjugationExponent (M₀ M₁ γ : ℝ) (k m : ℕ) : ℝ :=
  -M₁ * radialQ k - M₀ * radialQ m + γ * (radialS k - radialS m)

/-- A nonnegative block majorant after conjugation by the actual two weights. -/
def matchedWeightedKernel (M₀ M₁ γ : ℝ) (K : ℕ → ℕ → ℝ) (k m : ℕ) : ℝ :=
  exp (matchedConjugationExponent M₀ M₁ γ k m) * K k m

@[simp] theorem matchedWeightedKernel_apply (M₀ M₁ γ : ℝ)
    (K : ℕ → ℕ → ℝ) (k m : ℕ) :
    matchedWeightedKernel M₀ M₁ γ K k m =
      exp (matchedConjugationExponent M₀ M₁ γ k m) * K k m := rfl

/-- This identity fixes the source/output sign convention explicitly. -/
theorem matchedWeightedKernel_eq_weight_ratio (M₀ M₁ γ : ℝ)
    (K : ℕ → ℕ → ℝ) (k m : ℕ) :
    matchedWeightedKernel M₀ M₁ γ K k m =
      exp (-M₁ * radialQ k + γ * radialS k) * K k m /
        exp (M₀ * radialQ m + γ * radialS m) := by
  rw [matchedWeightedKernel_apply]
  have hexp : exp (matchedConjugationExponent M₀ M₁ γ k m) =
      exp (-M₁ * radialQ k + γ * radialS k) *
        exp (-(M₀ * radialQ m + γ * radialS m)) := by
    rw [← Real.exp_add]
    congr 1
    unfold matchedConjugationExponent
    ring
  rw [hexp, Real.exp_neg, div_eq_mul_inv]
  ring

theorem matchedWeightedKernel_nonneg {M₀ M₁ γ : ℝ} {K : ℕ → ℕ → ℝ}
    (hK : ∀ k m, 0 ≤ K k m) (k m : ℕ) :
    0 ≤ matchedWeightedKernel M₀ M₁ γ K k m :=
  mul_nonneg (Real.exp_pos _).le (hK k m)

/-- One absorption constant works for every exponent in the interval and
every transition index satisfying the outer-output comparison. -/
theorem matched_weight_exponent (M₀ M₁ a d c₁ C₁ γlo γhi : ℝ)
    (hd : 0 ≤ d) (hlo : 0 ≤ γlo) (hhi : γhi < 1)
    (hloss : 2 * a + d * c₁ < M₀ + M₁) :
    ∃ C : ℝ, ∀ γ ∈ Icc γlo γhi, ∀ n k m : ℕ,
      radialQ n ≤ c₁ * radialQ k + C₁ →
      matchedConjugationExponent M₀ M₁ γ k m +
          (a * (radialQ k + radialQ m) + d * radialQ n -
            |radialS k - radialS m|) ≤
        C - (1 - γhi) / 2 * |radialS k - radialS m| := by
  obtain ⟨C, hC⟩ := absorb_radialQ (a - M₀) ((1 - γhi) / 2) (by linarith)
  refine ⟨C + d * C₁, ?_⟩
  intro γ hγ n k m hposition
  have habs := hC k m
  have hcut := mul_le_mul_of_nonneg_left hposition hd
  have hdrop := mul_nonneg
    (show 0 ≤ M₀ + M₁ - (2 * a + d * c₁) by linarith)
    (radialQ_nonneg k)
  have hγ0 : 0 ≤ γ := hlo.trans hγ.1
  have hγabs := mul_le_mul_of_nonneg_left
    (le_abs_self (radialS k - radialS m)) hγ0
  have hγhi := mul_le_mul_of_nonneg_right hγ.2
    (abs_nonneg (radialS k - radialS m))
  unfold matchedConjugationExponent
  nlinarith only [habs, hcut, hdrop, hγabs, hγhi]

/-- The common row and column sum of the scalar exponential majorant. -/
def matchedSchurFactor (η : ℝ) : ℝ :=
  1 + 2 / (Real.exp (η * (2 / 3)) - 1)

theorem matchedSchurFactor_pos {η : ℝ} (hη : 0 < η) :
    0 < matchedSchurFactor η := by
  have hE : 0 < Real.exp (η * (2 / 3)) - 1 := by
    have h := Real.exp_lt_exp.mpr (show 0 < η * (2 / 3) by positivity)
    rw [Real.exp_zero] at h
    linarith
  unfold matchedSchurFactor
  positivity

/-- The same scalar comparison proves both orientations of the Schur sum. -/
theorem matched_sequence_sum_of_decay {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η)
    (k : ℕ) (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m)
    (hle : ∀ m, f m ≤ C * Real.exp (-(η * |radialS k - radialS m|))) :
    Summable f ∧ ∑' m, f m ≤ C * matchedSchurFactor η := by
  obtain ⟨hs, hb⟩ := radialS_row_sum hη k
  have hsm := hs.mul_left C
  have hsf : Summable f := Summable.of_nonneg_of_le hf hle hsm
  refine ⟨hsf, ?_⟩
  calc
    ∑' m, f m ≤ ∑' m, C * Real.exp (-(η * |radialS k - radialS m|)) :=
      Summable.tsum_le_tsum hle hsf hsm
    _ = C * ∑' m, Real.exp (-(η * |radialS k - radialS m|)) := tsum_mul_left
    _ ≤ C * matchedSchurFactor η := mul_le_mul_of_nonneg_left hb hC

theorem matched_kernel_sums_of_decay {K : ℕ → ℕ → ℝ} {C η : ℝ}
    (hC : 0 ≤ C) (hη : 0 < η) (hK : ∀ k m, 0 ≤ K k m)
    (hle : ∀ k m, K k m ≤ C * Real.exp (-(η * |radialS k - radialS m|))) :
    (∀ k, Summable (fun m => K k m) ∧ ∑' m, K k m ≤ C * matchedSchurFactor η) ∧
    (∀ m, Summable (fun k => K k m) ∧ ∑' k, K k m ≤ C * matchedSchurFactor η) := by
  refine ⟨fun k => matched_sequence_sum_of_decay hC hη k (K k) (hK k) (hle k), ?_⟩
  intro m
  apply matched_sequence_sum_of_decay hC hη m (fun k => K k m) (fun k => hK k m)
  intro k
  simpa only [abs_sub_comm (radialS m) (radialS k)] using hle k m

/-- Uniform block decay and row/column sums, including uniformity in an
arbitrary frequency parameter.  A zero block needs no location hypothesis. -/
theorem matched_weightedKernel_estimates {ι : Type*}
    (K : ι → ℕ → ℕ → ℝ) (transition : ι → ℕ)
    (M₀ M₁ C₀ a d c₁ C₁ γlo γhi : ℝ)
    (hC₀ : 0 < C₀) (hd : 0 ≤ d) (hlo : 0 ≤ γlo) (hhi : γhi < 1)
    (hloss : 2 * a + d * c₁ < M₀ + M₁)
    (hK : ∀ i k m, 0 ≤ K i k m)
    (hmajor : ∀ i k m, K i k m ≤ C₀ * Real.exp
      (a * (radialQ k + radialQ m) + d * radialQ (transition i) -
        |radialS k - radialS m|))
    (hposition : ∀ i k m, K i k m ≠ 0 →
      radialQ (transition i) ≤ c₁ * radialQ k + C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ ∈ Icc γlo γhi, ∀ i,
      (∀ k m, matchedWeightedKernel M₀ M₁ γ (K i) k m ≤
        C * Real.exp (-((1 - γhi) / 2 * |radialS k - radialS m|))) ∧
      (∀ k, Summable (fun m => matchedWeightedKernel M₀ M₁ γ (K i) k m) ∧
        ∑' m, matchedWeightedKernel M₀ M₁ γ (K i) k m ≤
          C * matchedSchurFactor ((1 - γhi) / 2)) ∧
      (∀ m, Summable (fun k => matchedWeightedKernel M₀ M₁ γ (K i) k m) ∧
        ∑' k, matchedWeightedKernel M₀ M₁ γ (K i) k m ≤
          C * matchedSchurFactor ((1 - γhi) / 2)) := by
  obtain ⟨C, hC⟩ := matched_weight_exponent M₀ M₁ a d c₁ C₁ γlo γhi hd hlo hhi hloss
  have hCpos : 0 < C₀ * Real.exp C := mul_pos hC₀ (Real.exp_pos _)
  refine ⟨C₀ * Real.exp C, hCpos, ?_⟩
  intro γ hγ i
  have hdecay : ∀ k m, matchedWeightedKernel M₀ M₁ γ (K i) k m ≤
      (C₀ * Real.exp C) *
        Real.exp (-((1 - γhi) / 2 * |radialS k - radialS m|)) := by
    intro k m
    by_cases hz : K i k m = 0
    · rw [matchedWeightedKernel_apply, hz, mul_zero]
      exact mul_nonneg hCpos.le (Real.exp_pos _).le
    · have he := hC γ hγ (transition i) k m (hposition i k m hz)
      calc
        matchedWeightedKernel M₀ M₁ γ (K i) k m ≤
            Real.exp (matchedConjugationExponent M₀ M₁ γ k m) *
              (C₀ * Real.exp (a * (radialQ k + radialQ m) +
                d * radialQ (transition i) - |radialS k - radialS m|)) :=
          mul_le_mul_of_nonneg_left (hmajor i k m) (Real.exp_pos _).le
        _ = C₀ * Real.exp (matchedConjugationExponent M₀ M₁ γ k m +
            (a * (radialQ k + radialQ m) + d * radialQ (transition i) -
              |radialS k - radialS m|)) := by
          rw [Real.exp_add]
          ring
        _ ≤ C₀ * Real.exp (C - (1 - γhi) / 2 * |radialS k - radialS m|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC₀.le
        _ = (C₀ * Real.exp C) *
            Real.exp (-((1 - γhi) / 2 * |radialS k - radialS m|)) := by
          rw [sub_eq_add_neg, Real.exp_add]
          ring
  exact ⟨hdecay, matched_kernel_sums_of_decay hCpos.le (by linarith)
    (matchedWeightedKernel_nonneg (hK i)) hdecay⟩

end ContinuousFlexibility.Radial
