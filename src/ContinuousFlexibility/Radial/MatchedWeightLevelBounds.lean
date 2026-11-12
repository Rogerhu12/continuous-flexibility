import ContinuousFlexibility.Radial.MatchedWeightFibers

/-!
# Weighted matched kernels on the actual cell enumeration

The level map is explicit: for a reference profile it is D.cellIndex.
No injectivity of that map is assumed. Uniformly bounded finite fibers
supply the cell multiplicity in the final row and column estimates.

The source and output weights are exactly exp(M₀ q + γ S) and
exp(-M₁ q + γ S). This file only transforms scalar block majorants;
it introduces neither a physical norm nor an inverse operator.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- Scalar conjugation with the attenuation level of each actual cell. -/
def matchedLevelWeightedKernel {κ : Type*} (level : κ → ℕ)
    (M₀ M₁ γ : ℝ) (K : κ → κ → ℝ) (k m : κ) : ℝ :=
  Real.exp (matchedConjugationExponent M₀ M₁ γ (level k) (level m)) * K k m

@[simp] theorem matchedLevelWeightedKernel_apply {κ : Type*} (level : κ → ℕ)
    (M₀ M₁ γ : ℝ) (K : κ → κ → ℝ) (k m : κ) :
    matchedLevelWeightedKernel level M₀ M₁ γ K k m =
      Real.exp (matchedConjugationExponent M₀ M₁ γ (level k) (level m)) * K k m := rfl

/-- Identity levels recover the earlier level-indexed scalar kernel. -/
theorem matchedLevelWeightedKernel_id (M₀ M₁ γ : ℝ) (K : ℕ → ℕ → ℝ) (k m : ℕ) :
    matchedLevelWeightedKernel id M₀ M₁ γ K k m =
      matchedWeightedKernel M₀ M₁ γ K k m := rfl

/-- The literal quotient of the output-cell and source-cell weights. -/
theorem matchedLevelWeightedKernel_eq_weight_ratio {κ : Type*} (level : κ → ℕ)
    (M₀ M₁ γ : ℝ) (K : κ → κ → ℝ) (k m : κ) :
    matchedLevelWeightedKernel level M₀ M₁ γ K k m =
      Real.exp (-M₁ * radialQ (level k) + γ * radialS (level k)) * K k m /
        Real.exp (M₀ * radialQ (level m) + γ * radialS (level m)) :=
  matchedWeightedKernel_eq_weight_ratio M₀ M₁ γ (fun _ _ => K k m) (level k) (level m)

theorem matchedLevelWeightedKernel_nonneg {κ : Type*} {level : κ → ℕ}
    {M₀ M₁ γ : ℝ} {K : κ → κ → ℝ}
    (hK : ∀ k m, 0 ≤ K k m) (k m : κ) :
    0 ≤ matchedLevelWeightedKernel level M₀ M₁ γ K k m :=
  mul_nonneg (Real.exp_pos _).le (hK k m)

/-- Actual-cell outer-block majorants give one decay constant for all
frequencies and all exponents in the interval, followed by actual-cell
Schur sums with the finite-fiber multiplicity. -/
theorem matched_level_weightedKernel_estimates {ι κ : Type*}
    (level : κ → ℕ) (N : ℕ)
    (hfibers : ∀ n, Set.Finite {m | level m = n})
    (hcard : ∀ n, Set.ncard {m | level m = n} ≤ N)
    (K : ι → κ → κ → ℝ) (transition : ι → ℕ)
    (M₀ M₁ C₀ a d c₁ C₁ γlo γhi : ℝ)
    (hC₀ : 0 < C₀) (hd : 0 ≤ d) (hlo : 0 ≤ γlo) (hhi : γhi < 1)
    (hloss : 2 * a + d * c₁ < M₀ + M₁)
    (hK : ∀ i k m, 0 ≤ K i k m)
    (hmajor : ∀ i k m, K i k m ≤ C₀ * Real.exp
      (a * (radialQ (level k) + radialQ (level m)) + d * radialQ (transition i) -
        |radialS (level k) - radialS (level m)|))
    (hposition : ∀ i k m, K i k m ≠ 0 →
      radialQ (transition i) ≤ c₁ * radialQ (level k) + C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ ∈ Icc γlo γhi, ∀ i,
      (∀ k m, matchedLevelWeightedKernel level M₀ M₁ γ (K i) k m ≤
        C * Real.exp (-((1 - γhi) / 2 * |radialS (level k) - radialS (level m)|))) ∧
      (∀ k, Summable (fun m => matchedLevelWeightedKernel level M₀ M₁ γ (K i) k m) ∧
        ∑' m, matchedLevelWeightedKernel level M₀ M₁ γ (K i) k m ≤
          C * ((N : ℝ) * matchedSchurFactor ((1 - γhi) / 2))) ∧
      (∀ m, Summable (fun k => matchedLevelWeightedKernel level M₀ M₁ γ (K i) k m) ∧
        ∑' k, matchedLevelWeightedKernel level M₀ M₁ γ (K i) k m ≤
          C * ((N : ℝ) * matchedSchurFactor ((1 - γhi) / 2))) := by
  obtain ⟨C, hC⟩ := matched_weight_exponent M₀ M₁ a d c₁ C₁ γlo γhi hd hlo hhi hloss
  have hCpos : 0 < C₀ * Real.exp C := mul_pos hC₀ (Real.exp_pos _)
  refine ⟨C₀ * Real.exp C, hCpos, ?_⟩
  intro γ hγ i
  have hdecay : ∀ k m, matchedLevelWeightedKernel level M₀ M₁ γ (K i) k m ≤
      (C₀ * Real.exp C) *
        Real.exp (-((1 - γhi) / 2 * |radialS (level k) - radialS (level m)|)) := by
    intro k m
    by_cases hz : K i k m = 0
    · rw [matchedLevelWeightedKernel_apply, hz, mul_zero]
      exact mul_nonneg hCpos.le (Real.exp_pos _).le
    · have he := hC γ hγ (transition i) (level k) (level m) (hposition i k m hz)
      calc
        matchedLevelWeightedKernel level M₀ M₁ γ (K i) k m ≤
            Real.exp (matchedConjugationExponent M₀ M₁ γ (level k) (level m)) *
              (C₀ * Real.exp (a * (radialQ (level k) + radialQ (level m)) +
                d * radialQ (transition i) - |radialS (level k) - radialS (level m)|)) :=
          mul_le_mul_of_nonneg_left (hmajor i k m) (Real.exp_pos _).le
        _ = C₀ * Real.exp (matchedConjugationExponent M₀ M₁ γ (level k) (level m) +
            (a * (radialQ (level k) + radialQ (level m)) + d * radialQ (transition i) -
              |radialS (level k) - radialS (level m)|)) := by
          rw [Real.exp_add]
          ring
        _ ≤ C₀ * Real.exp (C - (1 - γhi) / 2 * |radialS (level k) - radialS (level m)|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC₀.le
        _ = (C₀ * Real.exp C) *
            Real.exp (-((1 - γhi) / 2 * |radialS (level k) - radialS (level m)|)) := by
          rw [sub_eq_add_neg, Real.exp_add]
          ring
  have hnonneg : ∀ k m, 0 ≤ matchedLevelWeightedKernel level M₀ M₁ γ (K i) k m :=
    matchedLevelWeightedKernel_nonneg (hK i)
  exact ⟨hdecay, matched_level_kernel_sums_of_decay level N hfibers hcard
    hCpos.le (by linarith) hnonneg hdecay⟩

/-- For a global actual-cell majorant there is no transition-index or
outer-location hypothesis. This is the direct entry point for a
frequency-uniform matched inverse block estimate. -/
theorem matched_level_global_weightedKernel_estimates {ι κ : Type*}
    (level : κ → ℕ) (N : ℕ)
    (hfibers : ∀ n, Set.Finite {m | level m = n})
    (hcard : ∀ n, Set.ncard {m | level m = n} ≤ N)
    (K : ι → κ → κ → ℝ) (M₀ M₁ C₀ a γlo γhi : ℝ)
    (hC₀ : 0 < C₀) (hlo : 0 ≤ γlo) (hhi : γhi < 1)
    (hloss : 2 * a < M₀ + M₁)
    (hK : ∀ i k m, 0 ≤ K i k m)
    (hmajor : ∀ i k m, K i k m ≤ C₀ * Real.exp
      (a * (radialQ (level k) + radialQ (level m)) -
        |radialS (level k) - radialS (level m)|)) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ ∈ Icc γlo γhi, ∀ i,
      (∀ k m, matchedLevelWeightedKernel level M₀ M₁ γ (K i) k m ≤
        C * Real.exp (-((1 - γhi) / 2 * |radialS (level k) - radialS (level m)|))) ∧
      (∀ k, Summable (fun m => matchedLevelWeightedKernel level M₀ M₁ γ (K i) k m) ∧
        ∑' m, matchedLevelWeightedKernel level M₀ M₁ γ (K i) k m ≤
          C * ((N : ℝ) * matchedSchurFactor ((1 - γhi) / 2))) ∧
      (∀ m, Summable (fun k => matchedLevelWeightedKernel level M₀ M₁ γ (K i) k m) ∧
        ∑' k, matchedLevelWeightedKernel level M₀ M₁ γ (K i) k m ≤
          C * ((N : ℝ) * matchedSchurFactor ((1 - γhi) / 2))) := by
  refine matched_level_weightedKernel_estimates level N hfibers hcard K (fun _ => 0)
    M₀ M₁ C₀ a 0 0 (radialQ 0) γlo γhi hC₀ (le_refl 0) hlo hhi ?_ hK ?_ ?_
  · simpa only [zero_mul, add_zero] using hloss
  · intro i k m
    simpa only [zero_mul, add_zero] using hmajor i k m
  · intro i k m _
    simpa only [zero_mul, zero_add] using le_refl (radialQ 0)

end ContinuousFlexibility.Radial
