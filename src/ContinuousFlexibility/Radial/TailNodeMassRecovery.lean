import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

/-!
# Recovering square-summable node values from mass integrals

An actual differential-equation solution need not initially have a known
square-summable node sequence. A one-sided estimate bounds the next node
mass by the next cell integral and a strict contraction of the preceding
node mass. Uniform bounds on finite partial sums then prove summability,
without assuming it while summing the recurrence.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped BigOperators

/-- The preceding-node error in the physical mass estimate is controlled
by the square of the small inner-resistance product divided by the two
large neighboring mass--resistance products. -/
theorem tailNode_neighbor_mass_ratio_le {Λ η K μ ν S R : ℝ}
    (hΛ : 0 < Λ) (hK : 0 < K) (hμ : 0 < μ) (hν : 0 < ν)
    (hS : 0 ≤ S) (hR : 0 < R) (hsmall : Λ * μ * S ≤ η)
    (hleft : K ≤ Λ * μ * R) (hright : K ≤ Λ * ν * R) :
    μ * S ^ 2 / (ν * R ^ 2) ≤ η ^ 2 / K ^ 2 := by
  have hA : 0 ≤ Λ * μ * S := mul_nonneg (mul_pos hΛ hμ).le hS
  have hB : 0 < Λ * μ * R := mul_pos (mul_pos hΛ hμ) hR
  have hC : 0 < Λ * ν * R := mul_pos (mul_pos hΛ hν) hR
  have hnum : (Λ * μ * S) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hA hsmall 2
  have hden : K ^ 2 ≤ (Λ * μ * R) * (Λ * ν * R) := by
    simpa only [pow_two] using mul_le_mul hleft hright hK.le hB.le
  calc
    μ * S ^ 2 / (ν * R ^ 2) =
        (Λ * μ * S) ^ 2 / ((Λ * μ * R) * (Λ * ν * R)) := by
      field_simp [hΛ.ne', hμ.ne', hν.ne', hR.ne'] <;> ring
    _ ≤ η ^ 2 / ((Λ * μ * R) * (Λ * ν * R)) :=
      div_le_div_of_nonneg_right hnum (mul_pos hB hC).le
    _ ≤ η ^ 2 / K ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg η) (pow_pos hK 2) hden

/-- Uniform bounds on finite forcing sums give uniform bounds on finite
node sums. No infinite sum of the node sequence is assumed to exist. -/
theorem tailNode_mass_sum_range_le {A E : ℕ → ℝ} {M ρ B : ℝ}
    (hA : ∀ n, 0 ≤ A n) (hE : ∀ n, 0 ≤ E n)
    (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hstep : ∀ n, A (n + 1) ≤ M * E (n + 1) + ρ * A n)
    (hforcing : ∀ N, ∑ n ∈ Finset.range N, E n ≤ B) (N : ℕ) :
    (∑ n ∈ Finset.range N, A n) ≤ (A 0 + M * B) / (1 - ρ) := by
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ₁
  have hB : 0 ≤ B := by simpa only [Finset.range_zero, Finset.sum_empty] using hforcing 0
  cases N with
  | zero =>
    simpa only [Finset.range_zero, Finset.sum_empty] using
      div_nonneg (add_nonneg (hA 0) (mul_nonneg hM hB)) hden.le
  | succ N =>
    have hsum : (∑ n ∈ Finset.range N, A (n + 1)) ≤
        M * (∑ n ∈ Finset.range N, E (n + 1)) +
          ρ * (∑ n ∈ Finset.range N, A n) := by
      calc
        (∑ n ∈ Finset.range N, A (n + 1)) ≤
            ∑ n ∈ Finset.range N, (M * E (n + 1) + ρ * A n) :=
          Finset.sum_le_sum (fun n _ => hstep n)
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hEshift : (∑ n ∈ Finset.range N, E (n + 1)) ≤ B := by
      have hsplit := Finset.sum_range_succ' E N
      linarith only [hsplit, hforcing (N + 1), hE 0]
    have hAhead : (∑ n ∈ Finset.range N, A n) ≤
        ∑ n ∈ Finset.range (N + 1), A n := by
      rw [Finset.sum_range_succ]
      exact le_add_of_nonneg_right (hA N)
    have hEM := mul_le_mul_of_nonneg_left hEshift hM
    have hAρ := mul_le_mul_of_nonneg_left hAhead hρ
    have hsplit := Finset.sum_range_succ' A N
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hsum, hEM, hAρ, hsplit]

/-- A nonnegative sequence controlled by a summable forcing and a strict
one-step contraction is summable. -/
theorem tailNode_mass_summable_of_step {A E : ℕ → ℝ} {M ρ : ℝ}
    (hA : ∀ n, 0 ≤ A n) (hE : ∀ n, 0 ≤ E n)
    (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hstep : ∀ n, A (n + 1) ≤ M * E (n + 1) + ρ * A n)
    (hforcing : Summable E) : Summable A := by
  apply summable_of_sum_range_le hA
  exact tailNode_mass_sum_range_le hA hE hM hρ hρ₁ hstep
    (fun N => hforcing.sum_le_tsum (Finset.range N) (fun n _ => hE n))

/-- The recovery argument also gives an explicit total-mass bound. -/
theorem tailNode_mass_tsum_le {A E : ℕ → ℝ} {M ρ : ℝ}
    (hA : ∀ n, 0 ≤ A n) (hE : ∀ n, 0 ≤ E n)
    (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hstep : ∀ n, A (n + 1) ≤ M * E (n + 1) + ρ * A n)
    (hforcing : Summable E) :
    (∑' n, A n) ≤ (A 0 + M * ∑' n, E n) / (1 - ρ) :=
  Real.tsum_le_of_sum_range_le hA
    (tailNode_mass_sum_range_le hA hE hM hρ hρ₁ hstep
      (fun N => hforcing.sum_le_tsum (Finset.range N) (fun n _ => hE n)))

/-- Direct input form for the mass-weighted values of an actual node
sequence. The forcing can be any summable sequence of cell integrals. -/
theorem tailNode_weighted_sq_summable_of_recovery {μ a E : ℕ → ℝ} {M ρ : ℝ}
    (hμ : ∀ n, 0 ≤ μ n) (hE : ∀ n, 0 ≤ E n)
    (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hstep : ∀ n, μ (n + 1) * a (n + 1) ^ 2 ≤
      M * E (n + 1) + ρ * (μ n * a n ^ 2))
    (hforcing : Summable E) : Summable (fun n => μ n * a n ^ 2) :=
  tailNode_mass_summable_of_step (fun n => mul_nonneg (hμ n) (sq_nonneg _))
    hE hM hρ hρ₁ hstep hforcing

theorem tailNode_weighted_sq_tsum_le_of_recovery {μ a E : ℕ → ℝ} {M ρ : ℝ}
    (hμ : ∀ n, 0 ≤ μ n) (hE : ∀ n, 0 ≤ E n)
    (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hstep : ∀ n, μ (n + 1) * a (n + 1) ^ 2 ≤
      M * E (n + 1) + ρ * (μ n * a n ^ 2))
    (hforcing : Summable E) :
    (∑' n, μ n * a n ^ 2) ≤ (μ 0 * a 0 ^ 2 + M * ∑' n, E n) / (1 - ρ) :=
  tailNode_mass_tsum_le (fun n => mul_nonneg (hμ n) (sq_nonneg _))
    hE hM hρ hρ₁ hstep hforcing

/-- The forcing form used on the physical mass intervals: each `E n` is
the actual weighted square integral on `[left n, right n]`. Its summability
is supplied by the disjoint-cell decomposition of the continuous `L²` norm. -/
theorem tailNode_weighted_sq_summable_of_interval_recovery
    {μ a left right : ℕ → ℝ} {p u : ℝ → ℝ} {M ρ : ℝ}
    (hμ : ∀ n, 0 ≤ μ n) (hinterval : ∀ n, left n ≤ right n)
    (hp : ∀ n, ∀ x ∈ Icc (left n) (right n), 0 ≤ p x)
    (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hstep : ∀ n, μ (n + 1) * a (n + 1) ^ 2 ≤
      M * (∫ x in left (n + 1)..right (n + 1), p x * u x ^ 2) +
        ρ * (μ n * a n ^ 2))
    (hforcing : Summable (fun n => ∫ x in left n..right n, p x * u x ^ 2)) :
    Summable (fun n => μ n * a n ^ 2) := by
  apply tailNode_weighted_sq_summable_of_recovery hμ
    (fun n => intervalIntegral.integral_nonneg (hinterval n)
      (fun x hx => mul_nonneg (hp n x hx) (sq_nonneg _))) hM hρ hρ₁ hstep hforcing

end ContinuousFlexibility.Radial
