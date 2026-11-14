module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# Actual finite jets of a transported scalar field

Only C² regularity on the two open sets is used. The hypotheses bound
actual Fréchet derivatives at the evaluation point, and the conclusions
bound the actual derivatives of the product and composition there.
No extension or infinite-order smoothness is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A common bound for the first three outer jets and the first two
inner derivatives controls the actual composition jets through order two. -/
theorem n07b_norm_jet_comp_le_two
    {U : Set E} {V : Set F} {τ : E → F} {u : F → ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hτ : ContDiffOn ℝ 2 τ U) (hu : ContDiffOn ℝ 2 u V)
    (hmap : MapsTo τ U V) {x : E} (hx : x ∈ U)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (houter : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i u (τ x)‖ ≤ C)
    (hinner : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i τ x‖ ≤ R)
    {n : ℕ} (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (u ∘ τ) x‖ ≤ 2 * C * R ^ 2 := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hR2 : R ≤ R ^ 2 := by nlinarith
  have houter' (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i u V (τ x)‖ ≤ C := by
    rw [iteratedFDerivWithin_of_isOpen i hV (hmap hx)]
    exact houter i (hi.trans hn)
  have hinner' (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i τ U x‖ ≤ R ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hU hx]
    have hi2 : i ≤ 2 := hin.trans hn
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
    · simpa only [pow_one] using hinner 1 le_rfl (by norm_num)
    · exact (hinner 2 (by norm_num) le_rfl).trans hR2
  have hn' : (n : ℕ∞ω) ≤ 2 := by exact_mod_cast hn
  have h := norm_iteratedFDerivWithin_comp_le hu hτ hn'
    hV.uniqueDiffOn hU.uniqueDiffOn hmap hx houter' hinner'
  rw [iteratedFDerivWithin_of_isOpen n hU hx] at h
  have hfactorial : (n.factorial : ℝ) ≤ 2 := by
    interval_cases n <;> norm_num
  have hpower : R ^ n ≤ R ^ 2 := pow_le_pow_right₀ hR hn
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right hfactorial hC) hpower
    (pow_nonneg hR0 n) (mul_nonneg (by norm_num) hC))

/-- The binomial product estimate for the actual jets through order two. -/
theorem n07b_norm_jet_mul_le_two
    {U : Set E} {q g : E → ℝ} (hU : IsOpen U)
    (hq : ContDiffOn ℝ 2 q U) (hg : ContDiffOn ℝ 2 g U)
    {x : E} (hx : x ∈ U) {Q C : ℝ} (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (hqjet : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i q x‖ ≤ Q)
    (hgjet : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i g x‖ ≤ C)
    {n : ℕ} (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (fun y => q y * g y) x‖ ≤ 4 * Q * C := by
  have hn' : (n : ℕ∞ω) ≤ 2 := by exact_mod_cast hn
  calc
    _ = ‖iteratedFDerivWithin ℝ n (fun y => q y * g y) U x‖ := by
      rw [iteratedFDerivWithin_of_isOpen n hU hx]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i q U x‖ *
        ‖iteratedFDerivWithin ℝ (n - i) g U x‖ :=
      norm_iteratedFDerivWithin_mul_le hq hg hU.uniqueDiffOn hx hn'
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Q * C := by
      apply Finset.sum_le_sum
      intro i hi
      have hi2 : i ≤ 2 := by simp only [Finset.mem_range] at hi; omega
      have hni2 : n - i ≤ 2 := (Nat.sub_le n i).trans hn
      rw [iteratedFDerivWithin_of_isOpen i hU hx,
        iteratedFDerivWithin_of_isOpen (n - i) hU hx]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hqjet i hi2) (Nat.cast_nonneg _))
        (hgjet (n - i) hni2) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hQ)
    _ ≤ 4 * Q * C := by
      interval_cases n <;> norm_num [Finset.sum_range_succ] <;>
        nlinarith [mul_nonneg hQ hC]

/-- A finite C² transport has a polynomial bound depending only on
the indicated actual low-order jets at the two related points. -/
theorem n07b_norm_jet_transport_le_two
    {U : Set E} {V : Set F} {τ : E → F} {q : E → ℝ} {u : F → ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hq : ContDiffOn ℝ 2 q U) (hτ : ContDiffOn ℝ 2 τ U)
    (hu : ContDiffOn ℝ 2 u V) (hmap : MapsTo τ U V)
    {x : E} (hx : x ∈ U) {Q C R : ℝ}
    (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hqjet : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i q x‖ ≤ Q)
    (hujet : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i u (τ x)‖ ≤ C)
    (hτjet : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i τ x‖ ≤ R)
    {n : ℕ} (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (fun y => q y * u (τ y)) x‖ ≤ 8 * Q * C * R ^ 2 := by
  have hcomp (i : ℕ) (hi : i ≤ 2) :
      ‖iteratedFDeriv ℝ i (u ∘ τ) x‖ ≤ 2 * C * R ^ 2 :=
    n07b_norm_jet_comp_le_two hU hV hτ hu hmap hx hC hR hujet hτjet hi
  have h := n07b_norm_jet_mul_le_two hU hq (hu.comp hτ hmap) hx hQ
    (mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg R)) hqjet hcomp hn
  calc
    _ ≤ 4 * Q * (2 * C * R ^ 2) := h
    _ = _ := by ring

end ContinuousFlexibility.Analysis
