module

public import ContinuousFlexibility.Analysis.FiniteJetRemainder
public import ContinuousFlexibility.Analysis.FiniteTaylorPolynomial
public import ContinuousFlexibility.Analysis.WeightedJetComposition

/-!
# Weighted bounds for finite Taylor remainders

Subtracting the full Taylor polynomial of degree `n` leaves a function
whose lower jets vanish and whose top derivative is bounded by twice the
given bound. On a convex set of radius `ρ`, this gives all the powers
`ρ ^ (n - j)` needed by the scale-invariant composition estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A finite Taylor remainder has radius-weighted bounds for its entire
jet through the chosen degree. -/
theorem norm_iteratedFDeriv_sub_finiteTaylor_le
    {G : E → F} (hG : ContDiff ℝ ∞ G)
    {K : Set E} (hK : Convex ℝ K) {q : E} (hq : q ∈ K)
    {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hradius : ∀ z ∈ K, ‖z - q‖ ≤ ρ) (n : ℕ)
    (hbound : ∀ z ∈ K, ‖iteratedFDeriv ℝ n G z‖ ≤ M)
    (j : ℕ) (hj : j ≤ n) {z : E} (hz : z ∈ K) :
    ‖iteratedFDeriv ℝ j (G - finiteTaylorPolynomial n G q) z‖ ≤
      (2 * M) * ρ ^ (n - j) := by
  have hP : ContDiff ℝ ∞ (finiteTaylorPolynomial n G q) :=
    contDiff_finiteTaylorPolynomial n G q
  have hzero : ∀ k : ℕ, k < n →
      iteratedFDeriv ℝ k (G - finiteTaylorPolynomial n G q) q = 0 := by
    intro k hk
    rw [iteratedFDeriv_sub_apply (hG.contDiffAt.of_le (by simp))
      (hP.contDiffAt.of_le (by simp)),
      iteratedFDeriv_finiteTaylorPolynomial_at hG hk.le, sub_self]
  have htop : ∀ y ∈ K,
      ‖iteratedFDeriv ℝ n (G - finiteTaylorPolynomial n G q) y‖ ≤ 2 * M := by
    intro y hy
    rw [iteratedFDeriv_sub_apply (hG.contDiffAt.of_le (by simp))
      (hP.contDiffAt.of_le (by simp)),
      iteratedFDeriv_finiteTaylorPolynomial_top hG]
    calc
      ‖iteratedFDeriv ℝ n G y - iteratedFDeriv ℝ n G q‖ ≤
          ‖iteratedFDeriv ℝ n G y‖ + ‖iteratedFDeriv ℝ n G q‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hbound y hy) (hbound q hq)
      _ = 2 * M := (two_mul M).symm
  exact norm_iteratedFDeriv_le_pow_of_zero_jet (hG.sub hP) hK hq
    (mul_nonneg (by norm_num) hM) hρ hradius n hzero htop j hj z hz

/-- Composing a Taylor remainder with a coordinate whose jets have the
reciprocal scale removes the scale from the final bound. -/
theorem norm_iteratedFDeriv_finiteTaylor_remainder_comp_le
    {f : H → E} {G : E → F} {U : Set H} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hG : ContDiff ℝ ∞ G)
    {x : H} (hx : x ∈ U) {K : Set E} (hK : Convex ℝ K)
    {q : E} (hq : q ∈ K) (hfx : f x ∈ K)
    {M ρ D : ℝ} (hM : 0 ≤ M) (hρ : 0 < ρ)
    (hradius : ∀ z ∈ K, ‖z - q‖ ≤ ρ) (n : ℕ)
    (hbound : ∀ z ∈ K, ‖iteratedFDeriv ℝ n G z‖ ≤ M)
    (hinner : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i f x‖ ≤ ρ * (D / ρ) ^ i) :
    ‖iteratedFDeriv ℝ n ((G - finiteTaylorPolynomial n G q) ∘ f) x‖ ≤
      (n.factorial : ℝ) * (2 * M) * D ^ n := by
  apply norm_iteratedFDeriv_comp_le_weighted hU hf
    (hG.sub (contDiff_finiteTaylorPolynomial n G q)) hx hρ n
  · intro i hi
    exact norm_iteratedFDeriv_sub_finiteTaylor_le hG hK hq hM hρ.le hradius n
      hbound i hi hfx
  · exact hinner

end ContinuousFlexibility.Analysis
