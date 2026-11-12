import ContinuousFlexibility.Scalar.HeightDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum

/-!
# Finite jet algebra for actual scalar coefficients

The product bound uses jets only through the current order n. Its
constant can nevertheless be chosen once for any larger fixed order b.
Coordinate differentiation is treated through one common fixed-direction
estimate, without introducing a second representation of the derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def n07bFiniteJetProductConstant (b : ℕ) : ℝ := (2 : ℝ) ^ b

theorem one_le_n07bFiniteJetProductConstant (b : ℕ) :
    1 ≤ n07bFiniteJetProductConstant b :=
  one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

/-- Actual product jets require bounds only up to n, even when the
constant is fixed at a larger order b. -/
theorem n07b_norm_jet_mul_le
    {U : Set E} {f g : E → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : E} (hx : x ∈ U) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {n b : ℕ}
    (hfj : ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hgj : ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i g x‖ ≤ B)
    (hn : n ≤ b) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      n07bFiniteJetProductConstant b * A * B := by
  have hchoose : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have hpower : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ b :=
    pow_le_pow_right₀ (by norm_num) hn
  calc
    _ = ‖iteratedFDerivWithin ℝ n (fun y => f y * g y) U x‖ := by
      rw [iteratedFDerivWithin_of_isOpen n hU hx]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ *
        ‖iteratedFDerivWithin ℝ (n - i) g U x‖ :=
      norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx (by simp)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [iteratedFDerivWithin_of_isOpen i hU hx,
        iteratedFDerivWithin_of_isOpen (n - i) hU hx]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfj i hin) (Nat.cast_nonneg _))
        (hgj (n - i) (Nat.sub_le n i)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ n * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
    _ ≤ n07bFiniteJetProductConstant b * A * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpower hA) hB

/-- The actual additive jet obeys the ordinary norm triangle inequality. -/
theorem n07b_norm_jet_add_le
    {U : Set E} {f g : E → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : E} (hx : x ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n g x‖ := by
  have hfAt : ContDiffAt ℝ n f x :=
    ((hf x hx).contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  have hgAt : ContDiffAt ℝ n g x :=
    ((hg x hx).contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  have h := norm_add_le (iteratedFDeriv ℝ n f x) (iteratedFDeriv ℝ n g x)
  rw [← iteratedFDeriv_add_apply hfAt hgAt] at h
  have hfg : f + g = (fun y => f y + g y) := rfl
  rw [hfg] at h
  exact h

/-- Evaluation of the genuine derivative in a fixed direction loses
exactly one derivative and its vector norm. -/
theorem n07b_norm_jet_directional_le
    {U : Set E} {f : E → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) (n : ℕ) (v : E) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have hfAt : ContDiffAt ℝ ∞ f x := (hf x hx).contDiffAt (hU.mem_nhds hx)
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hfAt.fderiv_right (by simp)
  have h := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ f) (c := v) (x := x) (n := n) hd (by simp)
  simpa only [norm_iteratedFDeriv_fderiv] using h

theorem n07b_norm_jet_radialPartial_le
    {U : Set PolarPoint} {f : PolarPoint → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : PolarPoint} (hx : x ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (radialPartial f) x‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  change ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (1, 0)) x‖ ≤
    ‖iteratedFDeriv ℝ (n + 1) f x‖
  have hv : ‖((1, 0) : PolarPoint)‖ = 1 := by norm_num [Prod.norm_mk]
  simpa only [hv, one_mul] using
    n07b_norm_jet_directional_le hU hf hx n ((1, 0) : PolarPoint)

theorem n07b_norm_jet_angularPartial_le
    {U : Set PolarPoint} {f : PolarPoint → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : PolarPoint} (hx : x ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (angularPartial f) x‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  change ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (0, 1)) x‖ ≤
    ‖iteratedFDeriv ℝ (n + 1) f x‖
  have hv : ‖((0, 1) : PolarPoint)‖ = 1 := by norm_num [Prod.norm_mk]
  simpa only [hv, one_mul] using
    n07b_norm_jet_directional_le hU hf hx n ((0, 1) : PolarPoint)

end ContinuousFlexibility.Analysis
