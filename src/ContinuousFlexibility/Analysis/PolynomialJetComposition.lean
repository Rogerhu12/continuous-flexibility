import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Fixed component powers under finite jet operations

A finite list of component-power bounds has one common majorant. The
ordinary Faà di Bruno and Leibniz estimates therefore preserve growth by
a fixed power of the component weight. Circle-lift values need not be
bounded: composition only uses positive-order jets of the inner map.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators

theorem finite_polynomial_majorant
    {ι X : Type*} (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i)
    (U : ι → Set X) (u : ℕ → ι → X → ℝ) (n : ℕ)
    (hbound : ∀ k : ℕ, k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → u k i x ≤ A * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ k : ℕ, k ≤ n → ∀ i x, x ∈ U i → u k i x ≤ A * W i ^ P := by
  classical
  have hfinite (k : Fin (n + 1)) := hbound k.val (Nat.le_of_lt_succ k.isLt)
  choose A P hA hP hb using hfinite
  let C : ℝ := ∑ k : Fin (n + 1), A k
  let R : ℝ := ∑ k : Fin (n + 1), P k
  have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => hA k)
  have hR : 0 ≤ R := Finset.sum_nonneg (fun k _ => hP k)
  refine ⟨C, R, hC, hR, fun k hk i x hx => ?_⟩
  let j : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  have hAj : A j ≤ C := Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ j)
  have hPj : P j ≤ R := Finset.single_le_sum (fun k _ => hP k) (Finset.mem_univ j)
  exact (hb j i x hx).trans (mul_le_mul hAj
    (Real.rpow_le_rpow_of_exponent_le (hW i) hPj)
    (Real.rpow_nonneg (zero_le_one.trans (hW i)) _) hC)

theorem norm_iteratedFDeriv_comp_polynomial_bound
    {ι E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i)
    (U : ι → Set E) (V : ι → Set F)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (f : ι → E → F) (g : ι → F → G)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (V i))
    (hmap : ∀ i, MapsTo (f i) (U i) (V i)) (n : ℕ)
    (houter : ∀ k : ℕ, k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (g i) (f i x)‖ ≤ A * W i ^ P)
    (hinner : ∀ k : ℕ, 1 ≤ k → k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ A * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => g i (f i y)) x‖ ≤ A * W i ^ P := by
  obtain ⟨C, P, hC, hP, hCb⟩ := finite_polynomial_majorant W hW U
    (fun k i x => ‖iteratedFDeriv ℝ k (g i) (f i x)‖) n houter
  let v (k : ℕ) (i : ι) (x : E) : ℝ :=
    if k = 0 then 0 else ‖iteratedFDeriv ℝ k (f i) x‖
  have hv (k : ℕ) (hk : k ≤ n) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → v k i x ≤ A * W i ^ P := by
    by_cases hk0 : k = 0
    · exact ⟨0, 0, le_rfl, le_rfl, fun i x _ => by simp only [v, hk0, if_pos rfl, zero_mul]⟩
    · obtain ⟨A, P, hA, hP, hb⟩ := hinner k (by omega) hk
      exact ⟨A, P, hA, hP, fun i x hx => by simpa only [v, if_neg hk0] using hb i x hx⟩
  obtain ⟨D, Q, hD, hQ, hDb⟩ := finite_polynomial_majorant W hW U v n hv
  refine ⟨(n.factorial : ℝ) * C * (1 + D) ^ n, P + Q * n,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) (pow_nonneg (by linarith) _),
    add_nonneg hP (mul_nonneg hQ (Nat.cast_nonneg _)), fun i x hx => ?_⟩
  have hW₀ : 0 < W i := zero_lt_one.trans_le (hW i)
  have hscale : 1 ≤ (1 + D) * W i ^ Q := by
    simpa only [one_mul] using mul_le_mul (show (1 : ℝ) ≤ 1 + D by linarith)
      (Real.one_le_rpow (hW i) hQ) zero_le_one (by linarith : (0 : ℝ) ≤ 1 + D)
  have hout (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDerivWithin ℝ k (g i) (V i) (f i x)‖ ≤ C * W i ^ P := by
    rw [iteratedFDerivWithin_of_isOpen k (hV i) (hmap i hx)]
    exact hCb k hk i x hx
  have hin (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
      ‖iteratedFDerivWithin ℝ k (f i) (U i) x‖ ≤ ((1 + D) * W i ^ Q) ^ k := by
    rw [iteratedFDerivWithin_of_isOpen k (hU i) hx]
    have hb : ‖iteratedFDeriv ℝ k (f i) x‖ ≤ D * W i ^ Q := by
      simpa only [v, if_neg (by omega : k ≠ 0)] using hDb k hkn i x hx
    have hle : D * W i ^ Q ≤ (1 + D) * W i ^ Q :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hW₀.le _)
    have hpow : (1 + D) * W i ^ Q ≤ ((1 + D) * W i ^ Q) ^ k := by
      simpa only [pow_one] using pow_le_pow_right₀ hscale hk
    exact hb.trans (hle.trans hpow)
  have h := norm_iteratedFDerivWithin_comp_le (hg i) (hf i) (n := n) (by simp)
    (hV i).uniqueDiffOn (hU i).uniqueDiffOn (hmap i) hx hout hin
  rw [iteratedFDerivWithin_of_isOpen n (hU i) hx] at h
  have heq : (n.factorial : ℝ) * (C * W i ^ P) * ((1 + D) * W i ^ Q) ^ n =
      ((n.factorial : ℝ) * C * (1 + D) ^ n) * W i ^ (P + Q * n) := by
    rw [Real.rpow_add hW₀, Real.rpow_mul_natCast hW₀.le, mul_pow]
    ring
  have hcomp : ‖iteratedFDeriv ℝ n (fun y => g i (f i y)) x‖ ≤
      (n.factorial : ℝ) * (C * W i ^ P) * ((1 + D) * W i ^ Q) ^ n := by
    simpa only [Function.comp_def] using h
  exact hcomp.trans_eq heq

theorem norm_iteratedFDeriv_mul_polynomial_bound
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i) (U : ι → Set E)
    (hU : ∀ i, IsOpen (U i)) (f g : ι → E → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i)) (n : ℕ)
    (hfb : ∀ k : ℕ, k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ A * W i ^ P)
    (hgb : ∀ k : ℕ, k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (g i) x‖ ≤ A * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => f i y * g i y) x‖ ≤ A * W i ^ P := by
  obtain ⟨A, P, hA, hP, hAb⟩ := finite_polynomial_majorant W hW U
    (fun k i x => ‖iteratedFDeriv ℝ k (f i) x‖) n hfb
  obtain ⟨B, Q, hB, hQ, hBb⟩ := finite_polynomial_majorant W hW U
    (fun k i x => ‖iteratedFDeriv ℝ k (g i) x‖) n hgb
  let K : ℝ := ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * A * B
  have hK : 0 ≤ K := Finset.sum_nonneg (fun k _ => by positivity)
  refine ⟨K, P + Q, hK, add_nonneg hP hQ, fun i x hx => ?_⟩
  have h := norm_iteratedFDerivWithin_mul_le (hf i) (hg i) (hU i).uniqueDiffOn hx
    (n := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n (hU i) hx] at h
  apply h.trans
  rw [K, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [iteratedFDerivWithin_of_isOpen k (hU i) hx,
    iteratedFDerivWithin_of_isOpen (n - k) (hU i) hx]
  have hterm := mul_le_mul
    (mul_le_mul_of_nonneg_left (hAb k hkn i x hx) (Nat.cast_nonneg (n.choose k)))
    (hBb (n - k) (Nat.sub_le n k) i x hx) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hA
      (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)))
  exact hterm.trans_eq (by rw [Real.rpow_add (zero_lt_one.trans_le (hW i))]; ring)

end ContinuousFlexibility.Analysis
