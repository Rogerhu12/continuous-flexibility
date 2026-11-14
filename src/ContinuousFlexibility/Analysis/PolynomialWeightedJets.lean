module

public import ContinuousFlexibility.Analysis.PolynomialJetComposition

/-!
# Exact height weights through mixed-jet composition and multiplication

A positive component height factor is kept unchanged in every finite
jet estimate. Only the auxiliary component power grows under the chain
and product rules. The functions and their derivatives remain the
original ones; normalization is used only for a finite scalar majorant.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators


theorem norm_iteratedFDeriv_clm_left_weighted_polynomial_bound
    {ι E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (W H : ι → ℝ) (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (f : ι → E → F) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (L : F →L[ℝ] G) (n : ℕ)
    (hbound : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (f i) x‖ ≤ A * H i * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => L (f i y)) x‖ ≤ A * H i * W i ^ P := by
  obtain ⟨A, P, hA, hP, hb⟩ := hbound
  refine ⟨‖L‖ * A, P, mul_nonneg (ContinuousLinearMap.opNorm_nonneg L) hA,
    hP, fun i x hx => ?_⟩
  have h := L.norm_iteratedFDeriv_comp_left
    ((hf i).contDiffAt ((hU i).mem_nhds hx)) (n := n) (by simp)
  have h' : ‖iteratedFDeriv ℝ n (fun y => L (f i y)) x‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ n (f i) x‖ := by
    simpa only [Function.comp_def] using h
  exact h'.trans ((mul_le_mul_of_nonneg_left (hb i x hx)
    (ContinuousLinearMap.opNorm_nonneg L)).trans_eq (by ring))

theorem norm_iteratedFDeriv_add_weighted_polynomial_bound
    {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W H : ι → ℝ) (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 < H i)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (f g : ι → E → F)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i)) (n : ℕ)
    (hfb : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (f i) x‖ ≤ A * H i * W i ^ P)
    (hgb : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (g i) x‖ ≤ A * H i * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => f i y + g i y) x‖ ≤ A * H i * W i ^ P := by
  obtain ⟨A, P, hA, hP, hb⟩ := hfb
  obtain ⟨B, Q, hB, hQ, hc⟩ := hgb
  refine ⟨A + B, P + Q, add_nonneg hA hB, add_nonneg hP hQ, fun i x hx => ?_⟩
  rw [fun_iteratedFDeriv_add_apply
    (((hf i).contDiffAt ((hU i).mem_nhds hx)).of_le (by simp))
    (((hg i).contDiffAt ((hU i).mem_nhds hx)).of_le (by simp))]
  have ha' : A * H i * W i ^ P ≤ A * H i * W i ^ (P + Q) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hW i) (le_add_of_nonneg_right hQ))
      (mul_nonneg hA (hH i).le)
  have hb' : B * H i * W i ^ Q ≤ B * H i * W i ^ (P + Q) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hW i) (le_add_of_nonneg_left hP))
      (mul_nonneg hB (hH i).le)
  exact (norm_add_le _ _).trans ((add_le_add (hb i x hx) (hc i x hx)).trans
    ((add_le_add ha' hb').trans_eq (by ring)))

theorem finite_weighted_polynomial_majorant
    {ι X : Type*} (W H : ι → ℝ) (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 < H i)
    (U : ι → Set X) (u : ℕ → ι → X → ℝ) (n : ℕ)
    (hbound : ∀ k : ℕ, k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → u k i x ≤ A * H i * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ k : ℕ, k ≤ n → ∀ i x, x ∈ U i → u k i x ≤ A * H i * W i ^ P := by
  have hnormalized (k : ℕ) (hk : k ≤ n) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → u k i x / H i ≤ A * W i ^ P := by
    obtain ⟨A, P, hA, hP, hb⟩ := hbound k hk
    refine ⟨A, P, hA, hP, fun i x hx => ?_⟩
    apply (div_le_iff₀ (hH i)).mpr
    exact (hb i x hx).trans_eq (by ring)
  obtain ⟨A, P, hA, hP, hb⟩ := finite_polynomial_majorant W hW U
    (fun k i x => u k i x / H i) n hnormalized
  refine ⟨A, P, hA, hP, fun k hk i x hx => ?_⟩
  exact ((div_le_iff₀ (hH i)).mp (hb k hk i x hx)).trans_eq (by ring)

theorem norm_iteratedFDeriv_comp_weighted_polynomial_bound
    {ι E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (W H : ι → ℝ) (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 < H i)
    (U : ι → Set E) (V : ι → Set F)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (f : ι → E → F) (g : ι → F → G)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (V i))
    (hmap : ∀ i, MapsTo (f i) (U i) (V i)) (n : ℕ)
    (houter : ∀ k : ℕ, k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (g i) (f i x)‖ ≤ A * H i * W i ^ P)
    (hinner : ∀ k : ℕ, 1 ≤ k → k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ A * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => g i (f i y)) x‖ ≤ A * H i * W i ^ P := by
  obtain ⟨C, P, hC, hP, hCb⟩ := finite_weighted_polynomial_majorant W H hW hH U
    (fun k i x => ‖iteratedFDeriv ℝ k (g i) (f i x)‖) n houter
  let v (k : ℕ) (i : ι) (x : E) : ℝ :=
    if k = 0 then 0 else ‖iteratedFDeriv ℝ k (f i) x‖
  have hv (k : ℕ) (hk : k ≤ n) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → v k i x ≤ A * W i ^ P := by
    by_cases hk0 : k = 0
    · exact ⟨0, 0, le_rfl, le_rfl, fun i x _ => by
        simp only [v, hk0, if_pos rfl, zero_mul, le_refl]⟩
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
      ‖iteratedFDerivWithin ℝ k (g i) (V i) (f i x)‖ ≤ C * H i * W i ^ P := by
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
  have heq : (n.factorial : ℝ) * (C * H i * W i ^ P) * ((1 + D) * W i ^ Q) ^ n =
      ((n.factorial : ℝ) * C * (1 + D) ^ n) * H i * W i ^ (P + Q * n) := by
    rw [Real.rpow_add hW₀, Real.rpow_mul_natCast hW₀.le, mul_pow]
    ring
  have hcomp : ‖iteratedFDeriv ℝ n (fun y => g i (f i y)) x‖ ≤
      (n.factorial : ℝ) * (C * H i * W i ^ P) * ((1 + D) * W i ^ Q) ^ n := by
    simpa only [Function.comp_def] using h
  exact hcomp.trans_eq heq

theorem norm_iteratedFDeriv_mul_weighted_polynomial_bound
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W H : ι → ℝ) (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 < H i)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) (f g : ι → E → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i)) (n : ℕ)
    (hfb : ∀ k : ℕ, k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ A * W i ^ P)
    (hgb : ∀ k : ℕ, k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (g i) x‖ ≤ A * H i * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => f i y * g i y) x‖ ≤ A * H i * W i ^ P := by
  obtain ⟨A, P, hA, hP, hAb⟩ := finite_polynomial_majorant W hW U
    (fun k i x => ‖iteratedFDeriv ℝ k (f i) x‖) n hfb
  obtain ⟨B, Q, hB, hQ, hBb⟩ := finite_weighted_polynomial_majorant W H hW hH U
    (fun k i x => ‖iteratedFDeriv ℝ k (g i) x‖) n hgb
  let K : ℝ := ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * A * B
  have hK : 0 ≤ K := Finset.sum_nonneg (fun k _ => by positivity)
  refine ⟨K, P + Q, hK, add_nonneg hP hQ, fun i x hx => ?_⟩
  have h := norm_iteratedFDerivWithin_mul_le (hf i) (hg i) (hU i).uniqueDiffOn hx
    (n := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n (hU i) hx] at h
  apply h.trans
  dsimp only [K]
  simp only [Finset.sum_mul]
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
