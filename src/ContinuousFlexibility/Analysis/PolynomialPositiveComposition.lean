import ContinuousFlexibility.Analysis.PolynomialJetComposition

/-!
# Composition of two lifts with bounded positive jets

Circle lifts themselves are unbounded. For a positive derivative order,
the chain rule is applied first, so every outer derivative used in the
remaining Faà di Bruno estimate has positive order as well.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology BigOperators

theorem norm_iteratedFDeriv_bilinear_polynomial_bound
    {ι E F G X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (f : ι → E → F) (g : ι → E → G)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i))
    (L : F →L[ℝ] G →L[ℝ] X) (n : ℕ)
    (hfb : ∀ k : ℕ, k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ A * W i ^ P)
    (hgb : ∀ k : ℕ, k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (g i) x‖ ≤ A * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => L (f i y) (g i y)) x‖ ≤ A * W i ^ P := by
  obtain ⟨A, P, hA, hP, hAb⟩ := finite_polynomial_majorant W hW U
    (fun k i x => ‖iteratedFDeriv ℝ k (f i) x‖) n hfb
  obtain ⟨B, Q, hB, hQ, hBb⟩ := finite_polynomial_majorant W hW U
    (fun k i x => ‖iteratedFDeriv ℝ k (g i) x‖) n hgb
  let K : ℝ := ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * A * B
  have hK : 0 ≤ K := Finset.sum_nonneg (fun k _ => by positivity)
  refine ⟨‖L‖ * K, P + Q, mul_nonneg (ContinuousLinearMap.opNorm_nonneg L) hK,
    add_nonneg hP hQ, fun i x hx => ?_⟩
  have h := L.norm_iteratedFDerivWithin_le_of_bilinear
    (hf i) (hg i) (hU i).uniqueDiffOn hx (n := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n (hU i) hx] at h
  have hsum : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
      ‖iteratedFDerivWithin ℝ k (f i) (U i) x‖ *
      ‖iteratedFDerivWithin ℝ (n - k) (g i) (U i) x‖) ≤ K * W i ^ (P + Q) := by
    dsimp only [K]
    rw [Finset.sum_mul]
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
  exact h.trans ((mul_le_mul_of_nonneg_left hsum (ContinuousLinearMap.opNorm_nonneg L)).trans_eq
    (mul_assoc _ _ _).symm)

theorem norm_iteratedFDeriv_comp_positive_polynomial_bound
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
    (hmap : ∀ i, MapsTo (f i) (U i) (V i)) (n : ℕ) (hn : 1 ≤ n)
    (houter : ∀ k : ℕ, 1 ≤ k → k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (g i) (f i x)‖ ≤ A * W i ^ P)
    (hinner : ∀ k : ℕ, 1 ≤ k → k ≤ n → ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ A * W i ^ P) :
    ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ n (fun y => g i (f i y)) x‖ ≤ A * W i ^ P := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let a (i : ι) (p : E) : F →L[ℝ] G := fderiv ℝ (g i) (f i p)
  let b (i : ι) (p : E) : E →L[ℝ] F := fderiv ℝ (f i) p
  have hdg (i : ι) : ContDiffOn ℝ ∞ (fderiv ℝ (g i)) (V i) :=
    (hg i).fderiv_of_isOpen (hV i) (by simp)
  have ha (i : ι) : ContDiffOn ℝ ∞ (a i) (U i) := by
    simpa only [Function.comp_def] using (hdg i).comp (hf i) (hmap i)
  have hb (i : ι) : ContDiffOn ℝ ∞ (b i) (U i) :=
    (hf i).fderiv_of_isOpen (hU i) (by simp)
  have hab (k : ℕ) (hk : k ≤ n) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i p, p ∈ U i → ‖iteratedFDeriv ℝ k (a i) p‖ ≤ A * W i ^ P := by
    apply norm_iteratedFDeriv_comp_polynomial_bound W hW U V hU hV f
      (fun i => fderiv ℝ (g i)) hf hdg hmap k
    · intro j hj
      obtain ⟨A, P, hA, hP, hb⟩ := houter (j + 1) (by omega) (by omega)
      refine ⟨A, P, hA, hP, fun i p hp => ?_⟩
      rw [norm_iteratedFDeriv_fderiv]
      exact hb i p hp
    · exact fun j hj hjk => hinner j hj (by omega)
  have hbb (k : ℕ) (hk : k ≤ n) : ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧
      ∀ i p, p ∈ U i → ‖iteratedFDeriv ℝ k (b i) p‖ ≤ A * W i ^ P := by
    obtain ⟨A, P, hA, hP, hb⟩ := hinner (k + 1) (by omega) (by omega)
    refine ⟨A, P, hA, hP, fun i p hp => ?_⟩
    rw [norm_iteratedFDeriv_fderiv]
    exact hb i p hp
  obtain ⟨A, P, hA, hP, hbound⟩ := norm_iteratedFDeriv_bilinear_polynomial_bound
    W hW U hU a b ha hb (ContinuousLinearMap.compL ℝ E F G) n hab hbb
  refine ⟨A, P, hA, hP, fun i p hp => ?_⟩
  have heq : fderiv ℝ (fun q => g i (f i q)) =ᶠ[𝓝 p]
      fun q => ContinuousLinearMap.compL ℝ E F G (a i q) (b i q) := by
    filter_upwards [(hU i).mem_nhds hp] with q hq
    rw [ContinuousLinearMap.compL_apply]
    exact fderiv_fun_comp q
      (((hg i).contDiffAt ((hV i).mem_nhds (hmap i hq))).differentiableAt (by simp))
      (((hf i).contDiffAt ((hU i).mem_nhds hq)).differentiableAt (by simp))
  rw [← norm_iteratedFDeriv_fderiv, (heq.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hbound i p hp

end ContinuousFlexibility.Analysis
