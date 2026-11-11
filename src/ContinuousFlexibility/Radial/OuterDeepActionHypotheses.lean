import ContinuousFlexibility.Radial.OuterDeepActionSmallness
import ContinuousFlexibility.Radial.R07DeepTailSharp

/-!
# Deep hypotheses from fine physical action estimates

Only the small-product input differs from the fixed-frequency R07
construction. All geometric, adjacent large-product and mass-ratio
conditions are the existing conclusions for the actual realized profile.
The remaining two numerical conditions are independent of the frequency.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem outer_deepTail_hypotheses_of_action
    {M : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds M σ D C) (right : Bool) {j start : ℕ}
    (hj : 2 ≤ j) (hstart : M.index < start) (h32 : 32 ≤ start) {η K ε : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hK : 1 < K)
    (hclose : (r07DeepTailData M D right j start η K).endpoint -
      (r07DeepTailData M D right j start η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    (haction : ∀ m, start ≤ m → (j : ℝ) ^ 2 * morseChainA M m *
      sqrt (log (morseChainA M m / morseChainB M m)) ≤ ε)
    (hsmall : exp 2 * (C 0) ^ 2 * ε ^ 2 * (1 + (log 4)⁻¹) ≤ η)
    (hratio : exp 2 * (C 0) ^ 2 * exp (-(start : ℝ)) ≤ η)
    (hbig : K ≤ (exp (-2) / (C 0) ^ 2) * exp (start : ℝ)) :
    DeepTailHypotheses (r07DeepTailData M D right j start η K) := by
  let Q := r07DeepTailData M D right j start η K
  have hΛ : 0 < Q.Λ := r07_deepTail_lambda_pos hj
  have hΛ1 : 1 ≤ Q.Λ := r07_deepTail_lambda_one_le hj
  have hcoef : exp (-2) / (C 0) ^ 2 ≤ exp (-2) * Q.Λ / (C 0) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hΛ1 (exp_pos (-2)).le
  have hbigΛ : K ≤ (exp (-2) * Q.Λ / (C 0) ^ 2) * exp (start : ℝ) :=
    hbig.trans (mul_le_mul_of_nonneg_right hcoef (exp_pos _).le)
  have hinitialSmall : exp 2 * (C 0) ^ 2 * (ε ^ 2 / log 4) ≤ η := by
    apply le_trans _ hsmall
    calc
      _ = (exp 2 * (C 0) ^ 2 * ε ^ 2) * (log 4)⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith : (log (4 : ℝ))⁻¹ ≤ 1 + (log 4)⁻¹)
        (by positivity)
  have hden := r07_deepTail_density_properties h right j hstart η K
  have hnode := r07_deepTail_node_bounds h right j hstart η K 0
  have hmass (n : ℕ) : 0 ≤ tailMass Q n :=
    r07_deepTail_mass_nonneg h right j hstart η K n
  refine ⟨r07_deepTail_entrance_lt_endpoint h right j hstart η K, hnode.1, hΛ, ?_,
    hη, hη1, hK, hden.1, hden.2, r07_deepTail_nodes_tendsto h right j hstart η K, ?_⟩
  · cases right
    · have hi := r07_deepTail_initial_bounds h hσ hb hj hstart h32 η K hclose
      have hs := outer_deepTail_initial_small_of_action h hσ hb hj hstart η K hclose
        (haction start le_rfl)
      refine Or.inr ⟨r07_deepTail_initial_order h false j hstart η K,
        hs.trans hinitialSmall, ?_, hbigΛ.trans hi.2.2⟩
      exact hi.2.1.trans (mul_le_mul_of_nonneg_right hratio (hmass 0))
    · exact Or.inl (r07_deepTail_initial_order h true j hstart η K).symm
  · intro n
    have ho := r07_deepTail_interval_order h right j hstart η K n
    have hs := outer_deepTail_small_products_of_action h hσ hb right hj hstart η K
      hclose haction n
    have hn := r07_deepTail_adjacent_products h hσ hb right hj hstart h32 η K hclose
      n n (Or.inl rfl)
    have hnext := r07_deepTail_adjacent_products h hσ hb right hj hstart h32 η K hclose
      n (n + 1) (Or.inr rfl)
    have hcast : (start : ℝ) ≤ ((start + n : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right start n
    have hexp := exp_le_exp.mpr (neg_le_neg hcast)
    have hratn : exp 2 * (C 0) ^ 2 * exp (-((start + n : ℕ) : ℝ)) ≤ η :=
      (mul_le_mul_of_nonneg_left hexp (by positivity)).trans hratio
    have hbign : K ≤ (exp (-2) * Q.Λ / (C 0) ^ 2) * exp ((start + n : ℕ) : ℝ) :=
      hbigΛ.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hcast) (by positivity))
    refine ⟨ho.1, ho.2, hs.trans hsmall, hbign.trans hn.1, hbign.trans hnext.1, ?_⟩
    change tailGapMass Q n ≤ η * min (tailMass Q n) (tailMass Q (n + 1))
    rw [mul_min_of_nonneg _ _ hη.le]
    exact le_min
      (hn.2.1.trans (mul_le_mul_of_nonneg_right hratn (hmass n)))
      (hnext.2.1.trans (mul_le_mul_of_nonneg_right hratn (hmass (n + 1))))

end ContinuousFlexibility.Radial

