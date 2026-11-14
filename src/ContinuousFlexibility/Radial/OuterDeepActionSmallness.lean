module

public import ContinuousFlexibility.Radial.MorseTransitionBands
public import ContinuousFlexibility.Radial.R07DeepTailBounds

/-!
# Fine action bounds for the actual physical deep tail

The small products retain the true action j squared times A times the
square root of log(A/B). The adjacent mass and gap indices are treated
separately, so the estimate is uniform over the whole upper frequency
band and includes the left initial resistance interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- Squaring the true action controls both small scalar products. -/
theorem outer_deep_action_small_scales (M : MorseChainData) {j n : ℕ}
    (hj : 2 ≤ j) (hd : M.d n = morseChainInteger n) {ε : ℝ}
    (haction : (j : ℝ) ^ 2 * morseChainA M n *
      sqrt (log (morseChainA M n / morseChainB M n)) ≤ ε) :
    ((j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)) * morseChainA M n ^ 2 *
        log (morseChainA M n / morseChainB M n) ≤ ε ^ 2 ∧
      ((j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)) * morseChainA M n ^ 2 ≤
        ε ^ 2 / log 4 := by
  have hA : 0 < morseChainA M n :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds M n hd).1
  have hlog := morseTransition_log_ratio_lower M n hd
  have hlog4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
  have hlog0 : 0 ≤ log (morseChainA M n / morseChainB M n) :=
    hlog4.le.trans hlog
  have haction0 : 0 ≤ (j : ℝ) ^ 2 * morseChainA M n *
      sqrt (log (morseChainA M n / morseChainB M n)) := by positivity
  have hsq := (sq_le_sq₀ haction0 (haction0.trans haction)).2 haction
  have hsquare :
      ((j : ℝ) ^ 2 * morseChainA M n *
        sqrt (log (morseChainA M n / morseChainB M n))) ^ 2 =
        (j : ℝ) ^ 4 * morseChainA M n ^ 2 *
          log (morseChainA M n / morseChainB M n) := by
    rw [mul_pow, mul_pow, sq_sqrt hlog0]
    ring
  rw [hsquare] at hsq
  have hΛ4 : (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1) ≤ (j : ℝ) ^ 4 := by
    nlinarith only [sq_nonneg (j : ℝ)]
  have hcell : ((j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)) * morseChainA M n ^ 2 *
      log (morseChainA M n / morseChainB M n) ≤ ε ^ 2 :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hΛ4 (sq_nonneg _)) hlog0).trans hsq
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hj2 : (4 : ℝ) ≤ (j : ℝ) ^ 2 := by
    nlinarith only [hjR, sq_nonneg ((j : ℝ) - 2)]
  have hΛ : 0 ≤ (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1) :=
    mul_nonneg (sq_nonneg _) (by linarith only [hj2])
  refine ⟨hcell, (le_div_iff₀ hlog4).mpr ?_⟩
  exact (mul_le_mul_of_nonneg_left hlog
    (mul_nonneg hΛ (sq_nonneg _))).trans hcell

/-- The actual two small products have a bound quadratic in the true
action, with no frequency-dependent cutoff hidden in the constant. -/
theorem outer_deepTail_small_products_of_action
    {M : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds M σ D C) (right : Bool) {j start : ℕ}
    (hj : 2 ≤ j) (hstart : M.index < start) (η K : ℝ)
    (hclose : (r07DeepTailData M D right j start η K).endpoint -
      (r07DeepTailData M D right j start η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    {ε : ℝ}
    (haction : ∀ m, start ≤ m → (j : ℝ) ^ 2 * morseChainA M m *
      sqrt (log (morseChainA M m / morseChainB M m)) ≤ ε) (n : ℕ) :
    let Q := r07DeepTailData M D right j start η K
    Q.Λ * tailMass Q n * tailInnerResistance Q n +
        Q.Λ * tailGapMass Q n * tailResistance Q n ≤
      exp 2 * (C 0) ^ 2 * ε ^ 2 * (1 + (log 4)⁻¹) := by
  let Q := r07DeepTailData M D right j start η K
  let s := (if right then D.b else D.a) ^ 8
  have hs : 0 < s := by
    apply pow_pos
    have hD := r07_realization_geometry h
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hn : M.index < start + n := hstart.trans_le (Nat.le_add_right start n)
  have hg : start + n ≤ r07GapIndex right (start + n) := by
    cases right <;> simp [r07GapIndex]
  have hgn := hn.trans_le hg
  have hn0 := r07_realized_integrals_nonneg h right hn
  have hg0 := r07_realized_integrals_nonneg h right hgn
  have hc := r07_deepTail_integrals_compare h right hj hstart η K hclose n
  have hcell := r07_normalized_unitCompare_mul hs hc.1 hc.2.1 hn0.1 hn0.2.1
  have hgap := r07_normalized_unitCompare_mul hs hc.2.2.1 hc.2.2.2 hg0.2.2.1 hg0.2.2.2
  have hrawc := (r07_realized_small_products h hσ hb right hn.le).1
  have hrawg := (r07_realized_small_products h hσ hb right hgn.le).2
  have hac : Q.Λ * morseChainA M (start + n) ^ 2 *
      log (morseChainA M (start + n) / morseChainB M (start + n)) ≤ ε ^ 2 :=
    (outer_deep_action_small_scales M hj (h.d_eq _ hn.le)
      (haction _ (Nat.le_add_right start n))).1
  have hag : Q.Λ * morseChainA M (r07GapIndex right (start + n)) ^ 2 ≤ ε ^ 2 / log 4 :=
    (outer_deep_action_small_scales M hj (h.d_eq _ hgn.le)
      (haction _ ((Nat.le_add_right start n).trans hg))).2
  have hΛ : 0 ≤ Q.Λ := (r07_deepTail_lambda_pos hj).le
  have hsmallc : Q.Λ * tailMass Q n * tailInnerResistance Q n ≤
      exp 2 * (C 0) ^ 2 * ε ^ 2 := by
    calc
      _ = Q.Λ * (tailMass Q n * tailInnerResistance Q n) := by ring
      _ ≤ Q.Λ * (exp 2 * (morseCellMass M D right (start + n) *
          morseCellResistance M D right (start + n))) :=
        mul_le_mul_of_nonneg_left hcell.2 hΛ
      _ ≤ Q.Λ * (exp 2 * ((C 0) ^ 2 * morseChainA M (start + n) ^ 2 *
          log (morseChainA M (start + n) / morseChainB M (start + n)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrawc (exp_pos _).le) hΛ
      _ = (exp 2 * (C 0) ^ 2) *
          (Q.Λ * morseChainA M (start + n) ^ 2 *
            log (morseChainA M (start + n) / morseChainB M (start + n))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hac (by positivity)
  have hsmallg : Q.Λ * tailGapMass Q n * tailResistance Q n ≤
      exp 2 * (C 0) ^ 2 * (ε ^ 2 / log 4) := by
    calc
      _ = Q.Λ * (tailGapMass Q n * tailResistance Q n) := by ring
      _ ≤ Q.Λ * (exp 2 * (morseJoinMass M D right (r07GapIndex right (start + n)) *
          morseJoinResistance M D right (r07GapIndex right (start + n)))) :=
        mul_le_mul_of_nonneg_left hgap.2 hΛ
      _ ≤ Q.Λ * (exp 2 * ((C 0) ^ 2 * morseChainA M (r07GapIndex right (start + n)) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrawg (exp_pos _).le) hΛ
      _ = (exp 2 * (C 0) ^ 2) *
          (Q.Λ * morseChainA M (r07GapIndex right (start + n)) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hag (by positivity)
  calc
    _ ≤ exp 2 * (C 0) ^ 2 * ε ^ 2 + exp 2 * (C 0) ^ 2 * (ε ^ 2 / log 4) :=
      add_le_add hsmallc hsmallg
    _ = _ := by ring

/-- The left initial gap obeys the same fine action bound at its own
index; its smallness does not use the coarse exponential estimate. -/
theorem outer_deepTail_initial_small_of_action
    {M : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds M σ D C) {j start : ℕ}
    (hj : 2 ≤ j) (hstart : M.index < start) (η K : ℝ)
    (hclose : (r07DeepTailData M D false j start η K).endpoint -
      (r07DeepTailData M D false j start η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    {ε : ℝ}
    (haction : (j : ℝ) ^ 2 * morseChainA M start *
      sqrt (log (morseChainA M start / morseChainB M start)) ≤ ε) :
    let Q := r07DeepTailData M D false j start η K
    Q.Λ * tailInitialGapMass Q * tailInitialResistance Q ≤
      exp 2 * (C 0) ^ 2 * (ε ^ 2 / log 4) := by
  let Q := r07DeepTailData M D false j start η K
  have hs : 0 < D.a ^ 8 := pow_pos (r07_realization_geometry h).1 8
  have hi := r07_deepTail_initial_compare h false hj hstart η K hclose
  simp only [Bool.false_eq_true, if_false] at hi
  have hn0 := r07_realized_integrals_nonneg h false hstart
  have hgap := r07_normalized_unitCompare_mul hs hi.1 hi.2 hn0.2.2.1 hn0.2.2.2
  have hraw := (r07_realized_small_products h hσ hb false hstart.le).2
  have ha : Q.Λ * morseChainA M start ^ 2 ≤ ε ^ 2 / log 4 :=
    (outer_deep_action_small_scales M hj (h.d_eq _ hstart.le) haction).2
  have hΛ : 0 ≤ Q.Λ := (r07_deepTail_lambda_pos hj).le
  calc
    _ = Q.Λ * (tailInitialGapMass Q * tailInitialResistance Q) := by ring
    _ ≤ Q.Λ * (exp 2 * (morseJoinMass M D false start *
        morseJoinResistance M D false start)) :=
      mul_le_mul_of_nonneg_left hgap.2 hΛ
    _ ≤ Q.Λ * (exp 2 * ((C 0) ^ 2 * morseChainA M start ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hraw (exp_pos _).le) hΛ
    _ = (exp 2 * (C 0) ^ 2) * (Q.Λ * morseChainA M start ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ha (by positivity)

end ContinuousFlexibility.Radial

