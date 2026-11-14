module

public import ContinuousFlexibility.Radial.R07DeepTailComparison

/-!
# Numerical bounds for the actual outward logarithmic tail
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem r07_core_integrals_nonneg {D : ReferenceData} (hD : RadialProfileGeometry D)
    {a b : ℝ} (ha : a ∈ radialCore D) (hb : b ∈ radialCore D) (hab : a ≤ b) :
    0 ≤ (∫ r in a..b, D.w r * r ^ 6) ∧
      0 ≤ (∫ r in a..b, (D.w r * r ^ 8)⁻¹) := by
  have hp (r : ℝ) (hr : r ∈ Icc a b) : 0 < D.w r ∧ 0 < r := by
    have hc : r ∈ radialCore D := ordConnected_Ioo.uIcc_subset ha hb (Icc_subset_uIcc hr)
    exact ⟨hD.2.2.2.2.1 r hc, hD.1.trans hc.1⟩
  exact ⟨intervalIntegral.integral_nonneg hab (fun r hr => by
      obtain ⟨hw, hrp⟩ := hp r hr
      positivity),
    intervalIntegral.integral_nonneg hab (fun r hr => by
      obtain ⟨hw, hrp⟩ := hp r hr
      positivity)⟩

theorem r07_realized_integrals_nonneg {T : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (side : Bool) {n : ℕ} (hn : T.index < n) :
    0 ≤ morseCellMass T D side n ∧ 0 ≤ morseCellResistance T D side n ∧
      0 ≤ morseJoinMass T D side n ∧ 0 ≤ morseJoinResistance T D side n := by
  have hc := r07_chain_mass_cuts_core h side hn.le
  have hcell := r07_core_integrals_nonneg (r07_realization_geometry h) hc.1 hc.2.1
    (r07_chain_model_cuts h side hn.le).1.le
  have hgap := r07_core_integrals_nonneg (r07_realization_geometry h) hc.2.1
    (r07_chain_resistanceEnd_core h side hn)
    (r07_chain_massEnd_lt_resistanceEnd h side hn).le
  exact ⟨hcell.1, hcell.2, hgap.1, hgap.2⟩

theorem r07_deepTail_small_products {T : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds T σ D C) (right : Bool) {j start : ℕ}
    (hj : 2 ≤ j) (hstart : T.index < start) (h32 : 32 ≤ start) (η K : ℝ)
    (hclose : (r07DeepTailData T D right j start η K).endpoint -
      (r07DeepTailData T D right j start η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹) (n : ℕ) :
    let Q := r07DeepTailData T D right j start η K
    Q.Λ * tailMass Q n * tailInnerResistance Q n +
        Q.Λ * tailGapMass Q n * tailResistance Q n ≤
      (162 * exp 2 * Q.Λ * (C 0) ^ 2) * exp (-((start + n : ℕ) : ℝ)) := by
  let Q := r07DeepTailData T D right j start η K
  let s := (if right then D.b else D.a) ^ 8
  have hs : 0 < s := by
    apply pow_pos
    have hD := r07_realization_geometry h
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hn : T.index < start + n := hstart.trans_le (Nat.le_add_right start n)
  have hn32 : 32 ≤ start + n := h32.trans (Nat.le_add_right start n)
  have hg : start + n ≤ r07GapIndex right (start + n) := by cases right <;> simp [r07GapIndex]
  have hgn := hn.trans_le hg
  have hgn32 := hn32.trans hg
  have hn0 := r07_realized_integrals_nonneg h right hn
  have hg0 := r07_realized_integrals_nonneg h right hgn
  have hc := r07_deepTail_integrals_compare h right hj hstart η K hclose n
  have hcell := r07_normalized_unitCompare_mul hs hc.1 hc.2.1 hn0.1 hn0.2.1
  have hgap := r07_normalized_unitCompare_mul hs hc.2.2.1 hc.2.2.2 hg0.2.2.1 hg0.2.2.2
  have hrawc := (r07_realized_small_products_coarse h hσ hb right hn.le (by omega)).1
  have hrawg := (r07_realized_small_products_coarse h hσ hb right hgn.le (by omega)).2
  have hexp : exp (-((r07GapIndex right (start + n) : ℕ) : ℝ)) ≤
      exp (-((start + n : ℕ) : ℝ)) := exp_le_exp.mpr (neg_le_neg (Nat.cast_le.mpr hg))
  have hC : 0 < C 0 := h.constants_pos 0
  have hsmallc : tailMass Q n * tailInnerResistance Q n ≤
      (81 * exp 2 * (C 0) ^ 2) * exp (-((start + n : ℕ) : ℝ)) := by
    calc
      _ ≤ exp 2 * (morseCellMass T D right (start + n) *
          morseCellResistance T D right (start + n)) := hcell.2
      _ ≤ exp 2 * (81 * (C 0) ^ 2 * exp (-((start + n : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hrawc (exp_pos _).le
      _ = _ := by ring
  have hsmallg : tailGapMass Q n * tailResistance Q n ≤
      (81 * exp 2 * (C 0) ^ 2) * exp (-((start + n : ℕ) : ℝ)) := by
    calc
      _ ≤ exp 2 * (morseJoinMass T D right (r07GapIndex right (start + n)) *
          morseJoinResistance T D right (r07GapIndex right (start + n))) := hgap.2
      _ ≤ exp 2 * (81 * (C 0) ^ 2 * exp (-((r07GapIndex right (start + n) : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hrawg (exp_pos _).le
      _ ≤ exp 2 * (81 * (C 0) ^ 2 * exp (-((start + n : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity)) (exp_pos _).le
      _ = _ := by ring
  have hΛ : 0 ≤ Q.Λ := (r07_deepTail_lambda_pos hj).le
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hsmallc hΛ)
    (mul_le_mul_of_nonneg_left hsmallg hΛ)
  nlinarith only [hsum]

theorem r07_deepTail_adjacent_products {T : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2)
    (hb : MorseMassResistanceBounds T σ D C) (right : Bool) {j start : ℕ}
    (hj : 2 ≤ j) (hstart : T.index < start) (h32 : 32 ≤ start) (η K : ℝ)
    (hclose : (r07DeepTailData T D right j start η K).endpoint -
      (r07DeepTailData T D right j start η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    (n k : ℕ) (hk : k = n ∨ k = n + 1) :
    let Q := r07DeepTailData T D right j start η K
    (exp (-2) * Q.Λ / (C 0) ^ 2) * exp ((start + n : ℕ) : ℝ) ≤
        Q.Λ * tailMass Q k * tailResistance Q n ∧
      tailGapMass Q n ≤ ((exp 2 * (C 0) ^ 2) * exp (-((start + n : ℕ) : ℝ))) * tailMass Q k ∧
      (exp (-2) * Q.Λ / (C 0) ^ 2) *
          exp (2 * ((start + n : ℕ) : ℝ) ^ 2 -
            10 * ((start + n : ℕ) : ℝ) ^ (3 / 2 : ℝ) - 4 * (start + n : ℕ) - 51) ≤
        Q.Λ * tailMass Q k * tailResistance Q n := by
  let Q := r07DeepTailData T D right j start η K
  let s := (if right then D.b else D.a) ^ 8
  have hs : 0 < s := by
    apply pow_pos
    have hD := r07_realization_geometry h
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hn : T.index < start + n := hstart.trans_le (Nat.le_add_right start n)
  have hn32 : 32 ≤ start + n := h32.trans (Nat.le_add_right start n)
  have hkn : start + k = start + n ∨ start + k = start + n + 1 := by
    rcases hk with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Nat.add_assoc start n 1).symm
  have hgn : r07GapIndex right (start + n) = start + n ∨
      r07GapIndex right (start + n) = start + n + 1 := by
    cases right
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hkg : T.index < start + k := hstart.trans_le (Nat.le_add_right start k)
  have hgg : T.index < r07GapIndex right (start + n) := by
    rcases hgn with hgn | hgn <;> rw [hgn] <;> omega
  have hk0 := r07_realized_integrals_nonneg h right hkg
  have hg0 := r07_realized_integrals_nonneg h right hgg
  have hkC := r07_deepTail_integrals_compare h right hj hstart η K hclose k
  have hnC := r07_deepTail_integrals_compare h right hj hstart η K hclose n
  have hp := r07_normalized_unitCompare_mul hs hkC.1 hnC.2.2.2 hk0.1 hg0.2.2.2
  have hr := r07_realized_adjacent_products h hσ hb right hn32 hn.le hkn hgn
  have hΛ : 0 ≤ Q.Λ := (r07_deepTail_lambda_pos hj).le
  have hscaled (z : ℝ) (hz : z / (C 0) ^ 2 ≤
      morseCellMass T D right (start + k) *
        morseJoinResistance T D right (r07GapIndex right (start + n))) :
      (exp (-2) * Q.Λ / (C 0) ^ 2) * z ≤ Q.Λ * tailMass Q k * tailResistance Q n := by
    calc
      _ = Q.Λ * (exp (-2) * (z / (C 0) ^ 2)) := by ring
      _ ≤ Q.Λ * (exp (-2) * (morseCellMass T D right (start + k) *
          morseJoinResistance T D right (r07GapIndex right (start + n)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz (exp_pos _).le) hΛ
      _ ≤ Q.Λ * (tailMass Q k * tailResistance Q n) := mul_le_mul_of_nonneg_left hp.1 hΛ
      _ = _ := by ring
  refine ⟨hscaled _ hr.1, ?_, hscaled _ hr.2.2⟩
  have hnrm : s⁻¹ * morseJoinMass T D right (r07GapIndex right (start + n)) ≤
      ((C 0) ^ 2 * exp (-((start + n : ℕ) : ℝ))) *
        (s⁻¹ * morseCellMass T D right (start + k)) := by
    simpa only [mul_left_comm s⁻¹] using
      mul_le_mul_of_nonneg_left hr.2.1 (inv_nonneg.mpr hs.le)
  have hdom := r07_unitCompare_domination hnC.2.2.1 hkC.1 (by positivity) hnrm
  convert hdom using 1 <;> ring

theorem r07_deepTail_initial_bounds {T : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds T σ D C) {j start : ℕ}
    (hj : 2 ≤ j) (hstart : T.index < start) (h32 : 32 ≤ start) (η K : ℝ)
    (hclose : (r07DeepTailData T D false j start η K).endpoint -
      (r07DeepTailData T D false j start η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹) :
    let Q := r07DeepTailData T D false j start η K
    Q.Λ * tailInitialGapMass Q * tailInitialResistance Q ≤
        (162 * exp 2 * Q.Λ * (C 0) ^ 2) * exp (-(start : ℝ)) ∧
      tailInitialGapMass Q ≤ ((exp 2 * (C 0) ^ 2) * exp (-(start : ℝ))) * tailMass Q 0 ∧
      (exp (-2) * Q.Λ / (C 0) ^ 2) * exp (start : ℝ) ≤
        Q.Λ * tailMass Q 0 * tailInitialResistance Q := by
  let Q := r07DeepTailData T D false j start η K
  have hs : 0 < D.a ^ 8 := pow_pos (r07_realization_geometry h).1 8
  have hc := r07_deepTail_integrals_compare h false hj hstart η K hclose 0
  have hi := r07_deepTail_initial_compare h false hj hstart η K hclose
  simp only [Bool.false_eq_true, if_false, Nat.add_zero] at hi hc
  have hn0 := r07_realized_integrals_nonneg h false hstart
  have hgap := r07_normalized_unitCompare_mul hs hi.1 hi.2 hn0.2.2.1 hn0.2.2.2
  have hbig := r07_normalized_unitCompare_mul hs hc.1 hi.2 hn0.1 hn0.2.2.2
  have hrawsmall := (r07_realized_small_products_coarse h hσ hb false hstart.le (by omega)).2
  have hraw := r07_realized_adjacent_products h hσ hb false h32 hstart.le (Or.inl rfl) (Or.inl rfl)
  have hΛ : 0 ≤ Q.Λ := (r07_deepTail_lambda_pos hj).le
  have hC := h.constants_pos 0
  refine ⟨?_, ?_, ?_⟩
  · have hsm := mul_le_mul_of_nonneg_left
      (hgap.2.trans (mul_le_mul_of_nonneg_left hrawsmall (exp_pos _).le)) hΛ
    have hx : 0 ≤ exp 2 * Q.Λ * (C 0) ^ 2 * exp (-(start : ℝ)) := by positivity
    nlinarith only [hsm, hx]
  · have hnrm : (D.a ^ 8)⁻¹ * morseJoinMass T D false start ≤
        ((C 0) ^ 2 * exp (-(start : ℝ))) * ((D.a ^ 8)⁻¹ * morseCellMass T D false start) := by
      simpa only [mul_left_comm ((D.a ^ 8)⁻¹)] using
        mul_le_mul_of_nonneg_left hraw.2.1 (inv_nonneg.mpr hs.le)
    have hdom := r07_unitCompare_domination hi.1 hc.1 (by positivity) hnrm
    convert hdom using 1 <;> ring
  · calc
      _ = Q.Λ * (exp (-2) * (exp (start : ℝ) / (C 0) ^ 2)) := by ring
      _ ≤ Q.Λ * (exp (-2) * (morseCellMass T D false start * morseJoinResistance T D false start)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hraw.1 (exp_pos _).le) hΛ
      _ ≤ Q.Λ * (tailMass Q 0 * tailInitialResistance Q) := mul_le_mul_of_nonneg_left hbig.1 hΛ
      _ = _ := by ring

end ContinuousFlexibility.Radial
