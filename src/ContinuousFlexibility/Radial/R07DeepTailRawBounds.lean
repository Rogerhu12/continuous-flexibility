module

public import ContinuousFlexibility.Radial.R07DeepTailNumerics

/-!
# Uniform products of the actual radial masses and resistances

These estimates are direct consequences of `MorseMassResistanceBounds`.
All amplitude factors cancel at a single index; adjacent ratios are
controlled by the numerical estimates of the prescribed Morse chain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

theorem r07_realized_mass_pos {T : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds T σ D C) (side : Bool) {n : ℕ} (hn : T.index ≤ n) :
    0 < morseCellMass T D side n ∧ 0 < morseJoinResistance T D side n := by
  have hlam := morseChainAmplitude_pos T σ hσ n
  have hA : 0 < morseChainA T n :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T n (h.d_eq n hn)).1
  have hC := h.constants_pos 0
  have hnB := hb side n hn
  exact ⟨(div_pos (mul_pos hlam (pow_pos hA 2)) hC).trans_le hnB.1,
    (div_pos (mul_pos (inv_pos.mpr hlam) (rpow_pos_of_pos hA _)) hC).trans_le
      hnB.2.2.2.2.1⟩

theorem r07_realized_model_comparisons {T : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds T σ D C) (side : Bool) {m g : ℕ}
    (hm : T.index ≤ m) (hg : T.index ≤ g) :
    ((morseChainAmplitude T σ m / morseChainAmplitude T σ g) *
        morseChainA T m ^ 2 / morseChainA T g ^ 4) / (C 0) ^ 2 ≤
      morseCellMass T D side m * morseJoinResistance T D side g ∧
    morseJoinMass T D side g / morseCellMass T D side m ≤
      (C 0) ^ 2 * ((morseChainAmplitude T σ g / morseChainAmplitude T σ m) *
        morseChainA T g ^ 6 / morseChainA T m ^ 2) := by
  have hC := h.constants_pos 0
  have hlm := morseChainAmplitude_pos T σ hσ m
  have hlg := morseChainAmplitude_pos T σ hσ g
  have hAm : 0 < morseChainA T m :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T m (h.d_eq m hm)).1
  have hAg : 0 < morseChainA T g :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T g (h.d_eq g hg)).1
  have hmB := hb side m hm
  have hgB := hb side g hg
  have hμ := (r07_realized_mass_pos h hσ hb side hm).1
  have hp : morseChainA T g ^ (-4 : ℝ) = (morseChainA T g ^ 4)⁻¹ := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num,
      rpow_neg hAg.le, rpow_natCast]
  rw [hp] at hgB
  constructor
  · calc
      _ = (morseChainAmplitude T σ m * morseChainA T m ^ 2 / C 0) *
          ((morseChainAmplitude T σ g)⁻¹ * (morseChainA T g ^ 4)⁻¹ / C 0) := by
        field_simp [hlg.ne', hAg.ne', hC.ne']
        <;> ring
      _ ≤ _ := mul_le_mul hmB.1 hgB.2.2.2.2.1 (by positivity) hμ.le
  · calc
      _ ≤ (C 0 * morseChainAmplitude T σ g * morseChainA T g ^ 6) /
          morseCellMass T D side m :=
        div_le_div_of_nonneg_right hgB.2.2.2.1 hμ.le
      _ ≤ (C 0 * morseChainAmplitude T σ g * morseChainA T g ^ 6) /
          (morseChainAmplitude T σ m * morseChainA T m ^ 2 / C 0) :=
        div_le_div_of_nonneg_left (by positivity)
          (div_pos (mul_pos hlm (pow_pos hAm 2)) hC) hmB.1
      _ = _ := by
        field_simp [hlm.ne', hAm.ne', hC.ne']
        <;> ring

theorem r07_realized_small_products {T : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds T σ D C) (side : Bool) {n : ℕ} (hn : T.index ≤ n) :
    morseCellMass T D side n * morseCellResistance T D side n ≤
        (C 0) ^ 2 * morseChainA T n ^ 2 * log (morseChainA T n / morseChainB T n) ∧
      morseJoinMass T D side n * morseJoinResistance T D side n ≤
        (C 0) ^ 2 * morseChainA T n ^ 2 := by
  have hC := h.constants_pos 0
  have hlam := morseChainAmplitude_pos T σ hσ n
  have hA : 0 < morseChainA T n :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T n (h.d_eq n hn)).1
  have hlog := (r07_log_A_div_B_bound T n (h.d_eq n hn)).1
  have hnB := hb side n hn
  have hpos := r07_realized_mass_pos h hσ hb side hn
  have hp : morseChainA T n ^ (-4 : ℝ) = (morseChainA T n ^ 4)⁻¹ := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num,
      rpow_neg hA.le, rpow_natCast]
  rw [hp] at hnB
  constructor
  · calc
      _ ≤ morseCellMass T D side n * (C 0 / morseChainAmplitude T σ n *
          log (morseChainA T n / morseChainB T n)) :=
        mul_le_mul_of_nonneg_left hnB.2.2.1 hpos.1.le
      _ ≤ (C 0 * morseChainAmplitude T σ n * morseChainA T n ^ 2) *
          (C 0 / morseChainAmplitude T σ n * log (morseChainA T n / morseChainB T n)) :=
        mul_le_mul_of_nonneg_right hnB.2.1 (by positivity)
      _ = _ := by field_simp [hlam.ne']
  · calc
      _ ≤ (C 0 * morseChainAmplitude T σ n * morseChainA T n ^ 6) *
          morseJoinResistance T D side n :=
        mul_le_mul_of_nonneg_right hnB.2.2.2.1 hpos.2.le
      _ ≤ (C 0 * morseChainAmplitude T σ n * morseChainA T n ^ 6) *
          (C 0 * (morseChainAmplitude T σ n)⁻¹ * (morseChainA T n ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_left hnB.2.2.2.2.2 (by positivity)
      _ = _ := by field_simp [hlam.ne', hA.ne']

theorem r07_realized_small_products_coarse
    {T : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) (hn8 : 8 ≤ n) :
    morseCellMass T D side n * morseCellResistance T D side n ≤
        81 * (C 0) ^ 2 * exp (-(n : ℝ)) ∧
      morseJoinMass T D side n * morseJoinResistance T D side n ≤
        81 * (C 0) ^ 2 * exp (-(n : ℝ)) := by
  have hs := r07_realized_small_products h hσ hb side hn
  have hnS := r07_deep_small_scales T hn8 (h.d_eq n hn)
  constructor
  · calc
      _ ≤ (C 0) ^ 2 * (morseChainA T n ^ 2 *
          log (morseChainA T n / morseChainB T n)) := by simpa only [mul_assoc] using hs.1
      _ ≤ (C 0) ^ 2 * (81 * exp (-(n : ℝ))) :=
        mul_le_mul_of_nonneg_left hnS.2 (sq_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ (C 0) ^ 2 * morseChainA T n ^ 2 := hs.2
      _ ≤ (C 0) ^ 2 * (81 * exp (-(n : ℝ))) :=
        mul_le_mul_of_nonneg_left hnS.1 (sq_nonneg _)
      _ = _ := by ring

theorem r07_realized_adjacent_products
    {T : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds T σ D C) (side : Bool) {n m g : ℕ}
    (hn : 32 ≤ n) (hN : T.index ≤ n)
    (hm : m = n ∨ m = n + 1) (hg : g = n ∨ g = n + 1) :
    exp (n : ℝ) / (C 0) ^ 2 ≤ morseCellMass T D side m * morseJoinResistance T D side g ∧
      morseJoinMass T D side g ≤
        ((C 0) ^ 2 * exp (-(n : ℝ))) * morseCellMass T D side m ∧
      exp (2 * (n : ℝ) ^ 2 - 10 * (n : ℝ) ^ (3 / 2 : ℝ) - 4 * n - 51) /
          (C 0) ^ 2 ≤ morseCellMass T D side m * morseJoinResistance T D side g := by
  have hNm : T.index ≤ m := by rcases hm with rfl | rfl <;> omega
  have hNg : T.index ≤ g := by rcases hg with rfl | rfl <;> omega
  have hμ := (r07_realized_mass_pos h hσ hb side hNm).1
  have hc := r07_realized_model_comparisons h hσ hb side hNm hNg
  have hnC := r07_deep_model_products_coarse T σ hσ hn hN hm hg
    (h.d_eq m hNm) (h.d_eq g hNg)
  have hnS := r07_deep_model_products T σ hσ (by omega) hN hm hg
    (h.d_eq m hNm) (h.d_eq g hNg)
  refine ⟨(div_le_div_of_nonneg_right hnC.1 (sq_nonneg _)).trans hc.1, ?_,
    (div_le_div_of_nonneg_right hnS.1 (sq_nonneg _)).trans hc.1⟩
  exact (div_le_iff₀ hμ).mp
    (hc.2.trans (mul_le_mul_of_nonneg_left hnC.2 (sq_nonneg _)))

end ContinuousFlexibility.Radial
