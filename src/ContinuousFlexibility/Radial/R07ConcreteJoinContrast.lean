import ContinuousFlexibility.Radial.R07ChainIncoming
import ContinuousFlexibility.Radial.R07JoinContrast
import ContinuousFlexibility.Radial.MorseRealizedConnectorBounds

/-!
# The contrast bound on the actual preceding connector

The normalized cell endpoint bounds and the prescribed fractional join
width bound the adjacent radius dilation ratio. The logarithmic height
contrast is therefore uniform in the geometric placement. Monotonicity
on the physical connector then bounds every intermediate height by its
two endpoint heights, for either direction of traversal.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

private theorem r07_model_endpoint_bounds {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (k : ℕ) :
    let A := morseChainA T (T.index + k)
    let B := morseChainB T (T.index + k)
    let r := G.normal k
    let e := morseRightCapEnd A B (1 / 100)
    (1 / 2 ≤ r morseCellLeftCut ∧ r morseCellLeftCut ≤ 2) ∧
      (1 / 2 ≤ r e ∧ r e ≤ 2) ∧
      (A / 4 ≤ deriv r morseCellLeftCut ∧ deriv r morseCellLeftCut ≤ 7 * A) ∧
      ((1 / 100 : ℝ) * A ^ 5 ≤ deriv r e ∧ deriv r e ≤ (3 / 100 : ℝ) * A ^ 5) := by
  have hd : (2 : ℝ) ≤ T.d (T.index + k) := by
    rw [G.d_exact]
    exact_mod_cast morseChainInteger_ge_two (T.index + k)
  have hAB := morseChainParameters_pos T (T.index + k) hd
  have hA := (mul_pos (by norm_num : (0 : ℝ) < 4) hAB.2).trans hAB.1
  have he : morseRightTurn (morseChainA T (T.index + k)) (morseChainB T (T.index + k)) ≤
      morseRightCapEnd (morseChainA T (T.index + k)) (morseChainB T (T.index + k)) (1 / 100) :=
    le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le
  have hc : (0 : ℝ) ≤ morseJoinCollarWidth := by norm_num [morseJoinCollarWidth]
  have hL := (G.model k).left_collar morseCellLeftCut ⟨sub_le_self _ hc, le_rfl⟩
  have hR := (G.model k).right_collar
    (morseRightCapEnd (morseChainA T (T.index + k)) (morseChainB T (T.index + k)) (1 / 100))
    ⟨le_rfl, le_add_of_nonneg_right hc⟩
  have hvL := (G.model k).left_half morseCellLeftCut
    ⟨le_rfl, (morseCellLeftCut_lt_rightTurn hAB.2 hAB.1).le⟩
  have hvR := (G.model k).right_half _ ⟨he, le_rfl⟩
  exact ⟨⟨hL.1, hL.2.1⟩, ⟨hR.1, hR.2.1⟩,
    ⟨(G.model k).left_speed, hvL.2.2.2.2⟩, hvR.2.2.2⟩

private theorem r07_geometry_A_le_one {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (k : ℕ) : morseChainA T (T.index + k) ≤ 1 := by
  apply morseChainA_le_of_sq_ge_log T (T.index + k) (G.d_exact _) (by norm_num)
  have hn : (100 : ℝ) ≤ (T.index + k : ℕ) := by
    exact_mod_cast G.start_large.trans (Nat.le_add_right T.index k)
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hn 2
  have hl := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
  rw [div_one]
  linarith only [hs, hl]

/-- The actual endpoint logarithmic contrast, in increasing physical
radius. The departure is the current or next cell according to the side. -/
theorem r07_geometry_join_log_contrast {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {σ K : ℕ → ℝ} {D : ReferenceData}
    (hreal : MorseChainRealization T σ D K) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (right : Bool) (k : ℕ) :
    let d := if right then T.index + k else T.index + k + 1
    |log (D.w (T.joinRight right (T.index + k)) / D.w (T.joinLeft right (T.index + k))) -
      4 * (d : ℝ) ^ 2| ≤ 10 * (d : ℝ) ^ (3 / 2 : ℝ) + 2 * (d : ℝ) + 63 := by
  let l := if right then k else k + 1
  let r := if right then k + 1 else k
  let n := T.index + l
  let m := T.index + r
  let e := morseRightCapEnd (morseChainA T n) (morseChainB T n) (1 / 100)
  let frac := morseChainJoinFraction (fun i => morseChainA T (T.index + i)) (1 / 100) k
  have hl : T.joinLeft right (T.index + k) = G.factor right l * G.normal l e := by
    cases right
    · simpa only [l, n, e, if_false, Bool.false_eq_true, G.radius_eq, G.rightX_eq] using
        (G.joins k).2.2.1
    · simpa only [l, n, e, if_true, G.radius_eq, G.rightX_eq] using (G.joins k).1
  have hr : T.joinRight right (T.index + k) =
      G.factor right r * G.normal r morseCellLeftCut := by
    cases right
    · simpa only [r, if_false, Bool.false_eq_true, G.radius_eq, G.leftX_eq] using
        (G.joins k).2.2.2
    · simpa only [r, if_true, G.radius_eq, G.leftX_eq] using (G.joins k).2.1
  have hfrac : 0 ≤ frac ∧ frac ≤ 1 := by
    have hmin : 0 ≤ min (morseChainA T (T.index + k)) (morseChainA T (T.index + (k + 1))) :=
      le_min (sq_nonneg _) (sq_nonneg _)
    have hmin₁ : min (morseChainA T (T.index + k)) (morseChainA T (T.index + (k + 1))) ≤ 1 :=
      (min_le_left _ _).trans (r07_geometry_A_le_one G k)
    refine ⟨by dsimp only [frac, morseChainJoinFraction]; positivity, ?_⟩
    calc
      frac ≤ (1 / 100 : ℝ) * 1 ^ 12 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hmin hmin₁ 12) (by norm_num)
      _ ≤ 1 := by norm_num
  have hmatch : G.factor right r * G.normal r morseCellLeftCut =
      G.factor right l * G.normal l e * (1 + frac) := by
    have hw := G.join_width right k
    rw [hl, hr] at hw
    change G.factor right r * G.normal r morseCellLeftCut -
      G.factor right l * G.normal l e = G.factor right l * G.normal l e * frac at hw
    linarith only [hw]
  have hlp := G.factorLo_pos.trans_le (G.factor_bounds right l).1
  have hrp := G.factorLo_pos.trans_le (G.factor_bounds right r).1
  have hL := r07_model_endpoint_bounds G l
  have hR := r07_model_endpoint_bounds G r
  have hscale : |log (G.factor right r / G.factor right l)| ≤ 3 :=
    morseJoin_scaleRatio_log_bound hlp hrp hL.2.1 hR.1 hfrac hmatch
  have hn : T.index ≤ n := Nat.le_add_right _ _
  have hm : T.index ≤ m := Nat.le_add_right _ _
  have hn₁ : 1 ≤ n := by have := G.start_large; omega
  have hadj : m = n + 1 ∨ n = m + 1 := by
    cases right <;> dsimp only [m, n, l, r, if_true, if_false, Bool.false_eq_true] <;> omega
  have hcontrast := morseJoin_height_log_contrast T σ hσ hn₁ hn hm hadj
    (G.d_exact n) (G.d_exact m) hlp hrp hscale hL.2.2.2 hR.2.2.1
  have hWL : D.w (T.joinLeft right (T.index + k)) =
      morseChainAmplitude T σ n * G.factor right l * deriv (G.normal l) e := by
    rw [hl]
    have hx : e ∈ Icc morseCellLeftCut e := by
      have hab := (hreal.2.2.1 right n hn).2.1.le
      rw [G.leftX_eq right l, G.rightX_eq right l] at hab
      exact ⟨hab, le_rfl⟩
    simpa only [mul_assoc] using r07_realized_normalized_cell_profile G hreal right l e hx
  have hWR : D.w (T.joinRight right (T.index + k)) =
      morseChainAmplitude T σ m * G.factor right r * deriv (G.normal r) morseCellLeftCut := by
    rw [hr]
    have hx : morseCellLeftCut ∈ Icc morseCellLeftCut
        (morseRightCapEnd (morseChainA T m) (morseChainB T m) (1 / 100)) := by
      have hab := (hreal.2.2.1 right m hm).2.1.le
      rw [G.leftX_eq right r, G.rightX_eq right r] at hab
      exact ⟨le_rfl, hab⟩
    simpa only [mul_assoc] using r07_realized_normalized_cell_profile G hreal right r _ hx
  rw [hWL, hWR]
  have he := hcontrast.2.2.1
  cases right <;> simpa only [n, l, if_true, if_false, Bool.false_eq_true, Nat.add_assoc] using he

/-- Uniform contrast and intermediate-height bounds in the actual
outward join coordinates. -/
theorem r07_actual_join_contrast {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {σ K : ℕ → ℝ} {D : ReferenceData}
    (hreal : MorseChainRealization T σ D K) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (right : Bool) (k : ℕ) :
    let p := r07PreviousCellJoin T right (T.index + k)
    let e := r07CellEntry T right (T.index + k + 1)
    let contrast := max (D.w e / D.w p) (D.w p / D.w e)
    1 ≤ contrast ∧ contrast ≤ exp (6 * ((T.index + k + 1 : ℕ) : ℝ) ^ 2) ∧
      ∀ x ∈ uIcc p e, 0 < D.w x ∧ D.w x ≤ contrast * D.w p ∧ D.w p ≤ contrast * D.w x := by
  let m := T.index + k
  let a := T.joinLeft right m
  let b := T.joinRight right m
  have hm : T.index ≤ m := Nat.le_add_right _ _
  have hj := hreal.join_data right m hm
  obtain ⟨hn, hn', _, haEq, hbEq, _⟩ := morseRealizedJoin_endpoints hreal right m hm
  have horder (i : ℕ) (hi : T.index ≤ i) := (hreal.2.2.1 right i hi).2.1.le
  have haCore : a ∈ radialCore D := by
    rw [haEq]
    exact hreal.radius_mem_core right _ hn _ (right_mem_Icc.mpr (horder _ hn))
  have hbCore : b ∈ radialCore D := by
    rw [hbEq]
    exact hreal.radius_mem_core right _ hn' _ (left_mem_Icc.mpr (horder _ hn'))
  have hwp : ∀ x ∈ Icc a b, 0 < D.w x := fun x hx =>
    hreal.geometry.2.2.2.2.1 x ⟨haCore.1.trans_le hx.1, hx.2.trans_lt hbCore.2⟩
  have hWa := hwp a ⟨le_rfl, hj.1.le⟩
  have hWb := hwp b ⟨hj.1.le, le_rfl⟩
  have hmono := morseConnector_monotone_of_logSlope hreal.geometry.2.2.1.1
    (hreal.geometry.1.trans haCore.1) hwp hj.2.2.2.2
  have herror := r07_geometry_join_log_contrast G hreal hσ right k
  have hC := r07_height_contrast_le_of_error (n := T.index + k + 1) hWa hWb
    (by cases right <;> simp only [if_true, if_false, Bool.false_eq_true] <;>
      have h := G.start_large <;> omega)
    (by cases right <;> simp only [if_true, if_false, Bool.false_eq_true] <;> omega) herror
  have hbetween (x : ℝ) (hx : x ∈ Icc a b) : D.w a ≤ D.w x ∧ D.w x ≤ D.w b :=
    ⟨hmono ⟨le_rfl, hj.1.le⟩ hx hx.1, hmono hx ⟨hj.1.le, le_rfl⟩ hx.2⟩
  have hheightOrder : D.w a ≤ D.w b := hmono ⟨le_rfl, hj.1.le⟩ ⟨hj.1.le, le_rfl⟩ hj.1.le
  have hpa : r07PreviousCellJoin T right m = if right then a else b := by
    cases right <;> simp only [r07PreviousCellJoin, if_true, if_false, Bool.false_eq_true]
    · exact hj.2.2.1.symm
    · exact hj.2.1.symm
  have hea : r07CellEntry T right (m + 1) = if right then b else a := by
    cases right <;> simp only [r07CellEntry, if_true, if_false, Bool.false_eq_true]
    · exact hj.2.1.symm
    · exact hj.2.2.1.symm
  dsimp only
  rw [hpa, hea]
  cases right
  · simp only [Bool.false_eq_true, if_false, max_comm (D.w a / D.w b)]
    refine ⟨hC.1, hC.2, ?_⟩
    intro x hx
    rw [uIcc_of_ge hj.1.le] at hx
    simpa only [max_comm (D.w a / D.w b)] using r07_height_between_bounds hWb hWa (by
      rw [min_eq_right hheightOrder, max_eq_left hheightOrder]
      exact hbetween x hx)
  · simp only [if_true]
    refine ⟨hC.1, hC.2, ?_⟩
    intro x hx
    rw [uIcc_of_le hj.1.le] at hx
    exact r07_height_between_bounds hWa hWb (by
      rw [min_eq_left hheightOrder, max_eq_right hheightOrder]
      exact hbetween x hx)

end ContinuousFlexibility.Radial
