import ContinuousFlexibility.Radial.InnerBufferFullInverse
import ContinuousFlexibility.Radial.InnerMorseCapScale

/-!
# Actual Morse cut models for positive-buffer compression

The cuts lie halfway through the retained short and long positive caps.
The inner walls are the short-cap endpoint and the quarter-point of the
long cap. The two masses are exactly those of the physical cap estimate.
Only elementary mass-times-length conditions are needed to fit the
buffer layers; in particular the long-cap mass need not be at least one.

The full-line inverse is supplied by the actual nonsquare Morse spectral
theorem, and the uniform layer constant is four.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

def innerMorseBufferLeftCut : ℝ :=
  (morseCellLeftCut + morseShortLeftCapCut) / 2

def innerMorseBufferRightCut (A B : ℝ) : ℝ :=
  morseRightTurn A B + morseRightCapLength A (1 / 100) / 2

def innerMorseBufferMass (A B j : ℝ) (i : Fin 2) : ℝ :=
  innerMorseCapMass A B j (decide (i ≠ 0))

def innerMorseBufferDistance (A : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then morseShortLeftCapLength / 2 else morseRightCapLength A (1 / 100) / 4

def innerMorseBufferData (A B j B₀ : ℝ) : BufferData where
  bordered := false
  potential := morsePotential j A B
  border := 0
  l := innerMorseBufferLeftCut
  h := innerMorseBufferRightCut A B
  mass := innerMorseBufferMass A B j
  action := fun i => innerMorseBufferMass A B j i * innerMorseBufferDistance A i - 6
  B₀ := B₀
  layerBound := 4
  borderFunction := 0

theorem innerMorseBufferMass_pos {A B j : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hj : 0 < j) (i : Fin 2) : 0 < innerMorseBufferMass A B j i := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  unfold innerMorseBufferMass innerMorseCapMass
  split_ifs <;> positivity

theorem innerMorseBufferMass_zero (A B j : ℝ) :
    innerMorseBufferMass A B j 0 = j * sqrt (A / 4) := by
  simp only [innerMorseBufferMass, ne_eq, not_true_eq_false, decide_false,
    innerMorseCapMass, Bool.false_eq_true, ite_false]

theorem innerMorseBufferMass_one (A B j : ℝ) :
    innerMorseBufferMass A B j 1 = j * sqrt (B / 2) := by
  norm_num [innerMorseBufferMass, innerMorseCapMass]

theorem innerMorseBufferInnerWall_eq {A B j : ℝ} (B₀ : ℝ)
    (i : Fin 2) (hm : innerMorseBufferMass A B j i ≠ 0) :
    bufferInnerWall (innerMorseBufferData A B j B₀) i =
      bufferCut (innerMorseBufferData A B j B₀) i -
        bufferSign i * innerMorseBufferDistance A i := by
  unfold bufferInnerWall
  have ha : (innerMorseBufferData A B j B₀).action i =
      innerMorseBufferMass A B j i * innerMorseBufferDistance A i - 6 := rfl
  rw [ha, sub_add_cancel]
  rw [show (innerMorseBufferData A B j B₀).mass i =
    innerMorseBufferMass A B j i from rfl, mul_div_assoc, mul_div_cancel_left₀ _ hm]

theorem innerMorseBufferInnerWall_zero {A B j : ℝ} (B₀ : ℝ)
    (hm : innerMorseBufferMass A B j 0 ≠ 0) :
    bufferInnerWall (innerMorseBufferData A B j B₀) 0 = morseShortLeftCapCut := by
  rw [innerMorseBufferInnerWall_eq B₀ 0 hm]
  simp only [bufferCut, bufferSign, innerMorseBufferData, innerMorseBufferDistance,
    ite_true, innerMorseBufferLeftCut, morseShortLeftCapLength]
  ring

theorem innerMorseBufferInnerWall_one {A B j : ℝ} (B₀ : ℝ)
    (hm : innerMorseBufferMass A B j 1 ≠ 0) :
    bufferInnerWall (innerMorseBufferData A B j B₀) 1 =
      morseRightTurn A B + morseRightCapLength A (1 / 100) / 4 := by
  rw [innerMorseBufferInnerWall_eq B₀ 1 hm]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [bufferCut, bufferSign, innerMorseBufferData, innerMorseBufferDistance,
    h10, ite_false, innerMorseBufferRightCut]
  ring

theorem innerMorseBuffer_left_layer {A B j x : ℝ}
    (hm : 0 < innerMorseBufferMass A B j 0)
    (hfit : 16 ≤ innerMorseBufferMass A B j 0 * morseShortLeftCapLength)
    (hx : |x - innerMorseBufferLeftCut| ≤ 4 / innerMorseBufferMass A B j 0 ∨
      |x - morseShortLeftCapCut| ≤ 4 / innerMorseBufferMass A B j 0) :
    morseCellLeftCut ≤ x := by
  have hstep : 4 / innerMorseBufferMass A B j 0 ≤ morseShortLeftCapLength / 4 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith only [hfit]
  have hlen := morseShortLeftCapLength_pos
  rcases hx with hx | hx
  · have hl := (abs_le.mp hx).1
    dsimp only [innerMorseBufferLeftCut, morseShortLeftCapLength] at hl hstep hlen
    linarith only [hl, hstep, hlen]
  · have hl := (abs_le.mp hx).1
    dsimp only [morseShortLeftCapLength] at hstep hlen
    linarith only [hl, hstep, hlen]

theorem innerMorseBuffer_right_layer {A B j x : ℝ}
    (hm : 0 < innerMorseBufferMass A B j 1)
    (hL : 0 < morseRightCapLength A (1 / 100))
    (hfit : 32 ≤ innerMorseBufferMass A B j 1 * morseRightCapLength A (1 / 100))
    (hx : |x - innerMorseBufferRightCut A B| ≤ 4 / innerMorseBufferMass A B j 1 ∨
      |x - (morseRightTurn A B + morseRightCapLength A (1 / 100) / 4)| ≤
        4 / innerMorseBufferMass A B j 1) :
    morseRightTurn A B ≤ x := by
  have hstep : 4 / innerMorseBufferMass A B j 1 ≤
      morseRightCapLength A (1 / 100) / 8 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith only [hfit]
  rcases hx with hx | hx
  · have hl := (abs_le.mp hx).1
    dsimp only [innerMorseBufferRightCut] at hl
    linarith only [hl, hstep, hL]
  · have hl := (abs_le.mp hx).1
    linarith only [hl, hstep, hL]

/-- These raw cap inequalities give every analytic compression hypothesis.
No compressed inverse, flux error, or weighted Poisson bound is an input. -/
theorem innerMorseBufferData_hypotheses {A B j B₀ : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hj : 0 < j) (hB₀ : 0 < B₀)
    (hreal : ActualClosedFormRealization (morsePotential j A B))
    (hres : WeakResolventBound (morsePotential j A B) 0 B₀)
    (hleft : 16 ≤ innerMorseBufferMass A B j 0 * morseShortLeftCapLength)
    (hright : 32 ≤ innerMorseBufferMass A B j 1 * morseRightCapLength A (1 / 100))
    (hlong : 4 * log 4 ≤ morseRightCapLength A (1 / 100)) :
    BufferHypotheses (innerMorseBufferData A B j B₀) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL := morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)
  have hm (i : Fin 2) := innerMorseBufferMass_pos hB hAB hj i
  have hw0 := innerMorseBufferInnerWall_zero B₀ (hm 0).ne'
  have hw1 := innerMorseBufferInnerWall_one B₀ (hm 1).ne'
  have hshort := morseCellLeftCut_lt_shortLeftCapCut
  have hturn := (morseShortLeftCapCut_lt_leftTurn hB hAB).trans (morseTurn_order hB hAB)
  have hcuts : innerMorseBufferLeftCut < innerMorseBufferRightCut A B := by
    dsimp only [innerMorseBufferLeftCut, innerMorseBufferRightCut]
    linarith only [hshort, hturn, hL]
  have hwalls : bufferInnerWall (innerMorseBufferData A B j B₀) 0 <
      bufferInnerWall (innerMorseBufferData A B j B₀) 1 := by
    rw [hw0, hw1]
    linarith only [hturn, hL]
  refine ⟨hcuts, hwalls, hB₀, by norm_num [innerMorseBufferData], ?_, hreal,
    contDiff_const, HasCompactSupport.zero, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.mul (contDiff_morseRho A B)
  · simpa only [innerMorseBufferData, Pi.zero_apply] using (Lp.coeFn_zero ℝ 2 volume)
  · simp only [innerMorseBufferData, Function.support_zero, empty_subset]
  · intro i
    refine ⟨hm i, ?_⟩
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · simp only [innerMorseBufferData, innerMorseBufferDistance, ite_true]
      nlinarith only [hleft]
    · have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp only [innerMorseBufferData, innerMorseBufferDistance, h10, ite_false]
      nlinarith only [hright]
  · filter_upwards [ae_restrict_of_ae (Lp.coeFn_zero ℝ 2 volume)] with x hx
    simpa only [innerMorseBufferData, Pi.zero_apply] using hx
  · intro i x hx
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · have hx' : x ≤ morseShortLeftCapCut := by
        have he : (innerMorseBufferData A B j B₀).l +
            ((innerMorseBufferData A B j B₀).action 0 + 6) /
              (innerMorseBufferData A B j B₀).mass 0 = morseShortLeftCapCut := by
          simpa only [bufferInnerWall, bufferCut, bufferSign,
            ite_true, neg_one_mul, neg_div, sub_neg_eq_add] using hw0
        exact (show x ≤ (innerMorseBufferData A B j B₀).l +
          ((innerMorseBufferData A B j B₀).action 0 + 6) /
            (innerMorseBufferData A B j B₀).mass 0 from hx).trans_eq he
      have hρ := mul_le_mul_of_nonneg_left
        (morseShortLeftCap_negRho_lower hB hAB hx') (sq_nonneg j)
      rw [show (innerMorseBufferData A B j B₀).mass 0 = innerMorseBufferMass A B j 0
        from rfl, innerMorseBufferMass_zero, mul_pow, sq_sqrt (by positivity : 0 ≤ A / 4)]
      simpa only [innerMorseBufferData, morsePotential, neg_mul, mul_neg] using hρ
    · have h10 : (1 : Fin 2) ≠ 0 := by decide
      have hx' : morseRightTurn A B + morseRightCapLength A (1 / 100) / 4 ≤ x := by
        have he : (innerMorseBufferData A B j B₀).h -
            ((innerMorseBufferData A B j B₀).action 1 + 6) /
              (innerMorseBufferData A B j B₀).mass 1 =
            morseRightTurn A B + morseRightCapLength A (1 / 100) / 4 := by
          simpa only [bufferInnerWall, bufferCut, bufferSign,
            h10, ite_false, one_mul] using hw1
        exact he.symm.trans_le (show (innerMorseBufferData A B j B₀).h -
          ((innerMorseBufferData A B j B₀).action 1 + 6) /
            (innerMorseBufferData A B j B₀).mass 1 ≤ x from hx)
      have hlower : morseRightTurn A B + log 4 ≤ x := by
        linarith only [hx', hlong]
      have hρ := mul_le_mul_of_nonneg_left
        (morseRho_right_cap_lower hB hAB hlower) (sq_nonneg j)
      rw [show (innerMorseBufferData A B j B₀).mass 1 = innerMorseBufferMass A B j 1
        from rfl, innerMorseBufferMass_one, mul_pow, sq_sqrt (by positivity : 0 ≤ B / 2)]
      simpa only [innerMorseBufferData, morsePotential, neg_mul, mul_neg] using hρ
  · intro i x hx
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · have hx' : |x - innerMorseBufferLeftCut| ≤ 4 / innerMorseBufferMass A B j 0 ∨
          |x - morseShortLeftCapCut| ≤ 4 / innerMorseBufferMass A B j 0 := by
        rw [hw0] at hx
        simpa only [bufferCut, innerMorseBufferData, ite_true] using hx
      have hρ := mul_le_mul_of_nonneg_left
        (morseLeftCap_negRho_upper hB hAB (innerMorseBuffer_left_layer (hm 0) hleft hx'))
        (sq_nonneg j)
      have hmass : innerMorseBufferMass A B j 0 ^ 2 = j ^ 2 * (A / 4) := by
        rw [innerMorseBufferMass_zero, mul_pow, sq_sqrt (by positivity : 0 ≤ A / 4)]
      calc
        (innerMorseBufferData A B j B₀).potential x = j ^ 2 * (-morseRho A B x) := by
          simp only [innerMorseBufferData, morsePotential]
          ring
        _ ≤ j ^ 2 * A := hρ
        _ = (innerMorseBufferData A B j B₀).layerBound *
            (innerMorseBufferData A B j B₀).mass 0 ^ 2 := by
          rw [show (innerMorseBufferData A B j B₀).mass 0 =
            innerMorseBufferMass A B j 0 from rfl, hmass]
          norm_num only [innerMorseBufferData]
          ring
    · have h10 : (1 : Fin 2) ≠ 0 := by decide
      have hx' : |x - innerMorseBufferRightCut A B| ≤ 4 / innerMorseBufferMass A B j 1 ∨
          |x - (morseRightTurn A B + morseRightCapLength A (1 / 100) / 4)| ≤
            4 / innerMorseBufferMass A B j 1 := by
        rw [hw1] at hx
        simpa only [bufferCut, innerMorseBufferData, h10, ite_false] using hx
      have hρ := mul_le_mul_of_nonneg_left
        (morseRho_right_cap_bounds hB hAB
          (innerMorseBuffer_right_layer (hm 1) hL hright hx')).2 (sq_nonneg j)
      have hmass : innerMorseBufferMass A B j 1 ^ 2 = j ^ 2 * (B / 2) := by
        rw [innerMorseBufferMass_one, mul_pow, sq_sqrt (by positivity : 0 ≤ B / 2)]
      calc
        (innerMorseBufferData A B j B₀).potential x = j ^ 2 * (-morseRho A B x) := by
          simp only [innerMorseBufferData, morsePotential]
          ring
        _ ≤ j ^ 2 * B := hρ
        _ ≤ (innerMorseBufferData A B j B₀).layerBound *
            (innerMorseBufferData A B j B₀).mass 1 ^ 2 := by
          rw [show (innerMorseBufferData A B j B₀).mass 1 =
            innerMorseBufferMass A B j 1 from rfl, hmass]
          norm_num only [innerMorseBufferData]
          nlinarith only [mul_nonneg (sq_nonneg j) hB.le]
  · exact exists_innerUnborderedFullInverse hres

/-- Every actual nonsquare Morse model gives a genuine compression datum
as soon as its retained cap lengths fit the raw positive buffer layers. -/
theorem innerMorseBufferData_hypotheses_of_integer (d j : ℕ) (hd : 1 < d)
    (hns : ¬ ∃ k : ℕ, k ^ 2 = d) (hj : 2 ≤ j)
    (hleft : let A := ((d : ℝ) ^ (-1 / 2 : ℝ) + 2 * (d : ℝ) ^ (-9 / 2 : ℝ)) ^ 2
      let B := (d : ℝ) ^ (-9 : ℝ)
      16 ≤ innerMorseBufferMass A B j 0 * morseShortLeftCapLength)
    (hright : let A := ((d : ℝ) ^ (-1 / 2 : ℝ) + 2 * (d : ℝ) ^ (-9 / 2 : ℝ)) ^ 2
      let B := (d : ℝ) ^ (-9 : ℝ)
      32 ≤ innerMorseBufferMass A B j 1 * morseRightCapLength A (1 / 100))
    (hlong : let A := ((d : ℝ) ^ (-1 / 2 : ℝ) + 2 * (d : ℝ) ^ (-9 / 2 : ℝ)) ^ 2
      4 * log 4 ≤ morseRightCapLength A (1 / 100)) :
    let A := ((d : ℝ) ^ (-1 / 2 : ℝ) + 2 * (d : ℝ) ^ (-9 / 2 : ℝ)) ^ 2
    let B := (d : ℝ) ^ (-9 : ℝ)
    BufferHypotheses (innerMorseBufferData A B j (8 * (d : ℝ) ^ 9)) := by
  have hmodel := morse_R04_statement d hd hns
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hj' : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  exact innerMorseBufferData_hypotheses hmodel.2.1 hmodel.1 hj' (by positivity)
    (hmodel.2.2.1 j hj).1.1 (hmodel.2.2.1 j hj).2 hleft hright hlong

end ContinuousFlexibility.Radial
