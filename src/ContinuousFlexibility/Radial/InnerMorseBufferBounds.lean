import ContinuousFlexibility.Radial.InnerMorseBufferData
import ContinuousFlexibility.Radial.MorseTransitionBands

/-!
# Uniform raw Morse buffer bounds before tail selection

The left and right mass-times-length products are bounded below by
fixed positive multiples of tau=j sqrt(A). A single fixed threshold
therefore fits both buffer layers and leaves a positive linear fraction
of tau in both actions. On an actual realized chain every earlier cell
of a frequency band meets this threshold after Cstar is chosen large
enough. This construction does not enlarge a previously selected tail.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real ContinuousFlexibility.Statements

def innerMorseLeftFitScale : ℝ := morseShortLeftCapLength / 2

def innerMorseRightFitScale : ℝ := (1 / 100 : ℝ) / sqrt (2 * (9 : ℝ) ^ 9)

def innerMorseBufferThreshold : ℝ :=
  max (32 / innerMorseLeftFitScale) (64 / innerMorseRightFitScale)

def innerMorseBufferActionScale : ℝ :=
  min (innerMorseLeftFitScale / 4) (innerMorseRightFitScale / 8)

theorem innerMorseLeftFitScale_pos : 0 < innerMorseLeftFitScale :=
  div_pos morseShortLeftCapLength_pos (by norm_num)

theorem innerMorseRightFitScale_pos : 0 < innerMorseRightFitScale := by
  unfold innerMorseRightFitScale
  positivity

theorem innerMorseBufferThreshold_pos : 0 < innerMorseBufferThreshold :=
  (div_pos (by norm_num) innerMorseLeftFitScale_pos).trans_le (le_max_left _ _)

theorem innerMorseBufferActionScale_pos : 0 < innerMorseBufferActionScale :=
  lt_min (div_pos innerMorseLeftFitScale_pos (by norm_num))
    (div_pos innerMorseRightFitScale_pos (by norm_num))

theorem innerMorseBuffer_left_product {A B j : ℝ} (hA : 0 ≤ A) :
    innerMorseBufferMass A B j 0 * morseShortLeftCapLength =
      innerMorseLeftFitScale * (j * sqrt A) := by
  rw [innerMorseBufferMass_zero, sqrt_div hA]
  have h4 : sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h4]
  unfold innerMorseLeftFitScale
  ring

theorem innerMorseBuffer_right_product {A B j : ℝ}
    (hA : 0 < A) (hj : 0 ≤ j) (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) :
    innerMorseRightFitScale * (j * sqrt A) ≤
      innerMorseBufferMass A B j 1 * morseRightCapLength A (1 / 100) := by
  let L := morseRightCapLength A (1 / 100)
  let k := sqrt (2 * (9 : ℝ) ^ 9)
  have hL : 0 ≤ L := (morseRightCapLength_pos hA (by norm_num)).le
  have hLA : L * A ^ 4 = (1 / 100 : ℝ) := by
    exact div_mul_cancel₀ _ (pow_ne_zero 4 hA.ne')
  have hS : sqrt (A ^ 9) = A ^ 4 * sqrt A := by
    rw [show A ^ 9 = (A ^ 4) ^ 2 * A by ring, sqrt_mul (sq_nonneg _),
      sqrt_sq (pow_nonneg hA.le 4)]
  have harg : A ^ 9 / (2 * (9 : ℝ) ^ 9) ≤ B / 2 := by
    have h := div_le_div_of_nonneg_right hBAlo (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1 <;> ring
  have hlo : A ^ 4 * sqrt A / k ≤ sqrt (B / 2) := by
    have h := sqrt_le_sqrt harg
    rw [sqrt_div (pow_nonneg hA.le 9), hS] at h
    exact h
  calc
    innerMorseRightFitScale * (j * sqrt A) =
        j * L * (A ^ 4 * sqrt A / k) := by
      dsimp only [innerMorseRightFitScale]
      rw [← hLA]
      ring
    _ ≤ j * L * sqrt (B / 2) :=
      mul_le_mul_of_nonneg_left hlo (mul_nonneg hj hL)
    _ = innerMorseBufferMass A B j 1 * morseRightCapLength A (1 / 100) := by
      rw [innerMorseBufferMass_one]
      ring

/-- The fixed retained long cap is long enough for the global Morse
barrier independently of j. -/
theorem innerMorseBuffer_long_fit {A : ℝ} (hA : 0 < A) (hsmall : A ≤ 1 / 10) :
    4 * log 4 ≤ morseRightCapLength A (1 / 100) := by
  have hpow : A ^ 4 ≤ (1 / 10 : ℝ) ^ 4 := pow_le_pow_left₀ hA.le hsmall 4
  have h100 : (100 : ℝ) ≤ morseRightCapLength A (1 / 100) := by
    unfold morseRightCapLength
    apply (le_div_iff₀ (pow_pos hA 4)).mpr
    calc
      100 * A ^ 4 ≤ 100 * (1 / 10 : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = _ := by norm_num
  have hlog : log (4 : ℝ) ≤ 3 := by
    simpa only [show (4 : ℝ) - 1 = 3 by norm_num] using
      log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  exact (show 4 * log (4 : ℝ) ≤ 100 by linarith only [hlog]).trans h100

/-- Large tau fits both actual masses, including a potentially tiny
right mass, because its retained cap has the matching long length. -/
theorem innerMorseBuffer_fits_and_action {A B j : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hj : 0 < j)
    (hsmall : A ≤ 1 / 10) (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B)
    (htau : innerMorseBufferThreshold ≤ j * sqrt A) (B₀ : ℝ) :
    16 ≤ innerMorseBufferMass A B j 0 * morseShortLeftCapLength ∧
      32 ≤ innerMorseBufferMass A B j 1 * morseRightCapLength A (1 / 100) ∧
      4 * log 4 ≤ morseRightCapLength A (1 / 100) ∧
      ∀ i, innerMorseBufferActionScale * (j * sqrt A) ≤
        (innerMorseBufferData A B j B₀).action i := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have ht : 0 ≤ j * sqrt A := mul_nonneg hj.le (sqrt_nonneg _)
  have hl : 32 ≤ innerMorseLeftFitScale * (j * sqrt A) := by
    have h := (div_le_iff₀ innerMorseLeftFitScale_pos).mp
      ((le_max_left _ _).trans htau)
    simpa only [mul_comm] using h
  have hr : 64 ≤ innerMorseRightFitScale * (j * sqrt A) := by
    have h := (div_le_iff₀ innerMorseRightFitScale_pos).mp
      ((le_max_right _ _).trans htau)
    simpa only [mul_comm] using h
  have hleft := innerMorseBuffer_left_product (B := B) (j := j) hA.le
  have hright := innerMorseBuffer_right_product (B := B) hA hj.le hBAlo
  refine ⟨?_, ?_, innerMorseBuffer_long_fit hA hsmall, ?_⟩
  · rw [hleft]
    exact (by norm_num : (16 : ℝ) ≤ 32).trans hl
  · exact (by norm_num : (32 : ℝ) ≤ 64).trans (hr.trans hright)
  · intro i
    fin_cases i
    · have hc := mul_le_mul_of_nonneg_right
        (min_le_left (innerMorseLeftFitScale / 4) (innerMorseRightFitScale / 8)) ht
      have hprod : innerMorseBufferMass A B j 0 * (morseShortLeftCapLength / 2) =
          innerMorseLeftFitScale * (j * sqrt A) / 2 := by
        rw [← hleft]
        ring
      simp only [innerMorseBufferData, innerMorseBufferDistance, ite_true]
      rw [hprod]
      exact hc.trans (by nlinarith only [hl])
    · have h10 : (1 : Fin 2) ≠ 0 := by decide
      have hc := mul_le_mul_of_nonneg_right
        (min_le_right (innerMorseLeftFitScale / 4) (innerMorseRightFitScale / 8)) ht
      have hprod : innerMorseRightFitScale * (j * sqrt A) / 4 ≤
          innerMorseBufferMass A B j 1 * (morseRightCapLength A (1 / 100) / 4) := by
        have h := div_le_div_of_nonneg_right hright (by norm_num : (0 : ℝ) ≤ 4)
        simpa only [mul_div_assoc] using h
      simp only [innerMorseBufferData, innerMorseBufferDistance, h10, ite_false]
      exact hc.trans (by nlinarith only [hr, hprod])

/-- The raw smallness of A is uniform for every realized chain beginning
after the fixed numerical index ten. -/
theorem innerMorseChain_parameter_small {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {m : ℕ} (hindex : 10 ≤ T.index) (hm : T.index ≤ m) :
    morseChainA T m ≤ 1 / 10 := by
  have hm10 : (10 : ℝ) ≤ m := by exact_mod_cast hindex.trans hm
  apply morseChainA_le_of_sq_ge_log T m (h.d_eq m hm) (by norm_num : (0 : ℝ) < 1 / 10)
  have hlog : log (90 : ℝ) ≤ 89 := by
    simpa only [show (90 : ℝ) - 1 = 89 by norm_num] using
      log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 90)
  norm_num only
  nlinarith only [hlog, hm10, sq_nonneg ((m : ℝ) - 10)]

/-- Before any tail selection, every earlier actual Morse cell in every
band yields its complete BufferHypotheses and a fixed linear action
bound. Cstar is chosen first and the realized starting index afterwards. -/
theorem innerMorseChain_buffer {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {Cstar : ℝ} (hscale : innerMorseBufferThreshold ≤ Cstar) (hindex : 10 ≤ T.index)
    {m n j : ℕ} (hm : T.index ≤ m) (hmn : m < n) (hj : 2 ≤ j)
    (hband : radialFrequencyBand T Cstar n j) :
    BufferHypotheses
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j (8 * (T.d m : ℝ) ^ 9)) ∧
      ∀ i, innerMorseBufferActionScale * ((j : ℝ) * sqrt (morseChainA T m)) ≤
        (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
          (8 * (T.d m : ℝ) ^ 9)).action i := by
  have hCstar : 0 < Cstar := innerMorseBufferThreshold_pos.trans_le hscale
  have hj' : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hm10 : (10 : ℝ) ≤ m := by exact_mod_cast hindex.trans hm
  have hq : 1 ≤ radialQ m := by
    apply (show (1 : ℝ) ≤ (m : ℝ) ^ 2 by
      nlinarith only [hm10, sq_nonneg ((m : ℝ) - 10)]).trans
    exact radial_nat_sq_le_Q m
  have hCq : Cstar ≤ Cstar * radialQ m := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq hCstar.le
  have htau : innerMorseBufferThreshold ≤ (j : ℝ) * sqrt (morseChainA T m) :=
    hscale.trans (hCq.trans
        (morseTransition_earlier_cap_action T hCstar (fun k hk => h.d_eq k hk) hband hm hmn))
  have hd2 : 2 ≤ T.d m := by
    rw [h.d_eq m hm]
    exact morseChainInteger_ge_two m
  have hd1 : (1 : ℝ) ≤ T.d m := by exact_mod_cast (show 1 ≤ T.d m by omega)
  have hparams := morseChainParameters_pos T m (by exact_mod_cast hd2)
  obtain ⟨hleft, hright, hlong, haction⟩ := innerMorseBuffer_fits_and_action
    hparams.2 hparams.1 hj' (innerMorseChain_parameter_small h hindex hm)
    (morseChainB_A_bounds T m hd1).1 htau (8 * (T.d m : ℝ) ^ 9)
  exact ⟨innerMorseBufferData_hypotheses_of_integer (T.d m) j (by omega)
    (h.1 m hm).2.1 hj hleft hright hlong, haction⟩

end ContinuousFlexibility.Radial
