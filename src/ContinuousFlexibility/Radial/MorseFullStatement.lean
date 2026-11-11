import ContinuousFlexibility.Radial.MorseDiscreteSpectrum
import ContinuousFlexibility.Radial.MorseParameterBridges
import ContinuousFlexibility.Radial.MorseQuantitativeResolvent

/-!
# The full Morse model target

The actual spectrum, the quantitative inverse at zero, and the return
angle use the same nonsquare integer parameter.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real

theorem morse_R04_statement : Statements.R04Statement := by
  intro d hd hns
  let A := ((d : ℝ) ^ (-1 / 2 : ℝ) + 2 * (d : ℝ) ^ (-9 / 2 : ℝ)) ^ 2
  let B := (d : ℝ) ^ (-9 : ℝ)
  let δ := (8 * (d : ℝ) ^ 9)⁻¹
  obtain ⟨hAB, hB, htravel, hsin, hthreshold, hlevel⟩ :=
    morseParameter_return_and_level_gaps hd hns
  refine ⟨hAB, hB, ?_, htravel, hsin⟩
  intro j hj
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (zero_lt_one.trans hd)
  have hj₀ : (0 : ℝ) < j := by
    have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hδ : 0 < δ := inv_pos.mpr (mul_pos (by norm_num) (pow_pos hd₀ 9))
  have hspec := morseFullDifferentialSpectrum hj₀ hA B
  refine ⟨hspec, ?_⟩
  have hbound := morseWeakResolventBound_of_subthreshold_gap
    (j := (j : ℝ)) (A := A) (B := B) hj₀ hA hδ (hthreshold j hj) (by
      intro E hE heig
      obtain ⟨m, hm, heq⟩ := (hspec.2.1 E hE).mp heig
      rw [heq]
      exact hlevel j hj m hm)
  simpa only [δ, inv_inv] using hbound

end ContinuousFlexibility.Radial
