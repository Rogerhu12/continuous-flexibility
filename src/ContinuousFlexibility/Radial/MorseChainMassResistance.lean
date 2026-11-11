import ContinuousFlexibility.Radial.MorseRealizedIntegralTransfer
import ContinuousFlexibility.Radial.MorseRealizedJoinIntegrals

/-!
# Uniform mass and resistance of every realized Morse chain

One baseline realization controls the fixed radius charts. Their model
integrals therefore have constants independent of the height sequence.
The physical change of variables supplies the amplitude factors, and
the retained long cap supplies the lower bound on join resistance.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

/-- Enlarge the realization constants once for the entire height family.
The argument uses only the frozen realization hypotheses. -/
theorem exists_morseChainMassResistanceConstants
    (T : MorseChainData) (C : ℕ → ℝ) (family : (ℕ → ℝ) → ReferenceData)
    (hfamily : ∀ σ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) → MorseChainRealization T σ (family σ) C) :
    ∃ C' : ℕ → ℝ, ∀ σ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) →
      MorseChainRealization T σ (family σ) C' ∧ MorseMassResistanceBounds T σ (family σ) C' := by
  have h0 := hfamily (fun _ => 1) (fun _ => ⟨le_rfl, by norm_num⟩)
  obtain ⟨K, hcell⟩ := exists_morseRealizedCellEstimates h0
  obtain ⟨L, hL, hconn⟩ := exists_morseRealizedConnectorBounds h0 hcell
  let C' : ℕ → ℝ := fun s => max (C s) (K + L)
  have hCC (s : ℕ) : C s ≤ C' s := le_max_left _ _
  have hsum : K + L ≤ C' 0 := le_max_right _ _
  have hK : K ≤ C' 0 :=
    (le_add_of_nonneg_right (zero_le_one.trans hL)).trans hsum
  refine ⟨C', ?_⟩
  intro σ hσ
  have h := hfamily σ hσ
  refine ⟨h.mono hCC, ?_⟩
  intro side n hn
  have hlam : 0 < morseChainAmplitude T σ n := morseChainAmplitude_pos T σ hσ n
  have hlamI : 0 ≤ (morseChainAmplitude T σ n)⁻¹ := inv_nonneg.mpr hlam.le
  obtain ⟨hB, hAB, _, _, _, _, _⟩ := h.retained_data side n hn
  have hA : 0 < morseChainA T n := (mul_pos (by norm_num) hB).trans hAB
  have hlog : 0 ≤ log (morseChainA T n / morseChainB T n) := by
    apply log_nonneg
    apply (one_le_div hB).mpr
    linarith only [hAB, hB]
  have hpow : morseChainA T n ^ (-4 : ℝ) = (morseChainA T n ^ 4)⁻¹ := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hA.le, Real.rpow_natCast]
  obtain ⟨hMI, hRI, hMC, hRC⟩ := morseRealized_model_integrals h hσ side n hn
  obtain ⟨hJM, hJR, hRN⟩ := morseRealizedJoin_integrals h side n hn
  have hConn := hconn σ (family σ) hσ h side n hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hMI]
    calc
      morseChainAmplitude T σ n * morseChainA T n ^ 2 / C' 0 =
          morseChainAmplitude T σ n * (morseChainA T n ^ 2 / C' 0) := by ring
      _ ≤ morseChainAmplitude T σ n * (morseChainA T n ^ 2 / K) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (sq_nonneg _) hcell.pos hK) hlam.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcell.mass_lower side n hn) hlam.le
  · rw [hMI]
    calc
      _ ≤ morseChainAmplitude T σ n * (K * morseChainA T n ^ 2) :=
        mul_le_mul_of_nonneg_left (hcell.mass_upper side n hn) hlam.le
      _ ≤ morseChainAmplitude T σ n * (C' 0 * morseChainA T n ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK (sq_nonneg _)) hlam.le
      _ = _ := by ring
  · rw [hRI]
    calc
      _ ≤ (morseChainAmplitude T σ n)⁻¹ * (K * log (morseChainA T n / morseChainB T n)) :=
        mul_le_mul_of_nonneg_left (hcell.resistance_upper side n hn) hlamI
      _ ≤ (morseChainAmplitude T σ n)⁻¹ * (C' 0 * log (morseChainA T n / morseChainB T n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK hlog) hlamI
      _ = _ := by rw [div_eq_mul_inv]; ring
  · rw [hJM, hMC]
    calc
      _ ≤ morseChainAmplitude T σ n * (K * morseChainA T n ^ 6) +
          L * morseChainAmplitude T σ n * morseChainA T n ^ 6 :=
        add_le_add (mul_le_mul_of_nonneg_left (hcell.cap_mass_upper side n hn) hlam.le) hConn.1
      _ = (K + L) * morseChainAmplitude T σ n * morseChainA T n ^ 6 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsum hlam.le) (pow_nonneg hA.le 6)
  · rw [hpow, hJR, hRC]
    calc
      (morseChainAmplitude T σ n)⁻¹ * (morseChainA T n ^ 4)⁻¹ / C' 0 =
          (morseChainAmplitude T σ n)⁻¹ * ((morseChainA T n ^ 4)⁻¹ / C' 0) := by ring
      _ ≤ (morseChainAmplitude T σ n)⁻¹ * ((morseChainA T n ^ 4)⁻¹ / K) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (inv_nonneg.mpr (pow_nonneg hA.le 4)) hcell.pos hK) hlamI
      _ ≤ (morseChainAmplitude T σ n)⁻¹ * morseRealizedCapResistanceModel T side n :=
        mul_le_mul_of_nonneg_left (hcell.cap_resistance_lower side n hn) hlamI
      _ ≤ _ := le_add_of_nonneg_right hRN
  · rw [hpow, hJR, hRC]
    calc
      _ ≤ (morseChainAmplitude T σ n)⁻¹ * (K * (morseChainA T n ^ 4)⁻¹) +
          L * (morseChainAmplitude T σ n)⁻¹ * (morseChainA T n ^ 4)⁻¹ :=
        add_le_add (mul_le_mul_of_nonneg_left (hcell.cap_resistance_upper side n hn) hlamI) hConn.2
      _ = (K + L) * (morseChainAmplitude T σ n)⁻¹ * (morseChainA T n ^ 4)⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsum hlamI) (inv_nonneg.mpr (pow_nonneg hA.le 4))

end ContinuousFlexibility.Radial
