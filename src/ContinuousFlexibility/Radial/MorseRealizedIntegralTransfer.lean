import ContinuousFlexibility.Radial.MorseRealizedCellBounds

/-!
# Physical integrals of the realized model charts

The model integrals depend only on the fixed chain data. The actual
physical profile contributes exactly its height amplitude to mass and
the reciprocal amplitude to resistance.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem morseRealized_subinterval_integrals {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) {c d : ℝ}
    (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc (T.leftX side n) (T.rightX side n)) :
    (∫ z in T.radius side n c..T.radius side n d, D.w z * z ^ 6) =
        morseChainAmplitude T σ n *
          (∫ x in c..d, (deriv (T.radius side n) x) ^ 2 * (T.radius side n x) ^ 6) ∧
      (∫ z in T.radius side n c..T.radius side n d, (D.w z * z ^ 8)⁻¹) =
        (morseChainAmplitude T σ n)⁻¹ *
          (∫ x in c..d, ((T.radius side n x) ^ 8)⁻¹) := by
  obtain ⟨_, _, _, hab, hbe, _, _⟩ := h.retained_data side n hn
  have hw (x : ℝ) (hx : x ∈ Icc (T.leftX side n) (T.rightX side n)) :
      D.w (1 * T.radius side n x) = morseChainAmplitude T σ n * 1 *
        deriv (T.radius side n) x := by
    simpa only [one_mul, mul_one] using h.profile_eq side n hn x hx
  simpa only [one_mul, one_pow, mul_one] using
    morseCell_physical_mass_resistance_change (hab.trans hbe).le hcd hsub
      (morseChainAmplitude_pos T σ hσ n) (by norm_num : (0 : ℝ) < 1)
      (h.radius_smooth side n hn) (h.radius_positive side n hn)
      (h.derivative_positive side n hn) hw

theorem morseRealized_model_integrals {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) :
    morseCellMass T D side n = morseChainAmplitude T σ n * morseRealizedMassModel T side n ∧
      morseCellResistance T D side n =
        (morseChainAmplitude T σ n)⁻¹ * morseRealizedResistanceModel T side n ∧
      (∫ z in morseChainMassEnd T side n..T.radius side n (T.rightX side n), D.w z * z ^ 6) =
        morseChainAmplitude T σ n * morseRealizedCapMassModel T side n ∧
      (∫ z in morseChainMassEnd T side n..T.radius side n (T.rightX side n),
        (D.w z * z ^ 8)⁻¹) =
        (morseChainAmplitude T σ n)⁻¹ * morseRealizedCapResistanceModel T side n := by
  obtain ⟨_, _, _, hab, hbe, _, _⟩ := h.retained_data side n hn
  have hI : Icc (T.leftX side n) (morseChainRightTurn T n) ⊆
      Icc (T.leftX side n) (T.rightX side n) := fun _ hx => ⟨hx.1, hx.2.trans hbe.le⟩
  have hCap : Icc (morseChainRightTurn T n) (T.rightX side n) ⊆
      Icc (T.leftX side n) (T.rightX side n) := fun _ hx => ⟨hab.le.trans hx.1, hx.2⟩
  have hi := morseRealized_subinterval_integrals h hσ side n hn hab.le hI
  have hc := morseRealized_subinterval_integrals h hσ side n hn hbe.le hCap
  exact ⟨hi.1, hi.2, hc.1, hc.2⟩

end ContinuousFlexibility.Radial
