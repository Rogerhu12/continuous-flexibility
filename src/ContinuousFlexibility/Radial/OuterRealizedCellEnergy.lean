module

public import ContinuousFlexibility.Radial.OuterMorsePullback
public import ContinuousFlexibility.Radial.OuterMorseCellEnergy

/-!
# Whole-cell energy for actual physical states

The model estimate is applied to the pullback of the actual physical
solution.  Comparing the chosen state scale with the realized cell
amplitude then gives the ordinary two-coordinate square energy.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem state_energy_rescale_transfer {u₀ z₀ u₁ z₁ q M F : ℝ}
    (hM : 1 ≤ M) (hqhi : q ^ 2 ≤ M ^ 2) (hqlo : 1 ≤ M ^ 2 * q ^ 2)
    (hF : 0 ≤ F)
    (h : u₁ ^ 2 + q ^ 2 * z₁ ^ 2 ≤ (u₀ ^ 2 + q ^ 2 * z₀ ^ 2) * F) :
    u₁ ^ 2 + z₁ ^ 2 ≤ (u₀ ^ 2 + z₀ ^ 2) * M ^ 4 * F := by
  have hM2 : 1 ≤ M ^ 2 := by nlinarith only [hM, sq_nonneg (M - 1)]
  have hupper : u₀ ^ 2 + q ^ 2 * z₀ ^ 2 ≤ M ^ 2 * (u₀ ^ 2 + z₀ ^ 2) := by
    have hu := mul_le_mul_of_nonneg_right hM2 (sq_nonneg u₀)
    have hz := mul_le_mul_of_nonneg_right hqhi (sq_nonneg z₀)
    nlinarith only [hu, hz]
  have hlower : u₁ ^ 2 + z₁ ^ 2 ≤ M ^ 2 * (u₁ ^ 2 + q ^ 2 * z₁ ^ 2) := by
    have hu := mul_le_mul_of_nonneg_right hM2 (sq_nonneg u₁)
    have hz := mul_le_mul_of_nonneg_right hqlo (sq_nonneg z₁)
    nlinarith only [hu, hz]
  calc
    _ ≤ M ^ 2 * (u₁ ^ 2 + q ^ 2 * z₁ ^ 2) := hlower
    _ ≤ M ^ 2 * ((u₀ ^ 2 + q ^ 2 * z₀ ^ 2) * F) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg M)
    _ ≤ M ^ 2 * ((M ^ 2 * (u₀ ^ 2 + z₀ ^ 2)) * F) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hupper hF) (sq_nonneg M)
    _ = _ := by ring

theorem morseCellEnergyFactor_nonneg (A B j c : ℝ) :
    0 ≤ morseCellEnergyFactor A B j c :=
  mul_nonneg (mul_nonneg (morsePositiveEnergyFactor_nonneg _ _ _ _ _) (exp_pos _).le)
    (morsePositiveEnergyFactor_nonneg _ _ _ _ _)

/-- One actual retained cell has the model transfer bound, with only the
explicit loss needed to change the constant flux scale. -/
theorem morseRealized_cell_endpoint_energy {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {j scale M : ℝ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hscale : 0 < scale) (hM : 1 ≤ M)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n)
    (hhi : scale / morseChainAmplitude T σ n ≤ M)
    (hlo : morseChainAmplitude T σ n / scale ≤ M)
    (hstate : ∀ r ∈ Icc (T.radius side n (T.leftX side n))
        (T.radius side n (T.rightX side n)),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z (j ^ 2 * deriv D.w r / (scale * r) * u r) r) :
    let l := T.radius side n (T.leftX side n)
    let r := T.radius side n (T.rightX side n)
    let F := M ^ 4 * morseCellEnergyFactor (morseChainA T n) (morseChainB T n) j (1 / 100)
    (u r ^ 2 + z r ^ 2 ≤ (u l ^ 2 + z l ^ 2) * F) ∧
      (u l ^ 2 + z l ^ 2 ≤ (u r ^ 2 + z r ^ 2) * F) := by
  let R := T.radius side n
  let q := scale / morseChainAmplitude T σ n
  let F := morseCellEnergyFactor (morseChainA T n) (morseChainB T n) j (1 / 100)
  have hlam : 0 < morseChainAmplitude T σ n := morseChainAmplitude_pos T σ hσ n
  have hq : 0 < q := div_pos hscale hlam
  have hret := h.retained_data side n hn
  have ht : morseChainRightTurn T n = morseRightTurn (morseChainA T n) (morseChainB T n) := rfl
  have hl : T.leftX side n = morseCellLeftCut := hret.2.2.1
  have hr : T.rightX side n =
      morseRightCapEnd (morseChainA T n) (morseChainB T n) (1 / 100) := by
    simpa only [morseRightCapEnd, morseRightCapLength, ht] using hret.2.2.2.2.2.1
  have hp := morseRealized_state_pullback h hσ hscale side n hn hstate
  rw [hl, hr] at hp
  have he := morse_cell_endpoint_energy (j := j) hret.1 hret.2.1
    (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (fun x hx => (hp x hx).1) (fun x hx => (hp x hx).2)
  rw [← hl, ← hr] at he
  have hweighted :
      (u (R (T.rightX side n)) ^ 2 + q ^ 2 * z (R (T.rightX side n)) ^ 2 ≤
        (u (R (T.leftX side n)) ^ 2 + q ^ 2 * z (R (T.leftX side n)) ^ 2) * F) ∧
      (u (R (T.leftX side n)) ^ 2 + q ^ 2 * z (R (T.leftX side n)) ^ 2 ≤
        (u (R (T.rightX side n)) ^ 2 + q ^ 2 * z (R (T.rightX side n)) ^ 2) * F) := by
    simpa only [mul_pow] using he
  have hqhi : q ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hq.le hhi 2
  have hprod : 1 ≤ M * q := by
    have h := mul_le_mul_of_nonneg_right hlo hq.le
    have heq : (morseChainAmplitude T σ n / scale) * q = 1 := by
      dsimp only [q]
      field_simp [hscale.ne', hlam.ne']
    rw [heq] at h
    exact h
  have hqlo : 1 ≤ M ^ 2 * q ^ 2 := by
    simpa only [one_pow, mul_pow] using pow_le_pow_left₀ zero_le_one hprod 2
  have hF : 0 ≤ F := morseCellEnergyFactor_nonneg _ _ _ _
  constructor
  · simpa only [mul_assoc] using state_energy_rescale_transfer hM hqhi hqlo hF hweighted.1
  · simpa only [mul_assoc] using state_energy_rescale_transfer hM hqhi hqlo hF hweighted.2

end ContinuousFlexibility.Radial
