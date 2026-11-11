import ContinuousFlexibility.Radial.OuterNaturalMassAllIndices
import ContinuousFlexibility.Radial.OuterNaturalPhysicalL2

/-!
# The actual physical natural norm in every frequency band

All constants are chosen uniformly before the allowed height sequence.
The conclusion uses the actual radial Hilbert measure on the entire
selected tail, includes its initial resistance edge, and applies to
every positive transition index.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The normalized first mass of the actual tail has the required height
scale for all positive indices, uniformly in the height ratios. -/
theorem morsePhysicalDeepTail_first_mass_all_indices_uniform_of_upper
    {M : MorseChainData} {σ₀ : ℕ → ℝ} {D₀ : ReferenceData} {C₀ : ℕ → ℝ}
    {B Cstar : ℝ} (h₀ : MorseChainRealization M σ₀ D₀ C₀)
    (hcell : MorseRealizedCellEstimates M B) (hCstar : 0 < Cstar) :
    ∃ Cbound : ℝ, 0 < Cbound ∧
      ∀ (σ : ℕ → ℝ) (D : ReferenceData) (C : ℕ → ℝ),
        (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) → MorseChainRealization M σ D C →
        ∀ n : ℕ, 1 ≤ n → M.index ≤ n →
          ∀ j : ℕ, (j : ℝ) < radialFrequencyThreshold M Cstar n →
          ∀ right : Bool, ∀ entrance η K : ℝ,
            M.radius right (n + 1) (M.leftX right (n + 1)) ≤ entrance →
            tailMass (morsePhysicalDeepTail M D right j (n + 1) entrance η K) 0 /
                ((entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)) ^ 2 ≤
              morseChainAmplitude M σ n * exp (Cbound * (n : ℝ) ^ 2) := by
  obtain ⟨Cbound, hCbound, hbound⟩ :=
    morseRealized_next_normalized_mass_all_indices_uniform_of_upper h₀ hcell hCstar
  refine ⟨Cbound, hCbound, ?_⟩
  intro σ D C hσ h n hn hnidx j hj right entrance η K hentry
  have hstart : M.index ≤ n + 1 := hnidx.trans (Nat.le_succ n)
  obtain ⟨_, _, _, hlt, htr, _, _⟩ := h.retained_data right (n + 1) hstart
  have hepos : 0 < entrance :=
    (h.radius_positive right (n + 1) hstart _
      (left_mem_Icc.mpr (hlt.trans htr).le)).trans_le hentry
  rw [morsePhysicalDeepTail_normalized_first_mass h right j (n + 1) hstart hepos η K]
  exact hbound σ D C hσ h n hn hnidx j hj right entrance hentry

/-- The frequency-band form of the upper-only physical mass estimate. -/
theorem morsePhysicalDeepTail_first_mass_all_indices_uniform
    {M : MorseChainData} {σ₀ : ℕ → ℝ} {D₀ : ReferenceData} {C₀ : ℕ → ℝ}
    {B Cstar : ℝ} (h₀ : MorseChainRealization M σ₀ D₀ C₀)
    (hcell : MorseRealizedCellEstimates M B) (hCstar : 0 < Cstar) :
    ∃ Cbound : ℝ, 0 < Cbound ∧
      ∀ (σ : ℕ → ℝ) (D : ReferenceData) (C : ℕ → ℝ),
        (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) → MorseChainRealization M σ D C →
        ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, radialFrequencyBand M Cstar n j →
          ∀ right : Bool, ∀ entrance η K : ℝ,
            M.radius right (n + 1) (M.leftX right (n + 1)) ≤ entrance →
            tailMass (morsePhysicalDeepTail M D right j (n + 1) entrance η K) 0 /
                ((entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)) ^ 2 ≤
              morseChainAmplitude M σ n * exp (Cbound * (n : ℝ) ^ 2) := by
  obtain ⟨Cbound, hCbound, hbound⟩ :=
    morsePhysicalDeepTail_first_mass_all_indices_uniform_of_upper h₀ hcell hCstar
  refine ⟨Cbound, hCbound, ?_⟩
  intro σ D C hσ h n hn j hj right entrance η K hentry
  exact hbound σ D C hσ h n hn hj.1 j hj.2.2 right entrance η K hentry

/-- The physical natural solution required by Lemma 6.4 exists at every
positive transition index and has the actual full-tail Hilbert norm.
The equation and the unit entrance value are conclusions of the
construction. The deep-tail hypotheses are the previously required
small-parameter hypotheses, not an assumed norm estimate. -/
theorem exists_morsePhysicalNatural_L2_all_indices_uniform
    {M : MorseChainData} {σ₀ : ℕ → ℝ} {D₀ : ReferenceData} {C₀ : ℕ → ℝ}
    {B Cstar : ℝ} (h₀ : MorseChainRealization M σ₀ D₀ C₀)
    (hcell : MorseRealizedCellEstimates M B) (hCstar : 0 < Cstar) :
    ∃ Cbound : ℝ, 0 < Cbound ∧
      ∀ (σ : ℕ → ℝ) (D : ReferenceData) (C : ℕ → ℝ),
        (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) → MorseChainRealization M σ D C →
        ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, radialFrequencyBand M Cstar n j →
          ∀ right : Bool, ∀ entrance η K : ℝ,
            M.radius right (n + 1) (M.leftX right (n + 1)) ≤ entrance →
            η ≤ 1 / 16 → 32 ≤ K →
            DeepTailHypotheses (morsePhysicalDeepTail M D right j (n + 1) entrance η K) →
            let T := morsePhysicalDeepTail M D right j (n + 1) entrance η K
            ∃ u : ℝ → ℝ, TailNaturalEquation T u ∧
              tailPhysicalLift D right j u entrance = 1 ∧
              (∀ x ∈ Ioo T.entrance T.endpoint,
                radialJacobi ((j : ℝ) ^ 2) D.w (tailPhysicalLift D right j u)
                  (tailPhysicalRadius right x) = 0) ∧
              ∃ huL2 : MemLp (tailPhysicalLift D right j u) 2
                ((radialHilbertMeasure D).restrict (radialTailInterval D right entrance)),
                ‖huL2.toLp (tailPhysicalLift D right j u)‖ ≤
                  sqrt (morseChainAmplitude M σ n) * exp (Cbound * (n : ℝ) ^ 2) := by
  obtain ⟨Cbase, hCbase, hmass⟩ :=
    morsePhysicalDeepTail_first_mass_all_indices_uniform h₀ hcell hCstar
  refine ⟨(Cbase + 396) / 2, by linarith only [hCbase], ?_⟩
  intro σ D C hσ h n hn j hj right entrance η K hentry hη hK hT
  have hstart : M.index ≤ n + 1 := hj.1.trans (Nat.le_succ n)
  obtain ⟨_, _, _, hlt, htr, _, _⟩ := h.retained_data right (n + 1) hstart
  have hepos : 0 < entrance :=
    (h.radius_positive right (n + 1) hstart _
      (left_mem_Icc.mpr (hlt.trans htr).le)).trans_le hentry
  obtain ⟨u, hu, hue, hODE, hnorm⟩ :=
    exists_morsePhysicalDeepTail_natural_norm_bound h.geometry
      right j (n + 1) hepos hT hη hK
  refine ⟨u, hu, hue, hODE, morsePhysicalDeepTail_lift_memLp_radial h.geometry hepos hT hu, ?_⟩
  apply morsePhysicalDeepTail_lift_radial_norm_le h.geometry hepos hT hu
    (morseChainAmplitude_pos M σ hσ n).le n (exponent := Cbase + 396)
  have hfirst := hmass σ D C hσ h n hn j hj right entrance η K hentry
  have hpref : (396 : ℝ) ≤ exp (396 * (n : ℝ) ^ 2) :=
    nonneg_le_exp_mul_nat_sq (by norm_num) hn
  calc
    _ ≤ 396 * (tailMass (morsePhysicalDeepTail M D right j (n + 1) entrance η K) 0 /
        ((entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)) ^ 2) := hnorm
    _ ≤ 396 * (morseChainAmplitude M σ n * exp (Cbase * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hfirst (by norm_num)
    _ ≤ exp (396 * (n : ℝ) ^ 2) *
        (morseChainAmplitude M σ n * exp (Cbase * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right hpref
        (mul_nonneg (morseChainAmplitude_pos M σ hσ n).le (exp_pos _).le)
    _ = morseChainAmplitude M σ n * exp ((Cbase + 396) * (n : ℝ) ^ 2) := by
      rw [mul_left_comm, ← exp_add]
      congr 2
      ring

end ContinuousFlexibility.Radial
