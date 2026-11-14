module

public import ContinuousFlexibility.Radial.OuterPhysicalInverseGauge
public import ContinuousFlexibility.Radial.OuterNaturalPhysicalAllIndices

/-!
# The constructed natural basis has the full physical quantitative norm

The norm belongs to the same outward Hilbert space and the same actual
natural solution used in the Green basis. The bound applies to every
positive transition index, with a constant uniform in all height choices.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

namespace MorsePhysicalTailBasis

variable {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
  {entrance η K : ℝ}

theorem P_memLp_outward (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hD : RadialProfileGeometry D) (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K)) :
    MemLp F.P 2
      (outerOutwardTailMeasure D (morsePhysicalDeepTail M D right j start entrance η K) right) :=
  morsePhysicalDeepTail_outward_lift_memLp hD hentry hT F.P_natural

/-- The exact squared-norm identity for the same constructed outward P. -/
theorem P_square_integral (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hD : RadialProfileGeometry D) (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K)) :
    (∫ t, F.P t ^ 2 ∂outerOutwardTailMeasure D
      (morsePhysicalDeepTail M D right j start entrance η K) right) =
      12 * (∫ x, F.logP x ^ 2
        ∂deepTailMeasure (morsePhysicalDeepTail M D right j start entrance η K)) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  have hrad := morsePhysicalDeepTail_integral_lift_sq hD hT F.logP
  dsimp only at hrad
  rw [morsePhysicalDeepTail_interval_measure_eq hD hentry hT] at hrad
  unfold outerOutwardTailMeasure
  change (∫ t, F.P t ^ 2 ∂Measure.map (outerOutwardRadius right)
      ((radialHilbertMeasure D).restrict
        (radialTailInterval D right (tailPhysicalRadius right (tailPhysicalLog right entrance))))) = _
  rw [tailPhysicalRadius_log right hentry]
  calc
    _ = ∫ r in radialTailInterval D right entrance,
        F.P (outerOutwardRadius right r) ^ 2 ∂radialHilbertMeasure D :=
      (measurableEmbedding_outerOutwardRadius right).integral_map _
    _ = ∫ r in radialTailInterval D right entrance,
        tailPhysicalLift D right j F.logP r ^ 2 ∂radialHilbertMeasure D := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun r => by
        change outerTailOutwardLift D right j F.logP (outerOutwardRadius right r) ^ 2 =
          tailPhysicalLift D right j F.logP r ^ 2
        rw [outerTailOutwardLift_reflect])
    _ = _ := hrad

theorem P_norm_le (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hD : RadialProfileGeometry D) (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {scale exponent : ℝ} (hscale : 0 ≤ scale) (n : ℕ)
    (hbound : 12 * (∫ x, F.logP x ^ 2
      ∂deepTailMeasure (morsePhysicalDeepTail M D right j start entrance η K)) ≤
        scale * exp (exponent * (n : ℝ) ^ 2)) :
    ‖(F.P_memLp_outward hD hentry hT).toLp F.P‖ ≤
      sqrt scale * exp ((exponent / 2) * (n : ℝ) ^ 2) := by
  apply outerNatural_toLp_norm_le _ hscale n
  rw [F.P_square_integral hD hentry hT]
  exact hbound

end MorsePhysicalTailBasis

/-- A single constant controls the actual P in the constructed physical
basis at every positive transition index and for every allowed height
choice. The identical basis supplies Qflux=1 and natural-line uniqueness. -/
theorem exists_morsePhysicalTailBasis_all_indices_norm_of_upper
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
            η ≤ 1 / 16 → 32 ≤ K →
            DeepTailHypotheses (morsePhysicalDeepTail M D right j (n + 1) entrance η K) →
            ∃ F : MorsePhysicalTailBasis M D right j (n + 1) entrance η K,
              ∃ hP : MemLp F.P 2 (outerOutwardTailMeasure D
                (morsePhysicalDeepTail M D right j (n + 1) entrance η K) right),
                ‖hP.toLp F.P‖ ≤
                  sqrt (morseChainAmplitude M σ n) * exp (Cbound * (n : ℝ) ^ 2) := by
  obtain ⟨Cbase, hCbase, hmass⟩ :=
    morsePhysicalDeepTail_first_mass_all_indices_uniform_of_upper h₀ hcell hCstar
  refine ⟨(Cbase + 396) / 2, by linarith only [hCbase], ?_⟩
  intro σ D C hσ h n hn hnidx j hj right entrance η K hentry hη hK hT
  have hstart : M.index ≤ n + 1 := hnidx.trans (Nat.le_succ n)
  obtain ⟨_, _, _, hlt, htr, _, _⟩ := h.retained_data right (n + 1) hstart
  have hepos : 0 < entrance :=
    (h.radius_positive right (n + 1) hstart _
      (left_mem_Icc.mpr (hlt.trans htr).le)).trans_le hentry
  obtain ⟨F⟩ := exists_morsePhysicalTailBasis h.geometry right j (n + 1) hepos hT hη hK
  refine ⟨F, F.P_memLp_outward h.geometry hepos hT, ?_⟩
  apply F.P_norm_le h.geometry hepos hT (morseChainAmplitude_pos M σ hσ n).le n
    (exponent := Cbase + 396)
  have hfirst := hmass σ D C hσ h n hn hnidx j hj right entrance η K hentry
  have hpref : (396 : ℝ) ≤ exp (396 * (n : ℝ) ^ 2) :=
    nonneg_le_exp_mul_nat_sq (by norm_num) hn
  calc
    _ ≤ 396 * (tailMass (morsePhysicalDeepTail M D right j (n + 1) entrance η K) 0 /
        ((entrance / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2)) ^ 2) := F.P_bound
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

/-- The original band interface is retained without imposing a lower
frequency threshold on the underlying mass or natural norm estimate. -/
theorem exists_morsePhysicalTailBasis_all_indices_norm
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
            ∃ F : MorsePhysicalTailBasis M D right j (n + 1) entrance η K,
              ∃ hP : MemLp F.P 2 (outerOutwardTailMeasure D
                (morsePhysicalDeepTail M D right j (n + 1) entrance η K) right),
                ‖hP.toLp F.P‖ ≤
                  sqrt (morseChainAmplitude M σ n) * exp (Cbound * (n : ℝ) ^ 2) := by
  obtain ⟨Cbound, hCbound, hbound⟩ :=
    exists_morsePhysicalTailBasis_all_indices_norm_of_upper h₀ hcell hCstar
  refine ⟨Cbound, hCbound, ?_⟩
  intro σ D C hσ h n hn j hj right entrance η K hentry hη hK hT
  exact hbound σ D C hσ h n hn hj.1 j hj.2.2 right entrance η K hentry hη hK hT

end ContinuousFlexibility.Radial

