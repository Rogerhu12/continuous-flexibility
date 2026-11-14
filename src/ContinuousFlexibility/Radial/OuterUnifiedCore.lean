module

public import ContinuousFlexibility.Radial.OuterInitialCore
public import ContinuousFlexibility.Radial.OuterOutwardTransfer

/-!
# Uniform actual core inputs, including the initial frequency band

One pair of constants works for every frequency band, both ends, every
allowed state scale, and every inward cut in the actual initial middle
interval.  The initial band is handled by its fixed compact interval;
all later bands use the quantitative Morse estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

def morseTransitionCoreLeft (T : MorseChainData) (entry : ℝ) (side : Bool) (n : ℕ) : ℝ :=
  if n = T.index then morseInitialCoreLeft T side entry else morseOuterCoreLeft T side n

def morseTransitionCoreRight (T : MorseChainData) (entry : ℝ) (side : Bool) (n : ℕ) : ℝ :=
  if n = T.index then morseInitialCoreRight T side entry else morseOuterFullCoreRight T side n

def morseTransitionEnergyConstant (T : MorseChainData) (σ : ℕ → ℝ)
    (D : ReferenceData) (C : ℕ → ℝ) (K Cstar L : ℝ) : ℝ :=
  max (outerFullCoreQuadraticExponent C K D.a Cstar L)
    (morseInitialCoreEnergyConstant T σ D Cstar L)

def morseTransitionMassConstant (T : MorseChainData) (σ : ℕ → ℝ)
    (D₀ D : ReferenceData) (C : ℕ → ℝ) (K L : ℝ) : ℝ :=
  max (L + 135 + 2 * outerCoreMassPrefactor D₀ D C K) (morseInitialCoreMassConstant T σ D L)

theorem morseTransitionCore_interval {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {entry : ℝ} (h : MorseChainRealization T σ D C)
    (he : entry ∈ morseInitialMiddle T) (side : Bool) (n : ℕ) (hn : T.index ≤ n) :
    morseTransitionCoreLeft T entry side n < morseTransitionCoreRight T entry side n ∧
      Icc (morseTransitionCoreLeft T entry side n) (morseTransitionCoreRight T entry side n) ⊆ radialCore D := by
  by_cases hi : n = T.index
  · subst n
    have hc := morseInitialCore_geometry h he side
    have hb := morseInitialSupport_geometry h
    simpa only [morseTransitionCoreLeft, morseTransitionCoreRight, if_pos rfl, ite_true] using
      And.intro hc.1 (hc.2.trans hb.2.1)
  · have hn' : T.index < n := by omega
    simpa only [morseTransitionCoreLeft, morseTransitionCoreRight, if_neg hi] using
      morseOuterFullCore_interval h side n hn'

theorem morseTransitionEnergyConstant_nonneg {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) (K Cstar L : ℝ) :
    0 ≤ morseTransitionEnergyConstant T σ D C K Cstar L :=
  (morseInitialCoreEnergyConstant_nonneg h hσ Cstar L).trans (le_max_right _ _)

theorem morseTransitionCore_energy_on_exp
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {K Cstar L scale entry s t : ℝ} {n j : ℕ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale) (hL : 0 ≤ L)
    (he : entry ∈ morseInitialMiddle T) (side : Bool) (hband : radialFrequencyBand T Cstar n j)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2))
    (hstate : ∀ r ∈ Icc (morseTransitionCoreLeft T entry side n) (morseTransitionCoreRight T entry side n),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z ((j : ℝ) ^ 2 * deriv D.w r / (scale * r) * u r) r)
    (hs : s ∈ Icc (morseTransitionCoreLeft T entry side n) (morseTransitionCoreRight T entry side n))
    (ht : t ∈ Icc (morseTransitionCoreLeft T entry side n) (morseTransitionCoreRight T entry side n)) :
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) *
      exp (morseTransitionEnergyConstant T σ D C K Cstar L * (n : ℝ) ^ 2 +
        outerFullCoreActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n))) := by
  have hτ : 0 ≤ outerFullCoreActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n)) := by
    dsimp only [outerFullCoreActionExponent, outerCoreActionExponent, outerOutgoingActionExponent]
    positivity
  by_cases hi : n = T.index
  · subst n
    simp only [morseTransitionCoreLeft, morseTransitionCoreRight, if_pos rfl] at hstate hs ht
    have hh := morseInitialCore_energy_on_exp h hσ hscale side he hband hhi hlo hstate hs ht
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply exp_le_exp.mpr
    have hq := mul_le_mul_of_nonneg_right
      (le_max_right (outerFullCoreQuadraticExponent C K D.a Cstar L)
        (morseInitialCoreEnergyConstant T σ D Cstar L)) (sq_nonneg (T.index : ℝ))
    dsimp only [morseTransitionEnergyConstant]
    linarith only [hq, hτ]
  · have hn : T.index < n := by have hh := hband.1; omega
    simp only [morseTransitionCoreLeft, morseTransitionCoreRight, if_neg hi] at hstate hs ht
    have hh := morseOuterFullCore_energy_on_exp h hσ hcell hscale hL side hn hband hhi hlo hstate hs ht
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply exp_le_exp.mpr
    have hq := mul_le_mul_of_nonneg_right
      (le_max_left (outerFullCoreQuadraticExponent C K D.a Cstar L)
        (morseInitialCoreEnergyConstant T σ D Cstar L)) (sq_nonneg (n : ℝ))
    dsimp only [morseTransitionEnergyConstant]
    linarith only [hq]

theorem morseTransitionCore_mass_le_state_scale
    {T : MorseChainData} {σ : ℕ → ℝ} {D₀ D : ReferenceData} {C : ℕ → ℝ}
    {K Cstar L scale entry : ℝ} {n j : ℕ}
    (h₀ : MorseChainRealization T (fun _ => 1) D₀ C)
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale)
    (he : entry ∈ morseInitialMiddle T) (side : Bool) (hband : radialFrequencyBand T Cstar n j)
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2)) :
    radialHilbertIntervalMass D (morseTransitionCoreLeft T entry side n) (morseTransitionCoreRight T entry side n) ≤
      scale * exp (morseTransitionMassConstant T σ D₀ D C K L * (n : ℝ) ^ 2) := by
  by_cases hi : n = T.index
  · subst n
    simp only [morseTransitionCoreLeft, morseTransitionCoreRight, if_pos rfl]
    have hh := morseInitialCore_mass_le_state_scale h hσ hscale side he hband hlo
    exact hh.trans (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))) hscale.le)
  · have hn : T.index < n := by have hh := hband.1; omega
    simp only [morseTransitionCoreLeft, morseTransitionCoreRight, if_neg hi]
    have hh := morseOuterFullCore_mass_le_state_scale h₀ h hσ hcell side n hn hscale hlo
    exact hh.trans (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))) hscale.le)

def morseTransitionRadialTransfer {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {scale entry : ℝ}
    (h : MorseChainRealization T σ D C) (hscale : 0 < scale)
    (he : entry ∈ morseInitialMiddle T) (side : Bool) (n : ℕ) (hn : T.index ≤ n) (j : ℝ) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  let hi := morseTransitionCore_interval h he side n hn
  let hc := outerPhysical_coefficients_continuous h.geometry hscale hi.2 j
  outerStateTransfer hi.1.le hc.1 hc.2
    (left_mem_Icc.mpr hi.1.le) (right_mem_Icc.mpr hi.1.le)

def morseTransitionCoreTransfer {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {scale entry : ℝ}
    (h : MorseChainRealization T σ D C) (hscale : 0 < scale)
    (he : entry ∈ morseInitialMiddle T) (side : Bool) (n : ℕ) (hn : T.index ≤ n) (j : ℝ) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  outerOutwardTransfer side (morseTransitionRadialTransfer h hscale he side n hn j)

theorem morseTransitionCoreTransfer_actual {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {scale entry j : ℝ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hscale : 0 < scale)
    (he : entry ∈ morseInitialMiddle T) (side : Bool) (n : ℕ) (hn : T.index ≤ n)
    (hstate : ∀ r ∈ Icc (morseTransitionCoreLeft T entry side n) (morseTransitionCoreRight T entry side n),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z (j ^ 2 * deriv D.w r / (scale * r) * u r) r) :
    let l := morseTransitionCoreLeft T entry side n
    let r := morseTransitionCoreRight T entry side n
    morseTransitionCoreTransfer h hscale he side n hn j
        (if side then (u l, z l) else outerFluxReflection (u r, z r)) =
      if side then (u r, z r) else outerFluxReflection (u l, z l) := by
  have hi := morseTransitionCore_interval h he side n hn
  have hc := outerPhysical_coefficients_continuous h.geometry hscale hi.2 j
  apply outerOutwardTransfer_actual side
  exact outerStateTransfer_actual hi.1.le hc.1 hc.2
    (left_mem_Icc.mpr hi.1.le) (right_mem_Icc.mpr hi.1.le) hstate

theorem morseTransitionCoreTransfer_norms_le
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {K Cstar L scale entry : ℝ} {n j : ℕ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hscale : 0 < scale) (hL : 0 ≤ L)
    (he : entry ∈ morseInitialMiddle T) (side : Bool) (hband : radialFrequencyBand T Cstar n j)
    (hhi : scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2)) :
    ‖(morseTransitionCoreTransfer h hscale he side n hband.1 (j : ℝ)).toContinuousLinearMap‖ +
        ‖(morseTransitionCoreTransfer h hscale he side n hband.1 (j : ℝ)).symm.toContinuousLinearMap‖ ≤
      exp ((morseTransitionEnergyConstant T σ D C K Cstar L + 2) * (n : ℝ) ^ 2 +
        outerFullCoreActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n))) := by
  have hi := morseTransitionCore_interval h he side n hband.1
  have hc := outerPhysical_coefficients_continuous h.geometry hscale hi.2 (j : ℝ)
  have hQ := morseTransitionEnergyConstant_nonneg h hσ K Cstar L
  have hτ : 0 ≤ outerFullCoreActionExponent C K D.a * ((j : ℝ) * sqrt (morseChainA T n)) := by
    dsimp only [outerFullCoreActionExponent, outerCoreActionExponent, outerOutgoingActionExponent]
    positivity
  unfold morseTransitionCoreTransfer
  rw [outerOutwardTransfer_norm_sum]
  apply outerStateTransfer_norms_le_exp hi.1.le (radialFrequencyBand_index_pos hband) hc.1 hc.2
    (left_mem_Icc.mpr hi.1.le) (right_mem_Icc.mpr hi.1.le) hQ hτ
  intro u z hstate
  constructor
  · simpa only [outerStateEnergy, mul_comm] using
      morseTransitionCore_energy_on_exp h hσ hcell hscale hL he side hband hhi hlo hstate
        (left_mem_Icc.mpr hi.1.le) (right_mem_Icc.mpr hi.1.le)
  · simpa only [outerStateEnergy, mul_comm] using
      morseTransitionCore_energy_on_exp h hσ hcell hscale hL he side hband hhi hlo hstate
        (right_mem_Icc.mpr hi.1.le) (left_mem_Icc.mpr hi.1.le)

/-- The core assertions of Lemma 6.4, with all quantitative cell
certificates obtained from the actual baseline realization. -/
theorem exists_morseTransitionCore_bounds
    {T : MorseChainData} {σ : ℕ → ℝ} {D₀ D : ReferenceData} {C : ℕ → ℝ}
    (h₀ : MorseChainRealization T (fun _ => 1) D₀ C)
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (Cstar L : ℝ) (hL : 0 ≤ L) :
    ∃ Q Co : ℝ, 0 ≤ Q ∧ 0 ≤ Co ∧
      ∀ entry (he : entry ∈ morseInitialMiddle T) side n j
        (hb : radialFrequencyBand T Cstar n j) scale (hs : 0 < scale),
        scale / morseChainAmplitude T σ n ≤ exp (L * (n : ℝ) ^ 2) →
        morseChainAmplitude T σ n / scale ≤ exp (L * (n : ℝ) ^ 2) →
        (‖(morseTransitionCoreTransfer h hs he side n hb.1 (j : ℝ)).toContinuousLinearMap‖ +
          ‖(morseTransitionCoreTransfer h hs he side n hb.1 (j : ℝ)).symm.toContinuousLinearMap‖ ≤
            exp (Q * (n : ℝ) ^ 2 + Co * ((j : ℝ) * sqrt (morseChainA T n)))) ∧
        radialHilbertIntervalMass D (morseTransitionCoreLeft T entry side n)
          (morseTransitionCoreRight T entry side n) ≤ scale * exp (Q * (n : ℝ) ^ 2) := by
  obtain ⟨K, hcell⟩ := exists_morseRealizedCellEstimates h₀
  let Qe := morseTransitionEnergyConstant T σ D C K Cstar L + 2
  let Qm := morseTransitionMassConstant T σ D₀ D C K L
  let Co := outerFullCoreActionExponent C K D.a
  have hQe : 0 ≤ Qe := by
    have hh := morseTransitionEnergyConstant_nonneg h hσ K Cstar L
    dsimp only [Qe]
    linarith only [hh]
  have hCo : 0 ≤ Co := by
    dsimp only [Co, outerFullCoreActionExponent, outerCoreActionExponent, outerOutgoingActionExponent]
    positivity
  refine ⟨max Qe Qm, Co, hQe.trans (le_max_left _ _), hCo, ?_⟩
  intro entry he side n j hb scale hs hhi hlo
  constructor
  · calc
      _ ≤ exp (Qe * (n : ℝ) ^ 2 + Co * ((j : ℝ) * sqrt (morseChainA T n))) :=
        morseTransitionCoreTransfer_norms_le h hσ hcell hs hL he side hb hhi hlo
      _ ≤ exp (max Qe Qm * (n : ℝ) ^ 2 + Co * ((j : ℝ) * sqrt (morseChainA T n))) := by
        apply exp_le_exp.mpr
        have hq := mul_le_mul_of_nonneg_right (le_max_left Qe Qm) (sq_nonneg (n : ℝ))
        linarith only [hq]
  · exact (morseTransitionCore_mass_le_state_scale h₀ h hσ hcell hs he side hb hlo).trans
      (mul_le_mul_of_nonneg_left (exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_right Qe Qm) (sq_nonneg (n : ℝ)))) hs.le)

end ContinuousFlexibility.Radial
