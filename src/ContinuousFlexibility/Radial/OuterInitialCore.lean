module

public import ContinuousFlexibility.Radial.OuterCompactCore

/-!
# The initial transition core

The initial cell has no preceding indexed connector.  Its inward cut
may be any point of the actual middle interval between the two first
retained cells.  Both initial cores lie in one fixed regular compact
interval, ending at the actual right natural-tail mass entrance.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

def morseInitialSupportLeft (T : MorseChainData) : ℝ :=
  T.radius false T.index (T.leftX false T.index)

def morseInitialSupportRight (T : MorseChainData) : ℝ := T.joinRight true T.index

def morseInitialMiddle (T : MorseChainData) : Set ℝ :=
  Icc (T.radius false T.index (T.rightX false T.index))
    (T.radius true T.index (T.leftX true T.index))

def morseInitialCoreLeft (T : MorseChainData) (side : Bool) (entry : ℝ) : ℝ :=
  if side then entry else morseInitialSupportLeft T

def morseInitialCoreRight (T : MorseChainData) (side : Bool) (entry : ℝ) : ℝ :=
  if side then morseInitialSupportRight T else entry

theorem morseInitialSupport_geometry {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C) :
    morseInitialSupportLeft T < morseInitialSupportRight T ∧
      Icc (morseInitialSupportLeft T) (morseInitialSupportRight T) ⊆ radialCore D ∧
      morseInitialMiddle T ⊆ Ioo (morseInitialSupportLeft T) (morseInitialSupportRight T) := by
  have hf := morseRealized_retained_endpoints h false T.index le_rfl
  have ht := morseRealized_retained_endpoints h true T.index le_rfl
  have hn := morseRealized_retained_endpoints h true (T.index + 1) (by omega)
  have hj := h.join_data true T.index le_rfl
  have hgap : T.radius false T.index (T.rightX false T.index) <
      T.radius true T.index (T.leftX true T.index) := h.2.2.2.2.2.1
  have hright : T.radius true T.index (T.rightX true T.index) < T.joinRight true T.index := by
    simpa only [hj.2.1, ite_true] using hj.1
  have hrmem : T.joinRight true T.index ∈ radialCore D := by
    rw [hj.2.2.1]
    exact hn.1
  have horder : morseInitialSupportLeft T < morseInitialSupportRight T :=
    hf.2.2.trans (hgap.trans (ht.2.2.trans hright))
  exact ⟨horder,
    fun x hx => ⟨hf.1.1.trans_le hx.1, hx.2.trans_lt hrmem.2⟩,
    fun x hx => ⟨hf.2.2.trans_le hx.1, hx.2.trans_lt (ht.2.2.trans hright)⟩⟩

theorem morseInitialMiddle_nonempty {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C) :
    (morseInitialMiddle T).Nonempty :=
  ⟨T.radius false T.index (T.rightX false T.index), le_rfl, h.2.2.2.2.2.1.le⟩

theorem morseInitialCore_geometry {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {entry : ℝ}
    (h : MorseChainRealization T σ D C) (hentry : entry ∈ morseInitialMiddle T) (side : Bool) :
    morseInitialCoreLeft T side entry < morseInitialCoreRight T side entry ∧
      Icc (morseInitialCoreLeft T side entry) (morseInitialCoreRight T side entry) ⊆
        Icc (morseInitialSupportLeft T) (morseInitialSupportRight T) := by
  have he := (morseInitialSupport_geometry h).2.2 hentry
  cases side with
  | false => exact ⟨he.1, Icc_subset_Icc_right he.2.le⟩
  | true => exact ⟨he.2, Icc_subset_Icc_left he.1.le⟩

def morseInitialCoreEnergyConstant (T : MorseChainData) (σ : ℕ → ℝ)
    (D : ReferenceData) (Cstar L : ℝ) : ℝ :=
  outerCompactCost D (morseInitialSupportLeft T) (morseInitialSupportRight T)
    (exp (outerFrequencyExponent Cstar * (T.index : ℝ) ^ 2))
    (morseChainAmplitude T σ T.index * exp (L * (T.index : ℝ) ^ 2))
    (exp (L * (T.index : ℝ) ^ 2) / morseChainAmplitude T σ T.index)

def morseInitialCoreMassConstant (T : MorseChainData) (σ : ℕ → ℝ)
    (D : ReferenceData) (L : ℝ) : ℝ :=
  radialHilbertIntervalMass D (morseInitialSupportLeft T) (morseInitialSupportRight T) *
    exp (L * (T.index : ℝ) ^ 2) / morseChainAmplitude T σ T.index

theorem morseInitialCoreEnergyConstant_nonneg {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) (Cstar L : ℝ) :
    0 ≤ morseInitialCoreEnergyConstant T σ D Cstar L := by
  have hi := morseInitialSupport_geometry h
  have hlam := morseChainAmplitude_pos T σ hσ T.index
  exact outerCompactCost_nonneg h.geometry hi.1.le hi.2.1 (exp_pos _).le
    (mul_pos hlam (exp_pos _)).le (div_pos (exp_pos _) hlam).le

theorem morseInitialCore_energy_on_exp
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {Cstar L scale entry s t : ℝ} {j : ℕ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hscale : 0 < scale) (side : Bool) (hentry : entry ∈ morseInitialMiddle T)
    (hband : radialFrequencyBand T Cstar T.index j)
    (hhi : scale / morseChainAmplitude T σ T.index ≤ exp (L * (T.index : ℝ) ^ 2))
    (hlo : morseChainAmplitude T σ T.index / scale ≤ exp (L * (T.index : ℝ) ^ 2))
    (hstate : ∀ r ∈ Icc (morseInitialCoreLeft T side entry) (morseInitialCoreRight T side entry),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z ((j : ℝ) ^ 2 * deriv D.w r / (scale * r) * u r) r)
    (hs : s ∈ Icc (morseInitialCoreLeft T side entry) (morseInitialCoreRight T side entry))
    (ht : t ∈ Icc (morseInitialCoreLeft T side entry) (morseInitialCoreRight T side entry)) :
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) *
      exp (morseInitialCoreEnergyConstant T σ D Cstar L * (T.index : ℝ) ^ 2) := by
  have hbig := morseInitialSupport_geometry h
  have hsmall := morseInitialCore_geometry h hentry side
  have hn : 1 ≤ T.index := radialFrequencyBand_index_pos hband
  have hlam : 0 < morseChainAmplitude T σ T.index := morseChainAmplitude_pos T σ hσ T.index
  have hS : scale ≤ morseChainAmplitude T σ T.index * exp (L * (T.index : ℝ) ^ 2) :=
    ((div_le_iff₀ hlam).mp hhi).trans_eq (mul_comm _ _)
  have hR : 1 / scale ≤ exp (L * (T.index : ℝ) ^ 2) / morseChainAmplitude T σ T.index := by
    calc
      _ = (morseChainAmplitude T σ T.index / scale) / morseChainAmplitude T σ T.index := by
        field_simp [hscale.ne', hlam.ne']
      _ ≤ _ := div_le_div_of_nonneg_right hlo hlam.le
  have hj := outer_frequency_sq_le_exp hn (h.d_eq T.index le_rfl) hband
  have he := outer_compact_state_energy h.geometry hbig.1.le hbig.2.1 hsmall.1.le hsmall.2
    hscale hj hS hR hstate hs ht
  have hQ := morseInitialCoreEnergyConstant_nonneg h hσ Cstar L
  have hn' : (1 : ℝ) ≤ T.index := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (T.index : ℝ) ^ 2 := by nlinarith only [hn', sq_nonneg ((T.index : ℝ) - 1)]
  exact he.trans (mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (le_mul_of_one_le_right hQ hn2)) (by positivity))

theorem morseInitialCore_mass_le_state_scale
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {Cstar L scale entry : ℝ} {j : ℕ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hscale : 0 < scale) (side : Bool) (hentry : entry ∈ morseInitialMiddle T)
    (hband : radialFrequencyBand T Cstar T.index j)
    (hlo : morseChainAmplitude T σ T.index / scale ≤ exp (L * (T.index : ℝ) ^ 2)) :
    radialHilbertIntervalMass D (morseInitialCoreLeft T side entry) (morseInitialCoreRight T side entry) ≤
      scale * exp (morseInitialCoreMassConstant T σ D L * (T.index : ℝ) ^ 2) := by
  let M := radialHilbertIntervalMass D (morseInitialSupportLeft T) (morseInitialSupportRight T)
  have hbig := morseInitialSupport_geometry h
  have hsmall := morseInitialCore_geometry h hentry side
  have hn := radialFrequencyBand_index_pos hband
  have hlam : 0 < morseChainAmplitude T σ T.index := morseChainAmplitude_pos T σ hσ T.index
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg hbig.1.le (fun x hx =>
    div_nonneg (mul_nonneg (by norm_num) (h.geometry.2.2.2.2.1 x (hbig.2.1 hx)).le) (sq_nonneg x))
  have hbound : radialHilbertIntervalMass D (morseInitialCoreLeft T side entry) (morseInitialCoreRight T side entry) ≤ M :=
    radialHilbertIntervalMass_mono h.geometry hbig.1.le hbig.2.1
      (hsmall.2 (left_mem_Icc.mpr hsmall.1.le)) (hsmall.2 (right_mem_Icc.mpr hsmall.1.le))
  have hR : 1 / scale ≤ exp (L * (T.index : ℝ) ^ 2) / morseChainAmplitude T σ T.index := by
    calc
      _ = (morseChainAmplitude T σ T.index / scale) / morseChainAmplitude T σ T.index := by
        field_simp [hscale.ne', hlam.ne']
      _ ≤ _ := div_le_div_of_nonneg_right hlo hlam.le
  have hratio : M / scale ≤ morseInitialCoreMassConstant T σ D L := by
    calc
      _ = M * (1 / scale) := by ring
      _ ≤ M * (exp (L * (T.index : ℝ) ^ 2) / morseChainAmplitude T σ T.index) :=
        mul_le_mul_of_nonneg_left hR hM
      _ = _ := by dsimp only [morseInitialCoreMassConstant, M]; ring
  have hQ : 0 ≤ morseInitialCoreMassConstant T σ D L := by
    dsimp only [morseInitialCoreMassConstant]
    change 0 ≤ M * exp _ / _
    positivity
  have hexp := nonneg_le_exp_mul_nat_sq hQ hn
  calc
    _ ≤ M := hbound
    _ ≤ morseInitialCoreMassConstant T σ D L * scale := (div_le_iff₀ hscale).mp hratio
    _ ≤ exp (morseInitialCoreMassConstant T σ D L * (T.index : ℝ) ^ 2) * scale :=
      mul_le_mul_of_nonneg_right hexp hscale.le
    _ = _ := mul_comm _ _

end ContinuousFlexibility.Radial
