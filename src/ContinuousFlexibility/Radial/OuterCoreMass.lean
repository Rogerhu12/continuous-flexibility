module

public import ContinuousFlexibility.Radial.MorseRealizedIntegralTransfer
public import ContinuousFlexibility.Radial.MorseRealizedConnectorBounds

/-!
# The Hilbert density on the actual transition core

The Hilbert density is `12 w / r²`; the mass density used in the
mass-resistance construction is `w r⁶`.  The positive inner radius gives
their explicit comparison.  The retained-cell estimates below use the
actual physical profile and the already proved model integrals.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

/-- The Hilbert mass of an interval in increasing physical radius. -/
def radialHilbertIntervalMass (D : ReferenceData) (l r : ℝ) : ℝ :=
  ∫ x in l..r, 12 * D.w x / x ^ 2

theorem radialHilbertIntervalMass_le_moment {D : ReferenceData}
    (hD : RadialProfileGeometry D) {l r : ℝ} (hlr : l ≤ r)
    (hsub : Icc l r ⊆ radialCore D) :
    radialHilbertIntervalMass D l r ≤
      (12 / D.a ^ 8) * (∫ x in l..r, D.w x * x ^ 6) := by
  have hw : Continuous D.w := hD.2.2.1.1.continuous
  have hx₀ (x : ℝ) (hx : x ∈ Icc l r) : 0 < x := hD.1.trans (hsub hx).1
  have hw₀ (x : ℝ) (hx : x ∈ Icc l r) : 0 ≤ D.w x :=
    (hD.2.2.2.2.1 x (hsub hx)).le
  have hpoint (x : ℝ) (hx : x ∈ Icc l r) :
      12 * D.w x / x ^ 2 ≤ (12 / D.a ^ 8) * (D.w x * x ^ 6) := by
    have hp : D.a ^ 8 ≤ x ^ 8 :=
      pow_le_pow_left₀ hD.1.le (hsub hx).1.le 8
    have hratio : (1 : ℝ) / x ^ 2 ≤ x ^ 6 / D.a ^ 8 := by
      apply (div_le_div_iff₀ (pow_pos (hx₀ x hx) 2) (pow_pos hD.1 8)).mpr
      calc
        1 * D.a ^ 8 = D.a ^ 8 := one_mul _
        _ ≤ x ^ 8 := hp
        _ = x ^ 6 * x ^ 2 := by ring
    calc
      _ = (12 * D.w x) * (1 / x ^ 2) := by ring
      _ ≤ (12 * D.w x) * (x ^ 6 / D.a ^ 8) :=
        mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) (hw₀ x hx))
      _ = _ := by ring
  have hleft : ContinuousOn (fun x => 12 * D.w x / x ^ 2) (Icc l r) :=
    (continuousOn_const.mul hw.continuousOn).div (continuousOn_id.pow 2)
      (fun x hx => (pow_pos (hx₀ x hx) 2).ne')
  have hright : Continuous (fun x : ℝ => (12 / D.a ^ 8) * (D.w x * x ^ 6)) :=
    continuous_const.mul (hw.mul (continuous_id.pow 6))
  calc
    _ ≤ ∫ x in l..r, (12 / D.a ^ 8) * (D.w x * x ^ 6) :=
      intervalIntegral.integral_mono_on hlr
        (hleft.intervalIntegrable_of_Icc hlr) (hright.intervalIntegrable l r) hpoint
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- A whole retained cell, including its long cap, has Hilbert mass on
the same height scale as its physical profile. -/
theorem morseRealized_cell_hilbert_mass_le {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {K : ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) :
    radialHilbertIntervalMass D (T.radius side n (T.leftX side n))
        (T.radius side n (T.rightX side n)) ≤
      (12 / D.a ^ 8) * morseChainAmplitude T σ n * K *
        (morseChainA T n ^ 2 + morseChainA T n ^ 6) := by
  let l := T.radius side n (T.leftX side n)
  let r := T.radius side n (T.rightX side n)
  let c := morseChainMassEnd T side n
  obtain ⟨_, _, _, hlt, htr, _, _⟩ := h.retained_data side n hn
  have horder := hlt.trans htr
  have hl : l ∈ radialCore D :=
    h.radius_mem_core side n hn _ (left_mem_Icc.mpr horder.le)
  have hr : r ∈ radialCore D :=
    h.radius_mem_core side n hn _ (right_mem_Icc.mpr horder.le)
  have hlr : l ≤ r := (h.radius_strictMonoOn side n hn).monotoneOn
    (left_mem_Icc.mpr horder.le) (right_mem_Icc.mpr horder.le) horder.le
  have hsub : Icc l r ⊆ radialCore D := fun _ hx =>
    ⟨hl.1.trans_le hx.1, hx.2.trans_lt hr.2⟩
  have hw : Continuous (fun x : ℝ => D.w x * x ^ 6) :=
    h.geometry.2.2.1.1.continuous.mul (continuous_id.pow 6)
  have hsplit : (∫ x in l..r, D.w x * x ^ 6) =
      morseCellMass T D side n + (∫ x in c..r, D.w x * x ^ 6) := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hw.intervalIntegrable l c) (hw.intervalIntegrable c r)).symm
  have hmodels := morseRealized_model_integrals h hσ side n hn
  have hlam : 0 ≤ morseChainAmplitude T σ n := (morseChainAmplitude_pos T σ hσ n).le
  have hmoment : (∫ x in l..r, D.w x * x ^ 6) ≤
      morseChainAmplitude T σ n * K * (morseChainA T n ^ 2 + morseChainA T n ^ 6) := by
    rw [hsplit, hmodels.1, hmodels.2.2.1]
    calc
      _ ≤ morseChainAmplitude T σ n * (K * morseChainA T n ^ 2) +
          morseChainAmplitude T σ n * (K * morseChainA T n ^ 6) :=
        add_le_add (mul_le_mul_of_nonneg_left (hcell.mass_upper side n hn) hlam)
          (mul_le_mul_of_nonneg_left (hcell.cap_mass_upper side n hn) hlam)
      _ = _ := by ring
  calc
    _ ≤ (12 / D.a ^ 8) * (∫ x in l..r, D.w x * x ^ 6) :=
      radialHilbertIntervalMass_le_moment h.geometry hlr hsub
    _ ≤ (12 / D.a ^ 8) *
        (morseChainAmplitude T σ n * K * (morseChainA T n ^ 2 + morseChainA T n ^ 6)) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = _ := by ring

/-- Every compact connector is compared with the physical mass integral
on that same connector, with no identification of the two measures. -/
theorem morseRealized_join_hilbert_mass_le {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) :
    radialHilbertIntervalMass D (T.joinLeft side n) (T.joinRight side n) ≤
      (12 / D.a ^ 8) *
        (∫ x in T.joinLeft side n..T.joinRight side n, D.w x * x ^ 6) := by
  obtain ⟨hi, hj, _, hl, hr, _⟩ := morseRealizedJoin_endpoints h side n hn
  have hleftOrder := (h.retained_data side (if side then n else n + 1) hi).2.2.2
  have hrightOrder := (h.retained_data side (if side then n + 1 else n) hj).2.2.2
  have hlcore : T.joinLeft side n ∈ radialCore D := by
    rw [hl]
    exact h.radius_mem_core side _ hi _
      (right_mem_Icc.mpr (hleftOrder.1.trans hleftOrder.2.1).le)
  have hrcore : T.joinRight side n ∈ radialCore D := by
    rw [hr]
    exact h.radius_mem_core side _ hj _
      (left_mem_Icc.mpr (hrightOrder.1.trans hrightOrder.2.1).le)
  exact radialHilbertIntervalMass_le_moment h.geometry (h.join_data side n hn).1.le
    (fun _ hx => ⟨hlcore.1.trans_le hx.1, hx.2.trans_lt hrcore.2⟩)

end ContinuousFlexibility.Radial
