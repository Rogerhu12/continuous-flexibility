module

public import ContinuousFlexibility.Radial.MorseRealizationBasic
public import ContinuousFlexibility.Radial.MorseTransitionBands

/-!
# Entrances of the actual selected-chain construction

These statements concern the concrete radius expression used by R07's
\x60r07CellEntry\x60. They need only the already realized chain, so they do
not import the later incoming-ODE construction just to name that expression.
Every retained cell has a valid entrance, including cells whose frequency
band happens to be empty. Successive entrances move strictly outwards.
A sufficiently large construction index and Cstar put mode two in the
first band, independently of any existential selected-tail witness.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

theorem r10a_actual_entry_mem_core {T : MorseChainData} {σ constants : ℕ → ℝ}
    {D : ReferenceData} (hreal : MorseChainRealization T σ D constants)
    (right : Bool) {n : ℕ} (hn : T.index ≤ n) :
    T.radius right n (if right then T.leftX right n else T.rightX right n) ∈ radialCore D := by
  have hspan : T.leftX right n < T.rightX right n := (hreal.2.2.1 right n hn).2.1
  apply hreal.radius_mem_core right n hn
  cases right
  · exact ⟨hspan.le, le_rfl⟩
  · exact ⟨le_rfl, hspan.le⟩

/-- The cell width and the intervening positive gap both contribute to
strict outward ordering of the actual entries. -/
theorem r10a_actual_entry_succ_outward {T : MorseChainData} {σ constants : ℕ → ℝ}
    {D : ReferenceData} (hreal : MorseChainRealization T σ D constants)
    (right : Bool) {n : ℕ} (hn : T.index ≤ n) :
    if right then T.radius right n (if right then T.leftX right n else T.rightX right n) < T.radius right (n + 1) (if right then T.leftX right (n + 1) else T.rightX right (n + 1))
      else T.radius right (n + 1) (if right then T.leftX right (n + 1) else T.rightX right (n + 1)) < T.radius right n (if right then T.leftX right n else T.rightX right n) := by
  have hspan : T.leftX right n < T.rightX right n := (hreal.2.2.1 right n hn).2.1
  have hcell : T.radius right n (T.leftX right n) <
      T.radius right n (T.rightX right n) :=
    hreal.radius_strictMonoOn right n hn
      ⟨le_rfl, hspan.le⟩ ⟨hspan.le, le_rfl⟩ hspan
  have hjoin := hreal.join_data right n hn
  have hgap := hjoin.1
  rw [hjoin.2.1, hjoin.2.2.1] at hgap
  cases right
  · exact hgap.trans hcell
  · exact hcell.trans hgap

/-- Every later actual entrance belongs to the retained side of an
earlier entrance, with a single orientation parameter. -/
theorem r10a_actual_entry_outward_le {T : MorseChainData} {σ constants : ℕ → ℝ}
    {D : ReferenceData} (hreal : MorseChainRealization T σ D constants)
    (right : Bool) {m n : ℕ} (hm : T.index ≤ m) (hmn : m ≤ n) :
    if right then T.radius right m (if right then T.leftX right m else T.rightX right m) ≤ T.radius right n (if right then T.leftX right n else T.rightX right n)
      else T.radius right n (if right then T.leftX right n else T.rightX right n) ≤ T.radius right m (if right then T.leftX right m else T.rightX right m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero =>
      simp only [Nat.add_zero]
      cases right <;> exact le_rfl
  | succ k ih =>
      have ih' := ih (Nat.le_add_right m k)
      have hstep := r10a_actual_entry_succ_outward hreal right
        (hm.trans (Nat.le_add_right m k))
      cases right
      · exact hstep.le.trans ih'
      · exact ih'.trans hstep.le

theorem r10a_actual_entry_retained {T : MorseChainData} {σ constants : ℕ → ℝ}
    {D : ReferenceData} (hreal : MorseChainRealization T σ D constants)
    (right : Bool) {n : ℕ} (hn : T.index ≤ n) :
    T.radius right n (if right then T.leftX right n else T.rightX right n) ∈ radialCore D ∧
      (if right then T.radius right T.index (if right then T.leftX right T.index else T.rightX right T.index) ≤ T.radius right n (if right then T.leftX right n else T.rightX right n)
        else T.radius right n (if right then T.leftX right n else T.rightX right n) ≤ T.radius right T.index (if right then T.leftX right T.index else T.rightX right T.index)) :=
  ⟨r10a_actual_entry_mem_core hreal right hn,
    r10a_actual_entry_outward_le hreal right le_rfl hn⟩

/-- The actual large-index construction has a nonempty first band:
mode two is already below its first transition threshold. -/
theorem r10a_actual_first_band_two {T : MorseChainData} {σ constants : ℕ → ℝ}
    {D : ReferenceData} (hreal : MorseChainRealization T σ D constants)
    {C : ℝ} (hC : 1000 ≤ C) (hstart : 1 ≤ T.index) :
    radialFrequencyBand T C T.index 2 := by
  have hCpos : 0 < C := (by norm_num : (0 : ℝ) < 1000).trans_le hC
  have hA := morseChainA_exp_bounds T T.index (hreal.d_eq T.index le_rfl)
  have hApos : 0 < morseChainA T T.index :=
    (div_pos (exp_pos _) (by norm_num)).trans_le hA.1
  have hA9 : morseChainA T T.index ≤ 9 := hA.2.trans
    (mul_le_of_le_one_right (by norm_num)
      (exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))))
  have hsqrt : sqrt (morseChainA T T.index) ≤ 3 := by
    have hs := sqrt_le_sqrt hA9
    rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num,
      sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)] at hs
    exact hs
  have hindex : (1 : ℝ) ≤ (T.index : ℝ) := by exact_mod_cast hstart
  have hsq : (1 : ℝ) ≤ (T.index : ℝ) ^ 2 := by
    simpa only [one_pow] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hindex 2
  have hQ : 1 ≤ radialQ T.index := hsq.trans (radial_nat_sq_le_Q T.index)
  have hCQ : C ≤ C * radialQ T.index := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hQ hCpos.le
  apply (morseTransition_initial_band_iff T C 2).mpr
  refine ⟨le_rfl, ?_⟩
  change (2 : ℝ) < C * radialQ T.index / sqrt (morseChainA T T.index)
  apply (lt_div_iff₀ (sqrt_pos.mpr hApos)).mpr
  have hlarge := hC.trans hCQ
  linarith only [hsqrt, hlarge]

end ContinuousFlexibility.Radial
