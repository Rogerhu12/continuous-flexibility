module

public import ContinuousFlexibility.Analysis.N06MorsePhysicalPositiveFloor

/-!
# The actual positive coefficient on the Morse joins

The original realization covers every join point by a physical cell of
the same index. Its original reciprocal-profile estimate and the actual
join logarithmic slope then give a coefficient-power positive floor.
The slope inequality is extended to the two endpoints by continuity.
No bound on a new canonical chart is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The original zeroth reciprocal-profile bound already supplies a
coefficient-power lower bound on the same physical profile. -/
theorem n06_accumulatingProfile_cell_lower
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : AccumulatingProfileBounds D C) (m : ℕ) {r : ℝ} (hr : r ∈ D.cells m) :
    (C 0)⁻¹ * radialE (D.cellIndex m) ^ (-C 0) ≤ D.w r := by
  rcases h with ⟨hgeom, hpart, hC, _, _, _, _, _, _, hinv, _, _, _⟩
  have hcore : r ∈ radialCore D := hpart.2.2.2.1 m hr
  have hwp : 0 < D.w r := hgeom.2.2.2.2.1 r hcore
  have hb := hinv m r hr 0
  change |(D.w r)⁻¹| ≤ C 0 * radialE (D.cellIndex m) ^ C 0 at hb
  rw [abs_of_pos (inv_pos.mpr hwp)] at hb
  have hi := inv_le_of_inv_le₀ hwp hb
  have hE : 0 < radialE (D.cellIndex m) := exp_pos _
  simpa only [mul_inv_rev, Real.rpow_neg hE.le, mul_comm] using hi

/-- Every actual closed join lies in its own physical seam block,
on either tail. -/
theorem n06_morseRealization_join_subset_block
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) :
    Icc (T.joinLeft side n) (T.joinRight side n) ⊆ morseChainBlock T side n := by
  have hj := hreal.join_data side n hn
  have hab := (hreal.2.2.1 side n hn).2.1
  have hmono := (hreal.radius_strictMonoOn side n hn).monotoneOn
  have hends := hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab.le
  have hjoin := hj.1
  rw [hj.2.1, hj.2.2.1] at hjoin
  intro r hr
  rw [hj.2.1, hj.2.2.1] at hr
  cases side with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hjoin hr
    change r ∈ uIcc (T.radius false n (T.rightX false n))
      (T.radius false (n + 1) (T.rightX false (n + 1)))
    rw [uIcc_of_ge (hjoin.le.trans hends)]
    exact ⟨hr.1, hr.2.trans hends⟩
  | true =>
    simp only [↓reduceIte] at hjoin hr
    change r ∈ uIcc (T.radius true n (T.leftX true n))
      (T.radius true (n + 1) (T.leftX true (n + 1)))
    rw [uIcc_of_le (hends.trans hjoin.le)]
    exact ⟨hends.trans hr.1, hr.2⟩

/-- Both endpoints, and therefore the entire closed join, remain inside
the original physical annulus. -/
theorem n06_morseRealization_join_subset_core
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) :
    Icc (T.joinLeft side n) (T.joinRight side n) ⊆ radialCore D := by
  have hj := hreal.join_data side n hn
  have hn₁ : T.index ≤ n + 1 := hn.trans (Nat.le_succ n)
  have hleft (i : ℕ) (hi : T.index ≤ i) :
      T.radius side i (T.leftX side i) ∈ radialCore D :=
    hreal.radius_mem_core side i hi _ ⟨le_rfl, (hreal.2.2.1 side i hi).2.1.le⟩
  have hright (i : ℕ) (hi : T.index ≤ i) :
      T.radius side i (T.rightX side i) ∈ radialCore D :=
    hreal.radius_mem_core side i hi _ ⟨(hreal.2.2.1 side i hi).2.1.le, le_rfl⟩
  have hL : T.joinLeft side n ∈ radialCore D := by
    rw [hj.2.1]
    cases side
    · exact hright (n + 1) hn₁
    · exact hright n hn
  have hR : T.joinRight side n ∈ radialCore D := by
    rw [hj.2.2.1]
    cases side
    · exact hleft n hn
    · exact hleft (n + 1) hn₁
  intro r hr
  exact ⟨hL.1.trans_le hr.1, hr.2.trans_lt hR.2⟩

/-- The original join slope, multiplied through by its positive
denominators, also holds at the two actual endpoints. -/
theorem n06_morseRealization_join_closed_slope
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) :
    ∀ r ∈ Icc (T.joinLeft side n) (T.joinRight side n),
      2 * D.w r ≤ r * deriv D.w r := by
  have hj := hreal.join_data side n hn
  have hsub : Ioo (T.joinLeft side n) (T.joinRight side n) ⊆
      {r | 2 * D.w r ≤ r * deriv D.w r} := by
    intro r hr
    have hcore := n06_morseRealization_join_subset_core hreal side hn ⟨hr.1.le, hr.2.le⟩
    have hrp : 0 < r := hreal.geometry.1.trans hcore.1
    have hwp : 0 < D.w r := hreal.geometry.2.2.2.2.1 r hcore
    change 2 * D.w r ≤ r * deriv D.w r
    simpa only [mul_comm] using
      (div_le_div_iff₀ hrp hwp).mp (hj.2.2.2.2 r hr)
  have hw : Continuous D.w := hreal.geometry.2.2.1.1.continuous
  have hwd : Continuous (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hreal.geometry.2.2.1.1).2.continuous
  have hclosed : IsClosed {r | 2 * D.w r ≤ r * deriv D.w r} :=
    isClosed_le (continuous_const.mul hw) (continuous_id.mul hwd)
  have hclosure := closure_minimal hsub hclosed
  rw [closure_Ioo hj.1.ne] at hclosure
  exact hclosure

/-- A literal uniform floor for the physical positive coefficient on
all original closed joins. Its exponent and constant come from the
original accumulating profile estimates. -/
theorem n06_morseRealization_join_coefficient_lower
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) {r : ℝ}
    (hr : r ∈ Icc (T.joinLeft side n) (T.joinRight side n)) :
    (2 / (C 0 * D.b ^ 2)) * radialE n ^ (-C 0) ≤ deriv D.w r / r := by
  have hcore := n06_morseRealization_join_subset_core hreal side hn hr
  have hrp : 0 < r := hreal.geometry.1.trans hcore.1
  have hbp : 0 < D.b := hrp.trans hcore.2
  have hwp : 0 < D.w r := hreal.geometry.2.2.2.2.1 r hcore
  have hCp : 0 < C 0 := hreal.constants_pos 0
  obtain ⟨m, hm, hrm⟩ := hreal.2.2.2.2.2.2.2.2.1 side n hn r
    (n06_morseRealization_join_subset_block hreal side hn hr)
  have hprofile : (C 0)⁻¹ * radialE n ^ (-C 0) ≤ D.w r := by
    simpa only [hm] using n06_accumulatingProfile_cell_lower hreal.accumulating m hrm
  have hslope := n06_morseRealization_join_closed_slope hreal side hn r hr
  have hsq : r ^ 2 ≤ D.b ^ 2 := pow_le_pow_left₀ hrp.le hcore.2.le 2
  calc
    (2 / (C 0 * D.b ^ 2)) * radialE n ^ (-C 0) =
        (2 * ((C 0)⁻¹ * radialE n ^ (-C 0))) / D.b ^ 2 := by
      field_simp [hCp.ne', hbp.ne'] <;> ring
    _ ≤ (2 * D.w r) / D.b ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprofile (by norm_num))
        (sq_nonneg _)
    _ ≤ (2 * D.w r) / r ^ 2 :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hwp.le)
        (sq_pos_of_pos hrp) hsq
    _ ≤ deriv D.w r / r := by
      apply (div_le_iff₀ (sq_pos_of_pos hrp)).mpr
      calc
        2 * D.w r ≤ r * deriv D.w r := hslope
        _ = (deriv D.w r / r) * r ^ 2 := by field_simp [hrp.ne'] <;> ring

end ContinuousFlexibility.Analysis
