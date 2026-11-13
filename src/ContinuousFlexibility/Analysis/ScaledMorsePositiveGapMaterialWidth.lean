import ContinuousFlexibility.Analysis.MorsePositiveGapCells
import ContinuousFlexibility.Analysis.N06MorsePositiveWidth
import ContinuousFlexibility.Analysis.MaterialCellOverlapRadialPolynomial
import ContinuousFlexibility.Radial.DeepTailPhysicalWeights

/-!
# Material width of the same scaled positive Morse gap

Only the actual radius dilation and cell/index transport identities are
inputs. A real point of the gap supplies its original n or n + 1 cell.
The fixed index shift and the genuine material overlap estimate then
bound the width at any cell containing the physical midpoint. No whole
positive component is required to lie in that cell.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

/-- A fixed positive-gap model power is controlled at any actual cell
containing the same transported point. All constants precede the gap. -/
theorem morseRealization_scaled_positive_gap_weight_bound
    {Q : MorseChainData} {σ : ℕ → ℝ} {D E : ReferenceData} {C : ℕ → ℝ}
    {T : MaterialData} (hreal : MorseChainRealization Q σ D C)
    (hT : IsMaterialData E T) (hE : IsAccumulatingProfile E)
    (R : Bool → ℝ)
    (hcell : ∀ (side : Bool) (n : ℕ), Q.index ≤ n → ∀ m r,
      r ∈ Icc (n06MorsePositiveLeft Q side n) (n06MorsePositiveRight Q side n) →
      r ∈ D.cells m → R side * r ∈ E.cells m)
    (hindex : ∀ m, D.cellIndex m ≤ E.cellIndex m)
    {P : ℝ} (hP : 0 ≤ P) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ (side : Bool) (n : ℕ), Q.index ≤ n →
      ∀ j r, r ∈ Icc (n06MorsePositiveLeft Q side n) (n06MorsePositiveRight Q side n) →
        R side * r ∈ E.cells j →
        radialE (n + 1) ^ P ≤ K * T.E0 (T.sample j) ^ A := by
  obtain ⟨B, hB, hshift⟩ := physicalWeight_shift P hP 1
  obtain ⟨K, A, hK, hA, hweight⟩ :=
    materialCells_overlap_radialE_power_bound hT hE hB.le
  refine ⟨B * K, A, mul_pos hB hK, hA, ?_⟩
  intro side n hn j r hr hj
  obtain ⟨m, hm, hrm⟩ := morseRealization_positive_gap_cell_labels hreal side hn hr
  have hnm : n ≤ D.cellIndex m := by
    rcases hm with hm | hm <;> rw [hm] <;> omega
  have hmat := hweight m j n (R side * r)
    (hcell side n hn m r hr hrm) hj (hnm.trans (hindex m))
  calc
    radialE (n + 1) ^ P ≤ B * radialE n ^ B := hshift n
    _ ≤ B * (K * T.E0 (T.sample j) ^ A) := mul_le_mul_of_nonneg_left hmat hB.le
    _ = (B * K) * T.E0 (T.sample j) ^ A := by ring

/-- The fixed arrival cap gives a material inverse-width bound for the
same scaled gap, at its actual midpoint cell. The radius factors are
the fixed two tail dilations, not new componentwise choices. -/
theorem morseRealization_scaled_positive_gap_inverse_width_bound
    {Q : MorseChainData} {σ : ℕ → ℝ} {D E : ReferenceData} {C : ℕ → ℝ}
    {T : MaterialData} (hreal : MorseChainRealization Q σ D C)
    (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (hT : IsMaterialData E T) (hE : IsAccumulatingProfile E)
    (R : Bool → ℝ) (hR : ∀ side, 0 < R side)
    (hcell : ∀ (side : Bool) (n : ℕ), Q.index ≤ n → ∀ m r,
      r ∈ Icc (n06MorsePositiveLeft Q side n) (n06MorsePositiveRight Q side n) →
      r ∈ D.cells m → R side * r ∈ E.cells m)
    (hindex : ∀ m, D.cellIndex m ≤ E.cellIndex m) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ (side : Bool) (n : ℕ), Q.index ≤ n → ∀ j,
      R side * ((n06MorsePositiveLeft Q side n + n06MorsePositiveRight Q side n) / 2)
        ∈ E.cells j →
      (R side * n06MorsePositiveRight Q side n -
        R side * n06MorsePositiveLeft Q side n)⁻¹ ≤ K * T.E0 (T.sample j) ^ A := by
  obtain ⟨K₀, A, hK₀, hA, hweight⟩ :=
    morseRealization_scaled_positive_gap_weight_bound hreal hT hE R hcell hindex
      (hreal.constants_pos 0).le
  let c : ℝ := morseShortLeftCapLength / (2 * C 0)
  have hc : 0 < c := div_pos morseShortLeftCapLength_pos
    (mul_pos (by norm_num) (hreal.constants_pos 0))
  let B : ℝ := max (R false)⁻¹ (R true)⁻¹
  have hB : 0 < B := (inv_pos.mpr (hR false)).trans_le (le_max_left _ _)
  have hRB (side : Bool) : (R side)⁻¹ ≤ B := by
    cases side
    · exact le_max_left _ _
    · exact le_max_right _ _
  refine ⟨B * c⁻¹ * K₀, A, mul_pos (mul_pos hB (inv_pos.mpr hc)) hK₀, hA, ?_⟩
  intro side n hn j hj
  let l : ℝ := n06MorsePositiveLeft Q side n
  let u : ℝ := n06MorsePositiveRight Q side n
  have hg := n06_morsePositive_gap_geometry hreal side hn
  have hlu : l < u := hg.2.1.trans (hg.2.2.1.trans hg.2.2.2.1)
  have hmid : (l + u) / 2 ∈ Icc l u := by constructor <;> linarith only [hlu]
  have hmat := hweight side n hn j ((l + u) / 2) hmid hj
  have hwidth : c * radialE (n + 1) ^ (-C 0) ≤ u - l :=
    n06_morseRealization_positive_gap_length_lower hreal hσ side hn
  have hpositive : 0 < c * radialE (n + 1) ^ (-C 0) :=
    mul_pos hc (Real.rpow_pos_of_pos (exp_pos _) _)
  have hinv : (u - l)⁻¹ ≤ c⁻¹ * radialE (n + 1) ^ (C 0) := by
    calc
      (u - l)⁻¹ ≤ (c * radialE (n + 1) ^ (-C 0))⁻¹ := inv_anti₀ hpositive hwidth
      _ = c⁻¹ * radialE (n + 1) ^ (C 0) := by
        have hE0 : 0 ≤ radialE (n + 1) := (exp_pos _).le
        rw [mul_inv_rev, Real.rpow_neg hE0, inv_inv]
        ring
  change (R side * u - R side * l)⁻¹ ≤ (B * c⁻¹ * K₀) * T.E0 (T.sample j) ^ A
  calc
    (R side * u - R side * l)⁻¹ = (R side)⁻¹ * (u - l)⁻¹ := by
      rw [← mul_sub, mul_inv_rev]
      ring
    _ ≤ (R side)⁻¹ * (c⁻¹ * radialE (n + 1) ^ (C 0)) :=
      mul_le_mul_of_nonneg_left hinv (inv_pos.mpr (hR side)).le
    _ ≤ B * (c⁻¹ * radialE (n + 1) ^ (C 0)) :=
      mul_le_mul_of_nonneg_right (hRB side)
        (mul_nonneg (inv_pos.mpr hc).le (Real.rpow_nonneg (exp_pos _).le _))
    _ ≤ B * (c⁻¹ * (K₀ * T.E0 (T.sample j) ^ A)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmat (inv_pos.mpr hc).le) hB.le
    _ = (B * c⁻¹ * K₀) * T.E0 (T.sample j) ^ A := by ring

end ContinuousFlexibility.Analysis
