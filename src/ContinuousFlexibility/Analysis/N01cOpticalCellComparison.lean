import ContinuousFlexibility.Analysis.N01aMaterialContext
import ContinuousFlexibility.Analysis.N01aControlMaterialWeights

/-!
# Comparing optical lower weights on overlapping actual cells

An actual material coordinate is used only to read the existing bounded
index-coordinate discrepancy. Hence two cells meeting at one point have
indices differing by a uniform additive constant. A negative envelope
power at either index is controlled by one negative power at the other.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Real
open ContinuousFlexibility.Radial

/-- Two actual cells meeting at a point have a uniformly bounded additive
index discrepancy. This follows directly from the already constructed
material coordinate, without a new logarithm estimate. -/
theorem exists_n01c_overlappingCell_indexBound
    {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    ∃ B : ℝ, 0 < B ∧ ∀ i j : ℕ, ∀ r : ℝ,
      r ∈ D.cells i → r ∈ D.cells j →
      |(D.cellIndex i : ℝ) - D.cellIndex j| ≤ B := by
  obtain ⟨sample, hT, _, _⟩ := exists_n01a_affineMaterialData hD
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcompare⟩ := hT
  obtain ⟨C, A, hC, hA, hindex⟩ := hcompare
  refine ⟨2 * C, by positivity, fun i j r hri hrj => ?_⟩
  let x : ℝ := ContinuousFlexibility.Analysis.endpointX 1 (endpointDistance D r)
  have hi : |(D.cellIndex i : ℝ) - x| ≤ C := by
    simpa only [abs_sub_comm] using (hindex i r hri).1
  have hj : |x - (D.cellIndex j : ℝ)| ≤ C := (hindex j r hrj).1
  calc
    |(D.cellIndex i : ℝ) - D.cellIndex j| =
        |((D.cellIndex i : ℝ) - x) + (x - D.cellIndex j)| := by congr 1; ring
    _ ≤ |(D.cellIndex i : ℝ) - x| + |x - (D.cellIndex j : ℝ)| := abs_add_le _ _
    _ ≤ C + C := add_le_add hi hj
    _ = 2 * C := by ring

/-- Negative coefficient powers transfer between two actual cells that
meet. The constants depend on the profile and input exponent, not the
cells or their common point. -/
theorem exists_n01c_overlappingCell_negativePower
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {c α : ℝ} (hc : 0 < c) (hα : 0 ≤ α) :
    ∃ B : ℝ, 0 < B ∧ ∀ i j : ℕ, ∀ r : ℝ,
      r ∈ D.cells i → r ∈ D.cells j →
      B⁻¹ * radialE (D.cellIndex j) ^ (-B) ≤
        c * radialE (D.cellIndex i) ^ (-α) := by
  obtain ⟨C, hC, hindex⟩ := exists_n01c_overlappingCell_indexBound hD
  obtain ⟨L, hL, hQ⟩ := n01a_radialQ_linear_bound (C + 1)
  let M : ℝ := exp (α * L) / c
  let B : ℝ := max 1 (max (α * L) M)
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hαB : α * L ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hMB : M ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, hB, fun i j r hri hrj => ?_⟩
  have hij := (abs_le.mp (hindex i j r hri hrj)).2
  have hn : (D.cellIndex i : ℝ) ≤ (C + 1) * (1 + (D.cellIndex j : ℝ)) := by
    have hj0 : (0 : ℝ) ≤ D.cellIndex j := Nat.cast_nonneg _
    nlinarith only [hij, mul_nonneg hC.le hj0]
  have hq := mul_le_mul_of_nonneg_left (hQ _ _ hn) hα
  have hE : 1 ≤ radialE (D.cellIndex j) :=
    one_le_exp_iff.mpr (radialQ_nonneg _)
  have hRpos : 0 < radialE (D.cellIndex i) := exp_pos _
  have hEpos : 0 < radialE (D.cellIndex j) := exp_pos _
  have hp : radialE (D.cellIndex i) ^ α ≤
      exp (α * L) * radialE (D.cellIndex j) ^ (α * L) := by
    rw [radialE, radialE, ← exp_mul, ← exp_mul, ← exp_add]
    apply exp_le_exp.mpr
    nlinarith only [hq]
  have hb : c⁻¹ * radialE (D.cellIndex i) ^ α ≤
      B * radialE (D.cellIndex j) ^ B := by
    calc
      c⁻¹ * radialE (D.cellIndex i) ^ α ≤
          c⁻¹ * (exp (α * L) * radialE (D.cellIndex j) ^ (α * L)) :=
        mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hc.le)
      _ = M * radialE (D.cellIndex j) ^ (α * L) := by dsimp only [M]; ring
      _ ≤ B * radialE (D.cellIndex j) ^ B :=
        mul_le_mul hMB (rpow_le_rpow_of_exponent_le hE hαB)
          (rpow_nonneg hEpos.le _) hB.le
  have hinv := one_div_le_one_div_of_le
    (mul_pos (inv_pos.mpr hc) (rpow_pos_of_pos hRpos α)) hb
  rw [rpow_neg hEpos.le, rpow_neg hRpos.le]
  simpa only [one_div, mul_inv_rev, inv_inv, mul_comm] using hinv

end ContinuousFlexibility.Statements
