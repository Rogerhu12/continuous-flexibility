import ContinuousFlexibility.Analysis.MaterialSampleShift

/-!
# Comparison of actual containing radial cells

Two cells containing the same point have uniformly close cell indices.
Every fixed radial loss can therefore be transferred between them with
a new fixed power. No identification with a control label is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem one_le_radialE_of_nat (n : ℕ) : 1 ≤ radialE n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have he : 1 ≤ Real.exp 1 + (n : ℝ) :=
    (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans
      (le_add_of_nonneg_right hn)
  exact Real.one_le_exp_iff.mpr
    (mul_nonneg (Real.rpow_nonneg hn _) (Real.log_nonneg he))

theorem radialE_rpow_of_nat_sub_bound
    {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ i j : ℕ,
      |(i : ℝ) - j| ≤ B → radialE i ^ R ≤ K * radialE j ^ A := by
  obtain ⟨K, A, hK, hA, hb⟩ := materialE0_rpow_oneSided_shift hR hB
  refine ⟨K * Real.exp A, A, mul_pos hK (Real.exp_pos _), hA, fun i j hij => ?_⟩
  have hshift : (i : ℝ) ≤ (j : ℝ) + B := by linarith only [(abs_le.mp hij).2]
  have heq : materialE0 (j : ℝ) ^ A = Real.exp A * radialE j ^ A := by
    simp only [materialE0, materialE0Exponent, materialLogFactor,
      radialE, radialQ, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ materialE0 (i : ℝ) ^ R := radialE_rpow_le_materialE0_natCast i hR
    _ ≤ K * materialE0 (j : ℝ) ^ A := hb i j (Nat.cast_nonneg _) (Nat.cast_nonneg _) hshift
    _ = _ := by rw [heq]; ring

theorem material_actualCells_index_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) :
    ∃ B : ℝ, 0 < B ∧ ∀ i j : ℕ, ∀ r : ℝ,
      r ∈ D.cells i → r ∈ D.cells j →
      |(D.cellIndex i : ℝ) - D.cellIndex j| ≤ B := by
  have hdata := hT
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcomp⟩
  obtain ⟨B, _, hB, _, hb⟩ := hcomp
  refine ⟨2 * B, mul_pos (by norm_num) hB, fun i j r hi hj => ?_⟩
  have hleft : |(D.cellIndex i : ℝ) - endpointX 1 (endpointDistance D r)| ≤ B := by
    rw [abs_sub_comm]
    exact (hb i r hi).1
  calc
    _ ≤ |(D.cellIndex i : ℝ) - endpointX 1 (endpointDistance D r)| +
        |endpointX 1 (endpointDistance D r) - D.cellIndex j| := abs_sub_le _ _ _
    _ ≤ B + B := add_le_add hleft (hb j r hj).1
    _ = _ := by ring

end ContinuousFlexibility.Statements
