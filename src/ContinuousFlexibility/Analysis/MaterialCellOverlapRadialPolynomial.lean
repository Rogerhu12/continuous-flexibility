module

public import ContinuousFlexibility.Analysis.MaterialCellEndpointModels
public import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# Radial envelopes on overlapping actual material cells

A model cell and the actual host of a negative component need not have
the same index. A common physical point compares both indices to one
endpoint coordinate. The sample of the host then gives a uniform
polynomial material bound, without changing either cell assignment.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

/-- A radial model scale dominated by one actual cell index is controlled
by the material sample of any actual cell meeting it. All constants are
chosen before the cells, the model index, and their common point. -/
theorem materialCells_overlap_radialE_power_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ K P : ℝ, 0 < K ∧ 0 ≤ P ∧ ∀ m j n : ℕ, ∀ r : ℝ,
      r ∈ D.cells m → r ∈ D.cells j → n ≤ D.cellIndex m →
      radialE n ^ R ≤ K * T.E0 (T.sample j) ^ P := by
  obtain ⟨d0, L, KH, KE, KM, _, hL, _, hKE, _, hmodels⟩ :=
    materialCell_global_endpoint_models hT hRef
  obtain ⟨K, P, hK, hP, hshift⟩ :=
    materialE0_rpow_oneSided_shift hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hL)
  have hKEpos : 0 < KE := zero_lt_one.trans_le hKE
  have hsample : ∀ j, T.sample j ∈ D.cells j := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ := hT
    exact hs
  refine ⟨K * KE ^ P, P, mul_pos hK (Real.rpow_pos_of_pos hKEpos _), hP, ?_⟩
  intro m j n r hm hj hn
  let x := endpointX d0 (endpointDistance D (T.sample j))
  let y := endpointX d0 (endpointDistance D r)
  have hmx : |y - (D.cellIndex m : ℝ)| ≤ L := (hmodels m r hm).2.1
  have hjy : |y - (D.cellIndex j : ℝ)| ≤ L := (hmodels j r hj).2.1
  rcases hmodels j (T.sample j) (hsample j) with
    ⟨hx, hjx, _hH, _hH', _hE, hE', _hM, _hM'⟩
  have hn' : (n : ℝ) ≤ (D.cellIndex m : ℝ) := by exact_mod_cast hn
  have hmy := (abs_le.mp hmx).1
  have hiy := (abs_le.mp hjy).2
  have hxi := (abs_le.mp hjx).1
  have hnx : (n : ℝ) ≤ x + 3 * L := by
    change -L ≤ x - (D.cellIndex j : ℝ) at hxi
    linarith only [hn', hmy, hiy, hxi]
  have hEpos : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hRef hT j)).2.2.1
  have hpower : materialE0 x ^ P ≤ KE ^ P * T.E0 (T.sample j) ^ P := by
    have h := Real.rpow_le_rpow (materialE0_pos x).le hE' hP
    simpa only [Real.mul_rpow hKEpos.le hEpos.le] using h
  calc
    radialE n ^ R ≤ materialE0 (n : ℝ) ^ R :=
      radialE_rpow_le_materialE0_natCast n hR
    _ ≤ K * materialE0 x ^ P :=
      hshift (n : ℝ) x (Nat.cast_nonneg n) hx hnx
    _ ≤ K * (KE ^ P * T.E0 (T.sample j) ^ P) :=
      mul_le_mul_of_nonneg_left hpower hK.le
    _ = (K * KE ^ P) * T.E0 (T.sample j) ^ P := by ring

end ContinuousFlexibility.Statements
