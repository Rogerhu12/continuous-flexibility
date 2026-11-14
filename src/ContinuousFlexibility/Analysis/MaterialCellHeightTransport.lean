module

public import ContinuousFlexibility.Analysis.MaterialCellEndpointModels

/-!
# Actual height weights between points of one material cell

A map that stays inside the same physical cell has a uniform height
ratio bound in the requested coefficient envelope. The comparison uses
physical evaluation points, not an arbitrary reassignment of cell labels.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

/-- The exact height exponent is retained between any two actual points
of the same cell. All constants precede the cell and both points. -/
theorem materialCell_H_E0_rpow_same_cell
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (γ : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ m r s,
      r ∈ D.cells m → s ∈ D.cells m →
      T.H r ^ γ * T.E0 r ^ R ≤ K * T.H s ^ γ * T.E0 s ^ A := by
  obtain ⟨d0, L, KH, KE, KM, _, hL, hKH, hKE, _, hmodel⟩ :=
    materialCell_global_endpoint_models hT hRef
  let X : ℝ → ℝ := fun r => endpointX d0 (endpointDistance D r)
  have hKH0 : 0 < KH := zero_lt_one.trans_le hKH
  have hKE0 : 0 < KE := zero_lt_one.trans_le hKE
  have hpositive (m : ℕ) {r : ℝ} (hr : r ∈ D.cells m) :=
    hT.2.1 r (hRef.choose_spec.2.1.2.2.2.1 m hr)
  obtain ⟨K, A, hK, hA, hshift⟩ := materialH_E0_rpow_bounded_shift γ hR
    (show 0 ≤ 2 * L by positivity)
  let KF := KH ^ |γ| * KE ^ R
  let KG := KH ^ |γ| * KE ^ A
  have hKF : 0 < KF := mul_pos (Real.rpow_pos_of_pos hKH0 _) (Real.rpow_pos_of_pos hKE0 _)
  have hKG : 0 < KG := mul_pos (Real.rpow_pos_of_pos hKH0 _) (Real.rpow_pos_of_pos hKE0 _)
  refine ⟨KF * K * KG, A, mul_pos (mul_pos hKF hK) hKG, hA, ?_⟩
  intro m r s hr hs
  rcases hmodel m r hr with ⟨hxr, hdr, hHr, hHr', hEr, hEr', _⟩
  rcases hmodel m s hs with ⟨hxs, hds, hHs, hHs', hEs, hEs', _⟩
  have hdist : |X r - X s| ≤ 2 * L := by
    have hd := abs_sub_le (X r) (D.cellIndex m : ℝ) (X s)
    have hrev : |(D.cellIndex m : ℝ) - X s| ≤ L := by
      rw [abs_sub_comm]
      exact hds
    exact hd.trans ((add_le_add hdr hrev).trans_eq (by ring))
  have hHrγ := rpow_le_mul_rpow_of_twoSided (hpositive m hr).2.1 (materialH_pos (X r))
    hKH0 hHr hHr' γ
  have hErR := Real.rpow_le_rpow (hpositive m hr).2.2.1.le hEr hR
  rw [Real.mul_rpow hKE0.le (materialE0_pos (X r)).le] at hErR
  have hHsγ := rpow_le_mul_rpow_of_twoSided (materialH_pos (X s)) (hpositive m hs).2.1
    hKH0 hHs' hHs γ
  have hEsA := Real.rpow_le_rpow (materialE0_pos (X s)).le hEs' hA
  rw [Real.mul_rpow hKE0.le (hpositive m hs).2.2.1.le] at hEsA
  have hfirst : T.H r ^ γ * T.E0 r ^ R ≤
      KF * (materialH (X r) ^ γ * materialE0 (X r) ^ R) := by
    have h := mul_le_mul hHrγ hErR (Real.rpow_nonneg (hpositive m hr).2.2.1.le R)
      (mul_nonneg (Real.rpow_nonneg hKH0.le _) (Real.rpow_nonneg (materialH_pos (X r)).le γ))
    exact h.trans_eq (by dsimp only [KF]; ring)
  have hlast : materialH (X s) ^ γ * materialE0 (X s) ^ A ≤
      KG * (T.H s ^ γ * T.E0 s ^ A) := by
    have h := mul_le_mul hHsγ hEsA (Real.rpow_nonneg (materialE0_pos (X s)).le A)
      (mul_nonneg (Real.rpow_nonneg hKH0.le _) (Real.rpow_nonneg (hpositive m hs).2.1.le γ))
    exact h.trans_eq (by dsimp only [KG]; ring)
  calc
    _ ≤ KF * (materialH (X r) ^ γ * materialE0 (X r) ^ R) := hfirst
    _ ≤ KF * (K * (materialH (X s) ^ γ * materialE0 (X s) ^ A)) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [mul_assoc] using hshift (X r) (X s) hxr hxs hdist) hKF.le
    _ ≤ KF * (K * (KG * (T.H s ^ γ * T.E0 s ^ A))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlast hK.le) hKF.le
    _ = _ := by ring

/-- This is the height-ratio clause used by a genuine transport whose
source and image lie in one actual material cell. -/
theorem materialCell_height_ratio
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ m r s,
      r ∈ D.cells m → s ∈ D.cells m →
      T.H r / T.H s ≤ K * T.E0 s ^ A := by
  obtain ⟨K, A, hK, hA, hb⟩ := materialCell_H_E0_rpow_same_cell hT hRef 1
    (R := 0) le_rfl
  refine ⟨K, A, hK, hA, ?_⟩
  intro m r s hr hs
  have hp : 0 < T.H s := (hT.2.1 s (hRef.choose_spec.2.1.2.2.2.1 m hs)).2.1
  apply (div_le_iff₀ hp).mpr
  have h := hb m r s hr hs
  simpa only [Real.rpow_one, Real.rpow_zero, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using h

/-- The coefficient envelope itself can be moved to the physical source
point; no uniform lower bound of E0 by one is needed. -/
theorem materialCell_E0_rpow_same_cell
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ m r s,
      r ∈ D.cells m → s ∈ D.cells m → T.E0 r ^ R ≤ K * T.E0 s ^ A := by
  obtain ⟨K, A, hK, hA, hb⟩ := materialCell_H_E0_rpow_same_cell hT hRef 0 hR
  refine ⟨K, A, hK, hA, ?_⟩
  intro m r s hr hs
  simpa only [Real.rpow_zero, one_mul, mul_one] using hb m r s hr hs

end ContinuousFlexibility.Statements
