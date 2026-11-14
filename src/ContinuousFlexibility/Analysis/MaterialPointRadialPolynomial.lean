module

public import ContinuousFlexibility.Analysis.MaterialCellEndpointModels
public import ContinuousFlexibility.Analysis.MaterialSampleRadialPolynomial

/-!
# A discrete radial loss at an actual physical point

The fixed endpoint model and the genuine cell-index error turn every
fixed radial coefficient power into a fixed power of E0 at any point of
that cell. The point is not replaced by the chosen material sample.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem materialCell_radialE_power_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ K P : ℝ, 0 < K ∧ 0 ≤ P ∧ ∀ j r, r ∈ D.cells j →
      radialE (D.cellIndex j) ^ R ≤ K * T.E0 r ^ P := by
  obtain ⟨d0, L, KH, KE, KM, _, hL, _, hKE, _, hmodels⟩ :=
    materialCell_global_endpoint_models hT hRef
  obtain ⟨K, P, hK, hP, hshift⟩ := materialE0_rpow_oneSided_shift hR hL
  have hKEpos : 0 < KE := zero_lt_one.trans_le hKE
  refine ⟨K * KE ^ P, P, mul_pos hK (Real.rpow_pos_of_pos hKEpos _), hP, ?_⟩
  intro j r hr
  let x := endpointX d0 (endpointDistance D r)
  rcases hmodels j r hr with ⟨hx, hdist, _hH, _hH', _hE, hE', _hM, _hM'⟩
  have hn : (D.cellIndex j : ℝ) ≤ x + L := by
    have hd := (abs_le.mp hdist).1
    change -L ≤ x - (D.cellIndex j : ℝ) at hd
    linarith only [hd]
  have hcore : r ∈ radialCore D := hRef.choose_spec.2.1.2.2.2.1 j hr
  have hEpos : 0 < T.E0 r := (hT.2.1 r hcore).2.2.1
  have hpower : materialE0 x ^ P ≤ KE ^ P * T.E0 r ^ P := by
    have h := Real.rpow_le_rpow (materialE0_pos x).le hE' hP
    simpa only [Real.mul_rpow hKEpos.le hEpos.le] using h
  calc
    radialE (D.cellIndex j) ^ R ≤ materialE0 (D.cellIndex j : ℝ) ^ R :=
      radialE_rpow_le_materialE0_natCast _ hR
    _ ≤ K * materialE0 x ^ P :=
      hshift (D.cellIndex j : ℝ) x (Nat.cast_nonneg _) hx hn
    _ ≤ K * (KE ^ P * T.E0 r ^ P) := mul_le_mul_of_nonneg_left hpower hK.le
    _ = (K * KE ^ P) * T.E0 r ^ P := by ring

end ContinuousFlexibility.Statements
