import ContinuousFlexibility.Analysis.MaterialCellEndpointModels

/-!
# Actual material models throughout the annulus

The partition supplies a genuine cell containing each point. No cell
is reassigned, and no positive component is assumed to lie in one cell.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

/-- All three weights have uniform endpoint models at every core point.
The same model coordinate differs by a fixed amount from `endpointX 1`.
-/
theorem material_global_endpoint_models
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ d0 L KH KE KM : ℝ,
      0 < d0 ∧ 0 ≤ L ∧ 1 ≤ KH ∧ 1 ≤ KE ∧ 1 ≤ KM ∧
      ∀ r ∈ Ioo D.a D.b,
        let x := endpointX d0 (endpointDistance D r)
        0 ≤ x ∧ |x - endpointX 1 (endpointDistance D r)| ≤ L ∧
          T.H r ≤ KH * materialH x ∧ materialH x ≤ KH * T.H r ∧
          T.E0 r ≤ KE * materialE0 x ∧ materialE0 x ≤ KE * T.E0 r ∧
          T.M r ≤ KM * materialM x ∧ materialM x ≤ KM * T.M r := by
  obtain ⟨d0, L, KH, KE, KM, hd0, hL, hKH, hKE, hKM, hmodels⟩ :=
    materialCell_global_endpoint_models hT hRef
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcell⟩ := hdata
  obtain ⟨C, A, hC, hA, hindex⟩ := hcell
  have hpart : RadialPartition D := hRef.choose_spec.2.1
  refine ⟨d0, L + C, KH, KE, KM, hd0, add_nonneg hL hC.le, hKH, hKE, hKM, ?_⟩
  intro r hr
  have hex : ∃ m, D.localizer m r ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hz : (∑' m, D.localizer m r) = 0 := by simp only [hn, tsum_zero]
    have ho := (hpart.2.2.2.2.1 r hr).2
    linarith only [hz, ho]
  obtain ⟨m, hm⟩ := hex
  have hmem : r ∈ D.cells m := hpart.2.2.1 m hm
  obtain ⟨hx, hdist, hH, hH', hE, hE', hM, hM'⟩ := hmodels m r hmem
  refine ⟨hx, ?_, hH, hH', hE, hE', hM, hM'⟩
  exact (abs_sub_le _ (D.cellIndex m : ℝ) _).trans
    (add_le_add hdist (by simpa only [abs_sub_comm] using (hindex m r hmem).1))

/-- A fixed scaling of the actual material coefficient weight is at least
one everywhere. This does not assert the unscaled `E0 ≥ 1`. -/
theorem material_E0_uniform_scaled_lower
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ r ∈ Ioo D.a D.b, 1 ≤ K * T.E0 r := by
  obtain ⟨d0, L, KH, KE, KM, hd0, hL, hKH, hKE, hKM, hmodels⟩ :=
    material_global_endpoint_models hT hRef
  refine ⟨KE, hKE, ?_⟩
  intro r hr
  have h := hmodels r hr
  exact (materialE0_one_le h.1).trans h.2.2.2.2.2.1

end ContinuousFlexibility.Statements
