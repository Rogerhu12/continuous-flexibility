module

public import ContinuousFlexibility.Analysis.MaterialSampleShift
public import ContinuousFlexibility.Analysis.N01ControlIndexBound

/-!
# Actual sample losses at a controlled radial index

Every fixed power of the actual sample weight `E0` is bounded by a
fixed power of the discrete radial weight. Consequently a component
lying in a linearly indexed reference cell incurs only one material
weight at its control label. The comparison uses the actual endpoint
models and does not replace the sample map.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem materialE0_natCast_rpow_eq_radialE (n : ℕ) (P : ℝ) :
    materialE0 (n : ℝ) ^ P = Real.exp P * radialE n ^ P := by
  rw [radialE_rpow_eq_materialE0, ← mul_assoc, ← Real.exp_add]
  simp only [add_neg_cancel, Real.exp_zero, one_mul]

theorem materialSample_E0_rpow_le_radialE
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ K P : ℝ, 0 < K ∧ 0 ≤ P ∧ ∀ j : ℕ,
      T.E0 (T.sample j) ^ R ≤ K * radialE (D.cellIndex j) ^ P := by
  obtain ⟨d0, L, KH, KE, KM, _, hL, _, hKE, _, hmodel⟩ :=
    materialSample_global_endpoint_models hT hRef
  obtain ⟨K, P, hK, hP, hshift⟩ := materialE0_rpow_oneSided_shift hR hL
  have hKE0 : 0 < KE := zero_lt_one.trans_le hKE
  have hRef' := hRef
  obtain ⟨_, hgeom⟩ := hRef'
  have hsample (j : ℕ) : T.sample j ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hgeom.2.1 j
  refine ⟨KE ^ R * K * Real.exp P, P,
    mul_pos (mul_pos (Real.rpow_pos_of_pos hKE0 _) hK) (Real.exp_pos _),
    hP, fun j => ?_⟩
  let x := endpointX d0 (endpointDistance D (T.sample j))
  have hx : 0 ≤ x := (hmodel j).1
  have hxn : x ≤ (D.cellIndex j : ℝ) + L := by
    have h := (abs_le.mp (hmodel j).2.1).2
    change x - (D.cellIndex j : ℝ) ≤ L at h
    linarith only [h]
  have hE : T.E0 (T.sample j) ≤ KE * materialE0 x := (hmodel j).2.2.2.2.1
  have hfirst := Real.rpow_le_rpow (hT.2.1 _ (hsample j)).2.2.1.le hE hR
  rw [Real.mul_rpow hKE0.le (materialE0_pos x).le] at hfirst
  calc
    _ ≤ KE ^ R * materialE0 x ^ R := hfirst
    _ ≤ KE ^ R * (K * materialE0 (D.cellIndex j : ℝ) ^ P) :=
      mul_le_mul_of_nonneg_left
        (hshift x (D.cellIndex j : ℝ) hx (Nat.cast_nonneg _) hxn)
        (Real.rpow_nonneg hKE0.le _)
    _ = _ := by rw [materialE0_natCast_rpow_eq_radialE]; ring

theorem materialSample_E0_rpow_le_M_of_index_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {A R : ℝ} (hA : 0 < A) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ m j : ℕ,
      (D.cellIndex j : ℝ) ≤ A * ((D.cellIndex m : ℝ) + 1) →
      T.E0 (T.sample j) ^ R ≤ K * T.M (T.sample m) := by
  obtain ⟨K0, P, hK0, hP, hsample⟩ := materialSample_E0_rpow_le_radialE hT hRef hR
  obtain ⟨K1, hK1, hradial⟩ :=
    materialSample_radialE_rpow_le_M_of_index_bound hT hRef hA hP
  refine ⟨K0 * K1, mul_pos hK0 hK1, fun m j hj => ?_⟩
  exact (hsample j).trans ((mul_le_mul_of_nonneg_left
    (hradial m (D.cellIndex j) hj) hK0.le).trans_eq (by ring))

/-- This is the comparison needed for the actual coefficient-error
multipliers on a negative component: a fixed loss at any containing
reference cell is absorbed by one material weight at its control label. -/
theorem N01Properties.control_actual_cell_E0_rpow_le_M
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε R : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ m j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      T.E0 (T.sample j) ^ R ≤ K * T.M (T.sample m) := by
  obtain ⟨A, hA, hindex⟩ := hN.control_actual_cell_index_bound hS hT
  obtain ⟨K, hK, hbound⟩ :=
    materialSample_E0_rpow_le_M_of_index_bound hT hN.1.1 hA hR
  exact ⟨K, hK, fun m j hcell => hbound m j (hindex m j hcell)⟩

end ContinuousFlexibility.Statements

