import ContinuousFlexibility.Analysis.N01FlowSamplePrefactor
import ContinuousFlexibility.Analysis.MaterialSampleRadialUpper

/-!
# Fixed material loss for the radial collar factor

The actual containing-cell index is controlled by the original N01
hypotheses. An arbitrary fixed power of its radial weight costs one
material order at the control label. Together with the cancelled-height
flow prefactor, the total cost is two orders, independently of the
number of radial or angular derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.control_actual_cell_radialE_rpow_le_M
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ m j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      radialE (D.cellIndex j) ^ R ≤ K * T.M (T.sample m) := by
  obtain ⟨A, hA, hindex⟩ := hN.control_actual_cell_index_bound hS hT
  obtain ⟨K, hK, hbound⟩ :=
    materialSample_radialE_rpow_le_M_of_index_bound hT hN.1.1 hA hR
  exact ⟨K, hK, fun m j hcell => hbound m (D.cellIndex j) (hindex m j hcell)⟩

/-- The exponents may depend on the spatial jet order, while the material
exponent on the right is the literal natural number two. -/
theorem N01Properties.flow_collar_sample_prefactor_le_M_sq
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {R A : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ m j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      radialE (D.cellIndex j) ^ R *
        (T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
          T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ A) ≤ K * T.M (T.sample m) ^ 2 := by
  obtain ⟨KR, hKR, hradial⟩ := hN.control_actual_cell_radialE_rpow_le_M hS hT hR
  obtain ⟨KF, hKF, hflow⟩ := hN.flow_sample_prefactor_le_M hT hA
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hpos (m : ℕ) := hT.2.1 _ (materialSample_mem_radialCore hT hgeom.2.1 m)
  refine ⟨KR * KF, mul_pos hKR hKF, fun m j hcell => ?_⟩
  have hflowpos : 0 ≤ T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ A :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (hpos m).2.1.le _)
      (Real.rpow_nonneg (hpos (C.cell m)).2.1.le _))
      (Real.rpow_nonneg (hpos (C.cell m)).2.2.1.le _)
  have hbound := mul_le_mul (hradial m j hcell) (hflow m) hflowpos
    (mul_nonneg hKR.le (zero_le_one.trans (hpos m).2.2.2))
  exact hbound.trans_eq (by ring)

end ContinuousFlexibility.Statements
