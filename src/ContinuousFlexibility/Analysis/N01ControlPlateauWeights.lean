import ContinuousFlexibility.Analysis.N01ActualCellMaterialOrder
import ContinuousFlexibility.Analysis.MaterialPlateauSampleWeights

/-!
# Moving the complete return-label grading into actual local energy

The fixed loss from the actual mixed-response constraint is combined
with the uniform two-order sample-to-support bound. The complete height
and material weight is therefore controlled at every point in the
expanded component support, with one loss chosen before all orders.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem N01Properties.controlPlateau_weight_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ weightLoss : ℕ, ∀ s : ℕ, ∃ Cs : ℝ, 0 < Cs ∧ ∀ m t,
      t ∈ Icc
        (C.left m - endpointPlateauWidth D (C.left m) (C.right m))
        (C.right m + endpointPlateauWidth D (C.left m) (C.right m)) →
      T.H (T.sample m) ^ (-(3 / 4 : ℝ)) * T.M (T.sample m) ^ s ≤
        Cs * T.H t ^ (-(3 / 4 : ℝ)) * T.M t ^ (s + weightLoss) := by
  obtain ⟨L, hactual⟩ := hN.actualCell_weighted_order_bound hS hT
  obtain ⟨_, _, hcells⟩ := hN.actualCell_travel_lower_bound
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  refine ⟨L + 2, fun s => ?_⟩
  obtain ⟨K1, hK1, hsample⟩ := hactual s
  obtain ⟨K2, hK2, hpoint⟩ := materialCell_plateau_sample_weight_bound hN.1.1 hT
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (s + L)
  refine ⟨K1 * K2, mul_pos hK1 hK2, fun m t ht => ?_⟩
  obtain ⟨_, j, hj, _⟩ := hcells m
  have hp := hpoint j (C.left m) (C.right m)
    (hcontrol.1 m).1 (hcontrol.1 m).2.1 (hcontrol.1 m).2.2 hj t ht
  calc
    _ ≤ K1 * (T.H (T.sample j) ^ (-(3 / 4 : ℝ)) * T.M (T.sample j) ^ (s + L)) :=
      (hsample m j hj).trans_eq (by ring)
    _ ≤ K1 * (K2 * T.H t ^ (-(3 / 4 : ℝ)) * T.M t ^ ((s + L) + 2)) :=
      mul_le_mul_of_nonneg_left hp hK1.le
    _ = _ := by rw [Nat.add_assoc]; ring

end ContinuousFlexibility.Statements
