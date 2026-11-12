import ContinuousFlexibility.Analysis.N01HeightTestWeightBridge
import ContinuousFlexibility.Analysis.N01WeightedActualCellTransfer
import ContinuousFlexibility.Analysis.RadialPlateauNorm

/-!
# Actual one-order material comparison forced by N01

The compact radial primitive direction is constructed in the supplied
physical height model. Its proved grading bound is inserted into the
mixed flow response, so no test-direction or weight-comparison premise
remains in this conclusion.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01ActualCellMaterialOrderStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01ActualCellMaterialOrderRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

open Set

theorem N01Properties.actualCell_balanced_height_constraint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ K A N : ℝ, 0 < K ∧ ∀ m, ∃ j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      1 ≤ K * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ A *
        T.H (T.sample j) ^ (-(3 / 4 : ℝ)) * T.M (T.sample j) ^ N := by
  have hgeom : RadialProfileGeometry D := (Classical.choose_spec hN.1.1).1
  obtain ⟨parameterLoss, hbridge⟩ := hN.balanced_constraint_of_radialHeightTests hS hT
    (referenceRadialPrimitive D) (referenceRadialPrimitive_hasDerivAt hgeom)
  let n := max base (loss + parameterLoss)
  obtain ⟨K, A, R, hK, _, hR, htest⟩ :=
    exists_referencePlateau_heightPair_norm_bound hN.1.1 hT hS n
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  apply hbridge (n := n) (Nat.le_max_left base (loss + parameterLoss))
    (Nat.le_max_right base (loss + parameterLoss))
    (K := K) (A := A) (R := R) hK hR
  intro m j hj
  exact htest j (C.left m) (C.right m)
    (hcontrol.1 m).1 (hcontrol.1 m).2.1 (hcontrol.1 m).2.2 hj

theorem N01Properties.actualCell_material_order_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∀ s : ℕ, ∃ Cs : ℝ, 0 < Cs ∧ ∀ m j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      T.M (T.sample m) ^ s ≤ Cs * T.M (T.sample j) ^ (s + 1) := by
  obtain ⟨K, A, N, hK, hbalanced⟩ := hN.actualCell_balanced_height_constraint hS hT
  exact hN.material_order_transfer_at_every_actualCell hT hK hbalanced

/-- The complete grading weight has one loss chosen independently of
the requested order, uniformly over every actual containing cell. -/
theorem N01Properties.actualCell_weighted_order_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ weightLoss : ℕ, ∀ s : ℕ, ∃ Cs : ℝ, 0 < Cs ∧ ∀ m j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      T.H (T.sample m) ^ (-(3 / 4 : ℝ)) * T.M (T.sample m) ^ s ≤
        Cs * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) *
          T.M (T.sample j) ^ (s + weightLoss) := by
  obtain ⟨K, A, N, hK, hbalanced⟩ := hN.actualCell_balanced_height_constraint hS hT
  exact hN.weighted_order_transfer_at_every_actualCell hT hK hbalanced

end ContinuousFlexibility.Statements
