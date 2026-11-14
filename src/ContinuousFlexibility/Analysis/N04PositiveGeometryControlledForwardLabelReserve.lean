import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledForwardLabelPrefix

/-!
# An arbitrary fixed angular reserve for the actual forward label

The reserve is selected before the low parameter order. The subsequent
parameter prefixes change only the high-order shift. The existing
five-order defect and four-order slope interfaces remain unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

local instance n04ControlledForwardReserveStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The actual forward displacement with any fixed intrinsic reserve. -/
theorem n04PositiveGeometry_rootForwardDefect_fixedBase_reserve_of_flow
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) (reserve : ℕ) :
    N04LabelDefectPrefix (pairGrading (sectorGrading S) realGrading)
      (sectorNeighborhood S base ε ε)
      (fun b side m θ x => iteratedDeriv b (fun α =>
        n01RootLabel S C (liftSectorParameter S C x) m side α - α) θ)
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)) base reserve := by
  exact n04PositiveGeometry_labelDefect_prefix_of_oneHigh
    (pairGrading (sectorGrading S) realGrading) (sectorPairGrading_monotone S)
    (hasInterpolation_of_hasSmoothing (sectorPairGrading_monotone S)
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading))
    (sectorNeighborhood S base ε ε)
    (fun b side m θ x => iteratedDeriv b (fun α =>
      n01RootLabel S C (liftSectorParameter S C x) m side α - α) θ)
    (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
    (fun m => Real.rpow_nonneg ((material_circle_sample_weights_pos hT hN.1.1).2 m).le _)
    base reserve
    (n04PositiveGeometry_rootForwardDefect_fixedBase_oneHigh_of_flow hT hS hN hflow)

/-- The literal slope retains its reference value at parameter order
zero and the full sample height factor at every positive order. -/
theorem n04PositiveGeometry_rootForwardDerivative_fixedBase_reserve_of_flow
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) (reserve : ℕ) :
    N04LabelSlopePrefix (pairGrading (sectorGrading S) realGrading)
      (sectorNeighborhood S base ε ε)
      (fun b side m θ x => iteratedDeriv b
        (deriv (n01RootLabel S C (liftSectorParameter S C x) m side)) θ)
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)) base reserve := by
  let heightData := materialHeight_E0_weight_bounded hT
    (by norm_num : (0 : ℝ) < 3 / 4) 0
  let RH : ℝ := heightData.choose
  have hRH : 0 < RH := heightData.choose_spec.1
  have hheight := heightData.choose_spec.2
  have hHbound (m : ℕ) : T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ RH := by
    simpa only [RH, Real.rpow_zero, mul_one] using
      hheight _ (materialSample_mem_interval hN.1.1 hT m)
  exact n04PositiveGeometry_labelSlope_prefix_of_defect
    (pairGrading (sectorGrading S) realGrading) (sectorNeighborhood S base ε ε)
    (fun b side m θ x => iteratedDeriv b (fun α =>
      n01RootLabel S C (liftSectorParameter S C x) m side α - α) θ)
    (fun b side m θ x => iteratedDeriv b
      (deriv (n01RootLabel S C (liftSectorParameter S C x) m side)) θ)
    (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
    (fun m => Real.rpow_nonneg ((material_circle_sample_weights_pos hT hN.1.1).2 m).le _)
    base reserve hRH hHbound
    (n04PositiveGeometry_rootForwardDefect_angularDirections hT hS hN)
    (fun side m b θ x hx => n04PositiveGeometry_rootForwardDerivative_angular_eq
      hT hS hN hx side m b θ)
    (n04PositiveGeometry_rootForwardDefect_fixedBase_reserve_of_flow
      hT hS hN hflow (reserve + 1))

end ContinuousFlexibility.Analysis
