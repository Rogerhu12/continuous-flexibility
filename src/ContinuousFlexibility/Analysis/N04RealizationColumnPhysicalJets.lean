import ContinuousFlexibility.Analysis.N04RealizationLeftColumnTower
import ContinuousFlexibility.Analysis.N04RealizationNuColumnTower
import ContinuousFlexibility.Analysis.N04RealizationHeightFieldJets

/-!
# One neighborhood for both actual physical columns

The left and distinguished columns are the actual fields of the same
supplied nonlinear witness. Their two uniform height towers are
restricted once to a common sector neighborhood and weakened to common
fixed orders. The choice precedes every spatial and parameter order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- Both actual columns have uniform height towers on the same sector
neighborhood. Their decoded equalities hold on the entire physical
plane, so all physical mixed jets are retained as well. -/
theorem n04Realization_exists_uniformPhysicalColumns
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε) :
    ∃ b ell : ℕ, ∃ η : ℝ, base ≤ b ∧ 0 < η ∧ η ≤ ε ∧
      ∃ Nleft Nnu : (StateDirections S × ℝ) → ScalarHeightSpace S,
        FixedNeighborhoodSmoothTame (n07aParameterGrading S) (scalarHeightGrading S)
          (sectorNeighborhood S b η η) b ell Nleft ∧
        FixedNeighborhoodSmoothTame (n07aParameterGrading S) (scalarHeightGrading S)
          (sectorNeighborhood S b η η) b ell Nnu ∧
        (∀ z ∈ sectorNeighborhood S b η η,
          (S.height scalarBeta).decode (Nleft z) =
            n06CurrentLeftColumn S L (liftSectorParameter S C z)) ∧
        (∀ z ∈ sectorNeighborhood S b η η,
          (S.height scalarBeta).decode (Nnu z) =
            nuColumnField D S C (liftSectorParameter S C z)) := by
  obtain ⟨bL, ellL, ηL, hbL, hηL, hηLε, NL, hNL, hdecodeL⟩ :=
    n04Realization_exists_uniformLeftColumn hS hT h01 h03
  obtain ⟨bN, ellN, ηN, _hbN, hηN, _hηNε, NN, hNN, hdecodeN⟩ :=
    n04Realization_exists_uniformNuColumn hS hT h01
  let b : ℕ := max bL bN
  let ell : ℕ := max ellL ellN
  let η : ℝ := min ηL ηN
  have hη : 0 < η := lt_min hηL hηN
  have hUL : sectorNeighborhood S b η η ⊆ sectorNeighborhood S bL ηL ηL :=
    sectorNeighborhood_mono S (le_max_left _ _) (min_le_left _ _) (min_le_left _ _)
  have hUN : sectorNeighborhood S b η η ⊆ sectorNeighborhood S bN ηN ηN :=
    sectorNeighborhood_mono S (le_max_right _ _) (min_le_right _ _) (min_le_right _ _)
  have hU : IsOpen (sectorNeighborhood S b η η) := isOpen_sectorNeighborhood S b η η
  refine ⟨b, ell, η, hbL.trans (le_max_left _ _), hη,
    (min_le_left _ _).trans hηLε, NL, NN, ?_, ?_, ?_, ?_⟩
  · exact (hNL.restrict hU hUL).weaken (n07aParameterGrading_monotone S)
      (le_max_left _ _) (le_max_left _ _)
  · exact (hNN.restrict hU hUN).weaken (n07aParameterGrading_monotone S)
      (le_max_right _ _) (le_max_right _ _)
  · intro z hz
    exact funext (hdecodeL z (hUL hz))
  · intro z hz
    exact funext (hdecodeN z (hUN hz))

end ContinuousFlexibility.Analysis
