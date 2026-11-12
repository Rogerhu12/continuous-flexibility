import ContinuousFlexibility.Analysis.N04RealizationColumnPhysicalJets
import ContinuousFlexibility.Analysis.N04RealizationHeightFieldPowerBounds

/-!
# Actual physical column prefixes on one common neighborhood

The left and distinguished columns use the actual retained scalar-height
towers. One interpolation base is chosen for both, then both are
restricted to the same sector neighborhood. Every finite spatial and
parameter prefix retains the full physical height gain, ready for the
proved transfer to the same material sample.
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

/-- Both literal physical columns have genuine mixed towers and full
height-weighted finite prefixes on the same neighborhood and at the same
interpolation orders, chosen before either field or either jet order. -/
theorem n04Realization_exists_physicalColumn_powerBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ B outLoss : ℕ, ∃ η : ℝ, base ≤ B ∧ 0 < η ∧ η ≤ ε ∧ η ≤ 1 / 2 ∧
      (∀ z ∈ sectorNeighborhood S B η η, n07aParameterGrading S B z ≤ 1) ∧
      ∀ g : (StateDirections S × ℝ) → PolarPoint → ℝ,
      (g = (fun z => n06CurrentLeftColumn S L (liftSectorParameter S C z)) ∨
        g = (fun z => nuColumnField D S C (liftSectorParameter S C z))) →
      ∃ RF : MixedJetRegularity (sectorNeighborhood S B η η) (annularOpen D) g,
      ∀ K s : ℕ, ∃ C₀ A : ℝ, 1 ≤ C₀ ∧ 0 ≤ A ∧
        ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
        ∀ q ∈ annularOpen D,
        ∀ Jq : SmoothDirections (sectorNeighborhood S B η η)
          (fun z => mixedDerivative a b (g z) q),
        ∀ z ∈ sectorNeighborhood S B η η, n07aParameterGrading S B z ≤ 1 →
        ∀ v : Fin k → (StateDirections S × ℝ),
          (∀ i, n07aParameterGrading S B (v i) ≤ 1) →
        ∀ P : ℝ, 1 ≤ P → n07aParameterGrading S (s + outLoss) z ≤ P →
          (∀ i, n07aParameterGrading S (s + outLoss) (v i) ≤ P) →
          ‖Jq.D k z v‖ ≤ C₀ * T.E0 q.1 ^ A * T.H q.1 ^ (3 / 4 : ℝ) *
            P ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  obtain ⟨b₀, ell₀, η₀, hb₀, hη₀, hη₀ε, NL, NN, hNL, hNN, hleft, hnu⟩ :=
    n04Realization_exists_uniformPhysicalColumns hS hT h01 h03
  have hp : Monotone (n07aParameterGrading S) := n07aParameterGrading_monotone S
  have hIp : HasInterpolation (n07aParameterGrading S) :=
    hasInterpolation_of_hasSmoothing hp
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  obtain ⟨B, outLoss, hB, hbounds⟩ := n04Realization_heightField_spatialPower_choices
    hT (hS.1 scalarBeta) (n07aParameterGrading S) hp hIp b₀ ell₀ hE
  let η : ℝ := min η₀ (1 / 2)
  have hη : 0 < η := lt_min hη₀ (by norm_num)
  have hsub : sectorNeighborhood S B η η ⊆ sectorNeighborhood S b₀ η₀ η₀ :=
    sectorNeighborhood_mono S hB (min_le_left _ _) (min_le_left _ _)
  have hU : IsOpen (sectorNeighborhood S B η η) := isOpen_sectorNeighborhood S B η η
  refine ⟨B, outLoss, η, hb₀.trans hB, hη,
    (min_le_left _ _).trans hη₀ε, min_le_right _ _, ?_, ?_⟩
  · intro z hz
    have hηhalf : η ≤ 1 / 2 := min_le_right _ _
    have hsum : sectorGrading S B z.1 + |z.2| ≤ 1 := by
      linarith [hz.1, hz.2]
    simpa only [n07aParameterGrading, pairGrading_apply, realGrading,
      coe_normSeminorm, Real.norm_eq_abs] using hsum
  · intro g hg
    have hfield : ∃ N : (StateDirections S × ℝ) → ScalarHeightSpace S,
        FixedNeighborhoodSmoothTame (n07aParameterGrading S) (scalarHeightGrading S)
          (sectorNeighborhood S b₀ η₀ η₀) b₀ ell₀ N ∧
        ∀ z ∈ sectorNeighborhood S b₀ η₀ η₀,
          (S.height scalarBeta).decode (N z) = g z := by
      rcases hg with rfl | rfl
      · exact ⟨NL, hNL, hleft⟩
      · exact ⟨NN, hNN, hnu⟩
    obtain ⟨N, hN, hdecode⟩ := hfield
    obtain ⟨J, hJ⟩ := (hN.restrict hU hsub).2
    exact hbounds _ N g J hJ (fun z hz => hdecode z (hsub hz))

/-- The same actual columns and the same parameter neighborhood admit
the exact sampled height gain for every supplied one-sided sample shift.
No cell identity or final coordinate estimate is assumed. -/
theorem n04Realization_exists_physicalColumn_samplePowerBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ B outLoss : ℕ, ∃ η : ℝ, base ≤ B ∧ 0 < η ∧ η ≤ ε ∧ η ≤ 1 / 2 ∧
      (∀ z ∈ sectorNeighborhood S B η η, n07aParameterGrading S B z ≤ 1) ∧
      ∀ g : (StateDirections S × ℝ) → PolarPoint → ℝ,
      (g = (fun z => n06CurrentLeftColumn S L (liftSectorParameter S C z)) ∨
        g = (fun z => nuColumnField D S C (liftSectorParameter S C z))) →
      ∃ RF : MixedJetRegularity (sectorNeighborhood S B η η) (annularOpen D) g,
      ∀ Lshift : ℝ, 0 ≤ Lshift →
      ∀ K s : ℕ, ∃ C₀ A : ℝ, 1 ≤ C₀ ∧ 0 ≤ A ∧
        ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
        ∀ q ∈ annularOpen D, ∀ sample ∈ Ioo D.a D.b,
        endpointX 1 (Statements.endpointDistance D sample) ≤
          endpointX 1 (Statements.endpointDistance D q.1) + Lshift →
        ∀ Jq : SmoothDirections (sectorNeighborhood S B η η)
          (fun z => mixedDerivative a b (g z) q),
        ∀ z ∈ sectorNeighborhood S B η η, n07aParameterGrading S B z ≤ 1 →
        ∀ v : Fin k → (StateDirections S × ℝ),
          (∀ i, n07aParameterGrading S B (v i) ≤ 1) →
        ∀ P : ℝ, 1 ≤ P → n07aParameterGrading S (s + outLoss) z ≤ P →
          (∀ i, n07aParameterGrading S (s + outLoss) (v i) ≤ P) →
          ‖Jq.D k z v‖ ≤ C₀ * T.E0 sample ^ A * T.H sample ^ (3 / 4 : ℝ) *
            P ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  obtain ⟨B, outLoss, η, hB, hη, hηε, hηhalf, hunit, hfields⟩ :=
    n04Realization_exists_physicalColumn_powerBounds hS hT h01 h03 hE
  refine ⟨B, outLoss, η, hB, hη, hηε, hηhalf, hunit, ?_⟩
  intro g hg
  obtain ⟨RF, hb⟩ := hfields g hg
  refine ⟨RF, fun Lshift hLshift => ?_⟩
  exact n04Realization_sample_spatialPower_prefix h01.1.1 hT (by norm_num) hLshift hb

end ContinuousFlexibility.Analysis
