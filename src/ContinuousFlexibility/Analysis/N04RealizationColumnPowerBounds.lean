module

public import ContinuousFlexibility.Analysis.N04RealizationColumnPhysicalJets
public import ContinuousFlexibility.Analysis.N04RealizationHeightFieldPowerBounds

/-!
# Actual physical column prefixes on one common neighborhood

The left and distinguished columns use the actual retained scalar-height
towers. One interpolation base is chosen for both, then both are
restricted to the same sector neighborhood. Every finite spatial and
parameter prefix retains the full physical height gain, ready for the
proved transfer to the same material sample.
-/

@[expose] public section

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

/-- Assemble interpolation and restriction before specializing the state space. -/
private theorem n04Realization_decodedPair_powerAssembly
    {X Y P : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y)
    (V : ℕ → ℝ → Set X) (hopen : ∀ b η, IsOpen (V b η))
    (hmono : ∀ b₀ b₁ η₀ η₁, b₀ ≤ b₁ → η₁ ≤ η₀ → V b₁ η₁ ⊆ V b₀ η₀)
    (hunit : ∀ b η, η ≤ 1 / 2 → ∀ x ∈ V b η, p b x ≤ 1)
    (base : ℕ) (ε : ℝ) (decode : Y → P → ℝ) (left nu : X → P → ℝ)
    {Target : Set X → ℕ → ℕ → (X → P → ℝ) → Prop}
    (hpair : ∃ b ell : ℕ, ∃ η : ℝ, base ≤ b ∧ 0 < η ∧ η ≤ ε ∧
      ∃ NL NN : X → Y, FixedNeighborhoodSmoothTame p q (V b η) b ell NL ∧
        FixedNeighborhoodSmoothTame p q (V b η) b ell NN ∧
        (∀ x ∈ V b η, decode (NL x) = left x) ∧
        (∀ x ∈ V b η, decode (NN x) = nu x))
    (hchoices : ∀ b₀ ell₀ : ℕ, ∃ B outLoss : ℕ, b₀ ≤ B ∧
      ∀ U : Set X, ∀ N : X → Y, ∀ g : X → P → ℝ, ∀ J : SmoothDirections U N,
        UniformScalarTowerEstimate p q U b₀ ell₀ N J →
        (∀ x ∈ U, decode (N x) = g x) → Target U B outLoss g) :
    ∃ B outLoss : ℕ, ∃ η : ℝ, base ≤ B ∧ 0 < η ∧ η ≤ ε ∧ η ≤ 1 / 2 ∧
      (∀ x ∈ V B η, p B x ≤ 1) ∧
      ∀ g : X → P → ℝ, (g = left ∨ g = nu) → Target (V B η) B outLoss g := by
  obtain ⟨b₀, ell₀, η₀, hb₀, hη₀, hη₀ε, NL, NN, hNL, hNN, hleft, hnu⟩ := hpair
  obtain ⟨B, outLoss, hB, hbounds⟩ := hchoices b₀ ell₀
  let η : ℝ := min η₀ (1 / 2)
  have hsub : V B η ⊆ V b₀ η₀ := hmono _ _ _ _ hB (min_le_left _ _)
  refine ⟨B, outLoss, η, hb₀.trans hB, lt_min hη₀ (by norm_num),
    (min_le_left _ _).trans hη₀ε, min_le_right _ _,
    hunit B η (min_le_right _ _), ?_⟩
  intro g hg
  have hfield : ∃ N : X → Y, FixedNeighborhoodSmoothTame p q (V b₀ η₀) b₀ ell₀ N ∧
      ∀ x ∈ V b₀ η₀, decode (N x) = g x := by
    rcases hg with rfl | rfl
    · exact ⟨NL, hNL, hleft⟩
    · exact ⟨NN, hNN, hnu⟩
  obtain ⟨N, hN, hdecode⟩ := hfield
  obtain ⟨J, hJ⟩ := (hN.restrict (hopen B η) hsub).2
  exact hbounds _ N g J hJ (fun x hx => hdecode x (hsub hx))

private theorem n04Realization_powerWitness_map
    {base : ℕ} {ε : ℝ} {unit : ℕ → ℝ → Prop} {P Q : ℕ → ℕ → ℝ → Prop}
    (h : ∃ B outLoss : ℕ, ∃ η : ℝ, base ≤ B ∧ 0 < η ∧ η ≤ ε ∧ η ≤ 1 / 2 ∧
      unit B η ∧ P B outLoss η)
    (hmap : ∀ B outLoss η, P B outLoss η → Q B outLoss η) :
    ∃ B outLoss : ℕ, ∃ η : ℝ, base ≤ B ∧ 0 < η ∧ η ≤ ε ∧ η ≤ 1 / 2 ∧
      unit B η ∧ Q B outLoss η := by
  obtain ⟨B, outLoss, η, hB, hη, hηε, hηhalf, hu, hp⟩ := h
  exact ⟨B, outLoss, η, hB, hη, hηε, hηhalf, hu, hmap B outLoss η hp⟩

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
  have hp : Monotone (n07aParameterGrading S) := n07aParameterGrading_monotone S
  have hIp : HasInterpolation (n07aParameterGrading S) :=
    hasInterpolation_of_hasSmoothing hp
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  refine n04Realization_decodedPair_powerAssembly
    (X := StateDirections S × ℝ) (Y := ScalarHeightSpace S) (P := PolarPoint)
    (n07aParameterGrading S) (scalarHeightGrading S)
    (fun b η => sectorNeighborhood S b η η)
    (fun b η => isOpen_sectorNeighborhood S b η η)
    (fun _ _ _ _ hb hη => sectorNeighborhood_mono S hb hη hη)
    ?_ base ε (S.height scalarBeta).decode
    (fun z => n06CurrentLeftColumn S L (liftSectorParameter S C z))
    (fun z => nuColumnField D S C (liftSectorParameter S C z))
    (n04Realization_exists_uniformPhysicalColumns hS hT h01 h03)
    (fun b₀ ell₀ => n04Realization_heightField_spatialPower_choices
      hT (hS.1 scalarBeta) (n07aParameterGrading S) hp hIp b₀ ell₀ hE)
  intro B η hηhalf z hz
  have hsum : sectorGrading S B z.1 + |z.2| ≤ 1 := by linarith [hz.1, hz.2]
  simpa only [n07aParameterGrading, pairGrading_apply, realGrading,
    coe_normSeminorm, Real.norm_eq_abs] using hsum

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
  refine n04Realization_powerWitness_map
    (n04Realization_exists_physicalColumn_powerBounds hS hT h01 h03 hE) ?_
  intro B outLoss η hfields g hg
  let data := hfields g hg
  refine ⟨data.choose, fun Lshift hLshift => ?_⟩
  exact n04Realization_sample_spatialPower_prefix h01.1.1 hT (by norm_num)
    hLshift data.choose_spec

end ContinuousFlexibility.Analysis
