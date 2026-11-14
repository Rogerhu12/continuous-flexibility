module

public import ContinuousFlexibility.Analysis.N04PulledFieldsColumnPhysical
public import ContinuousFlexibility.Analysis.N04RealizationMixedJointDirections

/-!
# Common physical data for the two actual columns

The height-valued and sampled-power constructions initially choose different
neighborhoods. Their intersection is selected before the column. The height
tower is restricted with its original low order and loss. The sharper power
estimate is transferred from its original physical tower by uniqueness of
genuine derivatives on the smaller open neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

/-- Sampled physical bounds, with the state smallness already supplied
by the chosen common neighborhood. The endpoint shift remains explicit. -/
def N04PulledFieldsColumnSamplePower
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (base outLoss : ℕ) (ε : ℝ)
    (F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ)
    (RF : MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε)
      (annularOpen G.W.D) (fun z => F (G.lift η z))) : Prop :=
  ∀ Lshift : ℝ, 0 ≤ Lshift → ∀ K s : ℕ,
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ k : ℕ, k ≤ K → ∀ a c : ℕ, a + c ≤ s →
      ∀ q (hq : q ∈ annularOpen G.W.D),
      ∀ sample ∈ Ioo G.W.D.a G.W.D.b,
      endpointX 1 (Statements.endpointDistance G.W.D sample) ≤
        endpointX 1 (Statements.endpointDistance G.W.D q.1) + Lshift →
      ∀ z ∈ sectorNeighborhood (G.S η) base ε ε,
      ∀ v : Fin k → Parameter (G.S η),
        (∀ i, parameterGrading (G.S η) base (v i) ≤ 1) →
      ∀ P : ℝ, 1 ≤ P → parameterGrading (G.S η) (s + outLoss) z ≤ P →
        (∀ i, parameterGrading (G.S η) (s + outLoss) (v i) ≤ P) →
        ‖(RF.parameter a c q hq).D k z v‖ ≤
          C * G.W.U.E0 sample ^ A * G.W.U.H sample ^ (3 / 4 : ℝ) *
            P ^ (((a + c : ℕ) : ℝ) / ((s : ℝ) + 1))

/-- Actual mixed and joint towers, including their exact compatibility
and the sampled physical estimate on one common neighborhood. -/
structure N04PulledFieldsColumnData
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (base outLoss : ℕ) (ε : ℝ)
    (F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ) where
  mixed : MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε)
    (annularOpen G.W.D) (fun z => F (G.lift η z))
  joint : SmoothDirections
    (sectorNeighborhood (G.S η) base ε ε ×ˢ annularOpen G.W.D)
    (fun z : Parameter (G.S η) × PolarPoint => F (G.lift η z.1) z.2)
  uniformSeminorm : ∀ a c, UniformScalarJetSeminormBounds
    (fun q : annularOpen G.W.D => mixed.parameter a c q q.property)
  expansion : ∀ n : ℕ, ∀ z : Parameter (G.S η),
    ∀ q (hq : q ∈ annularOpen G.W.D), ∀ v : Fin n → Parameter (G.S η) × PolarPoint,
      joint.D n (z, q) v =
        scalarAngularExpansion n (fun c k => scalarAngularExpansion k
          (fun a j => ((mixed.parameter a c q hq).D j z).toMultilinearMap))
          (fun i => (((v i).1, (v i).2.1), (v i).2.2))
  periodic : ∀ z ∈ sectorNeighborhood (G.S η) base ε ε,
    Function.Periodic (F (G.lift η z)) (0, Real.pi)
  power : N04PulledFieldsColumnSamplePower G η base outLoss ε F mixed

/-- The qualitative physical construction keeps the original height
estimate's low order, even when the state domain has been restricted. -/
private def n04PulledFieldsColumn_dataOfHeight
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base baseHeight ell outLoss : ℕ} {ε : ℝ}
    (F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ)
    {N : Parameter (G.S η) → ScalarHeightSpace (G.S η)}
    (hN : FixedNeighborhoodSmoothTame (parameterGrading (G.S η))
      (scalarHeightGrading (G.S η)) (sectorNeighborhood (G.S η) base ε ε)
      baseHeight ell N)
    (heq : ∀ z ∈ sectorNeighborhood (G.S η) base ε ε,
      ((G.S η).height scalarBeta).decode (N z) = F (G.lift η z))
    (hpower : ∀ RF : MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε)
        (annularOpen G.W.D) (fun z => F (G.lift η z)),
      N04PulledFieldsColumnSamplePower G η base outLoss ε F RF) :
    N04PulledFieldsColumnData G η base outLoss ε F := by
  letI : IsTopologicalAddGroup (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).continuousSMul
  have hT : IsMaterialData G.W.D G.W.U :=
    isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT
  have hM : IsSobolevModel G.W.D G.W.U scalarBeta ((G.S η).height scalarBeta) :=
    (isPhysicalSpaces_enlargedMaterialData G.W.hS).1 scalarBeta
  let J : SmoothDirections (sectorNeighborhood (G.S η) base ε ε) N := hN.2.choose
  have hJ : UniformScalarTowerEstimate (parameterGrading (G.S η))
      (scalarHeightGrading (G.S η)) (sectorNeighborhood (G.S η) base ε ε)
      baseHeight ell N J := hN.2.choose_spec
  let RF : MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε)
      (annularOpen G.W.D) (fun z => F (G.lift η z)) :=
    n04Realization_heightFieldMixedJets hT hM J heq
  have hb : ∀ a c, UniformScalarJetSeminormBounds
      (fun q : annularOpen G.W.D => RF.parameter a c q q.property) :=
    n04Realization_heightField_uniformSeminormBounds hT hM (by norm_num [scalarBeta])
      (n07aParameterGrading_monotone (G.S η))
      (n07aParameterGrading_withSeminorms (G.S η)).continuous_seminorm J hJ heq
  let JF : SmoothDirections
      (sectorNeighborhood (G.S η) base ε ε ×ˢ annularOpen G.W.D)
      (fun z : Parameter (G.S η) × PolarPoint => F (G.lift η z.1) z.2) :=
    n04Realization_mixedJointDirections RF
      (isOpen_sectorNeighborhood (G.S η) base ε ε)
      (sectorNeighborhood_convex (G.S η) base ε ε) isOpen_Ioo
      (convex_Ioo G.W.D.a G.W.D.b) hb
  exact {
    mixed := RF
    joint := JF
    uniformSeminorm := hb
    expansion := n04Realization_mixedJointDirections_expansion RF
      (isOpen_sectorNeighborhood (G.S η) base ε ε)
      (sectorNeighborhood_convex (G.S η) base ε ε) isOpen_Ioo
      (convex_Ioo G.W.D.a G.W.D.b) hb
    periodic := fun z hz => n04PulledFieldsColumn_periodic G η heq hz
    power := hpower RF }

/-- One smaller neighborhood supports both actual physical columns.
The base, loss and radius are selected before choosing either column. -/
theorem n04PulledFieldsColumn_commonPhysicalData
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε) :
    ∃ base' outLoss : ℕ, ∃ ε' : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ,
        (F = G.leftColumnField η ∨ F = G.nuField η) →
        Nonempty (N04PulledFieldsColumnData G η base' outLoss ε' F) := by
  letI : IsTopologicalAddGroup (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).continuousSMul
  refine (n04PulledFieldsColumn_samplePowerBounds G).elim fun B0 hB0 => ?_
  refine hB0.elim fun outLoss hout => hout.elim fun δ0 hδ0 => ?_
  refine (n04PulledFieldsColumn_uniformHeight G).elim fun b1 hb1 => ?_
  refine hb1.elim fun ell1 hell1 => hell1.elim fun δ1 hδ1 => ?_
  let base' : ℕ := max base (max B0 b1)
  let ε' : ℝ := min ε (min δ0 δ1)
  have hbase : base ≤ base' := le_max_left _ _
  have hB0 : B0 ≤ base' := (le_max_left B0 b1).trans (le_max_right _ _)
  have hb1 : b1 ≤ base' := (le_max_right B0 b1).trans (le_max_right _ _)
  have hε' : 0 < ε' := lt_min hadm.2.1 (lt_min hδ0.2.1 hδ1.2.1)
  have hεε : ε' ≤ ε := min_le_left _ _
  have hε0 : ε' ≤ δ0 := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε' ≤ δ1 := (min_le_right _ _).trans (min_le_right _ _)
  have hsub0 : sectorNeighborhood (G.S η) base' ε' ε' ⊆
      sectorNeighborhood (G.S η) B0 δ0 δ0 :=
    sectorNeighborhood_mono (G.S η) hB0 hε0 hε0
  have hsub1 : sectorNeighborhood (G.S η) base' ε' ε' ⊆
      sectorNeighborhood (G.S η) b1 δ1 δ1 :=
    sectorNeighborhood_mono (G.S η) hb1 hε1 hε1
  have hU : IsOpen (sectorNeighborhood (G.S η) base' ε' ε') :=
    isOpen_sectorNeighborhood (G.S η) base' ε' ε'
  refine ⟨base', outLoss, ε', hbase, hε', hεε, ?_⟩
  intro F hF
  have hfield :
      (fun z => F (G.lift η z)) = (fun z => G.leftColumnField η (G.lift η z)) ∨
      (fun z => F (G.lift η z)) = (fun z => G.nuField η (G.lift η z)) :=
    hF.elim
      (fun h => Or.inl (congrArg (fun f z => f (G.lift η z)) h))
      (fun h => Or.inr (congrArg (fun f z => f (G.lift η z)) h))
  have hsource := (hδ0.2.2.2.2 η).2 (fun z => F (G.lift η z)) hfield
  refine hsource.elim fun RF0 hRF0 => ?_
  refine (hδ1.2.2.2 η (fun z => F (G.lift η z)) hfield).elim fun N hN => ?_
  refine ⟨n04PulledFieldsColumn_dataOfHeight G η F (hN.1.restrict hU hsub1)
    (fun z hz => hN.2 z (hsub1 hz)) ?_⟩
  intro RF Lshift hLshift K s
  refine (hRF0 Lshift hLshift K s).elim fun C hC => hC.elim fun A hCA => ?_
  refine ⟨C, A, hCA.1, hCA.2.1, ?_⟩
  intro k hk a c hac q hq sample hsample hshift z hz v hv P hP hzP hvP
  have hD : (RF.parameter a c q hq).D k z v =
      (RF0.parameter a c q hq).D k z v :=
    congrArg (fun T : Parameter (G.S η) [×k]→L[ℝ] ℝ => T v)
      ((RF.parameter a c q hq).unique
        ((RF0.parameter a c q hq).restrict hU hsub0) k z hz)
  rw [hD]
  exact hCA.2.2 k hk a c hac q hq sample hsample hshift (RF0.parameter a c q hq)
    z (hsub0 hz) ((hδ0.2.2.2.2 η).1 z (hsub0 hz)) v
    (fun i => ((n07aParameterGrading_monotone (G.S η) hB0) (v i)).trans (hv i))
    P hP hzP hvP

end ContinuousFlexibility.Analysis
