import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
import ContinuousFlexibility.Analysis.N04RealizationColumnPowerBounds
import ContinuousFlexibility.Analysis.N04RealizationHeightMovingEvaluation
import ContinuousFlexibility.Analysis.N04RealizationMovingPointMixedBounds

/-!
# The physical columns of the retained realization gauge

The two physical columns do not use the auxiliary normalizer.  Their
height-valued towers are constructed with the original physical spaces,
before that normalizer is quantified, and transported by definitional
equality.  The estimates below use the enlarged material envelope of
`CurrentJetDataOn`, including its actual sample height.

This module supplies physical data and the exact moving-evaluation
regularity interface.  Bounds for the inverse point are not assumed to
follow merely from qualitative smoothness.
-/

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

/-- Both actual columns have uniform height-valued towers.  The three
neighborhood choices precede the arbitrary auxiliary normalizer. -/
theorem n04PulledFieldsColumn_uniformHeight (G : N04RealizationGauge) :
    ∃ b ell : ℕ, ∃ δ : ℝ, G.W.base ≤ b ∧ 0 < δ ∧ δ ≤ G.W.ε ∧
      ∀ η : (G.W.S.height (3 / 4 : ℝ)).Space,
      ∀ g : Parameter (G.S η) → PolarPoint → ℝ,
        (g = (fun z => G.leftColumnField η (G.lift η z)) ∨
          g = (fun z => G.nuField η (G.lift η z))) →
        ∃ N : Parameter (G.S η) → ScalarHeightSpace (G.S η),
          FixedNeighborhoodSmoothTame (parameterGrading (G.S η))
            (scalarHeightGrading (G.S η))
            (sectorNeighborhood (G.S η) b δ δ) b ell N ∧
          ∀ z ∈ sectorNeighborhood (G.S η) b δ δ,
            ((G.S η).height scalarBeta).decode (N z) = g z := by
  have hS : IsPhysicalSpaces G.W.D G.W.U G.W.S :=
    isPhysicalSpaces_enlargedMaterialData G.W.hS
  have hT : IsMaterialData G.W.D G.W.U :=
    isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT
  have hN := nonlinearPropertiesThrough03_enlargedMaterialData G.W.hT G.W.through03
  have h := n04Realization_exists_uniformPhysicalColumns hS hT hN.1.1 hN.2
  refine h.elim fun b hb => hb.elim fun ell hell => hell.elim fun δ hδ => ?_
  refine ⟨b, ell, δ, hδ.1, hδ.2.1, hδ.2.2.1, ?_⟩
  intro η g hg
  have hp := hδ.2.2.2
  refine hp.elim fun NL hNL => hNL.elim fun NN hNN => ?_
  exact hg.elim
    (fun hleft => ⟨NL, hNN.1, fun z hz => (hNN.2.2.1 z hz).trans
      (congrFun hleft z).symm⟩)
    (fun hnu => ⟨NN, hNN.2.1, fun z hz => (hNN.2.2.2 z hz).trans
      (congrFun hnu z).symm⟩)

/-- The complete physical column prefixes have the sampled height cost
of the final current-jet interface.  The sample can be the sample of
any piece for which the displayed one-sided comparison is available. -/
theorem n04PulledFieldsColumn_samplePowerBounds (G : N04RealizationGauge) :
    ∃ B outLoss : ℕ, ∃ δ : ℝ,
      G.W.base ≤ B ∧ 0 < δ ∧ δ ≤ G.W.ε ∧ δ ≤ 1 / 2 ∧
      ∀ η : (G.W.S.height (3 / 4 : ℝ)).Space,
      (∀ z ∈ sectorNeighborhood (G.S η) B δ δ,
        parameterGrading (G.S η) B z ≤ 1) ∧
      ∀ g : Parameter (G.S η) → PolarPoint → ℝ,
        (g = (fun z => G.leftColumnField η (G.lift η z)) ∨
          g = (fun z => G.nuField η (G.lift η z))) →
      ∃ RF : MixedJetRegularity (sectorNeighborhood (G.S η) B δ δ)
          (annularOpen G.W.D) g,
        ∀ Lshift : ℝ, 0 ≤ Lshift →
        ∀ K s : ℕ, ∃ C₀ A : ℝ, 1 ≤ C₀ ∧ 0 ≤ A ∧
          ∀ k : ℕ, k ≤ K → ∀ a c : ℕ, a + c ≤ s →
          ∀ q ∈ annularOpen G.W.D, ∀ sample ∈ Ioo G.W.D.a G.W.D.b,
          endpointX 1 (Statements.endpointDistance G.W.D sample) ≤
            endpointX 1 (Statements.endpointDistance G.W.D q.1) + Lshift →
          ∀ Jq : SmoothDirections (sectorNeighborhood (G.S η) B δ δ)
            (fun z => mixedDerivative a c (g z) q),
          ∀ z ∈ sectorNeighborhood (G.S η) B δ δ,
            parameterGrading (G.S η) B z ≤ 1 →
          ∀ v : Fin k → Parameter (G.S η),
            (∀ i, parameterGrading (G.S η) B (v i) ≤ 1) →
          ∀ P : ℝ, 1 ≤ P → parameterGrading (G.S η) (s + outLoss) z ≤ P →
            (∀ i, parameterGrading (G.S η) (s + outLoss) (v i) ≤ P) →
            ‖Jq.D k z v‖ ≤ C₀ * G.W.U.E0 sample ^ A *
              G.W.U.H sample ^ (3 / 4 : ℝ) *
                P ^ (((a + c : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  have hS : IsPhysicalSpaces G.W.D G.W.U G.W.S :=
    isPhysicalSpaces_enlargedMaterialData G.W.hS
  have hT : IsMaterialData G.W.D G.W.U :=
    isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT
  have hN := nonlinearPropertiesThrough03_enlargedMaterialData G.W.hT G.W.through03
  have hE : ∀ r ∈ Ioo G.W.D.a G.W.D.b, 1 ≤ G.W.U.E0 r :=
    fun r _ => (G.W.floor r).trans (le_enlargedMaterialData_E0 G.W.T r)
  have h := n04Realization_exists_physicalColumn_samplePowerBounds hS hT hN.1.1 hN.2 hE
  refine h.elim fun B hB => hB.elim fun outLoss hout => hout.elim fun δ hδ => ?_
  refine ⟨B, outLoss, δ, hδ.1, hδ.2.1, hδ.2.2.1, hδ.2.2.2.1, ?_⟩
  intro η
  exact ⟨hδ.2.2.2.2.1, fun g hg => hδ.2.2.2.2.2 g hg⟩

/-- Periodicity of a decoded scalar-height family is retained by the
actual physical field.  No periodicity is postulated of a proxy. -/
theorem n04PulledFieldsColumn_periodic
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {U : Set (Parameter (G.S η))}
    {N : Parameter (G.S η) → ScalarHeightSpace (G.S η)}
    {g : Parameter (G.S η) → PolarPoint → ℝ}
    (heq : ∀ z ∈ U, ((G.S η).height scalarBeta).decode (N z) = g z)
    {z : Parameter (G.S η)} (hz : z ∈ U) :
    Function.Periodic (g z) (0, Real.pi) := by
  have hperiodic : Function.Periodic
      ((G.W.S.height scalarBeta).decode (N z)) (0, Real.pi) :=
    ((G.W.hS.1 scalarBeta).2.2.2.1 (N z)).2.2.1
  exact (heq z hz) ▸ hperiodic

/-- The exact physical height tower gives the actual joint tower in
state and physical position, for every auxiliary normalizer. -/
def n04PulledFieldsColumn_jointDirections
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {b ell : ℕ} {δ : ℝ}
    {N : Parameter (G.S η) → ScalarHeightSpace (G.S η)}
    {g : Parameter (G.S η) → PolarPoint → ℝ}
    (J : SmoothDirections (sectorNeighborhood (G.S η) b δ δ) N)
    (hJ : UniformScalarTowerEstimate (parameterGrading (G.S η))
      (scalarHeightGrading (G.S η)) (sectorNeighborhood (G.S η) b δ δ) b ell N J)
    (heq : ∀ z ∈ sectorNeighborhood (G.S η) b δ δ,
      ((G.S η).height scalarBeta).decode (N z) = g z) :
    SmoothDirections
      (sectorNeighborhood (G.S η) b δ δ ×ˢ annularOpen G.W.D)
      (fun z : Parameter (G.S η) × PolarPoint => g z.1 z.2) := by
  letI : IsTopologicalAddGroup (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).continuousSMul
  have hT : IsMaterialData G.W.D G.W.U :=
    isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT
  have hM : IsSobolevModel G.W.D G.W.U scalarBeta ((G.S η).height scalarBeta) :=
    (isPhysicalSpaces_enlargedMaterialData G.W.hS).1 scalarBeta
  exact n04Realization_heightFieldJointDirections hT hM (by norm_num [scalarBeta])
    (n07aParameterGrading_monotone (G.S η))
    (n07aParameterGrading_withSeminorms (G.S η)).continuous_seminorm J hJ heq
    (sectorNeighborhood_convex (G.S η) b δ δ)

/-- Composition is with the same inverse-chart point as `G.pulled`.
Every spatial derivative then has its genuine state tower on the
unchanged neighborhood. -/
def n04PulledFieldsColumn_pulledMixedRegularity
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {b : ℕ} {δ : ℝ}
    (F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ) (m : ℕ)
    (JF : SmoothDirections
      (sectorNeighborhood (G.S η) b δ δ ×ˢ annularOpen G.W.D)
      (fun z : Parameter (G.S η) × PolarPoint => F (G.lift η z.1) z.2))
    (Jφ : SmoothDirections (sectorNeighborhood (G.S η) b δ δ ×ˢ unitStrip)
      (fun z : Parameter (G.S η) × PolarPoint => G.pulledPoint η (G.lift η z.1) m z.2))
    (hφ : MapsTo
      (fun z : Parameter (G.S η) × PolarPoint => G.pulledPoint η (G.lift η z.1) m z.2)
      (sectorNeighborhood (G.S η) b δ δ ×ˢ unitStrip) (annularOpen G.W.D)) :
    MixedJetRegularity (sectorNeighborhood (G.S η) b δ δ) unitStrip
      (fun z y => G.pulled η F z m y) := by
  letI : IsTopologicalAddGroup (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).continuousSMul
  letI : LocallyConvexSpace ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).toLocallyConvexSpace
  exact n04Realization_movingPoint_mixedRegularity JF Jφ hφ
    (isOpen_sectorNeighborhood (G.S η) b δ δ) (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex (G.S η) b δ δ).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))

end ContinuousFlexibility.Analysis
