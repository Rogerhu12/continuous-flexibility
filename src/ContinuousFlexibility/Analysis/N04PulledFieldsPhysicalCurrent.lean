import ContinuousFlexibility.Analysis.N04PulledFieldsMovingFamilyOffset
import ContinuousFlexibility.Analysis.N04PulledFieldsInversePointData
import ContinuousFlexibility.Analysis.N04PulledFieldsSampleTransport
import ContinuousFlexibility.Analysis.N04PulledFieldsCurrentData

/-!
# Actual current data from physical prefixes and inverse-point data

The physical derivative is taken at a fixed physical point before that
point is evaluated at the inverse chart. Its prefix may have an offset
depending on the parameter order. The independently constructed inverse
prefix and masked composition then give the actual pulled derivatives.
Integration of the first derivative supplies the full reference difference.
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

/-- A genuine physical mixed tower and its actual joint expansion,
with the physical prefix and independently constructed inverse data,
give the complete current data of the retained pulled field. -/
theorem n04PulledFields_physical_currentData
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε) (hε : ε ≤ 1 / 2)
    (F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ)
    (RF : MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε)
      (annularOpen G.W.D) (fun z => F (G.lift η z)))
    (JF : SmoothDirections
      (sectorNeighborhood (G.S η) base ε ε ×ˢ annularOpen G.W.D)
      (fun x : Parameter (G.S η) × PolarPoint => F (G.lift η x.1) x.2))
    (hexpansion : ∀ n z, z ∈ sectorNeighborhood (G.S η) base ε ε →
      ∀ p (hp : p ∈ annularOpen G.W.D), ∀ v : Fin n → Parameter (G.S η) × PolarPoint,
        JF.D n (z, p) v =
          scalarAngularExpansion n (fun b k => scalarAngularExpansion k
            (fun a j => ((RF.parameter a b p hp).D j z).toMultilinearMap))
            (fun i => (((v i).1, (v i).2.1), (v i).2.2)))
    (hperiodic : ∀ z ∈ sectorNeighborhood (G.S η) base ε ε,
      ∀ p ∈ annularOpen G.W.D,
        F (G.lift η z) (p + (0, Real.pi)) = F (G.lift η z) p)
    (IP : N04PulledFieldsInversePointData G η base ε)
    (hphysical : ∀ K : ℕ, ∃ offset physicalLoss : ℕ, ∀ top : ℕ,
      ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ m z, z ∈ sectorNeighborhood (G.S η) base ε ε →
      ∀ q ∈ unitStrip, ∀ hp : G.pulledPoint η (G.lift η z) m q ∈ annularOpen G.W.D,
      ∀ a b j : ℕ, j ≤ K → a + b ≤ top →
      ∀ u : Fin j → Parameter (G.S η),
        (∀ i, parameterGrading (G.S η) base (u i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → parameterGrading (G.S η) (top + physicalLoss) z ≤ R →
        (∀ i, parameterGrading (G.S η) (top + physicalLoss) (u i) ≤ R) →
        |(RF.parameter a b (G.pulledPoint η (G.lift η z) m q) hp).D j z u| ≤
          C * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ A *
            parameterHeightWeight
              (G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)) j *
            (R ^ (1 / ((top : ℝ) + 1))) ^ (a + b + offset)) :
    G.Data η (fun _ => True) base ε (G.pulled η F) (G.pulledRef η F) := by
  classical
  letI : IsTopologicalAddGroup (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).continuousSMul
  letI : LocallyConvexSpace ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).toLocallyConvexSpace
  have hU := isOpen_sectorNeighborhood (G.S η) base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hc : Convex ℝ (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip) :=
    (sectorNeighborhood_convex (G.S η) base ε ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ)
  have hmap : ∀ m, MapsTo
      (fun x : Parameter (G.S η) × PolarPoint => G.pulledPoint η (G.lift η x.1) m x.2)
      (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip) (annularOpen G.W.D) :=
    fun m => n04PulledFields_pulledPoint_mapsTo G η hadm m
  let RP : ∀ m, MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε) unitStrip
      (fun z => G.pulled η F z m) :=
    fun m => n04Realization_movingPoint_mixedRegularity JF (IP.joint m) (hmap m) hU hΩ hc
  let A : ℕ → Parameter (G.S η) → PolarPoint →
      ∀ a b j : ℕ, Parameter (G.S η) [×j]→L[ℝ] ℝ :=
    fun m z q a b j => if hp : G.pulledPoint η (G.lift η z) m q ∈ annularOpen G.W.D then
      (RF.parameter a b (G.pulledPoint η (G.lift η z) m q) hp).D j z else 0
  have hA (m z q) (hp : G.pulledPoint η (G.lift η z) m q ∈ annularOpen G.W.D)
      (a b j : ℕ) :
      A m z q a b j = (RF.parameter a b (G.pulledPoint η (G.lift η z) m q) hp).D j z := by
    simp only [A, dif_pos hp]
  let physicalOffset : ℕ → ℕ := fun K => (hphysical K).choose
  let physicalLoss : ℕ → ℕ := fun K => (hphysical K).choose_spec.choose
  refine (n04PulledFields_sampleHeight_bounded G).elim fun L hL => ?_
  have hpositive := n04PulledFields_movingFamily_offset_positiveJets
    (f := fun (_m : ℕ) (x : Parameter (G.S η) × PolarPoint) => F (G.lift η x.1) x.2)
    (fun _ => JF) IP.joint hmap hU hΩ hc
    (parameterGrading (G.S η)) (n07aParameterGrading_monotone (G.S η)) base
    (fun m => G.W.U.E0 (G.W.U.sample ((G.V η).cell m)))
    (fun m => G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ))
    (G.cost_nonneg η).2.2 (fun m => Real.rpow_nonneg ((G.cost_nonneg η).2.1 m) _)
    hL.1 (hL.2 η) A
    (fun m z hz q hq n v => by
      have hp := @hmap m (z, q) ⟨hz, hq⟩
      simpa only [hA m z q hp] using
        hexpansion n z hz (G.pulledPoint η (G.lift η z) m q) hp v)
    physicalOffset physicalLoss
    (by
      intro K top
      refine ((hphysical K).choose_spec.choose_spec top).elim fun C hC => ?_
      refine hC.elim fun P hCP => ⟨C, P, hCP.1, hCP.2.1, ?_⟩
      intro m z hz q hq a b j hj hab u hu R hR hzR huR
      have hp := @hmap m (z, q) ⟨hz, hq⟩
      simpa only [hA m z q hp] using
        hCP.2.2 m z hz q hq hp a b j hj hab u hu R hR hzR huR)
    IP.prefix
  refine n04PulledFieldsCurrentData_of_positiveJets hadm.2.1
    (fun _ hz => n04PulledFields_parameterGrading_le_one (G.S η) hε hz)
    (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1 RP
    (fun z hz m _ => (n04PulledFields_spatial_of_physical G η hadm F hz
      (RF.spatial z hz) (hperiodic z hz) m).2)
    (n04PulledFields_pulled_zero G η F) ?_
  intro k hk
  refine (hpositive k hk).elim fun loss hloss => ⟨loss, fun s => ?_⟩
  refine (hloss s).elim fun B hB => ⟨B, hB.1, ?_⟩
  intro z hz v m _ q a b hab
  exact hB.2 m z hz q.val q.property a b hab ((RP m).parameter a b q.val q.property) v

end ContinuousFlexibility.Analysis
