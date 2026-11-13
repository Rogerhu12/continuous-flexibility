import ContinuousFlexibility.Analysis.N04PulledFieldsColumnTransport
import ContinuousFlexibility.Analysis.N04PulledFieldsMovingFamily
import ContinuousFlexibility.Analysis.N04PulledFieldsCurrentData

/-!
# Current data of the actual pulled physical columns

The physical mixed jets are evaluated at the retained inverse point.
Its pure-word prefix and the physical sampled prefix give the positive
parameter jets by masked composition. Integrating the genuine first
parameter jet supplies the reference difference and its value bound.
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

/-- A genuine inverse-point prefix and the constructed physical column
data yield the full current interface on their common neighborhood. -/
theorem n04PulledFieldsColumn_currentData_of_inversePrefix
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base outLoss : ℕ} {ε : ℝ} (hadm : G.Admissible base ε) (hε : ε ≤ 1 / 2)
    (F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ)
    (D : N04PulledFieldsColumnData G η base outLoss ε F)
    (Jφ : ∀ m, SmoothDirections (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip)
      (fun z : Parameter (G.S η) × PolarPoint =>
        G.pulledPoint η (G.lift η z.1) m z.2))
    (hinverse : ∀ K : ℕ, ∃ offset : ℕ, ∀ N : ℕ,
      ∃ M A : ℝ, 1 ≤ M ∧ 0 ≤ A ∧
      ∀ m z, z ∈ sectorNeighborhood (G.S η) base ε ε →
      ∀ q ∈ unitStrip, ∀ R : ℝ, 1 ≤ R →
      parameterGrading (G.S η) (base + N + offset + 1) z ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → Parameter (G.S η) × PolarPoint,
      (∀ i, parameterGrading (G.S η) base (v i).1 ≤ 1) →
      (∀ i, parameterGrading (G.S η) (base + N + offset + 1) (v i).1 ≤ R) →
      (∀ i, ‖(v i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (v i).1 = 0) →
      (∀ i, w.isState i = true → (v i).2 = 0) →
        ‖(Jφ m).D n (z, q) v‖ ≤
          M * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ A *
            parameterHeightWeight
              (G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)) w.stateArity *
            (R ^ (1 / (((N + offset : ℕ) : ℝ) + 1))) ^
              (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset)) :
    G.Data η (fun _ => True) base ε (G.pulled η F) (G.pulledRef η F) := by
  letI : IsTopologicalAddGroup (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).continuousSMul
  letI : LocallyConvexSpace ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).toLocallyConvexSpace
  have hmap : ∀ m, MapsTo
      (fun z : Parameter (G.S η) × PolarPoint => G.pulledPoint η (G.lift η z.1) m z.2)
      (sectorNeighborhood (G.S η) base ε ε ×ˢ unitStrip) (annularOpen G.W.D) :=
    fun m => n04PulledFields_pulledPoint_mapsTo G η hadm m
  let RF : ∀ m, MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε) unitStrip
      (fun z => G.pulled η F z m) :=
    fun m => n04PulledFieldsColumn_pulledMixedRegularity G η F m D.joint (Jφ m) (hmap m)
  refine (n04PulledFields_sampleHeight_bounded G).elim fun L hL => ?_
  have hpositive := n04PulledFields_movingFamily_positiveJets
    (f := fun (_m : ℕ) (z : Parameter (G.S η) × PolarPoint) => F (G.lift η z.1) z.2)
    (fun _ => D.joint) Jφ hmap (isOpen_sectorNeighborhood (G.S η) base ε ε)
    (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex (G.S η) base ε ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))
    (parameterGrading (G.S η)) (n07aParameterGrading_monotone (G.S η)) base
    (fun m => G.W.U.E0 (G.W.U.sample ((G.V η).cell m)))
    (fun m => G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ))
    (G.cost_nonneg η).2.2 (fun m => Real.rpow_nonneg ((G.cost_nonneg η).2.1 m) _)
    hL.1 (hL.2 η)
    (fun m z q => D.physicalJetAt z (G.pulledPoint η (G.lift η z) m q))
    (fun m z hz q hq n v => D.pulledPoint_expansion hadm m z hz q hq n v)
    (fun _ => outLoss) (fun K top => D.pulledPoint_power hadm hL.1 (hL.2 η) K top)
    hinverse
  refine n04PulledFieldsCurrentData_of_positiveJets hadm.2.1
    (fun _ hz => n04PulledFields_parameterGrading_le_one (G.S η) hε hz)
    (G.cost_nonneg η).2.2 (G.cost_nonneg η).2.1 RF
    (fun z hz m _ => (n04PulledFields_spatial_of_physical G η hadm F hz
      (D.mixed.spatial z hz) (fun p _ => D.periodic z hz p) m).2)
    (n04PulledFields_pulled_zero G η F) ?_
  intro k hk
  refine (hpositive k hk).elim fun loss hloss => ⟨loss, fun s => ?_⟩
  refine (hloss s).elim fun B hB => ⟨B, hB.1, ?_⟩
  intro z hz v m _ q a c hac
  exact hB.2 m z hz q.val q.property a c hac ((RF m).parameter a c q.val q.property) v

end ContinuousFlexibility.Analysis
