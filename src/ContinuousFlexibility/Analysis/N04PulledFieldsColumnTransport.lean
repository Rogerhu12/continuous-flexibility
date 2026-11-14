module

public import ContinuousFlexibility.Analysis.N04PulledFieldsColumnData
public import ContinuousFlexibility.Analysis.N04PulledFieldsSampleTransport
public import ContinuousFlexibility.Analysis.N04PulledFieldsSampleCost
public import ContinuousFlexibility.Analysis.N04PulledFieldsCompositionCost

/-!
# Physical column data at the actual moving inverse point

Restriction preserves the original physical loss. The exact mixed jets
are evaluated at the retained inverse-chart point, whose same-piece
sample comparison supplies the common sampled material weight.
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

namespace N04PulledFieldsColumnData

variable {G : N04RealizationGauge} {η : (G.W.S.height (3 / 4 : ℝ)).Space}
  {base outLoss : ℕ} {ε : ℝ}
  {F : AnnularState (G.S η) × ℝ → PolarPoint → ℝ}

/-- A stronger low order and a smaller radius keep the same genuine
jets and the same physical high-order loss. -/
def restrict (D : N04PulledFieldsColumnData G η base outLoss ε F)
    {base' : ℕ} {ε' : ℝ} (hb : base ≤ base') (hε : ε' ≤ ε) :
    N04PulledFieldsColumnData G η base' outLoss ε' F := by
  letI : IsTopologicalAddGroup (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter (G.S η)) :=
    (n07aParameterGrading_withSeminorms (G.S η)).continuousSMul
  have hU := isOpen_sectorNeighborhood (G.S η) base' ε' ε'
  have hsub : sectorNeighborhood (G.S η) base' ε' ε' ⊆
      sectorNeighborhood (G.S η) base ε ε := sectorNeighborhood_mono (G.S η) hb hε hε
  let RF : MixedJetRegularity (sectorNeighborhood (G.S η) base' ε' ε')
      (annularOpen G.W.D) (fun z => F (G.lift η z)) :=
    ⟨fun z hz => D.mixed.spatial z (hsub hz),
      fun a c q hq => (D.mixed.parameter a c q hq).restrict hU hsub⟩
  let JF : SmoothDirections
      (sectorNeighborhood (G.S η) base' ε' ε' ×ˢ annularOpen G.W.D)
      (fun z : Parameter (G.S η) × PolarPoint => F (G.lift η z.1) z.2) :=
    D.joint.restrict (hU.prod (isOpen_Ioo.prod isOpen_univ))
      (fun _ hz => ⟨hsub hz.1, hz.2⟩)
  refine {
    mixed := RF
    joint := JF
    uniformSeminorm := ?_
    expansion := ?_
    periodic := fun z hz => D.periodic z (hsub hz)
    power := ?_
  }
  · intro a c n
    refine (D.uniformSeminorm a c n).elim fun p hp => hp.elim fun B hB => ?_
    exact ⟨p, B, hB.1, hB.2.1, fun q z hz v => hB.2.2 q z (hsub hz) v⟩
  · exact D.expansion
  · intro Lshift hLshift K s
    refine (D.power Lshift hLshift K s).elim fun C hC => hC.elim fun A hCA => ?_
    refine ⟨C, A, hCA.1, hCA.2.1, ?_⟩
    intro k hk a c hac q hq sample hsample hshift z hz v hv P hP hzP hvP
    exact hCA.2.2 k hk a c hac q hq sample hsample hshift z (hsub hz) v
      (fun i => (n07aParameterGrading_monotone (G.S η) hb (v i)).trans (hv i))
      P hP hzP hvP

/-- The mixed physical jet, extended by zero only outside its physical
domain so that the moving-family formula has a total coefficient family. -/
def physicalJetAt (D : N04PulledFieldsColumnData G η base outLoss ε F)
    (z : Parameter (G.S η)) (q : PolarPoint) (a c k : ℕ) :
    Parameter (G.S η) [×k]→L[ℝ] ℝ := by
  classical
  exact if hq : q ∈ annularOpen G.W.D then (D.mixed.parameter a c q hq).D k z else 0

theorem physicalJetAt_of_mem (D : N04PulledFieldsColumnData G η base outLoss ε F)
    (z : Parameter (G.S η)) {q : PolarPoint} (hq : q ∈ annularOpen G.W.D)
    (a c k : ℕ) :
    D.physicalJetAt z q a c k = (D.mixed.parameter a c q hq).D k z := by
  simp only [physicalJetAt, dif_pos hq]

/-- The joint tower expands in exactly the mixed physical jets evaluated
at the retained inverse point. -/
theorem pulledPoint_expansion (D : N04PulledFieldsColumnData G η base outLoss ε F)
    (hadm : G.Admissible base ε) (m : ℕ)
    (z : Parameter (G.S η)) (hz : z ∈ sectorNeighborhood (G.S η) base ε ε)
    (q : PolarPoint) (hq : q ∈ unitStrip) (n : ℕ)
    (v : Fin n → Parameter (G.S η) × PolarPoint) :
    D.joint.D n (z, G.pulledPoint η (G.lift η z) m q) v =
      scalarAngularExpansion n (fun c k => scalarAngularExpansion k
        (fun a j => (D.physicalJetAt z
          (G.pulledPoint η (G.lift η z) m q) a c j).toMultilinearMap))
        (fun i => (((v i).1, (v i).2.1), (v i).2.2)) := by
  have hmap := n04PulledFields_pulledPoint_mapsTo G η hadm m
  have hp : G.pulledPoint η (G.lift η z) m q ∈ annularOpen G.W.D :=
    @hmap (z, q) ⟨hz, hq⟩
  simpa only [physicalJetAt_of_mem D z hp] using
    D.expansion n z (G.pulledPoint η (G.lift η z) m q) hp v

/-- The original physical sample estimate is precisely the raw prefix
needed for moving-point composition. The full height factor is retained
at positive parameter order; its uniform bound handles order zero. -/
theorem pulledPoint_power (D : N04PulledFieldsColumnData G η base outLoss ε F)
    (hadm : G.Admissible base ε)
    {L : ℝ} (hL : 1 ≤ L)
    (hHL : ∀ m, G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) ≤ L)
    (K top : ℕ) :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ m z, z ∈ sectorNeighborhood (G.S η) base ε ε →
      ∀ q ∈ unitStrip, ∀ a c k : ℕ, k ≤ K → a + c ≤ top →
      ∀ v : Fin k → Parameter (G.S η),
        (∀ i, parameterGrading (G.S η) base (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → parameterGrading (G.S η) (top + outLoss) z ≤ R →
        (∀ i, parameterGrading (G.S η) (top + outLoss) (v i) ≤ R) →
        |D.physicalJetAt z (G.pulledPoint η (G.lift η z) m q) a c k v| ≤
          C * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ A *
            parameterHeightWeight
              (G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ)) k *
            (R ^ (1 / ((top : ℝ) + 1))) ^ (a + c) := by
  refine (n04PulledFields_pulledPoint_sample_endpointX G hadm).elim fun Lshift hshift => ?_
  refine (D.power Lshift hshift.1 K top).elim fun C hC => hC.elim fun A hCA => ?_
  have hCL : 1 ≤ C * L := by
    simpa only [one_mul] using mul_le_mul hCA.1 hL zero_le_one (zero_le_one.trans hCA.1)
  refine ⟨C * L, A, hCL, hCA.2.1, ?_⟩
  intro m z hz q hq a c k hk hac v hv R hR hzR hvR
  have hmap := n04PulledFields_pulledPoint_mapsTo G η hadm m
  have hp : G.pulledPoint η (G.lift η z) m q ∈ annularOpen G.W.D :=
    @hmap (z, q) ⟨hz, hq⟩
  have hraw := hCA.2.2 k hk a c hac (G.pulledPoint η (G.lift η z) m q) hp
    (G.W.U.sample ((G.V η).cell m)) (n04PulledFields_sample_mem_interval G η m)
    (hshift.2 η z hz m q hq).2 z hz v hv R hR hzR hvR
  have hpower : R ^ (((a + c : ℕ) : ℝ) / ((top : ℝ) + 1)) =
      (R ^ (1 / ((top : ℝ) + 1))) ^ (a + c) := by
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hR)]
    congr 1
    ring
  have hraw' : |D.physicalJetAt z (G.pulledPoint η (G.lift η z) m q) a c k v| ≤
      C * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ A *
        G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
          (R ^ (1 / ((top : ℝ) + 1))) ^ (a + c) := by
    simpa only [physicalJetAt_of_mem D z hp, Real.norm_eq_abs, hpower] using hraw
  exact hraw'.trans (n04PulledFields_fullHeight_power_le (zero_le_one.trans hCA.1)
    ((G.cost_nonneg η).1 m) (Real.rpow_nonneg ((G.cost_nonneg η).2.1 m) _)
    (hHL m) hL (Real.rpow_nonneg (zero_le_one.trans hR) _) k (a + c))

end N04PulledFieldsColumnData

end ContinuousFlexibility.Analysis
