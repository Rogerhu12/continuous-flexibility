module

public import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientJoint
public import ContinuousFlexibility.Analysis.N04PulledFieldsPhysicalOneHighCurrent

/-!
# The actual coefficient towers on an admissible neighborhood

The original physical towers are restricted without changing any jet.
The original periodicity and the sampled raw physical estimate then
feed the common-neighborhood moving-point theorem for all three fields.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

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

/-- Restrict the original genuine coefficient tower to the admissible
state neighborhood, retaining every fixed-physical-point parameter jet. -/
def n04PulledFields_coefficientMixedOn
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε) (i : Fin 3) :
    MixedJetRegularity (sectorNeighborhood (G.S η) base ε ε)
      (annularOpen G.W.D) (fun z => G.coefficientField η i (G.lift η z)) := by
  have hsub : sectorNeighborhood (G.S η) base ε ε ⊆
      sectorNeighborhood (G.S η) G.W.base G.W.ε G.W.ε :=
    sectorNeighborhood_mono (G.S η) hadm.1 hadm.2.2.1 hadm.2.2.1
  let RF := n04PulledFields_gaugeCoefficientMixedRegularity G η i
  exact ⟨fun z hz => RF.spatial z (hsub hz),
    fun a b p hp => (RF.parameter a b p hp).restrict
      (isOpen_sectorNeighborhood (G.S η) base ε ε) hsub⟩

/-- The corresponding original joint tower is restricted to the same
neighborhood and the whole physical annulus. -/
def n04PulledFields_coefficientJointOn
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε) (i : Fin 3) :
    SmoothDirections (sectorNeighborhood (G.S η) base ε ε ×ˢ annularOpen G.W.D)
      (fun x : Parameter (G.S η) × PolarPoint =>
        G.coefficientField η i (G.lift η x.1) x.2) :=
  (n04PulledFields_gaugeCoefficientJointDirections G η i).restrict
    ((isOpen_sectorNeighborhood (G.S η) base ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun _ hx => ⟨sectorNeighborhood_mono (G.S η) hadm.1
      hadm.2.2.1 hadm.2.2.1 hx.1, hx.2⟩)

theorem n04PulledFields_coefficientPhysical_periodic
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (i : Fin 3) {z : Parameter (G.S η)}
    (hz : z ∈ sectorNeighborhood (G.S η) base ε ε)
    {p : PolarPoint} (hp : p ∈ annularOpen G.W.D) :
    G.coefficientField η i (G.lift η z) (p + (0, Real.pi)) =
      G.coefficientField η i (G.lift η z) p := by
  have hzstate : G.lift η z ∈ stateNeighborhood G.W.S G.W.C G.W.base G.W.ε :=
    stateNeighborhood_mono G.W.S G.W.C hadm.1 hadm.2.2.1
      (liftSectorParameter_mem_stateNeighborhood (C := G.C η) hz le_rfl)
  have hs := G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hper := G.W.field.periodic_coefficients _ hzstate hs p.1 hp.1
  have hpadd : p + (0, Real.pi) = (p.1, p.2 + Real.pi) :=
    Prod.ext (add_zero p.1) rfl
  unfold N04RealizationGauge.coefficientField canonicalCoefficientComponent
  rw [hpadd]
  split_ifs
  · exact hper.1 p.2
  · exact hper.2.1 p.2
  · exact hper.2.2 p.2

/-- A raw physical estimate for the retained coefficients, with a
common low order, gives their exact current data on one neighborhood. -/
theorem n04PulledFields_coefficient_currentData_of_sampledOneHigh
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (hgeo : G.GeometryData η (fun _ => True) base ε) (href : G.ReferenceData η)
    (hraw : N04PulledFieldsSampledPhysicalOneHigh G η base ε
      (G.coefficientField η) (n04PulledFields_coefficientMixedOn G η hadm)) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ i : Fin 3, G.Data η (fun _ => True) base' ε'
        (G.pulled η (G.coefficientField η i))
        (G.pulledRef η (G.coefficientField η i)) :=
  n04PulledFields_physicalOneHigh_currentData G η hadm hgeo href
    (G.coefficientField η) (n04PulledFields_coefficientMixedOn G η hadm)
    (n04PulledFields_coefficientJointOn G η hadm)
    (fun i _ hz _ hp => n04PulledFields_coefficientPhysical_periodic G η hadm i hz hp) hraw

end ContinuousFlexibility.Analysis
