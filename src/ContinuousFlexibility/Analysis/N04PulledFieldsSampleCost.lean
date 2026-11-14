module

public import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
public import ContinuousFlexibility.Analysis.MaterialSampleBounds
public import ContinuousFlexibility.Analysis.TameLocalCalculus

/-!
# Uniform material cost at the actual gauge samples

The sampled height bound is chosen before the auxiliary column. Cell
replacement changes neither the physical material nor its samples.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

/-- Every actual gauge sample lies in the physical radial interval. -/
theorem n04PulledFields_sample_mem_interval
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) :
    G.W.U.sample ((G.V η).cell m) ∈ Ioo G.W.D.a G.W.D.b :=
  materialSample_mem_interval G.W.radial.1
    (isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT) ((G.V η).cell m)

/-- One finite bound controls the height factor at all gauge samples,
before every auxiliary column and piece. -/
theorem n04PulledFields_sampleHeight_bounded (G : N04RealizationGauge) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ η : (G.W.S.height (3 / 4 : ℝ)).Space, ∀ m,
        G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) ≤ L := by
  have h := material_sample_height_coefficient_power_bounded G.W.radial.1
    (isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT)
    (fun m => m) 0 (by norm_num : 0 < (3 / 4 : ℝ))
  refine ⟨max 1 h.choose, le_max_left _ _, fun η m => ?_⟩
  have hh : G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) ≤ h.choose := by
    simpa only [Real.rpow_zero, mul_one] using h.choose_spec.2 ((G.V η).cell m)
  exact hh.trans (le_max_right _ _)

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

/-- The sum grading is at most one on any sector neighborhood of radius
at most one half. This holds at its own low order. -/
theorem n04PulledFields_parameterGrading_le_one
    (S : PhysicalSpacesData) {base : ℕ} {ε : ℝ} (hε : ε ≤ 1 / 2)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε) :
    parameterGrading S base z ≤ 1 := by
  have hsum : sectorGrading S base z.1 + |z.2| ≤ 1 := by linarith [hz.1, hz.2]
  simpa only [parameterGrading, pairGrading_apply, realGrading,
    coe_normSeminorm, Real.norm_eq_abs] using hsum

end ContinuousFlexibility.Analysis
