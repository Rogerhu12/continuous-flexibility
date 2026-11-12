import ContinuousFlexibility.Analysis.N07aParameterGrading
import ContinuousFlexibility.Analysis.StateNeighborhood
import ContinuousFlexibility.Scalar.WeightedUniformTameGerm

/-!
# One sector neighborhood for an existing uniform tower

A single low seminorm ball fits inside the supplied open domain. The
same base increase restricts its uniform tower, so the resulting sector
neighborhood is chosen before every spatial and parameter order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

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

/-- Restrict one fixed tower to a prescribed smaller sector neighborhood,
retaining the map and its derivative loss. -/
theorem n04Realization_fixedNeighborhood_sectorRestriction
    {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (S : PhysicalSpacesData) {q : ℕ → Seminorm ℝ F}
    {U : Set (StateDirections S × ℝ)} {f : (StateDirections S × ℝ) → F}
    {towerBase loss base : ℕ} {ε : ℝ}
    (hU : IsOpen U) (hzero : (0 : StateDirections S × ℝ) ∈ U)
    (hf : FixedNeighborhoodSmoothTame (n07aParameterGrading S) q U towerBase loss f)
    (hε : 0 < ε) :
    ∃ b : ℕ, ∃ η : ℝ, base ≤ b ∧ 0 < η ∧ η ≤ ε ∧
      sectorNeighborhood S b η η ⊆ U ∧
      FixedNeighborhoodSmoothTame (n07aParameterGrading S) q
        (sectorNeighborhood S b η η) b loss f := by
  obtain ⟨b, δ, hb, hδ, _, hsub⟩ := exists_small_uniformTameBall
    (n07aParameterGrading_monotone S) (n07aParameterGrading_withSeminorms S)
    (hU.mem_nhds hzero) (max base towerBase)
  let η : ℝ := min ε (δ / 2)
  have hη : 0 < η := lt_min hε (half_pos hδ)
  have hηε : η ≤ ε := min_le_left _ _
  have hmap : sectorNeighborhood S b η η ⊆ U := by
    intro z hz
    apply hsub
    have he : η ≤ δ / 2 := min_le_right _ _
    have hsize : n07aParameterGrading S b z =
        sectorGrading S b z.1 + |z.2| :=
      pairGrading_apply (sectorGrading S) realGrading b z
    have hbound : sectorGrading S b z.1 + |z.2| < δ := by
      linarith only [hz.1, hz.2, he]
    exact ((congrArg (fun x : StateDirections S × ℝ => n07aParameterGrading S b x)
      (sub_zero z)).trans hsize).trans_lt hbound
  refine ⟨b, η, (le_max_left _ _).trans hb, hη, hηε, hmap, ?_⟩
  exact (hf.restrict (isOpen_sectorNeighborhood S b η η) hmap).weaken
    (n07aParameterGrading_monotone S) ((le_max_right _ _).trans hb) le_rfl

end ContinuousFlexibility.Analysis
