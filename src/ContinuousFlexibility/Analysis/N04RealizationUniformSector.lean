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

/-- Perform the neighborhood choice over abstract graded data. The
concrete sector type enters only after the choice has been assembled. -/
private theorem n04Realization_uniformRestriction_family
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (ht : WithSeminorms p)
    {q : ℕ → Seminorm ℝ F} {U : Set E} {f : E → F}
    (V : ℕ → ℝ → Set E) (hV : ∀ b η, IsOpen (V b η))
    (hsize : ∀ b η x, x ∈ V b η → p b x < 2 * η)
    {towerBase loss base : ℕ} {ε : ℝ}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U)
    (hf : FixedNeighborhoodSmoothTame p q U towerBase loss f) (hε : 0 < ε) :
    ∃ b : ℕ, ∃ η : ℝ, base ≤ b ∧ 0 < η ∧ η ≤ ε ∧ V b η ⊆ U ∧
      FixedNeighborhoodSmoothTame p q (V b η) b loss f := by
  obtain ⟨b, δ, hb, hδ, _, hsub⟩ := exists_small_uniformTameBall hp ht
    (hU.mem_nhds hzero) (max base towerBase)
  let η : ℝ := min ε (δ / 2)
  have hη : 0 < η := lt_min hε (half_pos hδ)
  have hηε : η ≤ ε := min_le_left _ _
  have hmap : V b η ⊆ U := by
    intro x hx
    apply hsub
    have he : η ≤ δ / 2 := min_le_right _ _
    have hxδ : p b x < δ := lt_of_lt_of_le (hsize b η x hx) (by linarith)
    simpa only [Set.mem_setOf_eq, sub_zero] using hxδ
  exact ⟨b, η, (le_max_left _ _).trans hb, hη, hηε, hmap,
    (hf.restrict (hV b η) hmap).weaken hp ((le_max_right _ _).trans hb) le_rfl⟩

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
  apply n04Realization_uniformRestriction_family (n07aParameterGrading S)
    (n07aParameterGrading_monotone S) (n07aParameterGrading_withSeminorms S)
    (fun b η => sectorNeighborhood S b η η)
    (fun b η => isOpen_sectorNeighborhood S b η η) _ hU hzero hf hε
  intro b η z hz
  have hsize : n07aParameterGrading S b z =
      sectorGrading S b z.1 + |z.2| :=
    pairGrading_apply (sectorGrading S) realGrading b z
  rw [hsize]
  linarith only [hz.1, hz.2]

end ContinuousFlexibility.Analysis
