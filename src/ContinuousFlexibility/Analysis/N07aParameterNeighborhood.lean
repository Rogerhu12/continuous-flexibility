module

public import ContinuousFlexibility.Analysis.N07aNeighborhood
public import ContinuousFlexibility.Analysis.N07aSampleComposition

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

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

variable {S : PhysicalSpacesData} {base low : ℕ} {ε : ℝ}

/-- One choice of the sector neighborhood controls a fixed parameter seminorm. -/
theorem n07a_lowParameter_neighborhood (hε : 0 < ε) (low : ℕ) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      sectorNeighborhood S base' ε' ε' ⊆ sectorNeighborhood S base ε ε ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε',
        CanonicalGeometry.parameterGrading S low z ≤ 1 := by
  let base' := max base low
  let ε' := min ε (1 / 2 : ℝ)
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  have hle : ε' ≤ ε := min_le_left _ _
  have hhalf : ε' ≤ (1 / 2 : ℝ) := min_le_right _ _
  refine ⟨base', le_max_left _ _, ε', hε', hle,
    n07a_sectorNeighborhood_mono (S := S) (le_max_left _ _) hle, ?_⟩
  intro z hz
  have h₁ : sectorGrading S low z.1 < (1 / 2 : ℝ) :=
    ((solve_sectorGrading_monotone S (le_max_right base low) z.1).trans_lt hz.1).trans_le hhalf
  have h₂ : |z.2| < (1 / 2 : ℝ) := hz.2.trans_le hhalf
  have heq : CanonicalGeometry.parameterGrading S low z =
      sectorGrading S low z.1 + |z.2| :=
    pairGrading_apply (E := StateDirections S) (F := ℝ)
      (sectorGrading S) realGrading low z
  exact heq.le.trans (by linarith only [h₁, h₂])

end ContinuousFlexibility.Analysis
