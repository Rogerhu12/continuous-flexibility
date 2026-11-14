module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Continuity of linear maps bounded by a source seminorm

The source retains its original topological vector space topology. A
norm on that source is neither introduced nor needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped Topology

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bound by one continuous seminorm gives continuity in the original
source topology; no norm on the projective source is introduced. -/
theorem continuous_linear_of_seminorm_bound (L : E →ₗ[ℝ] F) (p : Seminorm ℝ E)
    (hp : Continuous p) (K : ℝ) (hbound : ∀ x, ‖L x‖ ≤ K * p x) : Continuous L := by
  apply continuous_of_tendsto_nhds_zero L
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hzero : Filter.Tendsto (fun x : E => K * p x) (𝓝 (0 : E)) (𝓝 (0 : ℝ)) := by
    simpa only [map_zero, mul_zero] using (hp.tendsto (0 : E)).const_mul K
  exact squeeze_zero' (Filter.Eventually.of_forall fun x : E => norm_nonneg (L x))
    (Filter.Eventually.of_forall hbound) hzero

end ContinuousFlexibility.Analysis
