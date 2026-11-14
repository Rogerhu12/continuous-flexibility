import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsMixedBlocks

/-!
# Actual composition through a state-preserving moving point

The same selected blocks used in the inverse recurrence also describe
an arbitrary scalar or vector field evaluated at the moving inverse
point. Only original state singletons survive in the state coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open scoped Topology ContDiff BigOperators

variable {P V Z : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem n04PositiveGeometry_movingPoint_projected_partition
    {f : P × V → Z} {g : P × V → V} {x : P × V}
    (hf : ContDiffAt ℝ ∞ f (n04PositiveGeometry_fiberLift g x))
    (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (b : Fin n → Bool) :
    n04PositiveGeometry_projectedJet b (f ∘ n04PositiveGeometry_fiberLift g) x =
      ∑ c : OrderedFinpartition n, ∑ s : Finset (Fin c.length),
        n04PositiveGeometry_inverseSelectedTerm b f g x c s := by
  classical
  have hcomp : iteratedFDeriv ℝ n (f ∘ n04PositiveGeometry_fiberLift g) x =
      ∑ c : OrderedFinpartition n,
        c.compAlongOrderedFinpartition
          (iteratedFDeriv ℝ c.length f (n04PositiveGeometry_fiberLift g x))
          (fun i => iteratedFDeriv ℝ (c.partSize i)
            (n04PositiveGeometry_fiberLift g) x) :=
    iteratedFDeriv_comp hf (contDiffAt_fst.prodMk hg)
      (by simp : (n : ℕ∞ω) ≤ ∞)
  apply ContinuousMultilinearMap.ext
  intro v
  rw [n04PositiveGeometry_projectedJet_apply, hcomp]
  simp only [ContinuousMultilinearMap.sum_apply,
    OrderedFinpartition.compAlongOrderFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply]
  apply Finset.sum_congr rfl
  intro c _
  rw [n04PositiveGeometry_multilinear_projection_expansion]
  apply Finset.sum_congr rfl
  intro s _
  exact (n04PositiveGeometry_inverseSelectedTerm_apply b f g x c s v).symm

theorem n04PositiveGeometry_movingPoint_projected_norm_terms
    {f : P × V → Z} {g : P × V → V} {x : P × V}
    (hf : ContDiffAt ℝ ∞ f (n04PositiveGeometry_fiberLift g x))
    (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (b : Fin n → Bool) :
    ‖n04PositiveGeometry_projectedJet b (f ∘ n04PositiveGeometry_fiberLift g) x‖ ≤
      ∑ c : OrderedFinpartition n, ∑ s : Finset (Fin c.length),
        ‖n04PositiveGeometry_inverseSelectedTerm b f g x c s‖ := by
  classical
  rw [n04PositiveGeometry_movingPoint_projected_partition hf hg b]
  calc
    _ ≤ ∑ c : OrderedFinpartition n,
        ‖∑ s : Finset (Fin c.length), n04PositiveGeometry_inverseSelectedTerm b f g x c s‖ :=
      norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)

end ContinuousFlexibility.Analysis
