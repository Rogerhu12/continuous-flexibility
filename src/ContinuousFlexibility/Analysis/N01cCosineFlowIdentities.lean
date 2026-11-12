import ContinuousFlexibility.Analysis.N01cCosineAngularJets

/-!
# The supplied ordinary trajectories in the compact coordinate

The closed-time continuity and initial value are inherited directly
from the supplied ordinary trajectories on the same radial component.
These facts are the compact-flow inputs for their actual state and
spatial regularity.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

theorem continuousOn_componentCosineFlow
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ) (θ : ℝ) :
    ContinuousOn (fun t => C.minusFlow z m (rootCosinePath (C.left m) (C.right m) t) θ)
      (Icc (0 : ℝ) Real.pi) :=
  (hB.1 z hz m θ).2.1.comp
    (contDiff_rootCosinePath (C.left m) (C.right m)).continuous.continuousOn
    (fun t _ => rootCosinePath_mem_Icc (hA.2.2.1.1 m).2.1.le t)

theorem componentCosineFlow_initial
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ) (θ : ℝ) :
    C.minusFlow z m (rootCosinePath (C.left m) (C.right m) 0) θ = θ := by
  rw [rootCosinePath_zero]
  exact (hB.1 z hz m θ).1

end ContinuousFlexibility.Statements
