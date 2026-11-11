import ContinuousFlexibility.Analysis.NeighborhoodCircleCharts
import ContinuousFlexibility.Analysis.NeighborhoodCircleChartsState
import ContinuousFlexibility.Blueprint.Statements

/-!
# Installing the actual flows and their actual inverses

The reference state, controls and component geometry are retained. The
return inverse and right-chart inverse are the inverses of their defining
maps on the real line.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function
open ContinuousFlexibility.Analysis
open ContinuousFlexibility.Blueprint

def circleFlowGeometry {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (Θ : (AnnularState S × ℝ) → ℕ → ℝ → ℝ → ℝ) : NonlinearGeometryData S :=
  { C with
    minusFlow := Θ
    minusReturnInverse := fun z m => invFun (Θ z m (C.right m))
    rightChartInverse := fun z m =>
      invFun (circleOddPart
        (stateLeftChart S z.1 m ∘ invFun (Θ z m (C.right m))) (C.travel m)) }

theorem circleFlowGeometry_partA {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : N01PartA D T S C)
    (Θ : (AnnularState S × ℝ) → ℕ → ℝ → ℝ → ℝ) :
    N01PartA D T S (circleFlowGeometry C Θ) := hC

theorem circleFlowGeometry_inverse_identities {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S)
    (Θ : (AnnularState S × ℝ) → ℕ → ℝ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (m : ℕ)
    (hLc : Continuous (stateLeftChart S z.1 m))
    (hLm : StrictMono (stateLeftChart S z.1 m))
    (hLl : ∀ θ, stateLeftChart S z.1 m (θ + Real.pi) =
      stateLeftChart S z.1 m θ + Real.pi)
    (hRc : Continuous (Θ z m (C.right m)))
    (hRm : StrictMono (Θ z m (C.right m)))
    (hRl : ∀ θ, Θ z m (C.right m) (θ + Real.pi) = Θ z m (C.right m) θ + Real.pi) :
    let C' := circleFlowGeometry C Θ
    (∀ θ, C'.minusFlow z m (C'.right m) (C'.minusReturnInverse z m θ) = θ ∧
      C'.minusReturnInverse z m (C'.minusFlow z m (C'.right m) θ) = θ) ∧
    (let hR : ℝ → ℝ := fun t =>
      ((stateLeftChart S z.1 m (C'.minusReturnInverse z m t) - C'.travel m) -
        (stateLeftChart S z.1 m (C'.minusReturnInverse z m (-t)) - C'.travel m)) / 2
      ∀ θ, hR (C'.rightChartInverse z m θ) = θ ∧ C'.rightChartInverse z m (hR θ) = θ) := by
  obtain ⟨_, _, hretRight, hretLeft, _⟩ :=
    circleLift_invFun_properties Real.pi_pos hRc hRm hRl
  obtain ⟨_, _, _, _, hchartRight, hchartLeft⟩ :=
    circleOddPart_comp_invFun_properties Real.pi_pos hLc hLm hLl hRc hRm hRl (C.travel m)
  constructor
  · intro θ
    exact ⟨hretRight θ, hretLeft θ⟩
  · intro hR θ
    exact ⟨hchartRight θ, hchartLeft θ⟩

end ContinuousFlexibility.Statements
