import ContinuousFlexibility.Statements.Radial
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# The exceptional critical radii of the reference profile

The profile specification makes every interior critical point simple.
Consequently its critical set is discrete, countable, and Lebesgue null.
No analyticity of the smooth accumulating profile is used.
-/

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem n04_countable_simple_zeros {f : ℝ → ℝ} {s : Set ℝ}
    (hf : ∀ x ∈ s, f x = 0 → DifferentiableAt ℝ f x ∧ deriv f x ≠ 0) :
    {x ∈ s | f x = 0}.Countable := by
  let Z : Set ℝ := {x ∈ s | f x = 0}
  have hd : DiscreteTopology Z := discreteTopology_subtype_iff.mpr (by
    intro x hx
    rw [inf_principal_eq_bot]
    obtain ⟨hfx, hnonzero⟩ := hf x hx.1 hx.2
    have hne : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 :=
      hfx.hasDerivAt.eventually_ne hnonzero
    exact hne.mono fun y hy hyZ => hy hyZ.2)
  letI : DiscreteTopology Z := hd
  exact Set.countable_coe_iff.mp
    (TopologicalSpace.separableSpace_iff_countable.mp (inferInstance : SeparableSpace Z))

theorem n04_reference_critical_set_countable {D : ReferenceData}
    (hD : RadialProfileGeometry D) :
    {r ∈ radialCore D | deriv D.w r = 0}.Countable := by
  apply n04_countable_simple_zeros
  intro r hr hz
  exact ⟨(hD.2.2.1.1.of_le (by simp)).differentiable_deriv_two r,
    hD.2.2.2.2.2.2 r hr hz⟩

theorem n04_reference_critical_set_null {D : ReferenceData}
    (hD : RadialProfileGeometry D) :
    volume {r ∈ radialCore D | deriv D.w r = 0} = 0 :=
  (n04_reference_critical_set_countable hD).measure_zero volume

end ContinuousFlexibility.Analysis
