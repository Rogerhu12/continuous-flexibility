import ContinuousFlexibility.Analysis.SmoothDirectionsGluing
import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition

/-!
# Joint towers on strips and a common zero region

The open-cover construction is performed over an abstract state space.
Concrete physical-state adapters only supply the strip towers and the
proved common zero set, avoiding expansion of their graded models in
the topological covering argument.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E ι : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {Ω : Set PolarPoint} {f : E × PolarPoint → ℝ}

def n04PulledFields_jointDirections_strip_or_zero
    (hU : IsOpen U) (hΩ : IsOpen Ω) (V : ι → Set PolarPoint)
    (hV : ∀ i, IsOpen (V i)) (Z : Set PolarPoint)
    (hcover : ∀ q ∈ Ω, (∃ i, q ∈ V i) ∨ q ∈ interior Z)
    (hzero : ∀ x ∈ U, ∀ q ∈ Z, f (x, q) = 0)
    (J : ∀ i, SmoothDirections (U ×ˢ V i) f) :
    SmoothDirections (U ×ˢ Ω) f := by
  classical
  let W : Option ι → Set (E × PolarPoint)
    | none => U ×ˢ (Ω ∩ interior Z)
    | some i => U ×ˢ (Ω ∩ V i)
  have hW (i : Option ι) : IsOpen (W i) := by
    cases i with
    | none => exact hU.prod (hΩ.inter isOpen_interior)
    | some i => exact hU.prod (hΩ.inter (hV i))
  have hsub (i : Option ι) : W i ⊆ U ×ˢ Ω := by
    cases i <;> exact fun _ hx => ⟨hx.1, hx.2.1⟩
  have hcov : ∀ x ∈ U ×ˢ Ω, ∃ i, x ∈ W i := by
    intro x hx
    rcases hcover x.2 hx.2 with ⟨i, hi⟩ | hz
    · exact ⟨some i, hx.1, hx.2, hi⟩
    · exact ⟨none, hx.1, hx.2, hz⟩
  let K : ∀ i, SmoothDirections (W i) f := by
    intro i
    cases i with
    | none =>
        exact (smoothDirections_constant (hW none) (0 : ℝ)).congrOn
          (fun x hx => (hzero x.1 hx.1 x.2 (interior_subset hx.2.2)).symm)
    | some i => exact (J i).restrict (hW (some i)) (fun _ hx => ⟨hx.1, hx.2.2⟩)
  exact (exists_smoothDirections_of_open_cover (hU.prod hΩ) W K hsub hcov).choose

end ContinuousFlexibility.Analysis
