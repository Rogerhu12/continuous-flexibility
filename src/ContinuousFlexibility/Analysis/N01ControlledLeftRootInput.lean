module

public import ContinuousFlexibility.Analysis.N01ControlledRootInput

/-!
# Left-root compatibility interface

The implementation is the single Boolean endpoint construction.
These aliases and the false-endpoint corollary retain the existing
left-root API, including its sharper odd-coefficient lower bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

abbrev N01ControlledLeftRootInputAtState
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (m : ℕ) (g : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (κ δ Λ : ℝ) (loss : ℕ) (B : ℕ → ℝ) (z : AnnularState S × ℝ) : Prop :=
  N01ControlledRootInputAtState D S C m false g hR κ δ Λ loss B z

abbrev N01ControlledLeftRootInputFamily
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (m : ℕ) (g : ℝ → ℝ)
    {R : ℝ} (hR : 0 < R) (κ δ Λ : ℝ) (B : ℕ → ℝ) : Prop :=
  N01ControlledRootInputFamily D S C base loss ε m false g hR κ δ Λ B

/-- The original left-root result is the false-endpoint specialization
of the common two-endpoint theorem. -/
theorem n01_exists_common_left_root_inputs
    (hFlow : N04FlowJetsTarget)
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ, base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m : ℕ, ∃ g : ℝ → ℝ, ∃ R : ℝ, ∃ hR : 0 < R, ∃ κ : ℝ,
        ContDiff ℝ ∞ g ∧ 0 < g 0 ∧ 0 < κ ∧
        (∀ t : ℝ, -deriv D.w (C.left m + t) = t * g t) ∧
        N01ActualRootFieldGeometry D S C newBase ε' (C.left m) 1 g hR ∧
        ∀ Λ : ℝ, 0 < Λ → ∃ δ : ℝ, ∃ B : ℕ → ℝ,
          0 < δ ∧ δ ≤ R / 4 ∧ δ ≤ 1 ∧ (∀ s, 0 < B s) ∧
          N01ControlledLeftRootInputFamily D S C newBase outLoss ε'
            m g hR κ δ Λ B := by
  obtain ⟨newBase, outLoss, ε', hb, hε', hsmall, _hreturn, hroots⟩ :=
    n01_exists_common_root_inputs hFlow hS hT hN
  refine ⟨newBase, outLoss, ε', hb, hε', hsmall, ?_⟩
  intro m
  simpa only [N01ControlledRootInputData, n01ComponentRoot,
    n01ComponentRootOrientation, Bool.false_eq_true, ite_false, one_mul] using hroots m false

end ContinuousFlexibility.Analysis
