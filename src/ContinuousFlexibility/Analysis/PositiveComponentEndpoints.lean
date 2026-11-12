import ContinuousFlexibility.Analysis.N04PositiveNormalizationBuffer
import ContinuousFlexibility.Statements.Radial

/-!
# The two kinds of positive-component endpoints

A component endpoint is either the corresponding ambient endpoint or a
true zero of the radial coefficient in the ambient open interval. For
the actual profile, every interior endpoint is therefore a simple root.
No adjacent negative component is silently imposed at an ambient end.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

def n04PositiveEndpoint {a b : ℝ} {f : ℝ → ℝ}
    (i : N04PositiveComponent a b f) (side : Bool) : ℝ :=
  if side then n04PositiveRight i else n04PositiveLeft i

theorem n04PositiveEndpoint_mem_closure {a b : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (i : N04PositiveComponent a b f) (side : Bool) :
    n04PositiveEndpoint i side ∈ closure i.val := by
  rw [n04PositiveComponent_eq_Ioo hf i,
    closure_Ioo (n04PositiveComponent_bounds hf i).2.1.ne]
  cases side
  · exact ⟨le_rfl, (n04PositiveComponent_bounds hf i).2.1.le⟩
  · exact ⟨(n04PositiveComponent_bounds hf i).2.1.le, le_rfl⟩

theorem n04PositiveEndpoint_not_mem {a b : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (i : N04PositiveComponent a b f) (side : Bool) :
    n04PositiveEndpoint i side ∉ i.val := by
  rw [n04PositiveComponent_eq_Ioo hf i]
  cases side <;> simp only [n04PositiveEndpoint, Bool.false_eq_true,
    ite_false, ite_true, mem_Ioo, lt_self_iff_false, false_and, and_false, not_false_eq_true]

theorem n04PositiveEndpoint_ambient_or_zero {a b : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (i : N04PositiveComponent a b f) (side : Bool) :
    n04PositiveEndpoint i side = (if side then b else a) ∨
      n04PositiveEndpoint i side ∈ Ioo a b ∧ f (n04PositiveEndpoint i side) = 0 := by
  by_cases he : n04PositiveEndpoint i side = (if side then b else a)
  · exact Or.inl he
  have hb := n04PositiveComponent_bounds hf i
  have hcore : n04PositiveEndpoint i side ∈ Ioo a b := by
    cases side
    · change n04PositiveLeft i ≠ a at he
      exact ⟨lt_of_le_of_ne hb.1 he.symm, hb.2.1.trans_le hb.2.2⟩
    · change n04PositiveRight i ≠ b at he
      exact ⟨hb.1.trans_lt hb.2.1, lt_of_le_of_ne hb.2.2 he⟩
  have hclosure := n04PositiveEndpoint_mem_closure hf i side
  have hnonnegative : 0 ≤ f (n04PositiveEndpoint i side) := by
    have hsubset : i.val ⊆ {x : ℝ | 0 ≤ f x} :=
      fun x hx => (n04PositiveComponent_subset i hx).2.le
    exact closure_minimal hsubset (isClosed_le continuous_const hf) hclosure
  have hnonpositive : f (n04PositiveEndpoint i side) ≤ 0 := by
    apply le_of_not_gt
    intro hpositive
    exact n04PositiveEndpoint_not_mem hf i side
      (n04PositiveComponent_closure_inter_region_subset hf i
        ⟨hclosure, hcore, hpositive⟩)
  exact Or.inr ⟨hcore, le_antisymm hnonpositive hnonnegative⟩

theorem n04PositiveEndpoint_ambient_or_simple_root {D : ReferenceData}
    (hD : RadialProfileGeometry D)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (side : Bool) :
    n04PositiveEndpoint i side = (if side then D.b else D.a) ∨
      n04PositiveEndpoint i side ∈ radialCore D ∧
      deriv D.w (n04PositiveEndpoint i side) = 0 ∧
      deriv (deriv D.w) (n04PositiveEndpoint i side) ≠ 0 := by
  have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  rcases n04PositiveEndpoint_ambient_or_zero hf i side with he | ⟨hc, hz⟩
  · exact Or.inl he
  · exact Or.inr ⟨hc, hz, hD.2.2.2.2.2.2 _ hc hz⟩

end ContinuousFlexibility.Analysis
