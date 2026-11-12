import ContinuousFlexibility.Analysis.N05SeedOpticalLowerMorse
import ContinuousFlexibility.Radial.SeedReferenceRetention
import ContinuousFlexibility.Radial.ProfileLayerGeometry

/-!
# The actual seed transports optical ratios and physical cell indices

Both statements use the profile and cell identities retained by the seed
construction. The source profile and the final profile are never reselected.
The index estimate applies to every final cell containing the same point.
-/

noncomputable section

namespace ContinuousFlexibility.Radial.SeedReferenceConstruction

open Set Filter Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {q : ℝ} (P : SeedReferenceConstruction q)

def n05TailScale (side : Bool) : ℝ :=
  if side then P.glued.radiusR else P.glued.radiusL

theorem n05TailScale_pos (side : Bool) : 0 < P.n05TailScale side := by
  cases side
  · exact P.glued.radiusL_pos
  · exact P.glued.radiusL_pos.trans_le P.glued.radius_order

theorem n05TailScale_le (side : Bool) : P.n05TailScale side ≤ P.glued.radiusR := by
  cases side
  · exact P.glued.radius_order
  · exact le_rfl

def n05ModelLeft (side : Bool) (n : ℕ) : ℝ :=
  P.selected.chain.radius side n
    (morseLeftTurn (morseChainA P.selected.chain n) (morseChainB P.selected.chain n))

def n05ModelRight (side : Bool) (n : ℕ) : ℝ :=
  P.selected.chain.radius side n (morseChainRightTurn P.selected.chain n)

theorem n05_model_component (side : Bool) {n : ℕ}
    (hn : P.selected.chain.index ≤ n) :
    NegativeRadialComponent (P.selected.family P.selected.sigma)
      (P.n05ModelLeft side n) (P.n05ModelRight side n) :=
  (morseRealization_model_return P.realization P.selected_spec.2.2.1 side hn).1

theorem n05_model_cover (side : Bool) {n : ℕ}
    (hn : P.selected.chain.index ≤ n) {r : ℝ}
    (hr : r ∈ Ioo (P.n05ModelLeft side n) (P.n05ModelRight side n)) :
    ∃ k : ℕ, (P.selected.family P.selected.sigma).cellIndex k = n ∧
      r ∈ (P.selected.family P.selected.sigma).cells k :=
  (morseRealization_model_return P.realization P.selected_spec.2.2.1 side hn).2.2 r hr

theorem n05_tail_mem_core (side : Bool) {r : ℝ}
    (hr : r ∈ radialTailInterval (P.selected.family P.selected.sigma) side
      (P.selected.entry side P.selected.chain.index)) :
    r ∈ radialCore (P.selected.family P.selected.sigma) := by
  cases side with
  | false => exact ⟨hr.1, hr.2.trans (P.entry_core false).2⟩
  | true => exact ⟨(P.entry_core true).1.trans hr.1, hr.2⟩

theorem n05_tail_scaled_mem_core (side : Bool) {r : ℝ}
    (hr : r ∈ radialTailInterval (P.selected.family P.selected.sigma) side
      (P.selected.entry side P.selected.chain.index)) :
    P.n05TailScale side * r ∈ radialCore P.reference := by
  have hG := P.accumulating.choose_spec.1
  have hscale := P.n05TailScale_pos side
  have hheight : 0 < (if side then P.glued.heightR else P.glued.heightL) := by
    cases side
    · exact P.glued.heightL_pos
    · exact P.glued.heightR_pos
  have hw : 0 < P.reference.w (P.n05TailScale side * r) := by
    rw [show P.reference.w (P.n05TailScale side * r) =
      (if side then P.glued.heightR else P.glued.heightL) *
        P.n05TailScale side * (P.selected.family P.selected.sigma).w r from
          P.tail_profile side hr]
    exact mul_pos (mul_pos hheight hscale)
      (P.realization.geometry.2.2.2.2.1 r (P.n05_tail_mem_core side hr))
  constructor
  · by_contra hh
    have hz := hG.2.2.1.2 _ (Or.inl (le_of_not_gt hh))
    exact hw.ne' hz
  · by_contra hh
    have hz := hG.2.2.1.2 _ (Or.inr (le_of_not_gt hh))
    exact hw.ne' hz

/-- The height scaling cancels; the actual optical square scales by the
inverse square of the actual radius scaling. -/
theorem n05_tail_opticalRatio (side : Bool) {r : ℝ}
    (hr : r ∈ radialTailInterval (P.selected.family P.selected.sigma) side
      (P.selected.entry side P.selected.chain.index)) :
    -deriv P.reference.w (P.n05TailScale side * r) /
        ((P.n05TailScale side * r) * P.reference.w (P.n05TailScale side * r)) =
      (-deriv (P.selected.family P.selected.sigma).w r /
        (r * (P.selected.family P.selected.sigma).w r)) / (P.n05TailScale side) ^ 2 := by
  have hG := P.realization.geometry
  have hrCore := P.n05_tail_mem_core side hr
  have hheight : 0 < (if side then P.glued.heightR else P.glued.heightL) := by
    cases side
    · exact P.glued.heightL_pos
    · exact P.glued.heightR_pos
  have ho : IsOpen (radialTailInterval (P.selected.family P.selected.sigma) side
      (P.selected.entry side P.selected.chain.index)) := by
    cases side <;> exact isOpen_Ioo
  apply n05_seed_opticalRatio_dilation
    ((P.accumulating.choose_spec.1.2.2.1.1.differentiable (by simp)) _)
    ((hG.2.2.1.1.differentiable (by simp)) r)
    (P.n05TailScale_pos side).ne' hheight.ne'
    (hG.1.trans hrCore.1).ne' (hG.2.2.2.2.1 r hrCore).ne'
  filter_upwards [ho.mem_nhds hr] with t ht
  exact P.tail_profile side ht

/-- A model index is uniformly below the index of any actual final cell
containing the same scaled point. Saturation and the finite floor cause no
loss depending on the model index. -/
theorem n05_tail_model_index_le_actual :
    ∃ N : ℕ, ∀ (side : Bool) (k j : ℕ) (r : ℝ),
      r ∈ radialTailInterval (P.selected.family P.selected.sigma) side
        (P.selected.entry side P.selected.chain.index) →
      r ∈ (P.selected.family P.selected.sigma).cells k →
      P.n05TailScale side * r ∈ P.reference.cells j →
      (P.selected.family P.selected.sigma).cellIndex k ≤ P.reference.cellIndex j + N := by
  obtain ⟨C, hC⟩ := P.accumulating
  obtain ⟨N, hN⟩ := profileEndpointLayer_index_window hC
  refine ⟨N, fun side k j r hr hk hj => ?_⟩
  have hscaled : P.n05TailScale side * r ∈ P.reference.cells k := P.tail_cell side k hr hk
  have hone := profileLayerCutoff_one_on_cell hC hscaled
  have hsupport : P.n05TailScale side * r ∈
      Function.support (profileLayerCutoff P.reference (C 0) (P.reference.cellIndex k)) := by
    change profileLayerCutoff P.reference (C 0) (P.reference.cellIndex k)
      (P.n05TailScale side * r) ≠ 0
    rw [hone]
    exact one_ne_zero
  have hlayer := tsupport_profileLayerCutoff_subset (D := P.reference) (hC.2.2.1 0)
    (P.reference.cellIndex k) (subset_tsupport _ hsupport)
  have hindex := (hN (P.reference.cellIndex k) j _ hlayer hj).1
  have hfloor : (P.selected.family P.selected.sigma).cellIndex k ≤ P.reference.cellIndex k := by
    rw [P.cellIndex]
    exact Nat.le_max_left _ _
  exact hfloor.trans hindex

end ContinuousFlexibility.Radial.SeedReferenceConstruction
