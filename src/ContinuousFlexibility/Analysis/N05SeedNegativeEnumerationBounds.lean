import ContinuousFlexibility.Analysis.N05SeedNegativeEnumeration
import Mathlib.Algebra.Order.Group.MinMax

/-!
# Actual host indices of the explicit seed enumeration

Only the original Morse partition's exact index formula is an extra
input.  The carrier comparison follows from the actual cells meeting at
one point.  The constant is chosen before every possible carrier map.
-/

noncomputable section

namespace ContinuousFlexibility.Radial.SeedReferenceConstruction

open Set Real
open ContinuousFlexibility.Statements

variable {q : ℝ} (P : SeedReferenceConstruction q)

theorem n05_same_point_cell_index_window :
    ∃ N : ℕ, ∀ (i j : ℕ) (r : ℝ), r ∈ P.reference.cells i →
      r ∈ P.reference.cells j →
      |(P.reference.cellIndex i : ℝ) - P.reference.cellIndex j| ≤ N := by
  obtain ⟨C, hC⟩ := P.accumulating
  obtain ⟨N, hN⟩ := profileEndpointLayer_index_window hC
  refine ⟨N, fun i j r hi hj => ?_⟩
  have hone := profileLayerCutoff_one_on_cell hC hi
  have hs : r ∈ Function.support
      (profileLayerCutoff P.reference (C 0) (P.reference.cellIndex i)) := by
    apply Function.mem_support.mpr
    rw [hone]
    exact one_ne_zero
  have hlayer := tsupport_profileLayerCutoff_subset (D := P.reference) (hC.2.2.1 0)
    (P.reference.cellIndex i) (subset_tsupport _ hs)
  have hw := hN (P.reference.cellIndex i) j r hlayer hj
  have hi' : (P.reference.cellIndex i : ℝ) ≤ (P.reference.cellIndex j : ℝ) + N := by
    exact_mod_cast hw.1
  have hj' : (P.reference.cellIndex j : ℝ) ≤ (P.reference.cellIndex i : ℝ) + N := by
    exact_mod_cast hw.2
  exact abs_le.mpr ⟨by linarith only [hj'], by linarith only [hi']⟩

theorem n05_tail_slot_index
    (hraw : (P.selected.family P.selected.sigma).cellIndex =
      morseTwoTailAt P.selected.chain.index (fun _ k => P.selected.chain.index + k))
    (side : Bool) (k : ℕ) :
    P.reference.cellIndex (morseTailIndex side k) =
      max (P.selected.chain.index + k) P.indexFloor := by
  rw [P.cellIndex, hraw, morseTwoTailAt_tail]

theorem n05_tail_floor_shift (k : ℕ) :
    |((max (P.retainedIndex + k) P.indexFloor : ℕ) : ℝ) -
      ((max (P.selected.chain.index + k) P.indexFloor : ℕ) : ℝ)| ≤
      |(P.retainedIndex : ℝ) - P.selected.chain.index| := by
  have he : ((P.retainedIndex + k : ℕ) : ℝ) -
      ((P.selected.chain.index + k : ℕ) : ℝ) =
      (P.retainedIndex : ℝ) - P.selected.chain.index := by
    simp only [Nat.cast_add]
    ring
  simpa only [Nat.cast_max, he] using abs_max_sub_max_le_abs
    ((P.retainedIndex + k : ℕ) : ℝ) ((P.selected.chain.index + k : ℕ) : ℝ)
    (P.indexFloor : ℝ)

/-- One constant controls every actual whole-component carrier.  The
central carrier is fixed once, before the arbitrary carriers below. -/
theorem n05NegativeComponentAt_carrier_index_bound (hq : 0 < q)
    (hraw : (P.selected.family P.selected.sigma).cellIndex =
      morseTwoTailAt P.selected.chain.index (fun _ k => P.selected.chain.index + k)) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m j : ℕ),
      Ioo (P.n05NegativeComponentAt hq m).val.1 (P.n05NegativeComponentAt hq m).val.2 ⊆
        P.reference.cells j →
      |(P.reference.cellIndex j : ℝ) - P.reference.cellIndex m| ≤ B := by
  obtain ⟨N, hN⟩ := P.n05_same_point_cell_index_window
  let J₀ := P.n05CentralNegativeComponent hq
  obtain ⟨_, _, hreturns⟩ := P.construction.2.2
  obtain ⟨_, j₀, hj₀, _⟩ := hreturns J₀.val.1 J₀.val.2 J₀.property
  let B : ℝ := 1 + (N : ℝ) + |(P.retainedIndex : ℝ) - P.selected.chain.index| +
    |(P.reference.cellIndex j₀ : ℝ) - P.reference.cellIndex 0|
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB, fun m j hcarrier => ?_⟩
  rcases n05_seed_slot_cases m with rfl | ⟨side, k, rfl⟩
  · rw [n05NegativeComponentAt_zero] at hcarrier
    have hmid : (J₀.val.1 + J₀.val.2) / 2 ∈ Ioo J₀.val.1 J₀.val.2 := by
      constructor <;> linarith only [J₀.property.2.1]
    have hw := hN j j₀ _ (hcarrier hmid) (hj₀ hmid)
    calc
      |(P.reference.cellIndex j : ℝ) - P.reference.cellIndex 0| ≤
          |(P.reference.cellIndex j : ℝ) - P.reference.cellIndex j₀| +
            |(P.reference.cellIndex j₀ : ℝ) - P.reference.cellIndex 0| := abs_sub_le _ _ _
      _ ≤ (N : ℝ) + |(P.reference.cellIndex j₀ : ℝ) - P.reference.cellIndex 0| :=
        add_le_add hw (le_refl _)
      _ ≤ B := by
        dsimp only [B]
        linarith only [abs_nonneg ((P.retainedIndex : ℝ) - P.selected.chain.index)]
  · rw [n05NegativeComponentAt_tail] at hcarrier
    have hn := P.retainedIndex_ge.trans (Nat.le_add_right P.retainedIndex k)
    have hc := P.n05_model_component side hn
    let r : ℝ := (P.n05ModelLeft side (P.retainedIndex + k) +
      P.n05ModelRight side (P.retainedIndex + k)) / 2
    have hr : r ∈ Ioo (P.n05ModelLeft side (P.retainedIndex + k))
        (P.n05ModelRight side (P.retainedIndex + k)) := by
      dsimp only [r]
      constructor <;> linarith only [hc.2.1]
    have hrtail := P.n05_model_closed_subset_retained_tail side
      (Nat.le_add_right P.retainedIndex k) (Ioo_subset_Icc_self hr)
    obtain ⟨i, hi, hri⟩ := P.n05_model_cover side hn hr
    have hscaled := P.tail_cell side i hrtail hri
    have hrhost : P.n05TailScale side * r ∈ P.reference.cells j :=
      hcarrier ⟨mul_lt_mul_of_pos_left hr.1 (P.n05TailScale_pos side),
        mul_lt_mul_of_pos_left hr.2 (P.n05TailScale_pos side)⟩
    have hindex : P.reference.cellIndex i = max (P.retainedIndex + k) P.indexFloor := by
      rw [P.cellIndex, hi]
    have hw := hN j i (P.n05TailScale side * r) hrhost hscaled
    rw [hindex] at hw
    have hf : |((max (P.retainedIndex + k) P.indexFloor : ℕ) : ℝ) -
        P.reference.cellIndex (morseTailIndex side k)| ≤
        |(P.retainedIndex : ℝ) - P.selected.chain.index| := by
      rw [P.n05_tail_slot_index hraw side k]
      exact P.n05_tail_floor_shift k
    calc
      |(P.reference.cellIndex j : ℝ) - P.reference.cellIndex (morseTailIndex side k)| ≤
          |(P.reference.cellIndex j : ℝ) -
            ((max (P.retainedIndex + k) P.indexFloor : ℕ) : ℝ)| +
          |((max (P.retainedIndex + k) P.indexFloor : ℕ) : ℝ) -
            P.reference.cellIndex (morseTailIndex side k)| := abs_sub_le _ _ _
      _ ≤ (N : ℝ) + |(P.retainedIndex : ℝ) - P.selected.chain.index| := add_le_add hw hf
      _ ≤ B := by
        dsimp only [B]
        linarith only [abs_nonneg ((P.reference.cellIndex j₀ : ℝ) - P.reference.cellIndex 0)]

/-- The explicit near-tag enumeration works for every actual carrier map,
with a single constant independent of that map. -/
theorem exists_n05_negativeEnumeration_carrier_index_bound (hq : 0 < q)
    (hraw : (P.selected.family P.selected.sigma).cellIndex =
      morseTwoTailAt P.selected.chain.index (fun _ k => P.selected.chain.index + k)) :
    ∃ e : ℕ ≃ {p : ℝ × ℝ // NegativeRadialComponent P.reference p.1 p.2},
      ∃ B : ℝ, 0 < B ∧
      ∀ host : {p : ℝ × ℝ // NegativeRadialComponent P.reference p.1 p.2} → ℕ,
        (∀ J : {p : ℝ × ℝ // NegativeRadialComponent P.reference p.1 p.2},
          Ioo J.val.1 J.val.2 ⊆ P.reference.cells (host J)) →
        ∀ m, |(P.reference.cellIndex (host (e m)) : ℝ) - P.reference.cellIndex m| ≤ B := by
  obtain ⟨B, hB, hbound⟩ := P.n05NegativeComponentAt_carrier_index_bound hq hraw
  refine ⟨P.n05NegativeEnumeration hq, B, hB, fun host hhost m => ?_⟩
  apply hbound m (host (P.n05NegativeEnumeration hq m))
  simpa only [n05NegativeEnumeration_apply] using hhost (P.n05NegativeEnumeration hq m)

end ContinuousFlexibility.Radial.SeedReferenceConstruction
