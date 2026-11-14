module

public import ContinuousFlexibility.Analysis.N04BufferedSubdivision
public import ContinuousFlexibility.Analysis.N04PositiveNormalizationBuffer

/-!
# Positive pieces with a buffered normalization region

Every positive component receives a central interval and two dyadic tails.
The resulting family has compactly interior closed pieces and covers the
positive region outside a countable set. Only central pieces meet the
normalization region. All choices are reference-only.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

abbrev N04BufferedPositiveIndex (a b : ℝ) (f : ℝ → ℝ) : Type :=
  N04PositiveComponent a b f × N04BufferedIndex

def n04BufferedPositiveLeft {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (i : N04BufferedPositiveIndex a b f) : ℝ :=
  n04BufferedLeft (n04PositiveLeft i.1) (B.centerLeft i.1)
    (B.centerRight i.1) (n04PositiveRight i.1) i.2

def n04BufferedPositiveRight {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (i : N04BufferedPositiveIndex a b f) : ℝ :=
  n04BufferedRight (n04PositiveLeft i.1) (B.centerLeft i.1)
    (B.centerRight i.1) (n04PositiveRight i.1) i.2

def n04BufferedPositiveExceptional {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) : Set ℝ :=
  ⋃ i, n04BufferedExceptional (n04PositiveLeft i) (B.centerLeft i)
    (B.centerRight i) (n04PositiveRight i)

theorem N04PositiveNormalizationBuffer.center_lt
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (i : N04PositiveComponent a b f) :
    B.centerLeft i < B.centerRight i :=
  (B.ordered i).2.1.trans ((B.ordered i).2.2.1.trans (B.ordered i).2.2.2.1)

theorem n04_bufferedPositive_bounds
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (i : N04BufferedPositiveIndex a b f) :
    n04PositiveLeft i.1 < n04BufferedPositiveLeft B i ∧
      n04BufferedPositiveLeft B i < n04BufferedPositiveRight B i ∧
      n04BufferedPositiveRight B i < n04PositiveRight i.1 :=
  n04_buffered_bounds (B.ordered i.1).1 (B.center_lt i.1) (B.ordered i.1).2.2.2.2 i.2

theorem n04_bufferedPositive_closed_subset_component
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (hf : Continuous f)
    (i : N04BufferedPositiveIndex a b f) :
    Icc (n04BufferedPositiveLeft B i) (n04BufferedPositiveRight B i) ⊆ i.1.val := by
  rw [n04PositiveComponent_eq_Ioo hf i.1]
  exact n04_buffered_closed_subset (B.ordered i.1).1
    (B.center_lt i.1) (B.ordered i.1).2.2.2.2 i.2

theorem n04_bufferedPositive_closed_positive
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (hf : Continuous f)
    (i : N04BufferedPositiveIndex a b f) :
    Icc (n04BufferedPositiveLeft B i) (n04BufferedPositiveRight B i) ⊆
      n04PositiveRegion a b f :=
  (n04_bufferedPositive_closed_subset_component B hf i).trans (n04PositiveComponent_subset i.1)

theorem n04_bufferedPositive_index_unique
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (hf : Continuous f)
    {i j : N04BufferedPositiveIndex a b f} {r : ℝ}
    (hi : r ∈ Ioo (n04BufferedPositiveLeft B i) (n04BufferedPositiveRight B i))
    (hj : r ∈ Ioo (n04BufferedPositiveLeft B j) (n04BufferedPositiveRight B j)) : i = j := by
  have hri := n04_bufferedPositive_closed_subset_component B hf i ⟨hi.1.le, hi.2.le⟩
  have hrj := n04_bufferedPositive_closed_subset_component B hf j ⟨hj.1.le, hj.2.le⟩
  have hij : i.1 = j.1 := Subtype.ext
    ((n04PositiveComponent_eq_component i.1 hri).trans
      (n04PositiveComponent_eq_component j.1 hrj).symm)
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  change i = j at hij
  subst j
  exact Prod.ext rfl (n04_buffered_index_unique (B.ordered i).1
    (B.center_lt i) (B.ordered i).2.2.2.2 hi hj)

theorem n04_bufferedPositive_exceptional_countable
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (hf : Continuous f) :
    (n04BufferedPositiveExceptional B).Countable := by
  letI := n04PositiveComponent_countable (a := a) (b := b) hf
  exact Set.countable_iUnion (fun i => n04_buffered_exceptional_countable
    (n04PositiveLeft i) (B.centerLeft i) (B.centerRight i) (n04PositiveRight i))

theorem n04_bufferedPositive_cover
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (hf : Continuous f)
    {r : ℝ} (hr : r ∈ n04PositiveRegion a b f) (hE : r ∉ n04BufferedPositiveExceptional B) :
    ∃! i : N04BufferedPositiveIndex a b f,
      r ∈ Ioo (n04BufferedPositiveLeft B i) (n04BufferedPositiveRight B i) := by
  obtain ⟨i, hi, _⟩ := (n04PositiveComponent_existsUnique_interval_iff hf r).mpr hr
  have hEi : r ∉ n04BufferedExceptional (n04PositiveLeft i) (B.centerLeft i)
      (B.centerRight i) (n04PositiveRight i) := fun h => hE (mem_iUnion.mpr ⟨i, h⟩)
  obtain ⟨k, hk, _⟩ := n04_buffered_cover (B.ordered i).1
    (B.center_lt i) (B.ordered i).2.2.2.2 hi hEi
  exact ⟨(i, k), hk, fun j hj => n04_bufferedPositive_index_unique B hf hj hk⟩

/-- A positive piece meeting the chosen normalization region is its
component's central piece. Its two collar buffers are strictly positive. -/
theorem n04_bufferedPositive_eq_central_of_mem_region
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (hf : Continuous f)
    {i : N04BufferedPositiveIndex a b f} {r : ℝ}
    (hi : r ∈ Ioo (n04BufferedPositiveLeft B i) (n04BufferedPositiveRight B i))
    (hN : r ∈ B.region) : i.2 = none := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hN
  have ho := B.ordered j
  have hrj : r ∈ j.val := (n04PositiveComponent_mem_iff hf j).mpr
    ⟨(ho.1.trans ho.2.1).trans hj.1, hj.2.trans (ho.2.2.2.1.trans ho.2.2.2.2)⟩
  have hri := n04_bufferedPositive_closed_subset_component B hf i ⟨hi.1.le, hi.2.le⟩
  have hij : i.1 = j := Subtype.ext
    ((n04PositiveComponent_eq_component i.1 hri).trans
      (n04PositiveComponent_eq_component j hrj).symm)
  subst j
  by_contra hnot
  have hdis := n04_buffered_noncentral_disjoint_middle (B.ordered i.1).1
    (B.center_lt i.1) (B.ordered i.1).2.2.2.2 hnot
  exact Set.disjoint_left.mp hdis hi
    ⟨((B.ordered i.1).2.1.trans hj.1).le, (hj.2.trans (B.ordered i.1).2.2.2.1).le⟩

end ContinuousFlexibility.Analysis
