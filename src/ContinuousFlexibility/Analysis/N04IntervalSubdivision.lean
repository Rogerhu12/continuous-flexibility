module

public import ContinuousFlexibility.Radial.MorseChainLocalGluing
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Countable subdivisions with interior closed intervals

An open bounded interval is partitioned, outside an explicit countable
grid, into the adjacent dyadic intervals approaching its two endpoints.
Every closed interval of the subdivision stays strictly inside the
original interval. This permits positive reference height factors to be
used on the closed pieces even when the original component reaches an
outer endpoint of the annulus.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology

/-- The descending dyadic grid from the midpoint towards the left endpoint. -/
def n04SubdivisionGrid (a b : ℝ) (n : ℕ) : ℝ :=
  a + (b - a) * (1 / 2 : ℝ) ^ (n + 1)

/-- `false` indexes the left half and `true` its reflection in the midpoint. -/
def n04SubdivisionLeft (a b : ℝ) (i : Bool × ℕ) : ℝ :=
  if i.1 then a + b - n04SubdivisionGrid a b i.2
  else n04SubdivisionGrid a b (i.2 + 1)

def n04SubdivisionRight (a b : ℝ) (i : Bool × ℕ) : ℝ :=
  if i.1 then a + b - n04SubdivisionGrid a b (i.2 + 1)
  else n04SubdivisionGrid a b i.2

/-- The endpoints shared by the adjacent intervals, including the midpoint. -/
def n04SubdivisionExceptional (a b : ℝ) : Set ℝ :=
  Set.range (n04SubdivisionGrid a b) ∪
    Set.range (fun n => a + b - n04SubdivisionGrid a b n)

theorem n04_subdivision_grid_zero (a b : ℝ) :
    n04SubdivisionGrid a b 0 = (a + b) / 2 := by
  unfold n04SubdivisionGrid
  norm_num
  ring

theorem n04_subdivision_grid_strictAnti {a b : ℝ} (hab : a < b) :
    StrictAnti (n04SubdivisionGrid a b) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have hp : 0 < (b - a) * (1 / 2 : ℝ) ^ (n + 1) :=
    mul_pos (sub_pos.mpr hab) (pow_pos (by norm_num) _)
  unfold n04SubdivisionGrid
  rw [pow_succ]
  nlinarith only [hp]

theorem n04_subdivision_grid_gt_left {a b : ℝ} (hab : a < b) (n : ℕ) :
    a < n04SubdivisionGrid a b n := by
  have hp : 0 < (b - a) * (1 / 2 : ℝ) ^ (n + 1) :=
    mul_pos (sub_pos.mpr hab) (pow_pos (by norm_num) _)
  unfold n04SubdivisionGrid
  linarith only [hp]

theorem n04_subdivision_grid_le_midpoint {a b : ℝ} (hab : a < b) (n : ℕ) :
    n04SubdivisionGrid a b n ≤ (a + b) / 2 := by
  rw [← n04_subdivision_grid_zero a b]
  exact (n04_subdivision_grid_strictAnti hab).antitone (Nat.zero_le n)

theorem n04_subdivision_grid_lt_right {a b : ℝ} (hab : a < b) (n : ℕ) :
    n04SubdivisionGrid a b n < b := by
  have hm := n04_subdivision_grid_le_midpoint hab n
  linarith only [hm, hab]

theorem n04_subdivision_grid_tendsto (a b : ℝ) :
    Tendsto (n04SubdivisionGrid a b) atTop (𝓝 a) := by
  change Tendsto (fun n : ℕ => a + (b - a) * (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 a)
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    simpa only [pow_succ, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2 : ℝ)
  simpa only [mul_zero, add_zero] using
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hp) :
      Tendsto (fun n : ℕ => a + (b - a) * (1 / 2 : ℝ) ^ (n + 1))
        atTop (𝓝 (a + (b - a) * 0)))

/-- Both endpoints of every nonempty piece lie strictly inside the given interval. -/
theorem n04_subdivision_bounds {a b : ℝ} (hab : a < b) (i : Bool × ℕ) :
    a < n04SubdivisionLeft a b i ∧
      n04SubdivisionLeft a b i < n04SubdivisionRight a b i ∧
      n04SubdivisionRight a b i < b := by
  rcases i with ⟨side, n⟩
  have hstep := n04_subdivision_grid_strictAnti hab (Nat.lt_succ_self n)
  cases side
  · change a < n04SubdivisionGrid a b (n + 1) ∧
      n04SubdivisionGrid a b (n + 1) < n04SubdivisionGrid a b n ∧
      n04SubdivisionGrid a b n < b
    exact ⟨n04_subdivision_grid_gt_left hab (n + 1), hstep,
      n04_subdivision_grid_lt_right hab n⟩
  · change a < a + b - n04SubdivisionGrid a b n ∧
      a + b - n04SubdivisionGrid a b n < a + b - n04SubdivisionGrid a b (n + 1) ∧
      a + b - n04SubdivisionGrid a b (n + 1) < b
    have hn := n04_subdivision_grid_lt_right hab n
    have hn' := n04_subdivision_grid_gt_left hab (n + 1)
    exact ⟨by linarith only [hn], by linarith only [hstep], by linarith only [hn']⟩

theorem n04_subdivision_closed_subset {a b : ℝ} (hab : a < b) (i : Bool × ℕ) :
    Icc (n04SubdivisionLeft a b i) (n04SubdivisionRight a b i) ⊆ Ioo a b := by
  intro r hr
  have hi := n04_subdivision_bounds hab i
  exact ⟨hi.1.trans_le hr.1, hr.2.trans_lt hi.2.2⟩

private theorem n04_decreasing_gap_index_unique {f : ℕ → ℝ} (hf : StrictAnti f)
    {m n : ℕ} {r : ℝ} (hm : r ∈ Ioo (f (m + 1)) (f m))
    (hn : r ∈ Ioo (f (n + 1)) (f n)) : m = n := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hh := hf.antitone (Nat.succ_le_of_lt h)
    linarith only [hh, hm.1, hn.2]
  · have hh := hf.antitone (Nat.succ_le_of_lt h)
    linarith only [hh, hn.1, hm.2]

theorem n04_subdivision_index_unique {a b r : ℝ} (hab : a < b)
    {i j : Bool × ℕ}
    (hi : r ∈ Ioo (n04SubdivisionLeft a b i) (n04SubdivisionRight a b i))
    (hj : r ∈ Ioo (n04SubdivisionLeft a b j) (n04SubdivisionRight a b j)) : i = j := by
  rcases i with ⟨si, m⟩
  rcases j with ⟨sj, n⟩
  have hm := n04_subdivision_grid_le_midpoint hab m
  have hn := n04_subdivision_grid_le_midpoint hab n
  cases si <;> cases sj
  · change r ∈ Ioo (n04SubdivisionGrid a b (m + 1)) (n04SubdivisionGrid a b m) at hi
    change r ∈ Ioo (n04SubdivisionGrid a b (n + 1)) (n04SubdivisionGrid a b n) at hj
    exact Prod.ext rfl
      (n04_decreasing_gap_index_unique (n04_subdivision_grid_strictAnti hab) hi hj)
  · change r ∈ Ioo (n04SubdivisionGrid a b (m + 1)) (n04SubdivisionGrid a b m) at hi
    change r ∈ Ioo (a + b - n04SubdivisionGrid a b n)
      (a + b - n04SubdivisionGrid a b (n + 1)) at hj
    exfalso
    linarith only [hi.2, hj.1, hm, hn]
  · change r ∈ Ioo (a + b - n04SubdivisionGrid a b m)
      (a + b - n04SubdivisionGrid a b (m + 1)) at hi
    change r ∈ Ioo (n04SubdivisionGrid a b (n + 1)) (n04SubdivisionGrid a b n) at hj
    exfalso
    linarith only [hi.1, hj.2, hm, hn]
  · change r ∈ Ioo (a + b - n04SubdivisionGrid a b m)
      (a + b - n04SubdivisionGrid a b (m + 1)) at hi
    change r ∈ Ioo (a + b - n04SubdivisionGrid a b n)
      (a + b - n04SubdivisionGrid a b (n + 1)) at hj
    have hi' : a + b - r ∈
        Ioo (n04SubdivisionGrid a b (m + 1)) (n04SubdivisionGrid a b m) :=
      ⟨by linarith only [hi.2], by linarith only [hi.1]⟩
    have hj' : a + b - r ∈
        Ioo (n04SubdivisionGrid a b (n + 1)) (n04SubdivisionGrid a b n) :=
      ⟨by linarith only [hj.2], by linarith only [hj.1]⟩
    exact Prod.ext rfl
      (n04_decreasing_gap_index_unique (n04_subdivision_grid_strictAnti hab) hi' hj')

theorem n04_subdivision_pairwise_disjoint {a b : ℝ} (hab : a < b) :
    Pairwise (fun i j : Bool × ℕ =>
      Disjoint (Ioo (n04SubdivisionLeft a b i) (n04SubdivisionRight a b i))
        (Ioo (n04SubdivisionLeft a b j) (n04SubdivisionRight a b j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro r hi hj
  exact hij (n04_subdivision_index_unique hab hi hj)

theorem n04_subdivision_exceptional_countable (a b : ℝ) :
    (n04SubdivisionExceptional a b).Countable :=
  (Set.countable_range _).union (Set.countable_range _)

theorem n04_subdivision_exceptional_subset {a b : ℝ} (hab : a < b) :
    n04SubdivisionExceptional a b ⊆ Ioo a b := by
  rintro r (⟨n, rfl⟩ | ⟨n, rfl⟩)
  · exact ⟨n04_subdivision_grid_gt_left hab n, n04_subdivision_grid_lt_right hab n⟩
  · have hn := n04_subdivision_grid_gt_left hab n
    have hn' := n04_subdivision_grid_lt_right hab n
    exact ⟨by linarith only [hn'], by linarith only [hn]⟩

theorem n04_subdivision_exceptional_volume (a b : ℝ) :
    volume (n04SubdivisionExceptional a b) = 0 :=
  (n04_subdivision_exceptional_countable a b).measure_zero volume

private theorem n04_subdivision_left_cover {a b r : ℝ} (hab : a < b)
    (har : a < r) (hr : r < (a + b) / 2)
    (hgrid : r ∉ Set.range (n04SubdivisionGrid a b)) :
    ∃ n : ℕ, r ∈ Ioo (n04SubdivisionGrid a b (n + 1)) (n04SubdivisionGrid a b n) := by
  have hr₀ : r < n04SubdivisionGrid a b 0 := by
    rwa [n04_subdivision_grid_zero]
  obtain ⟨n, hn⟩ := Radial.morse_outward_block_exists
    (enter := fun n => -n04SubdivisionGrid a b n) (endpoint := -a) (x := -r)
    (n04_subdivision_grid_tendsto a b).neg
    (by linarith only [hr₀]) (by linarith only [har])
  have hlo : n04SubdivisionGrid a b (n + 1) < r := by linarith only [hn.2]
  have hhi : r ≤ n04SubdivisionGrid a b n := by linarith only [hn.1]
  have hne : r ≠ n04SubdivisionGrid a b n := fun h => hgrid ⟨n, h.symm⟩
  exact ⟨n, hlo, (lt_or_eq_of_le hhi).resolve_right hne⟩

theorem n04_subdivision_cover {a b r : ℝ} (hab : a < b) (hr : r ∈ Ioo a b)
    (hE : r ∉ n04SubdivisionExceptional a b) :
    ∃! i : Bool × ℕ,
      r ∈ Ioo (n04SubdivisionLeft a b i) (n04SubdivisionRight a b i) := by
  have hleft : r ∉ Set.range (n04SubdivisionGrid a b) :=
    fun h => hE (Or.inl h)
  have hright : r ∉ Set.range (fun n => a + b - n04SubdivisionGrid a b n) :=
    fun h => hE (Or.inr h)
  have hex : ∃ i : Bool × ℕ,
      r ∈ Ioo (n04SubdivisionLeft a b i) (n04SubdivisionRight a b i) := by
    rcases lt_trichotomy r ((a + b) / 2) with h | h | h
    · obtain ⟨n, hn⟩ := n04_subdivision_left_cover hab hr.1 h hleft
      exact ⟨(false, n), hn⟩
    · exact (hleft ⟨0, (n04_subdivision_grid_zero a b).trans h.symm⟩).elim
    · have hgrid : a + b - r ∉ Set.range (n04SubdivisionGrid a b) := by
        rintro ⟨n, hn⟩
        apply hright
        refine ⟨n, ?_⟩
        linarith only [hn]
      obtain ⟨n, hn⟩ := n04_subdivision_left_cover hab
        (r := a + b - r) (by linarith only [hr.2]) (by linarith only [h]) hgrid
      refine ⟨(true, n), ?_⟩
      change a + b - n04SubdivisionGrid a b n < r ∧
        r < a + b - n04SubdivisionGrid a b (n + 1)
      exact ⟨by linarith only [hn.2], by linarith only [hn.1]⟩
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, hi, fun j hj => n04_subdivision_index_unique hab hj hi⟩

/-- A complete countable subdivision whose closed pieces are interior. -/
theorem n04_interval_subdivision {a b : ℝ} (hab : a < b) :
    ∃ left right : Bool × ℕ → ℝ, ∃ E : Set ℝ,
      E.Countable ∧ E ⊆ Ioo a b ∧
      (∀ i, a < left i ∧ left i < right i ∧ right i < b) ∧
      Pairwise (fun i j => Disjoint (Ioo (left i) (right i)) (Ioo (left j) (right j))) ∧
      ∀ r ∈ Ioo a b \ E, ∃! i, r ∈ Ioo (left i) (right i) := by
  refine ⟨n04SubdivisionLeft a b, n04SubdivisionRight a b, n04SubdivisionExceptional a b,
    n04_subdivision_exceptional_countable a b, n04_subdivision_exceptional_subset hab,
    n04_subdivision_bounds hab, n04_subdivision_pairwise_disjoint hab, ?_⟩
  intro r hr
  exact n04_subdivision_cover hab hr.1 hr.2

end ContinuousFlexibility.Analysis
