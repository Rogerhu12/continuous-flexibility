module

public import ContinuousFlexibility.Analysis.N01aPartitionGrouping

/-!
# Diameter of a group at one endpoint

The endpoint coordinate treats the two ends uniformly. A point of an old
cell is at most its diameter farther from the selected endpoint than the
cell's chosen point. Consequently every group has diameter at most twice
the original scale bound, including the finitely many central scales.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

def n01aEndpointOffset (D : ReferenceData) (left : Bool) (r : ℝ) : ℝ :=
  if left then r - D.a else D.b - r

theorem n01aEndpointOffset_nonneg (D : ReferenceData) (left : Bool) {r : ℝ}
    (hr : r ∈ radialCore D) : 0 ≤ n01aEndpointOffset D left r := by
  cases left <;> simp only [n01aEndpointOffset, Bool.false_eq_true, ↓reduceIte]
  · exact sub_nonneg.mpr hr.2.le
  · exact sub_nonneg.mpr hr.1.le

theorem n01aEndpointOffset_le (D : ReferenceData) (left : Bool) (r p : ℝ) :
    n01aEndpointOffset D left r ≤ n01aEndpointOffset D left p + |r - p| := by
  cases left <;> simp only [n01aEndpointOffset, Bool.false_eq_true, ↓reduceIte]
  · linarith only [neg_le_abs (r - p)]
  · linarith only [le_abs_self (r - p)]

theorem n01aEndpointOffset_nearest (D : ReferenceData) (left : Bool) (p : ℝ)
    (hleft : left = true ↔ p ≤ (D.a + D.b) / 2) :
    n01aEndpointOffset D left p = min (p - D.a) (D.b - p) := by
  cases left
  · have hp : ¬ p ≤ (D.a + D.b) / 2 := by simpa using hleft.symm
    simp only [n01aEndpointOffset, Bool.false_eq_true, ↓reduceIte]
    exact (min_eq_right (by linarith only [lt_of_not_ge hp])).symm
  · have hp : p ≤ (D.a + D.b) / 2 := hleft.mp rfl
    simp only [n01aEndpointOffset, ↓reduceIte]
    exact (min_eq_left (by linarith only [hp])).symm

theorem n01aEndpointOffset_interval (D : ReferenceData) (left : Bool) (R r : ℝ)
    (hr : 0 ≤ n01aEndpointOffset D left r ∧ n01aEndpointOffset D left r ≤ R) :
    r ∈ Icc (if left then D.a else D.b - R)
      (if left then D.a + R else D.b) := by
  cases left <;> simp only [n01aEndpointOffset, Bool.false_eq_true, ↓reduceIte] at hr ⊢
  all_goals constructor <;> linarith only [hr.1, hr.2]

theorem n01aCellTag_same_side (D : ReferenceData) (p : ℕ → ℝ) {i j : ℕ}
    (hij : n01aCellTag D p i = n01aCellTag D p j) :
    (p i ≤ (D.a + D.b) / 2 ↔ p j ≤ (D.a + D.b) / 2) := by
  have hindex := congrArg (fun n : ℕ => n / 2) hij
  simp only [n01aCellTag_div_two] at hindex
  unfold n01aCellTag at hij
  rw [hindex] at hij
  have hside := Nat.add_left_cancel hij
  by_cases hi : p i ≤ (D.a + D.b) / 2 <;>
    by_cases hj : p j ≤ (D.a + D.b) / 2
  · exact iff_of_true hi hj
  · norm_num [hi, hj] at hside
  · norm_num [hi, hj] at hside
  · exact iff_of_false hi hj

theorem n01a_cell_endpoint_bound (D : ReferenceData) (C : ℕ → ℝ)
    (hC : AccumulatingProfileBounds D C) (p : ℕ → ℝ)
    (hp : ∀ i, p i ∈ D.cells i) (i : ℕ) (left : Bool)
    (hleft : left = true ↔ p i ≤ (D.a + D.b) / 2) {r : ℝ} (hr : r ∈ D.cells i) :
    n01aEndpointOffset D left r ≤ 2 * C 0 * Real.exp (-(D.cellIndex i : ℝ) ^ 2) := by
  obtain ⟨_, _, _, _, _, _, hdist, _, _, _, hwidth, _⟩ := hC
  obtain ⟨l, h, hcell, hlen⟩ := hwidth i
  have hpr := hcell (hp i)
  have hrr := hcell hr
  have hdiff : |r - p i| ≤ C 0 * Real.exp (-(D.cellIndex i : ℝ) ^ 2) := by
    rw [abs_le]
    constructor <;> linarith only [hpr.1, hpr.2, hrr.1, hrr.2, hlen]
  have hnear := (hdist i (p i) (hp i)).2
  rw [← n01aEndpointOffset_nearest D left (p i) hleft] at hnear
  linarith only [n01aEndpointOffset_le D left r (p i), hnear, hdiff]

theorem n01aCoarseReference_diameter (D : ReferenceData) (C : ℕ → ℝ)
    (hC : AccumulatingProfileBounds D C) (p : ℕ → ℝ)
    (hp : ∀ i, p i ∈ D.cells i)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (j : ℕ) :
    ∃ l h : ℝ, (n01aCoarseReference D p hproper).cells j ⊆ Icc l h ∧
      h - l ≤ (2 * C 0) *
        Real.exp (-((n01aCoarseReference D p hproper).cellIndex j : ℝ) ^ 2) := by
  classical
  let k := n01aCellRepresentative D p hproper j
  let left : Bool := decide (p k ≤ (D.a + D.b) / 2)
  let R := (2 * C 0) *
    Real.exp (-((n01aCoarseReference D p hproper).cellIndex j : ℝ) ^ 2)
  have hk : n01aCellGrouping D p hproper k = j :=
    n01aCellRepresentative_spec D p hproper j
  refine ⟨if left then D.a else D.b - R,
    if left then D.a + R else D.b, ?_, ?_⟩
  · intro r hr
    obtain ⟨i, hi, hri⟩ := (n01aCoarseReference_mem_cell D p hproper j r).mp hr
    have htag : n01aCellTag D p i = n01aCellTag D p k := by
      rw [← n01aCellOrder_grouping D p hproper i,
        ← n01aCellOrder_grouping D p hproper k, hi, hk]
    have hleft : left = true ↔ p i ≤ (D.a + D.b) / 2 := by
      simpa only [left, decide_eq_true_eq] using (n01aCellTag_same_side D p htag).symm
    apply n01aEndpointOffset_interval
    refine ⟨n01aEndpointOffset_nonneg D left (hC.2.1.2.2.2.1 i hri), ?_⟩
    have hb := n01a_cell_endpoint_bound D C hC p hp i left hleft hri
    dsimp only [R]
    rw [n01aCoarseReference_cellIndex D p hproper i j hi]
    exact hb
  · change (if left then D.a + R else D.b) -
      (if left then D.a else D.b - R) ≤ R
    cases left <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

end ContinuousFlexibility.Statements
