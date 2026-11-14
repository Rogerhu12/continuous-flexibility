module

public import ContinuousFlexibility.Analysis.N01aCellCoarseningSeries
public import ContinuousFlexibility.Statements.Radial
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Grouping radial cells by scale and endpoint

Each original cell chooses one of its points. Its tag records its original
scale and the endpoint nearest that point. The nonempty tags are enumerated
in increasing order. Thus there are at most two coarse cells at each scale,
while every original localizer belongs to exactly one finite group.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped BigOperators

/-- The scale and the side of a chosen point, encoded as one natural number. -/
def n01aCellTag (D : ReferenceData) (p : ℕ → ℝ) (i : ℕ) : ℕ :=
  2 * D.cellIndex i + if p i ≤ (D.a + D.b) / 2 then 0 else 1

theorem n01aCellTag_div_two (D : ReferenceData) (p : ℕ → ℝ) (i : ℕ) :
    n01aCellTag D p i / 2 = D.cellIndex i := by
  unfold n01aCellTag
  split <;> omega

theorem n01aCellTag_fiber_finite (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (j : ℕ) :
    {i | n01aCellTag D p i = j}.Finite := by
  apply (hproper (j / 2)).subset
  intro i hi
  have he := congrArg (fun n : ℕ => n / 2) hi
  rw [n01aCellTag_div_two] at he
  exact he.le

theorem n01a_range_infinite_of_finite_fibers (f : ℕ → ℕ)
    (hf : ∀ j, {i | f i = j}.Finite) : (Set.range f).Infinite := by
  intro hr
  have hu : (Set.univ : Set ℕ).Finite := by
    apply (hr.biUnion (fun j _ => hf j)).subset
    intro i _
    exact Set.mem_iUnion.mpr ⟨f i,
      Set.mem_iUnion.mpr ⟨Set.mem_range_self i, rfl⟩⟩
  exact Set.infinite_univ hu

def n01aCellOrder (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) :
    ℕ ≃o Set.range (n01aCellTag D p) :=
  @Nat.Subtype.orderIsoOfNat (Set.range (n01aCellTag D p))
    (n01a_range_infinite_of_finite_fibers _
      (n01aCellTag_fiber_finite D p hproper)).to_subtype

/-- The unique new cell containing a given old cell. -/
def n01aCellGrouping (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (i : ℕ) : ℕ :=
  (n01aCellOrder D p hproper).symm ⟨n01aCellTag D p i, Set.mem_range_self i⟩

theorem n01aCellOrder_grouping (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (i : ℕ) :
    ((n01aCellOrder D p hproper) (n01aCellGrouping D p hproper i) : ℕ) =
      n01aCellTag D p i := by
  simp only [n01aCellGrouping, OrderIso.apply_symm_apply]

theorem n01aCellGrouping_surjective (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) :
    Function.Surjective (n01aCellGrouping D p hproper) := by
  intro j
  obtain ⟨i, hi⟩ := ((n01aCellOrder D p hproper) j).property
  refine ⟨i, (n01aCellOrder D p hproper).injective ?_⟩
  apply Subtype.ext
  exact (n01aCellOrder_grouping D p hproper i).trans hi

theorem n01aCellGrouping_fiber_finite (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (j : ℕ) :
    {i | n01aCellGrouping D p hproper i = j}.Finite := by
  apply (n01aCellTag_fiber_finite D p hproper
    ((n01aCellOrder D p hproper) j)).subset
  intro i hi
  exact (n01aCellOrder_grouping D p hproper i).symm.trans
    (congrArg (fun k => ((n01aCellOrder D p hproper) k : ℕ)) hi)

def n01aCellGroupIndex (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (j : ℕ) : ℕ :=
  ((n01aCellOrder D p hproper) j : ℕ) / 2

theorem n01aCellGroupIndex_grouping (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (i : ℕ) :
    n01aCellGroupIndex D p hproper (n01aCellGrouping D p hproper i) =
      D.cellIndex i := by
  rw [n01aCellGroupIndex, n01aCellOrder_grouping, n01aCellTag_div_two]

theorem n01aCellGroupIndex_lower (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (j : ℕ) :
    j ≤ 2 * n01aCellGroupIndex D p hproper j + 1 := by
  have hm : StrictMono (fun k => ((n01aCellOrder D p hproper) k : ℕ)) :=
    (Subtype.strictMono_coe _).comp (n01aCellOrder D p hproper).strictMono
  unfold n01aCellGroupIndex
  calc
    j ≤ ((n01aCellOrder D p hproper) j : ℕ) := hm.id_le j
    _ ≤ 2 * (((n01aCellOrder D p hproper) j : ℕ) / 2) + 1 := by omega

theorem n01aCellGroupIndex_proper (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (N : ℕ) :
    {j | n01aCellGroupIndex D p hproper j ≤ N}.Finite := by
  apply (Set.finite_le_nat (2 * N + 1)).subset
  intro j hj
  exact (n01aCellGroupIndex_lower D p hproper j).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hj) 1)

/-- One original cell in each nonempty group, used for the trace scaffold. -/
def n01aCellRepresentative (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (j : ℕ) : ℕ :=
  (n01aCellGrouping_surjective D p hproper j).choose

theorem n01aCellRepresentative_spec (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (j : ℕ) :
    n01aCellGrouping D p hproper (n01aCellRepresentative D p hproper j) = j :=
  (n01aCellGrouping_surjective D p hproper j).choose_spec

theorem n01aCellRepresentative_injective (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) :
    Function.Injective (n01aCellRepresentative D p hproper) := by
  intro i j hij
  have h := congrArg (n01aCellGrouping D p hproper) hij
  simpa only [n01aCellRepresentative_spec] using h

/-- The physical fields are unchanged. Only cells, localizers and their enumeration change. -/
def n01aCoarseReference (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) : ReferenceData :=
  { D with
    cells := fun j => ⋃ i ∈ n01aCoarseningFiber (n01aCellGrouping D p hproper)
      (n01aCellGrouping_fiber_finite D p hproper) j, D.cells i
    localizer := n01aCoarseLocalizer (n01aCellGrouping D p hproper)
      (n01aCellGrouping_fiber_finite D p hproper) D.localizer
    cellIndex := n01aCellGroupIndex D p hproper }

theorem n01aCoarseReference_mem_cell (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (j : ℕ) (r : ℝ) :
    r ∈ (n01aCoarseReference D p hproper).cells j ↔
      ∃ i, n01aCellGrouping D p hproper i = j ∧ r ∈ D.cells i := by
  simp only [n01aCoarseReference, Set.mem_iUnion, mem_n01aCoarseningFiber, exists_prop]

theorem n01aCoarseReference_cell_subset (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (i : ℕ) :
    D.cells i ⊆ (n01aCoarseReference D p hproper).cells
      (n01aCellGrouping D p hproper i) := by
  intro r hr
  exact (n01aCoarseReference_mem_cell D p hproper _ r).mpr ⟨i, rfl, hr⟩

theorem n01aCoarseReference_cell_nonempty (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite)
    (hne : ∀ i, (D.cells i).Nonempty) (j : ℕ) :
    ((n01aCoarseReference D p hproper).cells j).Nonempty := by
  obtain ⟨i, hi⟩ := n01aCellGrouping_surjective D p hproper j
  obtain ⟨r, hr⟩ := hne i
  exact ⟨r, (n01aCoarseReference_mem_cell D p hproper j r).mpr ⟨i, hi, hr⟩⟩

theorem n01aCoarseReference_cellIndex (D : ReferenceData) (p : ℕ → ℝ)
    (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite) (i j : ℕ)
    (hij : n01aCellGrouping D p hproper i = j) :
    (n01aCoarseReference D p hproper).cellIndex j = D.cellIndex i := by
  rw [← hij]
  exact n01aCellGroupIndex_grouping D p hproper i

end ContinuousFlexibility.Statements
