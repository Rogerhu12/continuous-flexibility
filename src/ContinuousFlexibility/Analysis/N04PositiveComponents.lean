module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The positive components of a continuous radial coefficient

The indices are the distinct nonempty connected components of the positive
set in a bounded open interval. Each component is exactly the open interval
between its infimum and supremum. The family is countable, pairwise
disjoint, and covers the positive set exactly.

Endpoints are allowed to equal the endpoints of the ambient interval.
No claim of compact containment is implicit in this decomposition.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

/-- The positive part of a real coefficient inside the ambient interval. -/
def n04PositiveRegion (a b : ℝ) (f : ℝ → ℝ) : Set ℝ :=
  {r | r ∈ Ioo a b ∧ 0 < f r}

/-- Distinct component sets, rather than points that may name the same component. -/
def N04PositiveComponent (a b : ℝ) (f : ℝ → ℝ) : Type :=
  {V : Set ℝ // ∃ r ∈ n04PositiveRegion a b f,
    V = connectedComponentIn (n04PositiveRegion a b f) r}

variable {a b : ℝ} {f : ℝ → ℝ}

def n04PositiveLeft (i : N04PositiveComponent a b f) : ℝ := sInf i.val

def n04PositiveRight (i : N04PositiveComponent a b f) : ℝ := sSup i.val

theorem n04PositiveRegion_isOpen (hf : Continuous f) :
    IsOpen (n04PositiveRegion a b f) :=
  isOpen_Ioo.inter (isOpen_lt continuous_const hf)

theorem n04PositiveComponent_nonempty (i : N04PositiveComponent a b f) :
    i.val.Nonempty := by
  obtain ⟨r, hr, hV⟩ := i.property
  rw [hV]
  exact ⟨r, mem_connectedComponentIn hr⟩

theorem n04PositiveComponent_subset (i : N04PositiveComponent a b f) :
    i.val ⊆ n04PositiveRegion a b f := by
  obtain ⟨r, hr, hV⟩ := i.property
  rw [hV]
  exact connectedComponentIn_subset _ _

theorem n04PositiveComponent_isConnected (i : N04PositiveComponent a b f) :
    IsConnected i.val := by
  obtain ⟨r, hr, hV⟩ := i.property
  rw [hV]
  exact isConnected_connectedComponentIn_iff.mpr hr

/-- An open subset of the real line has open connected components. The
interval neighborhood proof keeps the construction independent of any
choice of a component enumeration. -/
private theorem n04_isOpen_connectedComponentIn_real {U : Set ℝ}
    (hU : IsOpen U) (r : ℝ) : IsOpen (connectedComponentIn U r) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hxU : x ∈ U := connectedComponentIn_subset U r hx
  obtain ⟨l, u, hxI, hIU⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hxU)
  rw [connectedComponentIn_eq hx]
  exact mem_of_superset (Ioo_mem_nhds hxI.1 hxI.2)
    (isPreconnected_Ioo.subset_connectedComponentIn hxI hIU)

theorem n04PositiveComponent_isOpen (hf : Continuous f)
    (i : N04PositiveComponent a b f) : IsOpen i.val := by
  obtain ⟨r, hr, hV⟩ := i.property
  rw [hV]
  exact n04_isOpen_connectedComponentIn_real (n04PositiveRegion_isOpen hf) r

theorem n04PositiveComponent_eq_component (i : N04PositiveComponent a b f)
    {r : ℝ} (hr : r ∈ i.val) :
    i.val = connectedComponentIn (n04PositiveRegion a b f) r := by
  obtain ⟨x, hx, hV⟩ := i.property
  exact hV.trans (connectedComponentIn_eq (hV ▸ hr))

theorem n04PositiveComponent_pairwiseDisjoint :
    Pairwise (fun i j : N04PositiveComponent a b f => Disjoint i.val j.val) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro r hri hrj
  apply hij
  exact Subtype.ext ((n04PositiveComponent_eq_component i hri).trans
    (n04PositiveComponent_eq_component j hrj).symm)

theorem n04PositiveComponent_countable (hf : Continuous f) :
    Countable (N04PositiveComponent a b f) :=
  (n04PositiveComponent_pairwiseDisjoint (a := a) (b := b) (f := f)).countable_of_isOpen_disjoint
    (n04PositiveComponent_isOpen hf) n04PositiveComponent_nonempty

private theorem n04_open_connected_eq_Ioo {V : Set ℝ}
    (hopen : IsOpen V) (hconn : IsConnected V)
    (hbelow : BddBelow V) (habove : BddAbove V) :
    V = Ioo (sInf V) (sSup V) := by
  apply Set.Subset.antisymm ?_ (hconn.Ioo_csInf_csSup_subset hbelow habove)
  intro x hx
  obtain ⟨l, u, hxI, hIV⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hx)
  obtain ⟨y, hly, hyx⟩ := exists_between hxI.1
  obtain ⟨z, hxz, hzu⟩ := exists_between hxI.2
  have hyV : y ∈ V := hIV ⟨hly, hyx.trans hxI.2⟩
  have hzV : z ∈ V := hIV ⟨hxI.1.trans hxz, hzu⟩
  exact ⟨(csInf_le hbelow hyV).trans_lt hyx,
    hxz.trans_le (le_csSup habove hzV)⟩

theorem n04PositiveComponent_eq_Ioo (hf : Continuous f)
    (i : N04PositiveComponent a b f) :
    i.val = Ioo (n04PositiveLeft i) (n04PositiveRight i) := by
  apply n04_open_connected_eq_Ioo (n04PositiveComponent_isOpen hf i)
    (n04PositiveComponent_isConnected i)
  · exact ⟨a, fun r hr => (n04PositiveComponent_subset i hr).1.1.le⟩
  · exact ⟨b, fun r hr => (n04PositiveComponent_subset i hr).1.2.le⟩

theorem n04PositiveComponent_bounds (hf : Continuous f)
    (i : N04PositiveComponent a b f) :
    a ≤ n04PositiveLeft i ∧ n04PositiveLeft i < n04PositiveRight i ∧
      n04PositiveRight i ≤ b := by
  have hne := n04PositiveComponent_nonempty i
  refine ⟨le_csInf hne (fun r hr => (n04PositiveComponent_subset i hr).1.1.le), ?_,
    csSup_le hne (fun r hr => (n04PositiveComponent_subset i hr).1.2.le)⟩
  obtain ⟨r, hr⟩ := hne
  rw [n04PositiveComponent_eq_Ioo hf i] at hr
  exact hr.1.trans hr.2

theorem n04PositiveComponent_mem_iff (hf : Continuous f)
    (i : N04PositiveComponent a b f) {r : ℝ} :
    r ∈ i.val ↔ n04PositiveLeft i < r ∧ r < n04PositiveRight i := by
  simp only [n04PositiveComponent_eq_Ioo hf i, Set.mem_Ioo]

theorem n04PositiveComponent_interval_subset (hf : Continuous f)
    (i : N04PositiveComponent a b f) :
    Ioo (n04PositiveLeft i) (n04PositiveRight i) ⊆ Ioo a b := by
  rw [← n04PositiveComponent_eq_Ioo hf i]
  exact fun r hr => (n04PositiveComponent_subset i hr).1

theorem n04PositiveComponent_interval_pos (hf : Continuous f)
    (i : N04PositiveComponent a b f) {r : ℝ}
    (hr : r ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i)) : 0 < f r := by
  rw [← n04PositiveComponent_eq_Ioo hf i] at hr
  exact (n04PositiveComponent_subset i hr).2

theorem n04PositiveComponent_interval_pairwiseDisjoint (hf : Continuous f) :
    Pairwise (fun i j : N04PositiveComponent a b f =>
      Disjoint (Ioo (n04PositiveLeft i) (n04PositiveRight i))
        (Ioo (n04PositiveLeft j) (n04PositiveRight j))) := by
  intro i j hij
  rw [← n04PositiveComponent_eq_Ioo hf i, ← n04PositiveComponent_eq_Ioo hf j]
  exact n04PositiveComponent_pairwiseDisjoint hij

theorem n04PositiveComponent_existsUnique_mem_iff (r : ℝ) :
    (∃! i : N04PositiveComponent a b f, r ∈ i.val) ↔ r ∈ n04PositiveRegion a b f := by
  constructor
  · rintro ⟨i, hi, _⟩
    exact n04PositiveComponent_subset i hi
  · intro hr
    let i : N04PositiveComponent a b f :=
      ⟨connectedComponentIn (n04PositiveRegion a b f) r, r, hr, rfl⟩
    refine ⟨i, mem_connectedComponentIn hr, ?_⟩
    intro j hj
    apply Subtype.ext
    exact n04PositiveComponent_eq_component j hj

theorem n04PositiveComponent_existsUnique_interval_iff (hf : Continuous f) (r : ℝ) :
    (∃! i : N04PositiveComponent a b f,
      r ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i)) ↔
        r ∈ n04PositiveRegion a b f := by
  simp_rw [← n04PositiveComponent_eq_Ioo hf]
  exact n04PositiveComponent_existsUnique_mem_iff r

theorem n04PositiveComponent_iUnion_interval (hf : Continuous f) :
    (⋃ i : N04PositiveComponent a b f,
      Ioo (n04PositiveLeft i) (n04PositiveRight i)) = n04PositiveRegion a b f := by
  apply Set.Subset.antisymm
  · intro r hr
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hr
    rw [← n04PositiveComponent_eq_Ioo hf i] at hi
    exact n04PositiveComponent_subset i hi
  · intro r hr
    obtain ⟨i, hi, _⟩ := (n04PositiveComponent_existsUnique_interval_iff hf r).mpr hr
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

end ContinuousFlexibility.Analysis
