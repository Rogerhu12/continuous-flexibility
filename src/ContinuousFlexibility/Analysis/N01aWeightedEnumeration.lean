module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Monotone.Basic

/-!
# Enumerating an infinite family in increasing weight

At each step choose a point of least natural weight outside the finite
prefix. Finite sublevel sets make the resulting injection surjective.
A lower bound on the number of low-weight points becomes an upper bound
on the weight of each enumerated point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

variable {α : Type*} [Infinite α] [DecidableEq α]

theorem n01a_exists_min_weight_outside (f : α → ℕ) (s : Finset α) :
    ∃ a, a ∉ s ∧ ∀ b, b ∉ s → f a ≤ f b := by
  classical
  have hex : ∃ n : ℕ, ∃ a, a ∉ s ∧ f a = n := by
    obtain ⟨a, ha⟩ := s.exists_notMem
    exact ⟨f a, a, ha, rfl⟩
  obtain ⟨a, ha, he⟩ := Nat.find_spec hex
  refine ⟨a, ha, fun b hb => ?_⟩
  rw [he]
  exact Nat.find_min' hex ⟨b, hb, rfl⟩

def n01aWeightNext (f : α → ℕ) (s : Finset α) : α :=
  (n01a_exists_min_weight_outside f s).choose

theorem n01aWeightNext_spec (f : α → ℕ) (s : Finset α) :
    n01aWeightNext f s ∉ s ∧ ∀ b, b ∉ s → f (n01aWeightNext f s) ≤ f b :=
  (n01a_exists_min_weight_outside f s).choose_spec

def n01aWeightPrefix (f : α → ℕ) : ℕ → Finset α
  | 0 => ∅
  | n + 1 => insert (n01aWeightNext f (n01aWeightPrefix f n)) (n01aWeightPrefix f n)

def n01aWeightEnumeration (f : α → ℕ) (n : ℕ) : α :=
  n01aWeightNext f (n01aWeightPrefix f n)

theorem n01aWeightPrefix_zero (f : α → ℕ) : n01aWeightPrefix f 0 = ∅ := rfl

theorem n01aWeightPrefix_succ (f : α → ℕ) (n : ℕ) :
    n01aWeightPrefix f (n + 1) =
      insert (n01aWeightEnumeration f n) (n01aWeightPrefix f n) := rfl

theorem n01aWeightEnumeration_notMem (f : α → ℕ) (n : ℕ) :
    n01aWeightEnumeration f n ∉ n01aWeightPrefix f n :=
  (n01aWeightNext_spec f (n01aWeightPrefix f n)).1

theorem n01aWeightPrefix_card (f : α → ℕ) (n : ℕ) :
    (n01aWeightPrefix f n).card = n := by
  induction n with
  | zero => simp only [n01aWeightPrefix_zero, Finset.card_empty]
  | succ n ih =>
    rw [n01aWeightPrefix_succ, Finset.card_insert_of_notMem
      (n01aWeightEnumeration_notMem f n), ih]

theorem n01aWeightPrefix_monotone (f : α → ℕ) : Monotone (n01aWeightPrefix f) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [n01aWeightPrefix_succ]
  exact Finset.subset_insert _ _

theorem n01aWeightEnumeration_mem_later (f : α → ℕ) {m n : ℕ} (hmn : m < n) :
    n01aWeightEnumeration f m ∈ n01aWeightPrefix f n := by
  apply n01aWeightPrefix_monotone f (Nat.succ_le_of_lt hmn)
  rw [n01aWeightPrefix_succ]
  exact Finset.mem_insert_self _ _

theorem n01aWeightEnumeration_injective (f : α → ℕ) :
    Function.Injective (n01aWeightEnumeration f) := by
  intro m n he
  rcases lt_trichotomy m n with h | h | h
  · have hm := n01aWeightEnumeration_mem_later f h
    rw [he] at hm
    exact False.elim (n01aWeightEnumeration_notMem f n hm)
  · exact h
  · have hn := n01aWeightEnumeration_mem_later f h
    rw [← he] at hn
    exact False.elim (n01aWeightEnumeration_notMem f m hn)

theorem n01aWeightEnumeration_surjective (f : α → ℕ)
    (hf : ∀ N : ℕ, {a | f a ≤ N}.Finite) :
    Function.Surjective (n01aWeightEnumeration f) := by
  intro a
  by_contra hnot
  have ha (n : ℕ) : n01aWeightEnumeration f n ≠ a := fun h => hnot ⟨n, h⟩
  have hout (n : ℕ) : a ∉ n01aWeightPrefix f n := by
    induction n with
    | zero => simp [n01aWeightPrefix_zero]
    | succ n ih =>
      rw [n01aWeightPrefix_succ, Finset.mem_insert]
      exact not_or.mpr ⟨(ha n).symm, ih⟩
  have hsub : Set.range (n01aWeightEnumeration f) ⊆ {b | f b ≤ f a} := by
    rintro b ⟨n, rfl⟩
    exact (n01aWeightNext_spec f (n01aWeightPrefix f n)).2 a (hout n)
  exact (Set.infinite_range_of_injective (n01aWeightEnumeration_injective f))
    ((hf (f a)).subset hsub)

def n01aWeightEquiv (f : α → ℕ) (hf : ∀ N : ℕ, {a | f a ≤ N}.Finite) : ℕ ≃ α :=
  Equiv.ofBijective (n01aWeightEnumeration f)
    ⟨n01aWeightEnumeration_injective f, n01aWeightEnumeration_surjective f hf⟩

theorem n01aWeightEnumeration_le_of_count (f : α → ℕ)
    (hf : ∀ N : ℕ, {a | f a ≤ N}.Finite) {n N : ℕ}
    (hcount : n < {a | f a ≤ N}.ncard) : f (n01aWeightEnumeration f n) ≤ N := by
  have hc : (n01aWeightPrefix f n).card < (hf N).toFinset.card := by
    rw [n01aWeightPrefix_card, ← Set.ncard_eq_toFinset_card _ (hf N)]
    exact hcount
  obtain ⟨a, ha, hout⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ((n01aWeightNext_spec f (n01aWeightPrefix f n)).2 a hout).trans
    ((hf N).mem_toFinset.mp ha)

/-- A finite-set density estimate is precisely what the greedy enumeration needs. -/
theorem n01aWeightEnumeration_le_of_finite_family (f : α → ℕ)
    (hf : ∀ N : ℕ, {a | f a ≤ N}.Finite) (S : Finset α) {n N : ℕ}
    (hcard : n < S.card) (hweight : ∀ a ∈ S, f a ≤ N) :
    f (n01aWeightEnumeration f n) ≤ N := by
  apply n01aWeightEnumeration_le_of_count f hf
  apply lt_of_lt_of_le hcard
  have hs : S ⊆ (hf N).toFinset := fun a ha => (hf N).mem_toFinset.mpr (hweight a ha)
  simpa only [← Set.ncard_eq_toFinset_card _ (hf N)] using Finset.card_le_card hs

end ContinuousFlexibility.Statements
