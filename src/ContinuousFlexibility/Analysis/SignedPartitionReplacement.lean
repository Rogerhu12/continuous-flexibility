import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic

/-!
# Replacing positive pieces in an actual signed partition

An injective enumeration retains every negative piece. A new positive
family is disjoint and covers the positive points in question. The same
argument applies to reference intervals and to current planar domains;
it does not require the current negative pieces to be radial strips.
-/

namespace ContinuousFlexibility.Analysis

open Set

def signedReplacementPiece {X I J K : Type*}
    (old : I → Set X) (negative : J → I) (positive : K → Set X) :
    J ⊕ K → Set X
  | .inl j => old (negative j)
  | .inr k => positive k

theorem signedReplacementPiece_existsUnique
    {X I J K : Type*} {old : I → Set X} {negative : J → I}
    {positive : K → Set X} {flag : I → Bool} {f : X → ℝ} {p : X}
    (hinj : Function.Injective negative)
    (hnegativeFlag : ∀ j, flag (negative j) = false)
    (hnegativeCover : ∀ i, flag i = false → ∃ j, negative j = i)
    (hnegativeSign : ∀ i, flag i = false → p ∈ old i → f p < 0)
    (hpositiveSign : ∀ i, flag i = true → p ∈ old i → 0 < f p)
    (hnewSign : ∀ k, p ∈ positive k → 0 < f p)
    (hnewUnique : ∀ i j, p ∈ positive i → p ∈ positive j → i = j)
    (hnewCover : 0 < f p → ∃ k, p ∈ positive k)
    (hOld : ∃! i, p ∈ old i) :
    ∃! i, p ∈ signedReplacementPiece old negative positive i := by
  obtain ⟨i, hi, huniq⟩ := hOld
  have hretainedUnique (j k : J)
      (hj : p ∈ old (negative j)) (hk : p ∈ old (negative k)) : j = k :=
    hinj ((huniq _ hj).trans (huniq _ hk).symm)
  have hcross (j : J) (k : K)
      (hj : p ∈ old (negative j)) (hk : p ∈ positive k) : False :=
    lt_asymm (hnegativeSign _ (hnegativeFlag j) hj) (hnewSign k hk)
  have hunique (j k : J ⊕ K)
      (hj : p ∈ signedReplacementPiece old negative positive j)
      (hk : p ∈ signedReplacementPiece old negative positive k) : j = k := by
    cases j with
    | inl j =>
      cases k with
      | inl k => exact congrArg Sum.inl (hretainedUnique j k hj hk)
      | inr k => exact (hcross j k hj hk).elim
    | inr j =>
      cases k with
      | inl k => exact (hcross k j hk hj).elim
      | inr k => exact congrArg Sum.inr (hnewUnique j k hj hk)
  cases hflag : flag i with
  | false =>
    obtain ⟨j, hj⟩ := hnegativeCover i hflag
    have hmem : p ∈ signedReplacementPiece old negative positive (.inl j) := by
      change p ∈ old (negative j)
      rw [hj]
      exact hi
    exact ⟨.inl j, hmem, fun k hk => hunique k (.inl j) hk hmem⟩
  | true =>
    obtain ⟨k, hk⟩ := hnewCover (hpositiveSign i hflag hi)
    exact ⟨.inr k, hk, fun j hj => hunique j (.inr k) hj hk⟩

end ContinuousFlexibility.Analysis
