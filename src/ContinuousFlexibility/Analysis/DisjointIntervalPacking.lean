module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Data.Set.Card

/-!
# Packing disjoint intervals with a positive minimum length

Finite additivity of actual Lebesgue measure bounds the sum of the
interval lengths. If a selected label set had infinitely many elements,
finite subsets of arbitrary cardinality would contradict that bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped BigOperators

theorem finset_disjoint_Ioo_length_sum_le
    {ι : Type*} (s : Finset ι) (l r : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hinterval : ∀ i ∈ s, a ≤ l i ∧ l i ≤ r i ∧ r i ≤ b)
    (hdisjoint : Set.PairwiseDisjoint (s : Set ι) (fun i => Ioo (l i) (r i))) :
    ∑ i ∈ s, (r i - l i) ≤ b - a := by
  classical
  have hmeasure : volume.real (⋃ i ∈ s, Ioo (l i) (r i)) =
      ∑ i ∈ s, volume.real (Ioo (l i) (r i)) :=
    measureReal_biUnion_finset hdisjoint (fun _ _ => measurableSet_Ioo)
      (fun _ _ => by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hsub : (⋃ i ∈ s, Ioo (l i) (r i)) ⊆ Ioo a b := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨i, hx⟩
    rcases mem_iUnion.mp hx with ⟨hi, hx⟩
    exact ⟨(hinterval i hi).1.trans_lt hx.1, hx.2.trans_le (hinterval i hi).2.2⟩
  calc
    _ = ∑ i ∈ s, volume.real (Ioo (l i) (r i)) :=
      Finset.sum_congr rfl (fun i hi => (Real.volume_real_Ioo_of_le (hinterval i hi).2.1).symm)
    _ = volume.real (⋃ i ∈ s, Ioo (l i) (r i)) := hmeasure.symm
    _ ≤ volume.real (Ioo a b) := measureReal_mono hsub
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    _ = b - a := Real.volume_real_Ioo_of_le hab

theorem finite_ncard_mul_le_of_disjoint_Ioo
    (A : Set ℕ) (l r : ℕ → ℝ) {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hinterval : ∀ i ∈ A, a ≤ l i ∧ l i ≤ r i ∧ r i ≤ b)
    (hdisjoint : A.PairwiseDisjoint (fun i => Ioo (l i) (r i)))
    (hlength : ∀ i ∈ A, δ ≤ r i - l i) :
    A.Finite ∧ (A.ncard : ℝ) * δ ≤ b - a := by
  classical
  have hfiniteBound : ∀ s : Finset ℕ, (s : Set ℕ) ⊆ A →
      (s.card : ℝ) * δ ≤ b - a := by
    intro s hs
    calc
      _ = ∑ _i ∈ s, δ := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, (r i - l i) := Finset.sum_le_sum (fun i hi => hlength i (hs hi))
      _ ≤ b - a := finset_disjoint_Ioo_length_sum_le s l r hab
        (fun i hi => hinterval i (hs hi)) (hdisjoint.subset hs)
  have hfin : A.Finite := by
    by_contra hnot
    have hinf : A.Infinite := hnot
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
    obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq N
    have hb := hfiniteBound s hs
    rw [hcard] at hb
    exact (not_le_of_gt hN) ((le_div_iff₀ hδ).mpr hb)
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card A hfin]
  exact hfiniteBound hfin.toFinset (fun i hi => hfin.mem_toFinset.mp hi)

end ContinuousFlexibility.Analysis
