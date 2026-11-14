module

public import ContinuousFlexibility.Radial.ProfileLayerGeometry
public import ContinuousFlexibility.Radial.ProfilePartitionBounds
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Order.Interval.Finset.Nat
public import Lean.Elab.Tactic.Omega

/-!
# Finite overlap of endpoint layers

The profile partition supplies one cell containing each core point. Every
endpoint layer containing that point has index in the same fixed window
around this cell's index. We count the layer indices, irrespective of the
number of profile cells at any particular index.
-/

@[expose] public section

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace ContinuousFlexibility.Analysis

theorem finset_sum_setIntegral_le_of_overlap
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : ℕ → Set α) (t : Finset ℕ) {B : ℕ} {F : α → ℝ}
    (hs : ∀ n, MeasurableSet (s n)) (hF : Integrable F μ)
    (hF₀ : ∀ x, 0 ≤ F x)
    (hcard : ∀ x, (t.filter (fun n => x ∈ s n)).card ≤ B) :
    (∑ n ∈ t, ∫ x in s n, F x ∂μ) ≤ (B : ℝ) * ∫ x, F x ∂μ := by
  classical
  have hi (n : ℕ) : Integrable ((s n).indicator F) μ := hF.indicator (hs n)
  have hpoint (x : α) :
      (∑ n ∈ t, (s n).indicator F x) ≤ (B : ℝ) * F x := by
    have he : (∑ n ∈ t, (s n).indicator F x) =
        (t.filter (fun n => x ∈ s n)).card * F x := by
      calc
        (∑ n ∈ t, (s n).indicator F x) =
            ∑ n ∈ t with x ∈ s n, F x := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n _
          by_cases hn : x ∈ s n <;> simp [hn]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [he]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard x)) (hF₀ x)
  calc
    (∑ n ∈ t, ∫ x in s n, F x ∂μ) =
        ∑ n ∈ t, ∫ x, (s n).indicator F x ∂μ := by
      apply Finset.sum_congr rfl
      intro n _
      exact (integral_indicator (hs n)).symm
    _ = ∫ x, ∑ n ∈ t, (s n).indicator F x ∂μ :=
      (integral_finsetSum t (fun n _ => hi n)).symm
    _ ≤ ∫ x, (B : ℝ) * F x ∂μ :=
      integral_mono (integrable_finsetSum t (fun n _ => hi n))
        (hF.const_mul _) hpoint
    _ = (B : ℝ) * ∫ x, F x ∂μ := integral_const_mul _ _

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Radial

theorem measurableSet_profileEndpointLayer (D : ReferenceData) (C : ℝ) (n : ℕ) :
    MeasurableSet (profileEndpointLayer D C n) :=
  (isClosed_intervalEndpointLayer D.a D.b
    (profileLayerLower C n) (profileLayerUpper C n)).measurableSet

private theorem profile_overlap_exists_cell {D : ReferenceData}
    (h : RadialPartition D) {r : ℝ} (hr : r ∈ radialCore D) :
    ∃ m, r ∈ D.cells m := by
  obtain ⟨m, hm⟩ : ∃ m, D.localizer m r ≠ 0 := by
    by_contra hh
    have hz (m : ℕ) : D.localizer m r = 0 := by
      by_contra hm
      exact hh ⟨m, hm⟩
    have hzero : (∑' m, D.localizer m r) = 0 := by simp only [hz, tsum_zero]
    exact zero_ne_one (hzero.symm.trans (h.2.2.2.2.1 r hr).2)
  exact ⟨m, h.2.2.1 m hm⟩

theorem profileEndpointLayer_overlap_of_index_window
    {D : ReferenceData} {C : ℕ → ℝ} (h : AccumulatingProfileBounds D C)
    {N : ℕ}
    (hN : ∀ n m : ℕ, ∀ r : ℝ,
      r ∈ profileEndpointLayer D (C 0) n → r ∈ D.cells m →
        n ≤ D.cellIndex m + N ∧ D.cellIndex m ≤ n + N)
    (s : Finset ℕ) (r : ℝ) :
    (s.filter (fun n => r ∈ profileEndpointLayer D (C 0) n)).card ≤ 2 * N + 1 := by
  classical
  by_cases hr : r ∈ radialCore D
  · obtain ⟨m, hm⟩ := profile_overlap_exists_cell h.2.1 hr
    have hsub : s.filter (fun n => r ∈ profileEndpointLayer D (C 0) n) ⊆
        Finset.Icc (D.cellIndex m - N) (D.cellIndex m + N) := by
      intro n hn
      have hw := hN n m r (Finset.mem_filter.mp hn).2 hm
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  · have he : s.filter (fun n => r ∈ profileEndpointLayer D (C 0) n) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      exact hr (profileEndpointLayer_subset_core (h.2.2.1 0) n
        (Finset.mem_filter.mp hn).2)
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

theorem profileEndpointLayer_integral_sum_le
    {D : ReferenceData} {C : ℕ → ℝ} (h : AccumulatingProfileBounds D C)
    {N : ℕ}
    (hN : ∀ n m : ℕ, ∀ r : ℝ,
      r ∈ profileEndpointLayer D (C 0) n → r ∈ D.cells m →
        n ≤ D.cellIndex m + N ∧ D.cellIndex m ≤ n + N)
    (s : Finset ℕ) {F : ℝ → ℝ}
    (hF : IntegrableOn F (radialCore D) volume) (hF₀ : ∀ r, 0 ≤ F r) :
    (∑ n ∈ s, ∫ r in profileEndpointLayer D (C 0) n, F r) ≤
      ((2 * N + 1 : ℕ) : ℝ) * ∫ r in radialCore D, F r := by
  have hb := finset_sum_setIntegral_le_of_overlap (volume.restrict (radialCore D))
    (profileEndpointLayer D (C 0)) s
    (measurableSet_profileEndpointLayer D (C 0)) hF hF₀
    (profileEndpointLayer_overlap_of_index_window h hN s)
  have he (n : ℕ) : (volume.restrict (radialCore D)).restrict
      (profileEndpointLayer D (C 0) n) = volume.restrict (profileEndpointLayer D (C 0) n) :=
    Measure.restrict_restrict_of_subset
      (profileEndpointLayer_subset_core (h.2.2.1 0) n)
  simpa only [he] using hb

end ContinuousFlexibility.Radial
