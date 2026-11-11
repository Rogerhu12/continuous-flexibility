import ContinuousFlexibility.Statements.Radial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith

/-!
# Uniform bounds for the actual radial localizers

Nonnegativity and the partition-of-one identity give a pointwise bound of
one, without any derivative bounds or a bound on the number of cells at a
fixed index.
-/

open Set
open ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Radial

theorem profile_localizer_zero_outside_core {D : ReferenceData}
    (hD : RadialPartition D) (m : ℕ) {r : ℝ} (hr : r ∉ radialCore D) :
    D.localizer m r = 0 := by
  by_contra hn
  exact hr (hD.2.2.2.1 m (hD.2.2.1 m hn))

theorem profile_localizer_bounds {D : ReferenceData} (hD : RadialPartition D)
    (m : ℕ) (r : ℝ) :
    0 ≤ D.localizer m r ∧ D.localizer m r ≤ 1 := by
  refine ⟨hD.2.1 m r, ?_⟩
  by_cases hr : r ∈ radialCore D
  · obtain ⟨hs, he⟩ := hD.2.2.2.2.1 r hr
    exact (hs.le_tsum m (fun k _ => hD.2.1 k r)).trans_eq he
  · rw [profile_localizer_zero_outside_core hD m hr]
    exact zero_le_one

theorem profile_localizer_abs_le_one {D : ReferenceData} (hD : RadialPartition D)
    (m : ℕ) (r : ℝ) : |D.localizer m r| ≤ 1 := by
  rw [abs_of_nonneg (profile_localizer_bounds hD m r).1]
  exact (profile_localizer_bounds hD m r).2

theorem profile_localizer_sq_sum_le_one {D : ReferenceData}
    (hD : RadialPartition D) (s : Finset ℕ) (r : ℝ) :
    ∑ m ∈ s, D.localizer m r ^ 2 ≤ 1 := by
  by_cases hr : r ∈ radialCore D
  · obtain ⟨hs, he⟩ := hD.2.2.2.2.1 r hr
    calc
      ∑ m ∈ s, D.localizer m r ^ 2 ≤ ∑ m ∈ s, D.localizer m r := by
        apply Finset.sum_le_sum
        intro m _
        have hb := profile_localizer_bounds hD m r
        nlinarith only [mul_nonneg hb.1 (sub_nonneg.mpr hb.2)]
      _ ≤ ∑' m, D.localizer m r :=
        Summable.sum_le_tsum s (fun m _ => hD.2.1 m r) hs
      _ = 1 := he
  · have hz (m : ℕ) : D.localizer m r = 0 :=
      profile_localizer_zero_outside_core hD m hr
    simp only [hz, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, zero_le_one]

end ContinuousFlexibility.Radial
