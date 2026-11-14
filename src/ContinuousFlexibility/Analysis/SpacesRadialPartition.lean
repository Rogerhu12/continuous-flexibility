module

public import ContinuousFlexibility.Analysis.SpacesCutoff
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# A fixed unit-scale radial partition

Differences of two translates of the same smooth transition telescope.
At a point only the two indices surrounding its integer part can be
nonzero. This supplies the uniformly smooth localizations used by the
physical Fourier construction, together with a wider cutoff which is
identically one on each localization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter Function
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

def spacesRadialPartition (n : ℤ) (x : ℝ) : ℝ :=
  Real.smoothTransition (x - n + 1) - Real.smoothTransition (x - n)

theorem spacesRadialPartition_contDiff (n : ℤ) : ContDiff ℝ ∞ (spacesRadialPartition n) :=
  (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).add contDiff_const)).sub
      (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem spacesRadialPartition_nonneg (n : ℤ) (x : ℝ) : 0 ≤ spacesRadialPartition n x := by
  by_cases hx : x ≤ n
  · rw [spacesRadialPartition, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx), sub_zero]
    exact Real.smoothTransition.nonneg _
  · rw [spacesRadialPartition,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x - n + 1)]
    exact sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem spacesRadialPartition_le_one (n : ℤ) (x : ℝ) : spacesRadialPartition n x ≤ 1 := by
  have hlo := Real.smoothTransition.nonneg (x - n)
  have hhi := Real.smoothTransition.le_one (x - n + 1)
  unfold spacesRadialPartition
  linarith

theorem spacesRadialPartition_eq_zero_left (n : ℤ) {x : ℝ} (hx : x ≤ n - 1) :
    spacesRadialPartition n x = 0 := by
  rw [spacesRadialPartition,
    Real.smoothTransition.zero_of_nonpos (by linarith : x - n + 1 ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : x - n ≤ 0), sub_self]

theorem spacesRadialPartition_eq_zero_right (n : ℤ) {x : ℝ} (hx : n + 1 ≤ x) :
    spacesRadialPartition n x = 0 := by
  rw [spacesRadialPartition,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x - n + 1),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x - n), sub_self]

theorem spacesRadialPartition_support (n : ℤ) :
    support (spacesRadialPartition n) ⊆ Icc ((n : ℝ) - 1) (n + 1) := by
  intro x hx
  constructor
  · by_contra h
    exact hx (spacesRadialPartition_eq_zero_left n (le_of_not_ge h))
  · by_contra h
    exact hx (spacesRadialPartition_eq_zero_right n (le_of_not_ge h))

theorem spacesRadialPartition_hasCompactSupport (n : ℤ) :
    HasCompactSupport (spacesRadialPartition n) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (spacesRadialPartition_support n)

theorem spacesRadialPartition_locallyFinite : LocallyFinite (fun n : ℤ =>
    support (spacesRadialPartition n)) := by
  have ht : Tendsto (fun n : ℤ => (n : ℝ) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1 : ℝ) tendsto_intCast_atTop_atTop
  have hb : Tendsto (fun n : ℤ => (n : ℝ) + 1) atBot atBot :=
    tendsto_atBot_add_const_right _ (1 : ℝ) (tendsto_intCast_atBot_iff.mpr tendsto_id)
  exact (locallyFinite_Icc_of_tendsto ht hb).subset spacesRadialPartition_support

theorem spacesRadialPartition_eq_zero_of_index (x : ℝ) {n : ℤ}
    (hn : n ≠ ⌊x⌋ ∧ n ≠ ⌊x⌋ + 1) : spacesRadialPartition n x = 0 := by
  have hf := Int.floor_le x
  have hc := Int.lt_floor_add_one x
  have hsplit : n + 1 ≤ ⌊x⌋ ∨ ⌊x⌋ + 2 ≤ n := by omega
  rcases hsplit with h | h
  · apply spacesRadialPartition_eq_zero_right
    have h' : (n : ℝ) + 1 ≤ ⌊x⌋ := by exact_mod_cast h
    exact h'.trans hf
  · apply spacesRadialPartition_eq_zero_left
    have h' : (⌊x⌋ : ℝ) + 2 ≤ n := by exact_mod_cast h
    linarith

theorem spacesRadialPartition_sum (x : ℝ) : ∑' n : ℤ, spacesRadialPartition n x = 1 := by
  classical
  let m : ℤ := ⌊x⌋
  have hzero : ∀ n ∉ ({m, m + 1} : Finset ℤ), spacesRadialPartition n x = 0 := by
    intro n hn
    apply spacesRadialPartition_eq_zero_of_index x
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hn
  rw [tsum_eq_sum hzero, Finset.sum_pair (by omega : m ≠ m + 1)]
  have hf : (m : ℝ) ≤ x := Int.floor_le x
  have hc : x < (m : ℝ) + 1 := Int.lt_floor_add_one x
  simp only [spacesRadialPartition, Int.cast_add, Int.cast_one]
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x - m + 1),
    Real.smoothTransition.zero_of_nonpos (by linarith : x - ((m : ℝ) + 1) ≤ 0)]
  have he : x - ((m : ℝ) + 1) + 1 = x - m := by ring
  rw [he]
  ring

theorem spacesRadialPartition_derivative_bound (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, ∀ x : ℝ,
      |iteratedDeriv a (spacesRadialPartition n) x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := (spacesRadialPartition_hasCompactSupport 0).exists_bound_iteratedFDeriv
    (spacesRadialPartition_contDiff 0) a
  refine ⟨C, hC, fun n x => ?_⟩
  have he : spacesRadialPartition n = fun y => spacesRadialPartition 0 (y - n) := by
    funext y
    simp only [spacesRadialPartition, Int.cast_zero, sub_zero]
  rw [he, iteratedDeriv_comp_sub_const]
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
    hbound a le_rfl (x - n)

def spacesRadialEnvelope (n : ℤ) (x : ℝ) : ℝ :=
  Real.smoothTransition (x - n + 2) * Real.smoothTransition ((n : ℝ) + 2 - x)

theorem spacesRadialEnvelope_contDiff (n : ℤ) : ContDiff ℝ ∞ (spacesRadialEnvelope n) :=
  (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).add contDiff_const)).mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem spacesRadialEnvelope_eq_one (n : ℤ) {x : ℝ}
    (hx : x ∈ Icc ((n : ℝ) - 1) (n + 1)) : spacesRadialEnvelope n x = 1 := by
  rw [spacesRadialEnvelope,
    Real.smoothTransition.one_of_one_le (by linarith [hx.1] : 1 ≤ x - n + 2),
    Real.smoothTransition.one_of_one_le (by linarith [hx.2] : 1 ≤ (n : ℝ) + 2 - x), one_mul]

theorem spacesRadialEnvelope_mul_partition (n : ℤ) (x : ℝ) :
    spacesRadialEnvelope n x * spacesRadialPartition n x = spacesRadialPartition n x := by
  by_cases hx : spacesRadialPartition n x = 0
  · rw [hx, mul_zero]
  · rw [spacesRadialEnvelope_eq_one n (spacesRadialPartition_support n hx), one_mul]

theorem spacesRadialEnvelope_eq_zero (n : ℤ) {x : ℝ}
    (hx : x ∉ Ioo ((n : ℝ) - 2) (n + 2)) : spacesRadialEnvelope n x = 0 := by
  rcases not_and_or.mp hx with h | h
  · rw [spacesRadialEnvelope,
      Real.smoothTransition.zero_of_nonpos (by linarith : x - n + 2 ≤ 0), zero_mul]
  · rw [spacesRadialEnvelope,
      Real.smoothTransition.zero_of_nonpos (by linarith : (n : ℝ) + 2 - x ≤ 0), mul_zero]

end ContinuousFlexibility.Statements
