import ContinuousFlexibility.Analysis.N05ReferenceEndpointWeights
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Summing over actual finite index fibers

Finite piece sums are grouped by their genuine reference index. A bound
for the size of each fiber transfers a summable numerical majorant to the
piece family. The reciprocal discrete material weight is summable even
when fiber cardinalities grow by a fixed coefficient power.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped BigOperators

theorem n05_summable_comp_of_finite_fibers (index : ℕ → ℕ)
    (g w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hfinite : ∀ n, {m | index m = n}.Finite)
    (hcard : ∀ n, ({m | index m = n}.ncard : ℝ) ≤ g n)
    (hs : Summable (fun n => g n * w n)) :
    Summable (fun m => w (index m)) ∧
      (∑' m, w (index m)) ≤ ∑' n, g n * w n := by
  classical
  have hg (n : ℕ) : 0 ≤ g n := (Nat.cast_nonneg _).trans (hcard n)
  have hsum (s : Finset ℕ) :
      (∑ m ∈ s, w (index m)) ≤ ∑' n, g n * w n := by
    have hmap (m : ℕ) (hm : m ∈ s) : index m ∈ s.image index :=
      Finset.mem_image_of_mem index hm
    calc
      (∑ m ∈ s, w (index m)) =
          ∑ n ∈ s.image index, ∑ m ∈ s with index m = n, w (index m) :=
        (Finset.sum_fiberwise_of_maps_to hmap (fun m => w (index m))).symm
      _ ≤ ∑ n ∈ s.image index, g n * w n := by
        apply Finset.sum_le_sum
        intro n _
        have hsub : (↑(s.filter (fun m => index m = n)) : Set ℕ) ⊆
            {m | index m = n} := by
          intro m hm
          exact (Finset.mem_filter.mp hm).2
        have hcNat : (s.filter (fun m => index m = n)).card ≤
            {m | index m = n}.ncard := by
          simpa only [Set.ncard_coe_finset] using
            Set.ncard_le_ncard hsub (hfinite n)
        have hcReal : ((s.filter (fun m => index m = n)).card : ℝ) ≤
            ({m | index m = n}.ncard : ℝ) := by
          exact_mod_cast hcNat
        have hc : ((s.filter (fun m => index m = n)).card : ℝ) ≤ g n :=
          hcReal.trans (hcard n)
        calc
          (∑ m ∈ s with index m = n, w (index m)) =
              ∑ m ∈ s with index m = n, w n := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [(Finset.mem_filter.mp hm).2]
          _ = ((s.filter (fun m => index m = n)).card : ℝ) * w n := by simp
          _ ≤ g n * w n := mul_le_mul_of_nonneg_right hc (hw n)
      _ ≤ ∑' n, g n * w n :=
        Summable.sum_le_tsum _ (fun n _ => mul_nonneg (hg n) (hw n)) hs
  exact ⟨summable_of_sum_le (fun m => hw (index m)) hsum,
    Real.tsum_le_of_sum_le (fun m => hw (index m)) hsum⟩

theorem n05_radialIndex_le_Q (n : ℕ) : (n : ℝ) ≤ radialQ n := by
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith only [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hn1)]
  exact hn.trans (n05_radialIndexSquare_le_Q n)

/-- A coefficient-sized multiplicity is absorbed by one reciprocal
material envelope. The majorant is derived from exponential decay. -/
theorem n05_referenceReciprocalMaterial_fiber_summable (index : ℕ → ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hfiber : ∀ n, {m | index m = n}.Finite ∧
      ({m | index m = n}.ncard : ℝ) ≤ B * radialE n ^ B) :
    Summable (fun m => Real.exp (-Radial.logM (index m))) := by
  obtain ⟨A, hA⟩ := Radial.radialQ_le_logM_add (B + 1)
  have hmajor (n : ℕ) :
      (B * radialE n ^ B) * Real.exp (-Radial.logM n) ≤
        (B * Real.exp A) * Real.exp (-(n : ℝ)) := by
    have he : radialE n ^ B = Real.exp (B * radialQ n) := by
      rw [radialE, ← Real.exp_mul]
      congr 1
      ring
    have hexp : B * radialQ n - Radial.logM n ≤ A - (n : ℝ) := by
      nlinarith only [hA n, n05_radialIndex_le_Q n]
    calc
      (B * radialE n ^ B) * Real.exp (-Radial.logM n) =
          B * Real.exp (B * radialQ n - Radial.logM n) := by
        rw [he, sub_eq_add_neg, Real.exp_add, mul_assoc]
      _ ≤ B * Real.exp (A - (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hB
      _ = (B * Real.exp A) * Real.exp (-(n : ℝ)) := by
        rw [sub_eq_add_neg, Real.exp_add, mul_assoc]
  have hs : Summable (fun n =>
      (B * radialE n ^ B) * Real.exp (-Radial.logM n)) :=
    (Real.summable_exp_neg_nat.mul_left (B * Real.exp A)).of_nonneg_of_le
      (fun n => mul_nonneg
        (mul_nonneg hB (Real.rpow_nonneg (Real.exp_pos _).le _))
        (Real.exp_pos _).le) hmajor
  exact (n05_summable_comp_of_finite_fibers index
    (fun n => B * radialE n ^ B) (fun n => Real.exp (-Radial.logM n))
    (fun n => (Real.exp_pos _).le) (fun n => (hfiber n).1)
    (fun n => (hfiber n).2) hs).1

end ContinuousFlexibility.Statements

