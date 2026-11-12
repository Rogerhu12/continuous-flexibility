import ContinuousFlexibility.Statements.Radial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Counting the actual reference cells

The trace scaffold places a quantitatively wide open interval inside each
actual cell. These intervals are pairwise disjoint in the bounded radial
core. Their Lebesgue measures therefore bound the number of cells carrying
any one reference index by a fixed coefficient power.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped BigOperators

theorem n05_referenceCellIndex_count_of_bounds
    {D : ReferenceData} {constants : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D constants) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      {m | D.cellIndex m = n}.Finite ∧
        ({m | D.cellIndex m = n}.ncard : ℝ) ≤ B * radialE n ^ B := by
  classical
  obtain ⟨hgeometry, hpartition, _, _, hfinite, _, _, _, _, _, _, _, htrace⟩ := hD
  obtain ⟨centers, widths, K, hK, hwidth, hdisjoint⟩ := htrace
  let A : ℝ := (D.b - D.a) * K
  let B : ℝ := max K A + 1
  have hKB : K ≤ B := (le_max_left K A).trans (le_add_of_nonneg_right zero_le_one)
  have hAB : A ≤ B := (le_max_right K A).trans (le_add_of_nonneg_right zero_le_one)
  have hB : 0 < B := hK.trans_le hKB
  refine ⟨B, hB, ?_⟩
  intro n
  have hn : {m | D.cellIndex m = n}.Finite :=
    (hfinite n).subset (fun m hm => le_of_eq hm)
  refine ⟨hn, ?_⟩
  let F : Finset ℕ := hn.toFinset
  let I : ℕ → Set ℝ := fun m => Ioo (centers m - widths m) (centers m + widths m)
  have hsub : (⋃ m ∈ F, I m) ⊆ Ioo D.a D.b := by
    intro r hr
    obtain ⟨m, _, hr⟩ := mem_iUnion₂.mp hr
    exact hpartition.2.2.2.1 m ((hwidth m).2.2.2 ⟨hr.1.le, hr.2.le⟩)
  have hvolume : volume.real (⋃ m ∈ F, I m) = ∑ m ∈ F, volume.real (I m) :=
    measureReal_biUnion_finset
      (fun m _ j _ hmj => hdisjoint hmj)
      (fun _ _ => measurableSet_Ioo)
      (fun _ _ => by
        dsimp only [I]
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top)
  have hlocal (m : ℕ) (hm : m ∈ F) :
      K⁻¹ * radialE n ^ (-K) ≤ volume.real (I m) := by
    have hmn : D.cellIndex m = n := by
      simpa only [F, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hm
    have hp := (hwidth m).2.1
    have hw := (hwidth m).2.2.1
    rw [hmn] at hw
    dsimp only [I]
    rw [Real.volume_real_Ioo_of_le (by linarith only [hp])]
    linarith only [hw, hp]
  have hpacking : (F.card : ℝ) * (K⁻¹ * radialE n ^ (-K)) ≤ D.b - D.a := by
    calc
      (F.card : ℝ) * (K⁻¹ * radialE n ^ (-K)) =
          ∑ m ∈ F, K⁻¹ * radialE n ^ (-K) := by simp
      _ ≤ ∑ m ∈ F, volume.real (I m) := Finset.sum_le_sum hlocal
      _ = volume.real (⋃ m ∈ F, I m) := hvolume.symm
      _ ≤ volume.real (Ioo D.a D.b) :=
        measureReal_mono hsub (by
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_ne_top)
      _ = D.b - D.a := Real.volume_real_Ioo_of_le hgeometry.2.1.le
  have hE : 0 < radialE n := Real.exp_pos _
  have hcancel : (K⁻¹ * radialE n ^ (-K)) * (K * radialE n ^ K) = 1 := by
    calc
      _ = (K⁻¹ * K) * (radialE n ^ (-K) * radialE n ^ K) := by ring
      _ = 1 := by
        rw [inv_mul_cancel₀ hK.ne', ← Real.rpow_add hE, neg_add_cancel,
          Real.rpow_zero, one_mul]
  have hcard : (F.card : ℝ) ≤ A * radialE n ^ K := by
    calc
      (F.card : ℝ) =
          ((F.card : ℝ) * (K⁻¹ * radialE n ^ (-K))) * (K * radialE n ^ K) := by
        rw [mul_assoc, hcancel, mul_one]
      _ ≤ (D.b - D.a) * (K * radialE n ^ K) :=
        mul_le_mul_of_nonneg_right hpacking
          (mul_nonneg hK.le (Real.rpow_nonneg hE.le K))
      _ = A * radialE n ^ K := by dsimp only [A]; ring
  have hEone : 1 ≤ radialE n := by
    have hexp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr zero_le_one
    exact Real.one_le_exp_iff.mpr
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (Real.log_nonneg (hexp.trans (le_add_of_nonneg_right (Nat.cast_nonneg n)))))
  rw [Set.ncard_eq_toFinset_card _ hn]
  exact hcard.trans (mul_le_mul hAB
    (Real.rpow_le_rpow_of_exponent_le hEone hKB) (Real.rpow_nonneg hE.le K) hB.le)

theorem n05_referenceCellIndex_count {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      {m | D.cellIndex m = n}.Finite ∧
        ({m | D.cellIndex m = n}.ncard : ℝ) ≤ B * radialE n ^ B := by
  obtain ⟨constants, hbounds⟩ := hD
  exact n05_referenceCellIndex_count_of_bounds hbounds

end ContinuousFlexibility.Statements
