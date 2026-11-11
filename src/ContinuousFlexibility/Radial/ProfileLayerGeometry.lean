import ContinuousFlexibility.Analysis.IntervalLayerCutoff
import ContinuousFlexibility.Radial.MorseRealizationBasic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Endpoint layers and profile cell indices

The distance bounds in an accumulating profile imply that every cell
meeting an enlarged endpoint layer has index in a fixed finite window.
This statement counts indices, not cells: the number of cells with one
index is not assumed uniformly bounded.
-/

open Set Real
open ContinuousFlexibility.Analysis ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Radial

noncomputable section

def profileLayerLower (C : ℝ) (n : ℕ) : ℝ :=
  C⁻¹ * exp (-((n : ℝ) + 1) ^ 2)

def profileLayerUpper (C : ℝ) (n : ℕ) : ℝ :=
  C * exp (-(n : ℝ) ^ 2)

def profileEndpointLayer (D : ReferenceData) (C : ℝ) (n : ℕ) : Set ℝ :=
  intervalEndpointLayer D.a D.b (profileLayerLower C n) (profileLayerUpper C n)

def profileLayerCutoff (D : ReferenceData) (C : ℝ) (n : ℕ) : ℝ → ℝ :=
  intervalLayerCutoff D.a D.b (profileLayerLower C n) (profileLayerUpper C n)

theorem profileLayerLower_pos {C : ℝ} (hC : 0 < C) (n : ℕ) :
    0 < profileLayerLower C n := mul_pos (inv_pos.mpr hC) (exp_pos _)

theorem profileLayerUpper_pos {C : ℝ} (hC : 0 < C) (n : ℕ) :
    0 < profileLayerUpper C n := mul_pos hC (exp_pos _)

theorem profileLayerLower_le_upper {C : ℝ} (hC : 1 ≤ C) (n : ℕ) :
    profileLayerLower C n ≤ profileLayerUpper C n := by
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  have hInv : C⁻¹ ≤ C := ((inv_le_one₀ hC₀).2 hC).trans hC
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact mul_le_mul hInv (exp_le_exp.mpr (by nlinarith)) (exp_pos _).le hC₀.le

theorem exists_accumulatingProfileBounds_one_le {D : ReferenceData}
    (h : IsAccumulatingProfile D) :
    ∃ C : ℕ → ℝ, AccumulatingProfileBounds D C ∧ ∀ s, 1 ≤ C s := by
  obtain ⟨C, hC⟩ := h
  exact ⟨fun s => max 1 (C s), hC.mono (fun s => le_max_right _ _),
    fun s => le_max_left _ _⟩

theorem profileLayerCutoff_one_on_cell {D : ReferenceData} {C : ℕ → ℝ}
    (h : AccumulatingProfileBounds D C) {m : ℕ} {r : ℝ} (hr : r ∈ D.cells m) :
    profileLayerCutoff D (C 0) (D.cellIndex m) r = 1 := by
  rcases h with ⟨_, _, hC, _, _, _, hdist, _⟩
  obtain ⟨hlo, hhi⟩ := hdist m r hr
  exact intervalLayerCutoff_one (profileLayerLower_pos (hC 0) _)
    (profileLayerUpper_pos (hC 0) _) hlo hhi

theorem tsupport_profileLayerCutoff_subset {D : ReferenceData} {C : ℝ}
    (hC : 0 < C) (n : ℕ) :
    tsupport (profileLayerCutoff D C n) ⊆ profileEndpointLayer D C n :=
  tsupport_intervalLayerCutoff_subset (profileLayerLower_pos hC n) (profileLayerUpper_pos hC n)

theorem profileEndpointLayer_subset_core {D : ReferenceData} {C : ℝ}
    (hC : 0 < C) (n : ℕ) :
    profileEndpointLayer D C n ⊆ radialCore D :=
  intervalEndpointLayer_subset_Ioo (profileLayerLower_pos hC n)

private theorem layer_distance_index_bound {C d n : ℝ} (hC : 0 < C)
    (hd : 0 < d) (hn : 0 ≤ n)
    (hlo : C⁻¹ * exp (-((n + 1) ^ 2)) ≤ d)
    (hhi : d ≤ C * exp (-(n ^ 2))) :
    |sqrt (-log d) - n| ≤ 1 + sqrt |log C| := by
  have hlo' := log_le_log (mul_pos (inv_pos.mpr hC) (exp_pos _)) hlo
  have hhi' := log_le_log hd hhi
  rw [log_mul (inv_ne_zero hC.ne') (exp_pos _).ne', log_inv, log_exp] at hlo'
  rw [log_mul hC.ne' (exp_pos _).ne', log_exp] at hhi'
  let R : ℝ := sqrt |log C|
  let X : ℝ := sqrt (-log d)
  have hR : 0 ≤ R := sqrt_nonneg _
  have hR₂ : R ^ 2 = |log C| := sq_sqrt (abs_nonneg _)
  have hX : 0 ≤ X := sqrt_nonneg _
  have hlow : n ^ 2 - |log C| ≤ -log d := by
    linarith only [hhi', le_abs_self (log C)]
  have hupp : -log d ≤ (n + 1) ^ 2 + |log C| := by
    linarith only [hlo', le_abs_self (log C)]
  have hupper : X ≤ n + 1 + R := by
    apply sqrt_le_iff.mpr
    refine ⟨by linarith only [hn, hR], ?_⟩
    nlinarith only [hupp, hR₂, mul_nonneg (add_nonneg hn zero_le_one) hR]
  have hlogSq : -log d ≤ X ^ 2 := by
    by_cases hh : 0 ≤ -log d
    · exact (sq_sqrt hh).symm.le
    · exact (le_of_not_ge hh).trans (sq_nonneg X)
  have hlower : n ≤ X + R := by
    apply (sq_le_sq₀ hn (add_nonneg hX hR)).mp
    nlinarith only [hlow, hlogSq, hR₂, mul_nonneg hX hR]
  exact abs_le.mpr ⟨by linarith only [hlower], by linarith only [hupper]⟩

/-- Comparing the enlarged distance layer with a profile cell gives a
uniform real bound on the difference of their indices. -/
theorem profileEndpointLayer_index_bound {D : ReferenceData} {C : ℕ → ℝ}
    (h : AccumulatingProfileBounds D C) {n m : ℕ} {r : ℝ}
    (hn : r ∈ profileEndpointLayer D (C 0) n) (hm : r ∈ D.cells m) :
    |(n : ℝ) - D.cellIndex m| ≤
      2 + sqrt |log (2 * C 0)| + sqrt |log (C 0)| := by
  rcases h with ⟨_, _, hC, _, _, _, hdist, _⟩
  let d : ℝ := intervalEndpointDistance D.a D.b r
  have hC₂ : 0 < 2 * C 0 := mul_pos (by norm_num) (hC 0)
  have hdcell := hdist m r hm
  have hd : 0 < d := (profileLayerLower_pos (hC 0) (D.cellIndex m)).trans_le hdcell.1
  have hnlo : (2 * C 0)⁻¹ * exp (-((n : ℝ) + 1) ^ 2) ≤ d := by
    have he : (2 * C 0)⁻¹ * exp (-((n : ℝ) + 1) ^ 2) = profileLayerLower (C 0) n / 2 := by
      unfold profileLayerLower
      field_simp [(hC 0).ne']
      <;> ring
    rw [he]
    exact hn.1
  have hnhi : d ≤ (2 * C 0) * exp (-(n : ℝ) ^ 2) := by
    have hh := hn.2
    change d ≤ 2 * (C 0 * exp (-(n : ℝ) ^ 2)) at hh
    nlinarith only [hh]
  have h₁ := layer_distance_index_bound hC₂ hd (Nat.cast_nonneg n) hnlo hnhi
  have h₂ := layer_distance_index_bound (hC 0) hd (Nat.cast_nonneg (D.cellIndex m))
    hdcell.1 hdcell.2
  calc
    |(n : ℝ) - D.cellIndex m| ≤
        |(n : ℝ) - sqrt (-log d)| + |sqrt (-log d) - D.cellIndex m| := abs_sub_le _ _ _
    _ = |sqrt (-log d) - n| + |sqrt (-log d) - D.cellIndex m| := by
      rw [abs_sub_comm (n : ℝ)]
    _ ≤ (1 + sqrt |log (2 * C 0)|) + (1 + sqrt |log (C 0)|) := add_le_add h₁ h₂
    _ = 2 + sqrt |log (2 * C 0)| + sqrt |log (C 0)| := by ring

/-- The finite index window is independent of the number of cells in each
layer. Both inequalities are convenient for natural-number finite sums. -/
theorem profileEndpointLayer_index_window {D : ReferenceData} {C : ℕ → ℝ}
    (h : AccumulatingProfileBounds D C) :
    ∃ N : ℕ, ∀ n m : ℕ, ∀ r : ℝ,
      r ∈ profileEndpointLayer D (C 0) n → r ∈ D.cells m →
        n ≤ D.cellIndex m + N ∧ D.cellIndex m ≤ n + N := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 + sqrt |log (2 * C 0)| + sqrt |log (C 0)|)
  refine ⟨N, ?_⟩
  intro n m r hn hm
  have hb := abs_le.mp (profileEndpointLayer_index_bound h hn hm)
  constructor
  · have he : (n : ℝ) ≤ (D.cellIndex m : ℝ) + N := by linarith [hb.2]
    exact_mod_cast he
  · have he : (D.cellIndex m : ℝ) ≤ (n : ℝ) + N := by linarith [hb.1]
    exact_mod_cast he

end

end ContinuousFlexibility.Radial
