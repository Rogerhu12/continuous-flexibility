import ContinuousFlexibility.Analysis.N05MaterialCellCoordinates
import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# Actual endpoint weights and the discrete reference exponent

The prescribed material endpoint weight has the same cubic exponent as
the reference weights up to a coefficient-sized error. The compact middle
is handled using the actual local finiteness of the reference cells.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem n05_radialIndexSquare_le_Q (n : ℕ) : (n : ℝ) ^ 2 ≤ radialQ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [radialQ]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (5 / 2 : ℝ) := by
    calc
      _ = (n : ℝ) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hlog : 1 ≤ Real.log (Real.exp 1 + (n : ℝ)) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (le_add_of_nonneg_right (Nat.cast_nonneg n))
  calc
    _ ≤ (n : ℝ) ^ (5 / 2 : ℝ) := hp
    _ ≤ radialQ n := by
      simpa only [radialQ, mul_one] using
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem n05_materialH_log_shift {x A : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A)
    (n : ℕ) (hshift : |x - (n : ℝ)| ≤ A) :
    |Real.log (materialH x) + radialS n| ≤
      (6 * A * (A ^ 2 + 1)) * (radialQ n + 1) := by
  have hc := n05_cube_shift_bound hx (Nat.cast_nonneg n) hA hshift
  have hlog : |Real.log (materialH x) + radialS n| =
      (2 / 3 : ℝ) * |x ^ 3 - (n : ℝ) ^ 3| := by
    rw [materialH, Real.log_exp, radialS]
    rw [show -2 * x ^ 3 / 3 + (2 / 3 : ℝ) * (n : ℝ) ^ 3 =
      (-2 / 3 : ℝ) * (x ^ 3 - (n : ℝ) ^ 3) by ring, abs_mul]
    norm_num
  calc
    _ = (2 / 3 : ℝ) * |x ^ 3 - (n : ℝ) ^ 3| := hlog
    _ ≤ |x ^ 3 - (n : ℝ) ^ 3| := by
      nlinarith only [abs_nonneg (x ^ 3 - (n : ℝ) ^ 3)]
    _ ≤ (6 * A * (A ^ 2 + 1)) * ((n : ℝ) ^ 2 + 1) := hc
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add_right (n05_radialIndexSquare_le_Q n) 1) (by positivity)

/-- The error between the actual material logarithm and the reference
cubic exponent is bounded uniformly by a fixed coefficient exponent. -/
theorem n05_material_reference_logH_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    ∃ C : ℝ, 0 < C ∧ ∀ m r, r ∈ D.cells m →
      |Real.log (T.H r) + radialS (D.cellIndex m)| ≤
        C * (radialQ (D.cellIndex m) + 1) := by
  obtain ⟨δ, A, hδ, hA, hcoord⟩ := n05_materialCell_endpoint_coordinates hT
  obtain ⟨B, hB⟩ := hD
  let middle : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hmiddle : middle ⊆ radialCore D := by
    intro r hr
    exact ⟨by linarith only [hr.1, hδ], by linarith only [hr.2, hδ]⟩
  have hlog : ContinuousOn (fun r => Real.log (T.H r)) middle :=
    ((hT.1 T.H (by simp)).continuousOn.mono hmiddle).log
      (fun r hr => ((hT.2.1 r (hmiddle hr)).2.1).ne')
  obtain ⟨L, hL⟩ := isCompact_Icc.bddAbove_image hlog.abs
  have hfinite : {m | (D.cells m ∩ middle).Nonempty}.Finite :=
    hB.2.2.2.2.2.1 middle isCompact_Icc hmiddle
  obtain ⟨R, hR⟩ := (hfinite.image (fun m => radialS (D.cellIndex m))).bddAbove
  let C : ℝ := max (6 * A * (A ^ 2 + 1)) (|L| + |R| + 1)
  have hC : 0 < C := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨C, hC, fun m r hrm => ?_⟩
  have hr : r ∈ Ioo D.a D.b := hB.2.1.2.2.2.1 m hrm
  have hQ : 0 ≤ radialQ (D.cellIndex m) := Radial.radialQ_nonneg _
  by_cases hnear : endpointDistance D r < δ
  · obtain ⟨x, hx, hshift, hH, _, _⟩ := hcoord m r hr hrm hnear
    rw [hH]
    exact (n05_materialH_log_shift hx hA.le (D.cellIndex m) hshift).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith only [hQ]))
  · have hd : δ ≤ min (r - D.a) (D.b - r) := le_of_not_gt hnear
    have hrmid : r ∈ middle :=
      ⟨by linarith only [hd.trans (min_le_left _ _)],
        by linarith only [hd.trans (min_le_right _ _)]⟩
    have hLm : |Real.log (T.H r)| ≤ |L| :=
      (hL ⟨r, hrmid, rfl⟩).trans (le_abs_self L)
    have hRm : radialS (D.cellIndex m) ≤ |R| :=
      (hR ⟨m, ⟨r, hrm, hrmid⟩, rfl⟩).trans (le_abs_self R)
    have hSm : 0 ≤ radialS (D.cellIndex m) := Radial.radialS_nonneg _
    calc
      _ ≤ |Real.log (T.H r)| + |radialS (D.cellIndex m)| := abs_add_le _ _
      _ ≤ |L| + |R| := by rw [abs_of_nonneg hSm]; exact add_le_add hLm hRm
      _ ≤ C := (by linarith : |L| + |R| ≤ |L| + |R| + 1).trans (le_max_right _ _)
      _ ≤ C * (radialQ (D.cellIndex m) + 1) := by nlinarith only [mul_nonneg hC.le hQ]

end ContinuousFlexibility.Statements
