import ContinuousFlexibility.Analysis.N05MaterialCellCoordinates
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The actual coefficient envelope at a reference cell

The prescribed endpoint formula and the bounded error in the material
coordinate give an upper bound for the logarithm of the actual E0 weight.
The compact middle is treated by continuity. This converts primitive
geometry bounds at actual samples to the discrete reference envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

private theorem n05_materialE0Exponent_mono {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    materialE0Exponent x ≤ materialE0Exponent y := by
  have hy : 0 ≤ y := hx.trans hxy
  have hlogx : 0 ≤ materialLogFactor x := by
    apply Real.log_nonneg
    exact (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans
      (le_add_of_nonneg_right hx)
  have hlog : materialLogFactor x ≤ materialLogFactor y :=
    Real.log_le_log (add_pos_of_pos_of_nonneg (Real.exp_pos _) hx)
      (add_le_add_left hxy _)
  have hmul := mul_le_mul
    (Real.rpow_le_rpow hx hxy (by norm_num : (0 : ℝ) ≤ 5 / 2))
    hlog hlogx (Real.rpow_nonneg hy (5 / 2 : ℝ))
  change 1 + x ^ ((5 : ℝ) / 2) * materialLogFactor x ≤
    1 + y ^ ((5 : ℝ) / 2) * materialLogFactor y
  exact add_le_add_left hmul 1

/-- A bounded coordinate shift costs only a coefficient-sized logarithm. -/
theorem n05_materialE0_log_shift (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |x - (n : ℝ)| ≤ A →
        Real.log (materialE0 x) ≤ C * (radialQ n + 1) := by
  obtain ⟨c, B, hshift⟩ := Radial.radialQ_shift_le ⌈A⌉₊
  let C : ℝ := |c| + |B| + 2
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun n x hx hxn => ?_⟩
  have hceil : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  have hupper : x ≤ ((n + ⌈A⌉₊ : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    linarith only [(abs_le.mp hxn).2, hceil]
  have hmono := n05_materialE0Exponent_mono hx hupper
  have hcast : materialE0Exponent ((n + ⌈A⌉₊ : ℕ) : ℝ) =
      1 + radialQ (n + ⌈A⌉₊) := by
    rfl
  have hQ : 0 ≤ radialQ n := Radial.radialQ_nonneg n
  rw [materialE0, Real.log_exp]
  calc
    _ ≤ 1 + radialQ (n + ⌈A⌉₊) := hmono.trans_eq hcast
    _ ≤ 1 + (c * radialQ n + B) := add_le_add_left (hshift n) 1
    _ ≤ C * (radialQ n + 1) := by
      have hc := mul_le_mul_of_nonneg_right (le_abs_self c) hQ
      have hB := le_abs_self B
      have hBQ := mul_nonneg (abs_nonneg B) hQ
      dsimp only [C]
      nlinarith only [hc, hB, hBQ, abs_nonneg c, hQ]

/-- The actual material coefficient logarithm is controlled at every
point of an actual reference cell, including the compact middle. -/
theorem n05_material_reference_logE0_upper {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    ∃ C : ℝ, 0 < C ∧ ∀ m r, r ∈ D.cells m →
      Real.log (T.E0 r) ≤ C * (radialQ (D.cellIndex m) + 1) := by
  obtain ⟨δ, A, hδ, _, hcoord⟩ := n05_materialCell_endpoint_coordinates hT
  obtain ⟨C0, hC0, hshift⟩ := n05_materialE0_log_shift A
  let middle : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hmiddle : middle ⊆ radialCore D := by
    intro r hr
    exact ⟨by linarith only [hr.1, hδ], by linarith only [hr.2, hδ]⟩
  have hlog : ContinuousOn (fun r => Real.log (T.E0 r)) middle :=
    ((hT.1 T.E0 (by simp)).continuousOn.mono hmiddle).log
      (fun r hr => ((hT.2.1 r (hmiddle hr)).2.2.1).ne')
  obtain ⟨L, hL⟩ := isCompact_Icc.bddAbove_image hlog
  let C : ℝ := max C0 (|L| + 1)
  have hC : 0 < C := hC0.trans_le (le_max_left _ _)
  refine ⟨C, hC, fun m r hrm => ?_⟩
  have hr : r ∈ radialCore D := hD.choose_spec.2.1.2.2.2.1 m hrm
  have hQ : 0 ≤ radialQ (D.cellIndex m) := Radial.radialQ_nonneg _
  by_cases hnear : endpointDistance D r < δ
  · obtain ⟨x, hx, hclose, _, hE0, _⟩ := hcoord m r hr hrm hnear
    rw [hE0]
    exact (hshift (D.cellIndex m) x hx hclose).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hd : δ ≤ min (r - D.a) (D.b - r) := le_of_not_gt hnear
    have hrmid : r ∈ middle :=
      ⟨by linarith only [hd.trans (min_le_left _ _)],
        by linarith only [hd.trans (min_le_right _ _)]⟩
    have hLC : L ≤ C := (le_abs_self L).trans
      ((le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _))
    calc
      _ ≤ L := hL ⟨r, hrmid, rfl⟩
      _ ≤ C := hLC
      _ ≤ C * (radialQ (D.cellIndex m) + 1) := by
        nlinarith only [mul_nonneg hC.le hQ]

/-- Every fixed positive power of the actual sampled E0 costs a fixed
power of the discrete reference coefficient, with a uniform constant. -/
theorem n05_material_sample_E0_power_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ m,
      T.E0 (T.sample m) ^ A ≤ C * radialE (D.cellIndex m) ^ B := by
  obtain ⟨B0, hB0, hlog⟩ := n05_material_reference_logE0_upper hD hT
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _, _⟩ := hdata
  refine ⟨Real.exp (A * B0), A * B0, Real.exp_pos _, mul_nonneg hA hB0.le,
    fun m => ?_⟩
  have hr : T.sample m ∈ radialCore D := hD.choose_spec.2.1.2.2.2.1 m (hsample m)
  have hE0 : 0 < T.E0 (T.sample m) := (hT.2.1 _ hr).2.2.1
  have hexp := mul_le_mul_of_nonneg_left (hlog m _ (hsample m)) hA
  rw [Real.rpow_def_of_pos hE0, radialE, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hexp]

end ContinuousFlexibility.Statements
