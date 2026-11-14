module

public import ContinuousFlexibility.Analysis.N05ReferenceEndpointWeights
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# The material logarithm on a bounded shift of a reference index

The real endpoint coordinate is bracketed between consecutive integers.
The already proved discrete slow variation then controls its discrepancy
from the reference material weight by a coefficient exponent.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem n05_materialMExponent_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    materialMExponent x ≤ materialMExponent y := by
  have hy : 0 ≤ y := hx.trans hxy
  have hlogx : 0 ≤ materialLogFactor x := by
    apply Real.log_nonneg
    exact (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans
      (le_add_of_nonneg_right hx)
  have hxy' : Real.exp 1 + x ≤ Real.exp 1 + y := by
    linarith only [hxy]
  have hlog : materialLogFactor x ≤ materialLogFactor y :=
    Real.log_le_log (add_pos_of_pos_of_nonneg (Real.exp_pos _) hx)
      hxy'
  have hmon : x ^ ((5 : ℝ) / 2) * materialLogFactor x ^ 2 ≤
      y ^ ((5 : ℝ) / 2) * materialLogFactor y ^ 2 :=
    mul_le_mul (Real.rpow_le_rpow hx hxy (by norm_num : (0 : ℝ) ≤ 5 / 2))
      (pow_le_pow_left₀ hlogx hlog 2) (sq_nonneg _)
      (Real.rpow_nonneg hy _)
  change 1 + x ^ ((5 : ℝ) / 2) * materialLogFactor x ^ 2 ≤
    1 + y ^ ((5 : ℝ) / 2) * materialLogFactor y ^ 2
  linarith only [hmon]

/-- A bounded additive shift of the endpoint coordinate contributes only
a coefficient-sized logarithmic error, uniformly over all indices. -/
theorem n05_materialM_log_shift {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |x - (n : ℝ)| ≤ A →
      |Real.log (materialM x) - Radial.logM n| ≤ C * (radialQ n + 1) := by
  obtain ⟨B, hB⟩ := Radial.logM_sub_le 1 zero_lt_one
  let A1 : ℝ := A + 1
  let C1 : ℝ := 6 * A1 * (A1 ^ 2 + 1)
  let C : ℝ := C1 + |B| + 1
  have hA1 : 0 ≤ A1 := by dsimp only [A1]; positivity
  have hC1 : 0 ≤ C1 := by dsimp only [C1]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun n x hx hshift => ?_⟩
  let k : ℕ := ⌊x⌋₊
  have hklo : (k : ℝ) ≤ x := Nat.floor_le hx
  have hkhi : x < (k : ℝ) + 1 := Nat.lt_floor_add_one x
  have hsk : |(k : ℝ) - (n : ℝ)| ≤ A1 := by
    apply abs_le.mpr
    have hh := abs_le.mp hshift
    dsimp only [A1]
    constructor <;> linarith only [hklo, hkhi, hh.1, hh.2]
  have hsk1 : |((k + 1 : ℕ) : ℝ) - (n : ℝ)| ≤ A1 := by
    rw [Nat.cast_add, Nat.cast_one]
    apply abs_le.mpr
    have hh := abs_le.mp hshift
    dsimp only [A1]
    constructor <;> linarith only [hklo, hkhi, hh.1, hh.2]
  have hdiscrete (j : ℕ) (hj : |(j : ℝ) - (n : ℝ)| ≤ A1) :
      |Radial.logM j - Radial.logM n| ≤ C * (radialQ n + 1) := by
    have hc := n05_cube_shift_bound (Nat.cast_nonneg j) (Nat.cast_nonneg n) hA1 hj
    have hs : |radialS j - radialS n| ≤ C1 * ((n : ℝ) ^ 2 + 1) := by
      calc
        _ = (2 / 3 : ℝ) * |(j : ℝ) ^ 3 - (n : ℝ) ^ 3| := by
          simp only [radialS, ← mul_sub, abs_mul]
          norm_num
        _ ≤ |(j : ℝ) ^ 3 - (n : ℝ) ^ 3| := by
          nlinarith only [abs_nonneg ((j : ℝ) ^ 3 - (n : ℝ) ^ 3)]
        _ ≤ C1 * ((n : ℝ) ^ 2 + 1) := hc
    have hQ := Radial.radialQ_nonneg n
    calc
      _ ≤ |radialS j - radialS n| + B := by simpa only [one_mul] using hB j n
      _ ≤ C1 * ((n : ℝ) ^ 2 + 1) + |B| := add_le_add hs (le_abs_self B)
      _ ≤ C1 * (radialQ n + 1) + |B| := by
        have hq : (n : ℝ) ^ 2 + 1 ≤ radialQ n + 1 := by
          linarith only [n05_radialIndexSquare_le_Q n]
        have hmon : C1 * ((n : ℝ) ^ 2 + 1) ≤ C1 * (radialQ n + 1) :=
          mul_le_mul_of_nonneg_left hq hC1
        linarith only [hmon]
      _ ≤ C * (radialQ n + 1) := by
        dsimp only [C]
        nlinarith only [mul_nonneg (abs_nonneg B) hQ, hQ]
  have hlow : Radial.logM k ≤ materialMExponent x :=
    n05_materialMExponent_mono (Nat.cast_nonneg k) hklo
  have hupp : materialMExponent x ≤ Radial.logM (k + 1) :=
    n05_materialMExponent_mono hx (by exact_mod_cast hkhi.le)
  rw [materialM, Real.log_exp]
  apply abs_le.mpr
  constructor
  · linarith only [hlow, (abs_le.mp (hdiscrete k hsk)).1]
  · linarith only [hupp, (abs_le.mp (hdiscrete (k + 1) hsk1)).2]

/-- The actual material envelope and the discrete reference envelope have
the same logarithm up to a coefficient-sized error on every physical cell. -/
theorem n05_material_reference_logM_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) :
    ∃ C : ℝ, 0 < C ∧ ∀ m r, r ∈ D.cells m →
      |Real.log (T.M r) - Radial.logM (D.cellIndex m)| ≤
        C * (radialQ (D.cellIndex m) + 1) := by
  obtain ⟨δ, A, hδ, hA, hcoord⟩ := n05_materialCell_endpoint_coordinates hT
  obtain ⟨B, hB, hshiftbound⟩ := n05_materialM_log_shift hA.le
  obtain ⟨bounds, hbounds⟩ := hD
  let middle : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hmiddle : middle ⊆ radialCore D := by
    intro r hr
    exact ⟨by linarith only [hr.1, hδ], by linarith only [hr.2, hδ]⟩
  have hlog : ContinuousOn (fun r => Real.log (T.M r)) middle :=
    ((hT.1 T.M (by simp)).continuousOn.mono hmiddle).log
      (fun r hr => (zero_lt_one.trans_le (hT.2.1 r (hmiddle hr)).2.2.2).ne')
  obtain ⟨L, hL⟩ := isCompact_Icc.bddAbove_image hlog.abs
  have hfinite : {m | (D.cells m ∩ middle).Nonempty}.Finite :=
    hbounds.2.2.2.2.2.1 middle isCompact_Icc hmiddle
  obtain ⟨R, hR⟩ :=
    (hfinite.image (fun m => |Radial.logM (D.cellIndex m)|)).bddAbove
  let C : ℝ := max B (|L| + |R| + 1)
  have hC : 0 < C := hB.trans_le (le_max_left _ _)
  refine ⟨C, hC, fun m r hrm => ?_⟩
  have hr : r ∈ Ioo D.a D.b := hbounds.2.1.2.2.2.1 m hrm
  have hQ := Radial.radialQ_nonneg (D.cellIndex m)
  by_cases hnear : endpointDistance D r < δ
  · obtain ⟨x, hx, hshift, _, _, hM⟩ := hcoord m r hr hrm hnear
    rw [hM]
    exact (hshiftbound (D.cellIndex m) x hx hshift).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith only [hQ]))
  · have hd : δ ≤ min (r - D.a) (D.b - r) := le_of_not_gt hnear
    have hrmid : r ∈ middle :=
      ⟨by linarith only [hd.trans (min_le_left _ _)],
        by linarith only [hd.trans (min_le_right _ _)]⟩
    have hLm : |Real.log (T.M r)| ≤ |L| :=
      (hL ⟨r, hrmid, rfl⟩).trans (le_abs_self L)
    have hRm : |Radial.logM (D.cellIndex m)| ≤ |R| :=
      (hR ⟨m, ⟨r, hrm, hrmid⟩, rfl⟩).trans (le_abs_self R)
    calc
      _ ≤ |Real.log (T.M r)| + |Radial.logM (D.cellIndex m)| := abs_sub _ _
      _ ≤ |L| + |R| := add_le_add hLm hRm
      _ ≤ C := (by linarith : |L| + |R| ≤ |L| + |R| + 1).trans (le_max_right _ _)
      _ ≤ C * (radialQ (D.cellIndex m) + 1) := by
        nlinarith only [mul_nonneg hC.le hQ]

end ContinuousFlexibility.Statements
