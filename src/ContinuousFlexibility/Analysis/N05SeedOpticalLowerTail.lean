import ContinuousFlexibility.Analysis.N05SeedOpticalLowerBounds
import ContinuousFlexibility.Analysis.N05SeedOpticalLowerComponents

/-!
# The actual seed's quantitative optical lower bound on every deep tail

The model coefficient, physical dilation and actual carrier index are all
the ones retained by the same seed construction. The closed endpoints are
included using their actual zero derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Radial.SeedReferenceConstruction

open Set Real
open ContinuousFlexibility.Statements

variable {q : ℝ} (P : SeedReferenceConstruction q)

theorem n05_tail_optical_lower :
    ∃ B : ℝ, 0 < B ∧ ∀ (side : Bool) (n j : ℕ),
      P.selected.chain.index ≤ n → 100 ≤ n →
      Icc (P.n05ModelLeft side n) (P.n05ModelRight side n) ⊆
        radialTailInterval (P.selected.family P.selected.sigma) side
          (P.selected.entry side P.selected.chain.index) →
      (Ioo (P.n05TailScale side * P.n05ModelLeft side n)
        (P.n05TailScale side * P.n05ModelRight side n) ∩ P.reference.cells j).Nonempty →
      ∀ r ∈ Icc (P.n05TailScale side * P.n05ModelLeft side n)
        (P.n05TailScale side * P.n05ModelRight side n),
      (B * radialE (P.reference.cellIndex j) ^ (12 : ℝ))⁻¹ *
          min (r - P.n05TailScale side * P.n05ModelLeft side n)
            (P.n05TailScale side * P.n05ModelRight side n - r) ≤
        -deriv P.reference.w r / (r * P.reference.w r) := by
  obtain ⟨B, hB, hbound⟩ := P.n05_tail_optical_coefficient_bound
  refine ⟨B, hB, fun side n j hn h100 hclosed hcarrier r hr => ?_⟩
  have hcomp := P.n05_tail_component side (P.n05_model_component side hn) hclosed
  by_cases heL : r = P.n05TailScale side * P.n05ModelLeft side n
  · subst r
    simp only [sub_self, min_eq_left (sub_nonneg.mpr hcomp.2.1.le), mul_zero,
      hcomp.2.2.2.1, neg_zero, zero_div, le_refl]
  by_cases heR : r = P.n05TailScale side * P.n05ModelRight side n
  · subst r
    simp only [sub_self, min_eq_right (sub_nonneg.mpr hcomp.2.1.le), mul_zero,
      hcomp.2.2.2.2.1, neg_zero, zero_div, le_refl]
  have hrI : r ∈ Ioo (P.n05TailScale side * P.n05ModelLeft side n)
      (P.n05TailScale side * P.n05ModelRight side n) :=
    ⟨lt_of_le_of_ne hr.1 (Ne.symm heL), lt_of_le_of_ne hr.2 heR⟩
  let scale : ℝ := P.n05TailScale side
  let x : ℝ := r / scale
  have hs : 0 < scale := P.n05TailScale_pos side
  have hx : x ∈ Ioo (P.n05ModelLeft side n) (P.n05ModelRight side n) := by
    constructor
    · apply (lt_div_iff₀ hs).mpr
      simpa only [mul_comm] using hrI.1
    · apply (div_lt_iff₀ hs).mpr
      simpa only [mul_comm] using hrI.2
  have hxr : scale * x = r := by dsimp only [x]; field_simp [hs.ne']
  let A : ℝ := morseChainA P.selected.chain n
  let b : ℝ := morseChainB P.selected.chain n
  let d : ℝ := 1372 * (P.selected.family P.selected.sigma).b ^ 3 * A ^ 3
  let α : ℝ := b / d
  have hb : 0 < b := (P.realization.retained_data side n hn).1
  have hA : 0 < A := (mul_pos (by norm_num : (0 : ℝ) < 4) hb).trans
    (P.realization.retained_data side n hn).2.1
  have houter : 0 < (P.selected.family P.selected.sigma).b :=
    P.realization.geometry.1.trans P.realization.geometry.2.1
  have hd : 0 < d := by dsimp only [d]; positivity
  have hmodel : α * min (x - P.n05ModelLeft side n) (P.n05ModelRight side n - x) ≤
      -deriv (P.selected.family P.selected.sigma).w x /
        (x * (P.selected.family P.selected.sigma).w x) :=
    P.realization.n05_seed_opticalRatio_lower_bound_on_component side n hn h100 x hx
  have hcoef : scale ^ 3 * (d / b) ≤
      B * radialE (P.reference.cellIndex j) ^ (12 : ℝ) :=
    hbound side n j hn hclosed hcarrier
  have hInv := inv_anti₀ (mul_pos (pow_pos hs 3) (div_pos hd hb)) hcoef
  have hInvEq : (scale ^ 3 * (d / b))⁻¹ = α / scale ^ 3 := by
    dsimp only [α]
    field_simp [hs.ne', hd.ne', hb.ne']
    <;> ring
  rw [hInvEq] at hInv
  have hdelta : min (r - scale * P.n05ModelLeft side n)
      (scale * P.n05ModelRight side n - r) =
      scale * min (x - P.n05ModelLeft side n) (P.n05ModelRight side n - x) := by
    calc
      min (r - scale * P.n05ModelLeft side n) (scale * P.n05ModelRight side n - r) =
          min (scale * (x - P.n05ModelLeft side n))
            (scale * (P.n05ModelRight side n - x)) := by
        congr 1 <;> rw [mul_sub, hxr]
      _ = scale * min (x - P.n05ModelLeft side n) (P.n05ModelRight side n - x) :=
        (mul_min_of_nonneg _ _ hs.le).symm
  have hscaled : -deriv P.reference.w r / (r * P.reference.w r) =
      (-deriv (P.selected.family P.selected.sigma).w x /
        (x * (P.selected.family P.selected.sigma).w x)) / scale ^ 2 := by
    have he := P.n05_tail_opticalRatio side (hclosed (Ioo_subset_Icc_self hx))
    change -deriv P.reference.w (scale * x) /
      ((scale * x) * P.reference.w (scale * x)) = _ at he
    simpa only [hxr] using he
  have hδ : 0 ≤ min (r - scale * P.n05ModelLeft side n)
      (scale * P.n05ModelRight side n - r) :=
    le_min (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)
  calc
    (B * radialE (P.reference.cellIndex j) ^ (12 : ℝ))⁻¹ *
        min (r - scale * P.n05ModelLeft side n) (scale * P.n05ModelRight side n - r) ≤
        (α / scale ^ 3) *
          min (r - scale * P.n05ModelLeft side n) (scale * P.n05ModelRight side n - r) :=
      mul_le_mul_of_nonneg_right hInv hδ
    _ = (α * min (x - P.n05ModelLeft side n) (P.n05ModelRight side n - x)) /
        scale ^ 2 := by
      rw [hdelta]
      field_simp [hs.ne']
      <;> ring
    _ ≤ (-deriv (P.selected.family P.selected.sigma).w x /
        (x * (P.selected.family P.selected.sigma).w x)) / scale ^ 2 :=
      div_le_div_of_nonneg_right hmodel (sq_nonneg scale)
    _ = -deriv P.reference.w r / (r * P.reference.w r) := hscaled.symm

end ContinuousFlexibility.Radial.SeedReferenceConstruction
