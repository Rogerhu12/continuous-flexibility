module

public import ContinuousFlexibility.Radial.R07DeepTailComparison
public import ContinuousFlexibility.Radial.DeepTailPhysicalFlatness

/-!
# Uniform gauge and reciprocal density on an actual physical tail

The logarithmic entrance condition controls the frequency-dependent gauge
on the whole tail.  Combining it with the actual cell coefficient bounds
gives reciprocal-density estimates with constants independent of frequency.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem outer_tail_density_gauge_bounds {D : ReferenceData} {T : DeepTailData}
    (hD : RadialProfileGeometry D) {right : Bool} {j start : ℕ}
    (hj : 2 ≤ j) (hphysical : TailPhysicalRelation D T right j start)
    (hclose : T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    {x : ℝ} (hx : x ∈ Ico T.entrance T.endpoint) :
    exp (-1) ≤ (tailPhysicalRadius right x / (if right then D.b else D.a)) ^
        (2 * (j : ℝ) ^ 2) ∧
      (tailPhysicalRadius right x / (if right then D.b else D.a)) ^
        (2 * (j : ℝ) ^ 2) ≤ exp 1 := by
  have he : 0 < (if right then D.b else D.a) := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hendpoint : r07OutwardLog right (if right then D.b else D.a) = T.endpoint := by
    rw [hphysical.2.1]
    cases right <;> rfl
  have hlog : |log (tailPhysicalRadius right x / (if right then D.b else D.a))| ≤
      (2 * (j : ℝ) ^ 2)⁻¹ := by
    rw [r07_log_radius_ratio_abs right he, hendpoint,
      abs_of_nonpos (sub_nonpos.mpr hx.2.le)]
    linarith only [hclose, hx.1]
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hc : (2 * (j : ℝ) ^ 2) * (2 * (j : ℝ) ^ 2)⁻¹ = 1 :=
    mul_inv_cancel₀ (mul_pos (by norm_num) (pow_pos hjp 2)).ne'
  simpa only [neg_mul, hc] using
    r07_rpow_bounds_of_log (div_pos (r07_radius_pos right x) he)
      (by positivity : 0 ≤ 2 * (j : ℝ) ^ 2) hlog

/-- The actual logarithmic reciprocal density is a cell coefficient power. -/
theorem outer_tail_reciprocal_density_cell_bound
    {D : ReferenceData} {T : DeepTailData} {C : ℕ → ℝ}
    (hC : AccumulatingProfileBounds D C) {right : Bool} {j start : ℕ}
    (hj : 2 ≤ j) (hphysical : TailPhysicalRelation D T right j start)
    (hclose : T.endpoint - T.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    {x : ℝ} (hx : x ∈ Ioo T.entrance T.endpoint) {m : ℕ}
    (hm : tailPhysicalRadius right x ∈ D.cells m) :
    (T.p x)⁻¹ ≤ exp 1 * D.b * (C 0 * radialE (D.cellIndex m) ^ (C 0)) := by
  rcases hC with ⟨hD, hpart, hCpos, _, _, _, _, _, _, hinv, _, _, _⟩
  let r := tailPhysicalRadius right x
  let g := (r / (if right then D.b else D.a)) ^ (2 * (j : ℝ) ^ 2)
  have hr : r ∈ radialCore D := (hphysical.2.2.1 x hx).1
  have hrp : 0 < r := r07_radius_pos right x
  have hwp : 0 < D.w r := hD.2.2.2.2.1 r hr
  have hbp : 0 < D.b := hrp.trans hr.2
  have hg := outer_tail_density_gauge_bounds hD hj hphysical hclose (Ioo_subset_Ico_self hx)
  change exp (-1) ≤ g ∧ g ≤ exp 1 at hg
  have hgp : 0 < g := (exp_pos (-1)).trans_le hg.1
  have hgi : g⁻¹ ≤ exp 1 := by
    have h := inv_anti₀ (exp_pos (-1)) hg.1
    simpa only [← exp_neg, neg_neg] using h
  have hwi : (D.w r)⁻¹ ≤ C 0 * radialE (D.cellIndex m) ^ (C 0) := by
    simpa only [radialJet, abs_of_pos (inv_pos.mpr hwp)] using hinv m r hm 0
  have hp : T.p x = g * D.w r / r := (hphysical.2.2.1 x hx).2
  calc
    (T.p x)⁻¹ = r * g⁻¹ * (D.w r)⁻¹ := by
      rw [hp, inv_div, div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (D.b * exp 1) * (C 0 * radialE (D.cellIndex m) ^ (C 0)) :=
      mul_le_mul (mul_le_mul hr.2.le hgi (inv_pos.mpr hgp).le hbp.le) hwi
        (inv_pos.mpr hwp).le (mul_pos hbp (exp_pos 1)).le
    _ = _ := by ring

end ContinuousFlexibility.Radial
