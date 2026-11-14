module

public import ContinuousFlexibility.Radial.ModeLocalMeasure
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Glaeser control for the actual reference density

The tests in the frozen modal graph have ordinary support in the open
interval; their topological support need not avoid its endpoints. A global
bound on the square of the profile derivative, divided by the profile,
supplies the integrability that this distinction requires.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- A nonnegative smooth compactly supported function satisfies a global
Glaeser bound. The loose factor four avoids a second-order Taylor API. -/
theorem nonnegative_compact_deriv_sq_bound {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hnonneg : ∀ x, 0 ≤ w x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, (deriv w x) ^ 2 ≤ C * w x := by
  have hd : ContDiff ℝ ∞ (deriv w) := (contDiff_infty_iff_deriv.mp hw).2
  have hdd : ContDiff ℝ ∞ (deriv (deriv w)) :=
    (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨B, hB⟩ := hdd.continuous.bounded_above_of_compact_support hc.deriv.deriv
  let M : ℝ := max B 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  have hsecond (x : ℝ) : ‖deriv (deriv w) x‖ ≤ M :=
    le_trans (hB x) (le_max_left B 1)
  have hLip (x y : ℝ) : |deriv w y - deriv w x| ≤ M * |y - x| := by
    simpa only [Real.norm_eq_abs] using
      (Convex.norm_image_sub_le_of_norm_deriv_le
        (f := deriv w) (s := (univ : Set ℝ))
        (fun t _ => hd.differentiable (by simp) t)
        (fun t _ => hsecond t) convex_univ (mem_univ x) (mem_univ y))
  refine ⟨4 * M, by positivity, ?_⟩
  intro x
  let q : ℝ := deriv w x
  let h : ℝ := -q / (2 * M)
  let rem : ℝ → ℝ := fun t => w (x + t * h) - w x - t * h * q
  have hder (t : ℝ) :
      HasDerivAt rem (h * (deriv w (x + t * h) - q)) t := by
    have ht : HasDerivAt (fun s : ℝ => x + s * h) h t := by
      simpa using ((hasDerivAt_id t).mul_const h).const_add x
    have hu := (hw.differentiable (by simp) (x + t * h)).hasDerivAt.comp t ht
    have hv : HasDerivAt (fun s : ℝ => s * h * q) (h * q) t := by
      simpa using ((hasDerivAt_id t).mul_const h).mul_const q
    have hder' : HasDerivAt rem (deriv w (x + t * h) * h - h * q) t := by
      simpa only [rem, Function.comp_apply] using (hu.sub_const (w x)).fun_sub hv
    exact hder'.congr_deriv (by ring)
  have hrem : |w (x + h) - w x - h * q| ≤ M * h ^ 2 := by
    have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
        ‖h * (deriv w (x + t * h) - q)‖ ≤ M * h ^ 2 := by
      have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2.le
      have hth : |t * h| ≤ |h| := by
        rw [abs_mul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 (abs_nonneg h)
      calc
        ‖h * (deriv w (x + t * h) - q)‖ =
            |h| * |deriv w (x + t * h) - q| := by rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |h| * (M * |t * h|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg h)
          simpa only [q, add_sub_cancel_left] using hLip x (x + t * h)
        _ ≤ |h| * (M * |h|) := by gcongr
        _ = M * h ^ 2 := by nlinarith [sq_abs h]
    have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t _ => (hder t).hasDerivWithinAt) hb
    simpa only [rem, one_mul, zero_mul, add_zero, sub_self, sub_zero,
      Real.norm_eq_abs] using hm
  have hrel : 2 * M * h = -q := by
    dsimp [h]
    field_simp [hM.ne']
  have hq : q = -2 * M * h := by linarith
  have hqh : h * q = -2 * M * h ^ 2 := by rw [hq]; ring
  have hstep : M * h ^ 2 ≤ w x := by
    have hup := le_trans (le_abs_self (w (x + h) - w x - h * q)) hrem
    rw [hqh] at hup
    nlinarith [hnonneg (x + h)]
  have hsq : q ^ 2 = 4 * M ^ 2 * h ^ 2 := by rw [hq]; ring
  change q ^ 2 ≤ 4 * M * w x
  rw [hsq]
  nlinarith [mul_le_mul_of_nonneg_left hstep (by positivity : 0 ≤ 4 * M)]

theorem matchingProfile_nonneg {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    ∀ r, 0 ≤ D.w r := by
  intro r
  have hg := matchingProfileGeometry hD
  by_cases hr : r ∈ radialCore D
  · exact (hg.2.2.2.2.1 r hr).le
  · have hz : D.w r = 0 := hg.2.2.1.2 r (by
      by_cases ha : r ≤ D.a
      · exact Or.inl ha
      · exact Or.inr (le_of_not_gt (fun h' => hr ⟨lt_of_not_ge ha, h'⟩)))
    simp only [hz, le_refl]

theorem matchingProfile_hasCompactSupport {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    HasCompactSupport D.w := by
  apply HasCompactSupport.of_support_subset_isCompact
    (show IsCompact (Icc D.a D.b) from isCompact_Icc)
  intro r hr
  by_contra hn
  have hz : D.w r = 0 := (matchingProfileGeometry hD).2.2.1.2 r (by
    by_cases ha : r ≤ D.a
    · exact Or.inl ha
    · exact Or.inr (le_of_not_gt (fun h' => hn ⟨(lt_of_not_ge ha).le, h'.le⟩)))
  exact hr hz

theorem matchingProfile_deriv_sq_bound {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    ∃ C : ℝ, 0 < C ∧ ∀ r, (deriv D.w r) ^ 2 ≤ C * D.w r :=
  nonnegative_compact_deriv_sq_bound (matchingProfileGeometry hD).2.2.1.1
    (matchingProfile_hasCompactSupport hD) (matchingProfile_nonneg hD)

end ContinuousFlexibility.Radial
